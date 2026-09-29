import PredictiveState
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false

/-! Exact lumping of discrete controlled kernels. PMF carriers may be arbitrary,
but each distribution has countable support. Experiments retain actions as well
as observations; randomized policies may use the complete recorded past.
The kernel and policy semantics are assumptions, not claims about an organism. -/
namespace StochasticAbstraction

noncomputable section
universe u v w a b
variable {X : Type u} {R : Type v} {O : Type w} {A : Type a} {B : Type b}

def Exact (K : A → X → PMF X) (q : X → R) (L : A → R → PMF R) : Prop :=
  ∀ a x, (K a x).map q = L a (q x)

def Compatible (K : A → X → PMF X) (q : X → R) : Prop :=
  ∀ a x y, q x = q y → (K a x).map q = (K a y).map q

/-- Strong lumpability: an onto code has an exact kernel exactly when every
action's pushed transition law is constant on each code fibre. -/
theorem exact_iff (K : A → X → PMF X) (q : X → R)
    (onto : Function.Surjective q) : (∃ L, Exact K q L) ↔ Compatible K q := by
  constructor
  · rintro ⟨L, h⟩ a x y hxy
    rw [h a x, h a y, hxy]
  · intro h
    classical
    refine ⟨fun a r => (K a (Classical.choose (onto r))).map q, ?_⟩
    intro a x
    exact h a x _ (Classical.choose_spec (onto (q x))).symm

theorem exact_unique (K : A → X → PMF X) (q : X → R)
    (onto : Function.Surjective q) (L M : A → R → PMF R)
    (hL : Exact K q L) (hM : Exact K q M) : L = M := by
  funext a r
  obtain ⟨x, rfl⟩ := onto r
  exact (hL a x).symm.trans (hM a x)

/-- General bind/map interchange under a pointwise preservation contract. -/
theorem bind_transport {Y : Type w} {Z : Type b}
    (μ : PMF X) (q : X → R) (f : X → PMF Y) (g : R → PMF Z) (e : Y → Z)
    (h : ∀ x, (f x).map e = g (q x)) :
    (μ.bind f).map e = (μ.map q).bind g := by
  rw [PMF.map_bind, PMF.bind_map]
  exact congrArg (fun k => μ.bind k) (funext h)

theorem one_step_law (K : A → X → PMF X) (q : X → R) (L : A → R → PMF R)
    (h : Exact K q L) (a : A) (μ : PMF X) :
    (μ.bind (K a)).map q = (μ.map q).bind (L a) :=
  bind_transport μ q (K a) (L a) q (h a)

/-- The uniform initial-law contract is also necessary: test point masses. -/
theorem exact_iff_all_initial_laws (K : A → X → PMF X) (q : X → R)
    (L : A → R → PMF R) :
    Exact K q L ↔ ∀ (a : A) (μ : PMF X), (μ.bind (K a)).map q = (μ.map q).bind (L a) := by
  constructor
  · exact fun h => one_step_law K q L h
  · intro h a x
    simpa only [PMF.pure_bind, PMF.pure_map] using h a (PMF.pure x)

def runLaw (K : A → X → PMF X) : List A → X → PMF X
  | [], x => PMF.pure x
  | a :: word, x => (K a x).bind (runLaw K word)

theorem runLaw_preserves (K : A → X → PMF X) (q : X → R) (L : A → R → PMF R)
    (h : Exact K q L) (word : List A) (x : X) :
    (runLaw K word x).map q = runLaw L word (q x) := by
  induction word generalizing x with
  | nil => exact PMF.pure_map q x
  | cons a word ih =>
    change ((K a x).bind (runLaw K word)).map q =
      (L a (q x)).bind (runLaw L word)
    rw [bind_transport (K a x) q _ _ q ih, h a x]

theorem runLaw_initial (K : A → X → PMF X) (q : X → R) (L : A → R → PMF R)
    (h : Exact K q L) (word : List A) (μ : PMF X) :
    (μ.bind (runLaw K word)).map q = (μ.map q).bind (runLaw L word) :=
  bind_transport μ q _ _ q (runLaw_preserves K q L h word)

def mapHistory (q : X → R) (past : List (X × A)) : List (R × A) :=
  past.map (fun xa => (q xa.1, xa.2))

def view (q : X → R) (record : List (X × A) × X) : List (R × A) × R :=
  (mapHistory q record.1, q record.2)

theorem mapHistory_append (q : X → R) (past : List (X × A)) (x : X) (a : A) :
    mapHistory q (past ++ [(x, a)]) = mapHistory q past ++ [(q x, a)] := by
  simp [mapHistory]

theorem mapHistory_comp (q : X → R) (d : R → O) (past : List (X × A)) :
    mapHistory d (mapHistory q past) = mapHistory (d ∘ q) past := by
  simp [mapHistory, List.map_map, Function.comp_def]

theorem view_comp (q : X → R) (d : R → O) :
    (view (A := A) d) ∘ view q = view (d ∘ q) := by
  funext record
  exact Prod.ext (mapHistory_comp q d record.1) rfl

/-- A policy receives past (state, action) pairs and the current state. Its PMF
specifies the next randomized action, conditionally on exactly this history. -/
abbrev Policy (X : Type u) (A : Type a) := List (X × A) → X → PMF A

def experiment (K : A → X → PMF X) (choose : Policy X A) :
    Nat → List (X × A) → X → PMF (List (X × A) × X)
  | 0, past, x => PMF.pure (past, x)
  | n + 1, past, x =>
      (choose past x).bind fun a =>
        (K a x).bind fun y => experiment K choose n (past ++ [(x, a)]) y

/-- Full finite joint law, retaining actions and all states. No surjectivity is
needed for preservation once an exact target kernel has been supplied. -/
theorem experiment_preserves (K : A → X → PMF X) (q : X → R)
    (L : A → R → PMF R) (hK : Exact K q L)
    (choose : Policy X A) (chooseR : Policy R A)
    (hchoose : ∀ past x, choose past x = chooseR (mapHistory q past) (q x))
    (n : Nat) (past : List (X × A)) (x : X) :
    (experiment K choose n past x).map (view q) =
      experiment L chooseR n (mapHistory q past) (q x) := by
  induction n generalizing past x with
  | zero => exact PMF.pure_map (view q) (past, x)
  | succ n ih =>
    simp only [experiment, PMF.map_bind]
    rw [hchoose past x]
    apply congrArg (fun k => (chooseR (mapHistory q past) (q x)).bind k)
    funext a
    calc
      (K a x).bind (fun y =>
          (experiment K choose n (past ++ [(x, a)]) y).map (view q)) =
          (K a x).bind (fun y =>
            experiment L chooseR n (mapHistory q past ++ [(q x, a)]) (q y)) := by
        apply congrArg (fun k => (K a x).bind k)
        funext y
        simpa only [mapHistory_append] using ih (past ++ [(x, a)]) y
      _ = ((K a x).map q).bind
          (experiment L chooseR n (mapHistory q past ++ [(q x, a)])) :=
        (PMF.bind_map _ _ _).symm
      _ = _ := by rw [hK a x]

def experimentLaw (K : A → X → PMF X) (choose : Policy X A)
    (n : Nat) (μ : PMF X) : PMF (List (X × A) × X) :=
  μ.bind (experiment K choose n [])

theorem experimentLaw_preserves (K : A → X → PMF X) (q : X → R)
    (L : A → R → PMF R) (hK : Exact K q L)
    (choose : Policy X A) (chooseR : Policy R A)
    (hchoose : ∀ past x, choose past x = chooseR (mapHistory q past) (q x))
    (n : Nat) (μ : PMF X) :
    (experimentLaw K choose n μ).map (view q) =
      experimentLaw L chooseR n (μ.map q) :=
  bind_transport μ q _ _ (view q)
    (fun x => experiment_preserves K q L hK choose chooseR hchoose n [] x)

def observationPolicy (p : X → O) (chooseO : Policy O A) : Policy X A :=
  fun past x => chooseO (mapHistory p past) (p x)

theorem observationPolicy_factors (q : X → R) (p : X → O) (d : R → O)
    (hobs : ∀ x, d (q x) = p x) (chooseO : Policy O A) (past : List (X × A)) (x : X) :
    observationPolicy p chooseO past x =
      observationPolicy d chooseO (mapHistory q past) (q x) := by
  have hp : p = d ∘ q := funext (fun x => (hobs x).symm)
  simp only [observationPolicy, mapHistory_comp, hobs, ← hp]

/-- Any common observation/action-history policy has the same complete finite
observed transcript law, under the matching pushed initial law. -/
theorem observed_experiment_law (K : A → X → PMF X) (q : X → R)
    (L : A → R → PMF R) (hK : Exact K q L)
    (p : X → O) (d : R → O) (hobs : ∀ x, d (q x) = p x)
    (chooseO : Policy O A) (n : Nat) (μ : PMF X) :
    (experimentLaw K (observationPolicy p chooseO) n μ).map (view p) =
      (experimentLaw L (observationPolicy d chooseO) n (μ.map q)).map (view d) := by
  have hp : p = d ∘ q := funext (fun x => (hobs x).symm)
  have h := experimentLaw_preserves K q L hK (observationPolicy p chooseO)
    (observationPolicy d chooseO) (observationPolicy_factors q p d hobs chooseO) n μ
  have hm := congrArg (PMF.map (view d)) h
  simpa only [PMF.map_comp, view_comp, ← hp] using hm

theorem observed_statistic_preserves (K : A → X → PMF X) (q : X → R)
    (L : A → R → PMF R) (hK : Exact K q L)
    (p : X → O) (d : R → O) (hobs : ∀ x, d (q x) = p x)
    (chooseO : Policy O A) (n : Nat) (μ : PMF X)
    (statistic : (List (O × A) × O) → B) :
    ((experimentLaw K (observationPolicy p chooseO) n μ).map (view p)).map statistic =
      ((experimentLaw L (observationPolicy d chooseO) n (μ.map q)).map (view d)).map statistic :=
  congrArg (PMF.map statistic) (observed_experiment_law K q L hK p d hobs chooseO n μ)

/-- The earlier deterministic commutation contract embeds through point masses. -/
theorem deterministic_instance (T : A → X → X) (q : X → R) (G : A → R → R)
    (h : ∀ a x, q (T a x) = G a (q x)) :
    Exact (fun a x => PMF.pure (T a x)) q (fun a r => PMF.pure (G a r)) := by
  intro a x
  rw [PMF.pure_map, h a x]

/-- Retain the measured value along with the chosen latent-state code. -/
def sensorCode (q : X → R) (s : X × O) : R × O := (q s.1, s.2)

/-- A joint next-state/measurement kernel, with no independence between its
components. The current measurement is part of the augmented state. The next
joint draw is X-Markov: previous readings affect it through the chosen action.
Persistent sensor memory or drift must be included in X to use this contract. -/
def sensorStep (J : A → X → PMF (X × O)) (a : A) (s : X × O) : PMF (X × O) :=
  J a s.1

theorem joint_sensor_exact (J : A → X → PMF (X × O)) (q : X → R)
    (Jbar : A → R → PMF (R × O))
    (hJ : ∀ a x, (J a x).map (sensorCode q) = Jbar a (q x)) :
    Exact (sensorStep J) (sensorCode q) (sensorStep Jbar) :=
  fun a s => hJ a s.1

/-- Noisy measurements are covered by a JOINT preservation hypothesis; equal
transition and emission marginals alone are not substituted for this condition.
The initial law may also correlate the latent state and its first measurement. -/
theorem joint_sensor_observed_law (J : A → X → PMF (X × O)) (q : X → R)
    (Jbar : A → R → PMF (R × O))
    (hJ : ∀ a x, (J a x).map (sensorCode q) = Jbar a (q x))
    (chooseO : Policy O A) (n : Nat) (μ : PMF (X × O)) :
    (experimentLaw (sensorStep J) (observationPolicy Prod.snd chooseO) n μ).map
        (view Prod.snd) =
      (experimentLaw (sensorStep Jbar) (observationPolicy Prod.snd chooseO) n
        (μ.map (sensorCode q))).map (view Prod.snd) :=
  observed_experiment_law (sensorStep J) (sensorCode q) (sensorStep Jbar)
    (joint_sensor_exact J q Jbar hJ) Prod.snd Prod.snd (fun _ => rfl) chooseO n μ

end
end StochasticAbstraction
