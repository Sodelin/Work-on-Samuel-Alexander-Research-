import StochasticAbstraction
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false

/-! Invented finite counterexamples. No fitted parameters or biological
mechanism is asserted. All horizons below are quantified in Lean. -/
namespace StochasticExamples

noncomputable section

def coin : PMF Bool := PMF.uniformOfFintype Bool

theorem coin_support (b : Bool) : b ∈ coin.support := by
  simp [coin]

theorem coin_not : coin.map Bool.not = coin := by
  ext b
  cases b <;> simp [coin, PMF.map_apply, tsum_fintype]

def correlated : PMF (Bool × Bool) := coin.map (fun b => (b, b))
def anticorrelated : PMF (Bool × Bool) := coin.map (fun b => (b, !b))

theorem first_marginals : correlated.map Prod.fst = anticorrelated.map Prod.fst := by
  simp only [correlated, anticorrelated, PMF.map_comp, Function.comp_def]

theorem second_marginals : correlated.map Prod.snd = anticorrelated.map Prod.snd := by
  simp only [correlated, anticorrelated, PMF.map_comp, Function.comp_def]
  change coin.map id = coin.map Bool.not
  rw [PMF.map_id, coin_not]

def agrees (pair : Bool × Bool) : Bool := pair.1 == pair.2

theorem correlated_agrees : correlated.map agrees = PMF.pure true := by
  rw [correlated, PMF.map_comp]
  have h : agrees ∘ (fun b : Bool => (b, b)) = Function.const Bool true := by
    funext b
    cases b <;> rfl
  rw [h, PMF.map_const]

theorem anticorrelated_disagrees : anticorrelated.map agrees = PMF.pure false := by
  rw [anticorrelated, PMF.map_comp]
  have h : agrees ∘ (fun b : Bool => (b, !b)) = Function.const Bool false := by
    funext b
    cases b <;> rfl
  rw [h, PMF.map_const]

/-- Both component marginals can match while the joint laws disagree. -/
theorem matching_marginals_different_joint :
    correlated.map Prod.fst = anticorrelated.map Prod.fst ∧
    correlated.map Prod.snd = anticorrelated.map Prod.snd ∧
    correlated ≠ anticorrelated := by
  refine ⟨first_marginals, second_marginals, ?_⟩
  intro h
  have hh := congrArg (fun μ => (μ.map agrees) true) h
  simpa [correlated_agrees, anticorrelated_disagrees] using hh

inductive State where
  | s | t | u | b | c | v
  deriving DecidableEq

open State

def output : State → Bool
  | v => true
  | _ => false

def next : State → PMF State
  | s => coin.map (fun bit => if bit then b else u)
  | t => PMF.pure c
  | u => PMF.pure u
  | b => PMF.pure v
  | c => coin.map (fun bit => if bit then v else u)
  | v => PMF.pure v

/-- The whole joint output trace, including the current output and n transitions. -/
def trace : Nat → State → PMF (List Bool)
  | 0, x => PMF.pure [output x]
  | n + 1, x => (next x).bind (fun y => (trace n y).map (List.cons (output x)))

/-- An affine dependence of predictive laws, holding at every finite horizon. -/
theorem c_is_mixture (n : Nat) :
    trace n c = coin.bind (fun bit => trace n (if bit then b else u)) := by
  cases n with
  | zero =>
    have h : (fun bit : Bool => trace 0 (if bit then b else u)) =
        (fun _ : Bool => PMF.pure [false]) := by
      funext bit
      cases bit <;> rfl
    rw [h, PMF.bind_const]
    rfl
  | succ n =>
    simp only [trace, next, PMF.bind_map, Function.comp_def]
    apply congrArg (fun f => coin.bind f)
    funext bit
    cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte, output,
      PMF.pure_bind]

/-- Equal JOINT output trace laws at all horizons, not just equal marginals. -/
theorem same_all_traces (n : Nat) : trace n s = trace n t := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [trace, next, PMF.bind_map, PMF.pure_bind, Function.comp_def, output]
    rw [c_is_mixture, PMF.map_bind]

/-- Every randomized decision based only on the recorded output trace has the
same law in these two starts. Additional probes or measurements may differ. -/
theorem no_trace_based_test_separates {D : Type*} (n : Nat)
    (test : List Bool → PMF D) :
    (trace n s).bind test = (trace n t).bind test := by
  rw [same_all_traces]

def profile (x : State) : Nat → PMF (List Bool) := fun n => trace n x

theorem same_profile : profile s = profile t := funext same_all_traces

theorem u_one_trace : trace 1 u = PMF.pure [false, false] := by
  simp only [trace, next, PMF.pure_bind, PMF.pure_map, output]

theorem b_one_trace : trace 1 b = PMF.pure [false, true] := by
  simp only [trace, next, PMF.pure_bind, PMF.pure_map, output]

theorem c_one_trace : trace 1 c = coin.map (fun bit => [false, bit]) := by
  simp only [trace, next, PMF.bind_map, Function.comp_def, PMF.pure_map, output]
  change coin.bind _ = coin.bind _
  apply congrArg (fun f => coin.bind f)
  funext bit
  cases bit <;> rfl

theorem c_profile_ne_u : profile c ≠ profile u := by
  intro h
  have hh := congrArg (fun f => f 1) h
  change trace 1 c = trace 1 u at hh
  have hc : [false, true] ∈ (trace 1 c).support := by
    rw [c_one_trace, PMF.mem_support_map_iff]
    exact ⟨true, coin_support true, rfl⟩
  rw [hh, u_one_trace] at hc
  simpa using hc

theorem c_profile_ne_b : profile c ≠ profile b := by
  intro h
  have hh := congrArg (fun f => f 1) h
  change trace 1 c = trace 1 b at hh
  have hc : [false, false] ∈ (trace 1 c).support := by
    rw [c_one_trace, PMF.mem_support_map_iff]
    exact ⟨false, coin_support false, rfl⟩
  rw [hh, b_one_trace] at hc
  simpa using hc

/-- The actual pushed transitions disagree even on the complete predictive profile. -/
theorem profile_pushes_differ : (next s).map profile ≠ (next t).map profile := by
  intro h
  have hc : profile c ∈ ((next t).map profile).support := by
    simp [next, PMF.pure_map]
  rw [← h, next, PMF.map_comp, PMF.mem_support_map_iff] at hc
  obtain ⟨bit, _, hb⟩ := hc
  cases bit
  · exact c_profile_ne_u hb.symm
  · exact c_profile_ne_b hb.symm

/-- Output trace equivalence need not admit a kernel commuting with the
microscopic transitions. This does NOT exclude another output realization. -/
theorem no_commuting_profile_kernel :
    ¬ ∃ L : Unit → (Nat → PMF (List Bool)) → PMF (Nat → PMF (List Bool)),
      StochasticAbstraction.Exact (fun _ : Unit => next) profile L := by
  rintro ⟨L, hL⟩
  apply profile_pushes_differ
  rw [hL () s, hL () t, same_profile]

end
end StochasticExamples
