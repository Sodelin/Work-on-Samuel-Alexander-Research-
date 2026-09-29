import WongRecordTracing
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter

/-! Executable Appendix E caching: nonempty cached entries stop a traversal.
Roots and unvisited nodes both have `none`; a revisited root is looked up again.
Fuel is explicit. Cost fields count abstract cache checks, parent lookups and
nonempty writes, not record comparisons, allocation costs or CPU time. -/
namespace WongMemoizedTracing
open AncestryViews WongSampleTracing
universe u
variable {Node : Type u} [DecidableEq Node]

structure Result (Node : Type u) where
  cache : Node → Option Node
  writes : Nat
  lookups : Nat
  checks : Nat

def put (cache : Node → Option Node) (s p : Node) : Node → Option Node :=
  fun a => if a = s then some p else cache a

def visit (parent : Node → Option Node) : Nat → Node → (Node → Option Node) → Result Node
  | 0, _, cache => ⟨cache, 0, 0, 0⟩
  | fuel + 1, s, cache =>
    match cache s with
    | some _ => ⟨cache, 0, 0, 1⟩
    | none => match parent s with
      | none => ⟨cache, 0, 1, 1⟩
      | some p =>
        let r := visit parent fuel p (put cache s p)
        ⟨r.cache, r.writes + 1, r.lookups + 1, r.checks + 1⟩

def run (parent : Node → Option Node) (fuel : Nat) :
    List Node → (Node → Option Node) → Result Node
  | [], cache => ⟨cache, 0, 0, 0⟩
  | s :: rest, cache =>
    let first := visit parent fuel s cache
    let tail := run parent fuel rest first.cache
    ⟨tail.cache, first.writes + tail.writes,
      first.lookups + tail.lookups, first.checks + tail.checks⟩

def memoExtract (parent : Node → Option Node) (fuel : Nat) (samples : List Node) :
    Node → Option Node := (run parent fuel samples (fun _ => none)).cache

def Sound (parent cache : Node → Option Node) : Prop :=
  ∀ c p, cache c = some p → parent c = some p

def Closed (parent cache : Node → Option Node) : Prop :=
  ∀ c p, cache c = some p → ∀ a, OnTrace parent a c → cache a = parent a

omit [DecidableEq Node] in
lemma onTrace_trans {parent : Node → Option Node} {a b c : Node}
    (hab : OnTrace parent a b) (hbc : OnTrace parent b c) : OnTrace parent a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  apply Or.inr
  induction hbc with
  | edge he => exact .snoc hab he
  | snoc _ he ih => exact .snoc ih he

omit [DecidableEq Node] in
lemma onTrace_rank_le (parent : Node → Option Node) (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    {a s : Node} (h : OnTrace parent a s) : rank a ≤ rank s := by
  rcases h with rfl | h
  · exact Nat.le_refl _
  have hl : rank a < rank s := by
    induction h with
    | edge he => exact decreases _ _ he
    | snoc _ he ih => exact Nat.lt_trans ih (decreases _ _ he)
  exact Nat.le_of_lt hl

omit [DecidableEq Node] in
lemma onTrace_tail (parent : Node → Option Node) {a s p : Node}
    (hp : parent s = some p) (h : OnTrace parent a s) :
    a = s ∨ OnTrace parent a p := by
  rcases h with h | h
  · exact Or.inl h
  cases h with
  | edge he =>
    have hsame : a = p := Option.some.inj (he.symm.trans hp)
    exact Or.inr (Or.inl hsame)
  | snoc hpath he =>
    have hsame := Option.some.inj (he.symm.trans hp)
    subst_vars
    exact Or.inr (Or.inr hpath)

omit [DecidableEq Node] in
lemma onTrace_root (parent : Node → Option Node) {a s : Node}
    (hp : parent s = none) (h : OnTrace parent a s) : a = s := by
  rcases h with h | h
  · exact h
  cases h with
  | edge he => change parent s = some _ at he; rw [hp] at he; cases he
  | snoc _ he => change parent s = some _ at he; rw [hp] at he; cases he

lemma put_sound {parent cache : Node → Option Node} (sound : Sound parent cache)
    {s p : Node} (hp : parent s = some p) : Sound parent (put cache s p) := by
  intro a q h
  by_cases ha : a = s
  · subst a
    have hsame : p = q := Option.some.inj (by simpa [put] using h)
    simpa [hsame] using hp
  · exact sound a q (by simpa [put, ha] using h)

lemma visit_preserves (parent : Node → Option Node) (fuel : Nat)
    (s : Node) (cache : Node → Option Node) (a p : Node)
    (h : cache a = some p) : (visit parent fuel s cache).cache a = some p := by
  induction fuel generalizing s cache with
  | zero => exact h
  | succ fuel ih =>
    cases hs : cache s with
    | some q => simpa [visit, hs] using h
    | none =>
      cases hp : parent s with
      | none => simpa [visit, hs, hp] using h
      | some q =>
        have hne : a ≠ s := by intro heq; subst a; rw [hs] at h; cases h
        simpa only [visit, hs, hp] using
          ih q (put cache s q) (by simpa [put, hne] using h)

lemma visit_sound (parent : Node → Option Node) (fuel : Nat)
    (s : Node) (cache : Node → Option Node) (sound : Sound parent cache) :
    Sound parent (visit parent fuel s cache).cache := by
  induction fuel generalizing s cache with
  | zero => exact sound
  | succ fuel ih =>
    cases hs : cache s with
    | some q => simpa [visit, hs] using sound
    | none =>
      cases hp : parent s with
      | none => simpa [visit, hs, hp] using sound
      | some q =>
        simpa only [visit, hs, hp] using ih q (put cache s q) (put_sound sound hp)

omit [DecidableEq Node] in
lemma sound_preserves_correct {parent before after : Node → Option Node}
    (sound : Sound parent after)
    (preserves : ∀ a p, before a = some p → after a = some p)
    {a : Node} (correct : before a = parent a) : after a = parent a := by
  cases hp : parent a with
  | some p => exact preserves a p (correct.trans hp)
  | none =>
    cases ha : after a with
    | none => rfl
    | some p => have hbad := sound a p ha; rw [hp] at hbad; cases hbad

lemma visit_origin (parent : Node → Option Node) (fuel : Nat)
    (s : Node) (cache : Node → Option Node) (a p : Node)
    (h : (visit parent fuel s cache).cache a = some p) :
    cache a = some p ∨ OnTrace parent a s := by
  induction fuel generalizing s cache with
  | zero => exact Or.inl h
  | succ fuel ih =>
    cases hs : cache s with
    | some q => exact Or.inl (by simpa [visit, hs] using h)
    | none =>
      cases hp : parent s with
      | none => exact Or.inl (by simpa [visit, hs, hp] using h)
      | some q =>
        have hr := ih q (put cache s q) (by simpa only [visit, hs, hp] using h)
        rcases hr with old | path
        · by_cases heq : a = s
          · exact Or.inr (Or.inl heq)
          · exact Or.inl (by simpa [put, heq] using old)
        · exact Or.inr (onTrace_trans path (Or.inr (.edge hp)))

/-- A rank-local invariant permits writing a child before completing its parent.
New writes are strictly below the current ancestor in the descent orientation,
so a nonempty cache hit higher on the trace comes from the completed seed cache. -/
lemma visit_complete_aux (parent : Node → Option Node) (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    (seed : Node → Option Node) (closed : Closed parent seed)
    (fuel : Nat) (s : Node) (cache : Node → Option Node)
    (sound : Sound parent cache)
    (agrees : ∀ a, rank a ≤ rank s → cache a = seed a)
    (enough : rank s < fuel) :
    ∀ a, OnTrace parent a s → (visit parent fuel s cache).cache a = parent a := by
  induction fuel generalizing s cache with
  | zero => omega
  | succ fuel ih =>
    cases hs : cache s with
    | some q =>
      intro a ha
      have seedhit : seed s = some q := (agrees s (Nat.le_refl _)).symm.trans hs
      have hc := (agrees a (onTrace_rank_le parent rank decreases ha)).trans
        (closed s q seedhit a ha)
      simpa [visit, hs] using hc
    | none =>
      cases hp : parent s with
      | none =>
        intro a ha
        have heq := onTrace_root parent hp ha
        subst a
        simp [visit, hs, hp]
      | some q =>
        have hdec := decreases q s hp
        have low : ∀ a, rank a ≤ rank q → put cache s q a = seed a := by
          intro a ha
          have hne : a ≠ s := by intro heq; subst a; omega
          simpa [put, hne] using agrees a (by omega)
        have tail := ih q (put cache s q) (put_sound sound hp) low (by omega)
        intro a ha
        rcases onTrace_tail parent hp ha with heq | ha
        · subst a
          have saved := visit_preserves parent fuel q (put cache s q) s q
            (by simp [put])
          simpa only [visit, hs, hp] using saved.trans hp.symm
        · simpa only [visit, hs, hp] using tail a ha

lemma visit_complete (parent : Node → Option Node) (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    (fuel : Nat) (s : Node) (cache : Node → Option Node)
    (sound : Sound parent cache) (closed : Closed parent cache)
    (enough : rank s < fuel) :
    ∀ a, OnTrace parent a s → (visit parent fuel s cache).cache a = parent a :=
  visit_complete_aux parent rank decreases cache closed fuel s cache sound
    (fun _ _ => rfl) enough

lemma visit_closed (parent : Node → Option Node) (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    (fuel : Nat) (s : Node) (cache : Node → Option Node)
    (sound : Sound parent cache) (closed : Closed parent cache)
    (enough : rank s < fuel) : Closed parent (visit parent fuel s cache).cache := by
  intro c p hc a ha
  rcases visit_origin parent fuel s cache c p hc with old | path
  · exact sound_preserves_correct (visit_sound parent fuel s cache sound)
      (visit_preserves parent fuel s cache) (closed c p old a ha)
  · exact visit_complete parent rank decreases fuel s cache sound closed enough a
      (onTrace_trans ha path)

lemma run_preserves (parent : Node → Option Node) (fuel : Nat)
    (samples : List Node) (cache : Node → Option Node) (a p : Node)
    (h : cache a = some p) : (run parent fuel samples cache).cache a = some p := by
  induction samples generalizing cache with
  | nil => exact h
  | cons s rest ih =>
    exact ih (visit parent fuel s cache).cache (visit_preserves parent fuel s cache a p h)

lemma run_sound (parent : Node → Option Node) (fuel : Nat)
    (samples : List Node) (cache : Node → Option Node) (sound : Sound parent cache) :
    Sound parent (run parent fuel samples cache).cache := by
  induction samples generalizing cache with
  | nil => exact sound
  | cons s rest ih =>
    exact ih (visit parent fuel s cache).cache (visit_sound parent fuel s cache sound)

lemma run_origin (parent : Node → Option Node) (fuel : Nat)
    (samples : List Node) (cache : Node → Option Node) (a p : Node)
    (h : (run parent fuel samples cache).cache a = some p) :
    cache a = some p ∨ ∃ s ∈ samples, OnTrace parent a s := by
  induction samples generalizing cache with
  | nil => exact Or.inl h
  | cons s rest ih =>
    rcases ih (visit parent fuel s cache).cache h with old | tail
    · rcases visit_origin parent fuel s cache a p old with old | path
      · exact Or.inl old
      · exact Or.inr ⟨s, List.mem_cons_self, path⟩
    · obtain ⟨t, ht, path⟩ := tail
      exact Or.inr ⟨t, List.mem_cons_of_mem s ht, path⟩

lemma run_complete (parent : Node → Option Node) (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    (fuel : Nat) (samples : List Node) (cache : Node → Option Node)
    (sound : Sound parent cache) (closed : Closed parent cache)
    (enough : ∀ s ∈ samples, rank s < fuel) :
    ∀ s ∈ samples, ∀ a, OnTrace parent a s →
      (run parent fuel samples cache).cache a = parent a := by
  induction samples generalizing cache with
  | nil => simp
  | cons s rest ih =>
    have hs := visit_sound parent fuel s cache sound
    have hc := visit_closed parent rank decreases fuel s cache sound closed
      (enough s List.mem_cons_self)
    intro t ht a ha
    rcases List.mem_cons.mp ht with heq | ht
    · subst t
      exact sound_preserves_correct (run_sound parent fuel rest _ hs)
        (run_preserves parent fuel rest _)
        (visit_complete parent rank decreases fuel s cache sound closed
          (enough s List.mem_cons_self) a ha)
    · exact ih _ hs hc (fun t ht => enough t (List.mem_cons_of_mem s ht)) t ht a ha

/-- Exact output edges after all sample traversals, including early stopping. -/
theorem memoExtract_some_iff (parent : Node → Option Node) (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    (fuel : Nat) (samples : List Node) (enough : ∀ s ∈ samples, rank s < fuel)
    (p c : Node) : memoExtract parent fuel samples c = some p ↔
      ParentEdge parent p c ∧ ∃ s ∈ samples, OnTrace parent c s := by
  have hs : Sound parent (fun _ => none) := by intro c p h; cases h
  have hc : Closed parent (fun _ => none) := by intro c p h; cases h
  constructor
  · intro h
    have he := run_sound parent fuel samples _ hs c p h
    have origin := run_origin parent fuel samples (fun _ => none) c p h
    rcases origin with impossible | path
    · cases impossible
    · exact ⟨he, path⟩
  · rintro ⟨he, s, hsample, path⟩
    exact (run_complete parent rank decreases fuel samples _ hs hc enough s hsample c path).trans he

/-- Extensional equality with the slower reference traversal under explicit fuel. -/
theorem memoExtract_eq_reference (parent : Node → Option Node) (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    (fuel : Nat) (samples : List Node) (enough : ∀ s ∈ samples, rank s < fuel) :
    memoExtract parent fuel samples = WongSampleTracing.extract parent fuel samples := by
  funext c
  have eq : ∀ p, memoExtract parent fuel samples c = some p ↔
      WongSampleTracing.extract parent fuel samples c = some p := fun p =>
    (memoExtract_some_iff parent rank decreases fuel samples enough p c).trans
      (extract_some_iff parent rank decreases fuel samples enough p c).symm
  cases hm : memoExtract parent fuel samples c with
  | none =>
    cases hr : WongSampleTracing.extract parent fuel samples c with
    | none => rfl
    | some p => have hbad := (eq p).mpr hr; rw [hm] at hbad; cases hbad
  | some p => exact ((eq p).mp hm).symm


/-- Count entries holding an actual parent; root-none is not counted. -/
def filled [Fintype Node] (cache : Node → Option Node) : Finset Node :=
  Finset.univ.filter (fun a => cache a ≠ none)

lemma filled_put [Fintype Node] (cache : Node → Option Node) (s p : Node) :
    filled (put cache s p) = insert s (filled cache) := by
  ext a
  simp only [filled, Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
  by_cases ha : a = s
  · simp [put, ha]
  · simp [put, ha]

lemma filled_put_card [Fintype Node] (cache : Node → Option Node) (s p : Node)
    (hs : cache s = none) :
    (filled (put cache s p)).card = (filled cache).card + 1 := by
  rw [filled_put, Finset.card_insert_of_notMem]
  simp [filled, hs, Finset.mem_filter]

/-- Every write increases the number of nonempty entries by exactly one. -/
theorem visit_write_accounting [Fintype Node] (parent : Node → Option Node)
    (fuel : Nat) (s : Node) (cache : Node → Option Node) :
    (filled (visit parent fuel s cache).cache).card =
      (filled cache).card + (visit parent fuel s cache).writes := by
  induction fuel generalizing s cache with
  | zero => simp [visit]
  | succ fuel ih =>
    cases hs : cache s with
    | some q => simp [visit, hs]
    | none =>
      cases hp : parent s with
      | none => simp [visit, hs, hp]
      | some q =>
        have ht := ih q (put cache s q)
        have hw := filled_put_card cache s q hs
        simp only [visit, hs, hp]
        omega

theorem run_write_accounting [Fintype Node] (parent : Node → Option Node)
    (fuel : Nat) (samples : List Node) (cache : Node → Option Node) :
    (filled (run parent fuel samples cache).cache).card =
      (filled cache).card + (run parent fuel samples cache).writes := by
  induction samples generalizing cache with
  | nil => simp [run]
  | cons s rest ih =>
    have ht := ih (visit parent fuel s cache).cache
    have hf := visit_write_accounting parent fuel s cache
    simp only [run]
    omega

/-- One traversal has at most one terminal check beyond its writes, including
an early cache hit or a root lookup. Fuel exhaustion is not counted as a check. -/
theorem visit_cost_bounds (parent : Node → Option Node) (fuel : Nat)
    (s : Node) (cache : Node → Option Node) :
    (visit parent fuel s cache).checks ≤ (visit parent fuel s cache).writes + 1 ∧
    (visit parent fuel s cache).lookups ≤ (visit parent fuel s cache).writes + 1 := by
  induction fuel generalizing s cache with
  | zero => simp [visit]
  | succ fuel ih =>
    cases hs : cache s with
    | some q => simp [visit, hs]
    | none =>
      cases hp : parent s with
      | none => simp [visit, hs, hp]
      | some q =>
        have ht := ih q (put cache s q)
        simp only [visit, hs, hp]
        constructor <;> omega

/-- Duplicate samples are allowed; each contributes at most one extra check. -/
theorem run_cost_bounds (parent : Node → Option Node) (fuel : Nat)
    (samples : List Node) (cache : Node → Option Node) :
    (run parent fuel samples cache).checks ≤
        (run parent fuel samples cache).writes + samples.length ∧
    (run parent fuel samples cache).lookups ≤
        (run parent fuel samples cache).writes + samples.length := by
  induction samples generalizing cache with
  | nil => simp [run]
  | cons s rest ih =>
    have ht := ih (visit parent fuel s cache).cache
    have hf := visit_cost_bounds parent fuel s cache
    simp only [run, List.length_cons]
    constructor <;> omega

/-- Abstract write/check/lookup bounds. They do not assume constant-time record
scans or constant-time functional-cache access and are not CPU runtime bounds. -/
theorem memoized_cost_bounds [Fintype Node] (parent : Node → Option Node)
    (fuel : Nat) (samples : List Node) :
    let r := run parent fuel samples (fun _ => none)
    r.writes ≤ Fintype.card Node ∧
    r.checks ≤ r.writes + samples.length ∧
    r.lookups ≤ r.writes + samples.length := by
  dsimp only
  have hw := run_write_accounting parent fuel samples (fun _ => none)
  have empty : (filled (fun _ : Node => (none : Option Node))).card = 0 := by
    simp [filled]
  have cap : (filled (run parent fuel samples (fun _ => none)).cache).card ≤
      Fintype.card Node := by
    exact Finset.card_le_univ _
  have costs := run_cost_bounds parent fuel samples (fun _ => none)
  exact ⟨by omega, costs⟩

section ActualGARG
open WongGARG WongRecordTracing
universe v
variable {Coord : Type v} [Fintype Node] [LinearOrder Coord]

/-- Fuel equal to the actual finite node count suffices. Acyclicity is supplied
by the GARG; the ancestor-count rank is used in the proof only. -/
theorem actual_memoized_extraction (G : GARG Node Coord) (x : Coord)
    (parent : Node → Option Node)
    (represents : ∀ a b, parent b = some a ↔ G.AtLocus x a b)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples)
    (p c : Node) :
    memoExtract parent (Fintype.card Node) samples c = some p ↔ G.ExtractedAt x p c := by
  have dec : ∀ a b, ParentEdge parent a b →
      (G.ancestorSet a).card < (G.ancestorSet b).card := by
    intro a b he
    exact G.ancestor_count_lt_of_edge (G.locus_edge_topology ((represents a b).mp he))
  rw [memoExtract_eq_reference parent (fun a => (G.ancestorSet a).card) dec
    (Fintype.card Node) samples (fun s _ => G.ancestor_count_lt_card s)]
  exact actual_garg_extraction G x parent represents samples sampleIds p c

/-- Executable scan of actual interval records followed by the cached traversal. -/
theorem records_to_memoized_sample_array (G : GARG Node Coord) (x : Coord)
    (unique : G.UniqueParentAt x) (records : List (EdgeRecord Node Coord))
    (recordIds : ∀ e, e ∈ records ↔ e ∈ G.records)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples)
    (p c : Node) :
    memoExtract (lookup records x) (Fintype.card Node) samples c = some p ↔
      G.ExtractedAt x p c :=
  actual_memoized_extraction G x (lookup records x)
    (lookup_represents G x unique records recordIds) samples sampleIds p c

/-- Complete cached parent arrays recover the source local edge relation
exactly under the same sample-support condition as the reference traversal. -/
theorem memoized_records_round_trip_iff (G : GARG Node Coord)
    (unique : ∀ x, G.UniqueParentAt x) (records : List (EdgeRecord Node Coord))
    (recordIds : ∀ e, e ∈ records ↔ e ∈ G.records)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples) :
    (∀ x p c, memoExtract (lookup records x) (Fintype.card Node) samples c = some p ↔
      G.AtLocus x p c) ↔ G.SampleSupported := by
  have he : ∀ x p c,
      memoExtract (lookup records x) (Fintype.card Node) samples c = some p ↔
        G.ExtractedAt x p c := fun x p c =>
    records_to_memoized_sample_array G x (unique x) records recordIds samples sampleIds p c
  constructor
  · intro h
    exact G.extracted_eq_local_iff_sampleSupported.mp
      (fun x p c => (he x p c).symm.trans (h x p c))
  · intro h x p c
    exact (he x p c).trans (G.extracted_eq_local_iff_sampleSupported.mpr h x p c)
end ActualGARG

private def exampleParent (c : Fin 4) : Option (Fin 4) :=
  if c = 0 then none else if c = 1 then some 0 else some 1

/-- Shared unary node 1 remains, with the second trace stopping on its cache hit. -/
example : List.ofFn (memoExtract exampleParent 4 [2, 3]) =
    [none, some 0, some 1, some 1] := by decide

example : let r := run exampleParent 4 [2, 3] (fun _ => none)
    (r.writes, r.lookups, r.checks) = (3, 4, 5) := by decide

/-- Two root samples both require lookup, because root-none is not a visited bit. -/
example : let r := run exampleParent 4 [0, 0] (fun _ => none)
    (r.writes, r.lookups, r.checks) = (0, 2, 2) := by decide










end WongMemoizedTracing
