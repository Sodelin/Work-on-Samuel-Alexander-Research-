import WongGARG

/-!
# Executable sample tracing for persistent parent arrays

Reference implementation of the sample-rootward tracing in Wong et al. (2024),
Appendix E, printed pp. 14-15. Node identifiers persist and unary nodes are
retained. This first implementation repeats shared paths; it does not claim
verification of tskit's cached traversal or its machine-level running time.
-/
namespace WongSampleTracing

open AncestryViews
universe u
variable {Node : Type u}

def ParentEdge (parent : Node → Option Node) (a b : Node) : Prop :=
  parent b = some a

def OnTrace (parent : Node → Option Node) (a s : Node) : Prop :=
  a = s ∨ Reach (ParentEdge parent) a s

/-- A terminating executable traversal with an explicit fuel budget. -/
def trace (parent : Node → Option Node) : Nat → Node → List Node
  | 0, _ => []
  | fuel + 1, s => s :: match parent s with
    | none => []
    | some p => trace parent fuel p

theorem trace_sound (parent : Node → Option Node) (fuel : Nat) (a s : Node)
    (h : a ∈ trace parent fuel s) : OnTrace parent a s := by
  induction fuel generalizing s with
  | zero => simp [trace] at h
  | succ fuel ih =>
    rw [trace] at h
    rcases List.mem_cons.mp h with heq | htail
    · exact Or.inl heq
    · cases hp : parent s with
      | none => simp [hp] at htail
      | some p =>
        have hr := ih p (by simpa [hp] using htail)
        rcases hr with heq | hpath
        · subst a
          exact Or.inr (.edge hp)
        · exact Or.inr (.snoc hpath hp)

theorem trace_complete (parent : Node → Option Node) (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    (fuel : Nat) (a s : Node) (enough : rank s < fuel)
    (h : OnTrace parent a s) : a ∈ trace parent fuel s := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    rcases h with heq | hpath
    · subst a
      simp [trace]
    · cases hpath with
      | edge he =>
        have hp : parent s = some a := he
        have ha : rank a < fuel := by
          have := decreases a s he
          omega
        simp only [trace, hp, List.mem_cons]
        exact Or.inr (ih a ha (Or.inl rfl))
      | snoc hpath he =>
        have hdec := decreases _ _ he
        change parent s = some _ at he
        simp only [trace, he, List.mem_cons]
        exact Or.inr (ih _ (by omega) (Or.inr hpath))

theorem trace_exact (parent : Node → Option Node) (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    (fuel : Nat) (a s : Node) (enough : rank s < fuel) :
    a ∈ trace parent fuel s ↔ OnTrace parent a s :=
  ⟨trace_sound parent fuel a s,
    trace_complete parent rank decreases fuel a s enough⟩

theorem trace_length_le (parent : Node → Option Node) (fuel : Nat) (s : Node) :
    (trace parent fuel s).length ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [trace]
  | succ fuel ih =>
    cases hp : parent s with
    | none => simp [trace, hp]
    | some p => simpa [trace, hp] using Nat.add_le_add_right (ih p) 1

/-- The executable implementation takes an explicit sample list. -/
def tracedNodes (parent : Node → Option Node) (fuel : Nat) (samples : List Node) :
    List Node := samples.flatMap (trace parent fuel)

theorem tracedNodes_exact (parent : Node → Option Node) (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    (fuel : Nat) (samples : List Node) (enough : ∀ s ∈ samples, rank s < fuel)
    (a : Node) :
    a ∈ tracedNodes parent fuel samples ↔ ∃ s ∈ samples, OnTrace parent a s := by
  simp only [tracedNodes, List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, ha⟩
    exact ⟨s, hs, trace_sound parent fuel a s ha⟩
  · rintro ⟨s, hs, ha⟩
    exact ⟨s, hs, trace_complete parent rank decreases fuel a s (enough s hs) ha⟩

/-- Sample tracing records the parent of a visited node, and none elsewhere. -/
def extract [DecidableEq Node] (parent : Node → Option Node) (fuel : Nat)
    (samples : List Node) (c : Node) : Option Node :=
  if c ∈ tracedNodes parent fuel samples then parent c else none

theorem extract_some_iff [DecidableEq Node] (parent : Node → Option Node)
    (rank : Node → Nat)
    (decreases : ∀ a b, ParentEdge parent a b → rank a < rank b)
    (fuel : Nat) (samples : List Node) (enough : ∀ s ∈ samples, rank s < fuel)
    (p c : Node) :
    extract parent fuel samples c = some p ↔
      ParentEdge parent p c ∧ ∃ s ∈ samples, OnTrace parent c s := by
  rw [extract]
  split
  · rename_i h
    rw [ParentEdge]
    exact ⟨fun hp => ⟨hp, (tracedNodes_exact parent rank decreases fuel samples enough c).mp h⟩,
      fun hp => hp.1⟩
  · rename_i h
    constructor
    · intro he; cases he
    · rintro ⟨_, hs⟩
      exact False.elim (h ((tracedNodes_exact parent rank decreases fuel samples enough c).mpr hs))


section ActualGARG
open WongGARG
universe v
variable {Coord : Type v} [Fintype Node] [DecidableEq Node] [LinearOrder Coord]

omit [DecidableEq Node] in
/-- The input array's graph is checked against the actual interval gARG. -/
theorem onTrace_iff_garg (G : GARG Node Coord) (x : Coord)
    (parent : Node → Option Node)
    (represents : ∀ a b, parent b = some a ↔ G.AtLocus x a b)
    (a s : Node) :
    OnTrace parent a s ↔ a = s ∨ Reach (G.AtLocus x) a s := by
  constructor
  · rintro (heq | hpath)
    · exact Or.inl heq
    · exact Or.inr (reach_mono (fun a b he => (represents a b).mp he) hpath)
  · rintro (heq | hpath)
    · exact Or.inl heq
    · exact Or.inr (reach_mono (fun a b he => (represents a b).mpr he) hpath)

/-- At most n visited nodes per sample suffice, with n the actual node count.
The rank is used only in the proof, not computed by the tracing algorithm. -/
theorem actual_garg_extraction (G : GARG Node Coord) (x : Coord)
    (parent : Node → Option Node)
    (represents : ∀ a b, parent b = some a ↔ G.AtLocus x a b)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples)
    (p c : Node) :
    extract parent (Fintype.card Node) samples c = some p ↔ G.ExtractedAt x p c := by
  classical
  have dec : ∀ a b, ParentEdge parent a b →
      (G.ancestorSet a).card < (G.ancestorSet b).card := by
    intro a b he
    exact G.ancestor_count_lt_of_edge (G.locus_edge_topology ((represents a b).mp he))
  rw [extract_some_iff parent (fun a => (G.ancestorSet a).card) dec
    (Fintype.card Node) samples (fun s _ => G.ancestor_count_lt_card s)]
  constructor
  · rintro ⟨he, s, hs, hpath⟩
    exact ⟨(represents p c).mp he, s, (sampleIds s).mp hs,
      (onTrace_iff_garg G x parent represents c s).mp hpath⟩
  · rintro ⟨he, s, hs, hpath⟩
    exact ⟨(represents p c).mpr he, s, (sampleIds s).mpr hs,
      (onTrace_iff_garg G x parent represents c s).mpr hpath⟩

/-- Reconstruction means equality of indexed edge relations, not equality of
syntactically different ways to split or serialize adjacent intervals. -/
theorem actual_garg_reconstruction_iff (G : GARG Node Coord)
    (parent : Coord → Node → Option Node)
    (represents : ∀ x a b, parent x b = some a ↔ G.AtLocus x a b)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples) :
    (∀ x p c, extract (parent x) (Fintype.card Node) samples c = some p ↔
      G.AtLocus x p c) ↔ G.SampleSupported := by
  have he : ∀ x p c, extract (parent x) (Fintype.card Node) samples c = some p ↔
      G.ExtractedAt x p c := fun x p c =>
    actual_garg_extraction G x (parent x) (represents x) samples sampleIds p c
  constructor
  · intro h
    exact G.extracted_eq_local_iff_sampleSupported.mp
      (fun x p c => (he x p c).symm.trans (h x p c))
  · intro h x p c
    exact (he x p c).trans (G.extracted_eq_local_iff_sampleSupported.mpr h x p c)
end ActualGARG

private def exampleParent (c : Fin 4) : Option (Fin 4) :=
  if c = 0 then none else if c = 1 then some 0 else some 1

/-- A kernel-computed example retains the unary ancestor 1 and omits the
unsupported edge into node 3. It is not a benchmark of tskit. -/
example : List.ofFn (extract exampleParent 4 [2]) = [none, some 0, some 1, none] := by
  decide

end WongSampleTracing
