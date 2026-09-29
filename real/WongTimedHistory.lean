import WongEventEncoding
import SamuelAlexanderResearch.AncestryContraction
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Prod

/-!
# An omitted recombination event hides its time and lineage count

Wong et al. (2024), Appendix B (journal p. 13) and Appendix H.
Seven raw event nodes, three sampled genomes, one recombination. Contracting
only the recombination node produces an actual six-node gARG, with retained
node dates, in which the recombination time is not identifiable.
-/
namespace WongTimedHistory
open WongGARG WongEventEncoding AncestryViews AncestryContraction
noncomputable section

abbrev RawNode := Fin 7
abbrev ObservedNode := Fin 6

/-- Raw IDs: 0 root; 1 and 2 common ancestors; 3 hidden recombination;
4 recombinant sample; 5 and 6 other samples. -/
def rawParents (c : RawNode) : ParentSpec RawNode Nat 0 2 :=
  match c.val with
  | 0 => .root
  | 1 => .singleParent 0
  | 2 => .singleParent 0
  | 3 => .crossover 1 2 1 (by decide) (by decide)
  | 4 => .singleParent 3
  | 5 => .singleParent 1
  | _ => .singleParent 2

def RawTopology (p c : RawNode) : Prop :=
  (p = 0 ∧ c = 1) ∨ (p = 0 ∧ c = 2) ∨
  (p = 1 ∧ c = 3) ∨ (p = 2 ∧ c = 3) ∨
  (p = 3 ∧ c = 4) ∨ (p = 1 ∧ c = 5) ∨ (p = 2 ∧ c = 6)

instance (p c : RawNode) : Decidable (RawTopology p c) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

theorem raw_parent_iff (p c : RawNode) :
    (rawParents c).Parent p ↔ RawTopology p c := by
  fin_cases p <;> fin_cases c <;> simp [rawParents,ParentSpec.Parent,RawTopology]

theorem raw_topology_increases {p c : RawNode} (h : RawTopology p c) : p.val < c.val := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide

def rawEventGraph : EventGraph RawNode Nat 0 2 where
  span := by decide
  parents := rawParents
  acyclic := by
    intro a h
    have hs := reach_time_increases (fun n : RawNode => n.val)
      (fun p c he => raw_topology_increases ((raw_parent_iff p c).mp he)) h
    exact (Nat.lt_irrefl _) hs

def rawGARG : GARG RawNode Nat := rawEventGraph.toGARG {4,5,6}

theorem raw_garg_topology (p c : RawNode) : rawGARG.Topology p c ↔ RawTopology p c :=
  (rawEventGraph.encoded_topology {4,5,6} p c).trans (raw_parent_iff p c)

/-- Integer times are exact valid event times, measured backwards from samples.
The argument needs only these two concrete timed histories, not a stochastic law. -/
structure EventTime where
  value : Nat
  positive : 0 < value
  beforeOlderEvent : value < 7

def rawAge (τ : EventTime) (c : RawNode) : Nat :=
  match c.val with
  | 0 => 10
  | 1 => 8
  | 2 => 7
  | 3 => τ.value
  | _ => 0

/-- Every actual raw edge has an older parent, in both interval branches. -/
theorem raw_chronology (τ : EventTime) {p c : RawNode} (h : rawGARG.Topology p c) :
    rawAge τ c < rawAge τ p := by
  rcases (raw_garg_topology p c).mp h with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals have hp := τ.positive
  all_goals have hb := τ.beforeOlderEvent
  all_goals simp [rawAge]
  all_goals omega

/-- A dated event graph records a chronology proof, not arbitrary time labels. -/
structure TimedHistory where
  graph : GARG RawNode Nat
  age : RawNode → Nat
  chronological : ∀ p c, graph.Topology p c → age c < age p

def history (τ : EventTime) : TimedHistory where
  graph := rawGARG
  age := rawAge τ
  chronological := fun _ _ h => raw_chronology τ h

def degreePair (c : RawNode) : Nat × Nat :=
  ((Finset.univ.filter (fun p => RawTopology p c)).card,
   (Finset.univ.filter (fun d => RawTopology c d)).card)

/-- Strict binary raw event arities: root, two common ancestors, recombination,
and three samples, in that order. This refers to the proved actual topology. -/
theorem raw_event_arities :
    degreePair 0 = (0,2) ∧ degreePair 1 = (1,2) ∧ degreePair 2 = (1,2) ∧
    degreePair 3 = (2,1) ∧ degreePair 4 = (1,0) ∧ degreePair 5 = (1,0) ∧
    degreePair 6 = (1,0) := by decide

/-- Retained IDs in order: raw 0,1,2,4,5,6. The omitted ID 3 is not an
isolated observed node whose timestamp could inadvertently remain visible. -/
def embed (c : ObservedNode) : RawNode :=
  ⟨if c.val < 3 then c.val else c.val + 1, by split <;> omega⟩

def Keep (c : RawNode) : Prop := c ≠ 3

theorem embed_kept (c : ObservedNode) : Keep (embed c) := by
  fin_cases c <;> simp [Keep,embed]

def observedParents (c : ObservedNode) : ParentSpec ObservedNode Nat 0 2 :=
  match c.val with
  | 0 => .root
  | 1 => .singleParent 0
  | 2 => .singleParent 0
  | 3 => .crossover 1 2 1 (by decide) (by decide)
  | 4 => .singleParent 1
  | _ => .singleParent 2

theorem observed_parent_increases {p c : ObservedNode}
    (h : (observedParents c).Parent p) : p.val < c.val := by
  fin_cases p <;> fin_cases c <;> simp_all [observedParents, ParentSpec.Parent]

def observedEventGraph : EventGraph ObservedNode Nat 0 2 where
  span := by decide
  parents := observedParents
  acyclic := by
    intro a h
    have hs := reach_time_increases (fun n : ObservedNode => n.val)
      (fun _ _ he => observed_parent_increases he) h
    exact (Nat.lt_irrefl _) hs

def observedGARG : GARG ObservedNode Nat := observedEventGraph.toGARG {3,4,5}

/-- A direct local inheritance formula independent of record representation. -/
def RawAt (x : Nat) (p c : RawNode) : Prop := (rawParents c).At x p

def ObservedAt (x : Nat) (p c : ObservedNode) : Prop := (observedParents c).At x p

theorem raw_locus_iff (x : Nat) (p c : RawNode) :
    rawGARG.AtLocus x p c ↔ RawAt x p c :=
  rawEventGraph.encoded_atLocus {4,5,6} x p c

theorem observed_locus_iff (x : Nat) (p c : ObservedNode) :
    observedGARG.AtLocus x p c ↔ ObservedAt x p c :=
  observedEventGraph.encoded_atLocus {3,4,5} x p c

/-- Omitting only one node permits either a direct edge or a two-edge path.
The hidden node has no self edge, so no longer hidden chain is possible. -/
theorem hidden_path_iff (x : Nat) (p c : RawNode) :
    HiddenPath (RawAt x) Keep p c ↔
      RawAt x p c ∨ (RawAt x p 3 ∧ RawAt x 3 c) := by
  constructor
  · intro h
    induction h with
    | edge he => exact Or.inl he
    | @snoc b d hp hn he ih =>
      have hb : b = 3 := by simpa [Keep] using hn
      subst b
      rcases ih with direct | ⟨_, loop⟩
      · exact Or.inr ⟨direct,he⟩
      · have impossible : ¬ RawAt x 3 3 := by
          simp [RawAt,rawParents,ParentSpec.At]
        exact False.elim (impossible loop)
  · rintro (h | ⟨h1,h2⟩)
    · exact .edge h
    · exact .snoc (.edge h1) (by simp [Keep]) h2

/-- Direct or hidden-node-mediated edges are exactly the observed local edges. -/
theorem bypass_iff (x : Nat) (p c : ObservedNode) :
    (RawAt x (embed p) (embed c) ∨
      (RawAt x (embed p) 3 ∧ RawAt x 3 (embed c))) ↔ ObservedAt x p c := by
  fin_cases p <;> fin_cases c
  all_goals simp [RawAt,ObservedAt,rawParents,observedParents,embed,ParentSpec.At]
  all_goals omega

/-- Exact semantic validation of the named observation operation: eliminate the
recombination node separately at each locus, retaining all six other nodes. -/
theorem observed_represents_contraction (x : Nat) (p c : ObservedNode) :
    observedGARG.AtLocus x p c ↔
      Contract (rawGARG.AtLocus x) Keep (embed p) (embed c) := by
  have hrel : rawGARG.AtLocus x = RawAt x := by
    funext a b
    exact propext (raw_locus_iff x a b)
  rw [hrel]
  unfold Contract
  rw [hidden_path_iff]
  exact (observed_locus_iff x p c).trans
    ((bypass_iff x p c).symm.trans (by simp [embed_kept]))

/-- Observable dates are the raw dates restricted to genuinely retained IDs. -/
def observedAge (τ : EventTime) (c : ObservedNode) : Nat := rawAge τ (embed c)

theorem observed_dates_independent (τ σ : EventTime) : observedAge τ = observedAge σ := by
  funext c
  fin_cases c <;> rfl

theorem observed_chronology (τ : EventTime) {p c : ObservedNode}
    (h : observedGARG.Topology p c) : observedAge τ c < observedAge τ p := by
  have hp := (observedEventGraph.encoded_topology {3,4,5} p c).mp h
  fin_cases p <;> fin_cases c <;>
    simp_all [EventGraph.Topology,observedEventGraph,observedParents,ParentSpec.Parent,observedAge,rawAge,embed]

abbrev Observation := GARG ObservedNode Nat × (ObservedNode → Nat)

def observe (τ : EventTime) : Observation := (observedGARG,observedAge τ)

theorem observation_independent (τ σ : EventTime) : observe τ = observe σ :=
  Prod.ext rfl (observed_dates_independent τ σ)

/-- Counts actual raw graph edges crossing a backward-time slice. At a raw event
time, outgoing rootward lineages are counted (younger endpoint inclusive).
This count is used only before the root time 10. -/
def lineageCount (τ : EventTime) (t : Nat) : Nat :=
  (Finset.univ.filter (fun e : RawNode × RawNode =>
    RawTopology e.1 e.2 ∧ rawAge τ e.2 ≤ t ∧ t < rawAge τ e.1)).card

/-- The counted edge predicate agrees with the actual timed gARG, including
chronology-derived endpoints. It is not a free numeric label. -/
theorem counted_edge_iff (τ : EventTime) (t : Nat) (e : RawNode × RawNode) :
    (RawTopology e.1 e.2 ∧ rawAge τ e.2 ≤ t ∧ t < rawAge τ e.1) ↔
    ((history τ).graph.Topology e.1 e.2 ∧
      (history τ).age e.2 ≤ t ∧ t < (history τ).age e.1) := by
  change (RawTopology e.1 e.2 ∧ rawAge τ e.2 ≤ t ∧ t < rawAge τ e.1) ↔
    (rawGARG.Topology e.1 e.2 ∧ rawAge τ e.2 ≤ t ∧ t < rawAge τ e.1)
  rw [raw_garg_topology]

def early : EventTime := ⟨2,by decide,by decide⟩
def late : EventTime := ⟨4,by decide,by decide⟩

theorem hidden_times_differ : (history early).age 3 = 2 ∧ (history late).age 3 = 4 := by
  constructor <;> rfl

theorem lineage_counts_differ : lineageCount early 3 = 4 ∧ lineageCount late 3 = 3 := by
  decide

theorem sample_date_is_not_event_date (τ : EventTime) :
    (history τ).age 4 = 0 ∧ (history τ).age 3 = τ.value ∧
    observedAge τ 3 = 0 ∧ 0 < τ.value := ⟨rfl,rfl,rfl,τ.positive⟩

theorem no_exact_time_decoder :
    ¬ ∃ D : Observation → Nat, ∀ τ : EventTime, D (observe τ) = (history τ).age 3 := by
  rintro ⟨D,h⟩
  have he := h early
  have hl := h late
  rw [observation_independent early late] at he
  have bad : (history early).age 3 = (history late).age 3 := he.symm.trans hl
  change 2 = 4 at bad
  omega

theorem no_exact_lineage_decoder :
    ¬ ∃ D : Observation → Nat, ∀ τ : EventTime, D (observe τ) = lineageCount τ 3 := by
  rintro ⟨D,h⟩
  have he := h early
  have hl := h late
  rw [observation_independent early late] at he
  have bad : lineageCount early 3 = lineageCount late 3 := he.symm.trans hl
  rw [lineage_counts_differ.1,lineage_counts_differ.2] at bad
  omega

end
end WongTimedHistory
