import SamuelAlexanderResearch.AncestralRestriction

/-! Relation-level elimination of unretained nodes, separately at each locus.
It preserves ancestry between retained nodes but not event identities, path
lengths or lost nodes. This is not an implementation of tskit simplify. -/
namespace AncestryContraction
open AncestryViews AncestralRestriction
universe u v

/-- Nonempty original paths whose internal vertices are all unretained. -/
inductive HiddenPath {V : Type u} (R : V → V → Prop) (K : V → Prop) : V → V → Prop where
  | edge {a b} : R a b → HiddenPath R K a b
  | snoc {a b c} : HiddenPath R K a b → ¬ K b → R b c → HiddenPath R K a c

/-- Each retained-to-retained path with no retained interior becomes one edge. -/
def Contract {V : Type u} (R : V → V → Prop) (K : V → Prop) (a b : V) : Prop :=
  K a ∧ K b ∧ HiddenPath R K a b

theorem hidden_path_original {V : Type u} {R : V → V → Prop} {K : V → Prop}
    {a b : V} (h : HiddenPath R K a b) : Reach R a b := by
  induction h with
  | edge he => exact .edge he
  | snoc _ _ he ih => exact .snoc ih he

theorem contracted_path_original {V : Type u} {R : V → V → Prop} {K : V → Prop}
    {a b : V} (h : Reach (Contract R K) a b) : Reach R a b := by
  induction h with
  | edge he => exact hidden_path_original he.2.2
  | snoc _ he ih => exact reach_trans ih (hidden_path_original he.2.2)

/-- A partial original path has either ended at a retained vertex or has one
unfinished segment after its last retained vertex. -/
private theorem path_summary {V : Type u} {R : V → V → Prop} {K : V → Prop}
    {a b : V} (ha : K a) (h : Reach R a b) :
    (K b ∧ Reach (Contract R K) a b) ∨
    (¬ K b ∧ ∃ c, K c ∧ (a = c ∨ Reach (Contract R K) a c) ∧ HiddenPath R K c b) := by
  classical
  induction h with
  | @edge b he =>
    by_cases hb : K b
    · exact Or.inl ⟨hb, .edge ⟨ha, hb, .edge he⟩⟩
    · exact Or.inr ⟨hb, a, ha, Or.inl rfl, .edge he⟩
  | @snoc b d hp he ih =>
    rcases ih with ⟨hb, path⟩ | ⟨hb, c, hc, initialPath, segment⟩
    · by_cases hd : K d
      · exact Or.inl ⟨hd, .snoc path ⟨hb, hd, .edge he⟩⟩
      · exact Or.inr ⟨hd, b, hb, Or.inr path, .edge he⟩
    · have extended : HiddenPath R K c d := .snoc segment hb he
      by_cases hd : K d
      · apply Or.inl
        refine ⟨hd, ?_⟩
        rcases initialPath with same | path
        · subst c
          exact .edge ⟨ha, hd, extended⟩
        · exact .snoc path ⟨hc, hd, extended⟩
      · exact Or.inr ⟨hd, c, hc, initialPath, extended⟩

/-- Exact ancestry preservation between retained nodes. -/
theorem retained_path_iff {V : Type u} {R : V → V → Prop} {K : V → Prop}
    {a b : V} (ha : K a) (hb : K b) :
    Reach (Contract R K) a b ↔ Reach R a b := by
  constructor
  · exact contracted_path_original
  · intro h
    rcases path_summary ha h with ⟨_, path⟩ | ⟨hn, _⟩
    · exact path
    · exact False.elim (hn hb)

theorem contract_acyclic {V : Type u} {R : V → V → Prop} {K : V → Prop}
    (acyclic : ∀ a, ¬ Reach R a a) : ∀ a, ¬ Reach (Contract R K) a a :=
  fun a h => acyclic a (contracted_path_original h)

/-- A second contraction to fewer retained vertices preserves the same
ancestry as direct contraction. This states reachability, not raw edge syntax. -/
theorem nested_contraction_paths {V : Type u} {R : V → V → Prop}
    {K L : V → Prop} (hKL : ∀ a, K a → L a) {a b : V} (ha : K a) (hb : K b) :
    Reach (Contract (Contract R L) K) a b ↔ Reach (Contract R K) a b :=
  (retained_path_iff ha hb).trans
    ((retained_path_iff (hKL a ha) (hKL b hb)).trans (retained_path_iff ha hb).symm)

/-- Indexwise contraction never changes fixed-locus ancestry of kept nodes. -/
theorem locus_retained_path_iff {V : Type u} {I : Type v}
    (R : I → V → V → Prop) (K : I → V → Prop) (i : I) {a b : V}
    (ha : K i a) (hb : K i b) :
    Reach (Contract (R i) (K i)) a b ↔ Reach (R i) a b := retained_path_iff ha hb

/-- Filtering ancestral material and then eliminating unretained nodes still
preserves exactly all paths from a retained node to a retained sample. -/
theorem resolved_contracted_sample_path_iff {V : Type u} {R : V → V → Prop}
    {S K : V → Prop} {a s : V} (ha : K a) (hs : K s) (sample : S s) :
    Reach (Contract (Restrict R S) K) a s ↔ Reach R a s :=
  (retained_path_iff ha hs).trans (sample_path_iff sample)

end AncestryContraction

#print axioms AncestryContraction.retained_path_iff
#print axioms AncestryContraction.contract_acyclic
#print axioms AncestryContraction.nested_contraction_paths
#print axioms AncestryContraction.locus_retained_path_iff
#print axioms AncestryContraction.resolved_contracted_sample_path_iff
