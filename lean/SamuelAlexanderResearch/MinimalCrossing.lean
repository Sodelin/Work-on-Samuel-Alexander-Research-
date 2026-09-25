import SamuelAlexanderResearch.InfiniteConservation
import SamuelAlexanderResearch.BinaryPopulation

/-!
Equality in the binary root-free crossing bound determines the actual tail
graph. The hypotheses concern full infinite-graph cut counts; the edge pattern
and the degree equalities are conclusions, not fields of the model.
-/

namespace MinimalCrossing
open PopulationCounting InfiniteConservation

/-- Every finite block of target columns counts a subset of the cut edges. -/
theorem target_block_le_crossing {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n m : Nat) :
    sumBelow m (fun i => incomingFromPrefix p n (n+i)) ≤
      InfiniteConservation.crossingCount p n := by
  calc
    _ = sumBelow n (fun u => sumBelow m (fun i => edgeBit (p.edge u (n+i)))) :=
      sumBelow_swap m n _
    _ ≤ InfiniteConservation.crossingCount p n :=
      sumBelow_mono (fun u _ => target_block_le_crossing_row p n u m)

/-- The first two target columns and any later column are disjoint cut edges. -/
theorem first_two_and_later_le_crossing {k d : Nat}
    (p : InfiniteLabeledPopulation k d) (n v : Nat) (hv : n+2 ≤ v) :
    incomingFromPrefix p n n + incomingFromPrefix p n (n+1) +
      incomingFromPrefix p n v ≤ InfiniteConservation.crossingCount p n := by
  have h := target_block_le_crossing p n (v-n+1)
  rw [sumBelow_succ] at h
  have hm := sumBelow_range_mono (show 2 ≤ v-n by omega)
    (fun i => incomingFromPrefix p n (n+i))
  have he : n + (v-n) = v := by omega
  simp only [sumBelow_succ, sumBelow_zero, Nat.add_zero, Nat.zero_add] at hm
  rw [he] at h
  omega

/-- Equality in the binary bound fixes the two first incoming column counts. -/
theorem minimum_cut_columns {d : Nat} (p : InfiniteLabeledPopulation 2 d)
    (n : Nat) (hn : p.rootSupport ≤ n)
    (hc : InfiniteConservation.crossingCount p n = 3) :
    incomingFromPrefix p n n = 2 ∧ incomingFromPrefix p n (n+1) = 1 := by
  have h0 := old_parent_lower p n 0 hn
  have h1 := old_parent_lower p n 1 hn
  have hsum := target_block_le_crossing p n 2
  simp only [Nat.add_zero, Nat.sub_zero] at h0
  simp only [sumBelow_succ, sumBelow_zero, Nat.add_zero, Nat.zero_add] at hsum
  omega

/-- At a minimum-width cut, the two first future vertices are joined. -/
theorem minimum_cut_internal_edge {d : Nat} (p : InfiniteLabeledPopulation 2 d)
    (n : Nat) (hn : p.rootSupport ≤ n)
    (hc : InfiniteConservation.crossingCount p n = 3) :
    (p.edge n (n+1)).isSome = true := by
  have hcol := (minimum_cut_columns p n hn hc).2
  have hin := full_indegree_lower p (n+1) (p.no_roots_after (n+1) (by omega))
  change 2 ≤ incomingFromPrefix p n (n+1) + edgeBit (p.edge n (n+1)) at hin
  cases he : p.edge n (n+1) with
  | none => simp [he, edgeBit] at hin; omega
  | some label => simp

/-- All crossing edges at a minimum-width cut target its first two future vertices. -/
theorem minimum_cut_no_late_target {d : Nat} (p : InfiniteLabeledPopulation 2 d)
    (n : Nat) (hn : p.rootSupport ≤ n)
    (hc : InfiniteConservation.crossingCount p n = 3)
    (u v : Nat) (hu : u < n) (hv : n+2 ≤ v) : p.edge u v = none := by
  have hcols := minimum_cut_columns p n hn hc
  have h := first_two_and_later_le_crossing p n v hv
  have ht := term_le_sumBelow (fun a => edgeBit (p.edge a v)) hu
  change edgeBit (p.edge u v) ≤ incomingFromPrefix p n v at ht
  cases he : p.edge u v with
  | none => rfl
  | some label => simp [he, edgeBit] at ht; omega

/-- Equal neighboring cut widths after all roots force zero local defect. -/
theorem regular_of_equal_crossing (p : InfiniteLabeledPopulation 2 2)
    (n : Nat) (hn : p.rootSupport ≤ n)
    (hc : InfiniteConservation.crossingCount p (n+1) =
      InfiniteConservation.crossingCount p n) :
    p.root n = false ∧ fullInDegree p n = 2 ∧ fullOutDegree p n = 2 := by
  have h0 := conservation p n
  have h1 := conservation p (n+1)
  rw [roots_stable p n hn] at h0
  rw [roots_stable p (n+1) (by omega)] at h1
  change totalDefect p n + InfiniteConservation.crossingCount p n = _ at h0
  change totalDefect p (n+1) + InfiniteConservation.crossingCount p (n+1) = _ at h1
  have hs := total_defect_succ p n
  have hd : localDefect p n = 0 := by omega
  have hr := p.no_roots_after n hn
  have hi := full_indegree_lower p n hr
  have ho : fullOutDegree p n ≤ 2 := p.child_cap n
  simp only [localDefect, hr, Bool.false_eq_true, ↓reduceIte] at hd
  exact ⟨hr, by omega, by omega⟩

/-- A full outdegree supported at precisely the two possible forward positions. -/
theorem outdegree_short_edges {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (u : Nat) (hlong : ∀ v, u+3 ≤ v → p.edge u v = none) :
    fullOutDegree p u = edgeBit (p.edge u (u+1)) + edgeBit (p.edge u (u+2)) := by
  let f := fun v => edgeBit (p.edge u v)
  have hs : fullOutDegree p u = sumBelow (u+3) f := by
    apply Nat.le_antisymm
    · apply sumBelow_le_support f (u+3) (p.childSupport u)
      intro v hv
      simp [f, hlong v hv, edgeBit]
    · apply sumBelow_le_support f (p.childSupport u) (u+3)
      intro v hv
      simp [f, p.no_children_after u v hv, edgeBit]
  have hz : sumBelow (u+1) f = 0 := by
    calc
      _ = sumBelow (u+1) (fun _ => 0) := sumBelow_congr (fun v hv => by
        simp [f, no_parent_at_or_after p u v (by omega), edgeBit])
      _ = 0 := by simp
  rw [hs, show u+3 = (u+1)+2 by omega, sumBelow_shift, hz]
  simp [f, sumBelow_succ, Nat.add_assoc]

/-- Minimum crossing width on every cut of a root-free tail forces exactly
the +1 and +2 edges from every vertex of that same tail. -/
theorem minimum_tail_edges (p : InfiniteLabeledPopulation 2 2)
    (start : Nat) (hr : p.rootSupport ≤ start)
    (hc : ∀ n, start ≤ n → InfiniteConservation.crossingCount p n = 3) :
    ∀ u, start ≤ u → ∀ v,
      (p.edge u v).isSome = true ↔ v = u+1 ∨ v = u+2 := by
  intro u hu
  have hlong : ∀ v, u+3 ≤ v → p.edge u v = none := by
    intro v hv
    exact minimum_cut_no_late_target p (u+1) (by omega)
      (hc (u+1) (by omega)) u v (by omega) (by omega)
  have hregular := regular_of_equal_crossing p u (by omega)
    (by rw [hc u hu, hc (u+1) (by omega)])
  have hsum := outdegree_short_edges p u hlong
  rw [hregular.2.2] at hsum
  have hb1 := edgeBit_le_one (p.edge u (u+1))
  have hb2 := edgeBit_le_one (p.edge u (u+2))
  have hfirst : (p.edge u (u+1)).isSome = true := by
    cases he : p.edge u (u+1) with
    | none =>
      have hz : edgeBit (p.edge u (u+1)) = 0 := by rw [he]; rfl
      rw [hz] at hsum
      omega
    | some label => simp
  have hsecond : (p.edge u (u+2)).isSome = true := by
    cases he : p.edge u (u+2) with
    | none =>
      have hz : edgeBit (p.edge u (u+2)) = 0 := by rw [he]; rfl
      rw [hz] at hsum
      omega
    | some label => simp
  intro v
  constructor
  · intro he
    have ho := p.birth_order u v he
    by_cases hv : u+3 ≤ v
    · rw [hlong v hv] at he
      contradiction
    · omega
  · intro hv
    rcases hv with rfl | rfl
    · exact hfirst
    · exact hsecond

/-- An eventual minimum width, without a supplied root-free cutoff, still
forces an eventual exact underlying edge pattern. -/
theorem eventually_minimum_tail_edges (p : InfiniteLabeledPopulation 2 2)
    (hc : ∃ start, ∀ n, start ≤ n → InfiniteConservation.crossingCount p n = 3) :
    ∃ start, ∀ u, start ≤ u → ∀ v,
      (p.edge u v).isSome = true ↔ v = u+1 ∨ v = u+2 := by
  obtain ⟨s, hs⟩ := hc
  refine ⟨s+p.rootSupport, minimum_tail_edges p (s+p.rootSupport) (by omega) ?_⟩
  intro n hn
  exact hs n (by omega)

/-- No earlier exceptional source can remain a parent of the later tail. -/
theorem minimum_tail_parents (p : InfiniteLabeledPopulation 2 2)
    (start : Nat) (hr : p.rootSupport ≤ start)
    (hc : ∀ n, start ≤ n → InfiniteConservation.crossingCount p n = 3) :
    ∀ u, start ≤ u → ∀ a,
      (p.edge a (u+2)).isSome = true ↔ a = u ∨ a = u+1 := by
  intro u hu a
  constructor
  · intro he
    have hab := p.birth_order a (u+2) he
    by_cases hau : a < u
    · have hz := minimum_cut_no_late_target p u (by omega) (hc u hu)
        a (u+2) hau (by omega)
      rw [hz] at he
      contradiction
    · omega
  · intro ha
    rcases ha with ha | ha
    · rw [ha]
      exact (minimum_tail_edges p start hr hc u hu (u+2)).2 (Or.inr rfl)
    · rw [ha]
      exact (minimum_tail_edges p start hr hc (u+1) (by omega) (u+2)).2
        (Or.inl (by omega))

/-- Encode the two Boolean source genders as the model's labels 0 and 1. -/
def genderBit (b : Bool) : Nat := if b then 1 else 0

/-- Every outgoing label is the permanent gender of its source vertex. -/
def FixedSourceGender (p : InfiniteLabeledPopulation 2 2) (gender : Nat → Bool) : Prop :=
  ∀ u v, (p.edge u v).isSome = true → p.edge u v = some (genderBit (gender u))

/-- Required parents of both labels and minimum-width rigidity force alternating
permanent source genders on the same root-free tail. -/
theorem minimum_tail_genders (p : InfiniteLabeledPopulation 2 2)
    (gender : Nat → Bool) (hg : FixedSourceGender p gender)
    (start : Nat) (hr : p.rootSupport ≤ start)
    (hc : ∀ n, start ≤ n → InfiniteConservation.crossingCount p n = 3) :
    ∀ u, start ≤ u → gender (u+1) = !(gender u) := by
  intro u hu
  have hn := p.no_roots_after (u+2) (by omega)
  obtain ⟨a, ha⟩ := p.parent_of_label (u+2) hn 0 (by decide)
  obtain ⟨b, hb⟩ := p.parent_of_label (u+2) hn 1 (by decide)
  have hea : (p.edge a (u+2)).isSome = true := by rw [ha]; rfl
  have heb : (p.edge b (u+2)).isSome = true := by rw [hb]; rfl
  have hga := hg a (u+2) hea
  have hgb := hg b (u+2) heb
  rw [ha] at hga
  rw [hb] at hgb
  have hpa := (minimum_tail_parents p start hr hc u hu a).1 hea
  have hpb := (minimum_tail_parents p start hr hc u hu b).1 heb
  rcases hpa with hpa | hpa <;> rcases hpb with hpb | hpb <;>
    rw [hpa] at hga <;> rw [hpb] at hgb <;>
    cases h0 : gender u <;> cases h1 : gender (u+1) <;>
      simp [genderBit, h0, h1] at hga hgb ⊢

/-- The two actual Option-valued edge labels in the existing Boolean graph model. -/
def binaryEdge (p : InfiniteLabeledPopulation 2 2) : BinaryPopulation.LabelledGraph :=
  fun u v b => p.edge u v = some (genderBit b)

/-- Realization is exactly the existing Boolean labelled-path definition. -/
abbrev Realizes (p : InfiniteLabeledPopulation 2 2) (word : Nat → Bool) : Prop :=
  BinaryPopulation.Realizes (binaryEdge p) word

/-- Alternating source genders on the proved +1/+2 tail realize every word,
with a starting vertex above any requested natural bound. -/
theorem minimum_width_realizes_above (p : InfiniteLabeledPopulation 2 2)
    (gender : Nat → Bool) (hg : FixedSourceGender p gender)
    (start : Nat) (hr : p.rootSupport ≤ start)
    (hc : ∀ n, start ≤ n → InfiniteConservation.crossingCount p n = 3)
    (word : Nat → Bool) (requested : Nat) :
    ∃ path : Nat → Nat, requested ≤ path 0 ∧
      ∀ k, p.edge (path k) (path (k+1)) = some (genderBit (word k)) := by
  have halt := minimum_tail_genders p gender hg start hr hc
  have hpattern := minimum_tail_edges p start hr hc
  let base := start + requested
  let initial := if gender base = word 0 then base else base+1
  have hi : start ≤ initial ∧ requested ≤ initial ∧ gender initial = word 0 := by
    have ha := halt base (by dsimp [base]; omega)
    dsimp [initial]
    split
    · rename_i he
      exact ⟨by dsimp [base]; omega, by dsimp [base]; omega, he⟩
    · rename_i he
      refine ⟨by dsimp [base]; omega, by dsimp [base]; omega, ?_⟩
      cases h0 : gender base <;> cases h1 : word 0 <;> simp_all
  let next := fun (k u : Nat) => if gender (u+1) = word (k+1) then u+1 else u+2
  have hnext : ∀ k u, start ≤ u →
      start ≤ next k u ∧ gender (next k u) = word (k+1) ∧
      (p.edge u (next k u)).isSome = true := by
    intro k u hu
    have ha := halt (u+1) (by omega)
    dsimp [next]
    split
    · rename_i he
      exact ⟨by omega, he, (hpattern u hu (u+1)).2 (Or.inl rfl)⟩
    · rename_i he
      refine ⟨by omega, ?_, (hpattern u hu (u+2)).2 (Or.inr rfl)⟩
      have hab : gender (u+2) = !(gender (u+1)) := by simpa [Nat.add_assoc] using ha
      cases h0 : gender (u+1) <;> cases h1 : word (k+1) <;> simp_all
  let path : Nat → Nat := fun n => Nat.rec initial (fun k u => next k u) n
  have hp : ∀ k, start ≤ path k ∧ gender (path k) = word k := by
    intro k
    induction k with
    | zero => exact ⟨hi.1, hi.2.2⟩
    | succ k ih =>
      have h := hnext k (path k) ih.1
      exact ⟨h.1, h.2.1⟩
  refine ⟨path, hi.2.1, ?_⟩
  intro k
  have he := (hnext k (path k) (hp k).1).2.2
  have hl := hg (path k) (next k (path k)) he
  rw [(hp k).2] at hl
  exact hl

/-- Every Boolean word is realized in the fixed-gender minimum-width class. -/
theorem minimum_width_realizes_all (p : InfiniteLabeledPopulation 2 2)
    (gender : Nat → Bool) (hg : FixedSourceGender p gender)
    (hc : ∃ start, ∀ n, start ≤ n → InfiniteConservation.crossingCount p n = 3) :
    ∀ word, Realizes p word := by
  obtain ⟨s, hs⟩ := hc
  intro word
  obtain ⟨path, _, hp⟩ := minimum_width_realizes_above p gender hg (s+p.rootSupport)
    (by omega) (fun n hn => hs n (by omega)) word 0
  exact ⟨path, hp⟩

/-- A fixed-source-gender critical binary population avoiding even one word has
an eventual constant crossing width of at least four. -/
theorem avoiding_word_eventual_width_ge_four (p : InfiniteLabeledPopulation 2 2)
    (gender : Nat → Bool) (hg : FixedSourceGender p gender)
    (word : Nat → Bool) (ha : ¬Realizes p word) :
    ∃ start, 4 ≤ InfiniteConservation.crossingCount p start ∧
      ∀ n, start ≤ n →
        InfiniteConservation.crossingCount p n = InfiniteConservation.crossingCount p start := by
  obtain ⟨s, hs⟩ := eventual_constant_crossing p
  let start := s + p.rootSupport
  have hsr : p.rootSupport ≤ start := by dsimp [start]; omega
  have hss : s ≤ start := by dsimp [start]; omega
  have hc : ∀ n, start ≤ n →
      InfiniteConservation.crossingCount p n = InfiniteConservation.crossingCount p start := by
    intro n hn
    rw [hs n (by omega), hs start hss]
  have hl := binary_crossing_lower p start hsr
  have hne : InfiniteConservation.crossingCount p start ≠ 3 := by
    intro he
    have hm : ∃ start, ∀ n, start ≤ n → InfiniteConservation.crossingCount p n = 3 := by
      refine ⟨start, ?_⟩
      intro n hn
      rw [hc n hn, he]
    exact ha (minimum_width_realizes_all p gender hg hm word)
  exact ⟨start, by omega, hc⟩

#print axioms minimum_cut_internal_edge
#print axioms minimum_cut_no_late_target
#print axioms minimum_tail_edges
#print axioms eventually_minimum_tail_edges
#print axioms minimum_tail_parents
#print axioms minimum_tail_genders
#print axioms minimum_width_realizes_above
#print axioms minimum_width_realizes_all
#print axioms avoiding_word_eventual_width_ge_four

end MinimalCrossing
