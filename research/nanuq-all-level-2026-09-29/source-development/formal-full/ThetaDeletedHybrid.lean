import ThetaSourceUnbounded

/-! Deleting the second hybrid removes its switching choice exactly. These
lemmas concern the concrete path and quartet evaluator; raw cycle-graph
classification and suppression correspondence remain separate obligations. -/
namespace Nanuq.Theta

/-- The second switching bit only changes the terminal path of c2. -/
theorem terminalPath_second_independent (t : Counts) (first second other : Bool)
    (x : Leaf) (hx : x ≠ Leaf.c2) :
    terminalPath t (first,second) x = terminalPath t (first,other) x := by
  cases x <;> simp_all [terminalPath]

theorem treeDistance_second_independent (t : Counts) (first second other : Bool)
    (x y : Leaf) (hx : x ≠ Leaf.c2) (hy : y ≠ Leaf.c2) :
    treeDistance t (first,second) x y = treeDistance t (first,other) x y := by
  unfold treeDistance
  rw [terminalPath_second_independent t first second other x hx,
    terminalPath_second_independent t first second other y hy]

theorem quartet_second_independent (t : Counts) (first second other : Bool)
    (a b c d : Leaf) (ha : a ≠ Leaf.c2) (hb : b ≠ Leaf.c2)
    (hc : c ≠ Leaf.c2) (hd : d ≠ Leaf.c2) :
    quartet t (first,second) a b c d = quartet t (first,other) a b c d := by
  dsimp only [quartet]
  rw [treeDistance_second_independent t first second other a b ha hb,
    treeDistance_second_independent t first second other c d hc hd,
    treeDistance_second_independent t first second other a c ha hc,
    treeDistance_second_independent t first second other b d hb hd,
    treeDistance_second_independent t first second other a d ha hd,
    treeDistance_second_independent t first second other b c hb hc]

theorem sourceResolution_second_independent (t : Counts) (first second other : Bool)
    (a b c d : Leaf) (ha : a ≠ Leaf.c2) (hb : b ≠ Leaf.c2)
    (hc : c ≠ Leaf.c2) (hd : d ≠ Leaf.c2) :
    sourceResolution t a b c d (first,second) = sourceResolution t a b c d (first,other) := by
  simp only [sourceResolution,quartet_second_independent t first second other a b c d ha hb hc hd]

/-- Surjectively discarding the irrelevant bit preserves the set of distinct
resolutions and its source mean, including the case where the two choices agree. -/
theorem sourceMean_two_switchings (t : Counts) (a b c d : Leaf)
    (ha : a ≠ Leaf.c2) (hb : b ≠ Leaf.c2) (hc : c ≠ Leaf.c2) (hd : d ≠ Leaf.c2) :
    Nanuq.Quartet.sourceMean (sourceResolution t a b c d) =
      Nanuq.Quartet.sourceMean (fun first : Bool => sourceResolution t a b c d (first,false)) := by
  have he : sourceResolution t a b c d =
      fun s : Switching => sourceResolution t a b c d (s.1,false) := by
    funext s
    exact sourceResolution_second_independent t s.1 s.2 false a b c d ha hb hc hd
  calc
    Nanuq.Quartet.sourceMean (sourceResolution t a b c d) =
        Nanuq.Quartet.sourceMean (fun s : Switching => sourceResolution t a b c d (s.1,false)) :=
      congrArg Nanuq.Quartet.sourceMean he
    _ = Nanuq.Quartet.sourceMean (fun first : Bool => sourceResolution t a b c d (first,false)) :=
      Nanuq.Quartet.sourceMean_prod_fst (S := Bool) (T := Bool)
        (fun first : Bool => sourceResolution t a b c d (first,false))

/-- Direct source semantics for a quartet retained after deleting c2. -/
theorem rhoFin_two_switchings (t : Counts) (a b c d : Fin (circular t).length)
    (ha : leafIndex t a ≠ Leaf.c2) (hb : leafIndex t b ≠ Leaf.c2)
    (hc : leafIndex t c ≠ Leaf.c2) (hd : leafIndex t d ≠ Leaf.c2)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    rhoFin t a b c d = Nanuq.Quartet.sourceMean
      (fun first : Bool => sourceResolution t (leafIndex t a) (leafIndex t b)
        (leafIndex t c) (leafIndex t d) (first,false)) := by
  rw [rhoFin_source t a b c d hab hac had hbc hbd hcd]
  exact sourceMean_two_switchings t _ _ _ _ ha hb hc hd

def oneCycleLeaves (a b : Nat) : List Leaf :=
  [Leaf.c1] ++ ((List.range b).reverse.map (Leaf.arm 1)) ++
    ((List.range a).map (Leaf.arm 0))

/-- The retained order is exactly c1, reversed second arm, first arm. -/
theorem delete_c2_circular (a b : Nat) :
    (circular ⟨a,b,0,0⟩).filter (fun l => decide (l ≠ Leaf.c2)) = oneCycleLeaves a b := by
  have hf (k : Fin 4) (l : List Nat) :
      (l.map (Leaf.arm k)).filter (fun x => decide (x ≠ Leaf.c2)) = l.map (Leaf.arm k) := by
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨r,_hr,rfl⟩ := List.mem_map.mp hx
    simp
  simp only [ne_eq,decide_not] at hf
  simp [circular,oneCycleLeaves,List.filter_append,hf]

#print axioms quartet_second_independent
#print axioms rhoFin_two_switchings
#print axioms delete_c2_circular
end Nanuq.Theta