import ThetaCompression
import AnchorIndexTransport
import ZeroTheta
import ThetaSourceExact

/-! Source correctness for arbitrary canonical theta arm lengths. -/
namespace Nanuq.Theta

/-- Every switched restriction of four distinct taxa is a resolved quartet.
The four taxa and the two hybrids suffice to invoke the finite checker; exact
compression transports its conclusion to arbitrary original arm lengths. -/
theorem quartet_resolves (t : Counts) (a b c d : Fin (circular t).length)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (s : Switching) :
    (quartet t s (leafIndex t a) (leafIndex t b) (leafIndex t c) (leafIndex t d)).isSome = true := by
  let W : Finset Leaf :=
    [leafIndex t a, leafIndex t b, leafIndex t c, leafIndex t d, Leaf.c1, Leaf.c2].toFinset
  have hvalid : ∀ l ∈ W, l ∈ circular t := by
    intro l hl
    simp only [W, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact leafIndex_mem_circular t _ | simp [circular]
  have hc1 : Leaf.c1 ∈ W := by simp [W]
  have hc2 : Leaf.c2 ∈ W := by simp [W]
  have ha : leafIndex t a ∈ W := by simp [W]
  have hb : leafIndex t b ∈ W := by simp [W]
  have hc : leafIndex t c ∈ W := by simp [W]
  have hd : leafIndex t d ∈ W := by simp [W]
  let u := compressedCounts W
  let ix (x : Fin (circular t).length) (hx : leafIndex t x ∈ W) :=
    compressedIndex t W hvalid hc1 hc2 x hx
  have himage (x : Fin (circular t).length) (hx : leafIndex t x ∈ W) :
      leafIndex u (ix x hx) = compressLeaf W (leafIndex t x) :=
    leafIndex_compressedIndex t W hvalid hc1 hc2 x hx
  have hine {x y : Fin (circular t).length} (hx : leafIndex t x ∈ W)
      (hy : leafIndex t y ∈ W) (hne : x ≠ y) : ix x hx ≠ ix y hy := by
    intro he
    have he' := congrArg (leafIndex u) he
    rw [himage, himage] at he'
    exact hne (leafIndex_injective t (compressLeaf_injective_on W hx hy he'))
  have hsize : u.total ≤ 6 :=
    (compressedCounts_total_le W).trans (List.toFinset_card_le _)
  have hparts : checkQuartets u = true ∧ checkAnchors u = true := by
    simpa only [checkTemplate, Bool.and_eq_true] using check_template_upto_six u hsize
  have hr := resolves_of_check hparts.1
    (ix a ha).val (ix b hb).val (ix c hc).val (ix d hd).val
    (ix a ha).isLt (ix b hb).isLt (ix c hc).isLt (ix d hd).isLt
    (fun he => hine ha hb hab (Fin.ext he))
    (fun he => hine ha hc hac (Fin.ext he))
    (fun he => hine ha hd had (Fin.ext he))
    (fun he => hine hb hc hbc (Fin.ext he))
    (fun he => hine hb hd hbd (Fin.ext he))
    (fun he => hine hc hd hcd (Fin.ext he)) s
  change (quartet u s (leafIndex u (ix a ha)) (leafIndex u (ix b hb))
    (leafIndex u (ix c hc)) (leafIndex u (ix d hd))).isSome = true at hr
  rw [himage, himage, himage, himage] at hr
  rw [quartet_compression t W hvalid s _ _ _ _ ha hb hc hd
    (fun h => hab (leafIndex_injective t h))
    (fun h => hac (leafIndex_injective t h))
    (fun h => had (leafIndex_injective t h))
    (fun h => hbc (leafIndex_injective t h))
    (fun h => hbd (leafIndex_injective t h))
    (fun h => hcd (leafIndex_injective t h))]
  exact hr

/-- The actual arbitrary-arm tensor is exactly the source's mean over distinct
displayed quartet resolutions; there is no unresolved-quartet fallback. -/
theorem rhoFin_source (t : Counts) (a b c d : Fin (circular t).length)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    rhoFin t a b c d = Nanuq.Quartet.sourceMean
      (sourceResolution t (leafIndex t a) (leafIndex t b) (leafIndex t c) (leafIndex t d)) := by
  have hr := quartet_resolves t a b c d hab hac had hbc hbd hcd
  obtain ⟨r00,h00⟩ := Option.isSome_iff_exists.mp (hr (false,false))
  obtain ⟨r01,h01⟩ := Option.isSome_iff_exists.mp (hr (false,true))
  obtain ⟨r10,h10⟩ := Option.isSome_iff_exists.mp (hr (true,false))
  obtain ⟨r11,h11⟩ := Option.isSome_iff_exists.mp (hr (true,true))
  have he := rho2_eq_sourceMean_of_resolves t _ _ _ _ r00 r01 r10 r11 h00 h01 h10 h11
  unfold rhoFin
  rw [he]
  ring

#print axioms quartet_resolves
#print axioms rhoFin_source
end Nanuq.Theta