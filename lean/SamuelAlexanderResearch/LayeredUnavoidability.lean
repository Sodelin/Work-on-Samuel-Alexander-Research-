import SamuelAlexanderResearch.PositiveUnavoidability

/-! Strict consecutive generations realize every binary word. This checks
the binary specialization of the written layering comparison; it does not
claim universality merely from connectedness or the presence of generations. -/

namespace LayeredUnavoidability
open SpeciesBridge BinaryPopulation PositiveUnavoidability

def ConsecutiveLayers (E : LabelledGraph) (layer : Nat → Nat) : Prop :=
  ∀ u v b, E u v b → layer v = layer u + 1

theorem zero_layer_root {E : LabelledGraph} {layer : Nat → Nat}
    (hl : ConsecutiveLayers E layer) {v : Nat} (hv : layer v = 0) :
    Root (ForgetLabels E) v := by
  intro u ⟨b, he⟩
  have := hl u v b he
  omega

theorem finitePath_length_le_endpoint {E : LabelledGraph} {s : Nat → Bool}
    (strict : ∀ u v b, E u v b → u < v)
    {k n u v : Nat} (path : FinitePath E s k n u v) : u + n ≤ v := by
  induction path with
  | nil => omega
  | cons he _ ih => have := strict _ _ _ he; omega

/-- Backward parent choices land in generation zero with the correct forward word. -/
theorem backward_from_layer (E : LabelledGraph) (population : BinaryNatPopulation E)
    (layer : Nat → Nat) (hl : ConsecutiveLayers E layer)
    (root_layer : ∀ v, Root (ForgetLabels E) v → layer v = 0)
    (s : Nat → Bool) (n : Nat) :
    ∀ v, layer v = n → ∃ u, layer u = 0 ∧ FinitePath E s 0 n u v := by
  induction n with
  | zero => intro v hv; exact ⟨v, hv, .nil _ _⟩
  | succ n ih =>
    intro v hv
    have hnonroot : ¬ Root (ForgetLabels E) v := by
      intro hr
      have := root_layer v hr
      omega
    obtain ⟨parent, he⟩ := population.2.2.2 v hnonroot (s n)
    have hp : layer parent = n := by have := hl parent v (s n) he; omega
    obtain ⟨u, hu, path⟩ := ih parent hp
    exact ⟨u, hu, path.snoc (by simpa using he)⟩

/-- Every word is realized, with no periodicity condition. New roots in later
layers are excluded explicitly; every finite layer depth has a vertex. -/
theorem every_word_realized (E : LabelledGraph) (population : BinaryNatPopulation E)
    (layer : Nat → Nat) (hl : ConsecutiveLayers E layer)
    (root_layer : ∀ v, Root (ForgetLabels E) v → layer v = 0)
    (populated : ∀ n, ∃ v, layer v = n) (s : Nat → Bool) : Realizes E s := by
  classical
  obtain ⟨rootBound, hroot⟩ := (finiteSupport_iff_bounded _).mp population.2.2.1
  have hex : ∃ u, u < rootBound ∧ Good E s 0 u := by
    apply Classical.byContradiction
    intro hnone
    have bounded : ∀ u, u < rootBound → ∃ b, ∀ w, Endpoint E s 0 u w → w < b := by
      intro u hu
      have hn : ¬ Good E s 0 u := fun hg => hnone ⟨u, hu, hg⟩
      exact Classical.byContradiction (fun h => hn h)
    obtain ⟨ceiling, hc⟩ := finite_union_bound (fun u w => Endpoint E s 0 u w)
      rootBound bounded
    obtain ⟨v, hv⟩ := populated ceiling
    obtain ⟨u, hu, path⟩ := backward_from_layer E population layer hl root_layer s ceiling v hv
    have hub := hroot u (zero_layer_root hl hu)
    have below := hc u hub v ⟨ceiling, path⟩
    have above := finitePath_length_le_endpoint
      (fun u v b he => population.2.1.1 u v ⟨b, he⟩) path
    omega
  obtain ⟨u, _, good⟩ := hex
  obtain ⟨path, _, hp⟩ := infinite_path_from_good E s population.2.1.2.2.1 0 u good
  exact ⟨path, by simpa using hp⟩

end LayeredUnavoidability
