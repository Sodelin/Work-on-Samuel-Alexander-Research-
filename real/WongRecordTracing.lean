import WongSampleTracing

/-! Executable interval-record scanning followed by Appendix E sample tracing.
The list contains the actual interval records, not an assumed parent oracle. -/
namespace WongRecordTracing
open WongGARG WongSampleTracing
universe u v
variable {Node : Type u} {Coord : Type v} [DecidableEq Node] [LinearOrder Coord]

def covers (e : EdgeRecord Node Coord) (x : Coord) : Bool :=
  decide (∃ I ∈ e.regions, I.lo ≤ x ∧ x < I.hi)

omit [DecidableEq Node] in
@[simp] theorem covers_true (e : EdgeRecord Node Coord) (x : Coord) :
    covers e x = true ↔ e.Covers x := by
  simp [covers, EdgeRecord.Covers, Interval.Contains]

/-- Scan stored records in list order and return the first matching parent.
On inputs with a unique parent per locus, list order cannot change the result. -/
def lookup (records : List (EdgeRecord Node Coord)) (x : Coord) (c : Node) : Option Node :=
  match records with
  | [] => none
  | e :: rest => if e.child = c ∧ covers e x = true then some e.parent else lookup rest x c

theorem lookup_sound (records : List (EdgeRecord Node Coord)) (x : Coord)
    (p c : Node) (h : lookup records x c = some p) :
    ∃ e ∈ records, e.parent = p ∧ e.child = c ∧ e.Covers x := by
  induction records with
  | nil => simp [lookup] at h
  | cons e rest ih =>
    simp only [lookup] at h
    split at h
    · rename_i he
      exact ⟨e, List.mem_cons_self, Option.some.inj h, he.1, (covers_true e x).mp he.2⟩
    · obtain ⟨r, hr, hp, hc, hx⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem e hr, hp, hc, hx⟩

section GARG
variable [Fintype Node]

theorem lookup_complete (G : GARG Node Coord) (x : Coord) (unique : G.UniqueParentAt x)
    (records : List (EdgeRecord Node Coord))
    (valid : ∀ e ∈ records, e ∈ G.records)
    (p c : Node)
    (existsRecord : ∃ e ∈ records, e.parent = p ∧ e.child = c ∧ e.Covers x) :
    lookup records x c = some p := by
  induction records with
  | nil =>
    obtain ⟨r, hr, _⟩ := existsRecord
    simp at hr
  | cons e rest ih =>
    by_cases hit : e.child = c ∧ covers e x = true
    · obtain ⟨r, hr, hp, hc, hx⟩ := existsRecord
      have first : G.AtLocus x e.parent c :=
        ⟨e, valid e List.mem_cons_self, rfl, hit.1, (covers_true e x).mp hit.2⟩
      have target : G.AtLocus x p c := ⟨r, valid r hr, hp, hc, hx⟩
      have ep := unique c e.parent p first target
      simp [lookup, hit, ep]
    · have htail : ∃ r ∈ rest, r.parent = p ∧ r.child = c ∧ r.Covers x := by
        obtain ⟨r, hr, hp, hc, hx⟩ := existsRecord
        rcases List.mem_cons.mp hr with heq | hr
        · subst r
          exact False.elim (hit ⟨hc, (covers_true e x).mpr hx⟩)
        · exact ⟨r, hr, hp, hc, hx⟩
      simp only [lookup, if_neg hit]
      exact ih (fun r hr => valid r (List.mem_cons_of_mem e hr)) htail

theorem lookup_represents (G : GARG Node Coord) (x : Coord) (unique : G.UniqueParentAt x)
    (records : List (EdgeRecord Node Coord))
    (recordIds : ∀ e, e ∈ records ↔ e ∈ G.records) (p c : Node) :
    lookup records x c = some p ↔ G.AtLocus x p c := by
  constructor
  · intro h
    obtain ⟨e, he, hp, hc, hx⟩ := lookup_sound records x p c h
    exact ⟨e, (recordIds e).mp he, hp, hc, hx⟩
  · rintro ⟨e, he, hp, hc, hx⟩
    exact lookup_complete G x unique records (fun e he => (recordIds e).mp he) p c
      ⟨e, (recordIds e).mpr he, hp, hc, hx⟩

/-- End-to-end correctness from actual finite interval records to the persistent
sample parent array. The sample IDs and record IDs are checked enumerations. -/
theorem records_to_sample_array (G : GARG Node Coord) (x : Coord)
    (unique : G.UniqueParentAt x) (records : List (EdgeRecord Node Coord))
    (recordIds : ∀ e, e ∈ records ↔ e ∈ G.records)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples)
    (p c : Node) :
    extract (lookup records x) (Fintype.card Node) samples c = some p ↔
      G.ExtractedAt x p c :=
  actual_garg_extraction G x (lookup records x)
    (lookup_represents G x unique records recordIds) samples sampleIds p c

/-- Complete indexed parent arrays recover the original indexed inheritance
exactly when no annotated inheritance is unsupported by the samples. -/
theorem records_round_trip_iff (G : GARG Node Coord)
    (unique : ∀ x, G.UniqueParentAt x) (records : List (EdgeRecord Node Coord))
    (recordIds : ∀ e, e ∈ records ↔ e ∈ G.records)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples) :
    (∀ x p c, extract (lookup records x) (Fintype.card Node) samples c = some p ↔
      G.AtLocus x p c) ↔ G.SampleSupported :=
  actual_garg_reconstruction_iff G (lookup records)
    (fun x => lookup_represents G x (unique x) records recordIds) samples sampleIds
end GARG

private def exampleRecord (p c : Fin 4) : EdgeRecord (Fin 4) Nat where
  parent := p
  child := c
  regions := {⟨0, 10, by decide⟩}
  disjoint := by
    intro I hI J hJ hne
    have hi : I = ⟨0, 10, by decide⟩ := Finset.mem_singleton.mp hI
    have hj : J = ⟨0, 10, by decide⟩ := Finset.mem_singleton.mp hJ
    exact False.elim (hne (hi.trans hj.symm))

example : List.ofFn (extract (lookup [exampleRecord 0 1, exampleRecord 1 2,
    exampleRecord 1 3] 2) 4 [2]) = [none, some 0, some 1, none] := by
  decide

end WongRecordTracing
