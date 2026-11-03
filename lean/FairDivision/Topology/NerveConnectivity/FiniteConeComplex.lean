import FairDivision.Topology.NerveConnectivity.SimplicialCover

/-!
# The finite simplicial cone

The cone has one new vertex `none`; every old vertex is `some v`.
An apex-only face is present even when the base complex is empty.
This representation is useful for extending a map on a subdivided source
sphere into a map on a ball without invoking a general CW-complex library.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u

/-- The old vertices in a face of an Option-vertex cone. -/
noncomputable def coneBaseFace {V : Type u} [Fintype V]
    (S : Finset (Option V)) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => some v ∈ S)

@[simp] theorem mem_coneBaseFace {V : Type u} [Fintype V]
    {S : Finset (Option V)} {v : V} :
    v ∈ coneBaseFace S ↔ some v ∈ S := by
  classical
  simp [coneBaseFace]

theorem coneBaseFace_mono {V : Type u} [Fintype V]
    {S T : Finset (Option V)} (hST : S ⊆ T) :
    coneBaseFace S ⊆ coneBaseFace T := by
  intro v hv
  exact mem_coneBaseFace.mpr (hST (mem_coneBaseFace.mp hv))


/-- A cone face has at most one more vertex than its base face. -/
theorem coneFace_card_le {V : Type u} [Fintype V]
    (S : Finset (Option V)) :
    S.card ≤ (coneBaseFace S).card + 1 := by
  classical
  have hsub : S ⊆ insert none ((coneBaseFace S).image some) := by
    intro x hx
    cases x with
    | none => simp
    | some v =>
      simp only [Finset.mem_insert, Option.some_ne_none, false_or,
        Finset.mem_image]
      exact ⟨v, mem_coneBaseFace.mpr hx, rfl⟩
  calc
    S.card ≤ (insert none ((coneBaseFace S).image some)).card :=
      Finset.card_le_card hsub
    _ ≤ ((coneBaseFace S).image some).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (coneBaseFace S).card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1

/-- All nonempty base faces and their apex cones, together with the apex. -/
noncomputable def finiteConeComplex {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (Option V) where
  faces := {S | S.Nonempty ∧
    ((coneBaseFace S).Nonempty → coneBaseFace S ∈ K)}
  isRelLowerSet_faces := by
    intro S hS
    constructor
    · exact hS.1
    · intro T hTS hT
      refine ⟨hT, ?_⟩
      intro hTbase
      have hSbase : (coneBaseFace S).Nonempty :=
        hTbase.mono (coneBaseFace_mono hTS)
      exact (K.isRelLowerSet_faces (hS.2 hSbase)).2
        (coneBaseFace_mono hTS) hTbase

@[simp] theorem mem_finiteConeComplex_iff {V : Type u} [Fintype V]
    {K : PreAbstractSimplicialComplex V} {S : Finset (Option V)} :
    S ∈ finiteConeComplex K ↔
      S.Nonempty ∧ ((coneBaseFace S).Nonempty → coneBaseFace S ∈ K) :=
  Iff.rfl

theorem finiteConeComplex_mono {V : Type u} [Fintype V]
    {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L) :
    finiteConeComplex K ≤ finiteConeComplex L := by
  intro S hS
  exact ⟨hS.1, fun hbase => hKL (hS.2 hbase)⟩


/-- Coning a complex increases its face-cardinality bound by one. -/
theorem finiteConeComplex_card_le {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (d : ℕ)
    (hKdim : ∀ F : Finset V, F ∈ K → F.card ≤ d) :
    ∀ S : Finset (Option V), S ∈ finiteConeComplex K →
      S.card ≤ d + 1 := by
  intro S hS
  have hcard := coneFace_card_le S
  by_cases hb : (coneBaseFace S).Nonempty
  · have hdim := hKdim (coneBaseFace S) (hS.2 hb)
    omega
  · have hz : (coneBaseFace S).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hb)
    omega

theorem finiteConeComplex_sup {V : Type u} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    finiteConeComplex (K ⊔ L) =
      finiteConeComplex K ⊔ finiteConeComplex L := by
  ext S
  constructor
  · intro hS
    by_cases hbase : (coneBaseFace S).Nonempty
    · rcases hS.2 hbase with hK | hL
      · exact Or.inl ⟨hS.1, fun _ => hK⟩
      · exact Or.inr ⟨hS.1, fun _ => hL⟩
    · exact Or.inl ⟨hS.1, fun hb => (hbase hb).elim⟩
  · intro hS
    rcases hS with hK | hL
    · exact ⟨hK.1, fun hb => Or.inl (hK.2 hb)⟩
    · exact ⟨hL.1, fun hb => Or.inr (hL.2 hb)⟩

theorem finiteConeComplex_inf {V : Type u} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    finiteConeComplex (K ⊓ L) =
      finiteConeComplex K ⊓ finiteConeComplex L := by
  ext S
  constructor
  · intro hS
    exact ⟨⟨hS.1, fun hb => (hS.2 hb).1⟩,
      ⟨hS.1, fun hb => (hS.2 hb).2⟩⟩
  · intro hS
    exact ⟨hS.1.1, fun hb => ⟨hS.1.2 hb, hS.2.2 hb⟩⟩

/-- The base copy of a complex, with the new apex excluded. -/
noncomputable def finiteConeBaseComplex {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (Option V) where
  faces := {S | S.Nonempty ∧ none ∉ S ∧ coneBaseFace S ∈ K}
  isRelLowerSet_faces := by
    intro S hS
    constructor
    · exact hS.1
    · intro T hTS hT
      have hTbase : (coneBaseFace T).Nonempty := by
        rcases hT with ⟨v, hv⟩
        cases v with
        | none => exact (hS.2.1 (hTS hv)).elim
        | some v => exact ⟨v, mem_coneBaseFace.mpr hv⟩
      exact ⟨hT, fun hn => hS.2.1 (hTS hn),
        (K.isRelLowerSet_faces hS.2.2).2
          (coneBaseFace_mono hTS) hTbase⟩

theorem finiteConeBaseComplex_le {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    finiteConeBaseComplex K ≤ finiteConeComplex K := by
  intro S hS
  exact ⟨hS.1, fun _ => hS.2.2⟩


@[simp] theorem coneBaseFace_image_some {V : Type u} [Fintype V] [DecidableEq V]
    (S : Finset V) :
    coneBaseFace (S.image some) = S := by
  classical
  ext v
  simp [coneBaseFace]

/-- The base copy has exactly the old faces. -/
theorem mem_finiteConeBaseComplex_image_some_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    (K : PreAbstractSimplicialComplex V) (S : Finset V) :
    S.image some ∈ finiteConeBaseComplex K ↔ S ∈ K := by
  classical
  constructor
  · intro h
    simpa [coneBaseFace_image_some] using h.2.2
  · intro h
    obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces h).1
    refine ⟨⟨some v, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩, ?_, ?_⟩
    · simp
    · simpa [coneBaseFace_image_some] using h

/-- A face of the base complex is an old face, with `some` applied to each vertex. -/
theorem finiteConeBaseComplex_face_image {V : Type u} [Fintype V] [DecidableEq V]
    (K : PreAbstractSimplicialComplex V)
    {S : Finset (Option V)} (hS : S ∈ finiteConeBaseComplex K) :
    S = (coneBaseFace S).image some := by
  classical
  ext x
  cases x with
  | none => simp [hS.2.1]
  | some v => simp [mem_coneBaseFace]

theorem finiteConeBaseComplex_card_le {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (d : ℕ)
    (hKdim : ∀ F : Finset V, F ∈ K → F.card ≤ d) :
    ∀ S : Finset (Option V), S ∈ finiteConeBaseComplex K →
      S.card ≤ d := by
  classical
  intro S hS
  rw [finiteConeBaseComplex_face_image K hS]
  exact (Finset.card_image_le (s := coneBaseFace S) (f := (some : V → Option V))).trans
    (hKdim _ hS.2.2)

@[simp] theorem coneBaseFace_insert_none {V : Type u} [Fintype V] [DecidableEq V]
    (S : Finset (Option V)) :
    coneBaseFace (insert none S) = coneBaseFace S := by
  classical
  ext v
  simp [coneBaseFace]

/-- Adding the apex to any cone face gives another cone face. -/
theorem finiteConeComplex_insert_apex {V : Type u} [Fintype V] [DecidableEq V]
    (K : PreAbstractSimplicialComplex V)
    {S : Finset (Option V)} (hS : S ∈ finiteConeComplex K) :
    insert none S ∈ finiteConeComplex K := by
  refine ⟨⟨none, Finset.mem_insert_self _ _⟩, ?_⟩
  simpa [coneBaseFace_insert_none] using hS.2

/-- The new apex is always a face of the cone. -/
theorem finiteConeComplex_apex {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    ({none} : Finset (Option V)) ∈ finiteConeComplex K := by
  classical
  refine ⟨Finset.singleton_nonempty _, ?_⟩
  simp [coneBaseFace]

end FairDivision.Topology.NerveConnectivity
