import FairDivision.Topology.Volovikov.JoinFaceAction

/-!
# Representatives and unique translators of universal-join face orbits

The translation action is free on nonempty faces. Thus a chosen face
representative and a face in its orbit determine one group element uniquely.
This is the algebraic bookkeeping for extending a map equivariantly over one
orbit of simplex cells at a time.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- A nonempty face of the finite universal join. -/
abbrev UniversalJoinFace (m : ℕ) (G : Type*) :=
  {S : Finset (Fin m × G) // IsUniversalJoinFace S}

/-- Two join faces lie in the same orbit under group translation. -/
def universalJoinFaceOrbitSetoid (m : ℕ) (G : Type*)
    [AddGroup G] :
    Setoid (UniversalJoinFace m G) where
  r S T := ∃ a : G, translateJoinFace a S.1 = T.1
  iseqv := by
    constructor
    · intro S
      exact ⟨0, translateJoinFace_zero S.1⟩
    · intro S T h
      obtain ⟨a, ha⟩ := h
      refine ⟨-a, ?_⟩
      calc
        translateJoinFace (-a) T.1 =
            translateJoinFace (-a) (translateJoinFace a S.1) := by rw [ha]
        _ = S.1 := by
          rw [← translateJoinFace_add, neg_add_cancel,
            translateJoinFace_zero]
    · intro S T U hST hTU
      obtain ⟨a, ha⟩ := hST
      obtain ⟨b, hb⟩ := hTU
      refine ⟨b + a, ?_⟩
      rw [translateJoinFace_add, ha, hb]

/-- A chosen representative in the orbit of a join face. -/
noncomputable def universalJoinFaceOrbitRep {m : ℕ} {G : Type*}
    [AddGroup G]
    (S : UniversalJoinFace m G) : UniversalJoinFace m G :=
  Quotient.out (Quotient.mk (universalJoinFaceOrbitSetoid m G) S)

/-- The canonical representative really lies in the given face's orbit. -/
theorem universalJoinFaceOrbitRep_related {m : ℕ} {G : Type*}
    [AddGroup G]
    (S : UniversalJoinFace m G) :
    ∃ a : G, translateJoinFace a
      (universalJoinFaceOrbitRep S).1 = S.1 := by
  exact Quotient.exact
    (Quotient.out_eq
      (Quotient.mk (universalJoinFaceOrbitSetoid m G) S))

/-- The unique group element carrying the chosen representative to a face. -/
noncomputable def universalJoinFaceTranslator {m : ℕ} {G : Type*}
    [AddGroup G]
    (S : UniversalJoinFace m G) : G :=
  Classical.choose (universalJoinFaceOrbitRep_related S)

/-- The chosen translator carries the representative to the face. -/
theorem universalJoinFaceTranslator_spec {m : ℕ} {G : Type*}
    [AddGroup G]
    (S : UniversalJoinFace m G) :
    translateJoinFace (universalJoinFaceTranslator S)
      (universalJoinFaceOrbitRep S).1 = S.1 :=
  Classical.choose_spec (universalJoinFaceOrbitRep_related S)

/-- The chosen orbit representative has the same number of vertices as
its face. -/
theorem universalJoinFaceOrbitRep_card {m : ℕ} {G : Type*}
    [AddGroup G]
    (S : UniversalJoinFace m G) :
    (universalJoinFaceOrbitRep S).1.card = S.1.card := by
  calc
    (universalJoinFaceOrbitRep S).1.card =
        (translateJoinFace (universalJoinFaceTranslator S)
          (universalJoinFaceOrbitRep S).1).card :=
      (translateJoinFace_card _ _).symm
    _ = S.1.card := congrArg Finset.card
      (universalJoinFaceTranslator_spec S)

/-- Orbit representatives agree for faces related by a translation. -/
theorem universalJoinFaceOrbitRep_eq {m : ℕ} {G : Type*}
    [AddGroup G]
    (S T : UniversalJoinFace m G) (a : G)
    (h : translateJoinFace a S.1 = T.1) :
    universalJoinFaceOrbitRep S = universalJoinFaceOrbitRep T := by
  unfold universalJoinFaceOrbitRep
  exact congrArg Quotient.out (Quotient.sound ⟨a, h⟩)

/-- Translation changes the unique representative-to-face translator by
left addition of the translating group element. -/
theorem universalJoinFaceTranslator_translate {m : ℕ} {G : Type*}
    [AddGroup G]
    (S T : UniversalJoinFace m G) (a : G)
    (h : translateJoinFace a S.1 = T.1) :
    universalJoinFaceTranslator T =
      a + universalJoinFaceTranslator S := by
  have hrep := universalJoinFaceOrbitRep_eq S T a h
  apply translateJoinFace_unique
    (universalJoinFaceOrbitRep T).1
    (universalJoinFaceOrbitRep T).2
  calc
    translateJoinFace (universalJoinFaceTranslator T)
        (universalJoinFaceOrbitRep T).1 = T.1 :=
      universalJoinFaceTranslator_spec T
    _ = translateJoinFace a S.1 := h.symm
    _ = translateJoinFace a
        (translateJoinFace (universalJoinFaceTranslator S)
          (universalJoinFaceOrbitRep S).1) := by
      rw [universalJoinFaceTranslator_spec]
    _ = translateJoinFace (a + universalJoinFaceTranslator S)
        (universalJoinFaceOrbitRep T).1 := by
      rw [← translateJoinFace_add, hrep]

end FairDivision.Topology.Volovikov
