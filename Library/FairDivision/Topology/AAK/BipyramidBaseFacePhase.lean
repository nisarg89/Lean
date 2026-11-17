import FairDivision.Topology.AAK.BipyramidCyclicFaces

/-!
# Orbit phases for the proper base faces of the bipyramid

The representative/translator construction reuses the same quotient-choice
argument as `Volovikov/JoinFaceOrbits`. Freeness is supplied by the concrete
prime-cyclic bipyramid face theorem. It is applied only to base-only faces,
which have cardinality between 1 and p−1.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.ZeroFreeBipyramid

open scoped Classical

variable (p : ℕ) [Fact p.Prime]

/-- A nonempty proper base face, with neither pole. -/
abbrev BaseFace :=
  {S : Finset (Vertex (ZMod p)) //
    S ∈ complex (ZMod p) ∧ pole true ∉ S ∧ pole false ∉ S}

def BaseFace.translate (a : ZMod p) (S : BaseFace p) : BaseFace p :=
  ⟨translateFace a S.1, translateFace_mem_complex a S.2.1, by
    intro h
    apply S.2.2.1
    exact (mem_translateFace_iff a S.1 (pole true)).1 (by simpa [vertexPerm] using h), by
    intro h
    apply S.2.2.2
    exact (mem_translateFace_iff a S.1 (pole false)).1 (by simpa [vertexPerm] using h)⟩

@[simp] theorem BaseFace.translate_val (a : ZMod p) (S : BaseFace p) :
    (BaseFace.translate p a S).1 = translateFace a S.1 := rfl

theorem BaseFace.has_base (S : BaseFace p) : ∃ v : ZMod p, base v ∈ S.1 := by
  rcases face_pole_or_base S.2.1 with ⟨b, hb⟩ | hb
  · have hPole : pole b ∈ S.1 := by
      rw [hb]
      exact Finset.mem_singleton_self _
    cases b with
    | false => exact (S.2.2.2 hPole).elim
    | true => exact (S.2.2.1 hPole).elim
  · exact hb

/-- The proper base labels retain exactly the cardinality of their face. -/
def BaseFace.labels (S : BaseFace p) : Finset (ZMod p) :=
  Finset.univ.filter (fun v => base v ∈ S.1)

theorem BaseFace.eq_labels_image (S : BaseFace p) :
    S.1 = (BaseFace.labels p S).image base := by
  ext z
  cases z with
  | inl b => cases b <;> simp [BaseFace.labels, S.2.2.1, S.2.2.2]
  | inr v => simp [BaseFace.labels]

theorem BaseFace.card_bound (S : BaseFace p) : S.1.card ≤ p - 1 := by
  obtain ⟨v, hv⟩ := S.2.1.2.2
  have hsub : BaseFace.labels p S ⊆ (Finset.univ.erase v : Finset (ZMod p)) := by
    intro w hw
    simp only [BaseFace.labels, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun h => hv (h ▸ hw)
  have hc := Finset.card_le_card hsub
  rw [BaseFace.eq_labels_image p S,
    Finset.card_image_of_injective _ (show Function.Injective (base : ZMod p → Vertex (ZMod p))
      from Sum.inr_injective)]
  simpa [ZMod.card] using hc

/-- The barycentric color of a proper base face. -/
def BaseFace.color (S : BaseFace p) : Fin (p - 1) :=
  ⟨S.1.card - 1, by
    have hpos := Finset.card_pos.mpr S.2.1.1
    have hbound := BaseFace.card_bound p S
    omega⟩

@[simp] theorem BaseFace.card_translate (a : ZMod p) (S : BaseFace p) :
    (BaseFace.translate p a S).1.card = S.1.card := by
  exact Finset.card_image_of_injective _ (vertexPerm (cyclicPerm a)).injective

@[simp] theorem BaseFace.color_translate (a : ZMod p) (S : BaseFace p) :
    BaseFace.color p (BaseFace.translate p a S) = BaseFace.color p S := by
  apply Fin.ext
  change (BaseFace.translate p a S).1.card - 1 = S.1.card - 1
  exact congrArg (fun k : ℕ => k - 1) (BaseFace.card_translate p a S)

/-- The orbit relation on these free base faces. -/
def BaseFace.orbitSetoid : Setoid (BaseFace p) where
  r S T := ∃ a : ZMod p, translateFace a S.1 = T.1
  iseqv := by
    constructor
    · intro S
      exact ⟨0, translateFace_zero S.1⟩
    · intro S T h
      obtain ⟨a, ha⟩ := h
      refine ⟨-a, ?_⟩
      rw [← ha, ← translateFace_add, neg_add_cancel, translateFace_zero]
    · intro S T U hST hTU
      obtain ⟨a, ha⟩ := hST
      obtain ⟨b, hb⟩ := hTU
      exact ⟨b + a, by rw [translateFace_add, ha, hb]⟩

def BaseFace.representative (S : BaseFace p) : BaseFace p :=
  Quotient.out (Quotient.mk (BaseFace.orbitSetoid p) S)

theorem BaseFace.representative_related (S : BaseFace p) :
    ∃ a : ZMod p, translateFace a (BaseFace.representative p S).1 = S.1 :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (BaseFace.orbitSetoid p) S))

/-- The unique representative-to-face additive phase. -/
def BaseFace.phase (S : BaseFace p) : ZMod p :=
  Classical.choose (BaseFace.representative_related p S)

theorem BaseFace.phase_spec (S : BaseFace p) :
    translateFace (BaseFace.phase p S) (BaseFace.representative p S).1 = S.1 :=
  Classical.choose_spec (BaseFace.representative_related p S)

theorem BaseFace.representative_translate (a : ZMod p) (S : BaseFace p) :
    BaseFace.representative p (BaseFace.translate p a S) = BaseFace.representative p S := by
  unfold BaseFace.representative
  apply congrArg Quotient.out
  exact Quotient.sound ⟨-a, by
    rw [BaseFace.translate_val, ← translateFace_add, neg_add_cancel, translateFace_zero]⟩

/-- The orbit phase is equivariant, not merely a noncanonical label. -/
theorem BaseFace.phase_translate (a : ZMod p) (S : BaseFace p) :
    BaseFace.phase p (BaseFace.translate p a S) = a + BaseFace.phase p S := by
  apply translateFace_injective (BaseFace.representative p S).2.1
    (BaseFace.has_base p (BaseFace.representative p S))
  calc
    translateFace (BaseFace.phase p (BaseFace.translate p a S))
        (BaseFace.representative p S).1 = (BaseFace.translate p a S).1 := by
      rw [← BaseFace.representative_translate p a S]
      exact BaseFace.phase_spec p (BaseFace.translate p a S)
    _ = translateFace a S.1 := rfl
    _ = translateFace a (translateFace (BaseFace.phase p S)
        (BaseFace.representative p S).1) := by rw [BaseFace.phase_spec]
    _ = translateFace (a + BaseFace.phase p S) (BaseFace.representative p S).1 :=
      (translateFace_add _ _ _).symm

end FairDivision.Topology.AAK.ZeroFreeBipyramid
