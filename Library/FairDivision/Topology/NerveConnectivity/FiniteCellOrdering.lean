import FairDivision.Topology.NerveConnectivity.FiniteCellAttachment
import Mathlib.Order.Preorder.Finite

/-!
# Ordering missing faces for finite-cell extension

Among faces of a finite complex not yet present in a subcomplex, choose one
of smallest cardinality. Every proper face is then already present. This is
the combinatorial induction step for attaching finite simplex cells.
-/

set_option autoImplicit false

open scoped Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- Faces of `K` missing from `A`. -/
noncomputable def missingFaces {V : Type v} [Fintype V]
    (A K : PreAbstractSimplicialComplex V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun F => F ∈ K ∧ F ∉ A)

@[simp] theorem mem_missingFaces_iff {V : Type v} [Fintype V]
    (A K : PreAbstractSimplicialComplex V) (F : Finset V) :
    F ∈ missingFaces A K ↔ F ∈ K ∧ F ∉ A := by
  classical
  simp [missingFaces]

/-- If faces are missing, a smallest missing face has its whole proper
boundary in `A`. -/
theorem exists_minimal_missing_face {V : Type v} [Fintype V]
    (A K : PreAbstractSimplicialComplex V) (hnot : ¬ K ≤ A) :
    ∃ F : Finset V, F ∈ K ∧ F ∉ A ∧ F.Nonempty ∧
      ∀ G : Finset V, G.Nonempty → G ⊂ F → G ∈ A := by
  classical
  have hmissing : (missingFaces A K).Nonempty := by
    by_contra h
    apply hnot
    intro F hFK
    by_contra hFA
    exact h ⟨F, (mem_missingFaces_iff A K F).2 ⟨hFK, hFA⟩⟩
  obtain ⟨F, hmin⟩ :=
    (missingFaces A K).exists_minimalFor (fun G : Finset V => G.card) hmissing
  have hF : F ∈ K ∧ F ∉ A := (mem_missingFaces_iff A K F).1 hmin.1
  refine ⟨F, hF.1, hF.2, (K.isRelLowerSet_faces hF.1).1, ?_⟩
  intro G hGne hGF
  by_contra hGA
  have hGK : G ∈ K := (K.isRelLowerSet_faces hF.1).2 hGF.subset hGne
  have hGmissing : G ∈ missingFaces A K :=
    (mem_missingFaces_iff A K G).2 ⟨hGK, hGA⟩
  have hcardlt : G.card < F.card := Finset.card_lt_card hGF
  have hcardge : F.card ≤ G.card := hmin.2 hGmissing hcardlt.le
  omega

/-- A missing face of globally least cardinality: every face of the
ambient complex with fewer vertices is already in the old subcomplex. This
stronger form supports attaching whole free orbits of equal-size faces. -/
theorem exists_minimal_missing_face_global {V : Type v} [Fintype V]
    (A K : PreAbstractSimplicialComplex V) (hnot : ¬ K ≤ A) :
    ∃ F : Finset V, F ∈ K ∧ F ∉ A ∧ F.Nonempty ∧
      ∀ G : Finset V, G ∈ K → G.card < F.card → G ∈ A := by
  classical
  have hmissing : (missingFaces A K).Nonempty := by
    by_contra h
    apply hnot
    intro F hFK
    by_contra hFA
    exact h ⟨F, (mem_missingFaces_iff A K F).2 ⟨hFK, hFA⟩⟩
  obtain ⟨F, hmin⟩ :=
    (missingFaces A K).exists_minimalFor (fun G : Finset V => G.card) hmissing
  have hF : F ∈ K ∧ F ∉ A := (mem_missingFaces_iff A K F).1 hmin.1
  refine ⟨F, hF.1, hF.2, (K.isRelLowerSet_faces hF.1).1, ?_⟩
  intro G hGK hcard
  by_contra hGA
  have hGmissing : G ∈ missingFaces A K :=
    (mem_missingFaces_iff A K G).2 ⟨hGK, hGA⟩
  have hcardge : F.card ≤ G.card := hmin.2 hGmissing hcard.le
  omega

/-- Adding a missing face removes at least that face from the missing list. -/
theorem missingFaces_attach_ssubset {V : Type v} [Fintype V]
    (A K : PreAbstractSimplicialComplex V) (F : Finset V)
    (hF : F ∈ K) (hFnot : F ∉ A) :
    missingFaces (A ⊔ fullFaceComplex F) K ⊂ missingFaces A K := by
  classical
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro G hG
    have hGK : G ∈ K := ((mem_missingFaces_iff _ _ _).1 hG).1
    have hGnot : G ∉ A ⊔ fullFaceComplex F :=
      ((mem_missingFaces_iff _ _ _).1 hG).2
    exact (mem_missingFaces_iff A K G).2
      ⟨hGK, fun hGA => hGnot (Or.inl hGA)⟩
  · intro heq
    have hFmiss : F ∈ missingFaces A K :=
      (mem_missingFaces_iff A K F).2 ⟨hF, hFnot⟩
    have hFadded : F ∈ A ⊔ fullFaceComplex F :=
      Or.inr ⟨(K.isRelLowerSet_faces hF).1, subset_rfl⟩
    have hFnotmiss : F ∉ missingFaces (A ⊔ fullFaceComplex F) K := by
      intro hm
      exact ((mem_missingFaces_iff _ _ _).1 hm).2 hFadded
    exact hFnotmiss (heq.symm ▸ hFmiss)

end FairDivision.Topology.NerveConnectivity
