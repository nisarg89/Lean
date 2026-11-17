import FairDivision.Topology.NerveConnectivity.ClosedCoverPasting

/-!
# Attaching one finite simplex to a finite subcomplex

A realized finite face is a closed simplex, and its proper-face boundary is a
finite subcomplex. When all proper faces are already present, a prescribed map
on the new simplex can be pasted to a map on the old complex. The exact
restriction equations make this lemma usable for equivariant orbitwise cell
attachments as well as ordinary extension arguments.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- The full nonempty-face complex of a finite simplex. -/
def fullFaceComplex {V : Type v} (F : Finset V) :
    PreAbstractSimplicialComplex V where
  faces := {G | G.Nonempty ∧ G ⊆ F}
  isRelLowerSet_faces := by
    intro G hG
    constructor
    · exact hG.1
    · intro H hHG hH
      exact ⟨hH, hHG.trans hG.2⟩

/-- The proper nonempty faces of a finite simplex. -/
def boundaryFaceComplex {V : Type v} (F : Finset V) :
    PreAbstractSimplicialComplex V where
  faces := {G | G.Nonempty ∧ G ⊂ F}
  isRelLowerSet_faces := by
    intro G hG
    constructor
    · exact hG.1
    · intro H hHG hH
      exact ⟨hH, lt_of_le_of_lt hHG hG.2⟩

/-- A simplex already present in a complex brings along all its nonempty faces. -/
theorem fullFaceComplex_le_of_mem {V : Type v}
    (K : PreAbstractSimplicialComplex V) (F : Finset V)
    (hF : F ∈ K) : fullFaceComplex F ≤ K := by
  intro G hG
  exact (K.isRelLowerSet_faces hF).2 hG.2 hG.1

/-- Every proper face of a simplex is also a full face. -/
theorem boundaryFaceComplex_le_fullFaceComplex {V : Type v}
    (F : Finset V) : boundaryFaceComplex F ≤ fullFaceComplex F := by
  intro G hG
  exact ⟨hG.1, hG.2.subset⟩

/-- The boundary lies in a complex that contains every proper face. -/
theorem boundaryFaceComplex_le_of_proper {V : Type v}
    (A : PreAbstractSimplicialComplex V) (F : Finset V)
    (hproper : ∀ G : Finset V, G.Nonempty → G ⊂ F → G ∈ A) :
    boundaryFaceComplex F ≤ A := by
  intro G hG
  exact hproper G hG.1 hG.2

/-- A full simplex meets an old subcomplex in its boundary when its
proper faces, and only its proper faces, already belong to the old complex. -/
theorem inf_fullFaceComplex_eq_boundary {V : Type v}
    (A : PreAbstractSimplicialComplex V) (F : Finset V)
    (hproper : ∀ G : Finset V, G.Nonempty → G ⊂ F → G ∈ A)
    (hFnot : F ∉ A) :
    A ⊓ fullFaceComplex F = boundaryFaceComplex F := by
  ext G
  constructor
  · rintro ⟨hGA, hGF⟩
    have hne : G ≠ F := by
      intro h
      subst G
      exact hFnot hGA
    exact ⟨hGF.1, Finset.ssubset_iff_subset_ne.mpr ⟨hGF.2, hne⟩⟩
  · intro hG
    exact ⟨hproper G hG.1 hG.2,
      ⟨hG.1, hG.2.subset⟩⟩

/-- The realized boundary consists of the full-face points with at least
one zero coordinate among the face vertices. -/
theorem mem_boundaryFaceRealization_iff {V : Type v} [Fintype V]
    (F : Finset V) (w : stdSimplex ℝ V) :
    w ∈ simplicialRealization (boundaryFaceComplex F) ↔
      w ∈ simplicialRealization (fullFaceComplex F) ∧
        ∃ v ∈ F, w.1 v = 0 := by
  classical
  constructor
  · intro hw
    have hG : (FairDivision.Topology.finiteSimplexSupport w).Nonempty ∧
        FairDivision.Topology.finiteSimplexSupport w ⊂ F := hw
    obtain ⟨v, hvF, hvG⟩ := Finset.exists_of_ssubset hG.2
    have hvzero : w.1 v = 0 := by
      have hnpos : ¬ 0 < w.1 v := by
        intro hpos
        exact hvG ((FairDivision.Topology.mem_finiteSimplexSupport_iff w v).2 hpos)
      exact le_antisymm (le_of_not_gt hnpos) (w.2.1 v)
    exact ⟨⟨hG.1, hG.2.subset⟩, v, hvF, hvzero⟩
  · rintro ⟨hw, v, hvF, hvzero⟩
    have hG : (FairDivision.Topology.finiteSimplexSupport w).Nonempty ∧
        FairDivision.Topology.finiteSimplexSupport w ⊆ F := hw
    refine ⟨hG.1, Finset.ssubset_iff_subset_ne.mpr ⟨hG.2, ?_⟩⟩
    intro heq
    have hvG : v ∈ FairDivision.Topology.finiteSimplexSupport w := heq.symm ▸ hvF
    have hpos := (FairDivision.Topology.mem_finiteSimplexSupport_iff w v).1 hvG
    rw [hvzero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos

/-- Paste a prescribed map on one finite simplex onto a map on an old
complex, assuming the two maps agree on their common boundary. -/
noncomputable def attachOneFaceMap
    {V : Type v} [Fintype V] {X : Type u} [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex V) (F : Finset V)
    (f : C(simplicialRealization A, X))
    (g : C(simplicialRealization (fullFaceComplex F), X))
    (hfg : ∀ (w : stdSimplex ℝ V)
      (hwA : w ∈ simplicialRealization A)
      (hwF : w ∈ simplicialRealization (fullFaceComplex F)),
        f ⟨w, hwA⟩ = g ⟨w, hwF⟩) :
    C(simplicialRealization (A ⊔ fullFaceComplex F), X) :=
  simplicialCoverPaste A (fullFaceComplex F) f g hfg

/-- The pasted map agrees exactly with the old map. -/
theorem attachOneFaceMap_old
    {V : Type v} [Fintype V] {X : Type u} [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex V) (F : Finset V)
    (f : C(simplicialRealization A, X))
    (g : C(simplicialRealization (fullFaceComplex F), X))
    (hfg : ∀ (w : stdSimplex ℝ V)
      (hwA : w ∈ simplicialRealization A)
      (hwF : w ∈ simplicialRealization (fullFaceComplex F)),
        f ⟨w, hwA⟩ = g ⟨w, hwF⟩)
    (w : simplicialRealization A) :
    attachOneFaceMap A F f g hfg
      ⟨w.1, (simplicialRealization_mono le_sup_left) w.2⟩ = f w := by
  classical
  change closedCoverPaste (simplicialRealization A)
      (simplicialRealization (fullFaceComplex F))
      (simplicialRealization_isClosed A)
      (simplicialRealization_isClosed (fullFaceComplex F))
      f g hfg ⟨w.1, Or.inl w.2⟩ = f w
  exact closedCoverPaste_left _ _ _ _ _ _ _ w

/-- The pasted map agrees exactly with the prescribed new-simplex map. -/
theorem attachOneFaceMap_face
    {V : Type v} [Fintype V] {X : Type u} [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex V) (F : Finset V)
    (f : C(simplicialRealization A, X))
    (g : C(simplicialRealization (fullFaceComplex F), X))
    (hfg : ∀ (w : stdSimplex ℝ V)
      (hwA : w ∈ simplicialRealization A)
      (hwF : w ∈ simplicialRealization (fullFaceComplex F)),
        f ⟨w, hwA⟩ = g ⟨w, hwF⟩)
    (w : simplicialRealization (fullFaceComplex F)) :
    attachOneFaceMap A F f g hfg
      ⟨w.1, (simplicialRealization_mono le_sup_right) w.2⟩ = g w := by
  classical
  change closedCoverPaste (simplicialRealization A)
      (simplicialRealization (fullFaceComplex F))
      (simplicialRealization_isClosed A)
      (simplicialRealization_isClosed (fullFaceComplex F))
      f g hfg ⟨w.1, Or.inr w.2⟩ = g w
  exact closedCoverPaste_right _ _ _ _ _ _ _ w

end FairDivision.Topology.NerveConnectivity
