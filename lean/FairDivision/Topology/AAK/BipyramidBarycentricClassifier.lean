import FairDivision.Topology.AAK.BipyramidBaseFacePhase
import FairDivision.Topology.NerveConnectivity.BarycentricSubdivision
import FairDivision.Topology.FiniteSimplexSupportMap
import FairDivision.Topology.Volovikov.UniversalJoin

/-!
# A concrete pole-preserving classifier of the cyclic bipyramid

A barycentric vertex containing a pole is sent to that pole. A base-only
vertex is sent to its cardinality-minus-one color and its free orbit phase.
Comparable base faces with equal colors are equal, so the image of each
barycentric simplex is a simplex in the suspension of the (p−1)-color join.
This is an actual equivariant simplicial map, not an obstruction premise.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.ZeroFreeBipyramid

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- The suspension vertex set of a free, colored join. -/
abbrev SuspensionVertex (d : ℕ) (G : Type*) := Bool ⊕ (Fin d × G)

/-- The two cone points are not joined; the free part has one label per color. -/
def suspensionJoinComplex (d : ℕ) (G : Type*) :
    PreAbstractSimplicialComplex (SuspensionVertex d G) where
  faces := {S | S.Nonempty ∧
    ¬(pole true ∈ S ∧ pole false ∈ S) ∧
    ∀ (i : Fin d) (a b : G), base (i, a) ∈ S → base (i, b) ∈ S → a = b}
  isRelLowerSet_faces := by
    intro S hS
    refine ⟨hS.1, ?_⟩
    intro T hTS hT
    exact ⟨hT, fun h => hS.2.1 ⟨hTS h.1, hTS h.2⟩,
      fun i a b ha hb => hS.2.2 i a b (hTS ha) (hTS hb)⟩

abbrev SuspensionRealization (d : ℕ) (G : Type*) [Fintype G] :=
  simplicialRealization (suspensionJoinComplex d G)

/-- Translation of labels fixes the two suspension vertices. -/
def suspensionTranslate {d : ℕ} {G : Type*} [AddGroup G] (a : G) :
    SuspensionVertex d G → SuspensionVertex d G
  | .inl b => .inl b
  | .inr (i, g) => .inr (i, a + g)

variable (p : ℕ) [Fact p.Prime]

/-- The classifier is total on the common ambient face type. Its value on
invalid faces is irrelevant to the subdivided realization. -/
def faceClassifier (F : Finset (Vertex (ZMod p))) : SuspensionVertex (p - 1) (ZMod p) :=
  if hF : F ∈ complex (ZMod p) then
    if hn : pole true ∈ F then pole true
    else if hs : pole false ∈ F then pole false
    else base (BaseFace.color p ⟨F, hF, hn, hs⟩,
      BaseFace.phase p ⟨F, hF, hn, hs⟩)
  else pole false

theorem faceClassifier_of_no_poles {F : Finset (Vertex (ZMod p))}
    (hF : F ∈ complex (ZMod p)) (hn : pole true ∉ F) (hs : pole false ∉ F) :
    faceClassifier p F = base (BaseFace.color p ⟨F, hF, hn, hs⟩,
      BaseFace.phase p ⟨F, hF, hn, hs⟩) := by
  simp [faceClassifier, hF, hn, hs]

/-- On genuine faces a pole output detects exactly that pole's presence. -/
theorem faceClassifier_pole_iff {F : Finset (Vertex (ZMod p))}
    (hF : F ∈ complex (ZMod p)) (b : Bool) :
    faceClassifier p F = pole b ↔ pole b ∈ F := by
  have hNoBoth : ¬(pole true ∈ F ∧ pole false ∈ F) := hF.2.1
  cases b <;> by_cases hn : pole true ∈ F <;>
    by_cases hs : pole false ∈ F <;>
    simp_all [faceClassifier]

theorem faceClassifier_singleton_pole (b : Bool) :
    faceClassifier p {pole b} = pole b := by
  have hF : ({pole b} : Finset (Vertex (ZMod p))) ∈ complex (ZMod p) := by
    refine ⟨Finset.singleton_nonempty _, ?_, ⟨0, ?_⟩⟩
    · cases b <;> simp
    · simp
  exact (faceClassifier_pole_iff p hF b).2 (Finset.mem_singleton_self _)

/-- A free output has the concrete base-face data used by the classifier. -/
theorem faceClassifier_base_data {F : Finset (Vertex (ZMod p))}
    (hF : F ∈ complex (ZMod p)) {i : Fin (p - 1)} {a : ZMod p}
    (h : faceClassifier p F = base (i, a)) :
    ∃ B : BaseFace p, B.1 = F ∧ BaseFace.color p B = i ∧ BaseFace.phase p B = a := by
  have hn : pole true ∉ F := by
    intro hn
    have he := (faceClassifier_pole_iff p hF true).2 hn
    rw [h] at he
    cases he
  have hs : pole false ∉ F := by
    intro hs
    have he := (faceClassifier_pole_iff p hF false).2 hs
    rw [h] at he
    cases he
  refine ⟨⟨F, hF, hn, hs⟩, rfl, ?_⟩
  rw [faceClassifier_of_no_poles p hF hn hs] at h
  exact Prod.mk.inj (Sum.inr.inj h)

/-- Comparable proper base faces of the same barycentric color are equal. -/
theorem comparable_baseFace_eq {B C : BaseFace p}
    (hBC : B.1 ⊆ C.1 ∨ C.1 ⊆ B.1)
    (hc : BaseFace.color p B = BaseFace.color p C) : B = C := by
  have hcard : B.1.card = C.1.card := by
    have h := congrArg Fin.val hc
    change B.1.card - 1 = C.1.card - 1 at h
    have hB := Finset.card_pos.mpr B.2.1.1
    have hC := Finset.card_pos.mpr C.2.1.1
    omega
  apply Subtype.ext
  rcases hBC with hBC | hCB
  · exact Finset.eq_of_subset_of_card_le hBC hcard.ge
  · exact (Finset.eq_of_subset_of_card_le hCB hcard.le).symm

/-- The free labels agree whenever two comparable faces have the same color. -/
theorem faceClassifier_comparable_label {F G : Finset (Vertex (ZMod p))}
    (hF : F ∈ complex (ZMod p)) (hG : G ∈ complex (ZMod p))
    (hFG : F ⊆ G ∨ G ⊆ F) (i : Fin (p - 1)) (a b : ZMod p)
    (ha : faceClassifier p F = base (i, a))
    (hb : faceClassifier p G = base (i, b)) : a = b := by
  obtain ⟨B, hBF, hBi, hBa⟩ := faceClassifier_base_data p hF ha
  obtain ⟨C, hCG, hCi, hCb⟩ := faceClassifier_base_data p hG hb
  have hBC : B = C := comparable_baseFace_eq p (by simpa [hBF, hCG] using hFG)
    (hBi.trans hCi.symm)
  exact hBa.symm.trans ((congrArg (BaseFace.phase p) hBC).trans hCb)

/-- A chain cannot contain faces classified as opposite poles. -/
theorem faceClassifier_comparable_no_opposite {F G : Finset (Vertex (ZMod p))}
    (hF : F ∈ complex (ZMod p)) (hG : G ∈ complex (ZMod p))
    (hFG : F ⊆ G ∨ G ⊆ F)
    (hn : faceClassifier p F = pole true) (hs : faceClassifier p G = pole false) : False := by
  have hFn := (faceClassifier_pole_iff p hF true).1 hn
  have hGs := (faceClassifier_pole_iff p hG false).1 hs
  rcases hFG with hFG | hGF
  · exact hG.2.1 ⟨hFG hFn, hGs⟩
  · exact hF.2.1 ⟨hFn, hGF hGs⟩

/-- Literal simplicial-map property for the actual barycentric complex. -/
theorem faceClassifier_image_face {C : Finset (Finset (Vertex (ZMod p)))}
    (hC : C ∈ barycentricSubdivision (complex (ZMod p))) :
    C.image (faceClassifier p) ∈ suspensionJoinComplex (p - 1) (ZMod p) := by
  refine ⟨hC.1.image _, ?_, ?_⟩
  · rintro ⟨hn, hs⟩
    obtain ⟨F, hFC, hFn⟩ := Finset.mem_image.mp hn
    obtain ⟨G, hGC, hGs⟩ := Finset.mem_image.mp hs
    exact faceClassifier_comparable_no_opposite p (hC.2.1 F hFC) (hC.2.1 G hGC)
      (hC.2.2.total hFC hGC) hFn hGs
  · intro i a b ha hb
    obtain ⟨F, hFC, hFa⟩ := Finset.mem_image.mp ha
    obtain ⟨G, hGC, hGb⟩ := Finset.mem_image.mp hb
    exact faceClassifier_comparable_label p (hC.2.1 F hFC) (hC.2.1 G hGC)
      (hC.2.2.total hFC hGC) i a b hFa hGb

/-- The chosen orbit phase makes the classifier equivariant on every valid
face, including faces containing a fixed pole. -/
theorem faceClassifier_translate (a : ZMod p)
    {F : Finset (Vertex (ZMod p))} (hF : F ∈ complex (ZMod p)) :
    faceClassifier p (translateFace a F) = suspensionTranslate a (faceClassifier p F) := by
  have hT := translateFace_mem_complex a hF
  have hn : pole true ∈ translateFace a F ↔ pole true ∈ F := by
    simpa [vertexPerm] using mem_translateFace_iff a F (pole true)
  have hs : pole false ∈ translateFace a F ↔ pole false ∈ F := by
    simpa [vertexPerm] using mem_translateFace_iff a F (pole false)
  by_cases hFn : pole true ∈ F
  · simp [faceClassifier, hF, hT, hn, hFn, suspensionTranslate]
  · by_cases hFs : pole false ∈ F
    · simp [faceClassifier, hF, hT, hn, hs, hFn, hFs, suspensionTranslate]
    · let B : BaseFace p := ⟨F, hF, hFn, hFs⟩
      have hTB : (⟨translateFace a F, hT, fun h => hFn (hn.mp h),
          fun h => hFs (hs.mp h)⟩ : BaseFace p) = BaseFace.translate p a B := by
        apply Subtype.ext
        rfl
      rw [faceClassifier_of_no_poles p hF hFn hFs,
        faceClassifier_of_no_poles p hT (fun h => hFn (hn.mp h))
          (fun h => hFs (hs.mp h)), hTB]
      simp [BaseFace.color_translate, BaseFace.phase_translate, B, suspensionTranslate]

/-- The actual continuous realization map on the subdivided bipyramid. -/
def classifierMap : C(simplicialRealization (barycentricSubdivision (complex (ZMod p))),
    SuspensionRealization (p - 1) (ZMod p)) where
  toFun z := ⟨stdSimplex.map (faceClassifier p) z.1,
    ((suspensionJoinComplex (p - 1) (ZMod p)).isRelLowerSet_faces
      (faceClassifier_image_face p z.2)).2
      (FairDivision.Topology.finiteSimplexSupport_map_subset (faceClassifier p) z.1)
      (FairDivision.Topology.finiteSimplexSupport_nonempty _)⟩
  continuous_toFun := ((stdSimplex.continuous_map (faceClassifier p)).comp
    continuous_subtype_val).subtype_mk _

/-- A literal singleton pole in the subdivided realization. -/
def subdividedPole (b : Bool) :
    simplicialRealization (barycentricSubdivision (complex (ZMod p))) := by
  refine ⟨stdSimplex.vertex {pole b}, ?_⟩
  change FairDivision.Topology.finiteSimplexSupport (stdSimplex.vertex {pole b}) ∈
    barycentricSubdivision (complex (ZMod p))
  rw [FairDivision.Topology.finiteSimplexSupport_vertex]
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · intro F hF
    have hEq : F = {pole b} := Finset.mem_singleton.mp hF
    subst F
    exact ⟨Finset.singleton_nonempty _, by cases b <;> simp, ⟨0, by simp⟩⟩
  · intro F hF G hG _
    have hF' : F = {pole b} := Finset.mem_singleton.mp hF
    have hG' : G = {pole b} := Finset.mem_singleton.mp hG
    simp [hF', hG']

/-- The realization map sends the fixed source poles to the same target
poles, rather than merely to homotopic points. -/
theorem classifierMap_pole (b : Bool) :
    (classifierMap p (subdividedPole p b)).1 = stdSimplex.vertex (pole b) := by
  change stdSimplex.map (faceClassifier p) (stdSimplex.vertex {pole b}) = _
  rw [stdSimplex.map_vertex, faceClassifier_singleton_pole]

end FairDivision.Topology.AAK.ZeroFreeBipyramid
