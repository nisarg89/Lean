import FairDivision.Topology.AAK.BipyramidBarycentricClassifier
import FairDivision.Topology.NerveConnectivity.BarycentricHomeomorph

/-!
# Equivariant realization of the bipyramid classifier

The existing barycentric homeomorphism is natural under coordinate
permutations. Thus the finite face classifier gives a continuous map on the
original bipyramid, commuting with the prime-cyclic action and preserving
both fixed poles exactly. All maps here are literal finite-simplex maps.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.ZeroFreeBipyramid

open FairDivision.Topology.NerveConnectivity
open scoped BigOperators Classical

theorem simplex_map_equiv_apply {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (w : stdSimplex ℝ V) (v : V) :
    (stdSimplex.map e w).1 (e v) = w.1 v := by
  change FunOnFinite.linearMap ℝ ℝ e w.1 (e v) = _
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter : Finset.univ.filter (fun x : V => e x = e v) = {v} := by
    ext x
    simp [e.injective.eq_iff]
  rw [hfilter, Finset.sum_singleton]

theorem simplex_map_congr_support {V W : Type*} [Fintype V] [Fintype W]
    (f g : V → W) (w : stdSimplex ℝ V)
    (hfg : ∀ v ∈ FairDivision.Topology.finiteSimplexSupport w, f v = g v) :
    stdSimplex.map f w = stdSimplex.map g w := by
  apply Subtype.ext
  funext v
  change FunOnFinite.linearMap ℝ ℝ f w.1 v = FunOnFinite.linearMap ℝ ℝ g w.1 v
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ FairDivision.Topology.finiteSimplexSupport w
  · rw [hfg x hx]
  · have hw : w.1 x = 0 := le_antisymm
      (le_of_not_gt (by simpa using hx)) (w.2.1 x)
    simp [hw]

variable (p : ℕ) [Fact p.Prime]

def facePermutation (a : ZMod p) : Equiv.Perm (Finset (Vertex (ZMod p))) :=
  Equiv.finsetCongr (vertexPerm (cyclicPerm a))

@[simp] theorem facePermutation_apply (a : ZMod p) (F : Finset (Vertex (ZMod p))) :
    facePermutation p a F = translateFace a F := by
  simp [facePermutation, Equiv.finsetCongr_apply, Finset.map_eq_image, translateFace]

/-- Translation carries chains of valid faces to chains of valid faces. -/
theorem subdivision_translate_face (a : ZMod p)
    {C : Finset (Finset (Vertex (ZMod p)))}
    (hC : C ∈ barycentricSubdivision (complex (ZMod p))) :
    C.image (facePermutation p a) ∈ barycentricSubdivision (complex (ZMod p)) := by
  refine ⟨hC.1.image _, ?_, ?_⟩
  · intro F hF
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hF
    simpa only [facePermutation_apply] using
      translateFace_mem_complex a (hC.2.1 G hG)
  · intro F hF G hG _
    obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
    rcases hC.2.2.total hF' hG' with hFG | hGF
    · left
      simpa [facePermutation_apply, translateFace] using
        Finset.image_subset_image hFG
    · right
      simpa [facePermutation_apply, translateFace] using
        Finset.image_subset_image hGF

/-- Actual cyclic action on the subdivided realization. -/
def subdivisionTranslate (a : ZMod p) :
    C(simplicialRealization (barycentricSubdivision (complex (ZMod p))),
      simplicialRealization (barycentricSubdivision (complex (ZMod p)))) where
  toFun z := ⟨stdSimplex.map (facePermutation p a) z.1,
    ((barycentricSubdivision (complex (ZMod p))).isRelLowerSet_faces
      (subdivision_translate_face p a z.2)).2
      (FairDivision.Topology.finiteSimplexSupport_map_subset _ _)
      (FairDivision.Topology.finiteSimplexSupport_nonempty _)⟩
  continuous_toFun := ((stdSimplex.continuous_map _).comp
    continuous_subtype_val).subtype_mk _

def suspensionPermutation (a : ZMod p) :
    Equiv.Perm (SuspensionVertex (p - 1) (ZMod p)) :=
  Equiv.sumCongr (Equiv.refl Bool)
    (Equiv.prodCongr (Equiv.refl (Fin (p - 1))) (Equiv.addLeft a))

@[simp] theorem suspensionPermutation_apply (a : ZMod p)
    (v : SuspensionVertex (p - 1) (ZMod p)) :
    suspensionPermutation p a v = suspensionTranslate a v := by
  cases v with
  | inl b => rfl
  | inr v => rcases v with ⟨i, g⟩; rfl

theorem suspension_translate_face (a : ZMod p)
    {S : Finset (SuspensionVertex (p - 1) (ZMod p))}
    (hS : S ∈ suspensionJoinComplex (p - 1) (ZMod p)) :
    S.image (suspensionPermutation p a) ∈ suspensionJoinComplex (p - 1) (ZMod p) := by
  refine ⟨hS.1.image _, ?_, ?_⟩
  · rintro ⟨hn, hs⟩
    have hn' : pole true ∈ S := by
      obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hn
      have hVertex : v = pole true := (suspensionPermutation p a).injective
        (by simpa [suspensionPermutation] using heq)
      exact hVertex ▸ hv
    have hs' : pole false ∈ S := by
      obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hs
      have hVertex : v = pole false := (suspensionPermutation p a).injective
        (by simpa [suspensionPermutation] using heq)
      exact hVertex ▸ hv
    exact hS.2.1 ⟨hn', hs'⟩
  · intro i g h hg hh
    have hg' : base (i, g - a) ∈ S := by
      obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hg
      have hVertex : v = base (i,g-a) := (suspensionPermutation p a).injective
        (by simpa [suspensionPermutation,add_comm] using heq)
      exact hVertex ▸ hv
    have hh' : base (i, h - a) ∈ S := by
      obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hh
      have hVertex : v = base (i,h-a) := (suspensionPermutation p a).injective
        (by simpa [suspensionPermutation,add_comm] using heq)
      exact hVertex ▸ hv
    have he := congrArg (fun z : ZMod p => z + a)
      (hS.2.2 i (g - a) (h - a) hg' hh')
    simpa only [sub_add_cancel] using he

/-- The finite target's actual cyclic action. -/
def suspensionRelabel (a : ZMod p) :
    C(SuspensionRealization (p - 1) (ZMod p), SuspensionRealization (p - 1) (ZMod p)) where
  toFun x := ⟨stdSimplex.map (suspensionPermutation p a) x.1,
    ((suspensionJoinComplex (p - 1) (ZMod p)).isRelLowerSet_faces
      (suspension_translate_face p a x.2)).2
      (FairDivision.Topology.finiteSimplexSupport_map_subset _ _)
      (FairDivision.Topology.finiteSimplexSupport_nonempty _)⟩
  continuous_toFun := ((stdSimplex.continuous_map _).comp
    continuous_subtype_val).subtype_mk _

/-- Simplicial equivariance implies exact equivariance of the realization
map; the classifier need only commute on actual source faces. -/
theorem classifierMap_equivariant (a : ZMod p)
    (z : simplicialRealization (barycentricSubdivision (complex (ZMod p)))) :
    classifierMap p (subdivisionTranslate p a z) =
      suspensionRelabel p a (classifierMap p z) := by
  apply Subtype.ext
  change stdSimplex.map (faceClassifier p) (stdSimplex.map (facePermutation p a) z.1) =
    stdSimplex.map (suspensionPermutation p a) (stdSimplex.map (faceClassifier p) z.1)
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  apply simplex_map_congr_support
  intro F hF
  simpa only [Function.comp_apply, facePermutation_apply, suspensionPermutation_apply] using
    faceClassifier_translate p a (z.2.2.1 F hF)

private theorem faceBaryWeight_translate (a : ZMod p)
    (F : Finset (Vertex (ZMod p))) (v : Vertex (ZMod p)) :
    faceBaryWeight (facePermutation p a F) v =
      faceBaryWeight F ((vertexPerm (cyclicPerm a)).symm v) := by
  simp [faceBaryWeight, facePermutation, Equiv.finsetCongr_apply,
    Finset.mem_map_equiv]

/-- Naturality of the existing barycentric homeomorphism's forward map. -/
theorem barycentricForward_translate (a : ZMod p)
    (z : simplicialRealization (barycentricSubdivision (complex (ZMod p)))) :
    barycentricForwardMap (complex (ZMod p)) (subdivisionTranslate p a z) =
      relabel (cyclicPerm a) (barycentricForwardMap (complex (ZMod p)) z) := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  change (∑ F : Finset (Vertex (ZMod p)),
      (stdSimplex.map (facePermutation p a) z.1).1 F * faceBaryWeight F v) =
    ∑ F : Finset (Vertex (ZMod p)),
      z.1.1 F * faceBaryWeight F ((vertexPerm (cyclicPerm a)).symm v)
  calc
    _ = ∑ F : Finset (Vertex (ZMod p)),
        (stdSimplex.map (facePermutation p a) z.1).1 (facePermutation p a F) *
          faceBaryWeight (facePermutation p a F) v :=
      (Equiv.sum_comp (facePermutation p a) (fun F =>
        (stdSimplex.map (facePermutation p a) z.1).1 F * faceBaryWeight F v)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro F _
      rw [simplex_map_equiv_apply, faceBaryWeight_translate]

/-- The existing inverse homeomorphism consequently commutes with the
same actual cyclic action; no new subdivision construction is needed. -/
theorem barycentricInverse_translate (a : ZMod p) (x : Realization (ZMod p)) :
    (barycentricRealizationHomeomorph (complex (ZMod p))).symm (relabel (cyclicPerm a) x) =
      subdivisionTranslate p a ((barycentricRealizationHomeomorph (complex (ZMod p))).symm x) := by
  apply (barycentricRealizationHomeomorph (complex (ZMod p))).injective
  change barycentricForwardMap (complex (ZMod p))
      ((barycentricRealizationHomeomorph (complex (ZMod p))).symm
        (relabel (cyclicPerm a) x)) =
    barycentricForwardMap (complex (ZMod p))
      (subdivisionTranslate p a
        ((barycentricRealizationHomeomorph (complex (ZMod p))).symm x))
  rw [show barycentricForwardMap (complex (ZMod p))
      ((barycentricRealizationHomeomorph (complex (ZMod p))).symm
        (relabel (cyclicPerm a) x)) = relabel (cyclicPerm a) x from
    (barycentricRealizationHomeomorph _).apply_symm_apply _]
  rw [barycentricForward_translate]
  exact congrArg (relabel (cyclicPerm a))
    ((barycentricRealizationHomeomorph _).apply_symm_apply x).symm

/-- Continuous classifier on the original, unsubdivided finite bipyramid. -/
def freeSuspensionMap : C(Realization (ZMod p), SuspensionRealization (p - 1) (ZMod p)) :=
  (classifierMap p).comp
    ((barycentricRealizationHomeomorph (complex (ZMod p))).symm :
      C(Realization (ZMod p),
        simplicialRealization (barycentricSubdivision (complex (ZMod p)))))

theorem freeSuspensionMap_equivariant (a : ZMod p) (x : Realization (ZMod p)) :
    freeSuspensionMap p (relabel (cyclicPerm a) x) =
      suspensionRelabel p a (freeSuspensionMap p x) := by
  change classifierMap p ((barycentricRealizationHomeomorph _).symm
    (relabel (cyclicPerm a) x)) =
    suspensionRelabel p a (classifierMap p
      ((barycentricRealizationHomeomorph (complex (ZMod p))).symm x))
  rw [barycentricInverse_translate, classifierMap_equivariant]

theorem barycentricForward_subdividedPole (b : Bool) :
    barycentricForwardMap (complex (ZMod p)) (subdividedPole p b) = polePoint b := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  have hForward :
      (barycentricForwardMap (complex (ZMod p)) (subdividedPole p b)).1.1 v =
        ∑ F : Finset (Vertex (ZMod p)),
          (subdividedPole p b).1.1 F * faceBaryWeight F v := rfl
  rw [hForward, polePoint_coordinate]
  rw [Finset.sum_eq_single ({pole b} : Finset (Vertex (ZMod p)))]
  · simp [subdividedPole, stdSimplex.vertex_coe, Pi.single_apply, faceBaryWeight]
  · intro F _ hF
    simp [subdividedPole, stdSimplex.vertex_coe, Pi.single_apply, hF]
  · intro hNot
    exact (hNot (Finset.mem_univ _)).elim

/-- Both poles are preserved by the final original-realization map. -/
theorem freeSuspensionMap_pole (b : Bool) :
    (freeSuspensionMap p (polePoint b)).1 = stdSimplex.vertex (pole b) := by
  have hInv : (barycentricRealizationHomeomorph (complex (ZMod p))).symm (polePoint b) =
      subdividedPole p b := by
    apply (barycentricRealizationHomeomorph (complex (ZMod p))).injective
    exact ((barycentricRealizationHomeomorph _).apply_symm_apply _).trans
      (barycentricForward_subdividedPole p b).symm
  change (classifierMap p ((barycentricRealizationHomeomorph _).symm (polePoint b))).1 = _
  rw [hInv, classifierMap_pole]

end FairDivision.Topology.AAK.ZeroFreeBipyramid
