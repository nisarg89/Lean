import FairDivision.Topology.FiniteSimplexSkeleton
import FairDivision.Topology.SimplexCoordinatewiseExtension

/-!
# One higher-dimensional face preserves support-local admissibility

The geometric cap maximum is supplied by the actual coordinatewise simplex
extension theorem. The already proved finite-face homeomorphisms transport
that SAME map to an arbitrary closed face. Boundary values stay unchanged.
For an interior point its positive support is the whole face, so all selected
boundary vectors can be enlarged to that face's stock before taking their
attained coordinatewise maximum.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- Transport the actual capwise maximum extension to one finite face,
retaining both exact boundary agreement and the support-local predicate. -/
theorem exists_supportLocal_face_extension {V : Type*} [Fintype V] {n:ℕ}
    (P:Finset V→(Fin n→ℝ)→Prop) (hP:SupportLocalMaxClosed P)
    (F:Finset V) (hCard:3≤F.card)
    (f:C(simplicialRealization (boundaryFaceComplex F),Fin n→ℝ))
    (hf:∀x,P (finiteSimplexSupport x.1) (f x)) :
    ∃g:C(simplicialRealization (fullFaceComplex F),Fin n→ℝ),
      (∀x:simplicialRealization (boundaryFaceComplex F),
        g ⟨x.1,(simplicialRealization_mono (boundaryFaceComplex_le_fullFaceComplex F)) x.2⟩=f x) ∧
      ∀x,P (finiteSimplexSupport x.1) (g x) := by
  classical
  have hF:F.Nonempty:=Finset.card_pos.mp (by omega)
  let eF:=fullFaceRealizationHomeomorph F hF
  let eB:=boundaryFaceRealizationHomeomorph F hF
  let fStd:C(SimplexCoordinatewiseExtension.SimplexCoordinateBoundary (FaceVertex F),Fin n→ℝ):=
    f.comp (eB.symm : C(finiteFaceStandardSimplexBoundary F,
      simplicialRealization (boundaryFaceComplex F)))
  obtain ⟨gStd,hBoundary,hMaximum⟩:=SimplexCoordinatewiseExtension.exists_extension
    (FaceVertex F) (by simpa only [Fintype.card_coe] using hCard) fStd
  let g:C(simplicialRealization (fullFaceComplex F),Fin n→ℝ):=
    gStd.comp (eF : C(simplicialRealization (fullFaceComplex F),
      stdSimplex ℝ (FaceVertex F)))
  have hAgree:∀x:simplicialRealization (boundaryFaceComplex F),
      g ⟨x.1,(simplicialRealization_mono (boundaryFaceComplex_le_fullFaceComplex F)) x.2⟩=f x:=by
    intro x
    have hCoordinates:eF ⟨x.1,(simplicialRealization_mono
        (boundaryFaceComplex_le_fullFaceComplex F)) x.2⟩=(eB x).1:=rfl
    change gStd (eF ⟨x.1,_⟩)=f x
    rw [hCoordinates]
    have h := hBoundary (eB x)
    change gStd (eB x).1 = f (eB.symm (eB x)) at h
    rw [eB.symm_apply_apply] at h
    exact h
  refine ⟨g,hAgree,?_⟩
  intro x
  by_cases hxB:x.1∈simplicialRealization (boundaryFaceComplex F)
  · have hAt:=hAgree ⟨x.1,hxB⟩
    rw [hAt]
    exact hf ⟨x.1,hxB⟩
  · have hSupport:finiteSimplexSupport x.1=F:=by
      by_contra hNe
      apply hxB
      exact ⟨finiteSimplexSupport_nonempty x.1,
        Finset.ssubset_iff_subset_ne.mpr ⟨x.2.2,hNe⟩⟩
    obtain ⟨witness,hEq,hDom⟩:=hMaximum (eF x)
    let u:Fin n→Fin n→ℝ:=fun i=>f (eB.symm (witness i))
    have hAdm:∀i,P F (u i):=by
      intro i
      apply hP.mono (eB.symm (witness i)).2.2.subset
      exact hf (eB.symm (witness i))
    rw [hSupport]
    apply hP.attained F u (g x) hAdm
    ·intro i
     exact hEq i
    ·intro i j
     exact hDom i j

/-- Attach that higher face by the existing closed-pasting theorem. No
support-local property is weakened on previously defined boundary points. -/
theorem exists_supportLocal_attach_face {V:Type*} [Fintype V] {n:ℕ}
    (P:Finset V→(Fin n→ℝ)→Prop) (hP:SupportLocalMaxClosed P)
    (A:PreAbstractSimplicialComplex V) (F:Finset V) (hCard:3≤F.card)
    (hProper:∀S:Finset V,S.Nonempty→S⊂F→S∈A) (hAbsent:F∉A)
    (f:C(simplicialRealization A,Fin n→ℝ))
    (hf:∀x,P (finiteSimplexSupport x.1) (f x)) :
    ∃g:C(simplicialRealization (A⊔fullFaceComplex F),Fin n→ℝ),
      (∀x:simplicialRealization A,
        g ⟨x.1,(simplicialRealization_mono le_sup_left) x.2⟩=f x) ∧
      ∀x,P (finiteSimplexSupport x.1) (g x) := by
  let inclusion:C(simplicialRealization (boundaryFaceComplex F),simplicialRealization A):=
    ContinuousMap.inclusion (simplicialRealization_mono (boundaryFaceComplex_le_of_proper A F hProper))
  obtain ⟨gFace,hFaceBoundary,hFaceP⟩:=exists_supportLocal_face_extension P hP F hCard
    (f.comp inclusion) (fun x=>hf (inclusion x))
  have hCompatible:∀(x:stdSimplex ℝ V)(hxA:x∈simplicialRealization A)
      (hxF:x∈simplicialRealization (fullFaceComplex F)),f ⟨x,hxA⟩=gFace ⟨x,hxF⟩:=by
    intro x hxA hxF
    have hxB:x∈simplicialRealization (boundaryFaceComplex F):=by
      have hxI:x∈simplicialRealization (A⊓fullFaceComplex F):=⟨hxA,hxF⟩
      rwa [inf_fullFaceComplex_eq_boundary A F hProper hAbsent] at hxI
    exact (hFaceBoundary ⟨x,hxB⟩).symm
  let g:=attachOneFaceMap A F f gFace hCompatible
  refine ⟨g,attachOneFaceMap_old A F f gFace hCompatible,?_⟩
  intro x
  rcases x.2 with hxA|hxF
  · have hOld:=attachOneFaceMap_old A F f gFace hCompatible ⟨x.1,hxA⟩
    rw [hOld]
    exact hf ⟨x.1,hxA⟩
  · have hNew:=attachOneFaceMap_face A F f gFace hCompatible ⟨x.1,hxF⟩
    rw [hNew]
    exact hFaceP ⟨x.1,hxF⟩

end FairDivision.Topology
