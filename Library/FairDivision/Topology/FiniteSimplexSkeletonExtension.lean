import FairDivision.Topology.FiniteCoordinateMaxFaceExtension

/-!
# Finite closed-face induction for the manuscript virtual-value map

The base is the actual continuous one-skeleton map. At each step choose a
smallest missing face, whose proper boundary is already defined. Its at
least three vertices permit the actual capwise coordinate-maximum fill.
Existing closed pasting preserves the old map exactly. The finite set of
missing faces strictly decreases, so the resulting continuous map covers
the entire simplex and preserves the predicate at its actual support.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- Extend from the complete one-skeleton of a finite complex, preserving
an abstract support-local predicate with the manuscript's two closure laws.
The geometric fill is the proved capwise extension, not an input oracle. -/
theorem exists_supportLocal_complex_extension {V:Type*} [Fintype V] {n:ℕ}
    (P:Finset V→(Fin n→ℝ)→Prop) (hP:SupportLocalMaxClosed P)
    (A K:PreAbstractSimplicialComplex V) (hAK:A≤K)
    (hSmall:∀S:Finset V,S∈K→S.card≤2→S∈A)
    (f:C(simplicialRealization A,Fin n→ℝ))
    (hf:∀x,P (finiteSimplexSupport x.1) (f x)) :
    ∃g:C(simplicialRealization K,Fin n→ℝ),
      (∀x:simplicialRealization A,g ⟨x.1,(simplicialRealization_mono hAK) x.2⟩=f x) ∧
      ∀x,P (finiteSimplexSupport x.1) (g x) := by
  classical
  have aux:∀t:ℕ,∀(B:PreAbstractSimplicialComplex V)(hBK:B≤K),
      (∀S:Finset V,S∈K→S.card≤2→S∈B)→(missingFaces B K).card=t→
      ∀(q:C(simplicialRealization B,Fin n→ℝ)),
      (∀x,P (finiteSimplexSupport x.1) (q x))→
      ∃g:C(simplicialRealization K,Fin n→ℝ),
        (∀x:simplicialRealization B,g ⟨x.1,(simplicialRealization_mono hBK) x.2⟩=q x) ∧
        ∀x,P (finiteSimplexSupport x.1) (g x):=by
    intro t
    induction t using Nat.strong_induction_on with
    |h t ih=>
      intro B hBK hSmallB hCount q hq
      by_cases hKB:K≤B
      ·have hEq:B=K:=le_antisymm hBK hKB
       subst B
       exact ⟨q,fun _=>rfl,hq⟩
      ·obtain ⟨F,hFK,hAbsent,hF,hProper⟩:=exists_minimal_missing_face B K hKB
       have hCard:3≤F.card:=by
         by_contra hNot
         have hTwo:F.card≤2:=by omega
         exact hAbsent (hSmallB F hFK hTwo)
       let B':=B⊔fullFaceComplex F
       have hB'K:B'≤K:=sup_le hBK (fullFaceComplex_le_of_mem K F hFK)
       have hSmallB':∀S:Finset V,S∈K→S.card≤2→S∈B':=by
         intro S hSK hSCard
         exact Or.inl (hSmallB S hSK hSCard)
       have hSmaller:(missingFaces B' K).card<t:=by
         rw [←hCount]
         exact Finset.card_lt_card (missingFaces_attach_ssubset B K F hFK hAbsent)
       obtain ⟨q',hOld,hNewP⟩:=exists_supportLocal_attach_face P hP B F hCard hProper hAbsent q hq
       obtain ⟨g,hg,hgP⟩:=ih (missingFaces B' K).card hSmaller B' hB'K hSmallB' rfl q' hNewP
       refine ⟨g,?_,hgP⟩
       intro x
       calc
         g ⟨x.1,(simplicialRealization_mono hBK) x.2⟩=
             q' ⟨x.1,(simplicialRealization_mono le_sup_left) x.2⟩:=
           hg ⟨x.1,(simplicialRealization_mono le_sup_left) x.2⟩
         _=q x:=hOld x
  exact aux (missingFaces A K).card A hAK hSmall rfl f hf

/-- Final finite-simplex extension with the literal support-cardinality
source used by the actual edge construction. All one-skeleton values stay
unchanged; every full-simplex value satisfies P at its own positive support. -/
theorem exists_supportLocal_simplex_extension {V:Type*} [Fintype V] {n:ℕ}
    (P:Finset V→(Fin n→ℝ)→Prop) (hP:SupportLocalMaxClosed P)
    (base:C(SmallSupportSimplex V 2,Fin n→ℝ))
    (hBase:∀x,P (finiteSimplexSupport x.1) (base x)) :
    ∃F:C(stdSimplex ℝ V,Fin n→ℝ),
      (∀x:SmallSupportSimplex V 2,F x.1=base x) ∧
      ∀x,P (finiteSimplexSupport x) (F x) := by
  classical
  let A:=finiteSimplexSkeleton V 2
  let K:PreAbstractSimplicialComplex V:=⊤
  let e:=finiteSimplexSkeletonHomeomorph V 2
  let f:C(simplicialRealization A,Fin n→ℝ):=base.comp (e : C(simplicialRealization A,SmallSupportSimplex V 2))
  have hAK:A≤K:=le_top
  have hSmall:∀S:Finset V,S∈K→S.card≤2→S∈A:=by
    intro S hSK hCard
    exact ⟨hSK,hCard⟩
  obtain ⟨g,hg,hgP⟩:=exists_supportLocal_complex_extension P hP A K hAK hSmall f
    (fun x=>hBase (e x))
  let inclusionMap:C(stdSimplex ℝ V,simplicialRealization K):=
    ⟨fun x=>⟨x,finiteSimplexSupport_nonempty x⟩,by
      apply Continuous.subtype_mk
      exact continuous_id⟩
  let F:C(stdSimplex ℝ V,Fin n→ℝ):=g.comp inclusionMap
  refine ⟨F,?_,?_⟩
  ·intro x
   have h:=hg (e.symm x)
   change F x.1 = base (e (e.symm x)) at h
   rw [e.apply_symm_apply] at h
   exact h
  ·intro x
   exact hgP (inclusionMap x)

end FairDivision.Topology
