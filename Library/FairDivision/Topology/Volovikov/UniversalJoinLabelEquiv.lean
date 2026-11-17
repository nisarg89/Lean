import FairDivision.Topology.Volovikov.UniversalJoinRealization
import FairDivision.Topology.Volovikov.ComplexFiniteJoinReduction

/-!
# Relabeling a universal join by a group equivalence

This transport preserves the source colors and every barycentric weight.
It allows an obstruction to be used with the one-coordinate function
presentation of a cyclic elementary-abelian group, without a new no-map
hypothesis for the equivalent group presentation.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open scoped Classical
open FairDivision.Topology.NerveConnectivity

private theorem universalJoinFace_image_equiv {N : ℕ} {G H : Type*}
    (e : G≃H) {S : Finset (Fin N×G)} (hS : IsUniversalJoinFace S) :
    IsUniversalJoinFace (S.image ((Equiv.refl (Fin N)).prodCongr e)) := by
  classical
  refine ⟨hS.1.image _,?_⟩
  intro i h k hh hk
  obtain ⟨⟨j,g⟩,hj,hjg⟩:=Finset.mem_image.mp hh
  obtain ⟨⟨l,g'⟩,hl,hlg⟩:=Finset.mem_image.mp hk
  have hj' : j=i:=congrArg Prod.fst hjg
  have hl' : l=i:=congrArg Prod.fst hlg
  subst j
  subst l
  have hLabels : g=g':=hS.2 i g g' hj hl
  have ha : e g=h:=congrArg Prod.snd hjg
  have hb : e g'=k:=congrArg Prod.snd hlg
  exact ha.symm.trans ((congrArg e hLabels).trans hb)

/-- Exact color-preserving homeomorphism under an equivalence of labels. -/
noncomputable def universalJoinLabelHomeomorph (N : ℕ) {G H : Type*}
    [Fintype G] [Fintype H] (e : G≃H) :
    simplicialRealization (universalJoinComplex N G)≃ₜ
      simplicialRealization (universalJoinComplex N H) := by
  classical
  apply realizationHomeomorphOfVertexEquiv
    (universalJoinComplex N G) (universalJoinComplex N H)
    ((Equiv.refl (Fin N)).prodCongr e)
  · intro S hS
    exact universalJoinFace_image_equiv e hS
  · intro S hS
    exact universalJoinFace_image_equiv e.symm hS

/-- Relabeling intertwines the actual additive translations. -/
theorem universalJoinLabelHomeomorph_translate {N : ℕ} {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (e : G≃+H) (a : G)
    (x : simplicialRealization (universalJoinComplex N G)) :
    universalJoinLabelHomeomorph N e.toEquiv (translateJoinRealization a x)=
      translateJoinRealization (e a) (universalJoinLabelHomeomorph N e.toEquiv x) := by
  classical
  apply Subtype.ext
  change stdSimplex.map ((Equiv.refl (Fin N)).prodCongr e.toEquiv)
      (stdSimplex.map (translateJoinVertexEquiv a) x.1)=
    stdSimplex.map (translateJoinVertexEquiv (e a))
      (stdSimplex.map ((Equiv.refl (Fin N)).prodCongr e.toEquiv) x.1)
  rw [stdSimplex.map_comp_apply,stdSimplex.map_comp_apply]
  congr 1
  funext v
  rcases v with ⟨i,g⟩
  simp [translateJoinVertexEquiv,translateJoinVertex,map_add]

/-- The finite-source complex no-map theorem is invariant under an exact
group isomorphism. This transports both source labels and target indices. -/
theorem complexFiniteJoinNoMap_of_addEquiv {m : ℕ} {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (e : G≃+H) (hH : ComplexFiniteJoinNoMap m H) : ComplexFiniteJoinNoMap m G := by
  intro F hCenter hNonzero hEquivariant
  let source:=universalJoinLabelHomeomorph (m+m) e.symm.toEquiv
  let f : C(simplicialRealization (universalJoinComplex (m+m) H),H→ℂ) :=
    ⟨fun x h=>F (source x) (e.symm h),by
      apply continuous_pi
      intro h
      exact (continuous_apply (e.symm h)).comp (F.continuous.comp source.continuous)⟩
  apply hH f
  · intro x
    change (∑h : H,F (source x) (e.symm h))=0
    exact (e.symm.sum_comp (F (source x))).trans (hCenter (source x))
  · intro x hZero
    apply hNonzero (source x)
    funext g
    have hg:=congrFun hZero (e g)
    simpa [f] using hg
  · intro a x
    funext h
    change F (source (translateJoinRealization a x)) (e.symm h)=
      F (source x) (e.symm (h-a))
    rw [universalJoinLabelHomeomorph_translate e.symm a x,hEquivariant]
    simp only [complexRegularTranslate,map_sub,source]

/-- A single elementary-abelian coordinate is the cyclic group itself. -/
def finOneFunctionAddEquiv (G : Type*) [AddCommGroup G] : (Fin 1→G)≃+G where
  toFun f:=f 0
  invFun g:=fun _=>g
  left_inv f:=by funext i;exact congrArg f (Subsingleton.elim _ _)
  right_inv _:=rfl
  map_add' _ _:=rfl

end FairDivision.Topology.Volovikov
