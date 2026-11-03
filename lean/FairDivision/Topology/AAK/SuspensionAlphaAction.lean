import FairDivision.Topology.AAK.SuspensionAlphaList
import FairDivision.Topology.AAK.SuspendedJoinPoleHomotopy

/-!
# Actual equivariance of suspension-list normalization

The target action translates free labels by −1 and fixes both poles, exactly
the imported DKGM `vact (gen p)` convention after `Multiplicative.ofAdd`.
The wedge-action identity is reused, componentwise, through the raw three-cone
model and the actual relative projection. No equivariance hypothesis for
normalization is added to the final obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.SuspensionRelativeChains

open Dvoretzky.Dold ZeroFreeBipyramid
open scoped Classical

variable {R : Type*} [CommRing R] {D p : ℕ} [Fact p.Prime]

private theorem free_generator_vertex (i : Fin D) (a : ZMod p) :
    (i,Multiplicative.ofAdd ((-1 : ZMod p)+a))=
      vact (gen p) (i,Multiplicative.ofAdd a) := by
  simp [vact,gen,add_comm]

/-- The literal raw wedge commutes with the actual generator. -/
theorem rawWedge_generator (v : SVertex D p) (z : Raw R D p) :
    rawWedge (suspensionTranslate (-1 : ZMod p) v) (rawGenerator z)=
      rawGenerator (rawWedge v z) := by
  cases v with
  | inl b =>
    cases b <;> simp [suspensionTranslate,rawWedge,rawGenerator_apply,northInsertion,
      southInsertion,baseGenerator]
  | inr v =>
    rcases v with ⟨i,a⟩
    change (wedge (i,Multiplicative.ofAdd ((-1 : ZMod p)+a)) (baseGenerator z.1),
      -wedge (i,Multiplicative.ofAdd ((-1 : ZMod p)+a)) (baseGenerator z.2.1),
      -wedge (i,Multiplicative.ofAdd ((-1 : ZMod p)+a)) (baseGenerator z.2.2))=
      (baseGenerator (wedge (i,Multiplicative.ofAdd a) z.1),
        baseGenerator (-wedge (i,Multiplicative.ofAdd a) z.2.1),
        baseGenerator (-wedge (i,Multiplicative.ofAdd a) z.2.2))
    rw [free_generator_vertex]
    simp only [baseGenerator,wedge_tact,map_neg]

@[simp] theorem rawGenerator_rawEmpty : rawGenerator (rawEmpty : Raw R D p)=rawEmpty := by
  simp [rawEmpty,rawGenerator_apply]

/-- Naturality holds for all lists, before any face or degree condition. -/
theorem rawAlphaList_translate (l : List (SVertex D p)) :
    rawAlphaList (R:=R) (l.map (suspensionTranslate (-1 : ZMod p)))=
      rawGenerator (rawAlphaList l) := by
  induction l with
  | nil => exact rawGenerator_rawEmpty.symm
  | cons v l ih =>
    simp only [List.map_cons,rawAlphaList,ih,rawWedge_generator]

theorem rawAlpha_translate (c : Dvoretzky.Dold.Chain R (SVertex D p)) :
    rawAlpha (actL (suspensionTranslate (-1 : ZMod p)) c)=rawGenerator (rawAlpha c) := by
  have h :
      (rawAlpha (R := R) (D := D) (p := p) ∘ₗ
        actL (R := R) (suspensionTranslate (d := D) (-1 : ZMod p)) :
          Dvoretzky.Dold.Chain R (SVertex D p) →ₗ[R] Raw R D p) =
      rawGenerator (R := R) (D := D) (p := p) ∘ₗ
        rawAlpha (R := R) (D := D) (p := p) := by
    apply chain_hom_ext
    intro l
    simp [rawAlphaList_translate]
  exact LinearMap.congr_fun h c

/-- The actual relative normalization is equivariant for the same cyclic
operator that appears in the proved relative Dold exactness theorem. -/
theorem alpha_translate (c : Dvoretzky.Dold.Chain R (SVertex D p)) :
    alpha (actL (suspensionTranslate (-1 : ZMod p)) c)=generator (alpha c) := by
  change toRelative (rawAlpha (actL (suspensionTranslate (-1 : ZMod p)) c)) =
    generator (toRelative (rawAlpha c))
  rw [rawAlpha_translate,toRelative_generator]

end FairDivision.Topology.AAK.SuspensionRelativeChains
