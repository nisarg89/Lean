import FairDivision.Topology.Volovikov.UniversalJoinDoublingFace
import FairDivision.Topology.Volovikov.UniversalJoinRealization

/-!
# Equivariance of the doubled join coordinates

Translation of labels commutes with embedding either color block and with
convex interpolation of the two embedded simplex points.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The label translation homeomorphism viewed as a continuous map. -/
noncomputable def translateJoinMap {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G] (a : G) :
    C(simplicialRealization (universalJoinComplex m G),
      simplicialRealization (universalJoinComplex m G)) :=
  ⟨translateJoinRealization a, (translateJoinRealization a).continuous⟩

private theorem leftDoubledJoinVertex_translate
    {m : ℕ} {G : Type*} [AddGroup G] (a : G) :
    (leftDoubledJoinVertex (m := m) (G := G)) ∘ translateJoinVertex a =
      translateJoinVertex a ∘ leftDoubledJoinVertex := by
  funext v
  rcases v with ⟨i, g⟩
  rfl

private theorem rightDoubledJoinVertex_translate
    {m : ℕ} {G : Type*} [AddGroup G] (a : G) :
    (rightDoubledJoinVertex (m := m) (G := G)) ∘ translateJoinVertex a =
      translateJoinVertex a ∘ rightDoubledJoinVertex := by
  funext v
  rcases v with ⟨i, g⟩
  rfl

/-- Pushing a probability vector along a vertex map commutes with straight
segments because the pushforward is linear. -/
theorem finiteSimplexSegment_map
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V → W) (x y : stdSimplex ℝ V) (t : I) :
    stdSimplex.map f (FairDivision.Topology.finiteSimplexSegment x y t) =
      FairDivision.Topology.finiteSimplexSegment
        (stdSimplex.map f x) (stdSimplex.map f y) t := by
  apply Subtype.ext
  funext w
  simp only [stdSimplex.map_coe, FairDivision.Topology.finiteSimplexSegment]
  change (FunOnFinite.linearMap ℝ ℝ f)
      ((1 - (t : ℝ)) • x.1 + (t : ℝ) • y.1) w =
    (1 - (t : ℝ)) • ((FunOnFinite.linearMap ℝ ℝ f) x.1) w +
      (t : ℝ) • ((FunOnFinite.linearMap ℝ ℝ f) y.1) w
  rw [map_add, map_smul, map_smul]
  rfl

/-- Label translation commutes with the weighted doubled join point. -/
theorem doubledJoinCylinderPoint_translate
    {m : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (a : G)
    (z : I ×
      (simplicialRealization (universalJoinComplex m G) ×
        simplicialRealization (universalJoinComplex m G))) :
    doubledJoinCylinderPoint m G
        (z.1, (translateJoinRealization a z.2.1,
          translateJoinRealization a z.2.2)) =
      translateJoinRealization a (doubledJoinCylinderPoint m G z) := by
  apply Subtype.ext
  change FairDivision.Topology.finiteSimplexSegment
      (stdSimplex.map leftDoubledJoinVertex
        (stdSimplex.map (translateJoinVertex a) z.2.1.1))
      (stdSimplex.map rightDoubledJoinVertex
        (stdSimplex.map (translateJoinVertex a) z.2.2.1)) z.1 =
    stdSimplex.map (translateJoinVertex a)
      (FairDivision.Topology.finiteSimplexSegment
        (stdSimplex.map leftDoubledJoinVertex z.2.1.1)
        (stdSimplex.map rightDoubledJoinVertex z.2.2.1) z.1)
  rw [finiteSimplexSegment_map]
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply,
    stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  rw [leftDoubledJoinVertex_translate, rightDoubledJoinVertex_translate]

/-- The doubled map is equivariant for simultaneous translation on the two
join factors. -/
theorem doubledJoinMap_equivariant
    {m : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (a : G)
    (z : TopologicalJoin
      (simplicialRealization (universalJoinComplex m G))
      (simplicialRealization (universalJoinComplex m G))) :
    doubledJoinMap m G
        (topologicalJoinMap
          (translateJoinMap a)
          (translateJoinMap a) z) =
      translateJoinRealization a (doubledJoinMap m G z) := by
  induction z using Quotient.inductionOn with
  | _ z =>
      exact doubledJoinCylinderPoint_translate a z

end FairDivision.Topology.Volovikov
