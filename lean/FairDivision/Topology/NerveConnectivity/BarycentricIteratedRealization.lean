import FairDivision.Topology.NerveConnectivity.BarycentricAffineTransport
import FairDivision.Topology.NerveConnectivity.BarycentricMeshIteration
import FairDivision.Topology.NerveConnectivity.BarycentricHomeomorph

/-!
# Geometric realization of iterated barycentric subdivision

Each iterated abstract complex has a finite vertex type. Composing the
one-step barycentric homeomorphisms identifies its realization with the
original realization. Affine evaluation agrees with the recursively
assigned centroid points at every level.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

noncomputable instance iteratedBarycentricVertex_fintype
    {V : Type u} [Fintype V] (n : ℕ) :
    Fintype (iteratedBarycentricVertex V n) := by
  induction n with
  | zero =>
      change Fintype V
      infer_instance
  | succ n ih =>
      change Fintype (Finset (iteratedBarycentricVertex V n))
      letI : Fintype (iteratedBarycentricVertex V n) := ih
      infer_instance

/-- The realization of any iterated barycentric subdivision is
homeomorphic to the original finite realization. -/
noncomputable def iteratedBarycentricRealizationHomeomorph
    {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    (n : ℕ) → simplicialRealization (iteratedBarycentricComplex K n) ≃ₜ
      simplicialRealization K
  | 0 => Homeomorph.refl _
  | n + 1 =>
      (barycentricRealizationHomeomorph (iteratedBarycentricComplex K n)).trans
        (iteratedBarycentricRealizationHomeomorph K n)

/-- Composed subdivision homeomorphisms preserve affine evaluation in
any real normed vector space. -/
theorem finiteSimplexAffinePoint_iteratedBarycentric
    {V : Type u} {E : Type v} [Fintype V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (p : V → E) :
    ∀ (n : ℕ) (z : simplicialRealization (iteratedBarycentricComplex K n)),
      finiteSimplexAffinePoint p
        (iteratedBarycentricRealizationHomeomorph K n z).1 =
      finiteSimplexAffinePoint (iteratedBarycentricPoint p n) z.1 := by
  intro n
  induction n with
  | zero =>
      intro z
      rfl
  | succ n ih =>
      intro z
      let z' := barycentricRealizationHomeomorph
        (iteratedBarycentricComplex K n) z
      calc
        finiteSimplexAffinePoint p
            (iteratedBarycentricRealizationHomeomorph K (n + 1) z).1 =
          finiteSimplexAffinePoint p
            (iteratedBarycentricRealizationHomeomorph K n z').1 := rfl
        _ = finiteSimplexAffinePoint (iteratedBarycentricPoint p n) z'.1 :=
          ih z'
        _ = finiteSimplexAffinePoint
            (iteratedBarycentricPoint p (n + 1)) z.1 := by
          exact finiteSimplexAffinePoint_barycentricForward
            (iteratedBarycentricComplex K n)
            (iteratedBarycentricPoint p n) z

end FairDivision.Topology.NerveConnectivity
