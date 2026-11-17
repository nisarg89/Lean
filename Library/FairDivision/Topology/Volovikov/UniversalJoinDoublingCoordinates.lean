import FairDivision.Topology.Volovikov.UniversalJoinRealization
import FairDivision.Topology.FiniteSimplexSegment

/-!
# Coordinates for doubling a finite universal join

The two copies of `G^{*m}` occupy disjoint blocks of the vertices of
`G^{*(m+m)}`. Their probability vectors are joined by the ordinary convex
segment. This is the cylinder map underlying the real-to-complex doubling
argument; the descent through the topological join and the homeomorphism
remain separate theorems.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- Embed a vertex in the first block of the doubled universal join. -/
def leftDoubledJoinVertex {m : ℕ} {G : Type*}
    (v : Fin m × G) : Fin (m + m) × G :=
  (Fin.castAdd m v.1, v.2)

/-- Embed a vertex in the second block of the doubled universal join. -/
def rightDoubledJoinVertex {m : ℕ} {G : Type*}
    (v : Fin m × G) : Fin (m + m) × G :=
  (Fin.natAdd m v.1, v.2)

/-- Weighted coordinates for two finite joins in disjoint vertex blocks. -/
noncomputable def doubledJoinCylinderSimplex
    (m : ℕ) (G : Type*) [Fintype G]
    (z : I ×
      (simplicialRealization (universalJoinComplex m G) ×
        simplicialRealization (universalJoinComplex m G))) :
    stdSimplex ℝ (Fin (m + m) × G) :=
  FairDivision.Topology.finiteSimplexSegment
    (stdSimplex.map leftDoubledJoinVertex z.2.1.1)
    (stdSimplex.map rightDoubledJoinVertex z.2.2.1) z.1

/-- The doubled coordinates vary continuously in both points and time. -/
theorem doubledJoinCylinderSimplex_continuous
    (m : ℕ) (G : Type*) [Fintype G] :
    Continuous (doubledJoinCylinderSimplex m G) := by
  have hleft : Continuous
      (fun z : I ×
        (simplicialRealization (universalJoinComplex m G) ×
          simplicialRealization (universalJoinComplex m G)) =>
        stdSimplex.map leftDoubledJoinVertex z.2.1.1) :=
    (stdSimplex.continuous_map leftDoubledJoinVertex).comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hright : Continuous
      (fun z : I ×
        (simplicialRealization (universalJoinComplex m G) ×
          simplicialRealization (universalJoinComplex m G)) =>
        stdSimplex.map rightDoubledJoinVertex z.2.2.1) :=
    (stdSimplex.continuous_map rightDoubledJoinVertex).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  exact FairDivision.Topology.finiteSimplexSegment_continuous.comp
    (continuous_fst.prodMk (hleft.prodMk hright))

end FairDivision.Topology.Volovikov
