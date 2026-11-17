import FairDivision.Topology.Volovikov.UniversalJoinDoublingPushforward
import FairDivision.Topology.Volovikov.UniversalJoinDoublingMass
import FairDivision.Topology.Volovikov.UniversalJoinDoublingFace

/-!
# Exact weights of the doubled universal join

The first block carries weight `1-t` and the second carries weight `t`.
These formulas recover the join parameter and the two noncollapsed factors.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The first color-block embedding is injective. -/
theorem leftDoubledJoinVertex_injective
    {m : ℕ} {G : Type*} :
    Function.Injective (leftDoubledJoinVertex (m := m) (G := G)) := by
  intro v w h
  apply Prod.ext
  · exact Fin.castAdd_injective m m (congrArg Prod.fst h)
  · simpa [leftDoubledJoinVertex] using congrArg Prod.snd h

/-- The second color-block embedding is injective. -/
theorem rightDoubledJoinVertex_injective
    {m : ℕ} {G : Type*} :
    Function.Injective (rightDoubledJoinVertex (m := m) (G := G)) := by
  intro v w h
  apply Prod.ext
  · exact Fin.natAdd_injective m m (congrArg Prod.fst h)
  · simpa [rightDoubledJoinVertex] using congrArg Prod.snd h

/-- A first-block vertex is never a second-block vertex. -/
theorem leftDoubledJoinVertex_ne_right
    {m : ℕ} {G : Type*} (v w : Fin m × G) :
    leftDoubledJoinVertex v ≠ rightDoubledJoinVertex w := by
  intro h
  have hval := congrArg Fin.val (congrArg Prod.fst h)
  simp only [leftDoubledJoinVertex, rightDoubledJoinVertex,
    Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

/-- Pushing to the first block preserves source weights there. -/
theorem leftDoubledMap_apply_left
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin m × G)) (v : Fin m × G) :
    (stdSimplex.map leftDoubledJoinVertex w).1
      (leftDoubledJoinVertex v) = w.1 v :=
  finiteSimplexMap_apply_injective leftDoubledJoinVertex
    leftDoubledJoinVertex_injective w v

/-- Pushing to the second block preserves source weights there. -/
theorem rightDoubledMap_apply_right
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin m × G)) (v : Fin m × G) :
    (stdSimplex.map rightDoubledJoinVertex w).1
      (rightDoubledJoinVertex v) = w.1 v :=
  finiteSimplexMap_apply_injective rightDoubledJoinVertex
    rightDoubledJoinVertex_injective w v

/-- A first-block simplex pushforward vanishes on the other block. -/
theorem leftDoubledMap_apply_right
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin m × G)) (v : Fin m × G) :
    (stdSimplex.map leftDoubledJoinVertex w).1
      (rightDoubledJoinVertex v) = 0 := by
  apply finiteSimplexMap_apply_not_mem_range
  rintro ⟨u, hu⟩
  exact leftDoubledJoinVertex_ne_right u v hu

/-- A second-block simplex pushforward vanishes on the first block. -/
theorem rightDoubledMap_apply_left
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin m × G)) (v : Fin m × G) :
    (stdSimplex.map rightDoubledJoinVertex w).1
      (leftDoubledJoinVertex v) = 0 := by
  apply finiteSimplexMap_apply_not_mem_range
  rintro ⟨u, hu⟩
  exact leftDoubledJoinVertex_ne_right v u hu.symm

/-- The doubled point has first-block coordinates `(1-t) x`. -/
theorem doubledJoinCylinderSimplex_apply_left
    {m : ℕ} {G : Type*} [Fintype G]
    (z : I ×
      (simplicialRealization (universalJoinComplex m G) ×
        simplicialRealization (universalJoinComplex m G)))
    (v : Fin m × G) :
    (doubledJoinCylinderSimplex m G z).1 (leftDoubledJoinVertex v) =
      (1 - (z.1 : ℝ)) * z.2.1.1.1 v := by
  change (1 - (z.1 : ℝ)) *
      (stdSimplex.map leftDoubledJoinVertex z.2.1.1).1 (leftDoubledJoinVertex v) +
      (z.1 : ℝ) *
      (stdSimplex.map rightDoubledJoinVertex z.2.2.1).1 (leftDoubledJoinVertex v) = _
  rw [leftDoubledMap_apply_left, rightDoubledMap_apply_left]
  ring

/-- The doubled point has second-block coordinates `t y`. -/
theorem doubledJoinCylinderSimplex_apply_right
    {m : ℕ} {G : Type*} [Fintype G]
    (z : I ×
      (simplicialRealization (universalJoinComplex m G) ×
        simplicialRealization (universalJoinComplex m G)))
    (v : Fin m × G) :
    (doubledJoinCylinderSimplex m G z).1 (rightDoubledJoinVertex v) =
      (z.1 : ℝ) * z.2.2.1.1 v := by
  change (1 - (z.1 : ℝ)) *
      (stdSimplex.map leftDoubledJoinVertex z.2.1.1).1 (rightDoubledJoinVertex v) +
      (z.1 : ℝ) *
      (stdSimplex.map rightDoubledJoinVertex z.2.2.1).1 (rightDoubledJoinVertex v) = _
  rw [leftDoubledMap_apply_right, rightDoubledMap_apply_right]
  ring

/-- The first-block mass of a doubled point is `1-t`. -/
theorem leftDoubledJoinMass_cylinder
    {m : ℕ} {G : Type*} [Fintype G]
    (z : I ×
      (simplicialRealization (universalJoinComplex m G) ×
        simplicialRealization (universalJoinComplex m G))) :
    leftDoubledJoinMass (doubledJoinCylinderSimplex m G z) =
      1 - (z.1 : ℝ) := by
  simp only [leftDoubledJoinMass, doubledJoinCylinderSimplex_apply_left,
    ← Finset.mul_sum, z.2.1.1.2.2, mul_one]

/-- The second-block mass of a doubled point is `t`. -/
theorem rightDoubledJoinMass_cylinder
    {m : ℕ} {G : Type*} [Fintype G]
    (z : I ×
      (simplicialRealization (universalJoinComplex m G) ×
        simplicialRealization (universalJoinComplex m G))) :
    rightDoubledJoinMass (doubledJoinCylinderSimplex m G z) =
      (z.1 : ℝ) := by
  simp only [rightDoubledJoinMass, doubledJoinCylinderSimplex_apply_right,
    ← Finset.mul_sum, z.2.2.1.2.2, mul_one]

end FairDivision.Topology.Volovikov
