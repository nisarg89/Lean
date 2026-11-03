import FairDivision.Topology.Volovikov.UniversalJoinDoublingFace
import Mathlib.Data.Fintype.BigOperators

/-!
# Probability mass in the two doubled join blocks

A probability vector on the doubled vertex set splits into the mass carried
by the first and second color blocks. These identities are the coordinate
input for the inverse of the doubled-join map.
-/

set_option autoImplicit false

open scoped Topology Classical unitInterval

namespace FairDivision.Topology.Volovikov

/-- Sum a function over the two disjoint color blocks. -/
theorem doubledJoin_sum_blocks
    {m : ℕ} {G : Type*} [Fintype G]
    (f : Fin (m + m) × G → ℝ) :
    (∑ v : Fin (m + m) × G, f v) =
      (∑ v : Fin m × G, f (leftDoubledJoinVertex v)) +
      (∑ v : Fin m × G, f (rightDoubledJoinVertex v)) := by
  classical
  let e : (Fin m × G) ⊕ (Fin m × G) ≃ Fin (m + m) × G :=
    (Equiv.sumProdDistrib (Fin m) (Fin m) G).symm.trans
      (Equiv.prodCongr finSumFinEquiv (Equiv.refl G))
  calc
    (∑ v : Fin (m + m) × G, f v) =
        ∑ v : (Fin m × G) ⊕ (Fin m × G), f (e v) :=
      (e.sum_comp f).symm
    _ = (∑ v : Fin m × G, f (leftDoubledJoinVertex v)) +
        (∑ v : Fin m × G, f (rightDoubledJoinVertex v)) := by
      rw [Fintype.sum_sum_type]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro v _ <;>
        simp [e, leftDoubledJoinVertex, rightDoubledJoinVertex]

/-- Mass in the first color block. -/
def leftDoubledJoinMass
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin (m + m) × G)) : ℝ :=
  ∑ v : Fin m × G, w.1 (leftDoubledJoinVertex v)

/-- Mass in the second color block. -/
def rightDoubledJoinMass
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin (m + m) × G)) : ℝ :=
  ∑ v : Fin m × G, w.1 (rightDoubledJoinVertex v)

/-- The two block masses add to one. -/
theorem leftDoubledJoinMass_add_right
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin (m + m) × G)) :
    leftDoubledJoinMass w + rightDoubledJoinMass w = 1 := by
  change (∑ v : Fin m × G, w.1 (leftDoubledJoinVertex v)) +
    (∑ v : Fin m × G, w.1 (rightDoubledJoinVertex v)) = 1
  rw [← doubledJoin_sum_blocks]
  exact w.2.2

/-- Each block has nonnegative mass. -/
theorem leftDoubledJoinMass_nonneg
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin (m + m) × G)) :
    0 ≤ leftDoubledJoinMass w := by
  classical
  exact Finset.sum_nonneg (fun v _ => w.2.1 _)

theorem rightDoubledJoinMass_nonneg
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin (m + m) × G)) :
    0 ≤ rightDoubledJoinMass w := by
  classical
  exact Finset.sum_nonneg (fun v _ => w.2.1 _)

/-- First-block mass varies continuously. -/
theorem leftDoubledJoinMass_continuous
    {m : ℕ} {G : Type*} [Fintype G] :
    Continuous (leftDoubledJoinMass (m := m) (G := G)) := by
  unfold leftDoubledJoinMass
  apply continuous_finset_sum
  intro v _
  exact (continuous_apply (leftDoubledJoinVertex v)).comp continuous_subtype_val

/-- Second-block mass varies continuously. -/
theorem rightDoubledJoinMass_continuous
    {m : ℕ} {G : Type*} [Fintype G] :
    Continuous (rightDoubledJoinMass (m := m) (G := G)) := by
  unfold rightDoubledJoinMass
  apply continuous_finset_sum
  intro v _
  exact (continuous_apply (rightDoubledJoinVertex v)).comp continuous_subtype_val

/-- The second-block mass is a point of the unit interval. -/
def rightDoubledJoinTime
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin (m + m) × G)) : I :=
  ⟨rightDoubledJoinMass w,
    ⟨rightDoubledJoinMass_nonneg w,
      by
        have h := leftDoubledJoinMass_add_right w
        linarith [leftDoubledJoinMass_nonneg w]⟩⟩

/-- The join parameter varies continuously with the doubled vector. -/
theorem rightDoubledJoinTime_continuous
    {m : ℕ} {G : Type*} [Fintype G] :
    Continuous (rightDoubledJoinTime (m := m) (G := G)) := by
  exact rightDoubledJoinMass_continuous.subtype_mk _

end FairDivision.Topology.Volovikov
