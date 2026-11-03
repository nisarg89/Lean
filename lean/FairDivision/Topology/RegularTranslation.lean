import Mathlib

/-!
# Regular translation and the reduced score representation

For the Volovikov step, a prime-power group acts regularly on the labeled
positions. The reduced permutation representation consists of score vectors
whose coordinates sum to zero. Its only vector fixed by every translation is
zero. This file proves that fact for any additive group with a position
bijection, before specializing to a p-torus.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Transport left translation on an additive group to labeled positions. -/
def regularPositionPerm {n : ℕ} {G : Type*} [AddGroup G]
    (e : Fin n ≃ G) (g : G) : Equiv.Perm (Fin n) :=
  (e.trans (Equiv.addLeft g)).trans e.symm

@[simp] theorem regularPositionPerm_apply {n : ℕ} {G : Type*}
    [AddGroup G] (e : Fin n ≃ G) (g : G) (i : Fin n) :
    regularPositionPerm e g i = e.symm (g + e i) := rfl

/-- The transported translation action is transitive on positions. -/
theorem regularPositionPerm_transitive {n : ℕ} {G : Type*}
    [AddGroup G] (e : Fin n ≃ G) (i j : Fin n) :
    ∃ g : G, regularPositionPerm e g i = j := by
  refine ⟨e j - e i, ?_⟩
  apply e.injective
  simp [regularPositionPerm_apply]

/-- A centered score vector fixed by every regular translation is zero. -/
theorem centered_regular_fixed_zero {n : ℕ} {G : Type*}
    [AddGroup G] (e : Fin n ≃ G)
    (x : Fin n → ℝ)
    (hcenter : (∑ i : Fin n, x i) = 0)
    (hfixed : ∀ g : G, ∀ i : Fin n,
      x (regularPositionPerm e g i) = x i) :
    ∀ i : Fin n, x i = 0 := by
  let i₀ : Fin n := e.symm 0
  have hconstant (i : Fin n) : x i = x i₀ := by
    obtain ⟨g, hg⟩ := regularPositionPerm_transitive e i i₀
    rw [← hg, hfixed g i]
  have hsum : (n : ℝ) * x i₀ = 0 := by
    calc
      (n : ℝ) * x i₀ = ∑ i : Fin n, x i₀ := by simp
      _ = ∑ i : Fin n, x i := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hconstant i).symm
      _ = 0 := hcenter
  have hn : (0 : ℝ) < n := by
    have hnNat : 0 < n := lt_of_le_of_lt (Nat.zero_le i₀.val) i₀.isLt
    exact_mod_cast hnNat
  have hx₀ : x i₀ = 0 :=
    (mul_eq_zero.mp hsum).resolve_left (ne_of_gt hn)
  intro i
  rw [hconstant i, hx₀]

/-- The additive p-torus of rank `r` has exactly `p^r` elements. -/
theorem pTorus_card (p r : ℕ) [NeZero p] :
    Fintype.card (Fin r → ZMod p) = p ^ r := by
  rw [Fintype.card_pi_const, ZMod.card]

/-- Identify `p^r` labeled positions with the additive p-torus. -/
noncomputable def pTorusPositionEquiv (p r : ℕ) [NeZero p] :
    Fin (p ^ r) ≃ (Fin r → ZMod p) :=
  (Fintype.equivFinOfCardEq (pTorus_card p r)).symm

/-- Translation of the p-torus, transported to the labeled positions. -/
noncomputable def pTorusPositionPerm (p r : ℕ) [NeZero p]
    (g : Fin r → ZMod p) : Equiv.Perm (Fin (p ^ r)) :=
  regularPositionPerm (pTorusPositionEquiv p r) g

/-- The reduced regular score representation of the p-torus has no nonzero
common fixed vector. -/
theorem pTorus_centered_fixed_zero (p r : ℕ) [NeZero p]
    (x : Fin (p ^ r) → ℝ)
    (hcenter : (∑ i : Fin (p ^ r), x i) = 0)
    (hfixed : ∀ g : Fin r → ZMod p, ∀ i : Fin (p ^ r),
      x (pTorusPositionPerm p r g i) = x i) :
    ∀ i : Fin (p ^ r), x i = 0 :=
  centered_regular_fixed_zero (pTorusPositionEquiv p r) x hcenter hfixed

end FairDivision.Topology
