import FairDivision.Finite.DummyRemovalBalance
import FairDivision.Definitions

/-!
# Euclidean balance after removing fewer than `n` dummies

With `nq` augmented items and `d < n` dummies, the real item count is
`nq-d`. A full augmented bundle containing at most one dummy has exactly
one of the two balanced real-bundle sizes for that count.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- Removing dummies from one full augmented bundle produces a real-bundle
size equal to the floor or ceiling of the real item count divided by `n`. -/
theorem card_removeDummies_isBalancedSize {α : Type*} [DecidableEq α]
    (n q : ℕ) (B D : Finset α)
    (hn : 0 < n) (hq : 0 < q) (hD : D.card < n)
    (hFull : B.card = q) (hCap : (B ∩ D).card ≤ 1) :
    (B \ D).card = (n * q - D.card) / n ∨
      (B \ D).card = FairDivision.upperSize n (n * q - D.card) := by
  by_cases hZero : D.card = 0
  · have hEmpty : D = ∅ := Finset.card_eq_zero.mp hZero
    left
    simp [hEmpty, hFull, Nat.mul_div_cancel_left q hn]
  have hPos : 0 < D.card := Nat.pos_of_ne_zero hZero
  have hRemPos : 0 < n - D.card := Nat.sub_pos_of_lt hD
  have hRemLt : n - D.card < n := Nat.sub_lt hn hPos
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hMul : n * q = n * (q - 1) + n := by
    calc
      n * q = n * (q - 1 + 1) := by rw [hqsub]
      _ = n * (q - 1) + n := by simp [Nat.mul_add]
  have hDecomp : n * q - D.card = n * (q - 1) + (n - D.card) := by
    omega
  have hFloor : (n * q - D.card) / n = q - 1 := by
    rw [hDecomp, Nat.mul_add_div hn (q - 1) (n - D.card)]
    simp [Nat.div_eq_of_lt hRemLt]
  have hMod : (n * q - D.card) % n = n - D.card := by
    rw [hDecomp, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hRemLt
  have hUpper : FairDivision.upperSize n (n * q - D.card) = q := by
    simp [FairDivision.upperSize, hFloor, hMod,
      Nat.ne_of_gt hRemPos, hqsub]
  rcases card_removeDummies_full_or_short B D q hFull hCap with hc | hc
  · right
    simpa only [hUpper] using hc
  · left
    omega

end FairDivision.Finite
