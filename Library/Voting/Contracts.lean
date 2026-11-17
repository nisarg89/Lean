import Voting.Basic

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable

namespace MetricDistortion.Contracts

namespace Shared_CompactConvexMinimax

def Statement : Prop :=
∀ m, 0 < m → ∀ f : (Fin m → ℝ) → (Fin m → ℝ) → ℝ,
  ContinuousOn (Function.uncurry f) ((simplex m) ×ˢ (simplex m)) →
  (∀ p ∈ simplex m, ConcaveOn ℝ (simplex m) (fun a => f a p)) →
  (∀ a ∈ simplex m, ConvexOn ℝ (simplex m) (fun p => f a p)) →
  ∃ a ∈ simplex m, ∃ p ∈ simplex m,
    (∀ a' ∈ simplex m, f a' p ≤ f a p) ∧ (∀ p' ∈ simplex m, f a p ≤ f a p')

end Shared_CompactConvexMinimax



namespace Model_Lotteries

def Statement : Prop :=
∀ m (P : Lottery m), (∀ c, P.val c ∈ Icc (0 : ℝ) 1) ∧
  (∀ H, mass P H ∈ Icc (0 : ℝ) 1) ∧ ∑ c, P.val c = 1

end Model_Lotteries



namespace Comparison_PowerIntegral

def Statement : Prop :=
∀ k : ℕ, ∫ s in (0 : ℝ)..1, s^k = 1/(k+1 : ℕ)

end Comparison_PowerIntegral



namespace Comparison_LabeledTie

def Statement : Prop :=
∀ r s : ℕ, 0 < r+s → labelWin r s = (r : ℝ)/(r+s)

structure Needs : Prop where

  child_0 : Comparison_PowerIntegral.Statement

end Comparison_LabeledTie



namespace Model_Profiles

def Statement : Prop :=
∀ n m (σ : Profile n m) v a b,
  (¬ prefers (σ v) a a) ∧ (prefers (σ v) a b → ¬ prefers (σ v) b a) ∧
  (a ≠ b → prefers (σ v) a b ∨ prefers (σ v) b a)

end Model_Profiles



namespace Model_RankIntervals

def Statement : Prop :=
∀ m (r : Ranking m) (P : Lottery m),
  (∀ c, volume (block r P c) = ENNReal.ofReal (P.val c)) ∧
  (∀ a b, a ≠ b → Disjoint (block r P a) (block r P b)) ∧
  (∀ H, volume (region r P H) = ENNReal.ofReal (mass P H)) ∧
  (⋃ c, block r P c) = Ico (0 : ℝ) 1

structure Needs : Prop where

  child_0 : Model_Profiles.Statement

  child_1 : Model_Lotteries.Statement

end Model_RankIntervals



namespace Analysis_MonotoneSetIntegral

def Statement : Prop :=
∀ f : ℝ → ℝ, ContinuousOn f (Icc (0 : ℝ) 1) →
  MonotoneOn f (Icc (0 : ℝ) 1) → ∀ a p A : ℝ, 0 ≤ a → a ≤ p → p ≤ A → A ≤ 1 →
  ∀ S : Set ℝ, MeasurableSet S → S ⊆ Icc 0 A → volume S = ENNReal.ofReal p →
  (∀ᵐ u ∂volume, u ∈ Icc 0 a → u ∈ S) →
  (∫ u in S, f u) ≤ (∫ u in (0 : ℝ)..a, f u)+(∫ u in (a+A-p)..A, f u)

end Analysis_MonotoneSetIntegral



end MetricDistortion.Contracts
