import FairDivision.Topology.FiniteSimplexSupport
import FairDivision.Topology.UnlabeledDummyFaceCriterion

/-!
# Probability-simplex realization of the unlabeled-dummy complex

A point is a probability vector on auxiliary vertices whose positive support
is a face.  This is the realization on which the BF score map is defined.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Positive support of a probability vector on unlabeled-dummy vertices. -/
noncomputable def unlabeledLotterySupport {k m r c : ℕ}
    {D : Finset (Fin m)}
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D)) :
    Finset (UnlabeledDummyVertex k m r c D) :=
  finiteSimplexSupport lot

/-- Geometric realization of the corrected auxiliary complex in its finite
probability simplex. -/
def unlabeledLotterySpace (k m r c : ℕ) (D : Finset (Fin m)) :
    Set (stdSimplex ℝ (UnlabeledDummyVertex k m r c D)) :=
  {lot | IsUnlabeledCompatibleFamily (unlabeledLotterySupport lot)}

/-- Every probability vector has a nonempty positive support. -/
theorem unlabeledLotterySupport_nonempty {k m r c : ℕ}
    {D : Finset (Fin m)}
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D)) :
    (unlabeledLotterySupport lot).Nonempty := by
  exact finiteSimplexSupport_nonempty lot

/-- Realization membership is equivalent to positive support being a face. -/
theorem unlabeledLottery_iff_support_face {k m r c : ℕ}
    {D : Finset (Fin m)}
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D)) :
    lot ∈ unlabeledLotterySpace k m r c D ↔
      unlabeledLotterySupport lot ∈ unlabeledDummyComplex k m r c D := by
  change IsUnlabeledCompatibleFamily (unlabeledLotterySupport lot) ↔
    (unlabeledLotterySupport lot).Nonempty ∧
      IsUnlabeledCompatibleFamily (unlabeledLotterySupport lot)
  exact ⟨fun h => ⟨unlabeledLotterySupport_nonempty lot, h⟩,
    fun h => h.2⟩

/-- Expected value at one position, evaluated on its real bundle. Dummy
labels do not enter this expression. -/
noncomputable def unlabeledExpectedValue {k m r c : ℕ} {D : Finset (Fin m)}
    (v : Finset (Fin m) → ℝ)
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D))
    (i : Fin k) : ℝ :=
  ∑ p : UnlabeledDummyVertex k m r c D,
    lot.1 p * v (p.1 i).1

/-- Each position's score is continuous on the entire probability simplex,
and hence on the auxiliary realization. -/
theorem unlabeledExpectedValue_continuous {k m r c : ℕ}
    {D : Finset (Fin m)}
    (v : Finset (Fin m) → ℝ) (i : Fin k) :
    Continuous (fun lot : stdSimplex ℝ
      (UnlabeledDummyVertex k m r c D) =>
      unlabeledExpectedValue v lot i) := by
  unfold unlabeledExpectedValue
  apply continuous_finset_sum
  intro p _
  exact (((continuous_apply p).comp continuous_subtype_val).mul
    continuous_const)

end FairDivision.Topology
