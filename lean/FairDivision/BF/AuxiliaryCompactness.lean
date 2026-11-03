import FairDivision.Topology.UnlabeledLottery
import FairDivision.Topology.NerveConnectivity.ClosedRealization

/-!
# Compactness of BF's corrected auxiliary complex

The unlabeled-dummy lottery space is the finite simplicial realization of
its compatible-profile complex. The generic finite-realization theorem gives
compactness for the limiting argument in Section 5.
-/

set_option autoImplicit false

namespace FairDivision.BF

open scoped BigOperators Classical

open FairDivision.Topology

/-- The corrected unlabeled-dummy auxiliary space is compact. -/
theorem unlabeledLotterySpace_isCompact
    {k m r c : ℕ} (D : Finset (Fin m)) :
    IsCompact (unlabeledLotterySpace k m r c D) := by
  have heq : unlabeledLotterySpace k m r c D =
      NerveConnectivity.simplicialRealization
        (unlabeledDummyComplex k m r c D).toPreAbstractSimplicialComplex := by
    ext x
    exact unlabeledLottery_iff_support_face x
  rw [heq]
  exact NerveConnectivity.simplicialRealization_isCompact _

end FairDivision.BF
