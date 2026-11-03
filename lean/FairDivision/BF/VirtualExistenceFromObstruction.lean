import FairDivision.BF.VirtualWitnessAllDummyCounts
import FairDivision.BF.VirtualTopologicalEqualization

/-!
# BF Section 5: abstract prime-power existence composition

This theorem joins the manuscript's virtual-value, topological equalization,
compactness, and finite conversion steps. Its two remaining external premises
are exactly the virtual-valuation construction and the no-equivariant-sphere-
map obstruction on the corrected unlabeled auxiliary complex.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology
open FairDivision.Topology.Volovikov

/-- Given the virtual valuation and topological obstruction, the BF
prime-power allocation theorem follows for any number of actual dummies. -/
theorem exists_balanced_ef11_of_virtualSpec_and_noSphereMap
    (p rank N q : ℕ) [NeZero p]
    (D : Finset (Fin N))
    (v : Fin (p ^ rank) → Finset (Fin (N - D.card)) → ℝ)
    (spec : VirtualValuationSpec (q := q) v)
    (hq : 2 ≤ q) (hN : N = (p ^ rank) * q)
    (hDlt : D.card < p ^ rank)
    (hnoSphereMap :
      ∀ F : unlabeledLotterySpace (p ^ rank) N (q - 1) 1 D →
          ReducedSphere (p ^ rank),
        Continuous F →
        (∀ (g : Fin rank → ZMod p)
          (x : unlabeledLotterySpace (p ^ rank) N (q - 1) 1 D),
          F (auxiliaryRelabel (pTorusPositionPerm p rank g) x) =
            relabelReducedSphere (pTorusPositionPerm p rank g) (F x)) → False) :
    ∃ A : FairDivision.Allocation (p ^ rank) (N - D.card),
      FairDivision.IsBalanced A ∧ FairDivision.IsEF11 v A := by
  have hn : 0 < p ^ rank :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) rank
  have hEqual : ∀ ε : ℝ, 0 < ε →
      ∃ x : unlabeledLotterySpace (p ^ rank) N (q - 1) 1 D,
        ∀ s t : Fin (p ^ rank),
          positionScore hn (fun i z => spec.score z i) ε
            (fun a => unlabeledReducedMarginal a x) s =
          positionScore hn (fun i z => spec.score z i) ε
            (fun a => unlabeledReducedMarginal a x) t := by
    intro ε hε
    exact exists_equalized_virtualPreferenceScore_of_noSphereMap
      p rank N q D v spec ε hε hnoSphereMap
  exact exists_balanced_ef11_of_equalized_virtualScores
    hn D v spec hEqual hq hN hDlt

end FairDivision.BF
