import FairDivision.Finite.BundleExchangeChain
import FairDivision.Finite.FirstThresholdCrossing

/-!
# Finding a one-item exchange across a value threshold

First construct the entire manuscript exchange sequence, independently of
its values, using the same chain source as the heterogeneous one-skeleton.
Then choose its first index at or above the threshold. The immediately
preceding step is the required crossing; no threshold-stopping construction
is used to produce the path. No monotonicity or normalization is assumed.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- Within a common pool, two equal-size bundles whose values bracket `t`
give a one-item exchange that crosses `t`. -/
theorem exists_exchange_bracket {α : Type*} [DecidableEq α]
    (U B C : Finset α) (r : ℕ) (v : Finset α → ℝ) (t : ℝ)
    (hBU : B ⊆ U) (hCU : C ⊆ U)
    (hBcard : B.card = r) (hCcard : C.card = r)
    (hLow : v B < t) (hHigh : t ≤ v C) :
    ∃ F : Finset α, ∃ a b : α,
      F ⊆ U ∧ F.card = r ∧ a ∈ F ∧ b ∈ U \ F ∧
      v F < t ∧ t ≤ v (insert b (F.erase a)) := by
  classical
  obtain ⟨chain,_hLength⟩ :=
    exists_bundle_exchange_chain U B C (q := r + 1) rfl
      hBcard hCcard hBU hCU
  have hFirst : v (chain.bundle 0) < t := by
    rw [chain.first]
    exact hLow
  have hLast : t ≤ v (chain.bundle (Fin.last chain.length)) := by
    rw [chain.last]
    exact hHigh
  obtain ⟨j,hjLow,hjHigh⟩ :=
    exists_first_threshold_crossing (fun k => v (chain.bundle k)) t hFirst hLast
  obtain ⟨a,ha,b,hb,hStep⟩ := chain.step rfl j
  refine ⟨chain.bundle j.castSucc,a,b,chain.in_stock j.castSucc,
    chain.card j.castSucc,ha,hb,hjLow,?_⟩
  rw [← hStep]
  exact hjHigh

end FairDivision.Finite
