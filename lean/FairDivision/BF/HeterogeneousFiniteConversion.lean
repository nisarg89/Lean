import FairDivision.BF.HeterogeneousRebalanceCompletion
import FairDivision.BF.HeterogeneousShorteningCompletion

/-!
# BF Section 5: finite conversion from selected bundles

This composes the manuscript's two finite phases. First it assigns every
unused real item to a short selected augmented bundle. Then it removes all
dummies and transfers one real item from a distinct certified full donor to
each deficient recipient. The result is a disjoint covering family of real
bundles with balanced sizes and all heterogeneous deletion brackets.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- The manuscript's heterogeneous finite conversion, stated on the real
stock before the harmless reindexing to `Fin m`. -/
theorem complete_hetero_real_family
    {n N r : ℕ} (U D : Finset (Fin N))
    (v : Fin n → Finset (Fin N) → ℝ) (τ : Fin n → ℝ)
    (B : Fin n → Finset (Fin N))
    (hr : 1 ≤ r)
    (hDU : D ⊆ U)
    (hTotal : U.card = n * (r + 1))
    (hDlt : D.card < n)
    (hIgnore : ∀ j : Fin n, ∀ S : Finset (Fin N),
      v j (S \ D) = v j S)
    (hB : HeteroPartialState r U D v τ B)
    (hShorten : HeteroShortenable r D v τ B) :
    ∃ A : Fin n → Finset (Fin N),
      HeteroRealState r (U \ D) v τ A ∧
      (∀ i : Fin n, (A i).card = r ∨ (A i).card = r + 1) ∧
      (∀ i : Fin n, HeteroBrackets v τ i (A i)) := by
  obtain ⟨C, hC, hCShorten, hCovered⟩ :=
    complete_hetero_real_items_shortenable U D v τ hTotal B hB hShorten
  have hRealTotal : (U \ D).card + D.card = n * (r + 1) := by
    calc
      (U \ D).card + D.card = U.card :=
        Finset.card_sdiff_add_card_eq_card hDU
      _ = n * (r + 1) := hTotal
  have hRealState : HeteroRealState r (U \ D) v τ
      (fun i => C i \ D) :=
    hC.toRealState hCShorten hIgnore hCovered
  obtain ⟨A, hA, hSizes⟩ :=
    complete_hetero_real_rebalancing (fun i => C i \ D)
      hr hRealTotal hDlt hRealState
  exact ⟨A, hA, hSizes, hA.balanced_brackets hr hSizes⟩

end FairDivision.BF
