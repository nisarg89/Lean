import FairDivision.BF.HeterogeneousDummyProjection

/-!
# BF Section 5: one donor-to-recipient rebalancing step

After dummy removal, a real full donor supplies a certified short subbundle.
Its one removed real item fills a deficient recipient; the recipient's
former whole bundle supplies every comparison after deleting that item.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- A certified full donor has exactly one real item outside its certified
shortening. Giving that item to a disjoint deficient recipient preserves the
manuscript's heterogeneous brackets and makes both bundles size `r`. -/
theorem hetero_rebalance_pair
    {n m r : ℕ} {v : Fin n → Finset (Fin m) → ℝ}
    {τ : Fin n → ℝ} {donor recipient : Fin n}
    {F C S : Finset (Fin m)}
    (hr : 1 ≤ r)
    (hFull : F.card = r + 1)
    (hShort : C ⊆ F)
    (hShortCard : C.card = r)
    (hDonor : HeteroBrackets v τ donor C)
    (hSmall : S.card = r - 1)
    (hLower : ∀ j : Fin n, v j S ≤ τ j)
    (hUpper : τ recipient ≤ v recipient S)
    (hDisjoint : Disjoint F S) :
    ∃ z : Fin m,
      z ∈ F ∧ z ∉ S ∧ F \ {z} = C ∧
      C.card = r ∧ (insert z S).card = r ∧
      HeteroBrackets v τ donor C ∧
      HeteroBrackets v τ recipient (insert z S) := by
  classical
  obtain ⟨z, hzC, hInsert⟩ : ∃ z ∉ C, insert z C = F :=
    Finset.exists_eq_insert_iff.mpr ⟨hShort, by omega⟩
  have hzF : z ∈ F := by
    rw [← hInsert]
    exact Finset.mem_insert_self z C
  have hzS : z ∉ S := by
    exact (Finset.disjoint_left.mp hDisjoint) hzF
  have hRemove : F \ {z} = C := by
    rw [← hInsert, Finset.sdiff_singleton_eq_erase,
      Finset.erase_insert hzC]
  refine ⟨z, hzF, hzS, hRemove, hShortCard, ?_, hDonor, ?_⟩
  · simp [hzS, hSmall]
    omega
  · exact HeteroBrackets.insert_of_short hLower hUpper z hzS

end FairDivision.BF
