import FairDivision.BF.SwapDefinitions

/-!
# The manuscript's complementary-exchange proof for q ≤ 2t

For q≤t, exchange both complete bundles. Otherwise exchange floor(q/2)
items each way. The complementary exchange uses ceil(q/2) items and
produces exactly the same two bundles with their owners reversed. One
of these comparisons is weakly preferred by the envying agent. The
empty-bundle case has no envy. No monotonicity or additive assumption is
used, and the exact manuscript proof is retained.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- In the paper's nontrivial range t<q≤2t, both the chosen half and its
complement are genuine swaps of at most t items. This includes equality
q=2t; no strict q<2t hypothesis is used. -/
theorem swap_threshold_half_sizes {t q : ℕ} (ht : 1≤t)
    (hLarge : t<q) (hBound : q≤2*t) :
    1≤q/2 ∧ q/2≤t ∧ 1≤q-q/2 ∧ q-q/2≤t := by
  omega

/-- At the critical endpoint both complementary exchanges have exactly t
items. This is the finite integer identity behind the non-strict threshold.
-/
theorem swap_threshold_critical_sizes (t : ℕ) :
    (2*t)/2=t ∧ 2*t-(2*t)/2=t := by
  omega

/-- The literal pairwise complementary-swap argument, independent of
any allocation encoding or any relation between other agents' bundles. -/
theorem swap_threshold_pair {m t q : ℕ} (ht : 1≤t) (hq : q≤2*t)
    (v : Finset (Fin m)→ℝ) (S T : Finset (Fin m))
    (hS : S.card=q) (hT : T.card=q) (hEnvy : v S<v T) :
    ∃X Y : Finset (Fin m),X⊆S ∧Y⊆T ∧1≤X.card ∧X.card=Y.card ∧X.card≤t ∧
      v ((T\Y)∪X)≤v ((S\X)∪Y) := by
  classical
  have hqPositive : 0<q := by
    by_contra h
    have hqZero : q=0:=by omega
    have hSEmpty : S=∅:=Finset.card_eq_zero.mp (hS.trans hqZero)
    have hTEmpty : T=∅:=Finset.card_eq_zero.mp (hT.trans hqZero)
    exact (lt_irrefl (v ∅)) (by simpa only [hSEmpty,hTEmpty] using hEnvy)
  by_cases hSmall : q≤t
  · refine ⟨S,T,Finset.Subset.rfl,Finset.Subset.rfl,by omega,
      hS.trans hT.symm,by omega,?_⟩
    simpa only [Finset.sdiff_self,Finset.empty_union] using hEnvy.le
  · obtain ⟨hHalfPositive,hHalfLe,hComplementPositive,hComplementLe⟩ :=
      swap_threshold_half_sizes ht (lt_of_not_ge hSmall) hq
    obtain ⟨X,hXS,hX⟩:=Finset.exists_subset_card_eq
      (show q/2≤S.card by rw [hS];exact Nat.div_le_self q 2)
    obtain ⟨Y,hYT,hY⟩:=Finset.exists_subset_card_eq
      (show q/2≤T.card by rw [hT];exact Nat.div_le_self q 2)
    rcases le_total (v ((S\X)∪Y)) (v ((T\Y)∪X)) with hFirst|hSecond
    · refine ⟨S\X,T\Y,Finset.sdiff_subset,Finset.sdiff_subset,?_,?_,?_,?_⟩
      · rw [Finset.card_sdiff_of_subset hXS,hS,hX]
        exact hComplementPositive
      · rw [Finset.card_sdiff_of_subset hXS,Finset.card_sdiff_of_subset hYT,
          hS,hT,hX,hY]
      · rw [Finset.card_sdiff_of_subset hXS,hS,hX]
        exact hComplementLe
      · rw [Finset.sdiff_sdiff_eq_self hYT,Finset.sdiff_sdiff_eq_self hXS]
        simpa only [Finset.union_comm] using hFirst
    · exact ⟨X,Y,hXS,hYT,by omega,by omega,by omega,hSecond⟩

/-- Positive swap result: EVERY allocation into q-item bundles
is t-swap envy-free when q≤2t, for arbitrary heterogeneous valuations. -/
theorem every_equal_bundle_allocation_is_tSwapEF
    {n m t q : ℕ} (ht : 1≤t) (hq : q≤2*t)
    (v : Fin n→Finset (Fin m)→ℝ) (A : Allocation n m)
    (hSize : HasEqualBundleSize A q) : IsTSwapEF t v A := by
  intro i j hEnvy
  exact swap_threshold_pair ht hq (v i) (bundle A i) (bundle A j)
    (hSize i) (hSize j) hEnvy

/-- The q=1 boundary uses the manuscript's whole-bundle exchange. It never
enters the half-bundle branch, where floor(q/2) would be zero. -/
theorem every_singleton_allocation_is_tSwapEF
    {n m t : ℕ} (ht : 1≤t)
    (v : Fin n→Finset (Fin m)→ℝ) (A : Allocation n m)
    (hSize : HasEqualBundleSize A 1) : IsTSwapEF t v A :=
  every_equal_bundle_allocation_is_tSwapEF ht (by omega) v A hSize

end FairDivision.BF
