import FairDivision.BF.VirtualDummyTransport
import FairDivision.Topology.UnlabeledDummyFaces

/-!
# Compatible position pools for reduced virtual marginals

A corrected unlabeled auxiliary point has labeled representatives with
pairwise disjoint pools and at most one actual dummy per pool. For each
position, choose that dummy if the marginal support uses the placeholder.
The translated support union then lies in the same actual pool, which is the
locality premise needed by the virtual-valuation owner witnesses.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology
open FairDivision.Finite

/-- Select labeled representatives for a compatible unlabeled point and
choose one actual dummy label per position. Every item in the reindexed
marginal stock maps into its position's labeled pool. -/
theorem exists_compatible_pools_for_reducedMarginals
    {n N r : ℕ} {D : Finset (Fin N)}
    (hD : D.Nonempty)
    (x : unlabeledLotterySpace n N r 1 D) :
    ∃ T : Finset (PartialVertex n D r 1),
      IsCompatibleFamily T ∧
      T.image toUnlabeledDummyVertex =
        unlabeledLotterySupport x.1 ∧
      ∃ dummy : Fin n → Fin N,
        (∀ i, dummy i ∈ D) ∧
        ∀ i, (finMarginalStock (unlabeledReducedMarginal i x)).image
          (actualMarginalItem D (dummy i)) ⊆ pool T i := by
  classical
  have hx : IsUnlabeledCompatibleFamily
      (unlabeledLotterySupport x.1) := x.2
  obtain ⟨T, hT, hImage⟩ := hx
  let fallback : Fin N := Classical.choose hD
  have hFallback : fallback ∈ D := Classical.choose_spec hD
  let dummy (i : Fin n) : Fin N :=
    if h : (pool T i ∩ D).Nonempty then Classical.choose h
    else fallback
  have hDummyD (i : Fin n) : dummy i ∈ D := by
    by_cases h : (pool T i ∩ D).Nonempty
    · have hChosen : Classical.choose h ∈ pool T i ∩ D :=
        Classical.choose_spec h
      simpa only [dummy, dif_pos h] using (Finset.mem_inter.mp hChosen).2
    · simpa only [dummy, dif_neg h] using hFallback
  have hDummyPool (i : Fin n)
      (h : (pool T i ∩ D).Nonempty) : dummy i ∈ pool T i := by
    have hChosen : Classical.choose h ∈ pool T i ∩ D :=
      Classical.choose_spec h
    simpa only [dummy, dif_pos h] using (Finset.mem_inter.mp hChosen).1
  refine ⟨T, hT, hImage, dummy, hDummyD, ?_⟩
  intro i
  apply actualMarginalItem_image_subset D (dummy i)
    (finMarginalStock (unlabeledReducedMarginal i x)) (pool T i)
  · intro hZero
    obtain ⟨p, hp, hZeroP⟩ :=
      exists_source_of_reducedMarginalStock_mem x i 0 hZero
    have hCount : (p.1 i).2 ≠ 0 := by
      intro h0
      have hImpossible :
          (0 : Fin (N - D.card + 1)) ∉
            (reducedMarginalVertex p i).1 := by
        simp [reducedMarginalVertex, reducedMarginalBundle, h0]
      exact hImpossible hZeroP
    have hpImage : p ∈ T.image toUnlabeledDummyVertex := by
      rw [hImage]
      exact hp
    obtain ⟨X, hXT, hXp⟩ := Finset.mem_image.mp hpImage
    have hCountX : (partialBundle X.1 i ∩ D).card = (p.1 i).2 := by
      have h := congrArg
        (fun z : UnlabeledDummyVertex n N r 1 D => (z.1 i).2) hXp
      simpa [toUnlabeledDummyVertex, dummyProfileOf] using h
    have hPositive : 0 < (partialBundle X.1 i ∩ D).card := by
      rw [hCountX]
      omega
    obtain ⟨d, hd⟩ := Finset.card_pos.mp hPositive
    have hdPool : d ∈ pool T i :=
      partialBundle_subset_pool hXT i (Finset.mem_inter.mp hd).1
    have hPoolDummy : (pool T i ∩ D).Nonempty :=
      ⟨d, Finset.mem_inter.mpr ⟨hdPool, (Finset.mem_inter.mp hd).2⟩⟩
    exact hDummyPool i hPoolDummy
  · intro g hSucc
    obtain ⟨p, hp, hSuccP⟩ :=
      exists_source_of_reducedMarginalStock_mem x i g.succ hSucc
    have hgReal : g ∈ pullbackRealBundle D (p.1 i).1 := by
      rw [← marginalRealPart_reducedVertex p i]
      simpa [marginalRealPart] using hSuccP
    have hpImage : p ∈ T.image toUnlabeledDummyVertex := by
      rw [hImage]
      exact hp
    obtain ⟨X, hXT, hXp⟩ := Finset.mem_image.mp hpImage
    rw [← hXp] at hgReal
    change g ∈ pullbackRealBundle D (partialBundle X.1 i \ D) at hgReal
    have hActual : (realItemEquiv D g).val ∈ partialBundle X.1 i := by
      have hgSDiff : (realItemEquiv D g).val ∈
          partialBundle X.1 i \ D := by
        simpa [pullbackRealBundle] using hgReal
      exact (Finset.mem_sdiff.mp hgSDiff).1
    exact partialBundle_subset_pool hXT i hActual

end FairDivision.BF
