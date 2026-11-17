import FairDivision.Topology.UnlabeledLottery

/-!
# Lifting an unlabeled auxiliary point to a compatible labeled lottery

A support face supplies compatible labeled representatives. Push the simplex
weights forward along that choice. Vertices outside the support have zero
weight, so their arbitrary representatives do not affect compatibility.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Every point of the corrected auxiliary realization induces an ordinary
compatible lottery on labeled partial allocations. -/
theorem exists_compatible_lift {k m r c : ℕ}
    {D : Finset (Fin m)}
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D))
    (hlot : lot ∈ unlabeledLotterySpace k m r c D) :
    ∃ μ : stdSimplex ℝ (PartialVertex k D r c),
      μ ∈ compatibleLotterySpace k m r c D ∧
      ∀ (v : Finset (Fin m) → ℝ) (i : Fin k),
        (∑ X : PartialVertex k D r c,
          μ.1 X * v (partialBundle X.1 i \ D)) =
          unlabeledExpectedValue v lot i := by
  classical
  let S := unlabeledLotterySupport lot
  obtain ⟨T, hT, hImage⟩ : IsUnlabeledCompatibleFamily S := hlot
  have hChoice (p : UnlabeledDummyVertex k m r c D)
      (hp : p ∈ S) :
      ∃ X ∈ T, toUnlabeledDummyVertex X = p := by
    have hpImage : p ∈ T.image toUnlabeledDummyVertex := by
      rw [hImage]
      exact hp
    exact Finset.mem_image.mp hpImage
  let rep (p : UnlabeledDummyVertex k m r c D) :
      PartialVertex k D r c :=
    if hp : p ∈ S then Classical.choose (hChoice p hp)
    else Classical.choose p.2
  have hRepT (p : UnlabeledDummyVertex k m r c D)
      (hp : p ∈ S) : rep p ∈ T := by
    simp only [rep, dif_pos hp]
    exact (Classical.choose_spec (hChoice p hp)).1
  let μ : stdSimplex ℝ (PartialVertex k D r c) :=
    stdSimplex.map rep lot
  have hSupportSub : lotterySupport μ ⊆ T := by
    intro X hX
    have hpos : 0 < μ.1 X := (Finset.mem_filter.mp hX).2
    by_contra hnot
    have hAllZero (p : UnlabeledDummyVertex k m r c D)
        (hrep : rep p = X) : lot.1 p = 0 := by
      by_cases hp : p ∈ S
      · exact False.elim (hnot (hrep ▸ hRepT p hp))
      · have hnotpos : ¬ 0 < lot.1 p := by
          intro hpositive
          exact hp (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hpositive⟩)
        exact le_antisymm (le_of_not_gt hnotpos) (lot.2.1 p)
    have hzero : μ.1 X = 0 := by
      change FunOnFinite.linearMap ℝ ℝ rep lot.1 X = 0
      rw [FunOnFinite.linearMap_apply_apply]
      apply Finset.sum_eq_zero
      intro p hp
      exact hAllZero p (Finset.mem_filter.mp hp).2
    exact (ne_of_gt hpos) hzero
  have hRepProfile (p : UnlabeledDummyVertex k m r c D)
      (hp : p ∈ S) : toUnlabeledDummyVertex (rep p) = p := by
    simp only [rep, dif_pos hp]
    exact (Classical.choose_spec (hChoice p hp)).2
  have hRepReal (p : UnlabeledDummyVertex k m r c D)
      (hp : p ∈ S) (i : Fin k) :
      partialBundle (rep p).1 i \ D = (p.1 i).1 := by
    exact congrArg (fun q : UnlabeledDummyVertex k m r c D =>
      (q.1 i).1) (hRepProfile p hp)
  have hScore (v : Finset (Fin m) → ℝ) (i : Fin k) :
      (∑ X : PartialVertex k D r c,
        μ.1 X * v (partialBundle X.1 i \ D)) =
        unlabeledExpectedValue v lot i := by
    have hPush :
        (∑ X : PartialVertex k D r c,
          μ.1 X * v (partialBundle X.1 i \ D)) =
          ∑ p : UnlabeledDummyVertex k m r c D,
            lot.1 p * v (partialBundle (rep p).1 i \ D) := by
      change (∑ X : PartialVertex k D r c,
        (FunOnFinite.linearMap ℝ ℝ rep lot.1) X *
          v (partialBundle X.1 i \ D)) = _
      simp_rw [FunOnFinite.linearMap_apply_apply]
      calc
        (∑ X : PartialVertex k D r c,
          (∑ p with rep p = X, lot.1 p) *
            v (partialBundle X.1 i \ D)) =
            ∑ X : PartialVertex k D r c,
              ∑ p with rep p = X,
                lot.1 p * v (partialBundle (rep p).1 i \ D) := by
          apply Finset.sum_congr rfl
          intro X _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = ∑ p : UnlabeledDummyVertex k m r c D,
              lot.1 p * v (partialBundle (rep p).1 i \ D) := by
          exact Finset.sum_fiberwise Finset.univ rep _
    calc
      (∑ X : PartialVertex k D r c,
        μ.1 X * v (partialBundle X.1 i \ D)) =
          ∑ p : UnlabeledDummyVertex k m r c D,
            lot.1 p * v (partialBundle (rep p).1 i \ D) := hPush
      _ = ∑ p : UnlabeledDummyVertex k m r c D,
            lot.1 p * v (p.1 i).1 := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : p ∈ S
        · rw [hRepReal p hp i]
        · have hnotpos : ¬ 0 < lot.1 p := by
            intro hpositive
            exact hp (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hpositive⟩)
          have hzero : lot.1 p = 0 :=
            le_antisymm (le_of_not_gt hnotpos) (lot.2.1 p)
          simp [hzero]
      _ = unlabeledExpectedValue v lot i := rfl
  exact ⟨μ, compatible_mono hSupportSub hT, hScore⟩

end FairDivision.Topology
