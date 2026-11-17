import FairDivision.Topology.UnlabeledPositionFaces
import FairDivision.Topology.UnlabeledLottery

/-!
# Symmetric-group action on the BF auxiliary realization

A permutation of positions acts by reindexing each auxiliary vertex. The
induced simplex map preserves the realization and permutes expected scores.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Reindexing by the inverse permutation undoes reindexing by `σ`. -/
theorem relabelUnlabeledVertex_symm {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (p : UnlabeledDummyVertex k m r c D) :
    relabelUnlabeledVertex σ.symm (relabelUnlabeledVertex σ p) = p := by
  apply Subtype.ext
  funext i
  change p.1 (σ.symm (σ i)) = p.1 i
  simp

/-- Position relabeling is a permutation of auxiliary vertices. -/
def relabelUnlabeledEquiv {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k)) :
    UnlabeledDummyVertex k m r c D ≃
      UnlabeledDummyVertex k m r c D where
  toFun := relabelUnlabeledVertex σ
  invFun := relabelUnlabeledVertex σ.symm
  left_inv := relabelUnlabeledVertex_symm σ
  right_inv p := by
    simpa using relabelUnlabeledVertex_symm σ.symm p

/-- Pushing simplex weights along a position permutation only reindexes
coordinates. -/
theorem relabeledLottery_coordinate {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D))
    (p : UnlabeledDummyVertex k m r c D) :
    (stdSimplex.map (relabelUnlabeledVertex σ) lot).1
      (relabelUnlabeledVertex σ p) = lot.1 p := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ
    (relabelUnlabeledVertex σ) lot.1)
      (relabelUnlabeledVertex σ p) = lot.1 p
  rw [FunOnFinite.linearMap_apply_apply]
  simp only [Finset.sum_filter]
  have hinj : Function.Injective
      (relabelUnlabeledVertex (D := D) (r := r) (c := c) σ) :=
    (relabelUnlabeledEquiv (D := D) (r := r) (c := c) σ).injective
  simp [hinj.eq_iff]

/-- The positive support of a relabeled lottery is the relabeled support. -/
theorem relabeledLottery_support {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D)) :
    unlabeledLotterySupport
      (stdSimplex.map (relabelUnlabeledVertex σ) lot) =
      (unlabeledLotterySupport lot).image
        (relabelUnlabeledVertex σ) := by
  classical
  ext q
  constructor
  · intro hq
    let p := (relabelUnlabeledEquiv σ).symm q
    have hqp : relabelUnlabeledVertex σ p = q :=
      (relabelUnlabeledEquiv σ).apply_symm_apply q
    have hpos : 0 < lot.1 p := by
      rw [← hqp] at hq
      exact (relabeledLottery_coordinate σ lot p) ▸
        (Finset.mem_filter.mp hq).2
    exact Finset.mem_image.mpr
      ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩, hqp⟩
  · intro hq
    obtain ⟨p, hp, hqp⟩ := Finset.mem_image.mp hq
    rw [← hqp]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        (relabeledLottery_coordinate σ lot p) ▸
          (Finset.mem_filter.mp hp).2⟩

/-- Position relabeling maps the auxiliary realization to itself. -/
theorem relabeledLottery_mem {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D))
    (hlot : lot ∈ unlabeledLotterySpace k m r c D) :
    stdSimplex.map (relabelUnlabeledVertex σ) lot ∈
      unlabeledLotterySpace k m r c D := by
  change IsUnlabeledCompatibleFamily _
  rw [relabeledLottery_support]
  exact unlabeledCompatible_relabel σ _ hlot

/-- Relabeling positions permutes the continuous expected-value scores. -/
theorem relabeledLottery_score {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (v : Finset (Fin m) → ℝ)
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D))
    (i : Fin k) :
    unlabeledExpectedValue v
      (stdSimplex.map (relabelUnlabeledVertex σ) lot) (σ i) =
      unlabeledExpectedValue v lot i := by
  classical
  unfold unlabeledExpectedValue
  calc
    (∑ q : UnlabeledDummyVertex k m r c D,
      (stdSimplex.map (relabelUnlabeledVertex σ) lot).1 q *
        v (q.1 (σ i)).1) =
      ∑ p : UnlabeledDummyVertex k m r c D,
        (stdSimplex.map (relabelUnlabeledVertex σ) lot).1
          (relabelUnlabeledVertex σ p) *
          v ((relabelUnlabeledVertex σ p).1 (σ i)).1 := by
        exact (Equiv.sum_comp (relabelUnlabeledEquiv σ) _).symm
    _ = ∑ p : UnlabeledDummyVertex k m r c D,
          lot.1 p * v (p.1 i).1 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [relabeledLottery_coordinate]
      change lot.1 p * v (p.1 (σ.symm (σ i))).1 = _
      simp

end FairDivision.Topology
