import FairDivision.BF.AugmentedExistence
import FairDivision.BF.PaddingArithmetic
import FairDivision.Finite.DummyRemovalFinal
import FairDivision.Finite.AllocationCast
import FairDivision.Finite.SmallInstances

/-!
# BF Section 3 final theorem, conditional on the topological obstruction

The finite argument now reaches the manuscript's exact balanced EF[1,1]
conclusion on the original item type. The original finite conversion is exposed also with its already-produced
common threshold and its actual dummy-cardinality guard. The prime-power
equivariant no-sphere-map theorem remains an explicit premise here. Its derivation from
auxiliary connectivity and Volovikov is developed separately.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision
open FairDivision.Topology
open FairDivision.Topology.Volovikov
open FairDivision.Finite

/-- For `m > p^rank`, the manuscript's stronger common-threshold conclusion follows from
the no-equivariant-sphere-map obstruction for the corrected auxiliary space.
The obstruction is deliberately an explicit hypothesis until its proof is
compiled. -/
theorem identicalPrimePower_commonThreshold_of_boundedDummy_noSphereMap
    (p rank m : ℕ) [NeZero p]
    (v : Finset (Fin m) → ℝ)
    (hmBig : p ^ rank < m)
    (hno :
      ∀ D : Finset (Fin ((p ^ rank) * upperSize (p ^ rank) m)),
        D.card ≤ p ^ rank →
        ∀ F : unlabeledLotterySpace (p ^ rank)
            ((p ^ rank) * upperSize (p ^ rank) m)
            (upperSize (p ^ rank) m - 1) 1 D →
              ReducedSphere (p ^ rank),
          Continuous F →
          (∀ (g : Fin rank → ZMod p)
            (x : unlabeledLotterySpace (p ^ rank)
              ((p ^ rank) * upperSize (p ^ rank) m)
              (upperSize (p ^ rank) m - 1) 1 D),
            F (auxiliaryRelabel (pTorusPositionPerm p rank g) x) =
              relabelReducedSphere (pTorusPositionPerm p rank g) (F x)) →
            False) :
    ∃ (A : Allocation (p ^ rank) m) (t : ℝ),
      IsBalanced A ∧ HasCommonThreshold v A t := by
  let n : ℕ := p ^ rank
  let q : ℕ := upperSize n m
  have hn : 0 < n := by
    dsimp [n]
    exact pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) rank
  have hPad := upperSize_padding n m hn
  have hEnough : m ≤ n * q := hPad.1
  have hDummyLt : n * q - m < n := hPad.2
  have hq : 2 ≤ q := upperSize_two_le_of_lt n m hn hmBig
  have hDCountLe : n * q - m ≤
      (Finset.univ : Finset (Fin (n * q))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨D, _, hDcard⟩ :=
    Finset.exists_subset_card_eq hDCountLe
  have hDlt : D.card < n := by
    rw [hDcard]
    exact hDummyLt
  have hRealCount : n * q - D.card = m := by
    rw [hDcard]
    exact Nat.sub_sub_self hEnough
  let vReal : Finset (Fin (n * q - D.card)) → ℝ :=
    castValuation hRealCount v
  let vAug : Finset (Fin (n * q)) → ℝ :=
    fun S => vReal (pullbackRealBundle D S)
  obtain ⟨A, t, hA⟩ :=
    exists_augmentedAllocation_of_noSphereMap
      p rank q D vAug hq hDlt.le (hno D hDlt.le)
  have hVal (S : Finset (Fin (n * q))) :
      vAug (S \ D) = vAug S := by
    simp only [vAug, pullbackRealBundle_sdiff_dummy]
  have hFun : (fun S : Finset (Fin (n * q)) => vAug (S \ D)) =
      vAug := by
    funext S
    exact hVal S
  have hFull : ∀ i : Fin n,
      (bundle A i).card = q ∧
      BracketsOneDeletion
        (fun S => vReal (pullbackRealBundle D S)) (bundle A i) t ∧
      (bundle A i ∩ D).card ≤ 1 := by
    rw [hFun] at hA
    exact hA
  obtain ⟨hBalanced, hThreshold⟩ :=
    projectedRealAllocation_balanced_commonThreshold
      A D vReal t hn (by omega) hDlt hFull
  let R : Allocation n (n * q - D.card) :=
    projectedRealAllocation A D
  have hBalanced' : IsBalanced (castAllocation hRealCount R) :=
    castAllocation_balanced hRealCount R hBalanced
  have hThreshold' : HasCommonThreshold v
      (castAllocation hRealCount R) t :=
    castAllocation_commonThreshold hRealCount v R t hThreshold
  exact ⟨castAllocation hRealCount R,t,hBalanced',hThreshold'⟩

/-- Legacy conditional interface, retained as a corollary of the same
finite conversion. The stronger helper only asks for the dummy cardinality
bound actually used by that conversion and retains its common threshold. -/
theorem identicalPrimePower_of_noSphereMap
    (p rank m : ℕ) [NeZero p]
    (v : Finset (Fin m) → ℝ)
    (hmBig : p ^ rank < m)
    (hno :
      ∀ D : Finset (Fin ((p ^ rank) * upperSize (p ^ rank) m)),
        ∀ F : unlabeledLotterySpace (p ^ rank)
            ((p ^ rank) * upperSize (p ^ rank) m)
            (upperSize (p ^ rank) m - 1) 1 D →
              ReducedSphere (p ^ rank),
          Continuous F →
          (∀ (g : Fin rank → ZMod p)
            (x : unlabeledLotterySpace (p ^ rank)
              ((p ^ rank) * upperSize (p ^ rank) m)
              (upperSize (p ^ rank) m - 1) 1 D),
            F (auxiliaryRelabel (pTorusPositionPerm p rank g) x) =
              relabelReducedSphere (pTorusPositionPerm p rank g) (F x)) →
            False) :
    ∃ A : Allocation (p ^ rank) m,
      IsBalanced A ∧ IsEF11 (fun _ => v) A := by
  obtain ⟨A,t,hBalanced,hThreshold⟩ :=
    identicalPrimePower_commonThreshold_of_boundedDummy_noSphereMap p rank m v hmBig
      (fun D _ => hno D)
  exact ⟨A,hBalanced,hasCommonThreshold_implies_ef11 v A t hThreshold⟩

/-- The complete Section 3 item-count split. The topological obstruction is
needed only in the `m > p^rank` branch; the small-item branch is entirely
finite. This remains conditional until the no-map theorem is proved. -/
theorem identicalPrimePowerAllM_of_noSphereMap
    (p rank m : ℕ) [NeZero p]
    (v : Finset (Fin m) → ℝ)
    (hno : p ^ rank < m →
      ∀ D : Finset (Fin ((p ^ rank) * upperSize (p ^ rank) m)),
        ∀ F : unlabeledLotterySpace (p ^ rank)
            ((p ^ rank) * upperSize (p ^ rank) m)
            (upperSize (p ^ rank) m - 1) 1 D →
              ReducedSphere (p ^ rank),
          Continuous F →
          (∀ (g : Fin rank → ZMod p)
            (x : unlabeledLotterySpace (p ^ rank)
              ((p ^ rank) * upperSize (p ^ rank) m)
              (upperSize (p ^ rank) m - 1) 1 D),
            F (auxiliaryRelabel (pTorusPositionPerm p rank g) x) =
              relabelReducedSphere (pTorusPositionPerm p rank g) (F x)) →
            False) :
    ∃ A : Allocation (p ^ rank) m,
      IsBalanced A ∧ IsEF11 (fun _ => v) A := by
  by_cases hm : m ≤ p ^ rank
  · have hn : 0 < p ^ rank :=
      pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) rank
    obtain ⟨A, t, hbal, hthreshold⟩ :=
      identical_small hn hm v
    exact ⟨A, hbal,
      hasCommonThreshold_implies_ef11 v A t hthreshold⟩
  · have hbig : p ^ rank < m := by omega
    exact identicalPrimePower_of_noSphereMap p rank m v hbig
      (hno hbig)


/-- The SAME small/large item-count split, retaining the threshold already
constructed by the finite proof. The topological interface is restricted
to the actual admissible padding stocks, rather than arbitrary dummy sets. -/
theorem identicalPrimePowerAllM_commonThreshold_of_boundedDummy_noSphereMap
    (p rank m : ℕ) [NeZero p]
    (v : Finset (Fin m) → ℝ)
    (hno : p ^ rank < m →
      ∀ D : Finset (Fin ((p ^ rank) * upperSize (p ^ rank) m)),
        D.card ≤ p ^ rank →
        ∀ F : unlabeledLotterySpace (p ^ rank)
            ((p ^ rank) * upperSize (p ^ rank) m)
            (upperSize (p ^ rank) m - 1) 1 D →
              ReducedSphere (p ^ rank),
          Continuous F →
          (∀ (g : Fin rank → ZMod p)
            (x : unlabeledLotterySpace (p ^ rank)
              ((p ^ rank) * upperSize (p ^ rank) m)
              (upperSize (p ^ rank) m - 1) 1 D),
            F (auxiliaryRelabel (pTorusPositionPerm p rank g) x) =
              relabelReducedSphere (pTorusPositionPerm p rank g) (F x)) →
            False) :
    ∃ (A : Allocation (p ^ rank) m) (t : ℝ),
      IsBalanced A ∧ HasCommonThreshold v A t := by
  by_cases hm : m ≤ p ^ rank
  · exact identical_small (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) rank) hm v
  · have hBig : p ^ rank < m := by omega
    exact identicalPrimePower_commonThreshold_of_boundedDummy_noSphereMap
      p rank m v hBig (hno hBig)

end FairDivision.BF
