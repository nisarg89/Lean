import FairDivision.BF.IdenticalExistence
import Mathlib.Data.Int.Interval

/-!
# Equal integer parameters on almost all vertices

This is the manuscript's exact-deletion proof. Keep k*floor(N/k)
vertices, obtain equal-size parts with one common exact-deletion interval,
round the common threshold up to an integer, and delete a vertex attaining
that integer from each part. The unit deletion hypothesis makes every
part's possible deletion values two consecutive integers.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open FairDivision FairDivision.BF

/-- Deleting one present vertex decreases the integer parameter by zero or
one. Applied to P(S)=P(G[S]), this is precisely the manuscript hypothesis. -/
def UnitDeletionParameter {N : ℕ} (P : Finset (Fin N) → ℤ) : Prop :=
  ∀ S : Finset (Fin N), ∀ x ∈ S,
    0 ≤ P S - P (S.erase x) ∧ P S - P (S.erase x) ≤ 1

/-- The integer ceil of a common exact-deletion threshold is attained:
there is no skipped integer between two values in {P(B)-1,P(B)}. -/
theorem exact_deletion_attains_ceil {N : ℕ} {P : Finset (Fin N) → ℤ}
    (hP : UnitDeletionParameter P) {B : Finset (Fin N)} {t : ℝ}
    (hBracket : BracketsOneDeletion (fun S => (P S : ℝ)) B t) :
    ∃ x ∈ B, P (B.erase x) = Int.ceil t := by
  obtain ⟨⟨x, hx, hLow⟩, ⟨y, hy, hHigh⟩⟩ := hBracket
  have hLowInt : P (B.erase x) ≤ Int.ceil t := by
    have hReal := hLow.trans (Int.le_ceil t)
    change (P (B.erase x) : ℝ) ≤ (Int.ceil t : ℝ) at hReal
    exact_mod_cast hReal
  have hHighInt : Int.ceil t ≤ P (B.erase y) := Int.ceil_le.mpr hHigh
  have hxStep := hP B x hx
  have hyStep := hP B y hy
  by_cases hxValue : P (B.erase x) = Int.ceil t
  · exact ⟨x, hx, hxValue⟩
  · exact ⟨y, hy, by omega⟩

/-- With no dummies the augmented real-part operation is the identity. -/
@[simp] theorem realPart_no_dummies {M : ℕ} (S : Finset (Fin (M + 0))) :
    Recording.realPart S = S := by
  ext x
  simp [Recording.realPart, Recording.realEmbedding, Fin.castAddEmb, Fin.castLEEmb]

/-- The exact-deletion consequence of the root theorem with d=0. Every
part has q vertices. The recorder's one-agent base also gives its immediate
one-part case. -/
theorem exists_uniform_exact_deletion_threshold (k q : ℕ)
    (hk : 0 < k) (hq : 2 ≤ q) (v : Finset (Fin (k * q)) → ℝ) :
    ∃ (A : Allocation k (k * q)) (t : ℝ),
      ∀ i : Fin k, (bundle A i).card = q ∧ BracketsOneDeletion v (bundle A i) t := by
  have hItems : 2 ≤ k * q := by
    have hkOne : 1 ≤ k := by omega
    have hMul : 1 * q ≤ k * q := Nat.mul_le_mul_right q hkOne
    exact hq.trans (by simpa only [one_mul] using hMul)
  obtain ⟨A, t, hA⟩ := identical_exists_augmented_commonThreshold
    k (k * q) q 0 hk hq hItems hk (by simp) v
  refine ⟨A, t, ?_⟩
  intro i
  exact ⟨(hA i).1, by simpa only [realPart_no_dummies] using (hA i).2.1⟩

/-- Keeping the first k*q vertices, then deleting one vertex from each
common-threshold part, gives k disjoint (q-1)-sets with one integer value. -/
theorem equal_parameter_sets_on_multiple {N k q : ℕ}
    (hk : 0 < k) (hq : 2 ≤ q) (hKeep : k * q ≤ N)
    (P : Finset (Fin N) → ℤ) (hP : UnitDeletionParameter P) :
    ∃ (B : Fin k → Finset (Fin N)) (T : ℤ),
      (∀ i, (B i).card = q - 1) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i, P (B i) = T) := by
  classical
  let e : Fin (k * q) ↪ Fin N := Fin.castLEEmb hKeep
  let P' : Finset (Fin (k * q)) → ℤ := fun S => P (S.map e)
  have hP' : UnitDeletionParameter P' := by
    intro S x hx
    have hMapped := hP (S.map e) (e x) (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa only [P', Finset.map_erase] using hMapped
  obtain ⟨A, t, hA⟩ := exists_uniform_exact_deletion_threshold k q hk hq
    (fun S => (P' S : ℝ))
  have hChoices : ∀ i : Fin k, ∃ x ∈ bundle A i,
      P' ((bundle A i).erase x) = Int.ceil t := by
    intro i
    exact exact_deletion_attains_ceil hP' (hA i).2
  choose x hx hValue using hChoices
  let B : Fin k → Finset (Fin N) := fun i => ((bundle A i).erase (x i)).map e
  refine ⟨B, Int.ceil t, ?_, ?_, hValue⟩
  · intro i
    simp only [B, Finset.card_map, Finset.card_erase_of_mem (hx i), (hA i).1]
  · intro i j hij
    apply (Finset.disjoint_map e).mpr
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    have hi : A z = i := (Finset.mem_filter.mp (Finset.mem_erase.mp hzi).2).2
    have hj : A z = j := (Finset.mem_filter.mp (Finset.mem_erase.mp hzj).2).2
    exact hij (hi.symm.trans hj)

/-- The exact count discarded by the manuscript's construction. -/
theorem omitted_uniform_sets {N k q : ℕ} (hk : 0 < k) (hq : 1 ≤ q)
    (hKeep : k * q ≤ N) (B : Fin k → Finset (Fin N))
    (hCard : ∀ i, (B i).card = q - 1)
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    (Finset.univ \ Finset.univ.biUnion B).card = (N - k * q) + k := by
  classical
  have hPair : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint B := by
    intro i _ j _ hij
    exact hDisjoint i j hij
  have hUnion : (Finset.univ.biUnion B).card = k * (q - 1) := by
    rw [Finset.card_biUnion hPair]
    simp [hCard]
  have hMul : k * (q - 1) + k = k * q := by
    calc
      k * (q - 1) + k = k * ((q - 1) + 1) := by ring
      _ = k * q := by rw [Nat.sub_add_cancel hq]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, hUnion]
  omega

/-- Equal parameters on almost all vertices: the k parts have the paper's
exact order floor(N/k)-1, and at most 2k-1 vertices are omitted. -/
theorem exists_disjoint_equal_parameters (N k : ℕ) (hk : 0 < k)
    (hEnough : 2 * k ≤ N) (P : Finset (Fin N) → ℤ)
    (hP : UnitDeletionParameter P) :
    ∃ (B : Fin k → Finset (Fin N)) (T : ℤ),
      (∀ i, (B i).card = N / k - 1) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i, P (B i) = T) ∧
      (Finset.univ \ Finset.univ.biUnion B).card = (N - k * (N / k)) + k ∧
      (Finset.univ \ Finset.univ.biUnion B).card ≤ 2 * k - 1 := by
  have hq : 2 ≤ N / k := (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hEnough)
  have hKeep : k * (N / k) ≤ N := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self N k
  obtain ⟨B, T, hCard, hDisjoint, hValue⟩ :=
    equal_parameter_sets_on_multiple hk hq hKeep P hP
  have hOmit := omitted_uniform_sets hk (by omega : 1 ≤ N / k) hKeep B hCard hDisjoint
  refine ⟨B, T, hCard, hDisjoint, hValue, hOmit, ?_⟩
  have hRemainder := Nat.mod_lt N hk
  have hDecomp := Nat.mod_add_div N k
  rw [hOmit]
  omega

/-- Repeated deletion bounds every parameter value relative to the empty
set. No normalization P(empty)=0 is needed. -/
theorem unitDeletion_value_bounds {N : ℕ} {P : Finset (Fin N) → ℤ}
    (hP : UnitDeletionParameter P) (S : Finset (Fin N)) :
    P ∅ ≤ P S ∧ P S ≤ P ∅ + (S.card : ℤ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      have hStep := hP (insert x S) x (Finset.mem_insert_self _ _)
      rw [Finset.erase_insert hx] at hStep
      rw [Finset.card_insert_of_notMem hx]
      push_cast
      omega

/-- There are at most s+1 distinct values on s-vertex subsets, by the
integer interval [P(empty),P(empty)+s]. -/
theorem unitDeletion_distinct_values_le {N : ℕ} {P : Finset (Fin N) → ℤ}
    (hP : UnitDeletionParameter P) (s : ℕ) :
    ((Finset.univ.powersetCard s).image P).card ≤ s + 1 := by
  classical
  have hSubset : (Finset.univ.powersetCard s).image P ⊆
      Finset.Icc (P ∅) (P ∅ + (s : ℤ)) := by
    intro z hz
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hz
    have hCard : S.card = s := (Finset.mem_powersetCard.mp hS).2
    have hBounds := unitDeletion_value_bounds hP S
    exact Finset.mem_Icc.mpr (by simpa only [hCard] using hBounds)
  have hInterval : (Finset.Icc (P ∅) (P ∅ + (s : ℤ))).card = s + 1 := by
    rw [Int.card_Icc]
    have hEndpoint : P ∅ + (s : ℤ) + 1 - P ∅ = ((s + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hEndpoint]
    simp
  exact (Finset.card_le_card hSubset).trans_eq hInterval

/-- A finite family of integer values in one interval of length s has at
most s+1 distinct values. This also counts values across different graphs,
not just across subsets of a single fixed graph. -/
theorem integer_family_distinct_values_le {ι : Type*} [Fintype ι]
    (f : ι → ℤ) (base : ℤ) (s : ℕ)
    (h : ∀ i, base ≤ f i ∧ f i ≤ base + (s : ℤ)) :
    (Finset.univ.image f).card ≤ s + 1 := by
  classical
  have hSubset : Finset.univ.image f ⊆ Finset.Icc base (base + (s : ℤ)) := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_Icc.mpr (h i)
  have hInterval : (Finset.Icc base (base + (s : ℤ))).card = s + 1 := by
    rw [Int.card_Icc]
    have hEndpoint : base + (s : ℤ) + 1 - base = ((s + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hEndpoint]
    simp
  exact (Finset.card_le_card hSubset).trans_eq hInterval

/-- The generic Caro--Yuster comparison quoted in the introduction: at
s=floor(N/3), N-2s+2 is strictly larger than every g_P(s)≤s+1. -/
theorem caro_yuster_generic_comparison (N g : ℕ) (h : g ≤ N / 3 + 1) :
    g < N - 2 * (N / 3) + 2 := by
  have hDecomp := Nat.mod_add_div N 3
  have hRem := Nat.mod_lt N (by decide : 0 < 3)
  omega

end FairDivision.BF.Applications
