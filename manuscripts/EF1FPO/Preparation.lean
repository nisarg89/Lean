import EF1FPO.Prices
import EF1FPO.DirectedPaths

/-! Contracts for the perturbation and the return to the original values. -/

set_option autoImplicit false

open scoped BigOperators

namespace EF1FPO

/-- The ordered original columns retained by preparation and the augmented table. -/
structure Preparation (I : Instance) where
  keptCount : ℕ
  keptGood : Fin keptCount → I.Good
  v : I.Agent → Fin (keptCount + I.n) → ℚ
  nonneg : ∀ i g, 0 ≤ v i g

namespace Preparation

variable {I : Instance} (P : Preparation I)

def prepared (P : Preparation I) : Instance where
  n := I.n
  m := P.keptCount + I.n
  hn := I.hn
  v := P.v
  nonneg := P.nonneg

def scaled (i : I.Agent) (g : Fin P.keptCount) : ℕ :=
  (I.v i (P.keptGood g)).num.natAbs *
    ∏ g' ∈ Finset.univ.erase (P.keptGood g), (I.v i g').den

def positiveEntries : Finset (I.Agent × Fin P.keptCount) :=
  Finset.univ.filter (fun cell => 0 < I.v cell.1 (P.keptGood cell.2))

def entryIndex (i : I.Agent) (g : Fin P.keptCount) : ℕ :=
  1 + (P.positiveEntries.filter (fun cell =>
    cell.1 < i ∨ (cell.1 = i ∧ cell.2 < g))).card

def maxValue : ℕ := max 1 (P.positiveEntries.sup (fun cell => P.scaled cell.1 cell.2))

def perturbationExponent : ℕ :=
  let D := 2 ^ P.positiveEntries.card
  let V := P.maxValue
  (max (8 * (P.keptCount + 1) * V * D)
    (max (8 * I.n * V ^ I.n * D) (8 * I.n ^ 2 * D ^ 2))).size

def perturbation : ℚ := (1 / 2) ^ P.perturbationExponent

def originalColumn (g : Fin P.keptCount) : P.prepared.Good := Fin.castAdd I.n g

def auxiliaryColumn (i : I.Agent) : P.prepared.Good := Fin.natAdd P.keptCount i

/-- Exact row scaling, row-major numbering of positive entries, and private auxiliary goods. -/
def IsPreparation : Prop :=
  StrictMono P.keptGood ∧
  (∀ g : I.Good, (∃ k, P.keptGood k = g) ↔ ∃ i, 0 < I.v i g) ∧
  (∀ i g, P.v i (P.originalColumn g) =
    (P.scaled i g : ℚ) * (1 + (2 : ℚ) ^ P.entryIndex i g * P.perturbation)) ∧
  ∀ i j, P.v i (P.auxiliaryColumn j) = if i = j then 1 / 4 else 0

/-- Keep the assigned owners of the retained goods and assign all discarded goods to agent zero. -/
def IsRecoveredAllocation (A : P.prepared.Allocation) (B : I.Allocation) : Prop :=
  (∀ g, B (P.keptGood g) = A (P.originalColumn g)) ∧
  ∀ g, (∀ i, I.v i g = 0) → B g = ⟨0, I.hn⟩

theorem exists_preparation (I : Instance) : ∃ P : Preparation I, P.IsPreparation := by
  classical
  let kept : Finset I.Good := Finset.univ.filter (fun g => ∃ i, 0 < I.v i g)
  let order : Fin kept.card ↪o I.Good := kept.orderEmbOfFin rfl
  let base : Preparation I := ⟨kept.card, order, fun _ _ => 0, fun _ _ => le_rfl⟩
  let values (i : I.Agent) : Fin (kept.card + I.n) → ℚ :=
    Fin.addCases
      (fun g => (base.scaled i g : ℚ) *
        (1 + (2 : ℚ) ^ base.entryIndex i g * base.perturbation))
      (fun j => if i = j then 1 / 4 else 0)
  have hNonneg (i : I.Agent) (g : Fin (kept.card + I.n)) : 0 ≤ values i g := by
    refine Fin.addCases ?_ ?_ g
    · intro k
      simp only [values, Fin.addCases_left]
      unfold perturbation
      positivity
    · intro j
      simp only [values, Fin.addCases_right]
      split <;> norm_num
  let P : Preparation I := ⟨kept.card, order, values, hNonneg⟩
  refine ⟨P, order.strictMono, ?_, ?_, ?_⟩
  · intro g
    change (g ∈ Set.range (kept.orderEmbOfFin rfl)) ↔ ∃ i, 0 < I.v i g
    rw [Finset.range_orderEmbOfFin]
    simp [kept]
  · intro i g
    change values i (Fin.castAdd I.n g) =
      (base.scaled i g : ℚ) * (1 + 2 ^ base.entryIndex i g * base.perturbation)
    simp only [values, Fin.addCases_left]
  · intro i j
    change values i (Fin.natAdd kept.card j) = _
    simp only [values, Fin.addCases_right]

theorem prepared_positive_goods (h : P.IsPreparation) :
    ∀ g, ∃ i, 0 < P.prepared.v i g := by
  intro g
  refine Fin.addCases ?_ ?_ g
  · intro k
    obtain ⟨i, hi⟩ := (h.2.1 (P.keptGood k)).mp ⟨k, rfl⟩
    refine ⟨i, ?_⟩
    change 0 < P.v i (P.originalColumn k)
    rw [h.2.2.1 i k]
    have hNum : 0 < (I.v i (P.keptGood k)).num.natAbs :=
      Int.natAbs_pos.mpr (Rat.num_pos.mpr hi).ne'
    have hDens : 0 < ∏ g' ∈ Finset.univ.erase (P.keptGood k), (I.v i g').den :=
      CanonicallyOrderedAdd.prod_pos.mpr (fun g' _ => (I.v i g').den_pos)
    have hScaled : 0 < P.scaled i k := Nat.mul_pos hNum hDens
    unfold perturbation
    positivity
  · intro i
    refine ⟨i, ?_⟩
    change 0 < P.v i (P.auxiliaryColumn i)
    rw [h.2.2.2 i i]
    norm_num

theorem prepared_positive_agents (h : P.IsPreparation) :
    ∀ i, ∃ g, 0 < P.prepared.v i g := by
  change ∀ i : I.Agent, ∃ g : Fin (P.keptCount + I.n), 0 < P.v i g
  intro i
  refine ⟨P.auxiliaryColumn i, ?_⟩
  change 0 < P.v i (P.auxiliaryColumn i)
  rw [h.2.2.2 i i]
  norm_num

/-- Positive integral row multiplier used before perturbing a retained value. -/
def rowFactor (_P : Preparation I) (i : I.Agent) : ℕ :=
  ∏ g : I.Good, (I.v i g).den

abbrev Cell (P : Preparation I) := I.Agent × Fin P.keptCount

def ScaledProduct (S : Finset P.Cell) : ℕ :=
  ∏ e ∈ S, P.scaled e.1 e.2

def PerturbedProduct (S : Finset P.Cell) : ℚ :=
  ∏ e ∈ S, P.v e.1 (P.originalColumn e.2)

theorem rowFactor_pos (i : I.Agent) : 0 < P.rowFactor i := by
  exact CanonicallyOrderedAdd.prod_pos.mpr (fun g _ => (I.v i g).den_pos)

theorem scaled_eq_rowFactor_mul (i : I.Agent) (g : Fin P.keptCount) :
    (P.scaled i g : ℚ) = (P.rowFactor i : ℚ) * I.v i (P.keptGood g) := by
  let q := I.v i (P.keptGood g)
  let D := ∏ j ∈ Finset.univ.erase (P.keptGood g), (I.v i j).den
  have hProd : D * q.den = P.rowFactor i :=
    Finset.prod_erase_mul Finset.univ (fun j => (I.v i j).den) (Finset.mem_univ (P.keptGood g))
  have hNonneg : 0 ≤ q.num := Rat.num_nonneg.mpr (I.nonneg i (P.keptGood g))
  have hNum : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg hNonneg)
  change ((q.num.natAbs * D : ℕ) : ℚ) = (P.rowFactor i : ℚ) * q
  rw [← hProd, Nat.cast_mul, Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num, hNum, mul_comm]

theorem perturbation_bounds :
    let V : ℚ := P.maxValue
    let D : ℚ := 2 ^ P.positiveEntries.card
    0 < P.perturbation ∧ 8 * (P.keptCount + 1 : ℚ) * V * D * P.perturbation < 1 ∧
      8 * (I.n : ℚ) * V ^ I.n * D * P.perturbation < 1 ∧
      8 * (I.n : ℚ) ^ 2 * D ^ 2 * P.perturbation < 1 := by
  let V := P.maxValue
  let D := 2 ^ P.positiveEntries.card
  let a := 8 * (P.keptCount + 1) * V * D
  let b := 8 * I.n * V ^ I.n * D
  let c := 8 * I.n ^ 2 * D ^ 2
  let k := max a (max b c)
  have heq : P.perturbationExponent = k.size := rfl
  have hpert : P.perturbation = ((2 : ℚ) ^ k.size)⁻¹ := by
    rw [perturbation, heq, one_div, inv_pow]
  have hD : 0 < (2 : ℚ) ^ k.size := by positivity
  have hbound (t : ℕ) (ht : t ≤ k) : (t : ℚ) * P.perturbation < 1 := by
    rw [hpert, ← div_eq_mul_inv, div_lt_one₀ hD]
    exact_mod_cast ht.trans_lt (Nat.lt_size_self k)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpert]
    exact inv_pos.mpr hD
  · simpa [a, V, D] using hbound a (le_max_left a (max b c))
  · simpa [b, V, D] using hbound b ((le_max_left b c).trans (le_max_right a (max b c)))
  · simpa [c, V, D] using hbound c ((le_max_right b c).trans (le_max_right a (max b c)))

theorem entryIndex_le_positive_card (e : P.Cell) (he : e ∈ P.positiveEntries) :
    P.entryIndex e.1 e.2 ≤ P.positiveEntries.card := by
  let S := P.positiveEntries.filter (fun cell =>
    cell.1 < e.1 ∨ (cell.1 = e.1 ∧ cell.2 < e.2))
  have hsub : S ⊆ P.positiveEntries := Finset.filter_subset _ _
  have heS : e ∉ S := by simp [S]
  have hlt := Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨e, he, heS⟩)
  change 1 + S.card ≤ P.positiveEntries.card
  omega

theorem entryIndex_injOn_positive :
    Set.InjOn (fun e : P.Cell => P.entryIndex e.1 e.2) (P.positiveEntries : Set P.Cell) := by
  let prec (e f : P.Cell) : Prop := e.1 < f.1 ∨ (e.1 = f.1 ∧ e.2 < f.2)
  let smaller (f : P.Cell) := P.positiveEntries.filter (fun e => prec e f)
  have hirr (e : P.Cell) : ¬ prec e e := by simp [prec]
  have htrans {a b c : P.Cell} (hab : prec a b) (hbc : prec b c) : prec a c := by
    rcases hab with h | ⟨heq, h⟩ <;> rcases hbc with h' | ⟨heq', h'⟩
    · exact Or.inl (h.trans h')
    · exact Or.inl (h.trans_le heq'.le)
    · exact Or.inl (heq.le.trans_lt h')
    · exact Or.inr ⟨heq.trans heq', h.trans h'⟩
  have hmono {e f : P.Cell} (he : e ∈ P.positiveEntries) (hef : prec e f) :
      P.entryIndex e.1 e.2 < P.entryIndex f.1 f.2 := by
    have hsub : smaller e ⊆ smaller f := by
      intro k hk
      obtain ⟨hLeast, hrel⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hLeast, htrans hrel hef⟩
    have hEmem : e ∈ smaller f := Finset.mem_filter.mpr ⟨he, hef⟩
    have hEnomem : e ∉ smaller e := fun hh => hirr e (Finset.mem_filter.mp hh).2
    have hlt := Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨e, hEmem, hEnomem⟩)
    change 1 + (smaller e).card < 1 + (smaller f).card
    omega
  intro e he f hf hEq
  rcases lt_trichotomy e.1 f.1 with hlt | hsame | hgt
  · exact ((hmono he (Or.inl hlt)).ne hEq).elim
  · rcases lt_trichotomy e.2 f.2 with hlt | hsame' | hgt
    · exact ((hmono he (Or.inr ⟨hsame, hlt⟩)).ne hEq).elim
    · exact Prod.ext hsame hsame'
    · exact ((hmono hf (Or.inr ⟨hsame.symm, hgt⟩)).ne hEq.symm).elim
  · exact ((hmono hf (Or.inl hgt)).ne hEq.symm).elim

theorem product_one_add_bounds {α : Type*} (s : Finset α) (x : α → ℚ)
    (hn : ∀ a ∈ s, 0 ≤ x a) (hs : ∑ a ∈ s, x a ≤ 1 / 2) :
    0 ≤ (∏ a ∈ s, (1 + x a)) - (1 + ∑ a ∈ s, x a) ∧
      (∏ a ∈ s, (1 + x a)) - (1 + ∑ a ∈ s, x a) ≤ 2 * (∑ a ∈ s, x a) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num
  | @insert a s has ih =>
    rw [Finset.sum_insert has] at hs
    simp only [Finset.sum_insert has, Finset.prod_insert has]
    have ha : 0 ≤ x a := hn a (Finset.mem_insert_self _ _)
    have htail (b : α) (hb : b ∈ s) : 0 ≤ x b := hn b (Finset.mem_insert_of_mem hb)
    let S := ∑ b ∈ s, x b
    let B := ∏ b ∈ s, (1 + x b)
    have hSnonneg : 0 ≤ S := Finset.sum_nonneg htail
    have hSsmall : S ≤ 1 / 2 := by change x a + S ≤ 1 / 2 at hs; linarith
    obtain ⟨hlo, hhi⟩ := ih htail hSsmall
    change 0 ≤ B - (1 + S) at hlo
    change B - (1 + S) ≤ 2 * S ^ 2 at hhi
    change 0 ≤ (1 + x a) * B - (1 + (x a + S)) ∧
      (1 + x a) * B - (1 + (x a + S)) ≤ 2 * (x a + S) ^ 2
    have hpos : 0 ≤ 1 + x a := by linarith
    have hRlo := mul_nonneg hpos hlo
    have hRhi := mul_le_mul_of_nonneg_left hhi hpos
    have hxS : 0 ≤ x a * S := mul_nonneg ha hSnonneg
    have hquad : 2 * S ^ 2 ≤ S := by
      have h := mul_nonneg hSnonneg (show 0 ≤ 1 - 2 * S by linarith)
      nlinarith
    have hthird := mul_le_mul_of_nonneg_left hquad ha
    constructor <;> nlinarith [sq_nonneg (x a)]

private def entryBump (e : P.Cell) : ℚ := (2 : ℚ) ^ P.entryIndex e.1 e.2 * P.perturbation

private def bumpSum (S : Finset P.Cell) : ℚ := ∑ e ∈ S, P.entryBump e

private def factorProduct (S : Finset P.Cell) : ℚ := ∏ e ∈ S, (1 + P.entryBump e)

private def bumpBound : ℚ := (I.n : ℚ) * (2 : ℚ) ^ P.positiveEntries.card * P.perturbation

private theorem scaled_le_maxValue (e : P.Cell) : P.scaled e.1 e.2 ≤ P.maxValue := by
  by_cases h : e ∈ P.positiveEntries
  · exact (Finset.le_sup (f := fun c => P.scaled c.1 c.2) h).trans (le_max_right _ _)
  · have hv : ¬ 0 < I.v e.1 (P.keptGood e.2) := by simpa [positiveEntries] using h
    have he : I.v e.1 (P.keptGood e.2) = 0 := le_antisymm (le_of_not_gt hv) (I.nonneg _ _)
    simp [scaled, he]

private theorem perturb_product_control (h : P.IsPreparation) (S : Finset P.Cell)
    (hS : S ⊆ P.positiveEntries) (hn : S.card ≤ I.n) :
    P.PerturbedProduct S = (P.ScaledProduct S : ℚ) * P.factorProduct S ∧
    0 ≤ P.bumpSum S ∧ P.bumpSum S ≤ P.bumpBound ∧ P.bumpBound ≤ 1 / 2 ∧
    0 ≤ P.factorProduct S - (1 + P.bumpSum S) ∧
      P.factorProduct S - (1 + P.bumpSum S) ≤ 2 * P.bumpBound ^ 2 := by
  have hδ := P.perturbation_bounds.1
  have hBump (e : P.Cell) : 0 ≤ P.entryBump e := by unfold entryBump; positivity
  have hSum : 0 ≤ P.bumpSum S := Finset.sum_nonneg (fun e _ => hBump e)
  let D := (2 : ℚ) ^ P.positiveEntries.card
  have hD : 0 < D := by dsimp [D]; positivity
  have hSum_le : P.bumpSum S ≤ P.bumpBound := by
    change (∑ e ∈ S, P.entryBump e) ≤ (I.n : ℚ) * D * P.perturbation
    calc
      _ ≤ ∑ _ ∈ S, D * P.perturbation := by
        refine Finset.sum_le_sum (fun e he => ?_)
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (P.entryIndex_le_positive_card e (hS he))) hδ.le
      _ = (S.card : ℚ) * (D * P.perturbation) := by simp
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (mul_nonneg hD.le hδ.le)
  have hBN : 0 ≤ P.bumpBound := hSum.trans hSum_le
  have hV : (1 : ℚ) ≤ P.maxValue := by exact_mod_cast le_max_left 1 _
  have hVpow : (1 : ℚ) ≤ (P.maxValue : ℚ) ^ I.n := one_le_pow₀ hV
  have hSmall' : 8 * P.bumpBound * (P.maxValue : ℚ) ^ I.n < 1 := by
    have hSecond := P.perturbation_bounds.2.2.1
    dsimp [bumpBound] at *
    convert hSecond using 1 <;> ring
  have h8 := mul_le_mul_of_nonneg_left hVpow (show 0 ≤ 8 * P.bumpBound by positivity)
  have hSmall : P.bumpBound ≤ 1 / 2 := by linarith
  obtain ⟨hLo, hHi⟩ := product_one_add_bounds S (P.entryBump) (fun e _ => hBump e)
    (hSum_le.trans hSmall)
  refine ⟨?_, hSum, hSum_le, hSmall, hLo, ?_⟩
  · simp only [PerturbedProduct, ScaledProduct, Nat.cast_prod, factorProduct,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun e _ => h.2.2.1 e.1 e.2)
  · refine hHi.trans ?_
    have hsq := pow_le_pow_left₀ hSum hSum_le 2
    simpa only [bumpSum] using mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℚ) ≤ 2)

set_option maxHeartbeats 2000000 in
theorem preserves_strict_product (h : P.IsPreparation) (S T : Finset P.Cell)
    (hS : S ⊆ P.positiveEntries) (hT : T ⊆ P.positiveEntries)
    (hnS : S.card ≤ I.n) (hnT : T.card ≤ I.n)
    (hlt : P.ScaledProduct S < P.ScaledProduct T) :
    P.PerturbedProduct S < P.PerturbedProduct T := by
  obtain ⟨hSEq, hSN, hSe, hNsmall, hLo, hHi⟩ := P.perturb_product_control h S hS hnS
  obtain ⟨hTEq, hTN, _, _, hTLo, _⟩ := P.perturb_product_control h T hT hnT
  have hN : 0 ≤ P.bumpBound := hSN.trans hSe
  have hFactorS : P.factorProduct S - 1 ≤ 2 * P.bumpBound := by
    have hb := mul_nonneg hN (show 0 ≤ 1 - 2 * P.bumpBound by linarith)
    linarith [show 2 * P.bumpBound ^ 2 ≤ P.bumpBound by nlinarith]
  have hFactorT : 1 ≤ P.factorProduct T := by linarith
  have hOrig : P.ScaledProduct S ≤ P.maxValue ^ I.n := by
    unfold ScaledProduct
    calc
      _ ≤ ∏ _ ∈ S, P.maxValue := Finset.prod_le_prod' (fun e _ => P.scaled_le_maxValue e)
      _ = P.maxValue ^ S.card := by simp
      _ ≤ _ := Nat.pow_le_pow_right (le_max_left 1 _) hnS
  have hOrigCast : (P.ScaledProduct S : ℚ) ≤ (P.maxValue : ℚ) ^ I.n := by exact_mod_cast hOrig
  have hTiny : (P.maxValue : ℚ) ^ I.n * (2 * P.bumpBound) < 1 := by
    have hSecond := P.perturbation_bounds.2.2.1
    have hnN : 8 * ((P.maxValue : ℚ) ^ I.n * P.bumpBound) < 1 := by
      convert hSecond using 1 <;> unfold bumpBound <;> ring
    linarith
  have hGap : (P.ScaledProduct S : ℚ) + 1 ≤ (P.ScaledProduct T : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt hlt
  rw [hSEq, hTEq]
  calc
    _ = (P.ScaledProduct S : ℚ) + (P.ScaledProduct S : ℚ) * (P.factorProduct S - 1) := by ring
    _ ≤ (P.ScaledProduct S : ℚ) + (P.maxValue : ℚ) ^ I.n * (2 * P.bumpBound) := by
      have hmul : (P.ScaledProduct S : ℚ) * (P.factorProduct S - 1) ≤
          (P.maxValue : ℚ) ^ I.n * (2 * P.bumpBound) :=
        (mul_le_mul_of_nonneg_left hFactorS (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hOrigCast (by positivity))
      exact add_le_add le_rfl hmul
    _ < (P.ScaledProduct S : ℚ) + 1 := add_lt_add_of_le_of_lt le_rfl hTiny
    _ ≤ (P.ScaledProduct T : ℚ) := hGap
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hFactorT (Nat.cast_nonneg (P.ScaledProduct T))

set_option maxHeartbeats 2000000 in
theorem separates_product_sets (h : P.IsPreparation) (S T : Finset P.Cell)
    (hS : S ⊆ P.positiveEntries) (hT : T ⊆ P.positiveEntries)
    (hnS : S.card ≤ I.n) (hnT : T.card ≤ I.n) (hne : S ≠ T) :
    P.PerturbedProduct S ≠ P.PerturbedProduct T := by
  classical
  rcases lt_trichotomy (P.ScaledProduct S) (P.ScaledProduct T) with hlt | heq | hgt
  · exact (P.preserves_strict_product h S T hS hT hnS hnT hlt).ne
  · intro hEqual
    obtain ⟨hSEq, _, _, _, hSLo, hSHi⟩ := P.perturb_product_control h S hS hnS
    obtain ⟨hTEq, _, _, _, hTLo, hTHi⟩ := P.perturb_product_control h T hT hnT
    have hScale : 0 < (P.ScaledProduct S : ℚ) := by
      simp only [ScaledProduct, Nat.cast_prod]
      refine Finset.prod_pos (fun e me => ?_)
      rw [P.scaled_eq_rowFactor_mul]
      exact mul_pos (by exact_mod_cast P.rowFactor_pos e.1)
        ((Finset.mem_filter.mp (hS me)).2)
    rw [hSEq, hTEq, ← heq] at hEqual
    have hFactorEq := mul_left_cancel₀ hScale.ne' hEqual
    let index (e : P.Cell) := P.entryIndex e.1 e.2
    have hImages : S.image index ≠ T.image index := by
      intro himage
      apply hne
      ext e
      constructor
      · intro hm
        obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp
          (himage ▸ Finset.mem_image_of_mem index hm)
        exact P.entryIndex_injOn_positive (hT hf) (hS hm) hfe ▸ hf
      · intro hm
        obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp
          (himage.symm ▸ Finset.mem_image_of_mem index hm)
        exact P.entryIndex_injOn_positive (hS hf) (hT hm) hfe ▸ hf
    let Q (U : Finset P.Cell) : ℕ := ∑ e ∈ U, 2 ^ index e
    have hQ (U : Finset P.Cell) (hU : U ⊆ P.positiveEntries) :
        Q U = ∑ k ∈ U.image index, 2 ^ k := by
      unfold Q
      exact (Finset.sum_image (fun _ hx _ hy hxy =>
        P.entryIndex_injOn_positive (hU hx) (hU hy) hxy)).symm
    have hBits (U : Finset ℕ) : (∑ k ∈ U, 2 ^ k).bitIndices.toFinset = U := by
      have hSum : ((U.sort (· ≤ ·)).map (fun k => 2 ^ k)).sum = ∑ k ∈ U, 2 ^ k := by
        change ((↑(U.sort (· ≤ ·)) : Multiset ℕ).map (fun k => 2 ^ k)).sum = _
        rw [Finset.sort_eq]
        rfl
      have hBin := Nat.bitIndices_sum_map_two_pow U.sortedLT_sort
      rw [hSum] at hBin
      simpa using congrArg List.toFinset hBin
    have hQne : Q S ≠ Q T := by
      intro hQT
      rw [hQ S hS, hQ T hT] at hQT
      exact hImages ((hBits (S.image index)).symm.trans (hQT ▸ hBits (T.image index)))
    have hLinear (U : Finset P.Cell) : P.bumpSum U = (Q U : ℚ) * P.perturbation := by
      simp [bumpSum, entryBump, Q, index, Finset.sum_mul]
    have hδ := P.perturbation_bounds.1
    have hBound : 2 * P.bumpBound ^ 2 < P.perturbation := by
      have hb := mul_lt_mul_of_pos_right P.perturbation_bounds.2.2.2 hδ
      have hEq : (8 * (I.n : ℚ) ^ 2 * ((2 : ℚ) ^ P.positiveEntries.card) ^ 2 *
          P.perturbation) * P.perturbation = 8 * P.bumpBound ^ 2 := by
        unfold bumpBound
        ring
      rw [hEq, one_mul] at hb
      nlinarith [sq_nonneg P.bumpBound]
    have strictDiff {U V : Finset P.Cell} (hUV : Q U < Q V) :
        P.bumpSum U + P.perturbation ≤ P.bumpSum V := by
      have h := mul_le_mul_of_nonneg_right
        (show (Q U : ℚ) + 1 ≤ (Q V : ℚ) by exact_mod_cast Nat.succ_le_of_lt hUV) hδ.le
      simpa only [hLinear, add_mul, one_mul] using h
    rcases lt_or_gt_of_ne hQne with hs | ht
    · linarith [strictDiff hs]
    · linarith [strictDiff ht]
  · exact (P.preserves_strict_product h T S hT hS hnT hnS hgt).ne.symm

set_option maxHeartbeats 2000000 in
theorem alternating_cells_of_cycle (h : P.IsPreparation) (w : P.prepared.Weights)
    (hw : P.prepared.Positive w) (v : P.prepared.Agent ⊕ P.prepared.Good)
    (p : (P.prepared.highestBidderGraph w).Walk v v) (hp : p.IsCycle) :
    ∃ S T : Finset P.Cell, S ⊆ P.positiveEntries ∧ T ⊆ P.positiveEntries ∧
      S.card ≤ I.n ∧ T.card ≤ I.n ∧ S ≠ T ∧ P.PerturbedProduct S = P.PerturbedProduct T := by
  classical
  let J := P.prepared
  let W := J.Agent ⊕ J.Good
  let G : SimpleGraph W := J.highestBidderGraph w
  have high_left (i : J.Agent) (g : J.Good) (ha : G.Adj (Sum.inl i) (Sum.inr g)) :
      J.IsHighestBidder w i g := by
    change (Sum.inl i : W) ≠ Sum.inr g ∧ (J.IsHighestBidder w i g ∨ False) at ha
    exact ha.2.resolve_right id
  have positive_val (i : J.Agent) (g : J.Good) (hi : J.IsHighestBidder w i g) : 0 < J.value i g := by
    obtain ⟨j, hj⟩ := P.prepared_positive_goods h g
    have hv : 0 < J.value j g := by exact_mod_cast hj
    have hb : 0 < J.bid w i g := (mul_pos (hw j) hv).trans_le (hi j)
    exact pos_of_mul_pos_right hb (hw i).le
  have aux_neighbor (i : I.Agent) (a : W) (ha : G.Adj (Sum.inr (P.auxiliaryColumn i)) a) : a = Sum.inl i := by
    cases a with
    | inl j =>
      have hj : J.IsHighestBidder w j (P.auxiliaryColumn i) := by
        simpa [G, Instance.highestBidderGraph] using ha
      have hv := positive_val j (P.auxiliaryColumn i) hj
      change 0 < (P.v j (P.auxiliaryColumn i) : ℝ) at hv
      by_cases hji : @Eq I.Agent j i
      · exact congrArg (fun k : I.Agent => (Sum.inl k : W)) hji
      · have hv0 : P.v j (P.auxiliaryColumn i) = 0 := (h.2.2.2 j i).trans (ite_eq_right hji)
        rw [hv0] at hv
        norm_num at hv
    | inr g => simp [G, Instance.highestBidderGraph] at ha
  have noAux (i : I.Agent) : Sum.inr (P.auxiliaryColumn i) ∉ p.support := by
    intro hi
    let c := p.rotate (Sum.inr (P.auxiliaryColumn i)) hi
    have hc : c.IsCycle := hp.rotate hi
    have hs := aux_neighbor i c.snd (c.adj_snd hc.not_nil)
    have ht := aux_neighbor i c.penultimate (c.adj_penultimate hc.not_nil).symm
    exact hc.snd_ne_penultimate (hs.trans ht.symm)
  have original (g : J.Good) : Sum.inr g ∈ p.support → ∃ k, P.originalColumn k = g := by
    refine Fin.addCases (motive := fun g => Sum.inr g ∈ p.support → ∃ k, P.originalColumn k = g) ?_ ?_ g
    · intro k _
      exact ⟨k, rfl⟩
    · intro i hi
      exact (noAux i hi).elim
  let D : Finset G.Dart := p.darts.toFinset
  let D' := {d : G.Dart // d ∈ D}
  let shape (d : D') (e : P.Cell) : Prop :=
    (d.val.fst = Sum.inl e.1 ∧ d.val.snd = Sum.inr (P.originalColumn e.2)) ∨
      (d.val.fst = Sum.inr (P.originalColumn e.2) ∧ d.val.snd = Sum.inl e.1)
  have hcells (d : D') : ∃ e : P.Cell, shape d e := by
    have hd : d.val ∈ p.darts := List.mem_toFinset.mp d.property
    have hv := d.val.adj
    cases hf : d.val.fst with
    | inl i =>
      cases hs : d.val.snd with
      | inl j => simp [G, Instance.highestBidderGraph, hf, hs] at hv
      | inr g =>
        have hG : Sum.inr g ∈ p.support := hs ▸ p.dart_snd_mem_support_of_mem_darts hd
        obtain ⟨k, hk⟩ := original g hG
        exact ⟨(i, k), Or.inl ⟨hf, hs.trans (congrArg Sum.inr hk).symm⟩⟩
    | inr g =>
      cases hs : d.val.snd with
      | inl i =>
        have hG : Sum.inr g ∈ p.support := hf ▸ p.dart_fst_mem_support_of_mem_darts hd
        obtain ⟨k, hk⟩ := original g hG
        exact ⟨(i, k), Or.inr ⟨hf.trans (congrArg Sum.inr hk).symm, hs⟩⟩
      | inr k => simp [G, Instance.highestBidderGraph, hf, hs] at hv
  let cell (d : D') : P.Cell := (hcells d).choose
  have hshape (d : D') : shape d (cell d) := (hcells d).choose_spec
  have cell_positive (d : D') : cell d ∈ P.positiveEntries := by
    have ha := d.val.adj
    have hi : J.IsHighestBidder w (cell d).1 (P.originalColumn (cell d).2) := by
      rcases hshape d with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · exact high_left _ _ ((congrArg₂ (fun a b : W => G.Adj a b) ha' hb').mp ha)
      · exact high_left _ _ ((congrArg₂ (fun a b : W => G.Adj a b) hb' ha').mp ha.symm)
    have hv := positive_val (cell d).1 (P.originalColumn (cell d).2) hi
    have hq : 0 < P.v (cell d).1 (P.originalColumn (cell d).2) := by exact_mod_cast hv
    rw [h.2.2.1, P.scaled_eq_rowFactor_mul] at hq
    have hFactor : 0 < (1 : ℚ) + 2 ^ P.entryIndex (cell d).1 (cell d).2 * P.perturbation := by
      have := P.perturbation_bounds.1
      positivity
    have hpv : 0 < I.v (cell d).1 (P.keptGood (cell d).2) :=
      pos_of_mul_pos_right (pos_of_mul_pos_left hq hFactor.le) (Nat.cast_nonneg _)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpv⟩
  have hL (d : D') (hd : d.val.fst.isLeft) :
      d.val.fst = Sum.inl (cell d).1 ∧ d.val.snd = Sum.inr (P.originalColumn (cell d).2) := by
    rcases hshape d with hf | ⟨hf, _⟩
    · exact hf
    · simp [hf] at hd
  have hR (d : D') (hd : ¬ d.val.fst.isLeft) :
      d.val.fst = Sum.inr (P.originalColumn (cell d).2) ∧ d.val.snd = Sum.inl (cell d).1 := by
    rcases hshape d with ⟨hf, _⟩ | hf
    · exact (hd (by rw [hf]; rfl)).elim
    · exact hf
  let F : Finset D' := D.attach.filter (fun d => d.val.fst.isLeft)
  let B : Finset D' := D.attach.filter (fun d => ¬ d.val.fst.isLeft)
  let S := F.image cell
  let T := B.image cell
  have hF (d : D') (hd : d ∈ F) := hL d (Finset.mem_filter.mp hd).2
  have hB (d : D') (hd : d ∈ B) := hR d (Finset.mem_filter.mp hd).2
  have hEdgeList : (p.darts.map SimpleGraph.Dart.edge).Nodup := by
    rw [← p.edges_eq_map_darts]
    exact hp.isTrail.edges_nodup
  have hdarts : p.darts.Nodup := List.Nodup.of_map _ hEdgeList
  have hDval : D.val = (p.darts : Multiset G.Dart) := by
    unfold D
    rw [← List.toFinset_eq hdarts]
  have map_inj {β : Type} (f : G.Dart → β) (hf : (p.darts.map f).Nodup) :
      Set.InjOn f (D : Set G.Dart) := by
    apply Finset.nodup_map_iff_injOn.mp
    rwa [hDval, Multiset.map_coe, Multiset.coe_nodup]
  have injEdge := map_inj SimpleGraph.Dart.edge hEdgeList
  have injFst := map_inj (fun d => d.fst)
    (by rw [p.map_fst_darts]; exact hp.nodup_dropLast_support)
  have injSnd := map_inj (fun d => d.snd)
    (by rw [p.map_snd_darts]; exact hp.support_nodup)
  have projL : Set.InjOn (fun d : D' => (cell d).1) (F : Set D') := by
    intro a ha b hb he
    exact Subtype.ext (injFst a.property b.property ((hF a ha).1.trans
      ((congrArg Sum.inl he).trans (hF b hb).1.symm)))
  have projR : Set.InjOn (fun d : D' => (cell d).1) (B : Set D') := by
    intro a ha b hb he
    exact Subtype.ext (injSnd a.property b.property ((hB a ha).2.trans
      ((congrArg Sum.inl he).trans (hB b hb).2.symm)))
  have cellInjL : Set.InjOn cell (F : Set D') := fun _ ha _ hb he =>
    projL ha hb (congrArg Prod.fst he)
  have cellInjR : Set.InjOn cell (B : Set D') := fun _ ha _ hb he =>
    projR ha hb (congrArg Prod.fst he)
  have cardF : F.card ≤ I.n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card_of_injOn (fun d : D' => (cell d).1)
        (fun _ _ => Finset.mem_univ _) projL
  have cardB : B.card ≤ I.n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card_of_injOn (fun d : D' => (cell d).1)
        (fun _ _ => Finset.mem_univ _) projR
  have hS : S ⊆ P.positiveEntries := by
    intro e he
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp he
    exact cell_positive d
  have hT : T ⊆ P.positiveEntries := by
    intro e he
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp he
    exact cell_positive d
  have hDis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro e ha hb
    obtain ⟨a, ha, hcellA⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hb, hcellB⟩ := Finset.mem_image.mp hb
    have hd1 := hF a ha
    have hd2 := hB b hb
    have sameCell := hcellA.trans hcellB.symm
    have sameEdge : a.val.edge = b.val.edge := by
      rw [SimpleGraph.Dart.edge, SimpleGraph.Dart.edge, hd1.1, hd1.2, hd2.1, hd2.2, sameCell]
      exact Sym2.eq_swap
    have sameD : a = b := Subtype.ext (injEdge a.property b.property sameEdge)
    subst b
    exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2
  have hne : S ≠ T := by
    intro hEq
    have hd : D.Nonempty := by
      refine Finset.nonempty_of_ne_empty (fun he => hp.not_nil ?_)
      exact SimpleGraph.Walk.darts_eq_nil.mp ((List.toFinset_eq_empty_iff _).1 he)
    obtain ⟨a, ha⟩ := hd
    let d : D' := ⟨a, ha⟩
    by_cases hd' : a.fst.isLeft
    · have he : cell d ∈ S := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ _, hd'⟩)
      exact (Finset.disjoint_left.mp hDis) he (hEq ▸ he)
    · have he : cell d ∈ T := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ _, hd'⟩)
      exact (Finset.disjoint_left.mp hDis) (hEq.symm ▸ he) he
  let numerator (d : G.Dart) : ℝ := match d.fst, d.snd with
    | Sum.inl i, Sum.inr g => J.value i g
    | _, _ => 1
  let denominator (d : G.Dart) : ℝ := match d.fst, d.snd with
    | Sum.inr g, Sum.inl i => J.value i g
    | _, _ => 1
  let point (a : W) : ℝ := match a with
    | Sum.inl i => w i
    | Sum.inr g => J.price w g
  have edge_identity (d : G.Dart) :
      point d.fst * numerator d = point d.snd * denominator d := by
    have hj := d.adj
    cases hf : d.fst with
    | inl i =>
      cases hs : d.snd with
      | inl j => simp [G, Instance.highestBidderGraph, hf, hs] at hj
      | inr g =>
        have hHighest : J.IsHighestBidder w i g := by
          simpa [G, Instance.highestBidderGraph, hf, hs] using hj
        simpa [hf, hs, point, numerator, denominator, Instance.bid] using
          (J.highest_bidder_iff_bid_eq_price w i g).mp hHighest
    | inr g =>
      cases hs : d.snd with
      | inl i =>
        have hHighest : J.IsHighestBidder w i g := by
          simpa [G, Instance.highestBidderGraph, hf, hs] using hj
        simpa [hf, hs, point, numerator, denominator, Instance.bid] using
          ((J.highest_bidder_iff_bid_eq_price w i g).mp hHighest).symm
      | inr j => simp [G, Instance.highestBidderGraph, hf, hs] at hj
  have telescope {a b : W} (q : G.Walk a b) :
      point a * (q.darts.map numerator).prod = point b * (q.darts.map denominator).prod := by
    induction q with
    | nil => simp
    | @cons a c b ha q ih =>
      let d : G.Dart := ⟨(a, c), ha⟩
      have he : point a * numerator d = point c * denominator d := edge_identity d
      simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.prod_cons]
      change point a * (numerator d * (q.darts.map numerator).prod) =
        point b * (denominator d * (q.darts.map denominator).prod)
      calc
        _ = (point a * numerator d) * (q.darts.map numerator).prod := by ring
        _ = (point c * denominator d) * (q.darts.map numerator).prod := by rw [he]
        _ = (point c * (q.darts.map numerator).prod) * denominator d := by ring
        _ = (point b * (q.darts.map denominator).prod) * denominator d := by rw [ih]
        _ = _ := by ring
  have point_pos : 0 < point v := by
    cases v with
    | inl i => exact hw i
    | inr g =>
      obtain ⟨i, hi⟩ := P.prepared_positive_goods h g
      exact (mul_pos (hw i) (by exact_mod_cast hi)).trans_le (J.bid_le_price w i g)
  have hProducts := mul_left_cancel₀ point_pos.ne' (telescope p)
  have convertProd (f : G.Dart → ℝ) : (p.darts.map f).prod = ∏ d ∈ D, f d := by
    rw [Finset.prod_list_map_count]
    exact Finset.prod_congr rfl (fun d hd => by
      rw [List.count_eq_one_of_mem hdarts (List.mem_toFinset.mp hd), pow_one])
  rw [convertProd numerator, convertProd denominator] at hProducts
  have eqS : (P.PerturbedProduct S : ℝ) = ∏ d ∈ D, numerator d := by
    simp only [PerturbedProduct, Rat.cast_prod, S, Finset.prod_image cellInjL]
    calc
      _ = ∏ d ∈ F, numerator d.val := Finset.prod_congr rfl (fun d hd => by
        simp [numerator, (hF d hd).1, (hF d hd).2, J, prepared])
      _ = ∏ d ∈ D.attach, numerator d.val := Finset.prod_subset
        (Finset.filter_subset _ _) (fun d hd hnot => by
          have hside : ¬ d.val.fst.isLeft := fun hh => hnot (Finset.mem_filter.mpr ⟨hd, hh⟩)
          simp [numerator, (hR d hside).1, (hR d hside).2])
      _ = _ := Finset.prod_attach _ _
  have eqT : (P.PerturbedProduct T : ℝ) = ∏ d ∈ D, denominator d := by
    simp only [PerturbedProduct, Rat.cast_prod, T, Finset.prod_image cellInjR]
    calc
      _ = ∏ d ∈ B, denominator d.val := Finset.prod_congr rfl (fun d hd => by
        simp [denominator, (hB d hd).1, (hB d hd).2, J, prepared])
      _ = ∏ d ∈ D.attach, denominator d.val := Finset.prod_subset
        (Finset.filter_subset _ _) (fun d hd hnot => by
          have hside : d.val.fst.isLeft := by
            by_contra hn
            exact hnot (Finset.mem_filter.mpr ⟨hd, hn⟩)
          simp [denominator, (hL d hside).1, (hL d hside).2])
      _ = _ := Finset.prod_attach _ _
  exact ⟨S, T, hS, hT, Finset.card_image_le.trans cardF, Finset.card_image_le.trans cardB,
    hne, by exact_mod_cast eqS.trans (hProducts.trans eqT.symm)⟩

section

set_option allowUnsafeReducibility true in
attribute [local reducible] Preparation.prepared

set_option maxHeartbeats 2500000 in
theorem recover_ef1_only (h : P.IsPreparation) (A : P.prepared.Allocation)
    (hEF1 : P.prepared.IsEF1 A) (w : P.prepared.Weights) (hw : P.prepared.Positive w)
    (hSupport : P.prepared.IsSupported w A) :
    ∃ B : I.Allocation, P.IsRecoveredAllocation A B ∧ I.IsEF1 B := by
  let J := P.prepared
  let B : I.Allocation := fun g => if hg : ∃ k, P.keptGood k = g then
    A (P.originalColumn hg.choose) else ⟨0, I.hn⟩
  have hB : P.IsRecoveredAllocation A B := by
    constructor
    · intro k
      have hk : ∃ f, P.keptGood f = P.keptGood k := ⟨k, rfl⟩
      have he : hk.choose = k := h.1.injective hk.choose_spec
      unfold B
      rw [dite_eq_left hk, he]
    · intro g hg
      refine dite_eq_right (fun hkeep => ?_)
      obtain ⟨i, hi⟩ := (h.2.1 g).mp hkeep
      rw [hg i] at hi
      exact (lt_irrefl _) hi
  let retained (j : I.Agent) : Finset (Fin P.keptCount) :=
    Finset.univ.filter (fun k => A (P.originalColumn k) = j)
  have projection (i : I.Agent) (S : Finset I.Good) :
      I.utility i S = ∑ k ∈ Finset.univ.filter (fun k => P.keptGood k ∈ S),
        I.value i (P.keptGood k) := by
    let f : Fin P.keptCount ↪ I.Good := ⟨P.keptGood, h.1.injective⟩
    let K := Finset.univ.filter (fun k => P.keptGood k ∈ S)
    have hSub : K.map f ⊆ S := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hg
      exact (Finset.mem_filter.mp hk).2
    have hEq : (∑ g ∈ K.map f, I.value i g) = ∑ g ∈ S, I.value i g := by
      refine Finset.sum_subset hSub (fun g hg hn => ?_)
      have hnn : 0 ≤ I.value i g := by exact_mod_cast I.nonneg i g
      apply le_antisymm _ hnn
      by_contra hPos
      obtain ⟨k, hk⟩ := (h.2.1 g).2 ⟨i, by exact_mod_cast lt_of_not_ge hPos⟩
      exact hn (Finset.mem_map.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk ▸ hg⟩, hk⟩)
    exact hEq.symm.trans (Finset.sum_map _ _ _)
  have recovered_bundle (i j : I.Agent) : I.utility i (FairDivision.bundle B j) =
      ∑ k ∈ retained j, I.value i (P.keptGood k) := by
    rw [projection]
    simp [retained, FairDivision.bundle, hB.1]
  have recovered_erase (i j : I.Agent) (k : Fin P.keptCount) :
      I.utility i ((FairDivision.bundle B j).erase (P.keptGood k)) =
        ∑ f ∈ (retained j).erase k, I.value i (P.keptGood f) := by
    rw [projection]
    congr 1
    ext f
    simp [retained, FairDivision.bundle, hB.1, h.1.injective.eq_iff, and_comm]
  have scaled_sum (i : I.Agent) (S : Finset (Fin P.keptCount)) :
      ((∑ k ∈ S, P.scaled i k : ℕ) : ℝ) =
        (P.rowFactor i : ℝ) * ∑ k ∈ S, I.value i (P.keptGood k) := by
    simp only [Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by
      change (P.scaled i k : ℝ) = (P.rowFactor i : ℝ) * (I.v i (P.keptGood k) : ℝ)
      exact_mod_cast P.scaled_eq_rowFactor_mul i k)
  let δ := P.perturbation
  let D := (2 : ℚ) ^ P.positiveEntries.card
  let Δ := (P.maxValue : ℚ) * D * δ
  have hδ : 0 < δ := P.perturbation_bounds.1
  have hΔ : 0 ≤ Δ := by dsimp [Δ, D]; positivity
  have hPertLo (i : I.Agent) (k : Fin P.keptCount) :
      (P.scaled i k : ℝ) ≤ J.value i (P.originalColumn k) := by
    have hq : (P.scaled i k : ℚ) ≤ P.v i (P.originalColumn k) := by
      rw [h.2.2.1 i k]
      have hpos : 0 ≤ (2 : ℚ) ^ P.entryIndex i k * δ := by positivity
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (by linarith : (1 : ℚ) ≤ 1 + (2 : ℚ) ^ P.entryIndex i k * δ)
        (Nat.cast_nonneg (P.scaled i k))
    exact_mod_cast hq
  have hPertHi (i : I.Agent) (k : Fin P.keptCount) :
      J.value i (P.originalColumn k) ≤ (P.scaled i k : ℝ) + (Δ : ℝ) := by
    have hq : P.v i (P.originalColumn k) ≤ (P.scaled i k : ℚ) + Δ := by
      rw [h.2.2.1 i k]
      by_cases hp : (i, k) ∈ P.positiveEntries
      · have hpow : (2 : ℚ) ^ P.entryIndex i k ≤ D := pow_le_pow_right₀
          (by norm_num) (P.entryIndex_le_positive_card (i, k) hp)
        have hscale : (P.scaled i k : ℚ) ≤ P.maxValue :=
          by exact_mod_cast P.scaled_le_maxValue (i, k)
        have hExtra : (P.scaled i k : ℚ) * ((2 : ℚ) ^ P.entryIndex i k * δ) ≤ Δ := by
          unfold Δ
          rw [mul_assoc]
          exact mul_le_mul hscale (mul_le_mul_of_nonneg_right hpow hδ.le)
            (by positivity) (Nat.cast_nonneg _)
        rw [mul_add, mul_one]
        exact add_le_add le_rfl hExtra
      · have hNo : ¬ 0 < I.v i (P.keptGood k) := by simpa [positiveEntries] using hp
        have hZ : I.v i (P.keptGood k) = 0 := le_antisymm (le_of_not_gt hNo) (I.nonneg i _)
        rw [P.scaled_eq_rowFactor_mul, hZ, mul_zero, zero_mul, zero_add]
        exact hΔ
    exact_mod_cast hq
  have hIncrement : (P.keptCount : ℝ) * (Δ : ℝ) + 1 / 4 < 1 := by
    have hSm : 8 * ((P.keptCount : ℚ) + 1) * Δ < 1 := by
      convert P.perturbation_bounds.2.1 using 1 <;> dsimp [Δ, D, δ] <;> ring
    have hQ : (P.keptCount : ℚ) * Δ + 1 / 4 < 1 := by nlinarith
    have hReal : ((↑P.keptCount * Δ + 1 / 4 : ℚ) : ℝ) < (1 : ℚ) := by exact_mod_cast hQ
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] using hReal
  have own_upper (i : I.Agent) : J.utility i (FairDivision.bundle A i) <
      ((∑ k ∈ retained i, P.scaled i k : ℕ) : ℝ) + 1 := by
    let f (g : J.Good) : ℝ := if A g = i then J.value i g else 0
    have hSum : J.utility i (FairDivision.bundle A i) =
        ∑ g : Fin (P.keptCount + I.n), f g := by
      change (∑ g ∈ (Finset.univ.filter (fun g : J.Good => A g = i)), J.value i g) = _
      rw [Finset.sum_filter]
    rw [Fin.sum_univ_add] at hSum
    have hOrig : (∑ k : Fin P.keptCount, f (P.originalColumn k)) =
        ∑ k ∈ retained i, J.value i (P.originalColumn k) := by
      simp [f, retained, Finset.sum_filter]
    have hOrigBound : (∑ k : Fin P.keptCount, f (P.originalColumn k)) ≤
        ((∑ k ∈ retained i, P.scaled i k : ℕ) : ℝ) + (P.keptCount : ℝ) * (Δ : ℝ) := by
      rw [hOrig]
      calc
        _ ≤ ∑ k ∈ retained i, ((P.scaled i k : ℝ) + (Δ : ℝ)) :=
          Finset.sum_le_sum (fun k _ => hPertHi i k)
        _ = ((∑ k ∈ retained i, P.scaled i k : ℕ) : ℝ) + ((retained i).card : ℝ) * (Δ : ℝ) := by
          simp [Finset.sum_add_distrib, nsmul_eq_mul]
        _ ≤ _ := by
          have hcard : (retained i).card ≤ P.keptCount :=
            by simpa using Finset.card_le_card (Finset.subset_univ (retained i))
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (by exact_mod_cast hΔ))
    have hAuxBound : (∑ j : I.Agent, f (P.auxiliaryColumn j)) ≤ 1 / 4 := by
      calc
        _ ≤ ∑ j : I.Agent, if i = j then (1 / 4 : ℝ) else 0 := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          by_cases hij : i = j
          · have hv : J.value i (P.auxiliaryColumn j) = 1 / 4 := by
              change (P.v i (P.auxiliaryColumn j) : ℝ) = 1 / 4
              rw [(h.2.2.2 i j).trans (ite_eq_left hij)]
              norm_num
            simp only [hij, ite_true]
            dsimp only [f]
            rw [hv]
            split <;> norm_num
          · have hv : J.value i (P.auxiliaryColumn j) = 0 := by
              change (P.v i (P.auxiliaryColumn j) : ℝ) = 0
              rw [(h.2.2.2 i j).trans (ite_eq_right hij)]
              norm_num
            simp only [hij, ite_false]
            dsimp only [f]
            rw [hv]
            split <;> norm_num
        _ = 1 / 4 := by simp [eq_comm]
    change J.utility i (FairDivision.bundle A i) =
      (∑ k : Fin P.keptCount, f (P.originalColumn k)) +
        ∑ j : I.Agent, f (P.auxiliaryColumn j) at hSum
    linarith
  refine ⟨B, hB, ?_⟩
  intro i j hCompared
  by_cases hNonempty : (retained j).Nonempty
  · obtain ⟨k₀, hk₀⟩ := hNonempty
    have hNonemptyA : (FairDivision.bundle A j).Nonempty :=
      ⟨P.originalColumn k₀, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk₀).2⟩⟩
    obtain ⟨x, hx, hEnv⟩ := hEF1 i j hNonemptyA
    let f : Fin P.keptCount ↪ J.Good := ⟨P.originalColumn, Fin.castAdd_injective _ _⟩
    have delete_subset : ∃ k ∈ retained j,
        ((retained j).erase k).map f ⊆ (FairDivision.bundle A j).erase x := by
      refine Fin.addCases (m := P.keptCount) (n := I.n)
        (motive := fun x => x ∈ FairDivision.bundle A j → ∃ k ∈ retained j,
          ((retained j).erase k).map f ⊆ (FairDivision.bundle A j).erase x) ?_ ?_ x hx
      · intro k hx
        have hk : k ∈ retained j := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        refine ⟨k, hk, ?_⟩
        intro g hg
        obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hg
        have ht' := Finset.mem_erase.mp ht
        exact Finset.mem_erase.mpr ⟨fun hEq => ht'.1 (f.injective hEq),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht'.2).2⟩⟩
      · intro l _
        refine ⟨k₀, hk₀, ?_⟩
        intro g hg
        obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hg
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_erase.mp ht).2).2⟩⟩
        intro hEq
        have hV := congrArg Fin.val hEq
        change t.val = P.keptCount + l.val at hV
        omega
    obtain ⟨k, hk, hSubset⟩ := delete_subset
    have hTarget : ((∑ t ∈ (retained j).erase k, P.scaled i t : ℕ) : ℝ) ≤
        J.utility i ((FairDivision.bundle A j).erase x) := by
      rw [Nat.cast_sum]
      calc
        _ ≤ ∑ t ∈ (retained j).erase k, J.value i (f t) :=
          Finset.sum_le_sum (fun t _ => hPertLo i t)
        _ = ∑ y ∈ ((retained j).erase k).map f, J.value i y :=
          (Finset.sum_map _ _ _).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun y _ _ => by
          exact_mod_cast J.nonneg i y)
    have hNat : (∑ t ∈ (retained j).erase k, P.scaled i t) ≤ ∑ t ∈ retained i, P.scaled i t := by
      have hLt := (hTarget.trans hEnv).trans_lt (own_upper i)
      have hLtNat : (∑ t ∈ (retained j).erase k, P.scaled i t) <
          (∑ t ∈ retained i, P.scaled i t) + 1 := by exact_mod_cast hLt
      omega
    refine ⟨P.keptGood k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hB.1 k).trans (Finset.mem_filter.mp hk).2⟩, ?_⟩
    have hCast : ((∑ t ∈ (retained j).erase k, P.scaled i t : ℕ) : ℝ) ≤
        ((∑ t ∈ retained i, P.scaled i t : ℕ) : ℝ) := by exact_mod_cast hNat
    rw [scaled_sum, scaled_sum, ← recovered_erase, ← recovered_bundle] at hCast
    exact (mul_le_mul_iff_of_pos_left (by exact_mod_cast P.rowFactor_pos i)).mp hCast
  · obtain ⟨g, hg⟩ := hCompared
    refine ⟨g, hg, ?_⟩
    have hZero : I.utility i (FairDivision.bundle B j) = 0 := by
      rw [recovered_bundle, Finset.not_nonempty_iff_eq_empty.mp hNonempty]
      simp
    have hLe : I.utility i ((FairDivision.bundle B j).erase g) ≤ I.utility i (FairDivision.bundle B j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun x _ _ => by
        exact_mod_cast I.nonneg i x)
    rw [hZero] at hLe
    exact hLe.trans (Finset.sum_nonneg fun x _ => by exact_mod_cast I.nonneg i x)

end

set_option maxHeartbeats 4000000 in
theorem recovered_allocation_positive_support (h : P.IsPreparation)
    (A : P.prepared.Allocation) (w : P.prepared.Weights)
    (hw : P.prepared.Positive w) (hA : P.prepared.IsSupported w A)
    (B : I.Allocation) (hB : P.IsRecoveredAllocation A B) :
    ∃ q : I.Agent → ℚ, I.Positive (fun i => (q i : ℝ)) ∧
      I.IsSupported (fun i => (q i : ℝ)) B := by
  classical
  let J := P.prepared
  let owner (g : Fin P.keptCount) : I.Agent := A (P.originalColumn g)
  have owner_positive (g : Fin P.keptCount) : 0 < I.v (owner g) (P.keptGood g) := by
    obtain ⟨i, hi⟩ := P.prepared_positive_goods h (P.originalColumn g)
    have hBid : 0 < J.bid w i (P.originalColumn g) := mul_pos (hw i) (by exact_mod_cast hi)
    have hOwn := hBid.trans_le (hA (P.originalColumn g) i)
    have hP : 0 < P.v (owner g) (P.originalColumn g) := by
      exact_mod_cast pos_of_mul_pos_right hOwn (hw _).le
    rw [h.2.2.1, P.scaled_eq_rowFactor_mul] at hP
    have hFactor : 0 ≤ (1 : ℚ) + 2 ^ P.entryIndex (owner g) g * P.perturbation := by
      have := P.perturbation_bounds.1
      positivity
    exact pos_of_mul_pos_right (pos_of_mul_pos_left hP hFactor) (Nat.cast_nonneg _)
  have scaled_positive (i : I.Agent) (g : Fin P.keptCount) (hi : 0 < I.v i (P.keptGood g)) :
      0 < (P.scaled i g : ℚ) := by
    rw [P.scaled_eq_rowFactor_mul]
    exact mul_pos (by exact_mod_cast P.rowFactor_pos i) hi
  let arrow (i j : I.Agent) := {g : Fin P.keptCount // owner g = j ∧ 0 < I.v i (P.keptGood g)}
  letI : Quiver I.Agent := ⟨arrow⟩
  letI : ∀ i j : I.Agent, Finite (i ⟶ j) := fun i j => by
    change Finite (arrow i j)
    infer_instance
  let gain {i j : I.Agent} (e : i ⟶ j) : NNRat :=
    ((P.scaled i e.val : ℚ) / (P.scaled j e.val : ℚ)).toNNRat
  have gain_eq {i j : I.Agent} (e : i ⟶ j) :
      (gain e : ℚ) = (P.scaled i e.val : ℚ) / (P.scaled j e.val : ℚ) := by
    exact Rat.coe_toNNRat _ (by positivity)
  let sources : ∀ {i j : I.Agent}, Quiver.Path i j → List P.Cell :=
    fun {i j} p => p.recOn (motive := fun {_} _ => List P.Cell) []
      (fun {b c} _ e es => es ++ [(b, e.val)])
  let targets : ∀ {i j : I.Agent}, Quiver.Path i j → List P.Cell :=
    fun {i j} p => p.recOn (motive := fun {_} _ => List P.Cell) []
      (fun {b c} _ e es => es ++ [(c, e.val)])
  have source_append {i j : I.Agent} (p : Quiver.Path i j) :
      (sources p).map Prod.fst ++ [j] = p.vertices := by
    induction p with
    | nil => rfl
    | @cons b c p e ih =>
      change (((sources p) ++ [(b, e.val)]).map Prod.fst) ++ [c] = _
      simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
        ih, Quiver.Path.vertices_cons, List.concat_eq_append]
  have target_cons {i j : I.Agent} (p : Quiver.Path i j) :
      i :: (targets p).map Prod.fst = p.vertices := by
    induction p with
    | nil => rfl
    | @cons b c p e ih =>
      change i :: ((targets p ++ [(c, e.val)]).map Prod.fst) = _
      simp only [List.map_append, List.map_cons, List.map_nil, ← List.cons_append,
        ih, Quiver.Path.vertices_cons, List.concat_eq_append]
  have source_pos {i j : I.Agent} (p : Quiver.Path i j) :
      ∀ c ∈ sources p, c ∈ P.positiveEntries := by
    induction p with
    | nil => simp [sources]
    | @cons b c p e ih =>
      change ∀ d ∈ sources p ++ [(b, e.val)], d ∈ P.positiveEntries
      simp only [List.mem_append, List.mem_singleton]
      intro d hd
      rcases hd with hd | rfl
      · exact ih d hd
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.property.2⟩
  have target_pos {i j : I.Agent} (p : Quiver.Path i j) :
      ∀ c ∈ targets p, c ∈ P.positiveEntries := by
    induction p with
    | nil => simp [targets]
    | @cons b c p e ih =>
      change ∀ d ∈ targets p ++ [(c, e.val)], d ∈ P.positiveEntries
      simp only [List.mem_append, List.mem_singleton]
      intro d hd
      rcases hd with hd | rfl
      · exact ih d hd
      · have hv : 0 < I.v c (P.keptGood e.val) := by
          simpa only [e.property.1] using owner_positive e.val
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  let ss (c : P.Cell) : ℚ := P.scaled c.1 c.2
  let pv (c : P.Cell) : ℝ := J.value c.1 (P.originalColumn c.2)
  have scaled_path {i j : I.Agent} (p : Quiver.Path i j) :
      ((p.weight gain : NNRat) : ℚ) * ((targets p).map ss).prod = ((sources p).map ss).prod := by
    induction p with
    | nil => simp [sources, targets]
    | @cons b c p e ih =>
      have he : (gain e : ℚ) * ss (c, e.val) = ss (b, e.val) := by
        rw [gain_eq]
        have hv : 0 < I.v c (P.keptGood e.val) := by
          simpa only [e.property.1] using owner_positive e.val
        exact div_mul_cancel₀ _ (scaled_positive c e.val hv).ne'
      change (((p.cons e).weight gain : NNRat) : ℚ) *
        ((targets p ++ [(c, e.val)]).map ss).prod = ((sources p ++ [(b, e.val)]).map ss).prod
      simp only [Quiver.Path.weight_cons, NNRat.coe_mul, List.map_append, List.map_cons,
        List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
      rw [mul_mul_mul_comm _ _ _ _, ih, he]
  have pert_path {i j : I.Agent} (p : Quiver.Path i j) :
      w i * ((sources p).map pv).prod ≤ w j * ((targets p).map pv).prod := by
    induction p with
    | nil => simp [sources, targets]
    | @cons b c p e ih =>
      have he : w b * pv (b, e.val) ≤ w c * pv (c, e.val) := by
        have he := hA (P.originalColumn e.val) b
        change w b * pv (b, e.val) ≤ w (owner e.val) * pv (owner e.val, e.val) at he
        simpa only [e.property.1] using he
      have hP : 0 ≤ w b * ((targets p).map pv).prod := by
        refine mul_nonneg (hw b).le (List.prod_nonneg ?_)
        intro v hv
        obtain ⟨d, _, rfl⟩ := List.mem_map.mp hv
        change 0 ≤ (J.v d.1 (P.originalColumn d.2) : ℝ)
        exact_mod_cast J.nonneg d.1 (P.originalColumn d.2)
      have hV : 0 ≤ pv (b, e.val) := by
        change 0 ≤ (J.v b (P.originalColumn e.val) : ℝ)
        exact_mod_cast J.nonneg b (P.originalColumn e.val)
      change w i * ((sources p ++ [(b, e.val)]).map pv).prod ≤
        w c * ((targets p ++ [(c, e.val)]).map pv).prod
      simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one]
      rw [← mul_assoc, ← mul_assoc]
      refine (mul_le_mul_of_nonneg_right ih hV).trans ?_
      have ht : 0 ≤ ((targets p).map pv).prod := by
        exact nonneg_of_mul_nonneg_right hP (hw b)
      have hh := mul_le_mul_of_nonneg_left he ht
      simpa only [mul_left_comm ((targets p).map pv).prod, ← mul_assoc] using hh
  have cycles {i j : I.Agent} (p : Quiver.Path i j) (e : j ⟶ i) (hsimple : p.vertices.Nodup) :
      (p.cons e).weight gain ≤ 1 := by
    let c := p.cons e
    have hSource : (sources c).map Prod.fst = p.vertices := by
      have hh := source_append c
      rw [Quiver.Path.vertices_cons, List.concat_eq_append] at hh
      exact List.append_cancel_right hh
    have hTarget : (targets c).map Prod.fst = p.vertices.tail ++ [i] := by
      have hh := target_cons c
      rw [Quiver.Path.vertices_cons, List.concat_eq_append, ← target_cons p, List.cons_append] at hh
      rw [← target_cons p]
      simpa only [List.cons.injEq, List.tail_cons, true_and] using hh
    have hTN : ((targets c).map Prod.fst).Nodup := by
      rw [hTarget, ← target_cons p, List.tail_cons, ← List.concat_eq_append, List.nodup_concat]
      rwa [← target_cons p, List.nodup_cons] at hsimple
    have hSN : (sources c).Nodup := List.Nodup.of_map Prod.fst (hSource.symm ▸ hsimple)
    have hTN' : (targets c).Nodup := List.Nodup.of_map Prod.fst hTN
    let S := (sources c).toFinset
    let T := (targets c).toFinset
    have hS : S ⊆ P.positiveEntries := fun _ hx => source_pos c _ (List.mem_toFinset.mp hx)
    have hT : T ⊆ P.positiveEntries := fun _ hx => target_pos c _ (List.mem_toFinset.mp hx)
    have hnS : S.card ≤ I.n := by
      have hh := hsimple.length_le_card
      rw [← hSource, List.length_map] at hh
      simpa only [S, List.toFinset_card_of_nodup hSN, Instance.Agent, Fintype.card_fin] using hh
    have hnT : T.card ≤ I.n := by
      have hh := hTN.length_le_card
      rw [List.length_map] at hh
      simpa only [T, List.toFinset_card_of_nodup hTN', Instance.Agent, Fintype.card_fin] using hh
    have hScaled := scaled_path c
    have hPert := (mul_le_mul_iff_of_pos_left (hw i)).mp (pert_path c)
    have hScaled' : ((c.weight gain : NNRat) : ℚ) * (P.ScaledProduct T : ℚ) = (P.ScaledProduct S : ℚ) := by
      rw [← List.prod_toFinset ss hSN, ← List.prod_toFinset ss hTN'] at hScaled
      simpa only [ScaledProduct, S, T, Nat.cast_prod, ss] using hScaled
    have hPert' : P.PerturbedProduct S ≤ P.PerturbedProduct T := by
      have he (U : Finset P.Cell) : (P.PerturbedProduct U : ℝ) = ∏ a ∈ U, pv a := by
        simp only [PerturbedProduct, Rat.cast_prod]
        rfl
      have hReal : (P.PerturbedProduct S : ℝ) ≤ (P.PerturbedProduct T : ℝ) := by
        rw [he, he, List.prod_toFinset _ hSN, List.prod_toFinset _ hTN']
        exact hPert
      exact_mod_cast hReal
    have hST : P.ScaledProduct S ≤ P.ScaledProduct T :=
      le_of_not_gt (fun ht => (P.preserves_strict_product h T S hT hS hnT hnS ht).not_ge hPert')
    have hProd : (0 : ℚ) < P.ScaledProduct T := by
      rw [ScaledProduct, Nat.cast_prod]
      exact Finset.prod_pos (fun d hd => scaled_positive d.1 d.2 (Finset.mem_filter.mp (hT hd)).2)
    change c.weight gain ≤ 1
    have hCast : ((c.weight gain : NNRat) : ℚ) ≤ 1 := by
      apply (mul_le_mul_iff_of_pos_right hProd).mp
      rw [hScaled', one_mul]
      exact_mod_cast hST
    exact_mod_cast hCast
  let V (j : I.Agent) : Set NNRat := ⋃ i : I.Agent,
    {x | ∃ p : Quiver.Path i j, p.length ≤ I.n ∧ p.weight gain = x}
  have finiteV (j : I.Agent) : (V j).Finite := by
    exact Set.finite_iUnion (fun i => DirectedPaths.finite_bounded_weights gain i j I.n)
  have one_in (j : I.Agent) : (1 : NNRat) ∈ V j := Set.mem_iUnion.mpr
    ⟨j, Quiver.Path.nil, Nat.zero_le _, by simp⟩
  have nonemptyV (j : I.Agent) : (finiteV j).toFinset.Nonempty :=
    ⟨1, (finiteV j).mem_toFinset.mpr (one_in j)⟩
  let pot (j : I.Agent) := ((finiteV j).toFinset).max' (nonemptyV j)
  have pot_mem (j : I.Agent) : pot j ∈ V j := (finiteV j).mem_toFinset.mp (Finset.max'_mem _ _)
  have max_le (j : I.Agent) (x : NNRat) (hx : x ∈ V j) : x ≤ pot j :=
    Finset.le_max' _ _ ((finiteV j).mem_toFinset.mpr hx)
  have pot_pos (j : I.Agent) : (0 : NNRat) < pot j := zero_lt_one.trans_le (max_le j 1 (one_in j))
  have edge_le {i j : I.Agent} (e : i ⟶ j) : pot i * gain e ≤ pot j := by
    obtain ⟨a, p, _, hp⟩ := Set.mem_iUnion.mp (pot_mem i)
    have lmono (x : NNRatᵒᵈ) : Monotone (x * ·) := by
      have h (a : NNRat) : Monotone (a * ·) := fun _ _ hab =>
        mul_le_mul_of_nonneg_left hab (show 0 ≤ a from zero_le)
      exact (h (OrderDual.ofDual x)).dual
    have rmono (x : NNRatᵒᵈ) : Monotone (· * x) := by
      have h (a : NNRat) : Monotone (· * a) := fun _ _ hab =>
        mul_le_mul_of_nonneg_right hab (show 0 ≤ a from zero_le)
      exact (h (OrderDual.ofDual x)).dual
    obtain ⟨q, hq, hFavor⟩ := DirectedPaths.exists_nodup_path_weight_le
      (M := NNRatᵒᵈ) (fun e => gain e) lmono rmono (fun p e hp => cycles p e hp) (p.cons e)
    have hlen : q.length ≤ I.n := by
      have hh := hq.length_le_card
      simp only [Quiver.Path.vertices_length, Fintype.card_fin] at hh
      omega
    have hqMem : q.weight gain ∈ V j := Set.mem_iUnion.mpr ⟨a, q, hlen, rfl⟩
    have hEq : (p.cons e).weight gain = pot i * gain e := by
      rw [Quiver.Path.weight_cons, hp]
    exact (hEq ▸ (show (p.cons e).weight gain ≤ q.weight gain from hFavor)).trans (max_le _ _ hqMem)
  let q (i : I.Agent) : ℚ := (pot i : ℚ) * P.rowFactor i
  have hq (i : I.Agent) : 0 < q i := mul_pos (by exact_mod_cast pot_pos i) (by exact_mod_cast P.rowFactor_pos i)
  have compare (i j : I.Agent) (g : I.Good)
      (h : q i * I.v i g ≤ q j * I.v j g) :
      I.bid (fun k => (q k : ℝ)) i g ≤ I.bid (fun k => (q k : ℝ)) j g := by
    change (q i : ℝ) * (I.v i g : ℝ) ≤ (q j : ℝ) * (I.v j g : ℝ)
    exact_mod_cast h
  refine ⟨q, ?_, ?_⟩
  · intro i
    change 0 < (q i : ℝ)
    exact_mod_cast hq i
  intro g i
  by_cases hKept : ∃ k, P.keptGood k = g
  · obtain ⟨k, rfl⟩ := hKept
    have hOwn : B (P.keptGood k) = owner k := hB.1 k
    rw [hOwn]
    by_cases hi : 0 < I.v i (P.keptGood k)
    · let e : i ⟶ owner k := ⟨k, rfl, hi⟩
      have hh := edge_le e
      have hh' : (pot i : ℚ) * (gain e : ℚ) ≤ (pot (owner k) : ℚ) := by exact_mod_cast hh
      rw [gain_eq, ← mul_div_assoc] at hh'
      have hRat : q i * I.v i (P.keptGood k) ≤ q (owner k) * I.v (owner k) (P.keptGood k) := by
        dsimp [q]
        rw [mul_assoc, mul_assoc, ← P.scaled_eq_rowFactor_mul, ← P.scaled_eq_rowFactor_mul]
        exact (div_le_iff₀ (scaled_positive (owner k) k (owner_positive k))).mp hh'
      exact compare _ _ _ hRat
    · have hi0 : I.v i (P.keptGood k) = 0 := le_antisymm (le_of_not_gt hi) (I.nonneg i _)
      have hRat : q i * I.v i (P.keptGood k) ≤ q (owner k) * I.v (owner k) (P.keptGood k) := by
        rw [hi0, mul_zero]
        exact mul_nonneg (hq _).le (I.nonneg _ _)
      exact compare _ _ _ hRat
  · have hZero (i : I.Agent) : I.v i g = 0 := by
      refine le_antisymm (le_of_not_gt (fun hi => hKept ((h.2.1 g).2 ⟨i, hi⟩))) (I.nonneg i g)
    have hRat : q i * I.v i g ≤ q (B g) * I.v (B g) g := by simp only [hZero, mul_zero, le_refl]
    exact compare _ _ _ hRat

theorem prepared_forest (h : P.IsPreparation) (w : P.prepared.Weights)
    (hw : P.prepared.Positive w) : P.prepared.IsForest w := by
  intro v p hp
  obtain ⟨S, T, hS, hT, hnS, hnT, hne, heq⟩ := P.alternating_cells_of_cycle h w hw v p hp
  exact P.separates_product_sets h S T hS hT hnS hnT hne heq

theorem prepared_cap_covers (h : P.IsPreparation) : P.prepared.Covers P.prepared.cap := by
  classical
  let J := P.prepared
  choose A hA using (J.exists_highest_bidder J.cap)
  refine ⟨A, hA, ?_⟩
  intro agent
  let i : I.Agent := agent
  let g := P.auxiliaryColumn i
  have hi : J.bid J.cap i g = 1 := by
    have hVal : P.v i (P.auxiliaryColumn i) = 1 / 4 :=
      (h.2.2.2 i i).trans (if_pos rfl)
    change (4 : ℝ) * (P.v i (P.auxiliaryColumn i) : ℝ) = 1
    rw [hVal]
    norm_num
  have hOwner : A g = i := by
    by_contra hNe
    let a : I.Agent := A g
    have ha : a ≠ i := hNe
    have hVal : P.v a (P.auxiliaryColumn i) = 0 :=
      (h.2.2.2 a i).trans (if_neg ha)
    have hOther : J.bid J.cap (A g) g = 0 := by
      change (4 : ℝ) * (P.v a (P.auxiliaryColumn i) : ℝ) = 0
      rw [hVal]
      norm_num
    have hCompare := hA g i
    rw [hi, hOther] at hCompare
    norm_num at hCompare
  have hMem : g ∈ FairDivision.bundle A i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ g, hOwner⟩
  have hCap : J.Positive J.cap := fun _ => by norm_num [Instance.cap]
  exact (hi ▸ J.bid_le_price J.cap i g).trans
    (Finset.single_le_sum (f := J.price J.cap) (fun g _ => J.price_nonneg J.cap hCap g) hMem)

theorem recover_allocation (h : P.IsPreparation) (A : P.prepared.Allocation)
    (hEF1 : P.prepared.IsEF1 A) (w : P.prepared.Weights) (hw : P.prepared.Positive w)
    (hSupport : P.prepared.IsSupported w A) :
    ∃ (B : I.Allocation) (q : I.Agent → ℚ), P.IsRecoveredAllocation A B ∧ I.IsEF1 B ∧
      I.Positive (fun i => (q i : ℝ)) ∧ I.IsSupported (fun i => (q i : ℝ)) B := by
  obtain ⟨B, hB, hFair⟩ := P.recover_ef1_only h A hEF1 w hw hSupport
  obtain ⟨q, hPos, hBid⟩ := P.recovered_allocation_positive_support h A w hw hSupport B hB
  exact ⟨B, q, hB, hFair, hPos, hBid⟩

end Preparation

end EF1FPO
