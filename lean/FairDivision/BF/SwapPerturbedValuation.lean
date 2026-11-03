import FairDivision.BF.SwapDefinitions

/-!
# The manuscript's concave-cardinality valuation with q-layer noise

The literal baseline is (2m+1)|S|−|S|². Independent continuous uniform
weights enter only on q-item sets. This file proves the deterministic
claims for EVERY realization with weights in [0,1): normalization, strict
monotonicity, submodularity and EFX of every equal-q allocation. The later
probabilistic argument only has to choose a realization without a t-swap
allocation; it does not need to repeat any valuation proof.
-/

set_option autoImplicit false

namespace FairDivision.BF.SwapPerturbedValuation

open FairDivision.BF

variable {m q : ℕ}

/-- Exactly the baseline polynomial in Section 7. -/
def base (m : ℕ) (S : Finset (Fin m)) : ℝ :=(2*(m : ℝ)+1)*S.card-(S.card : ℝ)^2

def noise (q : ℕ) (W : Finset (Fin m)→ℝ) (S : Finset (Fin m)) : ℝ :=
  if S.card=q then W S else 0

def value (q : ℕ) (W : Finset (Fin m)→ℝ) (S : Finset (Fin m)) : ℝ :=
  base m S+noise q W S

theorem noise_bounds (W : Finset (Fin m)→ℝ)
    (hW : ∀S,0≤W S ∧W S<1) (S : Finset (Fin m)) :
    0≤noise q W S ∧noise q W S<1 := by
  unfold noise
  split_ifs
  · exact hW S
  · norm_num

/-- Normalization uses only q>0, as in the stated negative regime. -/
theorem normalized (hq : 0<q) (W : Finset (Fin m)→ℝ) : IsNormalized (value q W) := by
  simp [IsNormalized,value,base,noise,ne_of_lt hq]

/-- The baseline increases by exactly 2(m−|S|) on adding a fresh item. -/
theorem base_insert (S : Finset (Fin m)) (g : Fin m) (hg : g∉S) :
    base m (insert g S)-base m S=2*((m : ℝ)-S.card) := by
  rw [base,base,Finset.card_insert_of_notMem hg]
  push_cast
  ring

/-- Every fresh item increases the perturbed value by MORE than one. -/
theorem insert_gap (W : Finset (Fin m)→ℝ)
    (hW : ∀S,0≤W S ∧W S<1) (S : Finset (Fin m)) (g : Fin m) (hg : g∉S) :
    1<value q W (insert g S)-value q W S := by
  have hBound : (insert g S).card ≤ m := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (insert g S))
  rw [Finset.card_insert_of_notMem hg] at hBound
  have hNat : S.card + 1 ≤ m := hBound
  have hReal : (S.card : ℝ) + 1 ≤ m := by exact_mod_cast hNat
  have hOld:=(noise_bounds (q:=q) W hW S).2
  have hNew:=(noise_bounds (q:=q) W hW (insert g S)).1
  have hBase:=base_insert S g hg
  unfold value
  linarith

/-- Strict monotonicity is Mathlib's existing fresh-insertion criterion. -/
theorem strictly_monotone (W : Finset (Fin m)→ℝ)
    (hW : ∀S,0≤W S ∧W S<1) : StrictMono (value q W) := by
  classical
  apply Finset.strictMono_iff_forall_lt_insert.mpr
  intro S g hg
  have h:=insert_gap (q:=q) W hW S g hg
  linarith

/-- The baseline submodular defect is exactly twice the product of the
two asymmetric differences. This is the manuscript's r,a,b calculation. -/
theorem base_submodular_defect (S T : Finset (Fin m)) :
    base m S+base m T-base m (S∪T)-base m (S∩T)=
      2*((S\T).card : ℝ)*(T\S).card := by
  have hS:=Finset.card_sdiff_add_card_inter S T
  have hT:=Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at hT
  have hUnion:=Finset.card_union_add_card_inter S T
  have hSC : S.card=(S∩T).card+(S\T).card:=by omega
  have hTC : T.card=(S∩T).card+(T\S).card:=by omega
  have hUC : (S∪T).card=(S∩T).card+(S\T).card+(T\S).card:=by omega
  simp only [base,hSC,hTC,hUC]
  push_cast
  ring

/-- Every bounded realization has the exact submodular property. -/
theorem submodular (W : Finset (Fin m)→ℝ)
    (hW : ∀S,0≤W S ∧W S<1) : IsBundleSubmodular (value q W) := by
  classical
  intro S T
  by_cases hST:S⊆T
  · simp only [Finset.union_eq_right.mpr hST,Finset.inter_eq_left.mpr hST]
    exact le_of_eq (add_comm _ _)
  by_cases hTS:T⊆S
  · simp only [Finset.union_eq_left.mpr hTS,Finset.inter_eq_right.mpr hTS]
    exact le_rfl
  have hA : 1≤(S\T).card:=Finset.card_pos.mpr (Finset.sdiff_nonempty.mpr hST)
  have hB : 1≤(T\S).card:=Finset.card_pos.mpr (Finset.sdiff_nonempty.mpr hTS)
  have hAR : (1 : ℝ)≤(S\T).card:=by exact_mod_cast hA
  have hBR : (1 : ℝ)≤(T\S).card:=by exact_mod_cast hB
  have hProduct : (1 : ℝ)≤((S\T).card : ℝ)*(T\S).card := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAR) (sub_nonneg.mpr hBR)]
  have hBase:=base_submodular_defect S T
  have hSNoise:=(noise_bounds (q:=q) W hW S).1
  have hTNoise:=(noise_bounds (q:=q) W hW T).1
  have hUnionNoise:=(noise_bounds (q:=q) W hW (S∪T)).2
  have hInterNoise:=(noise_bounds (q:=q) W hW (S∩T)).2
  unfold value
  nlinarith

/-- On one cardinality layer the baseline cancels, leaving exactly the
same comparisons as the corresponding random weights. -/
theorem comparison_on_layer (W : Finset (Fin m)→ℝ) (S T : Finset (Fin m))
    (hS : S.card=q) (hT : T.card=q) :
    value q W S<value q W T ↔ W S<W T := by
  simp only [value,noise,hS,hT,if_true,base]
  exact add_lt_add_iff_left _

theorem layer_difference_lt_one (W : Finset (Fin m)→ℝ)
    (hW : ∀S,0≤W S ∧W S<1) (S T : Finset (Fin m))
    (hS : S.card=q) (hT : T.card=q) : value q W S<value q W T+1 := by
  have h₁:=(hW S).2
  have h₂:=(hW T).1
  simp only [value,noise,hS,hT,if_true,base]
  linarith

/-- Every equal-q allocation in the negative construction is EFX, with
strict inequalities whenever an item can actually be deleted. -/
theorem every_equal_allocation_EFX {n : ℕ}
    (W : Finset (Fin m)→ℝ) (hW : ∀S,0≤W S ∧W S<1)
    (A : Allocation n m) (hSize : HasEqualBundleSize A q) :
    IsBundleEFX (fun _=>value q W) A := by
  intro i j g hg
  have hFresh : g∉(bundle A j).erase g:=Finset.notMem_erase g _
  have hGap:=insert_gap (q:=q) W hW ((bundle A j).erase g) g hFresh
  rw [Finset.insert_erase hg] at hGap
  have hClose:=layer_difference_lt_one W hW (bundle A j) (bundle A i)
    (hSize j) (hSize i)
  linarith

end FairDivision.BF.SwapPerturbedValuation
