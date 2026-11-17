import FairDivision.Definitions
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Worst and best q-item completions from the replacement-fairness appendix

The original valuation is defined ONLY on q-item bundles. The worst-completion
extension uses the minimum over containing q-bundles below size q and the
global maximum above size q. The best-completion extension reverses min/max.
The attained extrema and monotonicity are exactly the manuscript argument.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.ReplacementFairness

open scoped Classical

/-- A bundle on which the manuscript's original valuation is specified. -/
abbrev QBundle (m q : ℕ) := {B : Finset (Fin m) // B.card = q}

instance (m q : ℕ) : Fintype (QBundle m q) := Fintype.ofFinite _

/-- All q-item completions of the displayed partial bundle. -/
def completions {m : ℕ} (q : ℕ) (S : Finset (Fin m)) : Finset (QBundle m q) :=
  Finset.univ.filter fun T => S ⊆ T.1

@[simp] theorem mem_completions {m q : ℕ} (S : Finset (Fin m)) (T : QBundle m q) :
    T ∈ completions q S ↔ S ⊆ T.1 := by simp [completions]

theorem completions_nonempty {m q : ℕ} (hqm : q ≤ m)
    (S : Finset (Fin m)) (hS : S.card ≤ q) : (completions q S).Nonempty := by
  obtain ⟨T,hST,hT⟩:=Finset.exists_superset_card_eq hS (by simpa using hqm)
  exact ⟨⟨T,hT⟩,(mem_completions S ⟨T,hT⟩).2 hST⟩

theorem qBundles_nonempty {m q : ℕ} (hqm : q ≤ m) :
    (Finset.univ : Finset (QBundle m q)).Nonempty := by
  obtain ⟨T,hT⟩:=completions_nonempty hqm ∅ (by simp)
  exact ⟨T,Finset.mem_univ _⟩

theorem completions_antitone {m q : ℕ} {S T : Finset (Fin m)} (hST : S ⊆ T) :
    completions q T ⊆ completions q S := by
  intro U hU
  exact (mem_completions S U).2 (hST.trans ((mem_completions T U).1 hU))

/-- A full q-bundle has exactly itself as a completion. -/
theorem completions_full {m q : ℕ} (S : QBundle m q) :
    completions q S.1={S} := by
  ext T
  simp only [mem_completions,Finset.mem_singleton]
  constructor
  · intro hST
    apply Subtype.ext
    exact (Finset.eq_of_subset_of_card_le hST (by rw [T.2,S.2])).symm
  · rintro rfl
    exact Finset.Subset.refl _

/-- The manuscript's nondecreasing worst-completion extension. -/
def worstExtension {m q : ℕ} (hqm : q ≤ m) (v : QBundle m q → ℝ)
    (S : Finset (Fin m)) : ℝ :=
  if hS : S.card ≤ q then (completions q S).inf' (completions_nonempty hqm S hS) v
  else (Finset.univ : Finset (QBundle m q)).sup' (qBundles_nonempty hqm) v

/-- The manuscript's nonincreasing best-completion extension. -/
def bestExtension {m q : ℕ} (hqm : q ≤ m) (v : QBundle m q → ℝ)
    (S : Finset (Fin m)) : ℝ :=
  if hS : S.card ≤ q then (completions q S).sup' (completions_nonempty hqm S hS) v
  else (Finset.univ : Finset (QBundle m q)).inf' (qBundles_nonempty hqm) v

@[simp] theorem worstExtension_full {m q : ℕ} (hqm : q ≤ m)
    (v : QBundle m q → ℝ) (S : QBundle m q) : worstExtension hqm v S.1=v S := by
  have hS : S.1.card ≤ q := S.2.le
  unfold worstExtension
  rw [dif_pos hS]
  apply Finset.inf'_eq_of_forall
  intro T hT
  rw [completions_full S] at hT
  exact congrArg v (Finset.mem_singleton.mp hT)

@[simp] theorem bestExtension_full {m q : ℕ} (hqm : q ≤ m)
    (v : QBundle m q → ℝ) (S : QBundle m q) : bestExtension hqm v S.1=v S := by
  have hS : S.1.card ≤ q := S.2.le
  unfold bestExtension
  rw [dif_pos hS]
  apply Finset.sup'_eq_of_forall
  intro T hT
  rw [completions_full S] at hT
  exact congrArg v (Finset.mem_singleton.mp hT)

theorem worstExtension_attained {m q : ℕ} (hqm : q ≤ m)
    (v : QBundle m q → ℝ) (S : Finset (Fin m)) (hS : S.card ≤ q) :
    ∃T : QBundle m q,S ⊆ T.1 ∧ worstExtension hqm v S=v T := by
  obtain ⟨T,hT,hValue⟩:=Finset.exists_mem_eq_inf' (completions_nonempty hqm S hS) v
  exact ⟨T,(mem_completions S T).1 hT,by simpa [worstExtension,hS] using hValue⟩

theorem bestExtension_attained {m q : ℕ} (hqm : q ≤ m)
    (v : QBundle m q → ℝ) (S : Finset (Fin m)) (hS : S.card ≤ q) :
    ∃T : QBundle m q,S ⊆ T.1 ∧ bestExtension hqm v S=v T := by
  obtain ⟨T,hT,hValue⟩:=Finset.exists_mem_eq_sup' (completions_nonempty hqm S hS) v
  exact ⟨T,(mem_completions S T).1 hT,by simpa [bestExtension,hS] using hValue⟩

/-- Enlarging an incomplete bundle restricts its completion family. Above
size q the chosen constant is at least every original q-bundle value. -/
theorem worstExtension_monotone {m q : ℕ} (hqm : q ≤ m) (v : QBundle m q → ℝ) :
    Monotone (worstExtension hqm v) := by
  intro S T hST
  by_cases hT : T.card ≤ q
  · have hS : S.card ≤ q:=(Finset.card_le_card hST).trans hT
    simp only [worstExtension,dif_pos hS,dif_pos hT]
    exact Finset.le_inf' (completions_nonempty hqm T hT) v
      (fun U hU => Finset.inf'_le v ((completions_antitone hST) hU))
  · by_cases hS : S.card ≤ q
    · obtain ⟨U,hU,hValue⟩:=worstExtension_attained hqm v S hS
      rw [hValue]
      simp only [worstExtension,dif_neg hT]
      exact Finset.le_sup' v (Finset.mem_univ U)
    · simp [worstExtension,hS,hT]

/-- The dual completion argument: best completions can only decrease as a
partial set is enlarged; above size q the global minimum is used. -/
theorem bestExtension_antitone {m q : ℕ} (hqm : q ≤ m) (v : QBundle m q → ℝ) :
    Antitone (bestExtension hqm v) := by
  intro S T hST
  by_cases hT : T.card ≤ q
  · have hS : S.card ≤ q:=(Finset.card_le_card hST).trans hT
    simp only [bestExtension,dif_pos hS,dif_pos hT]
    exact Finset.sup'_le (completions_nonempty hqm T hT) v
      (fun U hU => Finset.le_sup' v ((completions_antitone hST) hU))
  · by_cases hS : S.card ≤ q
    · obtain ⟨U,hU,hValue⟩:=bestExtension_attained hqm v S hS
      rw [hValue]
      simp only [bestExtension,dif_neg hT]
      exact Finset.inf'_le v (Finset.mem_univ U)
    · simp [bestExtension,hS,hT]

/-- A q-completion of a q−1 set differs by exactly one fresh item. This is
Mathlib's existing finite-set one-element extension theorem. -/
theorem completion_of_erase {m q : ℕ} (B : QBundle m q) (b : Fin m) (hb : b ∈ B.1)
    (T : QBundle m q) (hT : B.1.erase b ⊆ T.1) :
    ∃g∉B.1.erase b,insert g (B.1.erase b)=T.1 := by
  apply Finset.exists_eq_insert_iff.mpr
  refine ⟨hT,?_⟩
  rw [Finset.card_erase_of_mem hb,T.2,B.2]
  have hq : 0<q := by rw [←B.2]; exact Finset.card_pos.mpr ⟨b,hb⟩
  omega

end FairDivision.BF.ReplacementFairness
