import Mathlib

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable

namespace MetricDistortion

abbrev Ranking (m : ℕ) := Equiv.Perm (Fin m)

abbrev Profile (n m : ℕ) := Fin n → Ranking m

abbrev Lottery (m : ℕ) := {p : Fin m → ℝ // (∀ c, 0 ≤ p c) ∧ ∑ c, p c = 1}

def avg {n : ℕ} (f : Fin n → ℝ) : ℝ := (∑ v, f v) / n

def prefers {m : ℕ} (r : Ranking m) (a b : Fin m) : Prop := r b < r a

def mass {m : ℕ} (P : Lottery m) (H : Set (Fin m)) : ℝ :=
  ∑ c, if c ∈ H then P.val c else 0

def below {m : ℕ} (r : Ranking m) (P : Lottery m) (c : Fin m) : ℝ :=
  mass P {j | prefers r c j}

def block {m : ℕ} (r : Ranking m) (P : Lottery m) (c : Fin m) : Set ℝ :=
  Ico (below r P c) (below r P c + P.val c)

def region {m : ℕ} (r : Ranking m) (P : Lottery m) (H : Set (Fin m)) : Set ℝ :=
  ⋃ c ∈ H, block r P c

def labelWin (r s : ℕ) : ℝ :=
  ((Measure.pi fun _ : Fin (r+s) => volume.restrict (Icc (0 : ℝ) 1))
    {x | ∃ i : Fin (r+s), i.val < r ∧ ∀ j, j ≠ i → x j < x i}).toReal

def simplex (m : ℕ) : Set (Fin m → ℝ) := {p | (∀ c, 0 ≤ p c) ∧ ∑ c, p c = 1}

abbrev VotingRule := ∀ (n m : ℕ), 0 < n → 0 < m → Profile n m → Lottery m

end MetricDistortion
