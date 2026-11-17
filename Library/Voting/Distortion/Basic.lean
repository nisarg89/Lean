import Voting.Stable.Basic

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable

namespace MetricDistortion

abbrev Metric (n m : ℕ) := PseudoMetricSpace (Fin n ⊕ Fin m)

def distance {n m : ℕ} (d : Metric n m) : (Fin n ⊕ Fin m) → (Fin n ⊕ Fin m) → ℝ :=
  @dist _ d.toDist

def Consistent {n m : ℕ} (σ : Profile n m) (d : Metric n m) : Prop :=
  ∀ v a b, prefers (σ v) a b → distance d (.inl v) (.inr a) ≤ distance d (.inl v) (.inr b)

def sc {n m : ℕ} (d : Metric n m) (c : Fin m) : ℝ := avg fun v => distance d (.inl v) (.inr c)

def expectedCost {n m : ℕ} (d : Metric n m) (P : Lottery m) : ℝ := ∑ c, P.val c * sc d c

def optimum {n m : ℕ} (d : Metric n m) : ℝ := sInf (Set.range (sc d))

def Optimal {n m : ℕ} (d : Metric n m) (o : Fin m) : Prop := ∀ c, sc d o ≤ sc d c

def ratio (a b : ℝ) : ℝ≥0∞ :=
  if b = 0 then (if a = 0 then 1 else ⊤) else ENNReal.ofReal (a/b)

def distortion {n m : ℕ} (σ : Profile n m) (P : Lottery m) : ℝ≥0∞ :=
  ⨆ d : {d : Metric n m // Consistent σ d}, ratio (expectedCost d.val P) (optimum d.val)

def marked {n m : ℕ} (d : Metric n m) (o : Fin m) (t : ℝ) : Set (Fin m) :=
  {c | t < distance d (.inr o) (.inr c)}

def lowerCut {n m : ℕ} (σ : Profile n m) (P : Lottery m) (d : Metric n m)
    (o : Fin m) (v : Fin n) (t : ℝ) : ℝ :=
  sInf {a | ∃ c, c ∉ marked d o t ∧ a = below (σ v) P c}

def upperCut {n m : ℕ} (σ : Profile n m) (P : Lottery m) (d : Metric n m)
    (o : Fin m) (v : Fin n) (t : ℝ) : ℝ :=
  if ∃ c, c ∈ marked d o t ∧ 0 < P.val c then
    sSup {a | ∃ c, c ∈ marked d o t ∧ 0 < P.val c ∧ a = below (σ v) P c + P.val c}
  else 0

def crossing {n m : ℕ} (σ : Profile n m) (P : Lottery m) (d : Metric n m)
    (o : Fin m) (v : Fin n) (q : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ lowerCut σ P d o v t ≤ q ∧ q < upperCut σ P d o v t}

def indicator (S : Set ℝ) : ℝ → ℝ := S.indicator (fun _ => 1)

def tailIntegral (f : ℝ → ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), f t

structure CutParameters where
  C0 : ℝ
  b : ℝ
  lambda : ℝ → ℝ
  tau : Fin 9 → ℝ → ℝ
  roots : Fin 9 → Set ℝ
  nu : Fin 9 → Measure ℝ

def LocalCut (D : DrawLaw) (w : CutParameters) (j : Fin 9) (a p A r : ℝ) : Prop :=
  a + w.lambda p * (Phi D a + Phi D A - Phi D (a+A-p) - p*mu D) +
    w.tau j p * (mu D - phi D r) ≤
      (w.nu j {z | z ∈ Icc (0 : ℝ) 1 ∧ a ≤ min z r ∧ min z r < A}).toReal

def ValidCut (D : DrawLaw) (w : CutParameters) : Prop :=
  0 ≤ w.C0 ∧ w.b ∈ Icc (0 : ℝ) 1 ∧ phi D w.b ≤ mu D ∧
  (∀ p ∈ Icc (0 : ℝ) 1, 0 ≤ w.lambda p) ∧ w.lambda 0 = 0 ∧ w.lambda 1 = 0 ∧
  (∀ j, IsClosed (w.roots j) ∧ OrdConnected (w.roots j) ∧ w.roots j ⊆ Icc 0 w.b) ∧
  (Icc 0 w.b ⊆ ⋃ j, w.roots j) ∧
  (∀ j, w.nu j (Icc (0 : ℝ) 1) = ENNReal.ofReal w.C0 ∧ w.nu j (Icc (0 : ℝ) 1)ᶜ = 0) ∧
  (∀ j, ∀ p ∈ Icc (0 : ℝ) 1, 0 ≤ w.tau j p) ∧ (∀ j, w.tau j 0 = 0) ∧
  (∀ j r, r ∈ w.roots j ∪ Icc w.b 1 →
    ∀ a p A, 0 ≤ a → a ≤ min p r → p ≤ A → A ≤ 1 → LocalCut D w j a p A r)

def sOffset {m : ℕ} (r : Ranking m) (x : Fin m → ℝ) (c : Fin m) : ℝ :=
  sInf {t | ∃ j, r j ≤ r c ∧ t = x j}

def deltaOffset {m : ℕ} (r : Ranking m) (x : Fin m → ℝ) : ℝ :=
  sSup {t | ∃ i j, r j ≤ r i ∧ t = x i - x j}

def loss {n m : ℕ} (σ : Profile n m) (P : Lottery m) (x : Fin m → ℝ) : ℝ :=
  avg fun v => ∑ c, P.val c * sOffset (σ v) x c

def scale {n m : ℕ} (σ : Profile n m) (x : Fin m → ℝ) : ℝ := avg fun v => deltaOffset (σ v) x

def offsetRatio (L S : ℝ) : ℝ≥0∞ :=
  1 + 2 * (if S = 0 then (if L = 0 then 0 else ⊤) else ENNReal.ofReal (L/S))

end MetricDistortion
