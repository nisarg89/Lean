import Voting.Basic

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable

namespace MetricDistortion

abbrev DrawLaw := PMF ℕ -- index k represents the positive draw count k+1

def drawWeight (D : DrawLaw) (k : ℕ) : ℝ := (D k).toReal

def phi (D : DrawLaw) (t : ℝ) : ℝ := ∑' k, drawWeight D k * t^(k+1)

def Phi (D : DrawLaw) (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, phi D u

def mu (D : DrawLaw) : ℝ := ∑' k, drawWeight D k / (k+2 : ℕ)

def fixedCompare {m : ℕ} (r : Ranking m) (P : Lottery m) (c : Fin m) (k : ℕ) : ℝ :=
  ∑ xs : Fin k → Fin m, (∏ i, P.val (xs i)) *
    if ∀ i, r (xs i) ≤ r c then
      1 / (1 + ((Finset.univ.filter fun i => xs i = c).card : ℝ)) else 0

def compare {m : ℕ} (D : DrawLaw) (r : Ranking m) (P : Lottery m) (c : Fin m) : ℝ :=
  ∑' k, drawWeight D k * fixedCompare r P c (k+1)

def score {n m : ℕ} (D : DrawLaw) (σ : Profile n m) (P : Lottery m) (c : Fin m) : ℝ :=
  avg fun v => compare D (σ v) P c

def Stable {n m : ℕ} (D : DrawLaw) (σ : Profile n m) (P : Lottery m) : Prop :=
  ∀ c, score D σ P c ≤ mu D

def ApproxStable {n m : ℕ} (D : DrawLaw) (σ : Profile n m) (P : Lottery m) (δ : ℝ) : Prop :=
  ∀ c, score D σ P c ≤ mu D + δ

def payoff {n m : ℕ} (D : DrawLaw) (σ : Profile n m) (A P : Lottery m) : ℝ :=
  ∑ c, A.val c * score D σ P c

def ambientCompare {m : ℕ} (D : DrawLaw) (r : Ranking m) (p : Fin m → ℝ) (c : Fin m) : ℝ :=
  ∫ s in (0 : ℝ)..1, phi D ((∑ j, if prefers r c j then p j else 0)+s*p c)

def ambientScore {n m : ℕ} (D : DrawLaw) (σ : Profile n m) (p : Fin m → ℝ) (c : Fin m) : ℝ :=
  avg fun v => ambientCompare D (σ v) p c

end MetricDistortion
