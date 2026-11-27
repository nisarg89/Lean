import FairDivision.Definitions

/-! The allocation model and economic predicates for EF1 and fractional Pareto optimality. -/

set_option autoImplicit false

open scoped BigOperators

namespace EF1FPO

/-- A finite rational instance with at least one agent. -/
structure Instance where
  n : ℕ
  m : ℕ
  hn : 0 < n
  v : Fin n → Fin m → ℚ
  nonneg : ∀ i g, 0 ≤ v i g

namespace Instance

abbrev Agent (I : Instance) := Fin I.n
abbrev Good (I : Instance) := Fin I.m
abbrev Allocation (I : Instance) := FairDivision.Allocation I.n I.m
abbrev Weights (I : Instance) := I.Agent → ℝ
abbrev Shares (I : Instance) := I.Agent → I.Good → ℝ

abbrev value (I : Instance) (i : I.Agent) (g : I.Good) : ℝ := (I.v i g : ℝ)

abbrev utility (I : Instance) (i : I.Agent) (S : Finset I.Good) : ℝ :=
  FairDivision.additiveValue I.value i S

abbrev fractionalUtility (I : Instance) (x : I.Shares) (i : I.Agent) : ℝ :=
  FairDivision.fractionalValue I.value x i

/-- Fractional competitors may assign any nonnegative shares that exhaust each good. -/
def IsFractional (I : Instance) (x : I.Shares) : Prop :=
  (∀ i g, 0 ≤ x i g) ∧ ∀ g, ∑ i, x i g = 1

/-- EF1 requires an actual deletion for each nonempty compared bundle. -/
def IsEF1 (I : Instance) (A : I.Allocation) : Prop :=
  ∀ i j, (FairDivision.bundle A j).Nonempty →
    ∃ g ∈ FairDivision.bundle A j,
      I.utility i ((FairDivision.bundle A j).erase g) ≤
        I.utility i (FairDivision.bundle A i)

/-- fPO rules out every improving complete fractional allocation. -/
def IsFPO (I : Instance) (A : I.Allocation) : Prop :=
  ∀ x : I.Shares, I.IsFractional x →
    ¬ ((∀ i, I.utility i (FairDivision.bundle A i) ≤ I.fractionalUtility x i) ∧
      ∃ i, I.utility i (FairDivision.bundle A i) < I.fractionalUtility x i)

def Positive (I : Instance) (w : I.Weights) : Prop := ∀ i, 0 < w i

def bid (I : Instance) (w : I.Weights) (i : I.Agent) (g : I.Good) : ℝ :=
  w i * I.value i g

noncomputable def price (I : Instance) (w : I.Weights) (g : I.Good) : ℝ :=
  Finset.univ.sup' ⟨⟨0, I.hn⟩, Finset.mem_univ _⟩ (fun i => I.bid w i g)

def IsHighestBidder (I : Instance) (w : I.Weights) (i : I.Agent) (g : I.Good) : Prop :=
  ∀ j, I.bid w j g ≤ I.bid w i g

def IsSupported (I : Instance) (w : I.Weights) (A : I.Allocation) : Prop :=
  ∀ g, I.IsHighestBidder w (A g) g

noncomputable def bundlePrice (I : Instance) (w : I.Weights) (S : Finset I.Good) : ℝ :=
  ∑ g ∈ S, I.price w g

/-- Remove a most expensive good for the purpose of computing spending. -/
noncomputable def trim (I : Instance) (w : I.Weights) (S : Finset I.Good) : ℝ := by
  classical
  exact if h : S.Nonempty then I.bundlePrice w S - S.sup' h (I.price w) else 0

def LowerBand (I : Instance) (w : I.Weights) (A : I.Allocation) (τ : ℝ) : Prop :=
  ∀ i, τ ≤ I.bundlePrice w (FairDivision.bundle A i)

def UpperBand (I : Instance) (w : I.Weights) (A : I.Allocation) (τ : ℝ) : Prop :=
  ∀ i, I.trim w (FairDivision.bundle A i) ≤ τ

def Bands (I : Instance) (w : I.Weights) (A : I.Allocation) (τ : ℝ) : Prop :=
  I.LowerBand w A τ ∧ I.UpperBand w A τ

def Covers (I : Instance) (w : I.Weights) : Prop :=
  ∃ A : I.Allocation, I.IsSupported w A ∧ I.LowerBand w A 1

/-- The undirected incidence graph of agents and goods where the agent is a highest bidder. -/
def highestBidderGraph (I : Instance) (w : I.Weights) : SimpleGraph (I.Agent ⊕ I.Good) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | Sum.inl i, Sum.inr g => I.IsHighestBidder w i g
    | _, _ => False)

def IsForest (I : Instance) (w : I.Weights) : Prop := (I.highestBidderGraph w).IsAcyclic

/-- The goods an agent wins strictly against every rival. -/
noncomputable def forcedGoods (I : Instance) (w : I.Weights) (i : I.Agent) : Finset I.Good := by
  classical
  exact Finset.univ.filter (fun g => ∀ j, j ≠ i → I.bid w j g < I.bid w i g)

def ForcedFeasible (I : Instance) (w : I.Weights) : Prop :=
  ∀ i, I.bundlePrice w (I.forcedGoods w i) ≤ 1

def IsFeasible (I : Instance) (u w : I.Weights) : Prop :=
  I.Positive w ∧ w ≤ u ∧ I.ForcedFeasible w

def IsGreatestFeasible (I : Instance) (u w : I.Weights) : Prop :=
  IsGreatest {a | I.IsFeasible u a} w

def cap (I : Instance) : I.Weights := fun _ => 4

end Instance

end EF1FPO
