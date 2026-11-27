import FairDivision.Definitions
import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding

/-! Independent statement for the binary polynomial-time allocation theorem. -/

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

end Instance

open OAI.Optimization.LinearProgramming.OracleSpec

/-- All natural fields and rational components use the upstream framed binary encoding.
Both sets of indices are explicitly listed, including when the table has no columns. -/
def encodeInstance (I : Instance) : Word :=
  encodeNat I.n ++ encodeNat I.m ++
    (List.ofFn (fun i : I.Agent => i.val)).flatMap encodeNat ++
    (List.ofFn (fun g : I.Good => g.val)).flatMap encodeNat ++
    (List.ofFn (fun i : I.Agent => List.ofFn (I.v i))).flatten.flatMap encodeRat

def encodeAllocation {I : Instance} (A : I.Allocation) : Word :=
  encodeNat I.n ++ encodeNat I.m ++ (List.ofFn (fun g : I.Good => (A g).val)).flatMap encodeNat

/-- A closed execution accepts no external information. Every `ask` would create a
permanent transcript entry and violate the empty-transcript postcondition. -/
def ClosedComputesWithin (M : BitProgram) (input : Word) (time : ℕ)
    (post : Word → Prop) : Prop :=
  M.ComputesWithin (fun _ _ => []) input time (fun history output => history = [] ∧ post output)

/-- Program and clock are quantified before inputs. The cost is ordinary binary bit time. -/
def BitPolynomial {X : Type} (input : X → Word) (post : X → Word → Prop) : Prop :=
  ∃ (M : BitProgram) (C d : ℕ), ∀ x : X,
    ClosedComputesWithin M (input x) (C * ((input x).length + 1) ^ d) (post x)

/-- One fixed deterministic finite-alphabet program returns a complete EF1 and fPO
allocation at the original rational valuations, with one polynomial in the full binary input. -/
theorem ef1_fpo_polynomial : BitPolynomial encodeInstance (fun I bits =>
    ∃ A : I.Allocation, I.IsEF1 A ∧ I.IsFPO A ∧ bits = encodeAllocation A) := by
  sorry

end EF1FPO
