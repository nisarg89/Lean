import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Connected.PathConnected

/-!
# Connectivity for finite-cover arguments

`ConnectedThrough k S` means that `S` is path connected and its positive
homotopy groups through degree `k` vanish.  The ambient topology on `S` is
the subtype topology.  Thus `ConnectedThrough 0 S` is path connectedness.

The finite-cover theorem in BF Section 3 needs a high-dimensional nerve
theorem.  This file establishes the precise connectivity vocabulary and the
zero-dimensional case of that theorem.  It deliberately makes no claim
about the higher-dimensional case.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Path connectedness and vanishing of homotopy groups in positive degrees
at most `k`.  This is the usual `k`-connectedness convention for `k ≥ 0`. -/
def ConnectedThrough {X : Type u} [TopologicalSpace X]
    (k : ℕ) (S : Set X) : Prop :=
  IsPathConnected S ∧
    ∀ (x : S) (j : ℕ), 1 ≤ j → j ≤ k →
      Subsingleton (HomotopyGroup (Fin j) S x)

theorem connectedThrough_zero_iff {X : Type u} [TopologicalSpace X]
    (S : Set X) : ConnectedThrough 0 S ↔ IsPathConnected S := by
  constructor
  · exact And.left
  · intro hS
    refine ⟨hS, ?_⟩
    intro x j hj hzero
    omega

theorem ConnectedThrough.mono {X : Type u} [TopologicalSpace X]
    {k l : ℕ} {S : Set X} (hS : ConnectedThrough k S) (hkl : l ≤ k) :
    ConnectedThrough l S := by
  refine ⟨hS.1, ?_⟩
  intro x j hj hjl
  exact hS.2 x j hj (hjl.trans hkl)

/-- The intersection of the members of a finite subfamily of a cover. -/
def coverIntersection {ι : Type v} {X : Type u}
    (C : ι → Set X) (J : Finset ι) : Set X :=
  ⋂ i ∈ J, C i

/-- The union of a family of sets. -/
def coverUnion {ι : Type v} {X : Type u}
    (C : ι → Set X) : Set X :=
  ⋃ i, C i

/-- A common point of all members of a nonempty cover. -/
def HasCommonPoint {ι : Type v} {X : Type u}
    (C : ι → Set X) : Prop :=
  ∃ x, ∀ i, x ∈ C i

/-- The hypotheses of the BF finite-cover nerve proposition, expressed with
natural numbers. An intersection of `s` sets is `(k + 1 - s)`-connected when
`s ≤ k + 1`; all covering sets share a point. -/
def NerveConnectivityHypotheses {ι : Type v} {X : Type u}
    [TopologicalSpace X] [Fintype ι]
    (k : ℕ) (C : ι → Set X) : Prop :=
  HasCommonPoint C ∧
    ∀ J : Finset ι, J.Nonempty → J.card ≤ k + 1 →
      ConnectedThrough (k + 1 - J.card) (coverIntersection C J)

/-- The same numerical cover hypothesis for an arbitrary connectivity
predicate. This lets the π-group and cube-sphere routes share one finite-cover
induction. -/
def FiniteCoverConnectivityHypotheses {ι : Type v} {X : Type u}
    [Fintype ι] (P : ℕ → Set X → Prop) (k : ℕ) (C : ι → Set X) : Prop :=
  HasCommonPoint C ∧
    ∀ J : Finset ι, J.Nonempty → J.card ≤ k + 1 →
      P (k + 1 - J.card) (coverIntersection C J)

/-- The original homotopy-group hypothesis is the generic hypothesis with
`ConnectedThrough` as its connectivity predicate. -/
theorem finiteCoverConnectivityHypotheses_connectedThrough_iff
    {ι : Type v} {X : Type u} [TopologicalSpace X] [Fintype ι]
    (k : ℕ) (C : ι → Set X) :
    FiniteCoverConnectivityHypotheses (fun j S => ConnectedThrough j S) k C ↔
      NerveConnectivityHypotheses k C := Iff.rfl

theorem NerveConnectivityHypotheses.mono {ι : Type v} {X : Type u}
    [TopologicalSpace X] [Fintype ι]
    {k l : ℕ} {C : ι → Set X}
    (hC : NerveConnectivityHypotheses k C) (hlk : l ≤ k) :
    NerveConnectivityHypotheses l C := by
  refine ⟨hC.1, ?_⟩
  intro J hJ hcard
  have hlarge : J.card ≤ k + 1 := by omega
  exact (hC.2 J hJ hlarge).mono (by omega)

theorem coverIntersection_nonempty_of_commonPoint {ι : Type v} {X : Type u}
    {C : ι → Set X} (hC : HasCommonPoint C) (J : Finset ι) :
    (coverIntersection C J).Nonempty := by
  obtain ⟨x, hx⟩ := hC
  refine ⟨x, ?_⟩
  exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun _ => hx i))

/-- A union of path-connected sets with a common point is path connected.
Finiteness is unnecessary in dimension zero. -/
theorem pathConnected_coverUnion {ι : Type v} {X : Type u}
    [TopologicalSpace X] [Nonempty ι] (C : ι → Set X)
    (hC : HasCommonPoint C)
    (hpath : ∀ i, IsPathConnected (C i)) :
    IsPathConnected (coverUnion C) := by
  obtain ⟨x, hx⟩ := hC
  refine ⟨x, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨Classical.choice inferInstance, hx _⟩
  · intro y hy
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
    exact ((hpath i).joinedIn x (hx i) y hyi).mono
      (fun z hz => Set.mem_iUnion.mpr ⟨i, hz⟩)

/-- The zero-dimensional instance of the manuscript's finite-cover nerve
proposition. -/
theorem connectedThrough_zero_coverUnion {ι : Type v} {X : Type u}
    [TopologicalSpace X] [Fintype ι] [Nonempty ι]
    (C : ι → Set X)
    (hC : NerveConnectivityHypotheses 0 C) :
    ConnectedThrough 0 (coverUnion C) := by
  apply (connectedThrough_zero_iff (coverUnion C)).2
  apply pathConnected_coverUnion C hC.1
  intro i
  have hsingle := hC.2 ({i} : Finset ι) (Finset.singleton_nonempty i) (by simp)
  simpa [coverIntersection, connectedThrough_zero_iff] using hsingle

end FairDivision.Topology.NerveConnectivity
