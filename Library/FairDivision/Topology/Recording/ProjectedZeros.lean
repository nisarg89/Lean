import FairDivision.Topology.Recording.SignedDistance
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Projecting simultaneous child zeros and recording them

BF Section 4 first projects the zero set of the continuous child-score map
from the fixed equivariant source to the graph-times-target-interval space.
Compactness of the source makes this projection closed. Pathwise separation
then supplies precisely the signs of the signed-distance recorder.

This file carries out that projection and recording step. The pathwise-zero
statement is an explicit input to this generic adapter. The actual BF caller
discharges that input in `BF/Recording/AAKPathwise` using the cyclic zero proof.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Recording

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] {p : ℕ}

section TopologicalParameter

variable [TopologicalSpace Y]

/-- The parent parameter values for which all child scores vanish at some
point of the fixed equivariant source. -/
def projectedZeros (T : C(X×Y,Fin p→ℝ)) : Set Y :=
  {y | ∃x : X,T (x,y)=0}

theorem projectedZeros_eq_image (T : C(X×Y,Fin p→ℝ)) :
    projectedZeros T=Prod.snd '' {z : X×Y | T z=0} := by
  ext y
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨(x,y),hx,rfl⟩
  · rintro ⟨⟨x,z⟩,hx,hz⟩
    dsimp at hz
    subst z
    exact ⟨x,hx⟩

/-- Projection is closed because the forgotten fixed source is compact.
The parameter space itself need not be compact for this step. -/
theorem isClosed_projectedZeros [CompactSpace X]
    (T : C(X×Y,Fin p→ℝ)) : IsClosed (projectedZeros T) := by
  rw [projectedZeros_eq_image]
  exact isClosedMap_snd_of_compactSpace _ (isClosed_eq T.continuous continuous_const)

/-- The stronger compactness claim used in the manuscript when both the
fixed source and graph-times-interval parameter space are compact. -/
theorem isCompact_projectedZeros [CompactSpace X] [CompactSpace Y]
    (T : C(X×Y,Fin p→ℝ)) : IsCompact (projectedZeros T) := by
  rw [projectedZeros_eq_image]
  exact ((isClosed_eq T.continuous continuous_const).isCompact).image continuous_snd

/-- A strict sign of every child score excludes a parameter boundary from
the projected simultaneous-zero set. -/
theorem disjoint_projectedZeros_of_negative
    (hp : 0<p) (T : C(X×Y,Fin p→ℝ)) (lower : Set Y)
    (hLower : ∀x y,y∈lower→∀i,T (x,y) i<0) :
    Disjoint lower (projectedZeros T) := by
  apply Set.disjoint_left.mpr
  rintro y hy ⟨x,hZero⟩
  have h := hLower x y hy ⟨0,hp⟩
  rw [hZero] at h
  exact lt_irrefl (0:ℝ) h

theorem disjoint_projectedZeros_of_positive
    (hp : 0<p) (T : C(X×Y,Fin p→ℝ)) (upper : Set Y)
    (hUpper : ∀x y,y∈upper→∀i,0<T (x,y) i) :
    Disjoint upper (projectedZeros T) := by
  apply Set.disjoint_left.mpr
  rintro y hy ⟨x,hZero⟩
  have h := hUpper x y hy ⟨0,hp⟩
  rw [hZero] at h
  exact lt_irrefl (0:ℝ) h

/-- State the output needed from AAK along actual parameter paths. -/
def HasPathwiseZeros (T : C(X×Y,Fin p→ℝ)) (lower upper : Set Y) : Prop :=
  ∀a∈lower,∀b∈upper,∀γ : Path a b,∃t : unitInterval,∃x : X,T (x,γ t)=0

/-- A path avoiding the projected zero set contradicts the pathwise-zero
property on that very path. -/
theorem no_joinedIn_compl_projectedZeros (T : C(X×Y,Fin p→ℝ))
    {lower upper : Set Y} (hPath : HasPathwiseZeros T lower upper) :
    ∀a∈lower,∀b∈upper,¬JoinedIn (projectedZeros T)ᶜ a b := by
  intro a ha b hb hJoined
  obtain ⟨t,x,hZero⟩ := hPath a ha b hb hJoined.somePath
  exact hJoined.somePath_mem t ⟨x,hZero⟩

/-- One lower-to-upper path suffices for nonemptiness of the projected
zeros; in the manuscript this is a vertical path over any graph point. -/
theorem projectedZeros_nonempty_of_path (T : C(X×Y,Fin p→ℝ))
    {lower upper : Set Y} (hPath : HasPathwiseZeros T lower upper)
    {a b : Y} (ha : a∈lower) (hb : b∈upper) (γ : Path a b) :
    (projectedZeros T).Nonempty := by
  obtain ⟨t,x,hZero⟩ := hPath a ha b hb γ
  exact ⟨γ t,x,hZero⟩

/-- A simultaneous zero certificate is inherited by the projected set. -/
theorem projectedZeros_certifies (T : C(X×Y,Fin p→ℝ)) (P : Y→Prop)
    (hZero : ∀x y,T (x,y)=0→P y) : ∀y∈projectedZeros T,P y := by
  rintro y ⟨x,hx⟩
  exact hZero x y hx

end TopologicalParameter

/-- Assemble the manuscript parent recorder from actual child scores and
its pathwise-zero result. Its zero witness is the SAME simultaneous zero
used by the child-lottery construction. -/
theorem exists_projectedZero_recorder [CompactSpace X] [MetricSpace Y]
    [LocallyPathConnectedSpace Y] (hp : 0<p)
    (T : C(X×Y,Fin p→ℝ)) (lower upper : Set Y)
    (hLower : ∀x y,y∈lower→∀i,T (x,y) i<0)
    (hUpper : ∀x y,y∈upper→∀i,0<T (x,y) i)
    (hPath : HasPathwiseZeros T lower upper)
    {a b : Y} (ha : a∈lower) (hb : b∈upper) (γ : Path a b) :
    ∃Φ : C(Y,ℝ),
      (∀y∈lower,Φ y<0) ∧ (∀y∈upper,0<Φ y) ∧
      (∀y,Φ y=0 ↔ ∃x : X,T (x,y)=0) := by
  exact exists_signedDistance_recorder (isClosed_projectedZeros T)
    (projectedZeros_nonempty_of_path T hPath ha hb γ)
    (disjoint_projectedZeros_of_negative hp T lower hLower)
    (disjoint_projectedZeros_of_positive hp T upper hUpper)
    (no_joinedIn_compl_projectedZeros T hPath)

end FairDivision.Topology.Recording
