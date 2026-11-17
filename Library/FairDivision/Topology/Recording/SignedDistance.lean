import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Piecewise

/-!
# Recording a pathwise separator by the manuscript's signed distance

This is the final construction in BF Lemma “Multiplication by a prime”.
For a closed separating zero set `Z`, the negative region consists of the
points that can be reached from the lower boundary without meeting `Z`.
Its sign is locally constant off `Z` because the ambient graph-times-interval
space is locally path connected. The recorder is precisely minus distance
on that region and plus distance elsewhere. Its zero set is exactly `Z`.

The statement is expressed for an arbitrary metric locally path-connected
space, so the graph realization need only establish that standard structure
once. No alternative separation theorem replaces the manuscript argument.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Recording

open Set Filter Topology

variable {X : Type*} [MetricSpace X]

/-- Points reachable from the lower boundary through the complement of the
projected zero set. -/
def lowerReachable (Z lower : Set X) : Set X :=
  {x | ∃a∈lower,JoinedIn Zᶜ a x}

theorem lowerReachable_subset_compl (Z lower : Set X) :
    lowerReachable Z lower⊆Zᶜ := by
  rintro x ⟨a,_ha,hax⟩
  exact hax.target_mem

theorem lowerReachable_self {Z lower : Set X} {x : X}
    (hx : x∈lower) (hxZ : x∉Z) : x∈lowerReachable Z lower :=
  ⟨x,hx,JoinedIn.refl hxZ⟩

theorem lowerReachable_iff_of_joinedIn {Z lower : Set X} {x y : X}
    (hxy : JoinedIn Zᶜ x y) :
    x∈lowerReachable Z lower ↔ y∈lowerReachable Z lower := by
  constructor
  · rintro ⟨a,ha,hax⟩
    exact ⟨a,ha,hax.trans hxy⟩
  · rintro ⟨a,ha,hay⟩
    exact ⟨a,ha,hay.trans hxy.symm⟩

variable [LocallyPathConnectedSpace X]

/-- Reachability is open because it is a union of open path components in
the complement of the closed projected zero set. -/
theorem isOpen_lowerReachable {Z lower : Set X} (hZ : IsClosed Z) :
    IsOpen (lowerReachable Z lower) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨a,ha,hax⟩
  exact mem_of_superset ((hZ.isOpen_compl.pathComponentIn a).mem_nhds hax)
    (fun y hay=>⟨a,ha,hay⟩)

/-- The sign can change only at the projected zero set. The proof uses a
path-component neighborhood of any proposed frontier point outside `Z`. -/
theorem frontier_lowerReachable_subset {Z lower : Set X} (hZ : IsClosed Z) :
    frontier (lowerReachable Z lower)⊆Z := by
  intro x hx
  by_contra hxZ
  have hW : IsOpen (pathComponentIn Zᶜ x) := hZ.isOpen_compl.pathComponentIn x
  have hxW : x∈pathComponentIn Zᶜ x := mem_pathComponentIn_self hxZ
  obtain ⟨y,hyW,hyLower⟩ := mem_closure_iff.mp hx.1 _ hW hxW
  have hxLower : x∈lowerReachable Z lower :=
    (lowerReachable_iff_of_joinedIn hyW).mpr hyLower
  have hOpen := isOpen_lowerReachable (lower:=lower) hZ
  exact hx.2 (by simpa only [hOpen.interior_eq] using hxLower)

/-- The literal signed-distance formula used by the parent recording
function. The value at the zero set is zero independently of its sign branch. -/
noncomputable def signedDistance (Z lower : Set X) : X→ℝ := by
  classical
  exact (lowerReachable Z lower).piecewise
    (fun x=>-Metric.infDist x Z) (fun x=>Metric.infDist x Z)

/-- Both branches are continuous and agree on their common frontier,
because that frontier is contained in `Z`. -/
theorem continuous_signedDistance {Z lower : Set X} (hZ : IsClosed Z) :
    Continuous (signedDistance Z lower) := by
  classical
  apply Continuous.piecewise
  · intro x hx
    have hDist : Metric.infDist x Z=0 :=
      Metric.infDist_zero_of_mem (frontier_lowerReachable_subset hZ hx)
    simp only [hDist,neg_zero]
  · exact (Metric.continuous_infDist_pt Z).neg
  · exact Metric.continuous_infDist_pt Z

theorem signedDistance_eq_zero_iff {Z lower : Set X}
    (hZ : IsClosed Z) (hNonempty : Z.Nonempty) (x : X) :
    signedDistance Z lower x=0 ↔ x∈Z := by
  classical
  have hDist := (hZ.mem_iff_infDist_zero hNonempty (x:=x)).symm
  by_cases hx : x∈lowerReachable Z lower
  · simpa [signedDistance,hx] using hDist
  · simpa [signedDistance,hx] using hDist

theorem signedDistance_neg_on_lower {Z lower : Set X}
    (hZ : IsClosed Z) (hNonempty : Z.Nonempty)
    (hLower : Disjoint lower Z) {x : X} (hx : x∈lower) :
    signedDistance Z lower x<0 := by
  classical
  have hxZ : x∉Z := fun hxZ=>Set.disjoint_left.mp hLower hx hxZ
  have hReach := lowerReachable_self hx hxZ
  have hDist := (hZ.notMem_iff_infDist_pos hNonempty).mp hxZ
  simpa [signedDistance,hReach] using (neg_lt_zero.mpr hDist)

/-- Pathwise separation excludes the upper boundary from the lower-reachable
region, hence gives its required strictly positive sign. -/
theorem signedDistance_pos_on_upper {Z lower upper : Set X}
    (hZ : IsClosed Z) (hNonempty : Z.Nonempty)
    (hUpper : Disjoint upper Z)
    (hSeparate : ∀a∈lower,∀b∈upper,¬JoinedIn Zᶜ a b)
    {x : X} (hx : x∈upper) : 0<signedDistance Z lower x := by
  classical
  have hxZ : x∉Z := fun hxZ=>Set.disjoint_left.mp hUpper hx hxZ
  have hNotReach : x∉lowerReachable Z lower := by
    rintro ⟨a,ha,hax⟩
    exact hSeparate a ha x hx hax
  have hDist := (hZ.notMem_iff_infDist_pos hNonempty).mp hxZ
  simpa [signedDistance,hNotReach] using hDist

/-- Package the exact signed-distance construction as a continuous recorder.
Only its zeros need a lottery witness in the subsequent application. -/
theorem exists_signedDistance_recorder {Z lower upper : Set X}
    (hZ : IsClosed Z) (hNonempty : Z.Nonempty)
    (hLower : Disjoint lower Z) (hUpper : Disjoint upper Z)
    (hSeparate : ∀a∈lower,∀b∈upper,¬JoinedIn Zᶜ a b) :
    ∃Φ : C(X,ℝ),
      (∀x∈lower,Φ x<0) ∧ (∀x∈upper,0<Φ x) ∧
      (∀x,Φ x=0 ↔ x∈Z) := by
  refine ⟨⟨signedDistance Z lower,continuous_signedDistance hZ⟩,?_,?_,?_⟩
  · intro x hx
    exact signedDistance_neg_on_lower hZ hNonempty hLower hx
  · intro x hx
    exact signedDistance_pos_on_upper hZ hNonempty hUpper hSeparate hx
  · intro x
    exact signedDistance_eq_zero_iff hZ hNonempty x

end FairDivision.Topology.Recording
