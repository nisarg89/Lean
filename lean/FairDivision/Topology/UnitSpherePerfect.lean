import FairDivision.Topology.SphericalCapBasic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen

/-!
# Unit spheres of dimension at least two have no isolated points

The cap family becomes the whole sphere at one radius.  At that transition,
strict cap points are all points except the antipode, so this density fact
handles the exceptional geometric case.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open Set

private theorem dense_compl_singleton_of_preconnected
    {X : Type*} [TopologicalSpace X] [T1Space X] [PreconnectedSpace X]
    (x : X) (hne : ∃ z : X, z ≠ x) : Dense ({x}ᶜ : Set X) := by
  rw [dense_compl_singleton_iff_not_open]
  intro hOpen
  have hSub : (Set.univ : Set X) ⊆ {x} :=
    isPreconnected_univ.subset_isClopen
      ⟨isClosed_singleton, hOpen⟩ ⟨x, by simp⟩
  obtain ⟨z, hz⟩ := hne
  exact hz (Set.mem_singleton_iff.mp (hSub (Set.mem_univ z)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem unitSphere_preconnected (hRank : 1 < Module.rank ℝ E) :
    PreconnectedSpace (UnitSphere E) := by
  apply isPreconnected_iff_preconnectedSpace.mp
  have hset : {y : E | ‖y‖ = 1} = Metric.sphere (0 : E) 1 := by
    ext y
    simp [Metric.mem_sphere, dist_eq_norm]
  change IsPreconnected ({y : E | ‖y‖ = 1})
  rw [hset]
  exact isPreconnected_sphere hRank (0 : E) 1

theorem unitSphere_dense_compl_singleton
    (hRank : 1 < Module.rank ℝ E) (y : UnitSphere E) :
    Dense ({y}ᶜ : Set (UnitSphere E)) := by
  letI : PreconnectedSpace (UnitSphere E) := unitSphere_preconnected hRank
  apply dense_compl_singleton_of_preconnected y
  let z : UnitSphere E := ⟨-(y : E), by simpa using y.property⟩
  refine ⟨z, ?_⟩
  intro hz
  have hval : -(y : E) = (y : E) := congrArg Subtype.val hz
  have hadd : (y : E) + (y : E) = 0 := by
    calc
      (y : E) + (y : E) = -(y : E) + (y : E) := by rw [hval]
      _ = 0 := neg_add_cancel _
  have hnorm : ‖(y : E) + (y : E)‖ = 2 := by
    rw [← two_smul ℝ (y : E), norm_smul, y.property]
    norm_num
  simp [hadd] at hnorm

end FairDivision.Topology
