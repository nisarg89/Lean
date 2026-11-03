import FairDivision.Topology.CompatibleLottery

/-!
# The auxiliary complex with unlabeled dummy items

A vertex remembers the real bundle and the number of dummy items at each
position. It forgets which labeled dummy items were used. A family is a face
exactly when compatible labeled representatives can be chosen for its vertices.
This is the finite combinatorial complex of `def:configuration-complex` in the
first manuscript, before its geometric realization and connectivity proof.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The real bundle and dummy count at every position. -/
abbrev DummyProfile (k m : ℕ) := Fin k → Finset (Fin m) × ℕ

/-- The profile of a labeled partial allocation. -/
def dummyProfileOf {k m r c : ℕ} {D : Finset (Fin m)}
    (X : PartialVertex k D r c) : DummyProfile k m :=
  fun i => (partialBundle X.1 i \ D, (partialBundle X.1 i ∩ D).card)

/-- Exactly the manuscript's equivalence relation on partial allocations:
real bundles and dummy counts agree at every position. -/
theorem dummyProfileOf_eq_iff {k m r c : ℕ} {D : Finset (Fin m)}
    (X Y : PartialVertex k D r c) :
    dummyProfileOf X = dummyProfileOf Y ↔
      ∀ i : Fin k,
        partialBundle X.1 i \ D = partialBundle Y.1 i \ D ∧
          (partialBundle X.1 i ∩ D).card =
            (partialBundle Y.1 i ∩ D).card := by
  constructor
  · intro h i
    have hi := congrFun h i
    exact ⟨congrArg Prod.fst hi, congrArg Prod.snd hi⟩
  · intro h
    funext i
    exact Prod.ext (h i).1 (h i).2

/-- A vertex is a profile actually realized by a valid labeled allocation. -/
abbrev UnlabeledDummyVertex (k m r c : ℕ) (D : Finset (Fin m)) :=
  {p : DummyProfile k m // p ∈ Set.range
    (dummyProfileOf (k := k) (m := m) (r := r) (c := c) (D := D))}

/-- Forget the dummy labels of one valid partial allocation. -/
def toUnlabeledDummyVertex {k m r c : ℕ} {D : Finset (Fin m)}
    (X : PartialVertex k D r c) : UnlabeledDummyVertex k m r c D :=
  ⟨dummyProfileOf X, ⟨X, rfl⟩⟩

/-- Two valid partial allocations map to the same auxiliary vertex precisely
when they have the same real bundles and dummy counts. -/
theorem toUnlabeledDummyVertex_eq_iff {k m r c : ℕ}
    {D : Finset (Fin m)} (X Y : PartialVertex k D r c) :
    toUnlabeledDummyVertex X = toUnlabeledDummyVertex Y ↔
      ∀ i : Fin k,
        partialBundle X.1 i \ D = partialBundle Y.1 i \ D ∧
          (partialBundle X.1 i ∩ D).card =
            (partialBundle Y.1 i ∩ D).card := by
  rw [← dummyProfileOf_eq_iff]
  exact Subtype.ext_iff

noncomputable instance unlabeledDummyVertexFintype
    (k m r c : ℕ) (D : Finset (Fin m)) :
    Fintype (UnlabeledDummyVertex k m r c D) := by
  classical
  exact Fintype.ofFinite _

/-- Faces admit a compatible family of labeled representatives. -/
def IsUnlabeledCompatibleFamily {k m r c : ℕ} {D : Finset (Fin m)}
    (S : Finset (UnlabeledDummyVertex k m r c D)) : Prop :=
  ∃ T : Finset (PartialVertex k D r c),
    IsCompatibleFamily T ∧ T.image toUnlabeledDummyVertex = S

/-- Passing to fewer auxiliary vertices preserves compatibility: keep only
representatives whose profiles remain in the smaller family. -/
theorem unlabeledCompatible_mono {k m r c : ℕ}
    {D : Finset (Fin m)}
    {S U : Finset (UnlabeledDummyVertex k m r c D)}
    (hUS : U ⊆ S) (hS : IsUnlabeledCompatibleFamily S) :
    IsUnlabeledCompatibleFamily U := by
  classical
  obtain ⟨T, hT, hImage⟩ := hS
  let T' := T.filter (fun X => toUnlabeledDummyVertex X ∈ U)
  refine ⟨T', compatible_mono (Finset.filter_subset _ _) hT, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨X, hXT', hXp⟩ := Finset.mem_image.mp hp
    exact hXp ▸ (Finset.mem_filter.mp hXT').2
  · intro hpU
    have hpS : p ∈ S := hUS hpU
    rw [← hImage] at hpS
    obtain ⟨X, hXT, hXp⟩ := Finset.mem_image.mp hpS
    apply Finset.mem_image.mpr
    refine ⟨X, Finset.mem_filter.mpr ⟨hXT, ?_⟩, hXp⟩
    exact hXp.symm ▸ hpU

/-- Every auxiliary vertex has a compatible singleton representative. -/
theorem unlabeledCompatible_singleton {k m r c : ℕ}
    {D : Finset (Fin m)} (p : UnlabeledDummyVertex k m r c D) :
    IsUnlabeledCompatibleFamily ({p} :
      Finset (UnlabeledDummyVertex k m r c D)) := by
  classical
  obtain ⟨X, hX⟩ := p.2
  have hp : toUnlabeledDummyVertex X = p := Subtype.ext hX
  refine ⟨{X}, compatible_singleton X, ?_⟩
  simp [hp]

/-- The manuscript's auxiliary complex, with dummy labels identified but
retained in the existential face witness. -/
def unlabeledDummyComplex (k m r c : ℕ) (D : Finset (Fin m)) :
    AbstractSimplicialComplex (UnlabeledDummyVertex k m r c D) where
  faces := {S | S.Nonempty ∧ IsUnlabeledCompatibleFamily S}
  isRelLowerSet_faces := by
    intro S hS
    exact ⟨hS.1, fun _ hsub hne =>
      ⟨hne, unlabeledCompatible_mono hsub hS.2⟩⟩
  singleton_mem := by
    intro p
    exact ⟨Finset.singleton_nonempty p, unlabeledCompatible_singleton p⟩

end FairDivision.Topology
