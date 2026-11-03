import FairDivision.Topology.CompatibleLottery

/-!
# Variable-size auxiliary complex for the BF connectivity induction

The manuscript's induction decreases one position's bundle requirement at a
time. Accordingly, this canonical auxiliary complex has a size `r i` and
dummy cap `c i` at each position. It uses the same unlabeled-dummy vertex
identification and existential compatible-face convention as Section 3.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- A partial allocation satisfying position-dependent size and dummy caps. -/
def IsValidVariablePartial {k m : ℕ} (D : Finset (Fin m))
    (r c : Fin k → ℕ) (X : PartialAllocation k m) : Prop :=
  ∀ i : Fin k,
    (partialBundle X i).card = r i ∧
      ((partialBundle X i) ∩ D).card ≤ c i

/-- Labeled vertices for a variable-size auxiliary complex. -/
abbrev VariablePartialVertex (k : ℕ) {m : ℕ}
    (D : Finset (Fin m)) (r c : Fin k → ℕ) :=
  {X : PartialAllocation k m // IsValidVariablePartial D r c X}

/-- Position pool over a finite family of variable-size vertices. -/
def variablePool {k m : ℕ} {D : Finset (Fin m)}
    {r c : Fin k → ℕ}
    (T : Finset (VariablePartialVertex k D r c)) (i : Fin k) :
    Finset (Fin m) :=
  Finset.univ.filter (fun g => ∃ X ∈ T, X.1 g = some i)

/-- Compatibility uses disjoint pools and the cap at each position. -/
def IsVariableCompatibleFamily {k m : ℕ} {D : Finset (Fin m)}
    {r c : Fin k → ℕ}
    (T : Finset (VariablePartialVertex k D r c)) : Prop :=
  (∀ i j : Fin k, i ≠ j →
    Disjoint (variablePool T i) (variablePool T j)) ∧
  (∀ i : Fin k, ((variablePool T i) ∩ D).card ≤ c i)

/-- Restricting a family shrinks every variable-size pool. -/
theorem variablePool_mono {k m : ℕ} {D : Finset (Fin m)}
    {r c : Fin k → ℕ}
    {S T : Finset (VariablePartialVertex k D r c)}
    (hST : S ⊆ T) (i : Fin k) :
    variablePool S i ⊆ variablePool T i := by
  classical
  intro g hg
  obtain ⟨_, X, hXS, hXg⟩ := Finset.mem_filter.mp hg
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, X, hST hXS, hXg⟩

/-- A vertex's bundle lies in the pool of any family containing it. -/
theorem variableBundle_subset_pool {k m : ℕ} {D : Finset (Fin m)}
    {r c : Fin k → ℕ}
    {T : Finset (VariablePartialVertex k D r c)}
    {X : VariablePartialVertex k D r c}
    (hXT : X ∈ T) (i : Fin k) :
    partialBundle X.1 i ⊆ variablePool T i := by
  classical
  intro g hg
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, X, hXT, (Finset.mem_filter.mp hg).2⟩

/-- Compatibility is hereditary for variable-size families. -/
theorem variableCompatible_mono {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    {S T : Finset (VariablePartialVertex k D r c)}
    (hST : S ⊆ T) (hT : IsVariableCompatibleFamily T) :
    IsVariableCompatibleFamily S := by
  classical
  constructor
  · intro i j hij
    exact (hT.1 i j hij).mono
      (variablePool_mono hST i) (variablePool_mono hST j)
  · intro i
    have hsub : variablePool S i ∩ D ⊆ variablePool T i ∩ D := by
      intro g hg
      exact Finset.mem_inter.mpr
        ⟨variablePool_mono hST i (Finset.mem_inter.mp hg).1,
          (Finset.mem_inter.mp hg).2⟩
    exact (Finset.card_le_card hsub).trans (hT.2 i)

/-- Every variable-size vertex is a compatible singleton. -/
theorem variableCompatible_singleton {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (X : VariablePartialVertex k D r c) :
    IsVariableCompatibleFamily ({X} :
      Finset (VariablePartialVertex k D r c)) := by
  classical
  have hPool (i : Fin k) :
      variablePool ({X} : Finset (VariablePartialVertex k D r c)) i =
        partialBundle X.1 i := by
    ext g
    simp [variablePool, partialBundle]
  constructor
  · intro i j hij
    rw [hPool, hPool]
    apply Finset.disjoint_left.mpr
    intro g hgi hgj
    have hxi : X.1 g = some i := (Finset.mem_filter.mp hgi).2
    have hxj : X.1 g = some j := (Finset.mem_filter.mp hgj).2
    exact hij (Option.some.inj (hxi.symm.trans hxj))
  · intro i
    rw [hPool]
    exact (X.2 i).2

/-- Forget labels, retaining every real bundle and dummy count. -/
def variableDummyProfileOf {k m : ℕ} {D : Finset (Fin m)}
    {r c : Fin k → ℕ}
    (X : VariablePartialVertex k D r c) :
    Fin k → Finset (Fin m) × ℕ :=
  fun i => (partialBundle X.1 i \ D,
    (partialBundle X.1 i ∩ D).card)

/-- A variable-size auxiliary vertex is an actually realized profile. -/
abbrev VariableUnlabeledVertex (k m : ℕ) (D : Finset (Fin m))
    (r c : Fin k → ℕ) :=
  {p : Fin k → Finset (Fin m) × ℕ // p ∈ Set.range
    (variableDummyProfileOf (D := D) (r := r) (c := c))}

/-- Map a labeled variable-size allocation to its unlabeled profile. -/
def toVariableUnlabeledVertex {k m : ℕ} {D : Finset (Fin m)}
    {r c : Fin k → ℕ}
    (X : VariablePartialVertex k D r c) :
    VariableUnlabeledVertex k m D r c :=
  ⟨variableDummyProfileOf X, ⟨X, rfl⟩⟩

noncomputable instance variableUnlabeledVertexFintype
    (k m : ℕ) (D : Finset (Fin m)) (r c : Fin k → ℕ) :
    Fintype (VariableUnlabeledVertex k m D r c) := by
  classical
  exact Fintype.ofFinite _

/-- A family of unlabeled profiles is a face when compatible labeled
representatives exist. -/
def IsVariableUnlabeledFamily {k m : ℕ} {D : Finset (Fin m)}
    {r c : Fin k → ℕ}
    (S : Finset (VariableUnlabeledVertex k m D r c)) : Prop :=
  ∃ T : Finset (VariablePartialVertex k D r c),
    IsVariableCompatibleFamily T ∧
      T.image toVariableUnlabeledVertex = S

/-- Restricting an unlabeled face preserves compatible representatives. -/
theorem variableUnlabeled_mono {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    {S U : Finset (VariableUnlabeledVertex k m D r c)}
    (hUS : U ⊆ S) (hS : IsVariableUnlabeledFamily S) :
    IsVariableUnlabeledFamily U := by
  classical
  obtain ⟨T, hT, hImage⟩ := hS
  let T' := T.filter (fun X => toVariableUnlabeledVertex X ∈ U)
  refine ⟨T', variableCompatible_mono
    (Finset.filter_subset _ _) hT, ?_⟩
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

/-- Every realized profile has a compatible singleton witness. -/
theorem variableUnlabeled_singleton {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (p : VariableUnlabeledVertex k m D r c) :
    IsVariableUnlabeledFamily ({p} :
      Finset (VariableUnlabeledVertex k m D r c)) := by
  classical
  obtain ⟨X, hX⟩ := p.2
  have hp : toVariableUnlabeledVertex X = p := Subtype.ext hX
  refine ⟨{X}, variableCompatible_singleton X, ?_⟩
  simp [hp]

/-- The position-dependent complex used by the connectivity induction. -/
def variableDummyComplex (k m : ℕ) (D : Finset (Fin m))
    (r c : Fin k → ℕ) :
    AbstractSimplicialComplex (VariableUnlabeledVertex k m D r c) where
  faces := {S | S.Nonempty ∧ IsVariableUnlabeledFamily S}
  isRelLowerSet_faces := by
    intro S hS
    exact ⟨hS.1, fun _ hsub hne =>
      ⟨hne, variableUnlabeled_mono hsub hS.2⟩⟩
  singleton_mem := by
    intro p
    exact ⟨Finset.singleton_nonempty p, variableUnlabeled_singleton p⟩

end FairDivision.Topology
