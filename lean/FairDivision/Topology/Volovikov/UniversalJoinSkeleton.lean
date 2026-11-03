import FairDivision.Topology.Volovikov.JoinFaceCellActionLaws

/-!
# Cardinality skeleta of the finite universal join

A face with `d` vertices is a `(d-1)`-simplex. Filtering by cardinality
provides a finite sequence of invariant subcomplexes for equivariant
cell-by-cell extension into a sufficiently connected target.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- The subcomplex of `G^{*m}` containing only faces with at most `d`
vertices. -/
def universalJoinSkeleton (m : ℕ) (G : Type*) (d : ℕ) :
    PreAbstractSimplicialComplex (Fin m × G) where
  faces := {S | IsUniversalJoinFace S ∧ S.card ≤ d}
  isRelLowerSet_faces := by
    intro S hS
    constructor
    · exact hS.1.1
    · intro T hTS hT
      refine ⟨⟨hT, ?_⟩, ?_⟩
      · intro i g h hgi hhi
        exact hS.1.2 i g h (hTS hgi) (hTS hhi)
      · exact (Finset.card_le_card hTS).trans hS.2

/-- The skeleton increases with its cardinality cutoff. -/
theorem universalJoinSkeleton_mono {m d e : ℕ} {G : Type*}
    (hde : d ≤ e) :
    universalJoinSkeleton m G d ≤ universalJoinSkeleton m G e := by
  intro S hS
  exact ⟨hS.1, hS.2.trans hde⟩

/-- At cardinality at least `m`, the skeleton is the full universal join. -/
theorem universalJoinSkeleton_eq_full {m d : ℕ} {G : Type*}
    (hmd : m ≤ d) :
    universalJoinSkeleton m G d = universalJoinComplex m G := by
  ext S
  constructor
  · exact And.left
  · intro hS
    exact ⟨hS, (universalJoinFace_card_le hS).trans hmd⟩

/-- Translation preserves the cardinality skeleton. -/
theorem universalJoinSkeleton_translate {m d : ℕ} {G : Type*}
    [AddGroup G] {S : Finset (Fin m × G)}
    (hS : S ∈ universalJoinSkeleton m G d) (a : G) :
    translateJoinFace a S ∈ universalJoinSkeleton m G d := by
  refine ⟨universalJoinFace_translate hS.1 a, ?_⟩
  rw [translateJoinFace_card]
  exact hS.2

/-- Every full cell of a face at the cutoff lies in the skeleton. -/
theorem fullFaceComplex_le_universalJoinSkeleton {m d : ℕ} {G : Type*}
    (S : Finset (Fin m × G))
    (hS : S ∈ universalJoinSkeleton m G d) :
    FairDivision.Topology.NerveConnectivity.fullFaceComplex S ≤
      universalJoinSkeleton m G d :=
  FairDivision.Topology.NerveConnectivity.fullFaceComplex_le_of_mem
    (universalJoinSkeleton m G d) S hS

end FairDivision.Topology.Volovikov

namespace FairDivision.Topology.Volovikov

/-- A new face at the next stage has exactly the new cardinality. -/
theorem universalJoinSkeleton_newFace_card {m d : ℕ} {G : Type*}
    {S : Finset (Fin m × G)}
    (hnew : S ∈ universalJoinSkeleton m G (d + 1))
    (hold : S ∉ universalJoinSkeleton m G d) :
    S.card = d + 1 := by
  have hnot : ¬ S.card ≤ d := by
    intro hcard
    exact hold ⟨hnew.1, hcard⟩
  exact Nat.le_antisymm hnew.2 (Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot))

/-- Every proper nonempty subface of a new cell belongs to the previous
cardinality skeleton. -/
theorem universalJoinSkeleton_properFace_old {m d : ℕ} {G : Type*}
    {S T : Finset (Fin m × G)}
    (hS : S ∈ universalJoinSkeleton m G (d + 1))
    (hcard : S.card = d + 1)
    (hT : T.Nonempty) (hTS : T ⊂ S) :
    T ∈ universalJoinSkeleton m G d := by
  have hface : IsUniversalJoinFace T := by
    refine ⟨hT, ?_⟩
    intro i g h hgi hhi
    exact hS.1.2 i g h (hTS.subset hgi) (hTS.subset hhi)
  refine ⟨hface, ?_⟩
  have hlt : T.card < S.card := Finset.card_lt_card hTS
  exact Nat.lt_succ_iff.mp (by simpa only [hcard] using hlt)

/-- A face of the new cardinality is absent from the previous skeleton. -/
theorem universalJoinSkeleton_face_not_old {m d : ℕ} {G : Type*}
    {S : Finset (Fin m × G)} (hcard : S.card = d + 1) :
    S ∉ universalJoinSkeleton m G d := by
  intro hS
  have hle : d + 1 ≤ d := hcard ▸ hS.2
  exact Nat.not_succ_le_self d hle

end FairDivision.Topology.Volovikov
