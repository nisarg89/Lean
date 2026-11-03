import FairDivision.Topology.NerveConnectivity.SimplicialCover

/-!
# Reducing the dimension of a binary source-cover overlap

If every face of a source complex has at most `m` vertices, a face of
exactly `m` vertices that belongs to both covering subcomplexes can be
assigned to the first piece. Removing those top faces from the second
piece preserves its downward closure. The resulting intersection has
strictly fewer than `m` vertices per face, which is the dimension shift
needed for binary gluing by coning.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u

/-- Remove shared maximal-cardinality faces from the second cover piece. -/
noncomputable def trimTopOverlap {V : Type u}
    (A B : PreAbstractSimplicialComplex V) (m : ℕ)
    (hBdim : ∀ S : Finset V, S ∈ B → S.card ≤ m) :
    PreAbstractSimplicialComplex V where
  faces := {S | S ∈ B ∧ (S.card < m ∨ S ∉ A)}
  isRelLowerSet_faces := by
    intro S hS
    constructor
    · exact (B.isRelLowerSet_faces hS.1).1
    · intro T hTS hT
      have hTB : T ∈ B :=
        (B.isRelLowerSet_faces hS.1).2 hTS hT
      refine ⟨hTB, ?_⟩
      rcases hS.2 with hsmall | hnotA
      · exact Or.inl ((Finset.card_le_card hTS).trans_lt hsmall)
      · by_cases hTA : T ∈ A
        · left
          have hne : T ≠ S := by
            intro heq
            subst T
            exact hnotA hTA
          exact (Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hne⟩)).trans_le
              (hBdim S hS.1)
        · exact Or.inr hTA

/-- The trimmed piece remains inside the original second piece. -/
theorem trimTopOverlap_le {V : Type u}
    (A B : PreAbstractSimplicialComplex V) (m : ℕ)
    (hBdim : ∀ S : Finset V, S ∈ B → S.card ≤ m) :
    trimTopOverlap A B m hBdim ≤ B :=
  fun _ h => h.1

/-- Trimming shared top faces does not change the binary union. -/
theorem sup_trimTopOverlap_eq_sup {V : Type u}
    (A B : PreAbstractSimplicialComplex V) (m : ℕ)
    (hBdim : ∀ S : Finset V, S ∈ B → S.card ≤ m) :
    A ⊔ trimTopOverlap A B m hBdim = A ⊔ B := by
  ext S
  constructor
  · rintro (hA | hT)
    · exact Or.inl hA
    · exact Or.inr hT.1
  · rintro (hA | hB)
    · exact Or.inl hA
    · by_cases hA : S ∈ A
      · exact Or.inl hA
      · exact Or.inr ⟨hB, Or.inr hA⟩

/-- The overlap after assigning top faces to one side has lower dimension. -/
theorem inf_trimTopOverlap_card_lt {V : Type u}
    (A B : PreAbstractSimplicialComplex V) (m : ℕ)
    (hBdim : ∀ S : Finset V, S ∈ B → S.card ≤ m) :
    ∀ S : Finset V, S ∈ A ⊓ trimTopOverlap A B m hBdim →
      S.card < m := by
  intro S hS
  rcases hS.2.2 with hsmall | hnotA
  · exact hsmall
  · exact (hnotA hS.1).elim

end FairDivision.Topology.NerveConnectivity
