import FairDivision.Topology.VariableDummyFaceCriterion
import FairDivision.Finite.DisjointReserves
import FairDivision.Finite.BundlesToAllocation

/-!
# Constructing a variable-size auxiliary vertex from a profile

This construction is used by the connectivity induction's vertex operations.
It chooses disjoint labeled dummy reserves only as a witness that the proposed
unlabeled real bundles and dummy counts form a valid vertex.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open FairDivision.Finite

/-- Disjoint real bundles with valid sizes and aggregate dummy budget define
an auxiliary vertex with exactly the prescribed unlabeled profile. -/
theorem exists_variable_vertex_of_profile {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (F : Fin k → Finset (Fin m)) (dcount : Fin k → ℕ)
    (hFD : ∀ i, Disjoint (F i) D)
    (hFPair : ∀ i j : Fin k, i ≠ j → Disjoint (F i) (F j))
    (hCard : ∀ i, (F i).card + dcount i = r i)
    (hCap : ∀ i, dcount i ≤ c i)
    (hBudget : (∑ i : Fin k, dcount i) ≤ D.card) :
    ∃ p : VariableUnlabeledVertex k m D r c,
      ∀ i : Fin k, p.1 i = (F i, dcount i) := by
  classical
  obtain ⟨R, hRes, hRPair⟩ :=
    exists_disjoint_reserves (Finset.univ : Finset (Fin k))
      D dcount (by simpa using hBudget)
  have hR (i : Fin k) : R i ⊆ D ∧ (R i).card = dcount i :=
    hRes i (Finset.mem_univ i)
  let B (i : Fin k) : Finset (Fin m) := F i ∪ R i
  have hPair (i j : Fin k) (hij : i ≠ j) :
      Disjoint (B i) (B j) := by
    apply Finset.disjoint_left.mpr
    intro g hgi hgj
    rcases Finset.mem_union.mp hgi with hFi | hRi
    · rcases Finset.mem_union.mp hgj with hFj | hRj
      · exact (Finset.disjoint_left.mp (hFPair i j hij)) hFi hFj
      · exact (Finset.disjoint_left.mp (hFD i)) hFi ((hR j).1 hRj)
    · rcases Finset.mem_union.mp hgj with hFj | hRj
      · exact (Finset.disjoint_left.mp (hFD j)) hFj ((hR i).1 hRi)
      · exact (Finset.disjoint_left.mp
          (hRPair (Finset.mem_univ i) (Finset.mem_univ j) hij)) hRi hRj
  have hBcard (i : Fin k) : (B i).card = r i := by
    have hdisj : Disjoint (F i) (R i) :=
      (hFD i).mono_right (hR i).1
    rw [show B i = F i ∪ R i from rfl,
      Finset.card_union_of_disjoint hdisj, (hR i).2]
    exact hCard i
  have hBreal (i : Fin k) : B i \ D = F i := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgB, hnotD⟩ := Finset.mem_sdiff.mp hg
      rcases Finset.mem_union.mp hgB with hF | hgR
      · exact hF
      · exact False.elim (hnotD ((hR i).1 hgR))
    · intro hF
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union.mpr (Or.inl hF),
          fun hd => (Finset.disjoint_left.mp (hFD i)) hF hd⟩
  have hBdummy (i : Fin k) : B i ∩ D = R i := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgB, hd⟩ := Finset.mem_inter.mp hg
      rcases Finset.mem_union.mp hgB with hF | hR
      · exact False.elim ((Finset.disjoint_left.mp (hFD i)) hF hd)
      · exact hR
    · intro hgR
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union.mpr (Or.inr hgR), (hR i).1 hgR⟩
  let X : VariablePartialVertex k D r c :=
    ⟨partialAllocationFromBundles B, by
      intro i
      rw [partialBundle_fromBundles B hPair i]
      exact ⟨hBcard i, by
        rw [hBdummy i, (hR i).2]
        exact hCap i⟩⟩
  refine ⟨toVariableUnlabeledVertex X, ?_⟩
  intro i
  change (partialBundle X.1 i \ D,
    (partialBundle X.1 i ∩ D).card) = (F i, dcount i)
  rw [partialBundle_fromBundles B hPair i, hBreal i,
    hBdummy i, (hR i).2]

end FairDivision.Topology
