import FairDivision.Topology.VariableDummyFaces
import FairDivision.Topology.VariableDummyProfiles
import FairDivision.Finite.DisjointReserves
import FairDivision.Finite.BundlesToAllocation
import FairDivision.Finite.OrderedPrefix

/-!
# Numerical face criterion for the variable-size auxiliary complex

The dummy labels do not belong to vertices.  A family is a face exactly when
its real pools are disjoint across positions and the sum of its maximal dummy
counts fits in the available dummy stock.  The reverse implication explicitly
constructs compatible labeled representatives.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open FairDivision.Finite

private theorem profile_real_subset_pool {k m : ℕ} {r c : Fin k → ℕ}
    {D : Finset (Fin m)}
    (S : Finset (VariableUnlabeledVertex k m D r c))
    {p : VariableUnlabeledVertex k m D r c} (hp : p ∈ S) (i : Fin k) :
    (p.1 i).1 ⊆ variableRealPool S i := by
  classical
  intro g hg
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, hg⟩

private theorem realPool_disjoint_dummy {k m : ℕ} {r c : Fin k → ℕ}
    {D : Finset (Fin m)}
    (S : Finset (VariableUnlabeledVertex k m D r c)) (i : Fin k) :
    Disjoint (variableRealPool S i) D := by
  classical
  apply Finset.disjoint_left.mpr
  intro g hg hd
  obtain ⟨p, hp, hgp⟩ := (Finset.mem_filter.mp hg).2
  exact (Finset.disjoint_left.mp
    (variableProfile_real_disjoint_dummy p i)) hgp hd

/-- The converse to `variableFace_necessary`: numerical reserves can be
labeled consistently across every vertex of the family. -/
theorem variableFace_sufficient {k m : ℕ} {r c : Fin k → ℕ}
    {D : Finset (Fin m)}
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hReal : ∀ i j : Fin k, i ≠ j →
      Disjoint (variableRealPool S i) (variableRealPool S j))
    (hDummy : (∑ i : Fin k, variableDummyMax S i) ≤ D.card) :
    IsVariableUnlabeledFamily S := by
  classical
  obtain ⟨R, hRes, hRPair⟩ :=
    exists_disjoint_reserves (Finset.univ : Finset (Fin k)) D
      (variableDummyMax S) (by simpa using hDummy)
  have hR (i : Fin k) :
      R i ⊆ D ∧ (R i).card = variableDummyMax S i :=
    hRes i (Finset.mem_univ i)
  have hMaxCap (i : Fin k) : variableDummyMax S i ≤ c i := by
    unfold variableDummyMax
    apply Finset.sup_le
    intro p hp
    exact variableProfile_dummy_le_cap p i
  have hLargeDisj (i j : Fin k) (hij : i ≠ j) :
      Disjoint (variableRealPool S i ∪ R i)
        (variableRealPool S j ∪ R j) := by
    apply Finset.disjoint_left.mpr
    intro g hgi hgj
    rcases Finset.mem_union.mp hgi with hgi | hgi
    · rcases Finset.mem_union.mp hgj with hgj | hgj
      · exact (Finset.disjoint_left.mp (hReal i j hij)) hgi hgj
      · exact (Finset.disjoint_left.mp (realPool_disjoint_dummy S i))
          hgi ((hR j).1 hgj)
    · rcases Finset.mem_union.mp hgj with hgj | hgj
      · exact (Finset.disjoint_left.mp (realPool_disjoint_dummy S j))
          hgj ((hR i).1 hgi)
      · exact (Finset.disjoint_left.mp
          (hRPair (Finset.mem_univ i) (Finset.mem_univ j) hij)) hgi hgj
  have hBound (p : S) (i : Fin k) : (p.1.1 i).2 ≤ (R i).card := by
    calc
      (p.1.1 i).2 ≤ variableDummyMax S i := by
        exact Finset.le_sup (f := fun q : VariableUnlabeledVertex k m D r c =>
          (q.1 i).2) p.2
      _ = (R i).card := (hR i).2.symm
  let Q (p : S) (i : Fin k) : Finset (Fin m) :=
    orderedPrefix (R i) _ (hBound p i)
  have hQ (p : S) (i : Fin k) :
      Q p i ⊆ R i ∧ (Q p i).card = (p.1.1 i).2 :=
    orderedPrefix_spec (R i) _ (hBound p i)
  have hQsubD (p : S) (i : Fin k) : Q p i ⊆ D :=
    (hQ p i).1.trans (hR i).1
  let B (p : S) (i : Fin k) : Finset (Fin m) :=
    (p.1.1 i).1 ∪ Q p i
  have hBsub (p : S) (i : Fin k) :
      B p i ⊆ variableRealPool S i ∪ R i := by
    apply Finset.union_subset
    · exact (profile_real_subset_pool S p.2 i).trans Finset.subset_union_left
    · exact (hQ p i).1.trans Finset.subset_union_right
  have hCross (p q : S) (i j : Fin k) (hij : i ≠ j) :
      Disjoint (B p i) (B q j) :=
    (hLargeDisj i j hij).mono (hBsub p i) (hBsub q j)
  have hBreal (p : S) (i : Fin k) :
      B p i \ D = (p.1.1 i).1 := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgB, hnotD⟩ := Finset.mem_sdiff.mp hg
      rcases Finset.mem_union.mp hgB with hreal | hq
      · exact hreal
      · exact False.elim (hnotD (hQsubD p i hq))
    · intro hreal
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union.mpr (Or.inl hreal),
          fun hd => (Finset.disjoint_left.mp
            (variableProfile_real_disjoint_dummy p.1 i)) hreal hd⟩
  have hBdummy (p : S) (i : Fin k) :
      (B p i ∩ D).card = (p.1.1 i).2 := by
    have hInter : B p i ∩ D = Q p i := by
      ext g
      constructor
      · intro hg
        obtain ⟨hgB, hd⟩ := Finset.mem_inter.mp hg
        rcases Finset.mem_union.mp hgB with hreal | hq
        · exact False.elim ((Finset.disjoint_left.mp
            (variableProfile_real_disjoint_dummy p.1 i)) hreal hd)
        · exact hq
      · intro hq
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_union.mpr (Or.inr hq), hQsubD p i hq⟩
    rw [hInter]
    exact (hQ p i).2
  have hBcard (p : S) (i : Fin k) : (B p i).card = r i := by
    have hdisj : Disjoint (p.1.1 i).1 (Q p i) :=
      (variableProfile_real_disjoint_dummy p.1 i).mono_right
        (hQsubD p i)
    rw [show B p i = (p.1.1 i).1 ∪ Q p i from rfl,
        Finset.card_union_of_disjoint hdisj, (hQ p i).2]
    exact variableProfile_card p.1 i
  let X (p : S) : VariablePartialVertex k D r c :=
    ⟨partialAllocationFromBundles (B p), by
      intro i
      rw [partialBundle_fromBundles (B p) (hCross p p) i]
      exact ⟨hBcard p i,
        (hBdummy p i).symm ▸ variableProfile_dummy_le_cap p.1 i⟩⟩
  have hXprofile (p : S) : toVariableUnlabeledVertex (X p) = p.1 := by
    apply Subtype.ext
    funext i
    change (partialBundle (X p).1 i \ D,
      (partialBundle (X p).1 i ∩ D).card) = p.1.1 i
    apply Prod.ext
    · rw [partialBundle_fromBundles (B p) (hCross p p) i]
      exact hBreal p i
    · rw [partialBundle_fromBundles (B p) (hCross p p) i]
      exact hBdummy p i
  let T : Finset (VariablePartialVertex k D r c) := S.attach.image X
  have hPoolSub (i : Fin k) :
      variablePool T i ⊆ variableRealPool S i ∪ R i := by
    intro g hg
    obtain ⟨_, x, hxT, hxg⟩ := Finset.mem_filter.mp hg
    obtain ⟨p, _, hpx⟩ := Finset.mem_image.mp hxT
    have hgb : g ∈ partialBundle x.1 i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxg⟩
    rw [← hpx] at hgb
    rw [partialBundle_fromBundles (B p) (hCross p p) i] at hgb
    exact hBsub p i hgb
  refine ⟨T, ?_, ?_⟩
  · constructor
    · intro i j hij
      exact (hLargeDisj i j hij).mono (hPoolSub i) (hPoolSub j)
    · intro i
      have hDsub : variablePool T i ∩ D ⊆ R i := by
        intro g hg
        rcases Finset.mem_union.mp (hPoolSub i (Finset.mem_inter.mp hg).1)
          with hreal | hRg
        · exact False.elim ((Finset.disjoint_left.mp
            (realPool_disjoint_dummy S i)) hreal (Finset.mem_inter.mp hg).2)
        · exact hRg
      calc
        (variablePool T i ∩ D).card ≤ (R i).card := Finset.card_le_card hDsub
        _ = variableDummyMax S i := (hR i).2
        _ ≤ c i := hMaxCap i
  · calc
      T.image toVariableUnlabeledVertex =
          S.attach.image (toVariableUnlabeledVertex ∘ X) :=
        Finset.image_image
      _ = S.attach.image Subtype.val := by
        apply Finset.image_congr
        intro p _
        exact hXprofile p
      _ = S := Finset.attach_image_val

/-- The corrected manuscript's exact criterion for a face in the
unlabeled-dummy auxiliary complex. -/
theorem variableFace_iff {k m : ℕ} {r c : Fin k → ℕ}
    {D : Finset (Fin m)}
    (S : Finset (VariableUnlabeledVertex k m D r c)) :
    IsVariableUnlabeledFamily S ↔
      (∀ i j : Fin k, i ≠ j →
        Disjoint (variableRealPool S i) (variableRealPool S j)) ∧
        (∑ i : Fin k, variableDummyMax S i) ≤ D.card := by
  constructor
  · exact variableFace_necessary S
  · intro h
    exact variableFace_sufficient S h.1 h.2

end FairDivision.Topology
