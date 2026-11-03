import FairDivision.Topology.NerveConnectivity.ClosedCoverPasting

/-!
# Pasting maps on a finite family of closed sets

A map on a closed base set and prescribed maps on finitely many additional
closed sets paste to one continuous map when all pairwise overlaps agree.
The exact restriction equations support orbitwise simultaneous cell
attachments.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v w

/-- A closed base set together with a finite family of pieces. -/
def closedFamilyUnion {ι : Type u} {X : Type v}
    (A : Set X) (B : ι → Set X) (S : Finset ι) : Set X :=
  A ∪ ⋃ i ∈ S, B i

@[simp] theorem mem_closedFamilyUnion_iff
    {ι : Type u} {X : Type v} (A : Set X)
    (B : ι → Set X) (S : Finset ι) (x : X) :
    x ∈ closedFamilyUnion A B S ↔
      x ∈ A ∨ ∃ i ∈ S, x ∈ B i := by
  simp [closedFamilyUnion]

/-- Adding one index forms a binary union with its corresponding piece. -/
theorem closedFamilyUnion_insert
    {ι : Type u} {X : Type v} (A : Set X)
    (B : ι → Set X) (S : Finset ι) (i : ι) :
    closedFamilyUnion A B (insert i S) =
      closedFamilyUnion A B S ∪ B i := by
  ext x
  simp only [mem_closedFamilyUnion_iff, Set.mem_union,
    Finset.mem_insert, exists_eq_or_imp]
  aesop

/-- A finite union of closed pieces with a closed base is closed. -/
theorem closedFamilyUnion_isClosed
    {ι : Type u} {X : Type v} [TopologicalSpace X]
    (A : Set X) (B : ι → Set X) (S : Finset ι)
    (hA : IsClosed A) (hB : ∀ i, IsClosed (B i)) :
    IsClosed (closedFamilyUnion A B S) := by
  unfold closedFamilyUnion
  exact hA.union (isClosed_biUnion_finset (fun i _ => hB i))

/-- Compatibility of a base map with a finite family of piece maps. -/
def ClosedFamilyCompatible
    {ι : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : ι → Set X) (S : Finset ι)
    (f : C(A, Y)) (g : ∀ i, C(B i, Y)) : Prop :=
  (∀ i ∈ S, ∀ (x : X) (hxA : x ∈ A) (hxB : x ∈ B i),
    f ⟨x, hxA⟩ = g i ⟨x, hxB⟩) ∧
  (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
    ∀ (x : X) (hxi : x ∈ B i) (hxj : x ∈ B j),
      g i ⟨x, hxi⟩ = g j ⟨x, hxj⟩)

/-- A map has the prescribed restrictions on the base and all pieces. -/
def ClosedFamilyPasteSpec
    {ι : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : ι → Set X) (S : Finset ι)
    (f : C(A, Y)) (g : ∀ i, C(B i, Y))
    (H : C(closedFamilyUnion A B S, Y)) : Prop :=
  (∀ x : A, H ⟨x.1, (mem_closedFamilyUnion_iff A B S x.1).2
    (Or.inl x.2)⟩ = f x) ∧
  (∀ (i : ι) (hi : i ∈ S) (x : B i),
    H ⟨x.1, (mem_closedFamilyUnion_iff A B S x.1).2
      (Or.inr ⟨i, hi, x.2⟩)⟩ = g i x)

/-- Compatible maps on a finite closed family paste to one continuous map,
with exact restrictions on every piece. -/
theorem exists_closedFamilyPaste
    {ι : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : ι → Set X)
    (hA : IsClosed A) (hB : ∀ i, IsClosed (B i))
    (f : C(A, Y)) (g : ∀ i, C(B i, Y))
    (S : Finset ι) (hcomp : ClosedFamilyCompatible A B S f g) :
    ∃ H : C(closedFamilyUnion A B S, Y),
      ClosedFamilyPasteSpec A B S f g H := by
  classical
  have aux : ∀ T : Finset ι,
      ClosedFamilyCompatible A B T f g →
      ∃ H : C(closedFamilyUnion A B T, Y),
        ClosedFamilyPasteSpec A B T f g H := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      have hU : closedFamilyUnion A B ∅ = A := by
        ext x
        simp [closedFamilyUnion]
      let H : C(closedFamilyUnion A B ∅, Y) :=
        f.comp ⟨fun x => ⟨x.1, by simpa [hU] using x.2⟩, by
          apply Continuous.subtype_mk
          exact continuous_subtype_val⟩
      refine ⟨H, ?_⟩
      constructor
      · intro x
        rfl
      · intro i hi
        simp at hi
    | @insert i T hi ih =>
      intro hcompT
      have hcompOld : ClosedFamilyCompatible A B T f g := by
        refine ⟨?_, ?_⟩
        · intro j hj
          exact hcompT.1 j (Finset.mem_insert_of_mem hj)
        · intro j hj l hl
          exact hcompT.2 j (Finset.mem_insert_of_mem hj)
            l (Finset.mem_insert_of_mem hl)
      obtain ⟨H, hHbase, hHpiece⟩ := ih hcompOld
      have hcompat : ∀ (x : X)
          (hxU : x ∈ closedFamilyUnion A B T) (hxi : x ∈ B i),
          H ⟨x, hxU⟩ = g i ⟨x, hxi⟩ := by
        intro x hxU hxi
        rcases (mem_closedFamilyUnion_iff A B T x).1 hxU with hxA | ⟨j, hj, hxj⟩
        · calc
            H ⟨x, hxU⟩ = f ⟨x, hxA⟩ := hHbase ⟨x, hxA⟩
            _ = g i ⟨x, hxi⟩ :=
              hcompT.1 i (Finset.mem_insert_self i T) x hxA hxi
        · have hji : j ≠ i := by
            intro h
            subst j
            exact hi hj
          calc
            H ⟨x, hxU⟩ = g j ⟨x, hxj⟩ := hHpiece j hj ⟨x, hxj⟩
            _ = g i ⟨x, hxi⟩ :=
              hcompT.2 j (Finset.mem_insert_of_mem hj) i
                (Finset.mem_insert_self i T) hji x hxj hxi
      let P : C((closedFamilyUnion A B T ∪ B i : Set X), Y) :=
        closedCoverPaste (closedFamilyUnion A B T) (B i)
          (closedFamilyUnion_isClosed A B T hA hB) (hB i)
          H (g i) hcompat
      let H' : C(closedFamilyUnion A B (insert i T), Y) :=
        P.comp ⟨fun x => ⟨x.1, by
          exact (congrArg (fun S : Set X => x.1 ∈ S)
            (closedFamilyUnion_insert A B T i)).mp x.2⟩, by
            apply Continuous.subtype_mk
            exact continuous_subtype_val⟩
      refine ⟨H', ?_⟩
      constructor
      · intro x
        change P ⟨x.1, Or.inl (Or.inl x.2)⟩ = f x
        exact (closedCoverPaste_left _ _ _ _ _ _ _
          ⟨x.1, (mem_closedFamilyUnion_iff A B T x.1).2 (Or.inl x.2)⟩).trans
          (hHbase x)
      · intro j hj x
        rcases Finset.mem_insert.mp hj with rfl | hjT
        · change P ⟨x.1, Or.inr x.2⟩ = g j x
          exact closedCoverPaste_right _ _ _ _ _ _ _ x
        · change P ⟨x.1, Or.inl
            ((mem_closedFamilyUnion_iff A B T x.1).2
              (Or.inr ⟨j, hjT, x.2⟩))⟩ = g j x
          exact (closedCoverPaste_left _ _ _ _ _ _ _
            ⟨x.1, (mem_closedFamilyUnion_iff A B T x.1).2
              (Or.inr ⟨j, hjT, x.2⟩)⟩).trans
            (hHpiece j hjT x)
  exact aux S hcomp

end FairDivision.Topology.NerveConnectivity
