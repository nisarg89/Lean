import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/-!
# Finite universal join for equivariant obstruction theory

For a finite group `G`, the complex `G^{*m}` has vertex type `Fin m × G`:
a face contains at most one vertex from each copy. Translation of all group
labels preserves the complex and acts freely on its nonempty faces. This is
the finite source in Sarkaria's Borsuk–Ulam formulation of the
Özaydın–Volovikov obstruction. The eventual transfer from a connected BF
realization to this source, and the no-map theorem for this source, still
require proofs.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- A face of `G^{*m}` uses at most one vertex from each join factor. -/
def IsUniversalJoinFace {m : ℕ} {G : Type*}
    (S : Finset (Fin m × G)) : Prop :=
  S.Nonempty ∧
    ∀ (i : Fin m) (g h : G), (i, g) ∈ S → (i, h) ∈ S → g = h

/-- The simplicial complex `G^{*m}` with one copy of `G` per factor. -/
def universalJoinComplex (m : ℕ) (G : Type*) :
    PreAbstractSimplicialComplex (Fin m × G) where
  faces := {S | IsUniversalJoinFace S}
  isRelLowerSet_faces := by
    intro S hS
    constructor
    · exact hS.1
    · intro T hTS hT
      refine ⟨hT, ?_⟩
      intro i g h hgi hhi
      exact hS.2 i g h (hTS hgi) (hTS hhi)


/-- Every face has at most one vertex per join factor, hence at most `m`
vertices. This is the finite-dimensional bound for `G^{*m}`. -/
theorem universalJoinFace_card_le {m : ℕ} {G : Type*}
    {S : Finset (Fin m × G)} (hS : IsUniversalJoinFace S) :
    S.card ≤ m := by
  classical
  have hinj : Set.InjOn (fun v : Fin m × G => v.1) (S : Set (Fin m × G)) := by
    intro v hv w hw heq
    rcases v with ⟨i, g⟩
    rcases w with ⟨j, h⟩
    dsimp at heq
    subst j
    congr 1
    exact hS.2 i g h hv hw
  have hcard := Finset.card_le_card_of_injOn
    (s := S) (t := Finset.univ) (fun v : Fin m × G => v.1)
    (by intro v hv; exact Finset.mem_univ _) hinj
  simpa using hcard

/-- Left translation on a vertex of the finite universal join. -/
def translateJoinVertex {m : ℕ} {G : Type*} [AddGroup G]
    (a : G) (v : Fin m × G) : Fin m × G :=
  (v.1, a + v.2)

/-- The vertex map is injective. -/
theorem translateJoinVertex_injective {m : ℕ} {G : Type*}
    [AddGroup G] (a : G) :
    Function.Injective (translateJoinVertex (m := m) a) := by
  intro v w h
  change (v.1, a + v.2) = (w.1, a + w.2) at h
  exact Prod.ext (Prod.mk.inj h).1 (add_left_cancel (Prod.mk.inj h).2)

/-- Translation of a finite face, one group label at a time. -/
noncomputable def translateJoinFace {m : ℕ} {G : Type*} [AddGroup G]
    (a : G) (S : Finset (Fin m × G)) : Finset (Fin m × G) := by
  classical
  exact S.image (translateJoinVertex a)

/-- Translation preserves the universal-join face condition. -/
theorem universalJoinFace_translate {m : ℕ} {G : Type*}
    [AddGroup G] {S : Finset (Fin m × G)}
    (hS : IsUniversalJoinFace S) (a : G) :
    IsUniversalJoinFace (translateJoinFace a S) := by
  classical
  constructor
  · exact hS.1.image _
  · intro i g h hgi hhi
    rcases Finset.mem_image.mp hgi with ⟨v, hv, hve⟩
    rcases Finset.mem_image.mp hhi with ⟨w, hw, hwe⟩
    have hvi : v.1 = i := congrArg (fun z : Fin m × G => z.1) hve
    have hwi : w.1 = i := congrArg (fun z : Fin m × G => z.1) hwe
    have hvw : v.2 = w.2 := by
      apply hS.2 i v.2 w.2
      · simpa only [← hvi, Prod.mk.eta] using hv
      · simpa only [← hwi, Prod.mk.eta] using hw
    have hvg : a + v.2 = g := congrArg (fun z : Fin m × G => z.2) hve
    have hwh : a + w.2 = h := congrArg (fun z : Fin m × G => z.2) hwe
    exact hvg.symm ▸ hwh.symm ▸ congrArg (a + ·) hvw

/-- No nonzero translation stabilizes a nonempty face of `G^{*m}`. -/
theorem universalJoinFace_free {m : ℕ} {G : Type*}
    [AddGroup G] {S : Finset (Fin m × G)}
    (hS : IsUniversalJoinFace S) (a : G)
    (hfixed : translateJoinFace a S = S) : a = 0 := by
  classical
  obtain ⟨v, hv⟩ := hS.1
  have htranslated : translateJoinVertex a v ∈ S := by
    rw [← hfixed]
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have heq : a + v.2 = v.2 :=
    hS.2 v.1 (a + v.2) v.2 htranslated (by simpa only [Prod.mk.eta] using hv)
  exact add_right_cancel (by simpa only [zero_add] using heq)

end FairDivision.Topology.Volovikov
