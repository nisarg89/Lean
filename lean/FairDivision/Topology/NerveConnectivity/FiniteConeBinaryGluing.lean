import FairDivision.Topology.NerveConnectivity.FiniteConeRelativeMapExtension
import FairDivision.Topology.NerveConnectivity.FiniteConeExtension
import FairDivision.Topology.NerveConnectivity.FiniteConeBinaryPaste

/-!
# Nullhomotopy from a low-dimensional binary source cover

This is the combinatorial heart of positive-dimensional open-cover
gluing. A sphere source is subdivided into two subcomplexes whose maps
land in the respective target chambers. A cone filling of their
lower-dimensional overlap is extended across each chamber cone, then
the resulting maps are pasted and contracted.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- A source map subordinate to a binary target cover is nullhomotopic
when its chamber and overlap source dimensions match their target
connectivity bounds. -/
theorem finiteBinarySource_map_nullhomotopic
    {V : Type u} [Fintype V] [Nonempty V]
    {X : Type v} [TopologicalSpace X]
    (A B : PreAbstractSimplicialComplex V)
    (k : ℕ) (hk : 1 ≤ k)
    (hAdim : ∀ F : Finset V, F ∈ A → F.card ≤ k + 1)
    (hBdim : ∀ F : Finset V, F ∈ B → F.card ≤ k + 1)
    (hIdim : ∀ F : Finset V, F ∈ A ⊓ B → F.card ≤ k)
    (U W : Set X)
    (hU : NullConnectedSet k U)
    (hW : NullConnectedSet k W)
    (hI : NullConnectedSet (k - 1) (U ∩ W))
    (f : C(simplicialRealization (A ⊔ B), X))
    (hfA : ∀ z : simplicialRealization A,
      f ⟨z.1, (simplicialRealization_mono le_sup_left) z.2⟩ ∈ U)
    (hfB : ∀ z : simplicialRealization B,
      f ⟨z.1, (simplicialRealization_mono le_sup_right) z.2⟩ ∈ W) :
    ∃ x : X, f.Homotopic (ContinuousMap.const _ x) := by
  let J := A ⊓ B
  have hJA : J ≤ A := inf_le_left
  have hJB : J ≤ B := inf_le_right
  let fA : C(simplicialRealization A, U) := by
    let q : C(simplicialRealization A, X) :=
      f.comp (ContinuousMap.inclusion (simplicialRealization_mono le_sup_left))
    exact ⟨fun z => ⟨q z, hfA z⟩,
      Continuous.subtype_mk q.continuous _⟩
  let fB : C(simplicialRealization B, W) := by
    let q : C(simplicialRealization B, X) :=
      f.comp (ContinuousMap.inclusion (simplicialRealization_mono le_sup_right))
    exact ⟨fun z => ⟨q z, hfB z⟩,
      Continuous.subtype_mk q.continuous _⟩
  let fI : C(simplicialRealization J, ↥(U ∩ W)) := by
    let q : C(simplicialRealization J, X) :=
      f.comp (ContinuousMap.inclusion
        (simplicialRealization_mono (inf_le_left.trans le_sup_left)))
    exact ⟨fun z => ⟨q z, ⟨hfA ⟨z.1, z.2.1⟩, hfB ⟨z.1, z.2.2⟩⟩⟩,
      Continuous.subtype_mk q.continuous _⟩
  have hIdim' : ∀ F : Finset V, F ∈ J → F.card ≤ (k - 1) + 1 := by
    intro F hF
    have h := hIdim F hF
    omega
  obtain ⟨gI, hgI⟩ := exists_finiteCone_mapExtension
    J (k - 1) hIdim' hI fI
  let gIU : C(simplicialRealization (finiteConeComplex J), U) :=
    ⟨fun z => ⟨(gI z).1, (gI z).2.1⟩,
      Continuous.subtype_mk
        (continuous_subtype_val.comp gI.continuous) _⟩
  let gIW : C(simplicialRealization (finiteConeComplex J), W) :=
    ⟨fun z => ⟨(gI z).1, (gI z).2.2⟩,
      Continuous.subtype_mk
        (continuous_subtype_val.comp gI.continuous) _⟩
  have hcompA : ∀ z : simplicialRealization J,
      gIU (finiteConeBaseMap J z) =
        fA ⟨z.1, (simplicialRealization_mono hJA) z.2⟩ := by
    intro z
    apply Subtype.ext
    change (gI (finiteConeBaseMap J z)).1 = (fI z).1
    exact congrArg Subtype.val (hgI z)
  have hcompB : ∀ z : simplicialRealization J,
      gIW (finiteConeBaseMap J z) =
        fB ⟨z.1, (simplicialRealization_mono hJB) z.2⟩ := by
    intro z
    apply Subtype.ext
    change (gI (finiteConeBaseMap J z)).1 = (fI z).1
    exact congrArg Subtype.val (hgI z)
  obtain ⟨gA, hgAbase, hgAI⟩ :=
    exists_finiteCone_relativeMapExtension A J hJA k hAdim hU fA gIU hcompA
  obtain ⟨gB, hgBbase, hgBI⟩ :=
    exists_finiteCone_relativeMapExtension B J hJB k hBdim hW fB gIW hcompB
  let gAX : C(simplicialRealization (finiteConeComplex A), X) :=
    ⟨fun z => (gA z).1, continuous_subtype_val.comp gA.continuous⟩
  let gBX : C(simplicialRealization (finiteConeComplex B), X) :=
    ⟨fun z => (gB z).1, continuous_subtype_val.comp gB.continuous⟩
  have hcomp : ∀ (w : stdSimplex ℝ (Option V))
      (hwA : w ∈ simplicialRealization (finiteConeComplex A))
      (hwB : w ∈ simplicialRealization (finiteConeComplex B)),
      gAX ⟨w, hwA⟩ = gBX ⟨w, hwB⟩ := by
    intro w hwA hwB
    have hwJ : w ∈ simplicialRealization (finiteConeComplex J) := by
      have hp : w ∈ simplicialRealization
          (finiteConeComplex A ⊓ finiteConeComplex B) := ⟨hwA, hwB⟩
      rw [← finiteConeComplex_inf] at hp
      exact hp
    have hA := hgAI ⟨w, hwJ⟩
    have hB := hgBI ⟨w, hwJ⟩
    change (gA ⟨w, hwA⟩).1 = (gB ⟨w, hwB⟩).1
    calc
      (gA ⟨w, hwA⟩).1 = (gI ⟨w, hwJ⟩).1 := congrArg Subtype.val hA
      _ = (gB ⟨w, hwB⟩).1 := (congrArg Subtype.val hB).symm
  let g := finiteConeBinaryPaste A B gAX gBX hcomp
  have hbase : g.comp (finiteConeBaseMap (A ⊔ B)) = f := by
    apply ContinuousMap.ext
    intro z
    rcases z.2 with hzA | hzB
    · let zA : simplicialRealization A := ⟨z.1, hzA⟩
      have hnat := finiteConeBaseMap_natural
        (I := A) (K := A ⊔ B) le_sup_left zA
      calc
        g (finiteConeBaseMap (A ⊔ B) z) =
            gAX (finiteConeBaseMap A zA) := by
              rw [← hnat]
              exact finiteConeBinaryPaste_left A B gAX gBX hcomp
                (finiteConeBaseMap A zA)
        _ = f z := by
          exact congrArg Subtype.val (hgAbase zA)
    · let zB : simplicialRealization B := ⟨z.1, hzB⟩
      have hnat := finiteConeBaseMap_natural
        (I := B) (K := A ⊔ B) le_sup_right zB
      calc
        g (finiteConeBaseMap (A ⊔ B) z) =
            gBX (finiteConeBaseMap B zB) := by
              rw [← hnat]
              exact finiteConeBinaryPaste_right A B gAX gBX hcomp
                (finiteConeBaseMap B zB)
        _ = f z := by
          exact congrArg Subtype.val (hgBbase zB)
  refine ⟨g (finiteConeApex (A ⊔ B)), ?_⟩
  simpa [hbase] using finiteConeMap_base_nullhomotopic (A ⊔ B) g

end FairDivision.Topology.NerveConnectivity
