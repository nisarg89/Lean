import FairDivision.Topology.NerveConnectivity.FiniteConeRelativeExtension
import FairDivision.Topology.NerveConnectivity.FiniteConeNaturality

/-!
# Relative cone extension in the original source coordinates

A map on the original complex and a compatible map on an overlap cone
extend together across the larger cone. The base restriction is stated
in the original complex's realization, avoiding repeated Option-vertex
coordinate changes in the binary gluing theorem.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Extend an original source map while preserving a prescribed
subcone filling. -/
theorem exists_finiteCone_relativeMapExtension
    {V : Type u} [Fintype V] [Nonempty V]
    {X : Type v} [TopologicalSpace X]
    (K I : PreAbstractSimplicialComplex V) (hIK : I ≤ K)
    (k : ℕ)
    (hKdim : ∀ F : Finset V, F ∈ K → F.card ≤ k + 1)
    (hX : NullConnectedSpace k X)
    (f : C(simplicialRealization K, X))
    (gI : C(simplicialRealization (finiteConeComplex I), X))
    (hcomp : ∀ w : simplicialRealization I,
      gI (finiteConeBaseMap I w) =
        f ⟨w.1, (simplicialRealization_mono hIK) w.2⟩) :
    ∃ g : C(simplicialRealization (finiteConeComplex K), X),
      (∀ w : simplicialRealization K,
        g (finiteConeBaseMap K w) = f w) ∧
      (∀ w : simplicialRealization (finiteConeComplex I),
        g ((finiteConeInclusion hIK) w) = gI w) := by
  let eK := finiteConeBaseRealizationHomeomorph K
  let eI := finiteConeBaseRealizationHomeomorph I
  let fBase : C(simplicialRealization (finiteConeBaseComplex K), X) :=
    f.comp (eK.symm : C(simplicialRealization (finiteConeBaseComplex K),
      simplicialRealization K))
  have hbaseComp : ∀ (w : stdSimplex ℝ (Option V))
      (hwB : w ∈ simplicialRealization (finiteConeBaseComplex K))
      (hwI : w ∈ simplicialRealization (finiteConeComplex I)),
      fBase ⟨w, hwB⟩ = gI ⟨w, hwI⟩ := by
    intro w hwB hwI
    have hwPair : w ∈ simplicialRealization
        (finiteConeBaseComplex K ⊓ finiteConeComplex I) :=
      ⟨hwB, hwI⟩
    rw [finiteConeBase_inf_cone hIK] at hwPair
    let q : simplicialRealization I := eI.symm ⟨w, hwPair⟩
    have hEqI : finiteConeBaseMap I q = ⟨w, hwI⟩ := by
      apply Subtype.ext
      change (eI q).1 = w
      exact congrArg Subtype.val (eI.apply_symm_apply ⟨w, hwPair⟩)
    have hEqK : eK.symm ⟨w, hwB⟩ =
        ⟨q.1, (simplicialRealization_mono hIK) q.2⟩ := by
      apply eK.injective
      calc
        eK (eK.symm ⟨w, hwB⟩) = ⟨w, hwB⟩ := eK.apply_symm_apply _
        _ = eK ⟨q.1, (simplicialRealization_mono hIK) q.2⟩ := by
          apply Subtype.ext
          have heq : (eI q).1 = w :=
            congrArg Subtype.val (eI.apply_symm_apply ⟨w, hwPair⟩)
          exact heq.symm
    change f (eK.symm ⟨w, hwB⟩) = gI ⟨w, hwI⟩
    rw [hEqK, ← hEqI]
    exact (hcomp q).symm
  obtain ⟨g, hBase, hI⟩ := exists_finiteCone_relativeExtension
    K I hIK k hKdim hX fBase gI hbaseComp
  refine ⟨g, ?_, ?_⟩
  · intro w
    have h := hBase (eK w)
    change g (finiteConeBaseMap K w) = f (eK.symm (eK w)) at h
    simpa using h
  · intro w
    exact hI w

end FairDivision.Topology.NerveConnectivity
