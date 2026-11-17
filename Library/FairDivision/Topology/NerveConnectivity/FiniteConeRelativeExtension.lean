import FairDivision.Topology.NerveConnectivity.FiniteConeIntersection
import FairDivision.Topology.NerveConnectivity.FiniteCellExtension
import FairDivision.Topology.NerveConnectivity.SimplicialCoverPasteRestrictions

/-!
# Extending a chamber map while preserving an overlap-cone filling

A map prescribed on the base of a finite cone and on a subcone extends
over the whole cone if the prescriptions agree on their intersection
and the target is sufficiently connected. The theorem records both
restriction equations for subsequent binary pasting.
-/

set_option autoImplicit false

open scoped Topology

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Extend a compatible base map and subcone map over a larger cone. -/
theorem exists_finiteCone_relativeExtension
    {V : Type u} [Fintype V]
    {X : Type v} [TopologicalSpace X]
    (K I : PreAbstractSimplicialComplex V) (hIK : I ≤ K)
    (k : ℕ)
    (hKdim : ∀ F : Finset V, F ∈ K → F.card ≤ k + 1)
    (hX : NullConnectedSpace k X)
    (fBase : C(simplicialRealization (finiteConeBaseComplex K), X))
    (gI : C(simplicialRealization (finiteConeComplex I), X))
    (hcomp : ∀ (w : stdSimplex ℝ (Option V))
      (hwB : w ∈ simplicialRealization (finiteConeBaseComplex K))
      (hwI : w ∈ simplicialRealization (finiteConeComplex I)),
      fBase ⟨w, hwB⟩ = gI ⟨w, hwI⟩) :
    ∃ g : C(simplicialRealization (finiteConeComplex K), X),
      (∀ w : simplicialRealization (finiteConeBaseComplex K),
        g ⟨w.1, (simplicialRealization_mono
          (finiteConeBaseComplex_le K)) w.2⟩ = fBase w) ∧
      (∀ w : simplicialRealization (finiteConeComplex I),
        g ⟨w.1, (simplicialRealization_mono
          (finiteConeComplex_mono hIK)) w.2⟩ = gI w) := by
  let A := finiteConeBaseComplex K ⊔ finiteConeComplex I
  have hAK : A ≤ finiteConeComplex K :=
    finiteConeBase_sup_cone_le hIK
  let q : C(simplicialRealization A, X) :=
    simplicialCoverPasteExact (finiteConeBaseComplex K)
      (finiteConeComplex I) fBase gI hcomp
  have hConeDim : ∀ S : Finset (Option V),
      S ∈ finiteConeComplex K → S.card ≤ k + 2 := by
    intro S hS
    have h := finiteConeComplex_card_le K (k + 1) hKdim S hS
    omega
  obtain ⟨g, hg⟩ := exists_finiteComplex_mapExtension
    (finiteConeComplex K) k hConeDim hX A hAK q
  refine ⟨g, ?_, ?_⟩
  · intro w
    have hwA : w.1 ∈ simplicialRealization A :=
      (simplicialRealization_mono le_sup_left) w.2
    calc
      g ⟨w.1, (simplicialRealization_mono
          (finiteConeBaseComplex_le K)) w.2⟩ =
          q ⟨w.1, hwA⟩ := hg ⟨w.1, hwA⟩
      _ = fBase w := simplicialCoverPaste_left
        (finiteConeBaseComplex K) (finiteConeComplex I)
        fBase gI hcomp w
  · intro w
    have hwA : w.1 ∈ simplicialRealization A :=
      (simplicialRealization_mono le_sup_right) w.2
    calc
      g ⟨w.1, (simplicialRealization_mono
          (finiteConeComplex_mono hIK)) w.2⟩ =
          q ⟨w.1, hwA⟩ := hg ⟨w.1, hwA⟩
      _ = gI w := simplicialCoverPaste_right
        (finiteConeBaseComplex K) (finiteConeComplex I)
        fBase gI hcomp w

end FairDivision.Topology.NerveConnectivity
