import FairDivision.Topology.NerveConnectivity.BarycentricSubdivision
import FairDivision.Topology.FiniteSimplexRestriction
import FairDivision.Topology.FiniteSimplexSegment

/-!
# Projection from a barycentric open star onto its subcomplex

On the open star, the total weight on vertices from the subcomplex is positive.
Discarding other weights and renormalizing yields a continuous map to the
subcomplex realization. This is the map underlying the regular-neighborhood
deformation retraction.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- Barycentric vertices corresponding to faces of `K`. -/
noncomputable def barycentricFaceVertices {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (· ∈ K)

@[simp] theorem mem_barycentricFaceVertices_iff {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (F : Finset V) :
    F ∈ barycentricFaceVertices K ↔ F ∈ K := by
  classical
  simp [barycentricFaceVertices]

/-- The open-star witness makes the subcomplex weight strictly positive. -/
theorem barycentricOpenStar_mass_pos {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (w : stdSimplex ℝ (Finset V))
    (hw : w ∈ barycentricOpenStar K) :
    0 < FairDivision.Topology.finiteSimplexMass
      (barycentricFaceVertices K) w := by
  obtain ⟨F, hF, hpos⟩ := hw
  exact FairDivision.Topology.finiteSimplexMass_pos_of_mem
    (barycentricFaceVertices K) w
    ((mem_barycentricFaceVertices_iff K F).2 hF) hpos

/-- The part of `|sd L|` lying in the open star of `K`. -/
def barycentricStarDomain {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    Set (stdSimplex ℝ (Finset V)) :=
  simplicialRealization (barycentricSubdivision L) ∩ barycentricOpenStar K

/-- Restriction to `K` takes every point of its open star in `|sd L|`
continuously into `|sd K|`. -/
noncomputable def barycentricStarProject {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    C(barycentricStarDomain K L,
      simplicialRealization (barycentricSubdivision K)) := by
  classical
  let P := barycentricFaceVertices K
  let q : barycentricStarDomain K L →
      {w : stdSimplex ℝ (Finset V) //
        0 < FairDivision.Topology.finiteSimplexMass P w} :=
    fun z => ⟨z.1, barycentricOpenStar_mass_pos K z.1 z.2.2⟩
  have hq : Continuous q := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hmem : ∀ z : barycentricStarDomain K L,
      FairDivision.Topology.finiteSimplexRestrict P (q z) ∈
        simplicialRealization (barycentricSubdivision K) := by
    intro z
    let w' := FairDivision.Topology.finiteSimplexRestrict P (q z)
    have hsub := FairDivision.Topology.finiteSimplexRestrict_support_subset P (q z)
    have hw : FairDivision.Topology.finiteSimplexSupport z.1 ∈
        barycentricSubdivision L := z.2.1
    change FairDivision.Topology.finiteSimplexSupport w' ∈
      barycentricSubdivision K
    refine ⟨FairDivision.Topology.finiteSimplexSupport_nonempty w', ?_, ?_⟩
    · intro F hF
      exact (mem_barycentricFaceVertices_iff K F).1
        ((hsub F hF).2)
    · exact hw.2.2.mono (by
        intro F hF
        exact (hsub F hF).1)
  refine ⟨fun z => ⟨FairDivision.Topology.finiteSimplexRestrict P (q z), hmem z⟩, ?_⟩
  apply Continuous.subtype_mk
  exact (FairDivision.Topology.finiteSimplexRestrict_continuous P).comp hq

/-- Include the subdivided subcomplex in its open star inside a larger
subdivided complex. -/
def barycentricStarInclusion {V : Type v} [Fintype V]
    {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L) :
    C(simplicialRealization (barycentricSubdivision K),
      barycentricStarDomain K L) := by
  refine ⟨fun z => ⟨z.1, ?_⟩, ?_⟩
  · exact ⟨simplicialRealization_mono (barycentricSubdivision_mono hKL) z.2,
      barycentricRealization_subset_openStar K z.2⟩
  · exact Continuous.subtype_mk continuous_subtype_val _

/-- The open-star projection fixes every point of the subdivided subcomplex. -/
theorem barycentricStarProject_comp_inclusion {V : Type v} [Fintype V]
    {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L) :
    (barycentricStarProject K L).comp (barycentricStarInclusion hKL) =
      ContinuousMap.id (simplicialRealization (barycentricSubdivision K)) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change FairDivision.Topology.finiteSimplexRestrict
    (barycentricFaceVertices K)
    ⟨z.1, barycentricOpenStar_mass_pos K z.1
      (barycentricRealization_subset_openStar K z.2)⟩ = z.1
  apply FairDivision.Topology.finiteSimplexRestrict_eq_self
  intro F hF
  exact (mem_barycentricFaceVertices_iff K F).2 (z.2.2.1 F hF)

/-- Linear interpolation from a point in the open star to its normalized
projection stays inside the same open star. -/
noncomputable def barycentricStarSegment {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V)
    (z : barycentricStarDomain K L) (t : I) :
    barycentricStarDomain K L := by
  let P := barycentricFaceVertices K
  let q : {w : stdSimplex ℝ (Finset V) //
      0 < FairDivision.Topology.finiteSimplexMass P w} :=
    ⟨z.1, barycentricOpenStar_mass_pos K z.1 z.2.2⟩
  let y := FairDivision.Topology.finiteSimplexRestrict P q
  let x := z.1
  let s := FairDivision.Topology.finiteSimplexSegment x y t
  have hyx : FairDivision.Topology.finiteSimplexSupport y ⊆
      FairDivision.Topology.finiteSimplexSupport x := by
    intro F hF
    exact (FairDivision.Topology.finiteSimplexRestrict_support_subset P q F hF).1
  have hsupport : FairDivision.Topology.finiteSimplexSupport s ⊆
      FairDivision.Topology.finiteSimplexSupport x :=
    FairDivision.Topology.finiteSimplexSegment_support_subset_left x y t hyx
  have hreal : s ∈ simplicialRealization (barycentricSubdivision L) := by
    change FairDivision.Topology.finiteSimplexSupport s ∈ barycentricSubdivision L
    exact ((barycentricSubdivision L).isRelLowerSet_faces z.2.1).2
      hsupport (FairDivision.Topology.finiteSimplexSupport_nonempty s)
  have hstar : s ∈ barycentricOpenStar K := by
    obtain ⟨F, hFK, hFw⟩ := z.2.2
    have hFP : F ∈ P := (mem_barycentricFaceVertices_iff K F).2 hFK
    have hyF : 0 < y.1 F :=
      (FairDivision.Topology.finiteSimplexRestrict_pos_iff P q F).2 ⟨hFP, hFw⟩
    exact ⟨F, hFK,
      FairDivision.Topology.finiteSimplexSegment_pos_of_pos x y t F hFw hyF⟩
  exact ⟨s, ⟨hreal, hstar⟩⟩

/-- The pointwise open-star deformation is jointly continuous in time
and its starting point. -/
theorem barycentricStarSegment_continuous {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    Continuous (fun z : I × barycentricStarDomain K L =>
      barycentricStarSegment K L z.2 z.1) := by
  have ht : Continuous (fun z : I × barycentricStarDomain K L => z.1) :=
    continuous_fst
  have hx : Continuous (fun z : I × barycentricStarDomain K L => z.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hy : Continuous (fun z : I × barycentricStarDomain K L =>
      ((barycentricStarProject K L) z.2).1) :=
    continuous_subtype_val.comp
      ((barycentricStarProject K L).continuous.comp continuous_snd)
  have hcore : Continuous (fun z : I × barycentricStarDomain K L =>
      FairDivision.Topology.finiteSimplexSegment z.2.1
        ((barycentricStarProject K L) z.2).1 z.1) :=
    FairDivision.Topology.finiteSimplexSegment_continuous.comp
      (ht.prodMk (hx.prodMk hy))
  apply Continuous.subtype_mk
  convert hcore using 1
  funext z
  rfl

/-- The open star deformation retracts onto the subdivided subcomplex. -/
noncomputable def barycentricStarHomotopy {V : Type v} [Fintype V]
    {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L) :
    (ContinuousMap.id (barycentricStarDomain K L)).Homotopy
      ((barycentricStarInclusion hKL).comp (barycentricStarProject K L)) where
  toFun z := barycentricStarSegment K L z.2 z.1
  continuous_toFun := barycentricStarSegment_continuous K L
  map_zero_left := by
    intro z
    apply Subtype.ext
    change FairDivision.Topology.finiteSimplexSegment z.1
      ((barycentricStarProject K L) z).1 0 = z.1
    simp
  map_one_left := by
    intro z
    apply Subtype.ext
    change FairDivision.Topology.finiteSimplexSegment z.1
      ((barycentricStarProject K L) z).1 1 =
        ((barycentricStarProject K L) z).1
    simp

/-- The deformation fixes the subdivided subcomplex at every time. -/
theorem barycentricStarHomotopy_fixed {V : Type v} [Fintype V]
    {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L)
    (z : simplicialRealization (barycentricSubdivision K)) (t : I) :
    barycentricStarHomotopy hKL
      (t, (barycentricStarInclusion hKL) z) =
      (barycentricStarInclusion hKL) z := by
  apply Subtype.ext
  have hp := congrArg (fun f : C(simplicialRealization (barycentricSubdivision K),
      simplicialRealization (barycentricSubdivision K)) => f z)
    (barycentricStarProject_comp_inclusion hKL)
  change (barycentricStarProject K L) ((barycentricStarInclusion hKL) z) = z at hp
  change FairDivision.Topology.finiteSimplexSegment z.1
    ((barycentricStarProject K L) ((barycentricStarInclusion hKL) z)).1 t = z.1
  rw [hp]
  simp

end FairDivision.Topology.NerveConnectivity
