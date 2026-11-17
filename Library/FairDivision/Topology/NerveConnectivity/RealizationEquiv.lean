import FairDivision.Topology.NerveConnectivity.SimplicialCover

/-!
# Realization transport along a vertex equivalence

An equivalence of finite vertex sets that carries faces in both directions
induces a homeomorphism of their probability-simplex realizations. This is
the common topological bridge needed when an induction step removes items
or dummy coordinates and changes the type of vertices.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Every positive weight in a simplex pushforward comes from a positive
source weight. -/
theorem finiteSimplexSupport_map_subset {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (f : V → W) (lot : stdSimplex ℝ V) :
    FairDivision.Topology.finiteSimplexSupport (stdSimplex.map f lot) ⊆
      (FairDivision.Topology.finiteSimplexSupport lot).image f := by
  classical
  intro w hw
  have hpos : 0 < (stdSimplex.map f lot).1 w :=
    (Finset.mem_filter.mp hw).2
  change 0 < FunOnFinite.linearMap ℝ ℝ f lot.1 w at hpos
  rw [FunOnFinite.linearMap_apply_apply] at hpos
  obtain ⟨v, hv, hvpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun v _ => lot.2.1 v)).mp hpos
  exact Finset.mem_image.mpr
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvpos⟩,
      (Finset.mem_filter.mp hv).2⟩

/-- A face-preserving vertex equivalence induces a homeomorphism of finite
simplicial realizations. -/
noncomputable def realizationHomeomorphOfVertexEquiv
    {V : Type u} {W : Type v} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W)
    (e : V ≃ W)
    (hForward : ∀ S : Finset V, S ∈ K → S.image e ∈ L)
    (hBackward : ∀ T : Finset W, T ∈ L → T.image e.symm ∈ K) :
    (simplicialRealization K) ≃ₜ (simplicialRealization L) where
  toFun x := ⟨stdSimplex.map e x.1, by
    have hx : FairDivision.Topology.finiteSimplexSupport x.1 ∈ K := x.2
    exact (L.isRelLowerSet_faces
      (hForward (FairDivision.Topology.finiteSimplexSupport x.1) hx)).2
        (finiteSimplexSupport_map_subset e x.1)
        (FairDivision.Topology.finiteSimplexSupport_nonempty _)⟩
  invFun y := ⟨stdSimplex.map e.symm y.1, by
    have hy : FairDivision.Topology.finiteSimplexSupport y.1 ∈ L := y.2
    exact (K.isRelLowerSet_faces
      (hBackward (FairDivision.Topology.finiteSimplexSupport y.1) hy)).2
        (finiteSimplexSupport_map_subset e.symm y.1)
        (FairDivision.Topology.finiteSimplexSupport_nonempty _)⟩
  left_inv x := by
    apply Subtype.ext
    calc
      stdSimplex.map e.symm (stdSimplex.map e x.1) =
          stdSimplex.map (e.symm ∘ e) x.1 :=
        stdSimplex.map_comp_apply e e.symm x.1
      _ = stdSimplex.map id x.1 := by
        congr 1
        funext v
        exact e.symm_apply_apply v
      _ = x.1 := stdSimplex.map_id_apply x.1
  right_inv y := by
    apply Subtype.ext
    calc
      stdSimplex.map e (stdSimplex.map e.symm y.1) =
          stdSimplex.map (e ∘ e.symm) y.1 :=
        stdSimplex.map_comp_apply e.symm e y.1
      _ = stdSimplex.map id y.1 := by
        congr 1
        funext w
        exact e.apply_symm_apply w
      _ = y.1 := stdSimplex.map_id_apply y.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (stdSimplex.continuous_map e).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (stdSimplex.continuous_map e.symm).comp continuous_subtype_val


/-- Pushforward fixes a simplex if the vertex map fixes its positive support. -/
theorem finiteSimplexMap_eq_self_of_support_fixed {V : Type u} [Fintype V]
    (f : V → V) (lot : stdSimplex ℝ V)
    (hFixed : ∀ v ∈ FairDivision.Topology.finiteSimplexSupport lot,
      f v = v) :
    stdSimplex.map f lot = lot := by
  classical
  apply Subtype.ext
  funext q
  change (FunOnFinite.linearMap ℝ ℝ f lot.1) q = lot.1 q
  rw [FunOnFinite.linearMap_apply_apply]
  calc
    (Finset.univ.filter (fun v : V => f v = q)).sum lot.1 =
        (Finset.univ.filter (fun v : V => v = q)).sum lot.1 := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ FairDivision.Topology.finiteSimplexSupport lot
      · rw [hFixed v hv]
      · have hz : lot.1 v = 0 := by
          have hnot : ¬ 0 < lot.1 v :=
            fun h => hv ((FairDivision.Topology.mem_finiteSimplexSupport_iff
              lot v).2 h)
          exact le_antisymm (le_of_not_gt hnot) (lot.2.1 v)
        simp [hz]
    _ = lot.1 q := by
      have hfilter : Finset.univ.filter (fun v : V => v = q) = {q} := by
        ext v
        simp
      rw [hfilter]
      simp

/-- Face-preserving vertex maps that are inverse on the active faces give
homeomorphic realizations. Their behavior on unused ambient vertices is
irrelevant, which is essential for stock-restricted induction steps. -/
noncomputable def realizationHomeomorphOfVertexMaps
    {V : Type u} {W : Type v} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W)
    (f : V → W) (g : W → V)
    (hForward : ∀ S : Finset V, S ∈ K → S.image f ∈ L)
    (hBackward : ∀ T : Finset W, T ∈ L → T.image g ∈ K)
    (hgf : ∀ S : Finset V, S ∈ K → ∀ v ∈ S, g (f v) = v)
    (hfg : ∀ T : Finset W, T ∈ L → ∀ w ∈ T, f (g w) = w) :
    (simplicialRealization K) ≃ₜ (simplicialRealization L) where
  toFun x := ⟨stdSimplex.map f x.1, by
    have hx : FairDivision.Topology.finiteSimplexSupport x.1 ∈ K := x.2
    exact (L.isRelLowerSet_faces
      (hForward (FairDivision.Topology.finiteSimplexSupport x.1) hx)).2
        (finiteSimplexSupport_map_subset f x.1)
        (FairDivision.Topology.finiteSimplexSupport_nonempty _)⟩
  invFun y := ⟨stdSimplex.map g y.1, by
    have hy : FairDivision.Topology.finiteSimplexSupport y.1 ∈ L := y.2
    exact (K.isRelLowerSet_faces
      (hBackward (FairDivision.Topology.finiteSimplexSupport y.1) hy)).2
        (finiteSimplexSupport_map_subset g y.1)
        (FairDivision.Topology.finiteSimplexSupport_nonempty _)⟩
  left_inv x := by
    apply Subtype.ext
    calc
      stdSimplex.map g (stdSimplex.map f x.1) =
          stdSimplex.map (g ∘ f) x.1 :=
        stdSimplex.map_comp_apply f g x.1
      _ = x.1 := finiteSimplexMap_eq_self_of_support_fixed
        (g ∘ f) x.1 (hgf (FairDivision.Topology.finiteSimplexSupport x.1) x.2)
  right_inv y := by
    apply Subtype.ext
    calc
      stdSimplex.map f (stdSimplex.map g y.1) =
          stdSimplex.map (f ∘ g) y.1 :=
        stdSimplex.map_comp_apply g f y.1
      _ = y.1 := finiteSimplexMap_eq_self_of_support_fixed
        (f ∘ g) y.1 (hfg (FairDivision.Topology.finiteSimplexSupport y.1) y.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (stdSimplex.continuous_map f).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (stdSimplex.continuous_map g).comp continuous_subtype_val

end FairDivision.Topology.NerveConnectivity
