import FairDivision.Topology.AAK.ZeroFreeBipyramid

/-!
# A zero-free sign reversal produces an equivariant pole-to-pole homotopy

The explicit bipyramid normalization is followed by deformations within its
south and north cones. The resulting homotopy has exactly constant pole
endpoints. Its continuity and equivariance are proved for the literal maps;
no PL approximation, chain obstruction, or zero-count conservation statement
is assumed here.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.ZeroFreeBipyramid

open FairDivision.Topology
open FairDivision.Topology.NerveConnectivity
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [Nonempty V]

private theorem coordinate_zero_of_missing (x : Realization V) (v : Vertex V)
    (hv : v ∉ finiteSimplexSupport x.1) : x.1.1 v = 0 := by
  have hn : ¬0 < x.1.1 v := fun h => hv ((mem_finiteSimplexSupport_iff x.1 v).2 h)
  exact le_antisymm (le_of_not_gt hn) (x.1.2.1 v)

/-- A line segment to a pole stays in its closed cone. The opposite pole has
zero weight, and any missing base coordinate stays zero along the segment. -/
def conePoint (b : Bool) (x : Realization V)
    (hx : x.1.1 (pole (!b)) = 0) (t : unitInterval) : Realization V := by
  let w : stdSimplex ℝ (Vertex V) := ⟨
    fun v => (1 - t.1) * x.1.1 v + t.1 * (polePoint b).1.1 v,
    fun v => add_nonneg
      (mul_nonneg (sub_nonneg.mpr t.2.2) (x.1.2.1 v))
      (mul_nonneg t.2.1 ((polePoint b).1.2.1 v)), by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, x.1.2.2,
        (polePoint b).1.2.2, mul_one]
      ring⟩
  have hopposite : w.1 (pole (!b)) = 0 := by
    dsimp [w]
    rw [hx]
    cases b <;> simp [polePoint_coordinate]
  refine ⟨w, finiteSimplexSupport_nonempty w, ?_, ?_⟩
  · intro h
    cases b with
    | false =>
        have hp := (mem_finiteSimplexSupport_iff w (pole true)).1 h.1
        rw [show w.1 (pole true) = 0 from hopposite] at hp
        exact (lt_irrefl _) hp
    | true =>
        have hp := (mem_finiteSimplexSupport_iff w (pole false)).1 h.2
        rw [show w.1 (pole false) = 0 from hopposite] at hp
        exact (lt_irrefl _) hp
  · obtain ⟨v, hv⟩ := x.2.2.2
    have hz := coordinate_zero_of_missing x (base v) hv
    refine ⟨v, ?_⟩
    intro h
    have hp := (mem_finiteSimplexSupport_iff w (base v)).1 h
    have hw : w.1 (base v) = 0 := by
      simp [w, hz, polePoint_coordinate]
    rw [hw] at hp
    exact (lt_irrefl _) hp

@[simp] theorem conePoint_coordinate (b : Bool) (x : Realization V)
    (hx : x.1.1 (pole (!b)) = 0) (t : unitInterval) (v : Vertex V) :
    (conePoint b x hx t).1.1 v =
      (1 - t.1) * x.1.1 v + t.1 * (polePoint b).1.1 v := rfl

@[simp] theorem conePoint_zero (b : Bool) (x : Realization V)
    (hx : x.1.1 (pole (!b)) = 0) : conePoint b x hx 0 = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  simp

@[simp] theorem conePoint_one (b : Bool) (x : Realization V)
    (hx : x.1.1 (pole (!b)) = 0) : conePoint b x hx 1 = polePoint b := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  simp

/-- Joint continuity of the actual cone deformation for any continuous
family of points lying in that cone. -/
theorem conePoint_continuous
    {X : Type*} [TopologicalSpace X] (b : Bool) (f : C(X, Realization V))
    (hf : ∀ x, (f x).1.1 (pole (!b)) = 0) :
    Continuous (fun q : unitInterval × X => conePoint b (f q.2) (hf q.2) q.1) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  change Continuous (fun q : unitInterval × X =>
    (1 - q.1.1) * (f q.2).1.1 v + q.1.1 * (polePoint b).1.1 v)
  have hcoord : Continuous (fun q : unitInterval × X => (f q.2).1.1 v) :=
    (continuous_apply v).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp
        (f.continuous.comp continuous_snd)))
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hcoord).add
    ((continuous_subtype_val.comp continuous_fst).mul continuous_const)

/-- The concrete pole contraction as a bundled homotopy. -/
def coneHomotopy
    {X : Type*} [TopologicalSpace X] (b : Bool) (f : C(X, Realization V))
    (hf : ∀ x, (f x).1.1 (pole (!b)) = 0) :
    f.Homotopy (ContinuousMap.const X (polePoint b)) where
  toFun q := conePoint b (f q.2) (hf q.2) q.1
  continuous_toFun := conePoint_continuous b f hf
  map_zero_left x := conePoint_zero b (f x) (hf x)
  map_one_left x := conePoint_one b (f x) (hf x)

/-- Relabeling commutes with the actual line-segment cone deformation. -/
theorem conePoint_relabel (σ : Equiv.Perm V) (b : Bool)
    (x : Realization V) (hx : x.1.1 (pole (!b)) = 0) (t : unitInterval) :
    conePoint b (relabel σ x) (by simpa [vertexPerm] using hx) t =
      relabel σ (conePoint b x hx t) := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  change (1 - t.1) * x.1.1 ((vertexPerm σ).symm v) +
      t.1 * (polePoint b).1.1 v =
    (1 - t.1) * x.1.1 ((vertexPerm σ).symm v) +
      t.1 * (polePoint b).1.1 ((vertexPerm σ).symm v)
  have hp := congrArg (fun z : Realization V => z.1.1 v) (relabel_polePoint σ b)
  rw [show (polePoint b).1.1 ((vertexPerm σ).symm v) =
    (polePoint b).1.1 v from hp]

section SignReversal

variable {X : Type*} [TopologicalSpace X]

/-- The normalized zero-free homotopy, with time written first. -/
def normalizedHomotopyMap (H : C(X × unitInterval, V → ℝ)) (hn : ∀ q, H q ≠ 0) :
    C(unitInterval × X, Realization V) :=
  ⟨fun q => normalize ⟨H (q.2, q.1), hn (q.2, q.1)⟩,
    normalize_continuous.comp
      ((H.continuous.comp (continuous_snd.prodMk continuous_fst)).subtype_mk _)⟩

def normalizedEnd (H : C(X × unitInterval, V → ℝ)) (hn : ∀ q, H q ≠ 0)
    (t : unitInterval) : C(X, Realization V) :=
  (normalizedHomotopyMap H hn).comp ⟨fun x => (t, x), continuous_const.prodMk continuous_id⟩

def normalizedHomotopy (H : C(X × unitInterval, V → ℝ)) (hn : ∀ q, H q ≠ 0) :
    (normalizedEnd H hn 0).Homotopy (normalizedEnd H hn 1) where
  toContinuousMap := normalizedHomotopyMap H hn
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- Actual pole-to-pole homotopy forced by a hypothetical zero-free sign
reversal. The endpoint cones are explicit and stay in the same finite target. -/
def poleHomotopy (H : C(X × unitInterval, V → ℝ)) (hn : ∀ q, H q ≠ 0)
    (hneg : ∀ x v, H (x, 0) v < 0) (hpos : ∀ x v, 0 < H (x, 1) v) :
    (ContinuousMap.const X (polePoint (V := V) false)).Homotopy
      (ContinuousMap.const X (polePoint (V := V) true)) :=
  (coneHomotopy false (normalizedEnd H hn 0)
    (fun x => normalize_negative_north_zero ⟨H (x, 0), hn (x, 0)⟩ (hneg x))).symm.trans
      ((normalizedHomotopy H hn).trans
        (coneHomotopy true (normalizedEnd H hn 1)
          (fun x => normalize_positive_south_zero ⟨H (x, 1), hn (x, 1)⟩ (hpos x))))

/-- Equivariance of homotopies is a pointwise property, preserved by the
actual mathlib concatenation and time reversal. -/
def IsRelabelEquivariant {G : Type*} (action : G → X → X)
    (label : G → Equiv.Perm V) (F : unitInterval × X → Realization V) : Prop :=
  ∀ g t x, F (t, action g x) = relabel (label g) (F (t, x))

private theorem equivariant_trans
    {G : Type*} (action : G → X → X) (label : G → Equiv.Perm V)
    {f₀ f₁ f₂ : C(X, Realization V)}
    (F : f₀.Homotopy f₁) (K : f₁.Homotopy f₂)
    (hF : IsRelabelEquivariant action label F)
    (hK : IsRelabelEquivariant action label K) :
    IsRelabelEquivariant action label (F.trans K) := by
  intro g t x
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hF g _ x
  · exact hK g _ x

private theorem equivariant_symm
    {G : Type*} (action : G → X → X) (label : G → Equiv.Perm V)
    {f₀ f₁ : C(X, Realization V)} (F : f₀.Homotopy f₁)
    (hF : IsRelabelEquivariant action label F) :
    IsRelabelEquivariant action label F.symm := by
  intro g t x
  exact hF g (unitInterval.symm t) x

/-- The pole homotopy retains the full coordinate-permutation symmetry of
its input, with no freeness or obstruction premise. -/
theorem poleHomotopy_equivariant
    {G : Type*} (action : G → X → X) (label : G → Equiv.Perm V)
    (H : C(X × unitInterval, V → ℝ)) (hn : ∀ q, H q ≠ 0)
    (hneg : ∀ x v, H (x, 0) v < 0) (hpos : ∀ x v, 0 < H (x, 1) v)
    (heq : ∀ g x t, H (action g x, t) = permuteVector (label g) (H (x, t))) :
    IsRelabelEquivariant action label (poleHomotopy H hn hneg hpos) := by
  have hmiddle : IsRelabelEquivariant action label (normalizedHomotopy H hn) := by
    intro g t x
    change normalize ⟨H (action g x, t), _⟩ =
      relabel (label g) (normalize ⟨H (x, t), hn (x, t)⟩)
    have hPoint : (⟨H (action g x, t), hn (action g x, t)⟩ :
        {y : V → ℝ // y ≠ 0}) =
        ⟨permuteVector (label g) (H (x, t)),
          permuteVector_ne_zero (label g) (hn (x, t))⟩ :=
      Subtype.ext (heq g x t)
    exact (congrArg normalize hPoint).trans
      (normalize_relabel (label g) ⟨H (x, t), hn (x, t)⟩)
  have hcone (b : Bool) (t : unitInterval)
      (hc : ∀ x, (normalizedEnd H hn t x).1.1 (pole (!b)) = 0) :
      IsRelabelEquivariant action label (coneHomotopy b (normalizedEnd H hn t) hc) := by
    intro g s x
    change conePoint b (normalizedEnd H hn t (action g x)) (hc (action g x)) s =
      relabel (label g) (conePoint b (normalizedEnd H hn t x) (hc x) s)
    have hPoint : normalizedEnd H hn t (action g x) =
        relabel (label g) (normalizedEnd H hn t x) := hmiddle g t x
    simpa only [← hPoint] using
      conePoint_relabel (label g) b (normalizedEnd H hn t x) (hc x) s
  apply equivariant_trans action label
  · exact equivariant_symm action label _
      (hcone false 0 (fun x => normalize_negative_north_zero
        ⟨H (x, 0), hn (x, 0)⟩ (hneg x)))
  · exact equivariant_trans action label _ _ hmiddle
      (hcone true 1 (fun x => normalize_positive_south_zero
        ⟨H (x, 1), hn (x, 1)⟩ (hpos x)))

end SignReversal

end FairDivision.Topology.AAK.ZeroFreeBipyramid
