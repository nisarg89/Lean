import FairDivision.Topology.AAK.BipyramidClassifierEquivariance

/-!
# A concrete finite-dimensional pole homotopy from a zero-free reversal

This closes the geometric target reduction. The suspended free join has
at most p vertices per face, with p−1 free colors. Its two poles are fixed.
A hypothetical zero-free p-coordinate reversal produces an actual continuous
equivariant homotopy from SOUTH to NORTH in this target. The separate relative
chain obstruction must still rule out that homotopy.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.ZeroFreeBipyramid

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- A color for every suspension vertex, with the two poles sharing the one
extra color. The face predicate forbids their simultaneous presence. -/
def suspensionColor {d : ℕ} {G : Type*} : SuspensionVertex d G → Option (Fin d)
  | .inl _ => none
  | .inr v => some v.1

/-- A face has at most one vertex of each suspension color. -/
theorem suspensionColor_injOn {d : ℕ} {G : Type*}
    {S : Finset (SuspensionVertex d G)} (hS : S ∈ suspensionJoinComplex d G) :
    Set.InjOn (suspensionColor (d := d) (G := G)) (S : Set _) := by
  intro v hv w hw heq
  cases v with
  | inl b =>
    cases w with
    | inr u => cases heq
    | inl c =>
      have hbc : b = c := by
        cases b <;> cases c
        · rfl
        · exact False.elim (hS.2.1 ⟨hw, hv⟩)
        · exact False.elim (hS.2.1 ⟨hv, hw⟩)
        · rfl
      exact congrArg Sum.inl hbc
  | inr v =>
    cases w with
    | inl b => cases heq
    | inr w =>
      have hcolor : v.1 = w.1 := Option.some.inj heq
      rcases v with ⟨i, g⟩
      rcases w with ⟨j, k⟩
      dsimp at hcolor
      subst j
      exact congrArg Sum.inr (Prod.ext rfl (hS.2.2 i g k hv hw))

/-- Each actual suspension face contains at most d free vertices and one pole. -/
theorem suspensionJoinFace_card_le {d : ℕ} {G : Type*}
    {S : Finset (SuspensionVertex d G)} (hS : S ∈ suspensionJoinComplex d G) :
    S.card ≤ d + 1 := by
  classical
  have hcard := Finset.card_le_card_of_injOn
    (s := S) (t := Finset.univ) suspensionColor
    (fun _ _ => Finset.mem_univ _) (suspensionColor_injOn hS)
  simpa [Fintype.card_option] using hcard

/-- Literal target pole, available also when the free-color set is empty. -/
def suspensionPole (d : ℕ) (G : Type*) [Fintype G] (b : Bool) :
    SuspensionRealization d G := by
  refine ⟨stdSimplex.vertex (pole b), ?_⟩
  change FairDivision.Topology.finiteSimplexSupport (stdSimplex.vertex (pole b)) ∈
    suspensionJoinComplex d G
  rw [FairDivision.Topology.finiteSimplexSupport_vertex]
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · cases b <;> simp
  · intro i a c ha
    simp at ha

/-- The literal ambient simplex of either suspension pole. -/
@[simp] theorem suspensionPole_val (d : ℕ) (G : Type*) [Fintype G] (b : Bool) :
    (suspensionPole d G b).1 = stdSimplex.vertex (pole b) := rfl

variable (p : ℕ) [Fact p.Prime]

theorem suspensionJoinFace_card_le_prime
    {S : Finset (SuspensionVertex (p - 1) (ZMod p))}
    (hS : S ∈ suspensionJoinComplex (p - 1) (ZMod p)) : S.card ≤ p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h := suspensionJoinFace_card_le hS
  omega

@[simp] theorem freeSuspensionMap_pole_eq (b : Bool) :
    freeSuspensionMap p (polePoint b) = suspensionPole (p - 1) (ZMod p) b := by
  apply Subtype.ext
  rw [suspensionPole_val]
  apply Subtype.ext
  funext v
  have hCoord := congrArg
    (fun w : stdSimplex ℝ (SuspensionVertex (p - 1) (ZMod p)) => w.1 v)
    (freeSuspensionMap_pole p b)
  by_cases hv : v = pole b <;>
    simpa [stdSimplex.vertex_coe, Pi.single_apply, hv, eq_comm] using hCoord

@[simp] theorem suspensionRelabel_pole (a : ZMod p) (b : Bool) :
    suspensionRelabel p a (suspensionPole (p - 1) (ZMod p) b) =
      suspensionPole (p - 1) (ZMod p) b := by
  have hMap (x : SuspensionRealization (p - 1) (ZMod p)) :
      (suspensionRelabel p a x).1 = stdSimplex.map (suspensionPermutation p a) x.1 := rfl
  have hVertex : suspensionPermutation p a (pole b) = pole b := rfl
  apply Subtype.ext
  rw [hMap]
  simp only [suspensionPole_val, stdSimplex.map_vertex, hVertex]
  apply Subtype.ext
  funext v
  by_cases hv : v = pole b <;>
    simp [stdSimplex.vertex_coe, Pi.single_apply, hv, eq_comm]

section SignReversal

variable {X : Type*} [TopologicalSpace X]

/-- The actual continuous suspended-join pole homotopy. Its source is any
space carrying the zero-free p-coordinate reversal. -/
def suspendedPoleHomotopy (H : C(X × unitInterval, ZMod p → ℝ))
    (hn : ∀ q, H q ≠ 0)
    (hneg : ∀ x v, H (x, 0) v < 0) (hpos : ∀ x v, 0 < H (x, 1) v) :
    (ContinuousMap.const X (suspensionPole (p - 1) (ZMod p) false)).Homotopy
      (ContinuousMap.const X (suspensionPole (p - 1) (ZMod p) true)) where
  toFun q := freeSuspensionMap p (poleHomotopy H hn hneg hpos q)
  continuous_toFun := (freeSuspensionMap p).continuous.comp
    (poleHomotopy H hn hneg hpos).continuous
  map_zero_left x := by
    exact (congrArg (freeSuspensionMap p)
      ((poleHomotopy H hn hneg hpos).map_zero_left x)).trans
      (freeSuspensionMap_pole_eq p false)
  map_one_left x := by
    exact (congrArg (freeSuspensionMap p)
      ((poleHomotopy H hn hneg hpos).map_one_left x)).trans
      (freeSuspensionMap_pole_eq p true)

/-- Exact equivariance of the composed pole homotopy, with target additive
translation and no quotient or simplicial-approximation premise. -/
theorem suspendedPoleHomotopy_equivariant
    (action : ZMod p → X → X)
    (H : C(X × unitInterval, ZMod p → ℝ)) (hn : ∀ q, H q ≠ 0)
    (hneg : ∀ x v, H (x, 0) v < 0) (hpos : ∀ x v, 0 < H (x, 1) v)
    (heq : ∀ a x t, H (action a x, t) = permuteVector (cyclicPerm a) (H (x, t))) :
    ∀ a t x, suspendedPoleHomotopy p H hn hneg hpos (t, action a x) =
      suspensionRelabel p a (suspendedPoleHomotopy p H hn hneg hpos (t, x)) := by
  intro a t x
  change freeSuspensionMap p (poleHomotopy H hn hneg hpos (t, action a x)) = _
  rw [poleHomotopy_equivariant action cyclicPerm H hn hneg hpos heq a t x]
  exact freeSuspensionMap_equivariant p a _

end SignReversal

end FairDivision.Topology.AAK.ZeroFreeBipyramid
