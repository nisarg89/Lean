import FairDivision.Topology.NerveConnectivity.PrismConvexBody
import Mathlib.Topology.Constructions

/-!
# Coordinate model of a simplex prism

The product of an `n`-cube and an interval is the `(n+1)`-cube by appending
the interval coordinate. Composing this with the convex-body map produces
a homeomorphism of the whole standard-simplex prism to a cube.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.NerveConnectivity

/-- Append the interval coordinate to a finite cube. -/
noncomputable def finiteCubeSnocHomeomorph (n : ℕ) :
    ((I^ (Fin n)) × I) ≃ₜ I^ (Fin (n + 1)) where
  toFun x := Fin.snoc x.1 x.2
  invFun q := (Fin.init q, q (Fin.last n))
  left_inv x := by
    rcases x with ⟨p, t⟩
    simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv q := Fin.snoc_init_self q
  continuous_toFun := by
    exact (continuous_fst : Continuous (fun x : (Fin n → I) × I => x.1)).finSnoc
      (continuous_snd : Continuous (fun x : (Fin n → I) × I => x.2))
  continuous_invFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      exact continuous_apply i.castSucc
    · exact continuous_apply (Fin.last n)

/-- A whole-body homeomorphism from a standard-simplex prism to a cube. -/
noncomputable def finiteSimplexPrismCubeHomeomorph (n : ℕ) :
    (stdSimplex ℝ (Fin (n + 1)) × I) ≃ₜ I^ (Fin (n + 1)) :=
  (((standardSimplexCubeBodyHomeomorph n).trans
    (finiteUnitCubeBodyHomeomorph n)).prodCongr (Homeomorph.refl I)).trans
      (finiteCubeSnocHomeomorph n)

end FairDivision.Topology.NerveConnectivity
