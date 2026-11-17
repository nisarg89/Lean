import FairDivision.Topology.NerveConnectivity.FiniteCellOrdering
import FairDivision.Topology.NerveConnectivity.FiniteFaceBoundary

/-!
# Cardinality skeleta of a finite probability simplex

The support-cardinality subtype is exactly the realization of the finite
subcomplex with at most d vertices per face. Existing finite closed-face
pasting therefore applies directly to a continuous one-skeleton map.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- Faces with at most d vertices; the ordinary one-skeleton uses d=2. -/
def finiteSimplexSkeleton (V : Type*) (d : ℕ) : PreAbstractSimplicialComplex V where
  faces:={S | S.Nonempty ∧ S.card≤d}
  isRelLowerSet_faces:=by
    intro S hS
    refine ⟨hS.1,?_⟩
    intro T hTS hT
    exact ⟨hT,(Finset.card_le_card hTS).trans hS.2⟩

/-- Literal support-cardinality source used by the manuscript edge map. -/
abbrev SmallSupportSimplex (V : Type*) [Fintype V] (d : ℕ) :=
  {x : stdSimplex ℝ V // (finiteSimplexSupport x).card≤d}

theorem finiteSimplexSkeleton_mono (V : Type*) {d e : ℕ} (hde:d≤e) :
    finiteSimplexSkeleton V d≤finiteSimplexSkeleton V e:=by
  intro S hS
  exact ⟨hS.1,hS.2.trans hde⟩

/-- Positive support is automatically nonempty, so there is no extra
face condition in the literal support-cardinality source. -/
theorem finiteSimplexSkeleton_realization_eq (V : Type*) [Fintype V] (d:ℕ) :
    simplicialRealization (finiteSimplexSkeleton V d)=
      {x : stdSimplex ℝ V | (finiteSimplexSupport x).card≤d}:=by
  ext x
  change ((finiteSimplexSupport x).Nonempty ∧(finiteSimplexSupport x).card≤d)↔_
  exact ⟨And.right,fun h=>⟨finiteSimplexSupport_nonempty x,h⟩⟩

/-- Exact subtype transport between existing simplicial pasting and the
source type used by the manuscript's one-skeleton construction. -/
noncomputable def finiteSimplexSkeletonHomeomorph (V : Type*) [Fintype V] (d:ℕ) :
    simplicialRealization (finiteSimplexSkeleton V d) ≃ₜ SmallSupportSimplex V d :=
  Homeomorph.setCongr (finiteSimplexSkeleton_realization_eq V d)

@[simp] theorem finiteSimplexSkeletonHomeomorph_val (V : Type*) [Fintype V] (d:ℕ)
    (x : simplicialRealization (finiteSimplexSkeleton V d)) :
    (finiteSimplexSkeletonHomeomorph V d x).1=x.1:=rfl

@[simp] theorem finiteSimplexSkeletonHomeomorph_symm_val (V : Type*) [Fintype V] (d:ℕ)
    (x : SmallSupportSimplex V d) :
    ((finiteSimplexSkeletonHomeomorph V d).symm x).1=x.1:=rfl

/-- Support-local predicates need only these two closure properties for
higher-face construction. The maximum is selected from at most n input
vectors, one witness per coordinate, and is attained in that coordinate. -/
structure SupportLocalMaxClosed {V : Type*} {n : ℕ}
    (P : Finset V →(Fin n→ℝ)→Prop) : Prop where
  mono:∀ {S T:Finset V}{u:Fin n→ℝ},S⊆T→P S u→P T u
  attained:∀ (S:Finset V)(u:Fin n→Fin n→ℝ)(z:Fin n→ℝ),
    (∀j,P S (u j))→(∀i,z i=u i i)→(∀i j,u j i≤z i)→P S z

end FairDivision.Topology
