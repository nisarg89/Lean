import FairDivision.Topology.NerveConnectivity.BarycentricMeshFactor
import FairDivision.Topology.NerveConnectivity.BarycentricChainDimension

/-!
# Iterated barycentric subdivisions and their mesh

Each level has its own finite-face vertex type. The canonical vertex point
at the next level is the centroid of the previous level's face. A fixed
upper bound on face cardinality survives every subdivision.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Vertex type at the `n`-th barycentric subdivision. -/
def iteratedBarycentricVertex (V : Type u) : ℕ → Type u
  | 0 => V
  | n + 1 => Finset (iteratedBarycentricVertex V n)

/-- The `n`-th barycentric subdivision of a finite abstract complex. -/
def iteratedBarycentricComplex {V : Type u}
    (K : PreAbstractSimplicialComplex V) :
    (n : ℕ) → PreAbstractSimplicialComplex (iteratedBarycentricVertex V n)
  | 0 => K
  | n + 1 => barycentricSubdivision (iteratedBarycentricComplex K n)

/-- Geometric vertex locations under repeated barycentric subdivision. -/
noncomputable def iteratedBarycentricPoint
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) : (n : ℕ) → iteratedBarycentricVertex V n → E
  | 0 => p
  | n + 1 => fun F => F.centroid ℝ (iteratedBarycentricPoint p n)

/-- Pairwise vertex-distance bound on every face of a finite complex. -/
def VertexMeshBound
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (p : V → E) (δ : ℝ) : Prop :=
  ∀ F : Finset V, F ∈ K → ∀ i ∈ F, ∀ j ∈ F, dist (p i) (p j) ≤ δ

/-- The original face-size bound remains valid at every subdivision depth. -/
theorem iteratedBarycentric_faceCard_le
    {V : Type u} (K : PreAbstractSimplicialComplex V) (N : ℕ)
    (hsize : ∀ F : Finset V, F ∈ K → F.card ≤ N) :
    ∀ (n : ℕ) (F : Finset (iteratedBarycentricVertex V n)),
      F ∈ iteratedBarycentricComplex K n → F.card ≤ N := by
  intro n
  induction n with
  | zero =>
      exact hsize
  | succ n ih =>
      exact barycentricSubdivision_faceCard_le
        (iteratedBarycentricComplex K n) N ih

/-- One more subdivision multiplies a vertex-mesh bound by the strict
factor `(N-1)/N`, provided `N` is positive. -/
theorem vertexMeshBound_subdivision
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V)
    (p : V → E) (δ : ℝ) (N : ℕ)
    (hN : 0 < N) (hδ : 0 ≤ δ)
    (hsize : ∀ F : Finset V, F ∈ K → F.card ≤ N)
    (hmesh : VertexMeshBound K p δ) :
    VertexMeshBound (barycentricSubdivision K)
      (fun F : Finset V => F.centroid ℝ p)
      (((N : ℝ) - 1) / N * δ) := by
  intro C hC F hF G hG
  have h := barycentricSubdivision_vertexMeshFactor
    K p δ N hδ hsize hmesh C hC F G hF hG
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h' : dist (F.centroid ℝ p) (G.centroid ℝ p) ≤
      (((N : ℝ) - 1) * δ) / N :=
    (le_div_iff₀ hNr).2 (by simpa only [mul_comm] using h)
  convert h' using 1 <;> ring

/-- The uniform mesh factor determined by an upper bound on face size. -/
noncomputable def barycentricMeshFactor (N : ℕ) : ℝ := ((N : ℝ) - 1) / N

/-- The mesh factor is nonnegative when the face-size bound is positive. -/
theorem barycentricMeshFactor_nonneg (N : ℕ) (hN : 0 < N) :
    0 ≤ barycentricMeshFactor N := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact div_nonneg (sub_nonneg.mpr hNone) (le_of_lt hNreal)

/-- The factor is strictly smaller than one for every positive face-size
bound. -/
theorem barycentricMeshFactor_lt_one (N : ℕ) (hN : 0 < N) :
    barycentricMeshFactor N < 1 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold barycentricMeshFactor
  apply (div_lt_iff₀ hNreal).2
  nlinarith

/-- Repeated barycentric subdivision contracts every face's vertex mesh by
an explicit geometric factor. -/
theorem iteratedBarycentric_vertexMeshBound
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V)
    (p : V → E) (δ : ℝ) (N : ℕ)
    (hN : 0 < N) (hδ : 0 ≤ δ)
    (hsize : ∀ F : Finset V, F ∈ K → F.card ≤ N)
    (hmesh : VertexMeshBound K p δ) :
    ∀ n : ℕ,
      VertexMeshBound (iteratedBarycentricComplex K n)
        (iteratedBarycentricPoint p n)
        ((barycentricMeshFactor N) ^ n * δ) := by
  intro n
  induction n with
  | zero =>
      simpa [iteratedBarycentricVertex, iteratedBarycentricComplex,
        iteratedBarycentricPoint] using hmesh
  | succ n ih =>
      have hsize_n := iteratedBarycentric_faceCard_le K N hsize n
      have hδn : 0 ≤ (barycentricMeshFactor N) ^ n * δ :=
        mul_nonneg (pow_nonneg (barycentricMeshFactor_nonneg N hN) n) hδ
      have hstep := vertexMeshBound_subdivision
        (iteratedBarycentricComplex K n)
        (iteratedBarycentricPoint p n)
        ((barycentricMeshFactor N) ^ n * δ) N
        hN hδn hsize_n ih
      have hscale : barycentricMeshFactor N *
          ((barycentricMeshFactor N) ^ n * δ) =
          (barycentricMeshFactor N) ^ (n + 1) * δ := by
        rw [pow_succ]
        ring
      change VertexMeshBound
        (iteratedBarycentricComplex K (n + 1))
        (iteratedBarycentricPoint p (n + 1))
        (barycentricMeshFactor N *
          ((barycentricMeshFactor N) ^ n * δ)) at hstep
      simpa only [hscale] using hstep

end FairDivision.Topology.NerveConnectivity
