import FairDivision.Topology.NerveConnectivity.FiniteConeBinaryGluing
import FairDivision.Topology.NerveConnectivity.FiniteSphereSource
import FairDivision.Topology.NerveConnectivity.FiniteCoverTopOverlap
import FairDivision.Topology.NerveConnectivity.SubordinateSourceMembership
import FairDivision.Topology.NerveConnectivity.NullHomotopyTransport

/-!
# Positive-dimensional gluing for a binary open cover

Pull a sphere map back to the finite standard-simplex boundary and
subdivide until each face lands in one open-cover chamber. Assign each
shared top face to one chamber, so the overlap drops one dimension.
The finite-cone binary gluing theorem then gives a nullhomotopy.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u

/-- Every low-dimensional sphere map into a binary open cover is
nullhomotopic when both chambers and their overlap have the expected
connectivity. -/
theorem nullhomotopic_of_binaryOpenCover
    {X : Type u} [TopologicalSpace X]
    (U W : Set X) (hUopen : IsOpen U) (hWopen : IsOpen W)
    (hcover : U ∪ W = Set.univ)
    (k : ℕ) (hk : 1 ≤ k)
    (hU : NullConnectedSet k U)
    (hW : NullConnectedSet k W)
    (hI : NullConnectedSet (k - 1) (U ∩ W))
    (j : ℕ) (hj : j ≤ k)
    (f : C(CubeSphere j, X)) :
    ∃ x : X, f.Homotopic (ContinuousMap.const _ x) := by
  let S := finiteSphereComplex j
  let sphereEquiv := finiteSphereRealizationHomeomorph j
  let fS : C(simplicialRealization S, X) :=
    f.comp (sphereEquiv : C(simplicialRealization S, CubeSphere j))
  let OU : Set (simplicialRealization S) := fS ⁻¹' U
  let OW : Set (simplicialRealization S) := fS ⁻¹' W
  let O : Bool → Set (simplicialRealization S) :=
    fun b => if b then OW else OU
  have hOopen : ∀ b, IsOpen (O b) := by
    intro b
    cases b with
    | false => simpa [O, OU] using hUopen.preimage fS.continuous
    | true => simpa [O, OW] using hWopen.preimage fS.continuous
  have hOcover : ∀ w : simplicialRealization S, ∃ b, w ∈ O b := by
    intro w
    have hw : fS w ∈ U ∪ W := by
      rw [hcover]
      trivial
    rcases hw with hu | hw
    · exact ⟨false, by simpa [O, OU] using hu⟩
    · exact ⟨true, by simpa [O, OW] using hw⟩
  obtain ⟨n, hn⟩ :=
    exists_subordinateSourceComplex_cover S O hOopen hOcover
  let K := iteratedBarycentricComplex S n
  haveI : Nonempty (iteratedBarycentricVertex (Fin (j + 2)) n) := by
    cases n with
    | zero =>
        change Nonempty (Fin (j + 2))
        exact ⟨0⟩
    | succ n =>
        change Nonempty (Finset (iteratedBarycentricVertex (Fin (j + 2)) n))
        exact ⟨∅⟩
  let A := subordinateSourceComplex S n OU
  let B₀ := subordinateSourceComplex S n OW
  have hAK : A ≤ K := subordinateSourceComplex_le S n OU
  have hB₀K : B₀ ≤ K := subordinateSourceComplex_le S n OW
  have hKdim : ∀ F : Finset (iteratedBarycentricVertex (Fin (j + 2)) n),
      F ∈ K → F.card ≤ j + 1 :=
    iteratedFiniteSphereComplex_card_le j n
  have hB₀dim : ∀ F : Finset (iteratedBarycentricVertex (Fin (j + 2)) n),
      F ∈ B₀ → F.card ≤ j + 1 := by
    intro F hF
    exact hKdim F (hB₀K hF)
  have hAB₀ : A ⊔ B₀ = K := by
    ext F
    constructor
    · rintro (hA | hB)
      · exact hAK hA
      · exact hB₀K hB
    · intro hF
      obtain ⟨b, hb⟩ := hn F hF
      cases b with
      | false => exact Or.inl hb
      | true => exact Or.inr hb
  let B := trimTopOverlap A B₀ (j + 1) hB₀dim
  have hBB₀ : B ≤ B₀ := trimTopOverlap_le A B₀ (j + 1) hB₀dim
  have hBK : B ≤ K := hBB₀.trans hB₀K
  have hAB : A ⊔ B = K := by
    calc
      A ⊔ B = A ⊔ B₀ := sup_trimTopOverlap_eq_sup A B₀ (j + 1) hB₀dim
      _ = K := hAB₀
  have hAdim : ∀ F : Finset (iteratedBarycentricVertex (Fin (j + 2)) n),
      F ∈ A → F.card ≤ k + 1 := by
    intro F hF
    have h := hKdim F (hAK hF)
    omega
  have hBdim : ∀ F : Finset (iteratedBarycentricVertex (Fin (j + 2)) n),
      F ∈ B → F.card ≤ k + 1 := by
    intro F hF
    have h := hKdim F (hBK hF)
    omega
  have hIdim : ∀ F : Finset (iteratedBarycentricVertex (Fin (j + 2)) n),
      F ∈ A ⊓ B → F.card ≤ k := by
    intro F hF
    have h := inf_trimTopOverlap_card_lt A B₀ (j + 1) hB₀dim F hF
    omega
  let e := iteratedBarycentricRealizationHomeomorph S n
  let fK : C(simplicialRealization K, X) :=
    fS.comp (e : C(simplicialRealization K, simplicialRealization S))
  have hABK : A ⊔ B ≤ K := le_of_eq hAB
  let fAB : C(simplicialRealization (A ⊔ B), X) :=
    fK.comp (ContinuousMap.inclusion (simplicialRealization_mono hABK))
  have hfA : ∀ z : simplicialRealization A,
      fAB ⟨z.1, (simplicialRealization_mono le_sup_left) z.2⟩ ∈ U := by
    intro z
    change fS (e ⟨z.1, hAK z.2⟩) ∈ U
    exact subordinateSourceComplex_image_mem S n OU z
  have hfB : ∀ z : simplicialRealization B,
      fAB ⟨z.1, (simplicialRealization_mono le_sup_right) z.2⟩ ∈ W := by
    intro z
    let z₀ : simplicialRealization B₀ :=
      ⟨z.1, (simplicialRealization_mono hBB₀) z.2⟩
    change fS (e ⟨z.1, hBK z.2⟩) ∈ W
    exact subordinateSourceComplex_image_mem S n OW z₀
  obtain ⟨x, hnullAB⟩ := finiteBinarySource_map_nullhomotopic
    A B k hk hAdim hBdim hIdim U W hU hW hI fAB hfA hfB
  have hKAB : K ≤ A ⊔ B := le_of_eq hAB.symm
  let back : C(simplicialRealization K, simplicialRealization (A ⊔ B)) :=
    ContinuousMap.inclusion (simplicialRealization_mono hKAB)
  have hnullK' := ContinuousMap.Homotopic.comp hnullAB
    (ContinuousMap.Homotopic.refl back)
  have hback : fAB.comp back = fK := by
    ext z
    rfl
  have hnullK : fK.Homotopic (ContinuousMap.const _ x) := by
    simpa only [hback, ContinuousMap.const_comp] using hnullK'
  have hnullS := homotopic_const_of_comp_homeomorph e fS x hnullK
  exact ⟨x, homotopic_const_of_comp_homeomorph sphereEquiv f x hnullS⟩

/-- Positive-dimensional connectivity glues across any binary open
cover when the overlap is connected one dimension lower. -/
theorem nullConnectedSpace_binaryOpenCover
    {X : Type u} [TopologicalSpace X]
    (U W : Set X) (hUopen : IsOpen U) (hWopen : IsOpen W)
    (hcover : U ∪ W = Set.univ)
    (k : ℕ) (hk : 1 ≤ k)
    (hU : NullConnectedSet k U)
    (hW : NullConnectedSet k W)
    (hI : NullConnectedSet (k - 1) (U ∩ W)) :
    NullConnectedSpace k X := by
  refine ⟨⟨(Classical.choice hU.1).1⟩, ?_⟩
  intro j hj f
  exact nullhomotopic_of_binaryOpenCover U W hUopen hWopen
    hcover k hk hU hW hI j hj f

end FairDivision.Topology.NerveConnectivity
