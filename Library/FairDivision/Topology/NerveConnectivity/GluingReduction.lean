import FairDivision.Topology.NerveConnectivity.Combinatorics
import FairDivision.Topology.NerveConnectivity.SimplicialCover

/-!
# Reduction of the finite-cover theorem to binary simplicial gluing

The theorem `finiteCover_of_binaryGluing` is a proved induction. Its explicit
`BinarySimplicialGluing` argument is the unresolved high-dimensional topology
obligation; this module does not assert that the argument exists. In particular,
it must not be used as an endpoint certificate until binary gluing itself has a
Lean proof.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- The binary gluing statement for a connectivity predicate on the finite
probability simplex. It remains an explicit input until separately proved. -/
def BinarySimplicialGluingFor {V : Type v} [Fintype V]
    (P : ℕ → Set (stdSimplex ℝ V) → Prop) : Prop :=
  ∀ (k : ℕ), 1 ≤ k →
    ∀ (K L : PreAbstractSimplicialComplex V),
      P k (simplicialRealization K) →
      P k (simplicialRealization L) →
      P (k - 1) (simplicialRealization (K ⊓ L)) →
      P k (simplicialRealization (K ⊔ L))

/-- The π-group specialization of the binary gluing obligation. -/
def BinarySimplicialGluing (V : Type v) [Fintype V] : Prop :=
  BinarySimplicialGluingFor (fun k (S : Set (stdSimplex ℝ V)) => ConnectedThrough k S)

private theorem mem_iSup_complex {ι : Sort u} {V : Type v}
    (C : ι → PreAbstractSimplicialComplex V) (F : Finset V) :
    F ∈ (⨆ i, C i) ↔ ∃ i, F ∈ C i := by
  change F ∈ (⋃ K ∈ Set.range C, K.faces) ↔ _
  constructor
  · intro h
    obtain ⟨K, hK, hF⟩ := Set.mem_iUnion₂.mp h
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hK
    exact ⟨i, hF⟩
  · rintro ⟨i, hF⟩
    exact Set.mem_iUnion₂.mpr ⟨C i, Set.mem_range_self i, hF⟩

private theorem mem_sup_complex {V : Type v}
    (K L : PreAbstractSimplicialComplex V) (F : Finset V) :
    F ∈ K ⊔ L ↔ F ∈ K ∨ F ∈ L := Iff.rfl

/-- Realization commutes with the supremum of a family of finite-vertex
simplicial complexes. -/
theorem simplicialRealization_iSup {ι : Type u} {V : Type v} [Fintype V]
    (C : ι → PreAbstractSimplicialComplex V) :
    simplicialRealization (⨆ i, C i) =
      coverUnion (fun i => simplicialRealization (C i)) := by
  ext w
  simp [simplicialRealization, coverUnion, mem_iSup_complex]

/-- Realization commutes with a supremum restricted to a finite index set. -/
theorem simplicialRealization_iSup_finset {ι : Type u} {V : Type v}
    [Fintype V] (C : ι → PreAbstractSimplicialComplex V) (J : Finset ι) :
    simplicialRealization (⨆ i ∈ J, C i) = ⋃ i ∈ J, simplicialRealization (C i) := by
  ext w
  simp [simplicialRealization, mem_iSup_complex]

/-- The generic finite-cover nerve induction, conditional on an explicit
zero-dimensional theorem and positive-dimensional binary gluing. No proof of `BinarySimplicialGluing` is claimed here. -/
theorem finiteCover_of_binaryGluingFor {V : Type v} [Fintype V]
    (P : ℕ → Set (stdSimplex ℝ V) → Prop)
    (hzero : ∀ {ι : Type u} [Fintype ι] [Nonempty ι]
      (C : ι → PreAbstractSimplicialComplex V),
      FiniteCoverConnectivityHypotheses P 0
        (fun i => simplicialRealization (C i)) →
      P 0 (simplicialRealization (⨆ i, C i)))
    (hglue : BinarySimplicialGluingFor P) (k : ℕ) :
    ∀ {ι : Type u} [Fintype ι] [Nonempty ι]
      (C : ι → PreAbstractSimplicialComplex V),
      FiniteCoverConnectivityHypotheses P k
        (fun i => simplicialRealization (C i)) →
      P k (simplicialRealization (⨆ i, C i)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro ι instF instN C hC
    letI : Fintype ι := instF
    letI : Nonempty ι := instN
    letI : DecidableEq ι := Classical.decEq ι
    by_cases hk : k = 0
    · subst k
      exact hzero C hC
    · have hkpos : 1 ≤ k := by omega
      have hsub : ∀ J : Finset ι, J.Nonempty →
          P k (simplicialRealization (⨆ i ∈ J, C i)) := by
        intro J
        induction J using Finset.induction_on with
        | empty =>
            intro hJ
            simp at hJ
        | @insert a J ha hJind =>
            intro hnonempty
            by_cases hJ : J.Nonempty
            · letI : Nonempty J := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
              have hleft := hJind hJ
              have hright : P k (simplicialRealization (C a)) := by
                have hs := hC.2 ({a} : Finset ι) (Finset.singleton_nonempty a) (by simp)
                simpa [coverIntersection] using hs
              let C' : J → PreAbstractSimplicialComplex V :=
                fun i => C i.1 ⊓ C a
              have hC' : FiniteCoverConnectivityHypotheses P (k - 1)
                  (fun i : J => simplicialRealization (C' i)) := by
                have hinter := FiniteCoverConnectivityHypotheses.intersect P
                  (fun i => simplicialRealization (C i)) hkpos hC a J ha
                have hfamilies : (fun i : J => simplicialRealization (C' i)) =
                    intersectCover (fun i => simplicialRealization (C i)) a J := by
                  funext i
                  simp [C', intersectCover, simplicialRealization_inf]
                rw [hfamilies]
                exact hinter
              have hrec : P (k - 1)
                  (simplicialRealization (⨆ i : J, C' i)) :=
                ih (k - 1) (by omega) C' hC'
              have hset : simplicialRealization (⨆ i : J, C' i) =
                  simplicialRealization ((⨆ i ∈ J, C i) ⊓ C a) := by
                rw [simplicialRealization_iSup, simplicialRealization_inf]
                ext w
                simp only [coverUnion, Set.mem_iUnion, Set.mem_inter_iff,
                  simplicialRealization_iSup_finset, Set.mem_iUnion]
                simp only [C', simplicialRealization_inf, Set.mem_inter_iff]
                constructor
                · rintro ⟨i, hi, ha'⟩
                  exact ⟨⟨i.1, i.2, hi⟩, ha'⟩
                · rintro ⟨⟨i, hiJ, hi⟩, ha'⟩
                  exact ⟨⟨i, hiJ⟩, hi, ha'⟩
              have hmiddle : P (k - 1)
                  (simplicialRealization ((⨆ i ∈ J, C i) ⊓ C a)) := by
                rwa [hset] at hrec
              have hresult := hglue k hkpos (⨆ i ∈ J, C i) (C a)
                hleft hright hmiddle
              have hcomplex : (⨆ i ∈ insert a J, C i) =
                  (⨆ i ∈ J, C i) ⊔ C a := by
                rw [Finset.iSup_insert, sup_comm]
              rw [hcomplex]
              exact hresult
            · have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
              subst J
              have hs := hC.2 ({a} : Finset ι) (Finset.singleton_nonempty a) (by simp)
              simpa [coverIntersection] using hs
      have hall := hsub (Finset.univ : Finset ι) Finset.univ_nonempty
      simpa using hall


/-- Optional π-group route, derived from the shared induction. -/
theorem finiteCover_of_binaryGluing {V : Type v} [Fintype V]
    (hglue : BinarySimplicialGluing V) (k : ℕ) :
    ∀ {ι : Type u} [Fintype ι] [Nonempty ι]
      (C : ι → PreAbstractSimplicialComplex V),
      NerveConnectivityHypotheses k (fun i => simplicialRealization (C i)) →
      ConnectedThrough k (simplicialRealization (⨆ i, C i)) := by
  intro ι instF instN C hC
  letI : Fintype ι := instF
  letI : Nonempty ι := instN
  have hzero : ∀ {ζ : Type u} [Fintype ζ] [Nonempty ζ]
      (D : ζ → PreAbstractSimplicialComplex V),
      FiniteCoverConnectivityHypotheses
        (fun j (S : Set (stdSimplex ℝ V)) => ConnectedThrough j S) 0
        (fun i => simplicialRealization (D i)) →
      ConnectedThrough 0 (simplicialRealization (⨆ i, D i)) := by
    intro ζ _ _ D hD
    rw [simplicialRealization_iSup]
    exact connectedThrough_zero_coverUnion
      (fun i => simplicialRealization (D i)) hD
  exact finiteCover_of_binaryGluingFor
    (fun j (S : Set (stdSimplex ℝ V)) => ConnectedThrough j S)
    hzero hglue k C hC

/-- Conditional specialization to an actual finite subcomplex cover. This is a
reduction lemma, not an unconditional certificate of the manuscript theorem. -/
theorem FiniteSubcomplexCover.connectedThrough_of_binaryGluing
    {ι : Type u} {V : Type v} [Fintype ι] [Nonempty ι] [Fintype V]
    (C : FiniteSubcomplexCover ι V) (hglue : BinarySimplicialGluing V)
    (k : ℕ)
    (hC : NerveConnectivityHypotheses k
      (fun i => simplicialRealization (C.pieces i))) :
    ConnectedThrough k (simplicialRealization C.ambient) := by
  rw [C.realization_eq_union, ← simplicialRealization_iSup]
  exact finiteCover_of_binaryGluing hglue k C.pieces hC

end FairDivision.Topology.NerveConnectivity
