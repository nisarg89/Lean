import FairDivision.Topology.Volovikov.OddPrimeElementaryCharacterJoin
import FairDivision.Topology.Volovikov.CyclicRegularCharacterCoordinates
import FairDivision.Topology.Volovikov.ElementaryAbelianCharacterCount
import FairDivision.Topology.Volovikov.UniversalJoinDKGMRealization
import FairDivision.Topology.Volovikov.ComplexFiniteJoinReduction

/-!
# The odd-prime reduced regular obstruction in every positive rank

The existing finite Fourier basis supplies p^r−1 nontrivial complex
coordinates. Their coefficient-vector characters are already bijectively
parametrized in the project. The concrete two-color chart and the generic
shifted-cyclic join theorem exclude a nowhere-zero centered equivariant
map from 2p^r source colors. No cohomology, exactness, or no-map hypothesis
remains in this endpoint.

Local source translation and upstream right-label translation have
opposite signs. The Fourier scalar is also evaluated at the negative
translation, so the two signs cancel before the coefficient-vector
character is passed to the actual cyclic chart.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov

open scoped BigOperators
open FairDivision.Topology.NerveConnectivity
open OddPrimeElementaryCharacterJoin (baseCharacter)

/-- Complete finite-source complex no-map statement for every odd prime
and every positive elementary-abelian rank. This is proof SOURCE; it has
not been subjected to a build during the user's writing-only phase. -/
theorem complexFiniteJoinNoMap_odd_primePower
    (p r : ℕ) [Fact p.Prime] (hp : p≠2) (hr : 0<r) :
    ComplexFiniteJoinNoMap (p^r) (Fin r→ZMod p) := by
  classical
  intro F hCenter hNonzero hEquivariant
  let G:=Fin r→ZMod p
  let I:={ψ : AddChar G ℂ // ψ≠0}
  have hCard : Fintype.card I=p^r-1:=nontrivialElementaryAbelianCharacter_card p r
  let e : Fin (p^r-1)≃I:=(Fintype.equivFinOfCardEq hCard).symm
  let a : Fin (p^r-1)→Fin r→ZMod p:=
    fun i=>((nonzeroCoefficientCharacterEquiv p r).symm (e i)).1
  have hNontrivial : ∀i,a i≠0 :=
    fun i=>((nonzeroCoefficientCharacterEquiv p r).symm (e i)).2
  have hCharacter (i : Fin (p^r-1)) :
      elementaryAbelianCharacter p r (a i)=(e i).1 :=
    congrArg Subtype.val ((nonzeroCoefficientCharacterEquiv p r).apply_symm_apply (e i))
  let f : C(simplicialRealization (universalJoinComplex (p^r+p^r) G),Fin (p^r-1)→ℂ):=
    ⟨fun x i=>CyclicRegularCharacterCoordinates.coefficient G (F x) (e i).1,by
      apply continuous_pi
      intro i
      exact (CyclicRegularCharacterCoordinates.coefficient_continuous G (e i).1).comp
        F.continuous⟩
  have hfNonzero : ∀x,f x≠0 := by
    intro x hZero
    apply CyclicRegularCharacterCoordinates.nontrivial_coordinates_nonzero G
      (hCenter x) (hNonzero x)
    funext ψ
    have h:=congrFun hZero (e.symm ψ)
    change CyclicRegularCharacterCoordinates.coefficient G (F x)
      (e (e.symm ψ)).1=0 at h
    simpa only [Equiv.apply_symm_apply,Pi.zero_apply] using h
  have hfEquivariant : ∀b : G,∀x,f (translateJoinRealization b x)=
      fun i=>(e i).1 (-b)*f x i := by
    intro b x
    funext i
    change CyclicRegularCharacterCoordinates.coefficient G
      (F (translateJoinRealization b x)) (e i).1=_
    rw [hEquivariant b x]
    exact CyclicRegularCharacterCoordinates.coefficient_translate G b (F x) (e i).1
  let ambient:=universalJoinDKGMAmbientMap (0 : Fin (p^r-1)→ℂ) f
  have hAmbientContinuous : ContinuousOn ambient
      (Dvoretzky.GroupJoin (Multiplicative G) (p^r+p^r)) :=
    universalJoinDKGMAmbientMap_continuousOn _ f
  have hAmbientNonzero : ∀x∈Dvoretzky.GroupJoin (Multiplicative G) (p^r+p^r),
      ambient x≠0 := by
    intro x hx
    rw [show ambient x=f ((universalJoinDKGMHomeomorph (p^r+p^r) G).symm ⟨x,hx⟩) from
      universalJoinDKGMAmbientMap_on_source _ f ⟨x,hx⟩]
    exact hfNonzero _
  have hAmbientEquivariant : ∀b : G,
      ∀x∈Dvoretzky.GroupJoin (Multiplicative G) (p^r+p^r),
      ambient (Dvoretzky.joinAct (Multiplicative.ofAdd b) x)=
        fun i=>(e i).1 b*ambient x i := by
    intro b x hx
    have h:=universalJoinDKGMAmbientMap_equivariant
      (0 : Fin (p^r-1)→ℂ) (fun c z i=>(e i).1 (-c)*z i)
      f hfEquivariant b hx
    exact h.trans (congrArg (fun c : G=>fun i=>(e i).1 c*ambient x i) (neg_neg b))
  have hAtLeastTwo : 2≤p^r := by
    calc
      2≤p:=(Fact.out : p.Prime).two_le
      _=p^1:=(pow_one p).symm
      _≤p^r:=Nat.pow_le_pow_right (Fact.out : p.Prime).one_le (by omega : 1≤r)
  apply OddPrimeElementaryCharacterJoin.no_equivariant_map p r (p^r-1) (p^r+p^r)
    hp (by omega) (by omega) a hNontrivial ambient hAmbientContinuous hAmbientNonzero
  intro k x hx
  rw [show OddPrimeTensorSource.generator (p:=p) k=
    Multiplicative.ofAdd (Pi.single k (1 : ZMod p)) from rfl,
    hAmbientEquivariant (Pi.single k 1) x hx]
  funext i
  rw [←hCharacter i,elementaryAbelianCharacter_apply_single,
    OddPrimeElementaryCharacterJoin.canonical_character_at_one]

/-- Equivalent topological-join formulation used by the existing real
regular-space doubling construction. -/
theorem complexJoinNoMap_odd_primePower
    (p r : ℕ) [Fact p.Prime] (hp : p≠2) (hr : 0<r) :
    ComplexJoinNoMap (p^r) (Fin r→ZMod p) :=
  complexJoinNoMap_of_finiteJoinNoMap (complexFiniteJoinNoMap_odd_primePower p r hp hr)

end FairDivision.Topology.Volovikov
