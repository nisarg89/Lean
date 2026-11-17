import FairDivision.Topology.Volovikov.OddPrimeCharacterJoin
import FairDivision.Topology.Volovikov.CyclicRegularCharacterCoordinates
import FairDivision.Topology.Volovikov.UniversalJoinDKGMRealization
import FairDivision.Topology.Volovikov.ComplexFiniteJoinReduction
import FairDivision.Topology.Volovikov.ReducedSphereJoinReduction
import FairDivision.Topology.Volovikov.UniversalJoinLabelEquiv

/-!
# Unconditional reduced regular obstruction for odd cyclic primes

The existing Fourier basis gives p−1 nontrivial complex character
coordinates. Each has the concrete two-color chart map constructed in
OddPrimeCharacterJoin. Thus a hypothetical nonzero centered map out of
2p source colors would give a cyclic equivariant map to 2(p−1) colors,
contradicting the pinned chain-level Dold theorem.

The local source action and upstream right action have opposite signs.
The Fourier eigenvalue has the same minus sign, so the resulting upstream
character action is ψ(a), exactly as required by the two-color map. No
mod-two identification or unnoticed a=−a simplification is used.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The complete finite-source complex obstruction for a cyclic odd
prime, with no remaining no-map, characteristic-class or chain premise. -/
theorem complexFiniteJoinNoMap_cyclic_odd_prime
    (p : ℕ) [Fact p.Prime] (hp : p≠2) :
    ComplexFiniteJoinNoMap p (ZMod p) := by
  classical
  intro F hCenter hNonzero hEquivariant
  let f : C(simplicialRealization (universalJoinComplex (p+p) (ZMod p)),
      Fin (p-1)→ℂ) :=
    ⟨fun x=>CyclicRegularCharacterCoordinates.coordinates p (F x),
      (CyclicRegularCharacterCoordinates.coordinates_continuous p).comp F.continuous⟩
  let ambient:=universalJoinDKGMAmbientMap (0 : Fin (p-1)→ℂ) f
  have hAmbientContinuous : ContinuousOn ambient
      (Dvoretzky.GroupJoin (Multiplicative (ZMod p)) (p+p)) :=
    universalJoinDKGMAmbientMap_continuousOn _ f
  have hAmbientNonzero : ∀x∈Dvoretzky.GroupJoin (Multiplicative (ZMod p)) (p+p),
      ambient x≠0 := by
    intro x hx
    let point : DKGMJoinSpace (p+p) (ZMod p):=⟨x,hx⟩
    change universalJoinDKGMAmbientMap (0 : Fin (p-1)→ℂ) f point.1≠0
    rw [universalJoinDKGMAmbientMap_on_source]
    exact CyclicRegularCharacterCoordinates.coordinates_nonzero p
      (hCenter _) (hNonzero _)
  have hLocal : ∀a : ZMod p,∀x,
      f (translateJoinRealization a x)=
        fun i=>CyclicRegularCharacterCoordinates.characters p i (-a)*f x i := by
    intro a x
    change CyclicRegularCharacterCoordinates.coordinates p
      (F (translateJoinRealization a x))=_
    rw [hEquivariant a x]
    exact CyclicRegularCharacterCoordinates.coordinates_translate p a (F x)
  have hAmbientEquivariant : ∀a : ZMod p,
      ∀x∈Dvoretzky.GroupJoin (Multiplicative (ZMod p)) (p+p),
      ambient (Dvoretzky.joinAct (Multiplicative.ofAdd a) x)=
        fun i=>CyclicRegularCharacterCoordinates.characters p i a*ambient x i := by
    intro a x hx
    have h:=universalJoinDKGMAmbientMap_equivariant
      (0 : Fin (p-1)→ℂ)
      (fun b z i=>CyclicRegularCharacterCoordinates.characters p i (-b)*z i)
      f hLocal a hx
    simpa only [ambient,neg_neg] using h
  have hpTwo : 2≤p := (Fact.out : p.Prime).two_le
  exact OddPrimeCharacterJoin.no_equivariant_map p (p-1) (p+p) hp
    (by omega) (by omega)
    (CyclicRegularCharacterCoordinates.characters p)
    (CyclicRegularCharacterCoordinates.characters_nontrivial p)
    ambient hAmbientContinuous hAmbientNonzero hAmbientEquivariant

/-- Equivalent topological-join formulation, consumed by the already
proved real-to-complex doubling construction. -/
theorem complexJoinNoMap_cyclic_odd_prime
    (p : ℕ) [Fact p.Prime] (hp : p≠2) : ComplexJoinNoMap p (ZMod p) :=
  complexJoinNoMap_of_finiteJoinNoMap (complexFiniteJoinNoMap_cyclic_odd_prime p hp)

/-- The concrete real reduced regular sphere is also excluded. All
representation normalization and real/complex doubling are reused. -/
theorem no_reducedSphere_joinMap_cyclic_odd_prime
    (p : ℕ) [Fact p.Prime] (hp : p≠2) (e : Fin p≃ZMod p)
    (F : C(simplicialRealization (universalJoinComplex p (ZMod p)),ReducedSphere p))
    (hF : ∀a x,F (translateJoinRealization a x)=
      relabelReducedSphere (FairDivision.Topology.regularPositionPerm e a) (F x)) :
    False :=
  no_reducedSphere_joinMap_of_complexJoinNoMap e
    (complexJoinNoMap_cyclic_odd_prime p hp) F hF

/-- The same proved prime obstruction in the actual rank-one p-torus
presentation used by the Volovikov score interface. -/
theorem complexFiniteJoinNoMap_odd_prime_rank_one
    (p : ℕ) [Fact p.Prime] (hp : p≠2) :
    ComplexFiniteJoinNoMap p (Fin 1→ZMod p) :=
  complexFiniteJoinNoMap_of_addEquiv (finOneFunctionAddEquiv (ZMod p))
    (complexFiniteJoinNoMap_cyclic_odd_prime p hp)

end FairDivision.Topology.Volovikov
