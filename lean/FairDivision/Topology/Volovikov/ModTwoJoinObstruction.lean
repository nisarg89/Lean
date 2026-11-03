import FairDivision.Topology.Volovikov.ModTwoRealFourier
import FairDivision.Topology.Volovikov.SignedCoordinateJoin
import FairDivision.Topology.Volovikov.UniversalJoinDKGMRealization

/-!
# The real finite-join obstruction for every elementary abelian two-group

The nontrivial real Fourier coefficients identify the centered regular
representation with independent sign characters. Positive-part coordinates
send a hypothetical nowhere-zero map continuously to the corresponding
join of two-point character spheres. The pinned upstream chain theorem
`Dvoretzky.ElemAb.elemAb_join` excludes that map. There is no residual
no-map, characteristic-class or cohomology hypothesis in the conclusion.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open scoped BigOperators
open FairDivision.Topology.NerveConnectivity
open ModTwoRealFourier

/-- A centered equivariant real map from at least 2^r universal join colors
has a zero. This supplies the genuine finite-join obstruction at p=2. -/
theorem no_centered_real_joinMap_modTwo {r N : ℕ} (hr : 0<r) (hN : 2^r≤N)
    (f : C(simplicialRealization (universalJoinComplex N (Fin r → ZMod 2)),
      (Fin r → ZMod 2) → ℝ))
    (hCenter : ∀ x, ∑ g : Fin r → ZMod 2,f x g=0)
    (hNonzero : ∀ x,f x≠0)
    (hEquiv : ∀ a x g,f (translateJoinRealization a x) g=f x (g-a)) : False := by
  classical
  let G := Fin r → ZMod 2
  let I := {ψ : AddChar G ℂ // ψ≠0}
  let K := 2^r-2+1
  have hTwo := elementaryAbelian_exponentTwo r
  have hCardG : Fintype.card G=2^r := by simp [G]
  have hAtLeastTwo : 2≤2^r := by
    simpa using Nat.pow_le_pow_right (by decide : 1≤2) (show 1≤r by omega)
  have hCardI : Fintype.card I=K := by
    have h := Fintype.card_subtype_compl (fun ψ : AddChar G ℂ => ψ=0)
    have hCount : Fintype.card I=2^r-1 := by
      simpa [I,AddChar.card_eq,hCardG] using h
    dsimp [K]
    omega
  let e : Fin K ≃ I := (Fintype.equivFinOfCardEq hCardI).symm
  let ε : Fin K → Fin r → ZMod 2 :=
    fun i q => characterBit hTwo (e i).1 (Pi.single q 1)
  have hε : ∀ i,ε i≠0 := by
    intro i
    exact generator_values_ne_zero (characterBit hTwo (e i).1)
      (characterBit_ne_zero hTwo (e i).1 (e i).2)
  let v : simplicialRealization (universalJoinComplex N G) → Fin K → ℝ :=
    fun x i => coefficient (e i).1 (f x)
  have hvCont : Continuous v := by
    apply continuous_pi
    intro i
    exact (continuous_coefficient (e i).1).comp f.continuous
  have hvNonzero : ∀ x,v x≠0 := by
    intro x hx
    obtain ⟨ψ,hψ⟩ := exists_nonzero_coefficient hTwo (f x) (hCenter x) (hNonzero x)
    obtain ⟨i,hi⟩ := e.surjective ψ
    apply hψ
    have h := congrFun hx i
    simpa only [v,hi,Pi.zero_apply] using h
  let δ : G → Fin K → ZMod 2 := fun a i => characterBit hTwo (e i).1 a
  have hvEquiv : ∀ a x,v (translateJoinRealization a x)=
      SignedCoordinateJoin.flipCoordinates (δ a) (v x) := by
    intro a x
    funext i
    have hSource : f (translateJoinRealization a x)=(fun g => f x (g-a)) :=
      funext (hEquiv a x)
    change coefficient (e i).1 (f (translateJoinRealization a x)) =
      SignedCoordinateJoin.sign (Multiplicative.ofAdd (δ a i))*coefficient (e i).1 (f x)
    rw [hSource,coefficient_translate hTwo]
    rw [SignedCoordinateJoin.sign_ofAdd,←realCharacter_eq_bit_sign hTwo]
  let Φ : C(simplicialRealization (universalJoinComplex N G),Fin K → Dvoretzky.ElemAb.L2 → ℝ) :=
    ⟨fun x => SignedCoordinateJoin.coordinates (v x),
      SignedCoordinateJoin.continuous_coordinates_comp v hvCont hvNonzero⟩
  have hΦEquiv : ∀ a x,Φ (translateJoinRealization a x)=
      Dvoretzky.ElemAb.tflip (δ a) (Φ x) := by
    intro a x
    change SignedCoordinateJoin.coordinates (v (translateJoinRealization a x)) =
      Dvoretzky.ElemAb.tflip (δ a) (SignedCoordinateJoin.coordinates (v x))
    rw [hvEquiv,SignedCoordinateJoin.coordinates_flip]
  let ambient := universalJoinDKGMAmbientMap 0 Φ
  apply Dvoretzky.ElemAb.elemAb_join (N:=N) (D:=2^r-2) (by omega) ε hε ambient
  · exact universalJoinDKGMAmbientMap_continuousOn 0 Φ
  · intro x hx
    have hOn := universalJoinDKGMAmbientMap_on_source 0 Φ
      (⟨x,hx⟩ : DKGMJoinSpace N G)
    rw [show ambient x=Φ ((universalJoinDKGMHomeomorph N G).symm ⟨x,hx⟩) from hOn]
    exact SignedCoordinateJoin.coordinates_mem _ (hvNonzero _)
  · intro q x hx
    have h := universalJoinDKGMAmbientMap_equivariant 0
      (fun a y => Dvoretzky.ElemAb.tflip (δ a) y) Φ hΦEquiv (Pi.single q 1) hx
    have hNeg : -(Pi.single q (1 : ZMod 2) : G)=Pi.single q 1 := by
      apply neg_eq_iff_add_eq_zero.mpr
      exact hTwo _
    simpa only [ambient,Dvoretzky.ElemAb.egen,hNeg,δ,ε] using h

end FairDivision.Topology.Volovikov
