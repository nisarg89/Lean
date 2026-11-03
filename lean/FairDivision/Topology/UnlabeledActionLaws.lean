import FairDivision.Topology.UnlabeledContinuousAction

/-!
# Identity and composition laws for the BF position action

These laws make continuous relabeling a genuine symmetric-group action on
the corrected unlabeled-dummy auxiliary realization. They are used when
transferring the eventual equivariant obstruction to BF.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The identity permutation fixes each unlabeled auxiliary vertex. -/
theorem relabelUnlabeledVertex_one {k m r c : ℕ}
    {D : Finset (Fin m)} (p : UnlabeledDummyVertex k m r c D) :
    relabelUnlabeledVertex (1 : Equiv.Perm (Fin k)) p = p := by
  apply Subtype.ext
  funext i
  change p.1 ((1 : Equiv.Perm (Fin k)).symm i) = p.1 i
  rfl

/-- Vertex relabeling respects permutation multiplication. -/
theorem relabelUnlabeledVertex_mul {k m r c : ℕ}
    {D : Finset (Fin m)} (σ τ : Equiv.Perm (Fin k))
    (p : UnlabeledDummyVertex k m r c D) :
    relabelUnlabeledVertex (σ * τ) p =
      relabelUnlabeledVertex σ (relabelUnlabeledVertex τ p) := by
  apply Subtype.ext
  funext i
  change p.1 ((σ * τ).symm i) = p.1 (τ.symm (σ.symm i))
  rfl

/-- The identity position permutation fixes every auxiliary lottery. -/
theorem auxiliaryRelabel_one {k m r c : ℕ}
    {D : Finset (Fin m)} (x : unlabeledLotterySpace k m r c D) :
    auxiliaryRelabel (1 : Equiv.Perm (Fin k)) x = x := by
  apply Subtype.ext
  change stdSimplex.map
      (relabelUnlabeledVertex (D := D) (r := r) (c := c)
        (1 : Equiv.Perm (Fin k))) x.1 = x.1
  have hfun :
      relabelUnlabeledVertex (D := D) (r := r) (c := c)
        (1 : Equiv.Perm (Fin k)) = id := by
    funext p
    exact relabelUnlabeledVertex_one p
  rw [hfun]
  exact stdSimplex.map_id_apply x.1

/-- Successive position relabelings multiply as permutations. -/
theorem auxiliaryRelabel_mul {k m r c : ℕ}
    {D : Finset (Fin m)} (σ τ : Equiv.Perm (Fin k))
    (x : unlabeledLotterySpace k m r c D) :
    auxiliaryRelabel (σ * τ) x =
      auxiliaryRelabel σ (auxiliaryRelabel τ x) := by
  apply Subtype.ext
  change stdSimplex.map (relabelUnlabeledVertex (D := D) (r := r) (c := c)
      (σ * τ)) x.1 =
    stdSimplex.map (relabelUnlabeledVertex σ)
      (stdSimplex.map (relabelUnlabeledVertex τ) x.1)
  have hfun :
      relabelUnlabeledVertex (D := D) (r := r) (c := c) (σ * τ) =
        (relabelUnlabeledVertex σ).comp (relabelUnlabeledVertex τ) := by
    funext p
    exact relabelUnlabeledVertex_mul σ τ p
  rw [hfun]
  exact (stdSimplex.map_comp_apply
    (relabelUnlabeledVertex τ) (relabelUnlabeledVertex σ) x.1).symm

end FairDivision.Topology
