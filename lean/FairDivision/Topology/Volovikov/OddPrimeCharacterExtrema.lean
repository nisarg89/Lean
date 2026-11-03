import FairDivision.Topology.Volovikov.RegularCharacterEigenvectors
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Two strict-extremum charts for an odd-prime character circle

A faithful character orbit on a nonzero complex number has either a
unique largest real part or a unique smallest real part. If the largest
real part is tied, two distinct points of the same circle with that real
part are conjugate. Their midpoint LABEL exists because two is invertible
in Z/p; its orbit point is real and is consequently a unique extremum.

This supplies two continuous disjoint-support weight families without an
argument function, a triangulation theorem, or a new topological premise.
It is the scalar ingredient in the cyclic-prime Dold obstruction.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov.OddPrimeCharacterExtrema

open scoped BigOperators

/-- A nontrivial character on a prime-order cyclic group is faithful. The
only group-theoretic input is mathlib's prime-order generation theorem. -/
theorem character_injective (p : ℕ) [Fact p.Prime]
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ≠0) : Function.Injective ψ := by
  have hKernel : ∀x : ZMod p, ψ x=1→x=0 := by
    intro x hx
    by_contra hx0
    have hGen : AddSubgroup.zmultiples x=⊤ :=
      zmultiples_eq_top_of_prime_card (by simp : Nat.card (ZMod p)=p) hx0
    apply hψ
    apply DFunLike.ext
    intro y
    have hy : y∈AddSubgroup.zmultiples x := by rw [hGen];trivial
    obtain ⟨k,rfl⟩:=AddSubgroup.mem_zmultiples_iff.mp hy
    change ψ (k • x)=1
    rw [ψ.map_zsmul_eq_zpow,hx,one_zpow]
  intro x y hxy
  have hd : ψ (x-y)=1 := by
    rw [ψ.map_sub_eq_div,hxy]
    exact div_self (ψ.val_isUnit y).ne_zero
  exact sub_eq_zero.mp (hKernel (x-y) hd)

/-- Doubling labels is surjective for an odd prime. -/
theorem exists_half (p : ℕ) [Fact p.Prime] (hp : p≠2) (a : ZMod p) :
    ∃k : ZMod p,k+k=a := by
  have hTwo : (2 : ZMod p)≠0 := by
    intro h
    have hDiv : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    rcases (Nat.dvd_prime Nat.prime_two).mp hDiv with hOne|hEq
    · exact (Fact.out : p.Prime).ne_one hOne
    · exact hp hEq
  refine ⟨a/2,?_⟩
  calc a/2+a/2=2*(a/2) := by ring
       _=a := by field_simp

/-- Equal real parts on one centered circle give either equality or
complex conjugacy. This is elementary real/imaginary coordinate algebra. -/
theorem eq_or_conj_of_re_eq {u v : ℂ}
    (hNorm : Complex.normSq u=Complex.normSq v) (hRe : u.re=v.re) :
    u=v ∨ u=starRingEnd ℂ v := by
  have hSquares : (u.im-v.im)*(u.im+v.im)=0 := by
    simp only [Complex.normSq_apply] at hNorm
    rw [hRe] at hNorm
    nlinarith only [hNorm]
  rcases mul_eq_zero.mp hSquares with hSame|hOpposite
  · exact Or.inl (Complex.ext hRe (by linarith))
  · exact Or.inr (Complex.ext (by simpa using hRe) (by simpa using (show u.im= -v.im by linarith)))

def orbit {p : ℕ} (ψ : AddChar (ZMod p) ℂ) (z : ℂ) (g : ZMod p) : ℂ := ψ g*z

theorem orbit_injective {p : ℕ} (ψ : AddChar (ZMod p) ℂ)
    (hψ : Function.Injective ψ) {z : ℂ} (hz : z≠0) :
    Function.Injective (orbit ψ z) := by
  intro g h heq
  exact hψ ((mul_right_cancel₀ hz) heq)

theorem orbit_normSq {p : ℕ} [Fact p.Prime]
    (ψ : AddChar (ZMod p) ℂ) (z : ℂ) (g : ZMod p) :
    Complex.normSq (orbit ψ z g)=Complex.normSq z := by
  rw [orbit,Complex.normSq_mul,Complex.normSq_eq_norm_sq,ψ.norm_apply]
  simp

/-- A tied real coordinate supplies a real point in the same character
orbit. The proof uses the midpoint label, not a choice of an angle. -/
theorem exists_real_orbit_of_tie (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (ψ : AddChar (ZMod p) ℂ) (hψ : Function.Injective ψ)
    {z : ℂ} (hz : z≠0) {g h : ZMod p} (hgh : g≠h)
    (hRe : (orbit ψ z g).re=(orbit ψ z h).re) :
    ∃k : ZMod p,(orbit ψ z k).im=0 := by
  have hNorm : Complex.normSq (orbit ψ z g)=Complex.normSq (orbit ψ z h) := by
    rw [orbit_normSq,orbit_normSq]
  have hConj : orbit ψ z g=starRingEnd ℂ (orbit ψ z h) := by
    rcases eq_or_conj_of_re_eq hNorm hRe with hEq|hEq
    · exact (hgh (orbit_injective ψ hψ hz hEq)).elim
    · exact hEq
  obtain ⟨k,hk⟩:=exists_half p hp (g+h)
  have hSquare : orbit ψ z k*orbit ψ z k=orbit ψ z g*orbit ψ z h := by
    calc
      orbit ψ z k*orbit ψ z k=ψ (k+k)*(z*z) := by
        rw [ψ.map_add_eq_mul]
        simp only [orbit]
        ring
      _=ψ (g+h)*(z*z) := by rw [hk]
      _=orbit ψ z g*orbit ψ z h := by
        rw [ψ.map_add_eq_mul]
        simp only [orbit]
        ring
  have hNonzero : orbit ψ z h≠0 := mul_ne_zero (ψ.val_isUnit h).ne_zero hz
  have hPositive : 0<(orbit ψ z k*orbit ψ z k).re := by
    rw [hSquare,hConj]
    have h:=Complex.normSq_pos.mpr hNonzero
    simpa [Complex.mul_re,Complex.normSq_apply] using h
  have hImaginary : (orbit ψ z k*orbit ψ z k).im=0 := by
    rw [hSquare,hConj]
    simp [Complex.mul_im] <;> ring
  refine ⟨k,?_⟩
  simp only [Complex.mul_re] at hPositive
  simp only [Complex.mul_im] at hImaginary
  have hProduct : (orbit ψ z k).re*(orbit ψ z k).im=0 := by
    have hTwice : (2 : ℝ)*((orbit ψ z k).re*(orbit ψ z k).im)=0 := by
      calc
        _=(orbit ψ z k).re*(orbit ψ z k).im+
            (orbit ψ z k).im*(orbit ψ z k).re := by ring
        _=0 := hImaginary
    exact (mul_eq_zero.mp hTwice).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hProduct with hRealZero|hImagZero
  · rw [hRealZero] at hPositive
    nlinarith only [hPositive,mul_self_nonneg (orbit ψ z k).im]
  · exact hImagZero

/-- A real nonzero point on an injectively labelled circle is a unique
maximum or minimum of real parts. -/
theorem strict_extremum_of_real {p : ℕ} [Fact p.Prime]
    (ψ : AddChar (ZMod p) ℂ) (hψ : Function.Injective ψ)
    {z : ℂ} (hz : z≠0) (k : ZMod p) (hk : (orbit ψ z k).im=0) :
    (∀h : ZMod p,h≠k→(orbit ψ z h).re<(orbit ψ z k).re) ∨
    (∀h : ZMod p,h≠k→(orbit ψ z k).re<(orbit ψ z h).re) := by
  have hw : orbit ψ z k≠0 := mul_ne_zero (ψ.val_isUnit k).ne_zero hz
  have hRe : (orbit ψ z k).re≠0 := by
    intro h
    apply hw
    exact Complex.ext h hk
  have hEqual (h : ZMod p) :
      (orbit ψ z h).re^2+(orbit ψ z h).im^2=(orbit ψ z k).re^2 := by
    have hNorm : Complex.normSq (orbit ψ z h)=Complex.normSq (orbit ψ z k) := by
      rw [orbit_normSq,orbit_normSq]
    simpa [Complex.normSq_apply,hk,pow_two] using hNorm
  rcases lt_or_gt_of_ne hRe with hNeg|hPos
  · right
    intro h hne
    have hPoint : orbit ψ z h≠orbit ψ z k :=
      fun hEq=>hne (orbit_injective ψ hψ hz hEq)
    by_contra hNot
    have hLe : (orbit ψ z h).re≤(orbit ψ z k).re := le_of_not_gt hNot
    have hSame : (orbit ψ z h).re=(orbit ψ z k).re := by
      nlinarith [hEqual h,sq_nonneg (orbit ψ z h).im]
    have hIm : (orbit ψ z h).im=0 := by
      nlinarith [hEqual h]
    exact hPoint (Complex.ext hSame (hIm.trans hk.symm))
  · left
    intro h hne
    have hPoint : orbit ψ z h≠orbit ψ z k :=
      fun hEq=>hne (orbit_injective ψ hψ hz hEq)
    by_contra hNot
    have hLe : (orbit ψ z k).re≤(orbit ψ z h).re := le_of_not_gt hNot
    have hSame : (orbit ψ z h).re=(orbit ψ z k).re := by
      nlinarith [hEqual h,sq_nonneg (orbit ψ z h).im]
    have hIm : (orbit ψ z h).im=0 := by
      nlinarith [hEqual h]
    exact hPoint (Complex.ext hSame (hIm.trans hk.symm))

/-- The concrete two-chart theorem used by the odd-prime join map. -/
theorem exists_strict_extremum (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ≠0) {z : ℂ} (hz : z≠0) :
    ∃k : ZMod p,
      (∀h : ZMod p,h≠k→(orbit ψ z h).re<(orbit ψ z k).re) ∨
      (∀h : ZMod p,h≠k→(orbit ψ z k).re<(orbit ψ z h).re) := by
  classical
  obtain ⟨g,hg,hMax⟩:=Finset.exists_max_image Finset.univ
    (fun h : ZMod p=>(orbit ψ z h).re) Finset.univ_nonempty
  by_cases hStrict : ∀h : ZMod p,h≠g→(orbit ψ z h).re<(orbit ψ z g).re
  · exact ⟨g,Or.inl hStrict⟩
  push_neg at hStrict
  obtain ⟨h,hne,hNot⟩:=hStrict
  have hRe : (orbit ψ z g).re=(orbit ψ z h).re :=
    le_antisymm hNot (hMax h (Finset.mem_univ h))
  have hInjective:=character_injective p ψ hψ
  obtain ⟨k,hk⟩:=exists_real_orbit_of_tie p hp ψ hInjective hz hne.symm hRe
  exact ⟨k,strict_extremum_of_real ψ hInjective hz k hk⟩

end FairDivision.Topology.Volovikov.OddPrimeCharacterExtrema
