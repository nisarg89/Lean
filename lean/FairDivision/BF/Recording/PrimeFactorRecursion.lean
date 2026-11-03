import FairDivision.BF.Recording.PrimeMultiplication
import Mathlib.Data.Nat.Factorization.Induction

/-!
# The SAME prime-factor recursion, with the external pathwise theorem isolated

Use Mathlib's existing induction_on_primes. The leaf recorder is the base,
and each prime factor is added by the actual signed-distance multiplication
construction. The value interval is fixed once for the whole recursion.
The final source facade discharges the single external AAK interface.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

/-- All prime multiplication instances needed by the actual recursion,
phrased only for the constructed child score map. -/
def RecordingPathwiseTheorem:Prop:=
  ∀(p a q m:ℕ)(hp:p.Prime)(ha:0<a)(hq:2≤q)
    (v:Finset (Fin m)→ℝ)(L H:ℝ)(hLH:L≤H)
    (Φ:RecordingFunction a q m v L H hLH),
    HasRecordingPathwiseZeros hp.two_le ha hq Φ

/-- The literal prime factorization proof, with no allocation or lottery
existence premise. The isolated external theorem is supplied in the final
unconditional facade rather than included in its public conclusion. -/
theorem exists_recordingFunction_of_pathwiseZeros
    (hAAK:RecordingPathwiseTheorem)
    (n q m:ℕ) (hn:0<n) (hq:2≤q)
    (v:Finset (Fin m)→ℝ) (L H:ℝ) (hLH:L≤H)
    (hL:∀A:Finset (Fin m),L<v A) (hH:∀A:Finset (Fin m),v A<H):
    Nonempty (RecordingFunction n q m v L H hLH):=by
  have hAll:∀n:ℕ,0<n→Nonempty (RecordingFunction n q m v L H hLH):=by
    apply induction_on_primes
    ·intro hZero
     omega
    ·intro hOne
     exact exists_leaf_recordingFunction v L H hLH hL hH
    ·intro p a hp ih hPositive
     have ha:0<a:=by
       by_contra hNot
       have hz:a=0:=by omega
       simp only [hz,Nat.mul_zero] at hPositive
       exact Nat.not_lt_zero _ hPositive
     obtain ⟨Φ⟩:=ih ha
     have hProduct:=primeMultiplication_of_pathwiseZeros hp.two_le ha hq Φ
       (hAAK p a q m hp ha hq v L H hLH Φ)
     simpa only [Nat.mul_comm p a] using hProduct
  exact hAll n hn

end FairDivision.BF.Recording
