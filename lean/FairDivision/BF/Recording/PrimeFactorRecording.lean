import FairDivision.BF.Recording.PrimeFactorRecursion
import FairDivision.BF.Recording.AAKPathwise

/-!
# Unconditional recording functions for every positive number of agents

The separate actual AAK theorem now supplies the exact pathwise statement
for the SAME constructed child-score map. The manuscript's multiplication
and Mathlib's existing prime-factor induction therefore compose without any
external zero, connectivity, family, lottery, or recursion premise.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

/-- Actual manuscript multiplication by a prime, with AAK discharged. -/
theorem primeMultiplication (p:ℕ) [Fact p.Prime] {a q m:ℕ}
    (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH):
    Nonempty (RecordingFunction (a*p) q m v L H hLH):=
  primeMultiplication_of_pathwiseZeros (Fact.out:p.Prime).two_le ha hq Φ
    (hasRecordingPathwiseZeros p a q m ha hq Φ)

/-- The manuscript's full prime-factor recursion, with one value interval
fixed throughout. Every recorder zero supplies the actual equitable
compatible lottery in its exact available pool and with imposed labels. -/
theorem exists_recordingFunction (n q m:ℕ) (hn:0<n) (hq:2≤q)
    (v:Finset (Fin m)→ℝ) (L H:ℝ) (hLH:L≤H)
    (hL:∀A:Finset (Fin m),L<v A) (hH:∀A:Finset (Fin m),v A<H):
    Nonempty (RecordingFunction n q m v L H hLH):=by
  apply exists_recordingFunction_of_pathwiseZeros _ n q m hn hq v L H hLH hL hH
  intro p a q m hp ha hq v L H hLH Φ
  letI : Fact p.Prime:=⟨hp⟩
  exact hasRecordingPathwiseZeros p a q m ha hq Φ

/-- One choice from the fully proved actual construction, for the root
midpoint, interval zero, and final finite conversion. -/
def recordingFunction (n q m:ℕ) (hn:0<n) (hq:2≤q)
    (v:Finset (Fin m)→ℝ) (L H:ℝ) (hLH:L≤H)
    (hL:∀A:Finset (Fin m),L<v A) (hH:∀A:Finset (Fin m),v A<H):
    RecordingFunction n q m v L H hLH:=
  Classical.choice (exists_recordingFunction n q m hn hq v L H hLH hL hH)

end FairDivision.BF.Recording
