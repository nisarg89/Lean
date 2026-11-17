import Voting.Distortion
import RandomSizeMetricDistortion.Certificate

/-!
The paper's explicit draw law and certified rank-cut witness.

The law is specified by its probabilities on draw counts 1, 2, and 32. The
certificate packages the witness data with the existing proof of its validity.
-/

noncomputable section
open scoped ENNReal

namespace MetricDistortion

/-- The draw law used in the paper; `starLaw_spec` gives its exact probabilities. -/
def starLaw : DrawLaw := Classical.choose Certified.Numerics_CompleteWitness.1

/-- The paper's draw law satisfies its exact probability specification. -/
theorem starLaw_spec : IsStarLaw starLaw :=
  Classical.choose_spec Certified.Numerics_CompleteWitness.1

/-- The paper's validated rank-cut certificate for any law with the star probabilities. -/
def starCertificateFor (law : DrawLaw) (law_spec : IsStarLaw law) :
    Voting.Distortion.UpperBoundCertificate law :=
  ⟨fixedWitness, Certified.Numerics_CompleteWitness.2.1 law law_spec⟩

/-- The paper's validated rank-cut certificate for its chosen draw law. -/
def starCertificate : Voting.Distortion.UpperBoundCertificate starLaw :=
  starCertificateFor starLaw starLaw_spec

/-- The certificate's exact real distortion bound is 2.13609. -/
theorem starCertificate_bound :
    starCertificate.bound = (213609 / 100000 : ℝ) := by
  norm_num [Voting.Distortion.UpperBoundCertificate.bound, starCertificate,
    starCertificateFor, fixedWitness, cStar]

/-- The same certificate satisfies the paper's approximate-stability condition with B = 16. -/
theorem starCertificate_approximation :
    Voting.Distortion.ApproximationCertificate starCertificate 16 := by
  simpa [Voting.Distortion.ApproximationCertificate, starCertificate,
    starCertificateFor, fixedWitness] using Certified.Numerics_CompleteWitness.2.2

end MetricDistortion
