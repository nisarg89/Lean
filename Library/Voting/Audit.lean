import Voting.Stable
import Lean.Util.CollectAxioms
import Lean.Util.FindExpr

set_option maxRecDepth 0
set_option maxHeartbeats 0

namespace Voting.Audit
open Lean Elab Command Meta

private def auditTheorem (name : Name) (expected : Expr) : CommandElabM Unit := do
  let some info := (← getEnv).find? name | throwError "missing certified theorem: {name}"
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "certified export is not a theorem: {name}"
  unless (← liftTermElabM <| withTransparency .all <| isDefEq info.type expected) do
    throwError "certified theorem does not have its exact stated contract: {name}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms name
  let bad := axioms.filter fun ax => !allowed.contains ax
  unless bad.isEmpty do
    throwError "nonstandard axioms in {name}: {bad.toList}"
  let ty ← liftTermElabM <| withTransparency .all <| whnf info.type
  if ty.hasExprMVar then throwError "unresolved metavariable in {name}"
  let provider := ty.find? fun e =>
    match e with
    | .const (.str _ "Needs") _ => true
    | _ => false
  if provider.isSome then throwError "unresolved provider interface in {name}"

elab "#voting_audit " id:ident " : " expected:term : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  let target ← liftTermElabM <| Term.elabTerm expected (some (mkSort .zero))
  if target.hasExprMVar then throwError "unresolved expected theorem contract"
  names.forM fun name => auditTheorem name target

end Voting.Audit

namespace Voting.Audit

def exists_stableExpected : Prop :=
  ∀ {n m : ℕ}, 0 < n → 0 < m → ∀ (profile : Voting.Profile n m) (law : Voting.Stable.DrawLaw), ∃ lottery : Voting.Lottery m, Voting.Stable.IsStable law profile lottery

def support_score_eqExpected : Prop :=
  ∀ {n m : ℕ}, 0 < n → 0 < m → ∀ (profile : Voting.Profile n m) (law : Voting.Stable.DrawLaw) (lottery : Voting.Lottery m), Voting.Stable.IsStable law profile lottery → ∀ candidate : Fin m, 0 < lottery.val candidate → Voting.Stable.score law profile lottery candidate = Voting.Stable.benchmark law

def maximal_lottery_iffExpected : Prop :=
  ∀ {n m : ℕ}, 0 < n → 0 < m → ∀ (profile : Voting.Profile n m) (lottery : Voting.Lottery m), Voting.Stable.IsStable (PMF.pure 0) profile lottery ↔ ∀ c, MetricDistortion.avg (fun v => Voting.below (profile v) lottery c) + lottery.val c / 2 ≤ 1 / 2

end Voting.Audit

#voting_audit MetricDistortion.Certified.Analysis_MonotoneSetIntegral : MetricDistortion.Contracts.Analysis_MonotoneSetIntegral.Statement
#voting_audit MetricDistortion.Certified.Comparison_LabeledTie : MetricDistortion.Contracts.Comparison_LabeledTie.Statement
#voting_audit MetricDistortion.Certified.Comparison_PowerIntegral : MetricDistortion.Contracts.Comparison_PowerIntegral.Statement
#voting_audit MetricDistortion.Certified.Model_Lotteries : MetricDistortion.Contracts.Model_Lotteries.Statement
#voting_audit MetricDistortion.Certified.Model_Profiles : MetricDistortion.Contracts.Model_Profiles.Statement
#voting_audit MetricDistortion.Certified.Model_RankIntervals : MetricDistortion.Contracts.Model_RankIntervals.Statement
#voting_audit MetricDistortion.Certified.Shared_CompactConvexMinimax : MetricDistortion.Contracts.Shared_CompactConvexMinimax.Statement
#voting_audit MetricDistortion.Certified.Analysis_DrawSummability : MetricDistortion.Contracts.Analysis_DrawSummability.Statement
#voting_audit MetricDistortion.Certified.Analysis_GeneratingFunction : MetricDistortion.Contracts.Analysis_GeneratingFunction.Statement
#voting_audit MetricDistortion.Certified.Analysis_IntegralMixture : MetricDistortion.Contracts.Analysis_IntegralMixture.Statement
#voting_audit MetricDistortion.Certified.Comparison_AffineSubstitution : MetricDistortion.Contracts.Comparison_AffineSubstitution.Statement
#voting_audit MetricDistortion.Certified.Comparison_CandidateDraws : MetricDistortion.Contracts.Comparison_CandidateDraws.Statement
#voting_audit MetricDistortion.Certified.Comparison_ChallengerLinearity : MetricDistortion.Contracts.Comparison_ChallengerLinearity.Statement
#voting_audit MetricDistortion.Certified.Comparison_CountableMixture : MetricDistortion.Contracts.Comparison_CountableMixture.Statement
#voting_audit MetricDistortion.Certified.Comparison_Exchangeability : MetricDistortion.Contracts.Comparison_Exchangeability.Statement
#voting_audit MetricDistortion.Certified.Comparison_FixedDrawIntegral : MetricDistortion.Contracts.Comparison_FixedDrawIntegral.Statement
#voting_audit MetricDistortion.Certified.Comparison_FixedDrawSpecialization : MetricDistortion.Contracts.Comparison_FixedDrawSpecialization.Statement
#voting_audit MetricDistortion.Certified.Comparison_MaximalLottery : MetricDistortion.Contracts.Comparison_MaximalLottery.Statement
#voting_audit MetricDistortion.Certified.Comparison_ScoreRegularity : MetricDistortion.Contracts.Comparison_ScoreRegularity.Statement
#voting_audit MetricDistortion.Certified.Comparison_SelfPlay : MetricDistortion.Contracts.Comparison_SelfPlay.Statement
#voting_audit MetricDistortion.Certified.Geometry_ApproximateCancellation : MetricDistortion.Contracts.Geometry_ApproximateCancellation.Statement
#voting_audit MetricDistortion.Certified.Geometry_RankStability : MetricDistortion.Contracts.Geometry_RankStability.Statement
#voting_audit MetricDistortion.Certified.Geometry_Rearrangement : MetricDistortion.Contracts.Geometry_Rearrangement.Statement
#voting_audit MetricDistortion.Certified.Model_DrawLaws : MetricDistortion.Contracts.Model_DrawLaws.Statement
#voting_audit MetricDistortion.Certified.Stability_Existence : MetricDistortion.Contracts.Stability_Existence.Statement
#voting_audit MetricDistortion.Certified.Stability_MinimaxApplication : MetricDistortion.Contracts.Stability_MinimaxApplication.Statement
#voting_audit MetricDistortion.Certified.Stability_SupportEquality : MetricDistortion.Contracts.Stability_SupportEquality.Statement
#voting_audit Voting.Stable.exists_stable : Voting.Audit.exists_stableExpected
#voting_audit Voting.Stable.support_score_eq : Voting.Audit.support_score_eqExpected
#voting_audit Voting.Stable.maximal_lottery_iff : Voting.Audit.maximal_lottery_iffExpected
#voting_audit Voting.Stable.comparison_formula : MetricDistortion.Contracts.Comparison_CandidateDraws.Statement
#voting_audit Voting.Stable.rank_stability : MetricDistortion.Contracts.Geometry_RankStability.Statement
