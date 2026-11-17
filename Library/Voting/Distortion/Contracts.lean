import Voting.Stable.Contracts
import Voting.Distortion.Basic

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable

namespace MetricDistortion.Contracts

namespace Model_Metrics

def Statement : Prop :=
∀ n m (d : Metric n m), (∀ a, distance d a a = 0) ∧
  (∀ a b, distance d a b = distance d b a) ∧
  (∀ a b c, distance d a c ≤ distance d a b+distance d b c) ∧
  (∀ a b, 0 ≤ distance d a b)

end Model_Metrics



namespace Geometry_CutoffProperties

def Statement : Prop :=
∀ n m (σ : Profile n m) P d o v t, 0 ≤ t →
  let a := lowerCut σ P d o v t; let A := upperCut σ P d o v t;
  let p := mass P (marked d o t); let r := below (σ v) P o;
  0 ≤ a ∧ a ≤ min p r ∧ p ≤ A ∧ A ≤ 1 ∧
  region (σ v) P (marked d o t) ⊆ Icc 0 A ∧
  (∀ᵐ u ∂volume, u ∈ Icc 0 a → u ∈ region (σ v) P (marked d o t)) ∧
  (∃ j, j ∉ marked d o t ∧ lowerCut σ P d o v t = below (σ v) P j ∧
    ∀ c, c ∉ marked d o t → (σ v) j ≤ (σ v) c) ∧
  (upperCut σ P d o v t = 0 ∨ ∃ c, c ∈ marked d o t ∧ 0 < P.val c ∧
    upperCut σ P d o v t = below (σ v) P c + P.val c)

structure Needs : Prop where

  child_0 : Model_RankIntervals.Statement

  child_1 : Model_Metrics.Statement

end Geometry_CutoffProperties



namespace Geometry_ThresholdStepFunctions

def Statement : Prop :=
∀ n m (σ : Profile n m) P d o v,
  IntegrableOn (lowerCut σ P d o v) (Ioi (0 : ℝ)) volume ∧
  (∀ q, MeasurableSet (crossing σ P d o v q)) ∧
  (∀ t, sSup (Set.range fun c => distance d (.inr o) (.inr c)) ≤ t →
    lowerCut σ P d o v t = 0 ∧ upperCut σ P d o v t = 0) ∧
  (∀ F : Set (Fin m) → ℝ, Measurable (fun t => F (marked d o t)) ∧
    (F ∅ = 0 → IntegrableOn (fun t => F (marked d o t)) (Ioi (0 : ℝ)) volume))

structure Needs : Prop where

  child_0 : Geometry_CutoffProperties.Statement

end Geometry_ThresholdStepFunctions



namespace Geometry_MetricTail

def Statement : Prop :=
∀ n m (σ : Profile n m) P d, Consistent σ d → ∀ o v,
  (∑ c, P.val c*distance d (.inl v) (.inr c))-distance d (.inl v) (.inr o) ≤
    tailIntegral (lowerCut σ P d o v)

structure Needs : Prop where

  child_0 : Geometry_CutoffProperties.Statement

  child_1 : Geometry_ThresholdStepFunctions.Statement

  child_2 : Model_Metrics.Statement

end Geometry_MetricTail



namespace Geometry_CrossingDiameter

def Statement : Prop :=
∀ n m (σ : Profile n m) P d, Consistent σ d → ∀ o v q t s,
  t ∈ crossing σ P d o v q → s ∈ crossing σ P d o v q →
    |s-t| ≤ 2*distance d (.inl v) (.inr o)

structure Needs : Prop where

  child_0 : Geometry_CutoffProperties.Statement

  child_1 : Model_Metrics.Statement

end Geometry_CrossingDiameter



namespace Geometry_CrossingMeasure

def Statement : Prop :=
∀ n m (σ : Profile n m) P d, Consistent σ d → ∀ o v q,
  tailIntegral (indicator (crossing σ P d o v q)) ≤ 2*distance d (.inl v) (.inr o)

structure Needs : Prop where

  child_0 : Geometry_CrossingDiameter.Statement

  child_1 : Geometry_ThresholdStepFunctions.Statement

end Geometry_CrossingMeasure



namespace Geometry_MetricRankCuts

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) P d,
  Consistent σ d → ∀ o v,
  (∑ c, P.val c*distance d (.inl v) (.inr c))-distance d (.inl v) (.inr o) ≤
    tailIntegral (lowerCut σ P d o v) ∧
  ∀ q ∈ Icc (0 : ℝ) 1,
    tailIntegral (indicator (crossing σ P d o v q)) ≤ 2*distance d (.inl v) (.inr o)

structure Needs : Prop where

  child_0 : Geometry_MetricTail.Statement

  child_1 : Geometry_CrossingDiameter.Statement

  child_2 : Geometry_CrossingMeasure.Statement

end Geometry_MetricRankCuts



namespace Geometry_IntegratedLocalCut

def Statement : Prop :=
∀ D w, ValidCut D w → ∀ n m, 0 < n → 0 < m →
  ∀ (σ : Profile n m) P d, Consistent σ d → ∀ o v j,
  below (σ v) P o ∈ w.roots j ∪ Icc w.b 1 →
  tailIntegral (fun t => lowerCut σ P d o v t + w.lambda (mass P (marked d o t))*
    (∫ u in region (σ v) P (marked d o t), (phi D u-mu D))) +
  tailIntegral (fun t => w.tau j (mass P (marked d o t)))*(mu D-phi D (below (σ v) P o)) ≤
    2*w.C0*distance d (.inl v) (.inr o)

structure Needs : Prop where

  child_0 : Geometry_Rearrangement.Statement

  child_1 : Geometry_MetricRankCuts.Statement

  child_2 : Geometry_ThresholdStepFunctions.Statement

  child_3 : Geometry_CutoffProperties.Statement

  child_4 : Model_RankIntervals.Statement

end Geometry_IntegratedLocalCut



namespace Geometry_CommonCharge

def Statement : Prop :=
∀ (K : Fin 9 → ℝ) (w : CutParameters) D,
  (∀ j, 0 ≤ K j) → ValidCut D w → ∃ j0, (∀ j, K j0 ≤ K j) ∧
  ∀ r ∈ Icc (0 : ℝ) 1, ∃ j, r ∈ w.roots j ∪ Icc w.b 1 ∧
    K j0*(mu D-phi D r) ≤ K j*(mu D-phi D r)

structure Needs : Prop where

  child_0 : Analysis_GeneratingFunction.Statement

end Geometry_CommonCharge



namespace Model_DistortionConventions

def Statement : Prop :=
ratio 0 0 = 1 ∧ (∀ z : ℝ, 0 < z → ratio z 0 = ⊤) ∧
  offsetRatio 0 0 = 1 ∧ (∀ z : ℝ, 0 < z → offsetRatio z 0 = ⊤)

end Model_DistortionConventions



namespace Geometry_AverageAndDistortion

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) P R,
  1 ≤ R → (∀ d, Consistent σ d → ∀ o, Optimal d o → expectedCost d P ≤ R*sc d o) →
  distortion σ P ≤ ENNReal.ofReal R

structure Needs : Prop where

  child_0 : Model_DistortionConventions.Statement

  child_1 : Model_Metrics.Statement

end Geometry_AverageAndDistortion



namespace Geometry_RankCutCriterion

def Statement : Prop :=
∀ D w, ValidCut D w →
  (∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) P, Stable D σ P →
    distortion σ P ≤ ENNReal.ofReal (1+2*w.C0)) ∧
  (∀ B, (∀ p ∈ Icc (0 : ℝ) 1, (1-p)*w.lambda p+w.tau 0 p ≤ B) →
    ∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) P δ,
    0 ≤ δ → ApproxStable D σ P δ → ∀ d, Consistent σ d → ∀ o,
    Optimal d o → expectedCost d P ≤ (1+2*w.C0)*sc d o +
      B*δ*sSup (Set.range fun c => distance d (.inr o) (.inr c)))

structure Needs : Prop where

  child_0 : Geometry_IntegratedLocalCut.Statement

  child_1 : Geometry_CommonCharge.Statement

  child_2 : Geometry_ApproximateCancellation.Statement

  child_3 : Geometry_AverageAndDistortion.Statement

  child_4 : Geometry_ThresholdStepFunctions.Statement

  child_5 : Geometry_MetricTail.Statement

end Geometry_RankCutCriterion



namespace Offsets_BipartiteExtension

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ w : Fin n → Fin m → ℝ,
  (∀ v c, 0 ≤ w v c) →
  (∀ v v' c c', w v c ≤ w v c'+w v' c'+w v' c) →
  ∃ d : Metric n m, ∀ v c, distance d (.inl v) (.inr c) = w v c

structure Needs : Prop where

  child_0 : Model_Metrics.Statement

end Offsets_BipartiteExtension



namespace Model_OffsetDefinitions

def Statement : Prop :=
∀ m (r : Ranking m) (x : Fin m → ℝ), (∀ c, 0 ≤ x c) →
  (∀ c, 0 ≤ sOffset r x c ∧ sOffset r x c ≤ x c) ∧ 0 ≤ deltaOffset r x

end Model_OffsetDefinitions



namespace Offsets_CrossDistanceProperties

def Statement : Prop :=
∀ n m (σ : Profile n m) (x : Fin m → ℝ), (∀ c, 0 ≤ x c) →
  let w := fun v c => deltaOffset (σ v) x/2+sOffset (σ v) x c;
  (∀ v c, 0 ≤ w v c) ∧
  (∀ v v' c c', w v c ≤ w v c'+w v' c'+w v' c) ∧
  (∀ v a b, prefers (σ v) a b → w v a ≤ w v b)

structure Needs : Prop where

  child_0 : Model_OffsetDefinitions.Statement

end Offsets_CrossDistanceProperties



namespace Offsets_MetricRealization

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) (x : Fin m → ℝ),
  (∀ c, 0 ≤ x c) → ∀ o, x o = 0 → ∃ d : Metric n m, Consistent σ d ∧ Optimal d o ∧
  sc d o = scale σ x/2 ∧ (∀ c, sc d c-sc d o = avg (fun v => sOffset (σ v) x c)) ∧
  ∀ P, ratio (expectedCost d P) (sc d o) = offsetRatio (loss σ P x) (scale σ x)

structure Needs : Prop where

  child_0 : Offsets_BipartiteExtension.Statement

  child_1 : Offsets_CrossDistanceProperties.Statement

  child_2 : Model_OffsetDefinitions.Statement

  child_3 : Model_DistortionConventions.Statement

end Offsets_MetricRealization



namespace Offsets_MetricDomination

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) P d,
  Consistent σ d → ∀ o, Optimal d o →
  let x := fun c => distance d (.inr o) (.inr c);
  expectedCost d P-sc d o ≤ loss σ P x ∧ scale σ x ≤ 2*sc d o

structure Needs : Prop where

  child_0 : Model_OffsetDefinitions.Statement

  child_1 : Model_Metrics.Statement

end Offsets_MetricDomination



namespace Offsets_ReductionToOffsets

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) P,
  distortion σ P = ⨆ x : {x : Fin m → ℝ // (∀ c, 0 ≤ x c) ∧ ∃ c, x c = 0},
    offsetRatio (loss σ P x.val) (scale σ x.val)

structure Needs : Prop where

  child_0 : Offsets_MetricRealization.Statement

  child_1 : Offsets_MetricDomination.Statement

  child_2 : Model_OffsetDefinitions.Statement

  child_3 : Model_DistortionConventions.Statement

end Offsets_ReductionToOffsets



end MetricDistortion.Contracts
