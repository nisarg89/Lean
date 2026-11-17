import RandomSizeMetricDistortion.Numerics.WitnessData
import RandomSizeMetricDistortion.Computation.ProgramCode
import Voting.Distortion.Contracts

noncomputable section

open scoped BigOperators ENNReal

open MeasureTheory Set Filter

attribute [local instance] Classical.propDecidable

/- BEGIN shared rank-potential vocabulary -/
namespace MetricDistortion
def rankPotential (j : Fin 9) (x : ℝ) : ℝ :=
  if x ≤ bStar then 0 else
    if x ≤ cutoff j then cStar-x-eta j*psiStar x-shift j else cStar
end MetricDistortion
/- END shared rank-potential vocabulary -/

/- BEGIN shared tape-replay vocabulary -/
namespace MetricDistortion
inductive TapeOp where
  | const : ℚ → TapeOp
  | var : Fin 4 → TapeOp
  | add : ℕ → ℕ → TapeOp
  | mul : ℕ → ℕ → TapeOp
  | neg : ℕ → TapeOp

structure TapeBounds where
  value : QInterval
  gradient : Fin 4 → QInterval

def zeroTapeBounds : TapeBounds := ⟨⟨0,0⟩,fun _ => ⟨0,0⟩⟩
def tapeCompileStep (es : List PolyExpr) : TapeOp → PolyExpr
  | .const q => .const q
  | .var i => .var i
  | .add a b => .add (es.getD a (.const 0)) (es.getD b (.const 0))
  | .mul a b => .mul (es.getD a (.const 0)) (es.getD b (.const 0))
  | .neg a => .neg (es.getD a (.const 0))
def tapeCompile (tape : List TapeOp) : List PolyExpr :=
  tape.foldl (fun es op => es ++ [tapeCompileStep es op]) []
def tapeExpr (tape : List TapeOp) (root : ℕ) : PolyExpr :=
  (tapeCompile tape).getD root (.const 0)
def tapeRefsValid (n : ℕ) : TapeOp → Bool
  | .const _ => true
  | .var _ => true
  | .add a b => decide (a < n ∧ b < n)
  | .mul a b => decide (a < n ∧ b < n)
  | .neg a => decide (a < n)
def tapeExpected (B : Box) (done : List TapeBounds) : TapeOp → TapeBounds
  | .const q => ⟨⟨q,q⟩,fun _ => ⟨0,0⟩⟩
  | .var i => ⟨B i,fun j => if i = j then ⟨1,1⟩ else ⟨0,0⟩⟩
  | .add a b =>
      let A := done.getD a zeroTapeBounds
      let C := done.getD b zeroTapeBounds
      ⟨intervalAdd A.value C.value,fun i => intervalAdd (A.gradient i) (C.gradient i)⟩
  | .mul a b =>
      let A := done.getD a zeroTapeBounds
      let C := done.getD b zeroTapeBounds
      ⟨intervalMul A.value C.value,fun i =>
        intervalAdd (intervalMul (A.gradient i) C.value) (intervalMul A.value (C.gradient i))⟩
  | .neg a =>
      let A := done.getD a zeroTapeBounds
      ⟨intervalNeg A.value,fun i => intervalNeg (A.gradient i)⟩
def intervalEncloses (outer inner : QInterval) : Bool :=
  decide (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi)
def tapeBoundsEnclose (outer inner : TapeBounds) : Bool :=
  intervalEncloses outer.value inner.value &&
    (List.finRange 4).all (fun i => intervalEncloses (outer.gradient i) (inner.gradient i))
def tapeCheckAux (B : Box) (done : List TapeBounds) : List TapeOp → List TapeBounds → Bool
  | [],[] => true
  | op::ops,row::rows =>
      tapeRefsValid done.length op && tapeBoundsEnclose row (tapeExpected B done op) &&
        tapeCheckAux B (done ++ [row]) ops rows
  | _,_ => false
def tapeCheck (B : Box) (tape : List TapeOp) (rows : List TapeBounds) : Bool :=
  tapeCheckAux B [] tape rows
def midpointBox (B : Box) : Box :=
  fun i => ⟨((B i).lo+(B i).hi)/2,((B i).lo+(B i).hi)/2⟩
def tapeCenteredBound (B : Box) (root : ℕ) (rows centers : List TapeBounds) : ℚ :=
  (centers.getD root zeroTapeBounds).value.hi +
    ∑ i, max |((rows.getD root zeroTapeBounds).gradient i).lo|
      |((rows.getD root zeroTapeBounds).gradient i).hi| * ((B i).hi-(B i).lo)/2
inductive TapeTree where
  | direct : List TapeBounds → TapeTree
  | centered : List TapeBounds → List TapeBounds → TapeTree
  | face : Fin 4 → Bool → List TapeBounds → TapeTree → TapeTree
  | split : Fin 4 → ℚ → TapeTree → TapeTree → TapeTree

def verifyTapeTree (tape : List TapeOp) (root : ℕ) (B : Box) : TapeTree → Bool
  | .direct rows => decide (root < tape.length) && tapeCheck B tape rows &&
      decide ((rows.getD root zeroTapeBounds).value.hi ≤ 0)
  | .centered rows centers => decide (root < tape.length) && tapeCheck B tape rows &&
      tapeCheck (midpointBox B) tape centers && decide (tapeCenteredBound B root rows centers ≤ 0)
  | .face i upper rows child => decide (root < tape.length) && tapeCheck B tape rows &&
      (if upper then decide (0 ≤ ((rows.getD root zeroTapeBounds).gradient i).lo)
        else decide (((rows.getD root zeroTapeBounds).gradient i).hi ≤ 0)) &&
      verifyTapeTree tape root (faceBox B i upper) child
  | .split i q left right => decide ((B i).lo ≤ q ∧ q ≤ (B i).hi) &&
      verifyTapeTree tape root (splitBox B i q false) left &&
      verifyTapeTree tape root (splitBox B i q true) right

end MetricDistortion
/- END shared tape-replay vocabulary -/

/- BEGIN preprocessing-phase vocabulary -/
namespace MetricDistortion
def ProgramBases (n m : ℕ) (s : MachineState) : Prop :=
  s.naturals 0 = n ∧ s.naturals 1 = m ∧ s.naturals 2 = 0 ∧ s.naturals 3 = 1 ∧
  s.naturals 4 = n*m ∧ s.naturals 20 = n*m ∧ s.naturals 21 = 2*n*m ∧
  s.naturals 22 = 2*n*m+m ∧ s.naturals 23 = 2*n*m+2*m ∧
  s.naturals 24 = 2*n*m+3*m ∧ s.naturals 26 = m ∧
  s.naturals 27 = 2*m ∧ s.naturals 28 = 3*m ∧ s.naturals 29 = 4*m

def ProgramRanks {n m : ℕ} (σ : Profile n m) (s : MachineState) : Prop :=
  ∀ v : Fin n, ∀ c : Fin m,
    s.naturalMemory (v.val*m+c.val) = ((σ v) c).val

def ProgramInverse {n m : ℕ} (σ : Profile n m) (s : MachineState) : Prop :=
  ∀ v : Fin n, ∀ c : Fin m,
    s.naturalMemory (n*m+v.val*m+((σ v) c).val) = c.val

def ProgramKeep {n m : ℕ} (σ : Profile n m) (s : MachineState) : Prop :=
  ∀ c : Fin m, s.naturalMemory (2*n*m+c.val) = if Dominated σ c then 0 else 1

def ProgramMaps {n m : ℕ} (σ : Profile n m) (r : ℕ) (s : MachineState) : Prop :=
  s.naturals 5 = r ∧ 0 < r ∧ r ≤ m ∧
  (∀ j : Fin r, s.naturalMemory (2*n*m+m+j.val) < m) ∧
  Function.Injective (fun j : Fin r => s.naturalMemory (2*n*m+m+j.val)) ∧
  (∀ c : Fin m, ¬ Dominated σ c ↔
    ∃ j : Fin r, s.naturalMemory (2*n*m+m+j.val) = c.val) ∧
  ∀ j : Fin r,
    s.naturalMemory (2*n*m+2*m+s.naturalMemory (2*n*m+m+j.val)) = j.val
end MetricDistortion
/- END preprocessing-phase vocabulary -/

/- BEGIN rounded-tape-candidate vocabulary -/
namespace MetricDistortion
def tapeDyadicDen (bits : ℕ) : ℚ := 2^bits

def tapeRoundInterval (bits : ℕ) (I : QInterval) : QInterval :=
  ⟨(Rat.floor (I.lo*tapeDyadicDen bits) : ℚ)/tapeDyadicDen bits,
    (-Rat.floor (-I.hi*tapeDyadicDen bits) : ℚ)/tapeDyadicDen bits⟩

def tapeRoundRow (bits : ℕ) (preserve : Bool) (row : TapeBounds) : TapeBounds :=
  ⟨if preserve then row.value else tapeRoundInterval bits row.value,
    fun i => tapeRoundInterval bits (row.gradient i)⟩

def tapeDegreeStep (done : List ℕ) : TapeOp → ℕ
  | .const _ => 0
  | .var _ => 1
  | .add a b => max (done.getD a 0) (done.getD b 0)
  | .mul a b => done.getD a 0+done.getD b 0
  | .neg a => done.getD a 0

def roundedTapeRowsAux (bits : ℕ) (pick : ℕ → TapeBounds → Bool) (B : Box)
    (degrees : List ℕ) (done : List TapeBounds) : List TapeOp → List TapeBounds
  | [] => []
  | op::ops =>
      let degree := tapeDegreeStep degrees op
      let expected := tapeExpected B done op
      let row := tapeRoundRow bits (pick degree expected) expected
      row :: roundedTapeRowsAux bits pick B (degrees++[degree]) (done++[row]) ops

def tapeRefsValidAux (n : ℕ) : List TapeOp → Bool
  | [] => true
  | op::ops => tapeRefsValid n op && tapeRefsValidAux (n+1) ops

def roundedTapeRows (bits : ℕ) (pick : ℕ → TapeBounds → Bool) (B : Box) (tape : List TapeOp) :
    List TapeBounds := roundedTapeRowsAux bits pick B [] [] tape
end MetricDistortion
/- END rounded-tape-candidate vocabulary -/

/- BEGIN selected source-cancellation vocabulary -/
namespace MetricDistortion
def sourceDegree : Fin 3 → ℕ := ![1,2,32]
def sourceWeight : Fin 3 → ℝ := ![19/73,35/146,1/2]
def sourceDenom : ℝ := 1-muStar
def sourceF0 (x : ℝ) : ℝ := muStar/sourceDenom -
  ∑ k : Fin 3, (sourceWeight k/(sourceDegree k+1 : ℕ)/sourceDenom)*x^(sourceDegree k)
def sourceB (x : ℝ) : ℝ :=
  ∑ k : Fin 3, (sourceWeight k/(sourceDegree k+1 : ℕ)/sourceDenom)*
    ∑ i ∈ Finset.Icc 1 (sourceDegree k), x^i
def sourceInc (x h : ℝ) : ℝ :=
  -(∑ k : Fin 3, (sourceWeight k/(sourceDegree k+1 : ℕ)/sourceDenom)*
    ∑ j ∈ Finset.Icc 2 (sourceDegree k+1),
      ((sourceDegree k+1).choose j : ℝ)*x^(sourceDegree k+1-j)*h^(j-1))
def sourcePD (x y width : ℝ) : ℝ :=
  -(∑ k : Fin 3, (sourceWeight k/sourceDenom)*width*
    ∑ i ∈ Finset.range (sourceDegree k), y^(sourceDegree k-1-i)*x^i)
def sourceJ (x y : ℝ) : ℝ :=
  ∑ k : Fin 3, (sourceWeight k/(sourceDegree k+1 : ℕ)/sourceDenom)*
    ∑ i ∈ Finset.range (sourceDegree k), ((sourceDegree k-i : ℕ) : ℝ)*y^(sourceDegree k-1-i)*x^i

end MetricDistortion
/- END selected source-cancellation vocabulary -/

/- BEGIN integer-grid-tape vocabulary -/
namespace MetricDistortion
namespace FixedTape
structure I where
  lo : Int
  hi : Int

def decode (D : Int) (A : I) : QInterval := ⟨(A.lo : ℚ)/(D : ℚ),(A.hi : ℚ)/(D : ℚ)⟩
def add (A B : I) : I := ⟨A.lo+B.lo,A.hi+B.hi⟩
def neg (A : I) : I := ⟨-A.hi,-A.lo⟩
def mul (D : Int) (A B : I) : I :=
  let lo := min (min (A.lo*B.lo) (A.lo*B.hi)) (min (A.hi*B.lo) (A.hi*B.hi))
  let hi := max (max (A.lo*B.lo) (A.lo*B.hi)) (max (A.hi*B.lo) (A.hi*B.hi))
  ⟨lo/D,-((-hi)/D)⟩
def fromQ (D : Int) (q : ℚ) : I :=
  ⟨(q.num*D)/(q.den : Int),-(((-q.num)*D)/(q.den : Int))⟩

structure Row where
  value : I
  gradient : Fin 4 → I

def zero : I := ⟨0,0⟩
def zeroRow : Row := ⟨zero,fun _ => zero⟩
def decodeRow (D : Int) (A : Row) : TapeBounds :=
  ⟨decode D A.value,fun i => decode D (A.gradient i)⟩
def decodeBox (D : Int) (B : Fin 4 → I) : Box := fun i => decode D (B i)
 
def constRow (D : Int) (q : ℚ) : Row := ⟨fromQ D q,fun _ => zero⟩
def varRow (D : Int) (B : Fin 4 → I) (i : Fin 4) : Row :=
  ⟨B i,fun j => if i=j then ⟨D,D⟩ else zero⟩
def negRow (A : Row) : Row := ⟨neg A.value,fun i => neg (A.gradient i)⟩
def addRow (A C : Row) : Row := ⟨add A.value C.value,fun i => add (A.gradient i) (C.gradient i)⟩
def mulRow (D : Int) (A C : Row) : Row :=
  ⟨mul D A.value C.value,fun i => add (mul D (A.gradient i) C.value) (mul D A.value (C.gradient i))⟩
def step (D : Int) (B : Fin 4 → I) (done : List Row) : TapeOp → Row
  | .const q => constRow D q
  | .var i => varRow D B i
  | .neg a => negRow (done.getD a zeroRow)
  | .add a b => addRow (done.getD a zeroRow) (done.getD b zeroRow)
  | .mul a b => mulRow D (done.getD a zeroRow) (done.getD b zeroRow)
def rowsAux (D : Int) (B : Fin 4 → I) (done : List Row) : List TapeOp → List Row
  | [] => []
  | op::ops => let row := step D B done op; row::rowsAux D B (done++[row]) ops
def midBox (B : Fin 4 → I) : Fin 4 → I :=
  fun i => let q := ((B i).lo+(B i).hi)/2; ⟨q,q⟩
def centeredNumerator (D : Int) (B : Fin 4 → I) (root : ℕ) (rows centers : List Row) : Int :=
  let G := rows.getD root zeroRow
  let C := centers.getD root zeroRow
  2*D*C.value.hi + ∑ i, (max (G.gradient i).lo.natAbs (G.gradient i).hi.natAbs : Int)*((B i).hi-(B i).lo)
end FixedTape

end MetricDistortion
/- END integer-grid-tape vocabulary -/

namespace MetricDistortion.Contracts






















namespace Numerics_StarLaw

def Statement : Prop :=
(∃ D : DrawLaw, IsStarLaw D) ∧
  ∀ D, IsStarLaw D → (∀ u, phi D u = phiStar u) ∧
    (∀ u, Phi D u = PhiStar u) ∧ mu D = muStar ∧
    1+2*cStar = (213609/100000 : ℝ)

structure Needs : Prop where

  child_0 : Model_DrawLaws.Statement

end Numerics_StarLaw

namespace Numerics_WitnessData

def Statement : Prop :=
fixedCells.length = 152 ∧ etas.length = 9 ∧ cutoffs.length = 9 ∧
  rootLows.length = 9 ∧ rootHighs.length = 9 ∧
  (∀ c ∈ fixedCells, c.tauNums.length = 9)

end Numerics_WitnessData

namespace Numerics_TableCoverage

def Statement : Prop :=
(Icc (0 : ℝ) bStar ⊆ ⋃ j, root j) ∧
  (∀ j, IsClosed (root j) ∧ OrdConnected (root j) ∧ root j ⊆ Icc 0 bStar) ∧
  ∀ p ∈ Ioo (0 : ℝ) 1, ∃ c ∈ fixedCells, (c.lo : ℝ) ≤ p ∧ p < (c.hi : ℝ)

structure Needs : Prop where

  child_0 : Numerics_WitnessData.Statement

end Numerics_TableCoverage

namespace Numerics_RationalBernstein

def Statement : Prop :=
∀ n (a : Fin (n+1) → ℝ), (∀ k, 0 ≤ a k) →
  ∀ t ∈ Icc (0 : ℝ) 1,
    0 ≤ ∑ k, a k*(Nat.choose n k.val)*t^k.val*(1-t)^(n-k.val)

end Numerics_RationalBernstein

namespace Numerics_CorrectionSigns

def Statement : Prop :=
(∀ p ∈ Icc (0 : ℝ) 1, 0 ≤ lambdaStar p) ∧
  (∀ j, ∀ p ∈ Icc (0 : ℝ) 1, 0 ≤ tauStar j p) ∧
  lambdaStar 0 = 0 ∧ lambdaStar 1 = 0 ∧
  (∀ j, tauStar j 0 = 0 ∧ tauStar j 1 = eta j)

structure Needs : Prop where

  child_0 : Numerics_TableCoverage.Statement

  child_1 : Numerics_RationalBernstein.Statement

end Numerics_CorrectionSigns

namespace Numerics_ShiftedCoefficients

def Statement : Prop :=
∀ e : Polynomial ℚ, (∀ k, 0 ≤ e.coeff k) →
  ∀ x : ℝ, 0 ≤ x → 0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x e

end Numerics_ShiftedCoefficients

namespace Numerics_MeasureSigns

def Statement : Prop :=
∀ j, bStar < cutoff j ∧ cutoff j < 1 ∧ 0 ≤ atom j ∧ 0 < shift j ∧
  (∀ z ∈ Icc bStar (cutoff j), 0 ≤ eta j*phiStarDeriv z-1) ∧
  (∀ a, cutoff j ≤ a → a+eta j*psiStar a ≤ 0)

structure Needs : Prop where

  child_0 : Numerics_WitnessData.Statement

  child_1 : Numerics_ShiftedCoefficients.Statement

end Numerics_MeasureSigns

namespace Numerics_MeasureMass

def Statement : Prop :=
∀ j, nuStar j (Icc (0 : ℝ) 1) = ENNReal.ofReal cStar ∧
  nuStar j (Icc (0 : ℝ) 1)ᶜ = 0

structure Needs : Prop where

  child_0 : Numerics_MeasureSigns.Statement

  child_1 : Numerics_StarLaw.Statement

end Numerics_MeasureMass

namespace Numerics_PolynomialExpressions

def Statement : Prop :=
∀ e : PolyExpr, ∀ x : Fin 4 → ℚ,
  eval e (fun i => (x i : ℝ)) = (qEval e x : ℝ)

end Numerics_PolynomialExpressions

namespace Numerics_RationalIntervals

def Statement : Prop :=
∀ e B, ValidBox B → ∀ x, inBox B x →
  eval e x ∈ Icc ((intervalEval e B).lo : ℝ) ((intervalEval e B).hi : ℝ)

structure Needs : Prop where

  child_0 : Numerics_PolynomialExpressions.Statement

end Numerics_RationalIntervals

namespace Numerics_DerivativeBounds

def Statement : Prop :=
∀ e i x, HasDerivAt
  (fun t : ℝ => eval e (Function.update x i t)) (eval (derivative i e) x) (x i)

structure Needs : Prop where

  child_0 : Numerics_PolynomialExpressions.Statement

end Numerics_DerivativeBounds

namespace Numerics_CenteredBounds

def Statement : Prop :=
∀ e B, ValidBox B → ∀ x, inBox B x → eval e x ≤ (centeredBound e B : ℝ)

structure Needs : Prop where

  child_0 : Numerics_RationalIntervals.Statement

  child_1 : Numerics_DerivativeBounds.Statement

  child_2 : Numerics_PolynomialExpressions.Statement

end Numerics_CenteredBounds

namespace Numerics_MonotoneFaces

def Statement : Prop :=
∀ e B i upper, ValidBox B →
  (if upper then 0 ≤ (intervalEval (derivative i e) B).lo else
    (intervalEval (derivative i e) B).hi ≤ 0) →
  (∀ x, inBox (faceBox B i upper) x → eval e x ≤ 0) →
  ∀ x, inBox B x → eval e x ≤ 0

structure Needs : Prop where

  child_0 : Numerics_RationalIntervals.Statement

  child_1 : Numerics_DerivativeBounds.Statement

end Numerics_MonotoneFaces

namespace Numerics_TreeSoundness

def Statement : Prop :=
∀ e B tree, ValidBox B → verifyTree e B tree = true →
  ∀ x, inBox B x → eval e x ≤ 0

structure Needs : Prop where

  child_0 : Numerics_RationalIntervals.Statement

  child_1 : Numerics_CenteredBounds.Statement

  child_2 : Numerics_MonotoneFaces.Statement

end Numerics_TreeSoundness

namespace Numerics_MeasureIntervals

def Statement : Prop :=
∀ j : Fin 9, ∀ a A : ℝ, 0 ≤ a → a ≤ A → A ≤ 1 →
  (nuStar j (Ico a A)).toReal =
    (if a ≤ bStar ∧ bStar < A then atom j else 0) +
    (∫ z in Ico a A ∩ Ioo bStar (cutoff j), (eta j*phiStarDeriv z-1))

structure Needs : Prop where

  child_0 : Numerics_MeasureSigns.Statement

  child_1 : Numerics_MeasureMass.Statement

end Numerics_MeasureIntervals

namespace Numerics_RankMeasurePrimitive

def Statement : Prop :=
(∀ j : Fin 9, ∀ a A : ℝ, 0 ≤ a → a ≤ A → A ≤ 1 →
  (nuStar j (Ico a A)).toReal = rankPotential j A-rankPotential j a) ∧
(∀ j : Fin 9, ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
  (nuStar j (Icc a 1)).toReal = cStar-rankPotential j a)

structure Needs : Prop where

  child_0 : Numerics_MeasureIntervals.Statement

  child_1 : Numerics_MeasureMass.Statement

  child_2 : Numerics_MeasureSigns.Statement

end Numerics_RankMeasurePrimitive

namespace Numerics_TapeReplay

def Statement : Prop :=
∀ tape root B tree, ValidBox B → verifyTapeTree tape root B tree = true →
  ∀ x, inBox B x → eval (tapeExpr tape root) x ≤ 0

structure Needs : Prop where

  child_0 : Numerics_DerivativeBounds.Statement

  child_1 : Numerics_RationalIntervals.Statement

end Numerics_TapeReplay

namespace Numerics_DomainTemplates

def Statement : Prop :=
∀ a p A r : ℝ,
  (0 ≤ a ∧ a ≤ min p r ∧ p ≤ A ∧ A ≤ 1) →
  ({z : ℝ | z ∈ Icc 0 1 ∧ a ≤ min z r ∧ min z r < A} =
    if r < A then Icc a 1 else Ico a A)

end Numerics_DomainTemplates

namespace Numerics_EndpointBounds

def Statement : Prop :=
∀ j, EndpointFamily j

structure Needs : Prop where

  child_0 : Numerics_TreeSoundness.Statement

  child_1 : Numerics_MeasureIntervals.Statement

  child_2 : Numerics_StarLaw.Statement

  child_3 : Numerics_CorrectionSigns.Statement

  child_4 : Numerics_RankMeasurePrimitive.Statement

  child_5 : Numerics_MeasureSigns.Statement

  child_6 : Numerics_DomainTemplates.Statement

  child_7 : Numerics_TableCoverage.Statement

  child_8 : Numerics_TapeReplay.Statement

end Numerics_EndpointBounds

namespace Numerics_MixedDifference

def Statement : Prop :=
∀ y h w : ℝ, 0 ≤ y → 0 ≤ h → 0 ≤ w →
  0 ≤ HStar (y+w)-HStar y-HStar (y+h+w)+HStar (y+h)

structure Needs : Prop where

  child_0 : Numerics_ShiftedCoefficients.Statement

end Numerics_MixedDifference

namespace Numerics_FactorIdentities

def Statement : Prop :=
(∀ x : ℝ, HStar x = muStar*x-PhiStar x) ∧
  (∀ j : Fin 9, ∀ a p A r : ℝ,
    internalResidual j a p A r-firstResidual j a p r =
      lambdaStar p*(HStar (a+A-p)-HStar A-HStar (a+1-p)) +
      cStar-oldPotential j A)

structure Needs : Prop where

  child_0 : Numerics_WitnessData.Statement

end Numerics_FactorIdentities

namespace Numerics_BranchComposition

def Statement : Prop :=
(∀ j, FiniteFamily j) → (∀ j, StrongCrossing j) →
  ∀ D, IsStarLaw D → ∀ j r, r ∈ root j ∪ Icc bStar 1 →
  ∀ p ∈ Ioo (0 : ℝ) 1, ∀ a A, 0 ≤ a → a ≤ min p r → p ≤ A → A ≤ 1 →
    LocalCut D fixedWitness j a p A r

structure Needs : Prop where

  child_0 : Numerics_MixedDifference.Statement

  child_1 : Numerics_MeasureIntervals.Statement

  child_2 : Numerics_DomainTemplates.Statement

  child_3 : Numerics_FactorIdentities.Statement

  child_4 : Numerics_MeasureSigns.Statement

  child_5 : Numerics_StarLaw.Statement

  child_6 : Numerics_TableCoverage.Statement

  child_7 : Numerics_MeasureMass.Statement

  child_8 : Numerics_CorrectionSigns.Statement

  child_9 : Numerics_RankMeasurePrimitive.Statement

end Numerics_BranchComposition

namespace Numerics_Robustness

def Statement : Prop :=
∀ p ∈ Icc (0 : ℝ) 1, (1-p)*lambdaStar p+tauStar 0 p ≤ 16

structure Needs : Prop where

  child_0 : Numerics_WitnessData.Statement

  child_1 : Numerics_RationalBernstein.Statement

  child_2 : Numerics_TableCoverage.Statement

end Numerics_Robustness

namespace Numerics_Benchmark

def Statement : Prop :=
phiStar bStar ≤ muStar ∧ 0 ≤ cStar ∧ bStar ∈ Icc (0 : ℝ) 1

structure Needs : Prop where

  child_0 : Numerics_TreeSoundness.Statement

end Numerics_Benchmark

namespace Numerics_FiniteTemplates

def Statement : Prop :=
∀ j a p A r, 0 ≤ a → a ≤ p → p ≤ A → A ≤ r → r ≤ 1 →
  internalResidual j a p A r =
    a+lambdaStar p*(PhiStar a+PhiStar A-PhiStar (a+A-p)-p*muStar) +
    tauStar j p*(muStar-phiStar r)+oldPotential j a-oldPotential j A

structure Needs : Prop where

  child_0 : Numerics_FactorIdentities.Statement

end Numerics_FiniteTemplates

namespace Numerics_RoundedTapeCandidates

def Statement : Prop :=
∀ bits (pick : ℕ → TapeBounds → Bool) B tape,
  tapeRefsValidAux 0 tape = true →
  tapeCheck B tape (roundedTapeRows bits pick B tape) = true

end Numerics_RoundedTapeCandidates

namespace Numerics_SourceCancellations

def Statement : Prop :=
(∀ x : ℝ, x*sourceF0 x=HStar x/sourceDenom) ∧
(∀ x : ℝ, (1-x)*sourceB x=HStar x/sourceDenom) ∧
(∀ x h : ℝ, h*(psiStar x/sourceDenom+sourceInc x h)=
  (HStar (x+h)-HStar x)/sourceDenom) ∧
(∀ x y : ℝ, sourcePD x y (y-x)=(psiStar y-psiStar x)/sourceDenom) ∧
(∀ x y : ℝ, (y-x)^2*sourceJ x y=
  (HStar y-HStar x-(y-x)*psiStar y)/sourceDenom)

end Numerics_SourceCancellations

namespace Numerics_FixedTapeCandidates

def Statement : Prop :=
(∀ (D : ℤ), 0 < D → ∀ (B : Fin 4 → FixedTape.I) (tape : List TapeOp),
  tapeRefsValidAux 0 tape = true →
  tapeCheck (FixedTape.decodeBox D B) tape
    ((FixedTape.rowsAux D B [] tape).map (FixedTape.decodeRow D)) = true) ∧
(∀ (D : ℤ), 0 < D → ∀ (B : Fin 4 → FixedTape.I) (root : ℕ) (rows centers : List FixedTape.Row),
  FixedTape.centeredNumerator D B root rows centers ≤ 0 →
  tapeCenteredBound (FixedTape.decodeBox D B) root
    (rows.map (FixedTape.decodeRow D)) (centers.map (FixedTape.decodeRow D)) ≤ 0) ∧
(∀ (D : ℤ) (B : Fin 4 → FixedTape.I),
  (∀ i, 2 ∣ (B i).lo+(B i).hi) →
  midpointBox (FixedTape.decodeBox D B) = FixedTape.decodeBox D (FixedTape.midBox B)) ∧
(∀ (D z : ℤ), 0 < D →
  (z ≤ 0 → (z : ℚ)/(D : ℚ) ≤ 0) ∧ (0 ≤ z → 0 ≤ (z : ℚ)/(D : ℚ))) ∧
(∀ (D : ℤ), 0 < D → ∀ (B : Fin 4 → FixedTape.I),
  (∀ i, (B i).lo ≤ (B i).hi) → ValidBox (FixedTape.decodeBox D B))

end Numerics_FixedTapeCandidates

namespace Numerics_StrongCrossing0

def Statement : Prop :=
StrongCrossing (0 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_TableCoverage.Statement

  child_3 : Numerics_TapeReplay.Statement

  child_4 : Numerics_RoundedTapeCandidates.Statement

  child_5 : Numerics_SourceCancellations.Statement

  child_6 : Numerics_FixedTapeCandidates.Statement

end Numerics_StrongCrossing0

namespace Numerics_FiniteCoordinates

def Statement : Prop :=
(∀ (lo hi : ℚ) (r0 r1 p a r : ℝ), ((lo : ℝ) < p ∧ p ≤ (hi : ℝ)) → ((hi : ℝ) ≤ r0 ∨ r0 ≤ (lo : ℝ)) →
  r ∈ Icc r0 r1 → 0 ≤ a → a ≤ min p r → a ≤ r0 →
  ∃ x : Fin 4 → ℝ, inBox (![⟨lo,hi⟩,⟨0,1⟩,⟨0,1⟩,⟨0,1⟩]) x ∧ x 0 = p ∧ (if (hi : ℝ) ≤ r0 then x 0 else r0)*x 1 = a ∧ r0+(r1-r0)*x 2 = r) ∧
(∀ (lo hi : ℚ) (r0 r1 p a r : ℝ), ((lo : ℝ) < p ∧ p ≤ (hi : ℝ)) → ((hi : ℝ) ≤ r0 ∨ r0 ≤ (lo : ℝ)) → ((hi : ℝ) ≤ r1 ∨ r1 ≤ (lo : ℝ)) →
  r ∈ Icc r0 r1 → a ≤ min p r → r0 < a → r0 ≤ (lo : ℝ) ∧
  ∃ x : Fin 4 → ℝ, inBox (![⟨lo,hi⟩,⟨0,1⟩,⟨0,1⟩,⟨0,1⟩]) x ∧ x 0 = p ∧ (r0+((if (hi : ℝ) ≤ r1 then x 0 else r1)-r0)*x 1) = a ∧ (r0+((if (hi : ℝ) ≤ r1 then x 0 else r1)-r0)*x 1)+(r1-(r0+((if (hi : ℝ) ≤ r1 then x 0 else r1)-r0)*x 1))*x 2 = r) ∧
(∀ (lo hi : ℚ) (r0 r1 p a cap r : ℝ), ((lo : ℝ) < p ∧ p ≤ (hi : ℝ)) → ((hi : ℝ) ≤ r0 ∨ r0 ≤ (lo : ℝ)) → ((hi : ℝ) ≤ r1 ∨ r1 ≤ (lo : ℝ)) →
  r ∈ Icc r0 r1 → 0 ≤ a → a ≤ p → p ≤ cap → cap ≤ r → (hi : ℝ) ≤ r1 ∧
  ∃ x : Fin 4 → ℝ, inBox (![⟨lo,hi⟩,⟨0,1⟩,⟨0,1⟩,⟨0,1⟩]) x ∧ x 0 = p ∧ x 0*x 1 = a ∧ x 0+(((if (hi : ℝ) ≤ r0 then r0 else x 0)+(r1-(if (hi : ℝ) ≤ r0 then r0 else x 0))*x 3)-x 0)*x 2 = cap ∧ ((if (hi : ℝ) ≤ r0 then r0 else x 0)+(r1-(if (hi : ℝ) ≤ r0 then r0 else x 0))*x 3) = r) ∧
(∀ (lo hi : ℚ) (b p a r : ℝ), ((lo : ℝ) < p ∧ p ≤ (hi : ℝ)) → ((hi : ℝ) ≤ b ∨ b ≤ (lo : ℝ)) →
  r ∈ Icc b 1 → 0 ≤ a → a ≤ min p r → a ≤ b →
  ∃ x : Fin 4 → ℝ, inBox (![⟨lo,hi⟩,⟨0,1⟩,⟨0,1⟩,⟨0,1⟩]) x ∧ x 0 = p ∧ (if (hi : ℝ) ≤ b then x 0 else b)*x 1 = a ∧ b+(1-b)*x 2 = r) ∧
(∀ (lo hi : ℚ) (b p a r : ℝ), ((lo : ℝ) < p ∧ p ≤ (hi : ℝ)) → ((hi : ℝ) ≤ b ∨ b ≤ (lo : ℝ)) →
  r ≤ 1 → a ≤ min p r → b < a → b ≤ (lo : ℝ) ∧
  ∃ x : Fin 4 → ℝ, inBox (![⟨lo,hi⟩,⟨0,1⟩,⟨0,1⟩,⟨0,1⟩]) x ∧ x 0 = p ∧ (b+(x 0-b)*x 1) = a ∧ (b+(x 0-b)*x 1)+(1-(b+(x 0-b)*x 1))*x 2 = r) ∧
(∀ (lo hi : ℚ) (b p a cap r : ℝ), ((lo : ℝ) < p ∧ p ≤ (hi : ℝ)) → ((hi : ℝ) ≤ b ∨ b ≤ (lo : ℝ)) →
  r ∈ Icc b 1 → 0 ≤ a → a ≤ p → p ≤ cap → cap ≤ b → (hi : ℝ) ≤ b ∧
  ∃ x : Fin 4 → ℝ, inBox (![⟨lo,hi⟩,⟨0,1⟩,⟨0,1⟩,⟨0,1⟩]) x ∧ x 0 = p ∧ x 0*x 1 = a ∧ x 0+(b-x 0)*x 2 = cap ∧ b+(1-b)*x 3 = r) ∧
(∀ (lo hi : ℚ) (b p a cap r : ℝ), ((lo : ℝ) < p ∧ p ≤ (hi : ℝ)) → ((hi : ℝ) ≤ b ∨ b ≤ (lo : ℝ)) →
  r ≤ 1 → a ≤ p → b < a → p ≤ cap → cap ≤ r → b ≤ (lo : ℝ) ∧
  ∃ x : Fin 4 → ℝ, inBox (![⟨lo,hi⟩,⟨0,1⟩,⟨0,1⟩,⟨0,1⟩]) x ∧ x 0 = p ∧ (b+(x 0-b)*x 1) = a ∧ (x 0+(1-x 0)*x 2) = cap ∧ (x 0+(1-x 0)*x 2)+(1-(x 0+(1-x 0)*x 2))*x 3 = r)

end Numerics_FiniteCoordinates

namespace Numerics_FiniteFamily0

def Statement : Prop :=
FiniteFamily (0 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_ShiftedCoefficients.Statement

  child_3 : Numerics_TableCoverage.Statement

  child_4 : Numerics_TapeReplay.Statement

  child_5 : Numerics_RoundedTapeCandidates.Statement

  child_6 : Numerics_StrongCrossing0.Statement

  child_7 : Numerics_MeasureSigns.Statement

  child_8 : Numerics_SourceCancellations.Statement

  child_9 : Numerics_FiniteCoordinates.Statement

  child_10 : Numerics_FixedTapeCandidates.Statement

end Numerics_FiniteFamily0

namespace Numerics_StrongCrossing1

def Statement : Prop :=
StrongCrossing (1 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_TableCoverage.Statement

  child_3 : Numerics_TapeReplay.Statement

  child_4 : Numerics_RoundedTapeCandidates.Statement

  child_5 : Numerics_SourceCancellations.Statement

  child_6 : Numerics_FixedTapeCandidates.Statement

end Numerics_StrongCrossing1

namespace Numerics_FiniteFamily1

def Statement : Prop :=
FiniteFamily (1 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_ShiftedCoefficients.Statement

  child_3 : Numerics_TableCoverage.Statement

  child_4 : Numerics_TapeReplay.Statement

  child_5 : Numerics_RoundedTapeCandidates.Statement

  child_6 : Numerics_StrongCrossing1.Statement

  child_7 : Numerics_MeasureSigns.Statement

  child_8 : Numerics_SourceCancellations.Statement

  child_9 : Numerics_FiniteCoordinates.Statement

  child_10 : Numerics_FixedTapeCandidates.Statement

end Numerics_FiniteFamily1

namespace Numerics_StrongCrossing2

def Statement : Prop :=
StrongCrossing (2 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_TableCoverage.Statement

  child_3 : Numerics_TapeReplay.Statement

  child_4 : Numerics_RoundedTapeCandidates.Statement

  child_5 : Numerics_SourceCancellations.Statement

  child_6 : Numerics_FixedTapeCandidates.Statement

end Numerics_StrongCrossing2

namespace Numerics_FiniteFamily2

def Statement : Prop :=
FiniteFamily (2 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_ShiftedCoefficients.Statement

  child_3 : Numerics_TableCoverage.Statement

  child_4 : Numerics_TapeReplay.Statement

  child_5 : Numerics_RoundedTapeCandidates.Statement

  child_6 : Numerics_StrongCrossing2.Statement

  child_7 : Numerics_MeasureSigns.Statement

  child_8 : Numerics_SourceCancellations.Statement

  child_9 : Numerics_FiniteCoordinates.Statement

  child_10 : Numerics_FixedTapeCandidates.Statement

end Numerics_FiniteFamily2

namespace Numerics_StrongCrossing3

def Statement : Prop :=
StrongCrossing (3 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_TableCoverage.Statement

  child_3 : Numerics_TapeReplay.Statement

  child_4 : Numerics_RoundedTapeCandidates.Statement

  child_5 : Numerics_SourceCancellations.Statement

  child_6 : Numerics_FixedTapeCandidates.Statement

end Numerics_StrongCrossing3

namespace Numerics_FiniteFamily3

def Statement : Prop :=
FiniteFamily (3 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_ShiftedCoefficients.Statement

  child_3 : Numerics_TableCoverage.Statement

  child_4 : Numerics_TapeReplay.Statement

  child_5 : Numerics_RoundedTapeCandidates.Statement

  child_6 : Numerics_StrongCrossing3.Statement

  child_7 : Numerics_MeasureSigns.Statement

  child_8 : Numerics_SourceCancellations.Statement

  child_9 : Numerics_FiniteCoordinates.Statement

  child_10 : Numerics_FixedTapeCandidates.Statement

end Numerics_FiniteFamily3

namespace Numerics_StrongCrossing4

def Statement : Prop :=
StrongCrossing (4 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_TableCoverage.Statement

  child_3 : Numerics_TapeReplay.Statement

  child_4 : Numerics_RoundedTapeCandidates.Statement

  child_5 : Numerics_SourceCancellations.Statement

  child_6 : Numerics_FixedTapeCandidates.Statement

end Numerics_StrongCrossing4

namespace Numerics_FiniteFamily4

def Statement : Prop :=
FiniteFamily (4 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_ShiftedCoefficients.Statement

  child_3 : Numerics_TableCoverage.Statement

  child_4 : Numerics_TapeReplay.Statement

  child_5 : Numerics_RoundedTapeCandidates.Statement

  child_6 : Numerics_StrongCrossing4.Statement

  child_7 : Numerics_MeasureSigns.Statement

  child_8 : Numerics_SourceCancellations.Statement

  child_9 : Numerics_FiniteCoordinates.Statement

  child_10 : Numerics_FixedTapeCandidates.Statement

end Numerics_FiniteFamily4

namespace Numerics_StrongCrossing5

def Statement : Prop :=
StrongCrossing (5 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_TableCoverage.Statement

  child_3 : Numerics_TapeReplay.Statement

  child_4 : Numerics_RoundedTapeCandidates.Statement

  child_5 : Numerics_SourceCancellations.Statement

  child_6 : Numerics_FixedTapeCandidates.Statement

end Numerics_StrongCrossing5

namespace Numerics_FiniteFamily5

def Statement : Prop :=
FiniteFamily (5 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_ShiftedCoefficients.Statement

  child_3 : Numerics_TableCoverage.Statement

  child_4 : Numerics_TapeReplay.Statement

  child_5 : Numerics_RoundedTapeCandidates.Statement

  child_6 : Numerics_StrongCrossing5.Statement

  child_7 : Numerics_MeasureSigns.Statement

  child_8 : Numerics_SourceCancellations.Statement

  child_9 : Numerics_FiniteCoordinates.Statement

  child_10 : Numerics_FixedTapeCandidates.Statement

end Numerics_FiniteFamily5

namespace Numerics_StrongCrossing6

def Statement : Prop :=
StrongCrossing (6 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_TableCoverage.Statement

  child_3 : Numerics_TapeReplay.Statement

  child_4 : Numerics_RoundedTapeCandidates.Statement

  child_5 : Numerics_SourceCancellations.Statement

  child_6 : Numerics_FixedTapeCandidates.Statement

end Numerics_StrongCrossing6

namespace Numerics_FiniteFamily6

def Statement : Prop :=
FiniteFamily (6 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_ShiftedCoefficients.Statement

  child_3 : Numerics_TableCoverage.Statement

  child_4 : Numerics_TapeReplay.Statement

  child_5 : Numerics_RoundedTapeCandidates.Statement

  child_6 : Numerics_StrongCrossing6.Statement

  child_7 : Numerics_MeasureSigns.Statement

  child_8 : Numerics_SourceCancellations.Statement

  child_9 : Numerics_FiniteCoordinates.Statement

  child_10 : Numerics_FixedTapeCandidates.Statement

end Numerics_FiniteFamily6

namespace Numerics_StrongCrossing7

def Statement : Prop :=
StrongCrossing (7 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_TableCoverage.Statement

  child_3 : Numerics_TapeReplay.Statement

  child_4 : Numerics_RoundedTapeCandidates.Statement

  child_5 : Numerics_SourceCancellations.Statement

  child_6 : Numerics_FixedTapeCandidates.Statement

end Numerics_StrongCrossing7

namespace Numerics_FiniteFamily7

def Statement : Prop :=
FiniteFamily (7 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_ShiftedCoefficients.Statement

  child_3 : Numerics_TableCoverage.Statement

  child_4 : Numerics_TapeReplay.Statement

  child_5 : Numerics_RoundedTapeCandidates.Statement

  child_6 : Numerics_StrongCrossing7.Statement

  child_7 : Numerics_MeasureSigns.Statement

  child_8 : Numerics_SourceCancellations.Statement

  child_9 : Numerics_FiniteCoordinates.Statement

  child_10 : Numerics_FixedTapeCandidates.Statement

end Numerics_FiniteFamily7

namespace Numerics_StrongCrossing8

def Statement : Prop :=
StrongCrossing (8 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_TableCoverage.Statement

  child_3 : Numerics_TapeReplay.Statement

  child_4 : Numerics_RoundedTapeCandidates.Statement

  child_5 : Numerics_SourceCancellations.Statement

  child_6 : Numerics_FixedTapeCandidates.Statement

end Numerics_StrongCrossing8

namespace Numerics_FiniteFamily8

def Statement : Prop :=
FiniteFamily (8 : Fin 9)

structure Needs : Prop where

  child_0 : Numerics_FiniteTemplates.Statement

  child_1 : Numerics_TreeSoundness.Statement

  child_2 : Numerics_ShiftedCoefficients.Statement

  child_3 : Numerics_TableCoverage.Statement

  child_4 : Numerics_TapeReplay.Statement

  child_5 : Numerics_RoundedTapeCandidates.Statement

  child_6 : Numerics_StrongCrossing8.Statement

  child_7 : Numerics_MeasureSigns.Statement

  child_8 : Numerics_SourceCancellations.Statement

  child_9 : Numerics_FiniteCoordinates.Statement

  child_10 : Numerics_FixedTapeCandidates.Statement

end Numerics_FiniteFamily8

namespace Numerics_CompleteWitness

def Statement : Prop :=
(∃ D, IsStarLaw D) ∧ (∀ D, IsStarLaw D → ValidCut D fixedWitness) ∧
  (∀ p ∈ Icc (0 : ℝ) 1, (1-p)*lambdaStar p+tauStar 0 p ≤ 16)

structure Needs : Prop where

  child_0 : Numerics_StarLaw.Statement

  child_1 : Numerics_TableCoverage.Statement

  child_2 : Numerics_CorrectionSigns.Statement

  child_3 : Numerics_MeasureMass.Statement

  child_4 : Numerics_EndpointBounds.Statement

  child_5 : Numerics_BranchComposition.Statement

  child_6 : Numerics_Robustness.Statement

  child_7 : Numerics_Benchmark.Statement

  child_8 : Numerics_FiniteFamily0.Statement

  child_9 : Numerics_FiniteFamily1.Statement

  child_10 : Numerics_FiniteFamily2.Statement

  child_11 : Numerics_FiniteFamily3.Statement

  child_12 : Numerics_FiniteFamily4.Statement

  child_13 : Numerics_FiniteFamily5.Statement

  child_14 : Numerics_FiniteFamily6.Statement

  child_15 : Numerics_FiniteFamily7.Statement

  child_16 : Numerics_FiniteFamily8.Statement

  child_17 : Numerics_StrongCrossing0.Statement

  child_18 : Numerics_StrongCrossing1.Statement

  child_19 : Numerics_StrongCrossing2.Statement

  child_20 : Numerics_StrongCrossing3.Statement

  child_21 : Numerics_StrongCrossing4.Statement

  child_22 : Numerics_StrongCrossing5.Statement

  child_23 : Numerics_StrongCrossing6.Statement

  child_24 : Numerics_StrongCrossing7.Statement

  child_25 : Numerics_StrongCrossing8.Statement

end Numerics_CompleteWitness
















namespace Results_ExactStarDistortion

def Statement : Prop :=
∀ D, IsStarLaw D → ∀ n m, 0 < n → 0 < m →
  ∀ (σ : Profile n m) P, Stable D σ P → distortion σ P ≤ ENNReal.ofReal (213609/100000 : ℝ)

structure Needs : Prop where

  child_0 : Geometry_RankCutCriterion.Statement

  child_1 : Numerics_CompleteWitness.Statement

end Results_ExactStarDistortion

namespace Results_MainUpper

def Statement : Prop :=
∃ R : VotingRule, ∀ n m hn hm σ,
  distortion σ (R n m hn hm σ) ≤ ENNReal.ofReal (213609/100000 : ℝ)

structure Needs : Prop where

  child_0 : Stability_Existence.Statement

  child_1 : Numerics_CompleteWitness.Statement

  child_2 : Results_ExactStarDistortion.Statement

end Results_MainUpper

namespace Lower_ReferenceLotteries

def Statement : Prop :=
∀ N : ℕ, 0 < N → ∀ t ∈ Icc (0 : ℝ) 1,
  ∃ P : Lottery (N+1), Reference t P

structure Needs : Prop where

  child_0 : Model_Lotteries.Statement

end Lower_ReferenceLotteries

namespace Lower_SymmetricAverages

def Statement : Prop :=
∀ n N k, 0 < n → 0 < k → k < N → ∀ z ∈ Ioc (0 : ℝ) 1,
  ∀ σ : Profile n (N+1), Symmetric σ k z → ∀ f : Ranking (N+1) → ℝ,
  avg (fun v => f (σ v)) =
    (z/(Nat.factorial N))*∑ r ∈ Finset.univ.filter (fun r : Ranking (N+1) => (r 0).val = k), f r +
    ((1-z)/(Nat.factorial N))*∑ r ∈ Finset.univ.filter (fun r : Ranking (N+1) => (r 0).val = N), f r

end Lower_SymmetricAverages

namespace Lower_FiniteElectorate

def Statement : Prop :=
∀ N k : ℕ, 0 < k → k < N → ∀ z : ℚ,
  0 < z → z ≤ 1 → ∃ n, 0 < n ∧ ∃ σ : Profile n (N+1), Symmetric σ k z

structure Needs : Prop where

  child_0 : Model_Profiles.Statement

end Lower_FiniteElectorate

namespace Lower_PermutationInvariance

def Statement : Prop :=
∀ n N k, 0 < n → 0 < k → k < N → ∀ z ∈ Ioc (0 : ℝ) 1,
  ∀ D (σ : Profile n (N+1)), Symmetric σ k z →
  ∀ g : Ranking (N+1), g 0 = 0 → ∀ P Q : Lottery (N+1),
  (∀ c, Q.val c = P.val (g c)) → ∀ c, score D σ Q c = score D σ P (g c)

structure Needs : Prop where
  child_0 : Comparison_CandidateDraws.Statement
  child_1 : Lower_SymmetricAverages.Statement

end Lower_PermutationInvariance

namespace Lower_Symmetrization

def Statement : Prop :=
∀ n N k, 0 < n → 0 < k → k < N → ∀ z ∈ Ioc (0 : ℝ) 1,
  ∀ D (σ : Profile n (N+1)), Symmetric σ k z → ∀ Q, Stable D σ Q →
  ∃ P, Reference (1-Q.val 0) P ∧ Stable D σ P

structure Needs : Prop where

  child_0 : Comparison_CandidateDraws.Statement

  child_1 : Lower_ReferenceLotteries.Statement

  child_2 : Lower_FiniteElectorate.Statement

  child_3 : Lower_SymmetricAverages.Statement

  child_4 : Lower_PermutationInvariance.Statement

end Lower_Symmetrization

namespace Lower_ForcedMass

def Statement : Prop :=
∀ n N k, 0 < n → 0 < k → k < N → ∀ z ∈ Ioc (0 : ℝ) 1,
  ∀ D (σ : Profile n (N+1)), Symmetric σ k z →
  ∀ p ∈ Ioc (0 : ℝ) 1, ∀ P, Reference p P → score D σ P 0 < mu D →
  ∀ Q, Stable D σ Q → p ≤ 1-Q.val 0

structure Needs : Prop where

  child_0 : Lower_Symmetrization.Statement

  child_1 : Comparison_SelfPlay.Statement

  child_2 : Comparison_CandidateDraws.Statement

  child_3 : Lower_PermutationInvariance.Statement

  child_4 : Lower_ReferenceLotteries.Statement

end Lower_ForcedMass





namespace Lower_OffsetCost

def Statement : Prop :=
∀ n N k, 0 < n → 0 < k → k < N → ∀ z ∈ Ioc (0 : ℝ) 1,
  ∀ σ : Profile n (N+1), Symmetric σ k z → ∀ Q,
    ENNReal.ofReal (1+2*(1-Q.val 0)*((k : ℝ)/N+(1-z)/z)) ≤ distortion σ Q

structure Needs : Prop where

  child_0 : Offsets_MetricRealization.Statement

  child_1 : Lower_FiniteElectorate.Statement

  child_2 : Lower_SymmetricAverages.Statement

end Lower_OffsetCost

namespace Lower_RationalPerturbation

def Statement : Prop :=
∀ f : ℝ → ℝ, ∀ z : ℝ, 0 < z → z ≤ 1 →
  ContinuousAt f z → f z < 0 → ∃ q : ℚ, 0 < q ∧ (q : ℝ) < z ∧ f q < 0

end Lower_RationalPerturbation

namespace Lower_ScoreFormula

def Statement : Prop :=
(∀ n N k, 0 < n → 0 < k → k < N → ∀ z ∈ Ioc (0 : ℝ) 1,
  ∀ D (σ : Profile n (N+1)), Symmetric σ k z →
  ∀ p ∈ Ioo (0 : ℝ) 1, ∀ P, Reference p P →
    (1-p)*score D σ P 0 = z*(Phi D (p*k/N+1-p)-Phi D (p*k/N)) +
      (1-z)*(mu D-Phi D p)) ∧
(∀ n N k, 0 < n → 0 < k → k < N → ∀ z ∈ Ioc (0 : ℝ) 1,
  ∀ D (σ : Profile n (N+1)), Symmetric σ k z →
  ∀ p ∈ Icc (0 : ℝ) 1, ∀ P, Reference p P →
    score D σ P 0 = z*(∫ s in (0 : ℝ)..1, phi D (p*k/N+s*(1-p))) +
      (1-z)*(∫ s in (0 : ℝ)..1, phi D (p+s*(1-p))))

structure Needs : Prop where

  child_0 : Comparison_CandidateDraws.Statement

  child_1 : Lower_ReferenceLotteries.Statement

  child_2 : Lower_SymmetricAverages.Statement

  child_3 : Analysis_GeneratingFunction.Statement

end Lower_ScoreFormula

namespace Lower_FirstCase

def Statement : Prop :=
∀ D : DrawLaw, phi D (71/125) < mu D →
  ∃ z : ℚ, 0 < z ∧ z ≤ 1 ∧ ∀ n, 0 < n → ∀ σ : Profile n 126,
  Symmetric σ 71 z → ∀ Q, Stable D σ Q → ENNReal.ofReal (267/125 : ℝ) < distortion σ Q

structure Needs : Prop where

  child_0 : Lower_ForcedMass.Statement

  child_1 : Lower_OffsetCost.Statement

  child_2 : Lower_RationalPerturbation.Statement

  child_3 : Comparison_CandidateDraws.Statement

  child_4 : Lower_ScoreFormula.Statement

  child_5 : Lower_ReferenceLotteries.Statement

end Lower_FirstCase

namespace Lower_NormalizedTail

def Statement : Prop :=
∀ d : ℕ, 3 ≤ d →
  (7/26 : ℝ)*( (7/26 : ℝ)/(3/4 : ℝ))^(d+1) ≤
    (7/26 : ℝ)*((7/26 : ℝ)/(3/4 : ℝ))^d ∧
  ((d+2 : ℕ) : ℝ)*((71/125 : ℝ)/(3/4 : ℝ))^(d+1) <
    ((d+1 : ℕ) : ℝ)*((71/125 : ℝ)/(3/4 : ℝ))^d

end Lower_NormalizedTail

namespace Lower_IntegerPowerGaps

def Statement : Prop :=
(∀ d : ℕ, 0 < d → 0 < lowerGap d) ∧
  lowerGap 1 = (97/1625000 : ℝ) ∧ lowerGap 2 = (22093/5281250000 : ℝ) ∧
  ((71/125 : ℝ)-1/52)*(3/4 : ℝ)^3-(7/26 : ℝ)^4-
    4*((71/125 : ℝ)-7/26)*(71/125 : ℝ)^3 > 1/200

structure Needs : Prop where

  child_0 : Lower_NormalizedTail.Statement

end Lower_IntegerPowerGaps

namespace Lower_AveragedPowerGap

def Statement : Prop :=
∀ D : DrawLaw,
  Phi D (7/26)+(71/125-7/26)*phi D (71/125) <
    Phi D (1/52)+((71/125-1/52)/(3/4))*Phi D (3/4)

structure Needs : Prop where

  child_0 : Lower_IntegerPowerGaps.Statement

  child_1 : Analysis_IntegralMixture.Statement

  child_2 : Model_DrawLaws.Statement

end Lower_AveragedPowerGap

namespace Lower_SecondCase

def Statement : Prop :=
∀ D : DrawLaw, mu D ≤ phi D (71/125) →
  ∃ z : ℚ, 0 < z ∧ z ≤ 1 ∧ ∀ n, 0 < n → ∀ σ : Profile n 40,
  Symmetric σ 1 z → ∀ Q, Stable D σ Q → ENNReal.ofReal (267/125 : ℝ) < distortion σ Q

structure Needs : Prop where

  child_0 : Lower_ScoreFormula.Statement

  child_1 : Lower_AveragedPowerGap.Statement

  child_2 : Lower_ForcedMass.Statement

  child_3 : Lower_OffsetCost.Statement

  child_4 : Lower_RationalPerturbation.Statement

  child_5 : Lower_ReferenceLotteries.Statement

end Lower_SecondCase

namespace Results_IntegerLower

def Statement : Prop :=
∀ D : DrawLaw, ∃ n m, 0 < n ∧ 0 < m ∧ m ≤ 126 ∧
  ∃ σ : Profile n m, ∀ Q : Lottery m, Stable D σ Q →
    ENNReal.ofReal (267/125 : ℝ) < distortion σ Q

structure Needs : Prop where

  child_0 : Lower_FirstCase.Statement

  child_1 : Lower_SecondCase.Statement

  child_2 : Lower_RationalPerturbation.Statement

  child_3 : Lower_FiniteElectorate.Statement

end Results_IntegerLower




namespace Computation_RealMachine

def Statement : Prop :=
(∀ prog k s t u, Runs prog k s t → Runs prog k s u → t = u) ∧
  (∀ prog k l s t u, Runs prog k s t → Halted prog t →
    Runs prog l s u → Halted prog u → t = u)

end Computation_RealMachine

namespace Computation_Preprocessing

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ σ : Profile n m,
  ∃ R : Reduction σ, ∀ d, Consistent σ d →
    sInf (Set.range fun c => sc d (R.embed c)) = optimum d

structure Needs : Prop where

  child_0 : Model_Profiles.Statement

  child_1 : Model_Metrics.Statement

end Computation_Preprocessing

namespace Computation_MWTrajectory

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ D (σ : Profile n m) δ,
  0 < δ → ∃ P : ℕ → Lottery m, Trajectory D σ δ P ∧
    ∀ t c, 0 < (P t).val c

structure Needs : Prop where

  child_0 : Model_Lotteries.Statement

  child_1 : Comparison_CandidateDraws.Statement

end Computation_MWTrajectory

namespace Computation_IterationCount

def Statement : Prop :=
∀ m : ℕ, 2 ≤ m → ∀ δ : ℝ, 0 < δ →
  let N := Nat.ceil (Real.log m/(2*δ^2));
  0 < N ∧ Real.log m/(4*δ*N)+δ/2 ≤ δ ∧ (N : ℝ) ≤ Real.log m/(2*δ^2)+1

end Computation_IterationCount

namespace Computation_ScoreScan

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ D, IsStarLaw D →
  ∀ (σ : Profile n m) P c, 0 < P.val c →
  score D σ P c = (∑ v, (PhiStar (below (σ v) P c+P.val c)-PhiStar (below (σ v) P c)))/(n*P.val c)

structure Needs : Prop where

  child_0 : Comparison_CandidateDraws.Statement

  child_1 : Numerics_StarLaw.Statement

end Computation_ScoreScan

namespace Computation_RunRules

def Statement : Prop :=
(∀ prog k l s u t, Runs prog k s u → Runs prog l u t → Runs prog (k+l) s t) ∧
(∀ (prog : Program) (Inv Done : MachineState → Prop) (rank : MachineState → ℕ) (K : ℕ),
  (∀ s, Inv s → ∃ k t, Runs prog k s t ∧ k ≤ K ∧
    (Done t ∨ (Inv t ∧ rank t < rank s))) →
  ∀ s, Inv s → ∃ k t, Runs prog k s t ∧ Done t ∧ k ≤ K*(rank s+1))

structure Needs : Prop where

end Computation_RunRules

namespace Computation_ProgramSetup

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m) ε,
  ∃ k t, Runs metricProgram k (inputState σ ε) t ∧ t.pc = 27 ∧ t.naturals 8 = 0 ∧ t.naturals 10 = 0 ∧
    ProgramBases n m t ∧ ProgramConstants ε t ∧ ProgramRanks σ t ∧
    k ≤ 32*n*m

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

end Computation_ProgramSetup

namespace Computation_ProgramInverse

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m) ε, ∀ s,
  s.pc = 27 → s.naturals 8 = 0 → s.naturals 10 = 0 → ProgramBases n m s → ProgramConstants ε s → ProgramRanks σ s →
  ∃ k t, Runs metricProgram k s t ∧ t.pc = 40 ∧
    ProgramBases n m t ∧ ProgramConstants ε t ∧ ProgramRanks σ t ∧
    ProgramInverse σ t ∧ k ≤ 32*n*m

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

end Computation_ProgramInverse

namespace Computation_ProgramPrune

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m) ε, ∀ s,
  s.pc = 40 → ProgramBases n m s → ProgramConstants ε s → ProgramRanks σ s →
  ProgramInverse σ s → ∃ k t, Runs metricProgram k s t ∧ t.pc = 63 ∧
    ProgramBases n m t ∧ ProgramConstants ε t ∧ ProgramRanks σ t ∧
    ProgramInverse σ t ∧ ProgramKeep σ t ∧ k ≤ 64*n*m^2

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

end Computation_ProgramPrune

namespace Computation_ProgramRelabel

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m) ε, ∀ s,
  s.pc = 63 → ProgramBases n m s → ProgramConstants ε s → ProgramRanks σ s →
  ProgramInverse σ s → ProgramKeep σ s →
  ∃ r k t, Runs metricProgram k s t ∧ t.pc = 76 ∧
    ProgramBases n m t ∧ ProgramConstants ε t ∧ ProgramRanks σ t ∧
    ProgramInverse σ t ∧ ProgramKeep σ t ∧ ProgramMaps σ r t ∧ k ≤ 16*m

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

  child_1 : Computation_Preprocessing.Statement

end Computation_ProgramRelabel

namespace Computation_ProgramRanking

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m) ε, ∀ r s,
  s.pc = 76 → ProgramBases n m s → ProgramConstants ε s → ProgramRanks σ s →
  ProgramInverse σ s → ProgramKeep σ s → ProgramMaps σ r s →
  ∃ R : Reduction σ, ∃ k t, Runs metricProgram k s t ∧
    R.count = r ∧ ProgramPreprocessed σ ε R t ∧ k ≤ 32*n*m

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

end Computation_ProgramRanking

namespace Computation_ProgramPreprocess

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m) ε,
  ∃ R : Reduction σ, ∃ k s,
    Runs metricProgram k (inputState σ ε) s ∧
    ProgramPreprocessed σ ε R s ∧ k ≤ 256*n*m^2

structure Needs : Prop where

  child_0 : Computation_RealMachine.Statement

  child_1 : Computation_Preprocessing.Statement

  child_2 : Computation_RunRules.Statement

  child_3 : Computation_ProgramSetup.Statement

  child_4 : Computation_ProgramInverse.Statement

  child_5 : Computation_ProgramPrune.Statement

  child_6 : Computation_ProgramRelabel.Statement

  child_7 : Computation_ProgramRanking.Statement

end Computation_ProgramPreprocess

namespace Computation_ProgramScores

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) (R : Reduction σ),
  2 ≤ R.count → ∀ ε (P : Lottery R.count) s,
  ProgramScoresInput R ε P s → ∃ k t,
    Runs metricProgram k s t ∧ t.pc = 182 ∧
    k ≤ 64*n*R.count ∧ ProgramScoresFrame R s t ∧
    (∀ c, t.memory (4*m+c.val) =
      ∑ v, (PhiStar (below (R.profile v) P c+P.val c)-PhiStar (below (R.profile v) P c))) ∧
    ∀ D, IsStarLaw D → ∀ c,
      t.memory (4*m+c.val)/(n*P.val c) = score D R.profile P c

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

  child_1 : Computation_ScoreScan.Statement

end Computation_ProgramScores

namespace Computation_ProgramCount

def Statement : Prop :=
∀ r : ℕ, 2 ≤ r → ∀ δ : ℝ, 0 < δ →
  let N := Nat.ceil (Real.log r/(2*δ^2));
  ∀ s : MachineState, s.pc = 118 → s.naturals 3 = 1 → s.naturals 17 = 0 →
    s.reals 1 = 0 → s.reals 4 = 2*δ^2 → s.reals 6 = r → s.reals 8 = 0 →
  ∃ t, Runs metricProgram (5*N+2) s t ∧ t.pc = 123 ∧
    t.naturals 17 = N ∧ t.reals 8 = 2*δ^2*N ∧
    t.naturalMemory = s.naturalMemory ∧ t.memory = s.memory ∧
    (∀ i, i ≠ 17 → t.naturals i = s.naturals i) ∧
    (∀ i, i ≠ 8 → i ≠ 9 → t.reals i = s.reals i)

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

end Computation_ProgramCount

namespace Computation_ProgramSingleton

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m) ε (R : Reduction σ) s,
  ProgramPreprocessed σ ε R s → R.count = 1 →
  ∃ k out Q, Runs metricProgram k s out ∧ Halted metricProgram out ∧
    outputState out Q ∧ AlgorithmOutput σ ε Q ∧ k = 4*m+6

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

end Computation_ProgramSingleton

namespace Computation_ProgramInitialize

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m), ∀ ε ∈ Ioc (0 : ℝ) 1,
  ∀ (R : Reduction σ) s, ProgramPreprocessed σ ε R s → 2 ≤ R.count →
  ∃ D, IsStarLaw D ∧ ∃ P : ℕ → Lottery R.count,
    Trajectory D R.profile (ε/(32*n)) P ∧ (∀ t c, 0 < (P t).val c) ∧
    ∃ k out, Runs metricProgram k s out ∧ ProgramRoundInvariant R ε P 0 out ∧
      k ≤ 16*(Nat.ceil (Real.log R.count/(2*(ε/(32*n))^2))+m+1)

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

  child_1 : Computation_ProgramCount.Statement

  child_2 : Computation_MWTrajectory.Statement

  child_3 : Numerics_StarLaw.Statement

end Computation_ProgramInitialize

namespace Computation_ProgramRound

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m) (R : Reduction σ),
  2 ≤ R.count → ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ D, IsStarLaw D →
  ∀ P : ℕ → Lottery R.count, Trajectory D R.profile (ε/(32*n)) P →
  (∀ t c, 0 < (P t).val c) → ∀ t s, ProgramRoundInvariant R ε P t s →
  t < Nat.ceil (Real.log R.count/(2*(ε/(32*n))^2)) →
  ∃ k out, Runs metricProgram k s out ∧ ProgramRoundInvariant R ε P (t+1) out ∧
    k ≤ 256*n*R.count

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

  child_1 : Computation_ProgramScores.Statement

end Computation_ProgramRound

namespace Computation_ProgramFinish

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m) (R : Reduction σ) ε D,
  IsStarLaw D → ∀ P : ℕ → Lottery R.count, Trajectory D R.profile (ε/(32*n)) P →
  let N := Nat.ceil (Real.log R.count/(2*(ε/(32*n))^2));
  0 < N → ∀ s, ProgramRoundInvariant R ε P N s →
  ∃ k out Q, Runs metricProgram k s out ∧ Halted metricProgram out ∧
    outputState out Q ∧ AlgorithmOutput σ ε Q ∧ k ≤ 16*m+16

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

end Computation_ProgramFinish

namespace Computation_ProgramMW

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ (σ : Profile n m), ∀ ε ∈ Ioc (0 : ℝ) 1,
  ∀ (R : Reduction σ) s, ProgramPreprocessed σ ε R s →
  ∃ k out Q, Runs metricProgram k s out ∧ Halted metricProgram out ∧
    outputState out Q ∧ AlgorithmOutput σ ε Q ∧
    k ≤ 1024*(n*m*Nat.ceil (Real.log m/(2*(ε/(32*n))^2))+m+1)

structure Needs : Prop where

  child_0 : Computation_RunRules.Statement

  child_1 : Computation_ProgramScores.Statement

  child_2 : Computation_MWTrajectory.Statement

  child_3 : Computation_IterationCount.Statement

  child_4 : Numerics_StarLaw.Statement

  child_5 : Computation_ProgramCount.Statement

  child_6 : Computation_ProgramSingleton.Statement

  child_7 : Computation_ProgramInitialize.Statement

  child_8 : Computation_ProgramRound.Statement

  child_9 : Computation_ProgramFinish.Statement

end Computation_ProgramMW

namespace Computation_Program

def Statement : Prop :=
∃ prog : Program, ImplementsAlgorithm prog ∧ LoopCost prog

structure Needs : Prop where

  child_0 : Computation_RealMachine.Statement

  child_1 : Computation_Preprocessing.Statement

  child_2 : Computation_MWTrajectory.Statement

  child_3 : Computation_IterationCount.Statement

  child_4 : Computation_ScoreScan.Statement

  child_5 : Computation_RunRules.Statement

  child_6 : Computation_ProgramPreprocess.Statement

  child_7 : Computation_ProgramMW.Statement

end Computation_Program

namespace Shared_ExponentialWeights

def Statement : Prop :=
∀ m, 0 < m → ∀ g : ℕ → Fin m → ℝ,
  (∀ t c, g t c ∈ Icc (0 : ℝ) 1) → ∀ η : ℝ, 0 < η → ∀ N : ℕ, 0 < N → ∀ c,
    (∑ t ∈ Finset.range N, g t c)/N ≤
    (∑ t ∈ Finset.range N, ∑ b, mwProbability g η t b*g t b)/N +
      Real.log m/(η*N)+η/8

end Shared_ExponentialWeights

namespace Comparison_ScoreBounds

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ D (σ : Profile n m) P,
  (∀ c, score D σ P c ∈ Icc (0 : ℝ) 1) ∧ mu D ∈ Ioc (0 : ℝ) (1/2)

structure Needs : Prop where

  child_0 : Comparison_CandidateDraws.Statement

  child_1 : Analysis_GeneratingFunction.Statement

  child_2 : Model_DrawLaws.Statement

end Comparison_ScoreBounds

namespace Computation_MWGuarantee

def Statement : Prop :=
∀ n m, 0 < n → 2 ≤ m → ∀ D (σ : Profile n m) δ P,
  0 < δ → Trajectory D σ δ P →
  ∀ Q, AverageLottery P (Nat.ceil (Real.log m/(2*δ^2))) Q → ApproxStable D σ Q δ

structure Needs : Prop where

  child_0 : Shared_ExponentialWeights.Statement

  child_1 : Computation_MWTrajectory.Statement

  child_2 : Computation_IterationCount.Statement

  child_3 : Comparison_SelfPlay.Statement

  child_4 : Comparison_CandidateDraws.Statement

  child_5 : Comparison_ScoreBounds.Statement

end Computation_MWGuarantee

namespace Computation_DiameterBound

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) d,
  Consistent σ d → ∀ o, Optimal d o → (∀ c, ¬ Dominated σ c) →
  ∀ c, distance d (.inr o) (.inr c) ≤ 2*n*sc d o

structure Needs : Prop where

  child_0 : Computation_Preprocessing.Statement

  child_1 : Model_Metrics.Statement

end Computation_DiameterBound

namespace Computation_ScoreErrorDistortion

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ D, IsStarLaw D →
  ∀ (σ : Profile n m), (∀ c, ¬ Dominated σ c) → ∀ Q δ, 0 ≤ δ → ApproxStable D σ Q δ →
    distortion σ Q ≤ ENNReal.ofReal (213609/100000+32*n*δ)

structure Needs : Prop where

  child_0 : Geometry_RankCutCriterion.Statement

  child_1 : Numerics_CompleteWitness.Statement

  child_2 : Computation_DiameterBound.Statement

  child_3 : Geometry_AverageAndDistortion.Statement

end Computation_ScoreErrorDistortion

namespace Computation_RestrictionLift

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) (R : Reduction σ),
  (∀ c, ¬ Dominated R.profile c) ∧
  ∀ d, Consistent σ d → ∃ d' : Metric n R.count, Consistent R.profile d' ∧
    (∀ c, sc d' c = sc d (R.embed c)) ∧ optimum d' = optimum d ∧
    ∀ P Q, Lifts R P Q → expectedCost d' P = expectedCost d Q

structure Needs : Prop where

  child_0 : Computation_Preprocessing.Statement

  child_1 : Model_Metrics.Statement

end Computation_RestrictionLift

namespace Computation_ProgramCorrectness

def Statement : Prop :=
∀ prog : Program, ImplementsAlgorithm prog → CorrectOutput prog

structure Needs : Prop where

  child_0 : Computation_Program.Statement

  child_1 : Computation_MWGuarantee.Statement

  child_2 : Computation_ScoreErrorDistortion.Statement

  child_3 : Computation_Preprocessing.Statement

  child_4 : Computation_RestrictionLift.Statement

  child_5 : Computation_RealMachine.Statement

end Computation_ProgramCorrectness

namespace Computation_ProgramCost

def Statement : Prop :=
∀ prog : Program, ImplementsAlgorithm prog →
  LoopCost prog → CorrectOutput prog → RuntimeSpec prog

structure Needs : Prop where

  child_0 : Computation_Program.Statement

  child_1 : Computation_ProgramCorrectness.Statement

  child_2 : Computation_ScoreScan.Statement

  child_3 : Computation_IterationCount.Statement

end Computation_ProgramCost

namespace Computation_Approximation

def Statement : Prop :=
∃ prog : Program, RuntimeSpec prog

structure Needs : Prop where

  child_0 : Computation_Program.Statement

  child_1 : Computation_ProgramCorrectness.Statement

  child_2 : Computation_ProgramCost.Statement

end Computation_Approximation

namespace Appendix_MixingCounterexample

def Statement : Prop :=
∃ σ : Profile 5 2, ∃ P1 P2 P : Lottery 2,
  ((Finset.univ.filter fun v => prefers (σ v) 0 1).card = 3) ∧
  (P1.val 0 = 1 ∧ P1.val 1 = 0) ∧ (P2.val 0 = 4/5 ∧ P2.val 1 = 1/5) ∧
  (∀ c, P.val c = (P1.val c+P2.val c)/2) ∧
  Stable (PMF.pure 0) σ P1 ∧ Stable (PMF.pure 1) σ P2 ∧
  avg (fun v => fixedCompare (σ v) P 0 1) = 51/100 ∧
  avg (fun v => fixedCompare (σ v) P 0 2) = 33/100 ∧
  (1/2 : ℝ)*avg (fun v => fixedCompare (σ v) P 0 1) +
  (1/2 : ℝ)*avg (fun v => fixedCompare (σ v) P 0 2) > 5/12

structure Needs : Prop where

  child_0 : Comparison_CandidateDraws.Statement

  child_1 : Model_Lotteries.Statement

end Appendix_MixingCounterexample

namespace Examples_TwoCandidateGap

def Statement : Prop :=
∃ σ : Profile 2 2,
  prefers (σ 0) 0 1 ∧ prefers (σ 1) 1 0 ∧
  (∃ dA dB : Metric 2 2, Consistent σ dA ∧ Consistent σ dB ∧
    sc dA 0 = 1 ∧ sc dA 1 = 3 ∧ sc dB 0 = 3 ∧ sc dB 1 = 1) ∧
  ∀ P : Lottery 2, distortion σ P =
    ENNReal.ofReal (max (3-2*P.val 0) (1+2*P.val 0))

structure Needs : Prop where

  child_0 : Model_Metrics.Statement

  child_1 : Model_Lotteries.Statement

  child_2 : Model_DistortionConventions.Statement

end Examples_TwoCandidateGap



namespace Results_PolynomialCorollary

def Statement : Prop :=
∃ prog : Program, ∃ K : ℝ, 0 < K ∧
  ∀ n m, 0 < n → 2 ≤ m → ∀ σ : Profile n m, ∃ Q k out,
    Runs prog k (inputState σ (1/100000)) out ∧ Halted prog out ∧ outputState out Q ∧
    distortion σ Q ≤ ENNReal.ofReal (21361/10000 : ℝ) ∧
    (k : ℝ) ≤ K*(n*m^2+n^3*m*Real.log m)

structure Needs : Prop where

  child_0 : Computation_Approximation.Statement

end Results_PolynomialCorollary

namespace Certificate

def Statement : Prop :=
(∃ R : VotingRule, ∀ n m hn hm σ,
  distortion σ (R n m hn hm σ) ≤ ENNReal.ofReal (213609/100000 : ℝ)) ∧
  (∀ D : DrawLaw, ∃ n m, 0 < n ∧ 0 < m ∧ m ≤ 126 ∧ ∃ σ : Profile n m,
    ∀ Q, Stable D σ Q → ENNReal.ofReal (267/125 : ℝ) < distortion σ Q) ∧
  (∃ prog : Program, RuntimeSpec prog)

structure Needs : Prop where

  child_0 : Results_MainUpper.Statement

  child_1 : Results_IntegerLower.Statement

  child_2 : Stability_Existence.Statement

  child_3 : Comparison_CandidateDraws.Statement

  child_4 : Geometry_RankStability.Statement

  child_5 : Geometry_MetricRankCuts.Statement

  child_6 : Geometry_Rearrangement.Statement

  child_7 : Geometry_RankCutCriterion.Statement

  child_8 : Offsets_ReductionToOffsets.Statement

  child_9 : Offsets_MetricRealization.Statement

  child_10 : Computation_Approximation.Statement

  child_11 : Appendix_MixingCounterexample.Statement

  child_12 : Results_PolynomialCorollary.Statement

  child_13 : Results_PolynomialCorollary.Statement

  child_14 : Examples_TwoCandidateGap.Statement

  child_15 : Comparison_MaximalLottery.Statement

end Certificate

end MetricDistortion.Contracts
