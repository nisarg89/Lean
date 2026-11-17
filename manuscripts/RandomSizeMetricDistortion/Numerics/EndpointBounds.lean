import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_EndpointBounds
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

/- The p=1 low-root polynomials are replayed separately, as in the paper's
endpoint checks. All data below are ordinary rational Lean constructors. -/
private def e0_0 : PolyExpr := .const (0 / 1 : ℚ)
private def e0_1 : PolyExpr := .const (1 / 1 : ℚ)
private def e0_2 : PolyExpr := .var 0
private def e0_3 : PolyExpr := .const (1085 / 4818 : ℚ)
private def e0_4 : PolyExpr := .const (19 / 73 : ℚ)
private def e0_5 : PolyExpr := .mul e0_4 e0_2
private def e0_6 : PolyExpr := .mul e0_2 e0_2
private def e0_7 : PolyExpr := .const (35 / 146 : ℚ)
private def e0_8 : PolyExpr := .mul e0_7 e0_6
private def e0_9 : PolyExpr := .add e0_5 e0_8
private def e0_10 : PolyExpr := .mul e0_6 e0_6
private def e0_11 : PolyExpr := .mul e0_10 e0_10
private def e0_12 : PolyExpr := .mul e0_11 e0_11
private def e0_13 : PolyExpr := .mul e0_12 e0_12
private def e0_14 : PolyExpr := .const (1 / 2 : ℚ)
private def e0_15 : PolyExpr := .mul e0_14 e0_13
private def e0_16 : PolyExpr := .add e0_9 e0_15
private def e0_17 : PolyExpr := .neg e0_16
private def e0_18 : PolyExpr := .add e0_3 e0_17
private def e0_19 : PolyExpr := .const (4818 / 3733 : ℚ)
private def e0_20 : PolyExpr := .mul e0_19 e0_18
private def e0_21 : PolyExpr := .const (145513 / 100000 : ℚ)
private def e0_22 : PolyExpr := .mul e0_21 e0_20
private def e0_23 : PolyExpr := .add e0_2 e0_22
private def e0_24 : PolyExpr := .const (113609 / 200000 : ℚ)
private def e0_25 : PolyExpr := .const (-113609 / 200000 : ℚ)
private def e0_26 : PolyExpr := .add e0_23 e0_25
private def expr0 : PolyExpr := e0_26
private def box0 : Box := ![⟨(49 / 100 : ℚ), (2840189 / 5000000 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩]
private def tree0 : BoundTree := (.split 0 (5290189 / 10000000 : ℚ) .centered (.split 0 (10970567 / 20000000 : ℚ) .centered (.split 0 (22331323 / 40000000 : ℚ) .centered (.split 0 (9010567 / 16000000 : ℚ) .centered (.split 0 (90495859 / 160000000 : ℚ) .centered .centered)))))
private theorem checked0 : verifyTree expr0 box0 tree0 = true := by decide +kernel
private theorem valid0 : ValidBox box0 := by
  intro i
  fin_cases i <;> norm_num [box0]
private theorem identity0 (r : ℝ) :
    eval expr0 ![r,0,0,0] = r+eta 0*psiStar r-cStar := by
  norm_num [expr0,e0_0,e0_1,e0_2,e0_3,e0_4,e0_5,e0_6,e0_7,e0_8,e0_9,e0_10,e0_11,e0_12,e0_13,e0_14,e0_15,e0_16,e0_17,e0_18,e0_19,e0_20,e0_21,e0_22,e0_23,e0_24,e0_25,e0_26,
    eval,eta,etas,psiStar,muStar,phiStar,cStar]
  ring
private def e1_0 : PolyExpr := .const (0 / 1 : ℚ)
private def e1_1 : PolyExpr := .const (1 / 1 : ℚ)
private def e1_2 : PolyExpr := .var 0
private def e1_3 : PolyExpr := .const (1085 / 4818 : ℚ)
private def e1_4 : PolyExpr := .const (19 / 73 : ℚ)
private def e1_5 : PolyExpr := .mul e1_4 e1_2
private def e1_6 : PolyExpr := .mul e1_2 e1_2
private def e1_7 : PolyExpr := .const (35 / 146 : ℚ)
private def e1_8 : PolyExpr := .mul e1_7 e1_6
private def e1_9 : PolyExpr := .add e1_5 e1_8
private def e1_10 : PolyExpr := .mul e1_6 e1_6
private def e1_11 : PolyExpr := .mul e1_10 e1_10
private def e1_12 : PolyExpr := .mul e1_11 e1_11
private def e1_13 : PolyExpr := .mul e1_12 e1_12
private def e1_14 : PolyExpr := .const (1 / 2 : ℚ)
private def e1_15 : PolyExpr := .mul e1_14 e1_13
private def e1_16 : PolyExpr := .add e1_9 e1_15
private def e1_17 : PolyExpr := .neg e1_16
private def e1_18 : PolyExpr := .add e1_3 e1_17
private def e1_19 : PolyExpr := .const (4818 / 3733 : ℚ)
private def e1_20 : PolyExpr := .mul e1_19 e1_18
private def e1_21 : PolyExpr := .const (150314929 / 100000000 : ℚ)
private def e1_22 : PolyExpr := .mul e1_21 e1_20
private def e1_23 : PolyExpr := .add e1_2 e1_22
private def e1_24 : PolyExpr := .const (113609 / 200000 : ℚ)
private def e1_25 : PolyExpr := .const (-113609 / 200000 : ℚ)
private def e1_26 : PolyExpr := .add e1_23 e1_25
private def expr1 : PolyExpr := e1_26
private def box1 : Box := ![⟨(21 / 50 : ℚ), (49 / 100 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩]
private def tree1 : BoundTree := (.face 0 true .direct)
private theorem checked1 : verifyTree expr1 box1 tree1 = true := by decide +kernel
private theorem valid1 : ValidBox box1 := by
  intro i
  fin_cases i <;> norm_num [box1]
private theorem identity1 (r : ℝ) :
    eval expr1 ![r,0,0,0] = r+eta 1*psiStar r-cStar := by
  norm_num [expr1,e1_0,e1_1,e1_2,e1_3,e1_4,e1_5,e1_6,e1_7,e1_8,e1_9,e1_10,e1_11,e1_12,e1_13,e1_14,e1_15,e1_16,e1_17,e1_18,e1_19,e1_20,e1_21,e1_22,e1_23,e1_24,e1_25,e1_26,
    eval,eta,etas,psiStar,muStar,phiStar,cStar]
  ring
private def e2_0 : PolyExpr := .const (0 / 1 : ℚ)
private def e2_1 : PolyExpr := .const (1 / 1 : ℚ)
private def e2_2 : PolyExpr := .var 0
private def e2_3 : PolyExpr := .const (1085 / 4818 : ℚ)
private def e2_4 : PolyExpr := .const (19 / 73 : ℚ)
private def e2_5 : PolyExpr := .mul e2_4 e2_2
private def e2_6 : PolyExpr := .mul e2_2 e2_2
private def e2_7 : PolyExpr := .const (35 / 146 : ℚ)
private def e2_8 : PolyExpr := .mul e2_7 e2_6
private def e2_9 : PolyExpr := .add e2_5 e2_8
private def e2_10 : PolyExpr := .mul e2_6 e2_6
private def e2_11 : PolyExpr := .mul e2_10 e2_10
private def e2_12 : PolyExpr := .mul e2_11 e2_11
private def e2_13 : PolyExpr := .mul e2_12 e2_12
private def e2_14 : PolyExpr := .const (1 / 2 : ℚ)
private def e2_15 : PolyExpr := .mul e2_14 e2_13
private def e2_16 : PolyExpr := .add e2_9 e2_15
private def e2_17 : PolyExpr := .neg e2_16
private def e2_18 : PolyExpr := .add e2_3 e2_17
private def e2_19 : PolyExpr := .const (4818 / 3733 : ℚ)
private def e2_20 : PolyExpr := .mul e2_19 e2_18
private def e2_21 : PolyExpr := .const (38851971 / 25000000 : ℚ)
private def e2_22 : PolyExpr := .mul e2_21 e2_20
private def e2_23 : PolyExpr := .add e2_2 e2_22
private def e2_24 : PolyExpr := .const (113609 / 200000 : ℚ)
private def e2_25 : PolyExpr := .const (-113609 / 200000 : ℚ)
private def e2_26 : PolyExpr := .add e2_23 e2_25
private def expr2 : PolyExpr := e2_26
private def box2 : Box := ![⟨(7 / 20 : ℚ), (21 / 50 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩]
private def tree2 : BoundTree := (.face 0 true .direct)
private theorem checked2 : verifyTree expr2 box2 tree2 = true := by decide +kernel
private theorem valid2 : ValidBox box2 := by
  intro i
  fin_cases i <;> norm_num [box2]
private theorem identity2 (r : ℝ) :
    eval expr2 ![r,0,0,0] = r+eta 2*psiStar r-cStar := by
  norm_num [expr2,e2_0,e2_1,e2_2,e2_3,e2_4,e2_5,e2_6,e2_7,e2_8,e2_9,e2_10,e2_11,e2_12,e2_13,e2_14,e2_15,e2_16,e2_17,e2_18,e2_19,e2_20,e2_21,e2_22,e2_23,e2_24,e2_25,e2_26,
    eval,eta,etas,psiStar,muStar,phiStar,cStar]
  ring
private def e3_0 : PolyExpr := .const (0 / 1 : ℚ)
private def e3_1 : PolyExpr := .const (1 / 1 : ℚ)
private def e3_2 : PolyExpr := .var 0
private def e3_3 : PolyExpr := .const (1085 / 4818 : ℚ)
private def e3_4 : PolyExpr := .const (19 / 73 : ℚ)
private def e3_5 : PolyExpr := .mul e3_4 e3_2
private def e3_6 : PolyExpr := .mul e3_2 e3_2
private def e3_7 : PolyExpr := .const (35 / 146 : ℚ)
private def e3_8 : PolyExpr := .mul e3_7 e3_6
private def e3_9 : PolyExpr := .add e3_5 e3_8
private def e3_10 : PolyExpr := .mul e3_6 e3_6
private def e3_11 : PolyExpr := .mul e3_10 e3_10
private def e3_12 : PolyExpr := .mul e3_11 e3_11
private def e3_13 : PolyExpr := .mul e3_12 e3_12
private def e3_14 : PolyExpr := .const (1 / 2 : ℚ)
private def e3_15 : PolyExpr := .mul e3_14 e3_13
private def e3_16 : PolyExpr := .add e3_9 e3_15
private def e3_17 : PolyExpr := .neg e3_16
private def e3_18 : PolyExpr := .add e3_3 e3_17
private def e3_19 : PolyExpr := .const (4818 / 3733 : ℚ)
private def e3_20 : PolyExpr := .mul e3_19 e3_18
private def e3_21 : PolyExpr := .const (80468689 / 50000000 : ℚ)
private def e3_22 : PolyExpr := .mul e3_21 e3_20
private def e3_23 : PolyExpr := .add e3_2 e3_22
private def e3_24 : PolyExpr := .const (113609 / 200000 : ℚ)
private def e3_25 : PolyExpr := .const (-113609 / 200000 : ℚ)
private def e3_26 : PolyExpr := .add e3_23 e3_25
private def expr3 : PolyExpr := e3_26
private def box3 : Box := ![⟨(3 / 10 : ℚ), (7 / 20 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩]
private def tree3 : BoundTree := (.face 0 true .direct)
private theorem checked3 : verifyTree expr3 box3 tree3 = true := by decide +kernel
private theorem valid3 : ValidBox box3 := by
  intro i
  fin_cases i <;> norm_num [box3]
private theorem identity3 (r : ℝ) :
    eval expr3 ![r,0,0,0] = r+eta 3*psiStar r-cStar := by
  norm_num [expr3,e3_0,e3_1,e3_2,e3_3,e3_4,e3_5,e3_6,e3_7,e3_8,e3_9,e3_10,e3_11,e3_12,e3_13,e3_14,e3_15,e3_16,e3_17,e3_18,e3_19,e3_20,e3_21,e3_22,e3_23,e3_24,e3_25,e3_26,
    eval,eta,etas,psiStar,muStar,phiStar,cStar]
  ring
private def e4_0 : PolyExpr := .const (0 / 1 : ℚ)
private def e4_1 : PolyExpr := .const (1 / 1 : ℚ)
private def e4_2 : PolyExpr := .var 0
private def e4_3 : PolyExpr := .const (1085 / 4818 : ℚ)
private def e4_4 : PolyExpr := .const (19 / 73 : ℚ)
private def e4_5 : PolyExpr := .mul e4_4 e4_2
private def e4_6 : PolyExpr := .mul e4_2 e4_2
private def e4_7 : PolyExpr := .const (35 / 146 : ℚ)
private def e4_8 : PolyExpr := .mul e4_7 e4_6
private def e4_9 : PolyExpr := .add e4_5 e4_8
private def e4_10 : PolyExpr := .mul e4_6 e4_6
private def e4_11 : PolyExpr := .mul e4_10 e4_10
private def e4_12 : PolyExpr := .mul e4_11 e4_11
private def e4_13 : PolyExpr := .mul e4_12 e4_12
private def e4_14 : PolyExpr := .const (1 / 2 : ℚ)
private def e4_15 : PolyExpr := .mul e4_14 e4_13
private def e4_16 : PolyExpr := .add e4_9 e4_15
private def e4_17 : PolyExpr := .neg e4_16
private def e4_18 : PolyExpr := .add e4_3 e4_17
private def e4_19 : PolyExpr := .const (4818 / 3733 : ℚ)
private def e4_20 : PolyExpr := .mul e4_19 e4_18
private def e4_21 : PolyExpr := .const (82505871 / 50000000 : ℚ)
private def e4_22 : PolyExpr := .mul e4_21 e4_20
private def e4_23 : PolyExpr := .add e4_2 e4_22
private def e4_24 : PolyExpr := .const (113609 / 200000 : ℚ)
private def e4_25 : PolyExpr := .const (-113609 / 200000 : ℚ)
private def e4_26 : PolyExpr := .add e4_23 e4_25
private def expr4 : PolyExpr := e4_26
private def box4 : Box := ![⟨(13 / 50 : ℚ), (3 / 10 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩]
private def tree4 : BoundTree := .centered
private theorem checked4 : verifyTree expr4 box4 tree4 = true := by decide +kernel
private theorem valid4 : ValidBox box4 := by
  intro i
  fin_cases i <;> norm_num [box4]
private theorem identity4 (r : ℝ) :
    eval expr4 ![r,0,0,0] = r+eta 4*psiStar r-cStar := by
  norm_num [expr4,e4_0,e4_1,e4_2,e4_3,e4_4,e4_5,e4_6,e4_7,e4_8,e4_9,e4_10,e4_11,e4_12,e4_13,e4_14,e4_15,e4_16,e4_17,e4_18,e4_19,e4_20,e4_21,e4_22,e4_23,e4_24,e4_25,e4_26,
    eval,eta,etas,psiStar,muStar,phiStar,cStar]
  ring
private def e5_0 : PolyExpr := .const (0 / 1 : ℚ)
private def e5_1 : PolyExpr := .const (1 / 1 : ℚ)
private def e5_2 : PolyExpr := .var 0
private def e5_3 : PolyExpr := .const (1085 / 4818 : ℚ)
private def e5_4 : PolyExpr := .const (19 / 73 : ℚ)
private def e5_5 : PolyExpr := .mul e5_4 e5_2
private def e5_6 : PolyExpr := .mul e5_2 e5_2
private def e5_7 : PolyExpr := .const (35 / 146 : ℚ)
private def e5_8 : PolyExpr := .mul e5_7 e5_6
private def e5_9 : PolyExpr := .add e5_5 e5_8
private def e5_10 : PolyExpr := .mul e5_6 e5_6
private def e5_11 : PolyExpr := .mul e5_10 e5_10
private def e5_12 : PolyExpr := .mul e5_11 e5_11
private def e5_13 : PolyExpr := .mul e5_12 e5_12
private def e5_14 : PolyExpr := .const (1 / 2 : ℚ)
private def e5_15 : PolyExpr := .mul e5_14 e5_13
private def e5_16 : PolyExpr := .add e5_9 e5_15
private def e5_17 : PolyExpr := .neg e5_16
private def e5_18 : PolyExpr := .add e5_3 e5_17
private def e5_19 : PolyExpr := .const (4818 / 3733 : ℚ)
private def e5_20 : PolyExpr := .mul e5_19 e5_18
private def e5_21 : PolyExpr := .const (84252027 / 50000000 : ℚ)
private def e5_22 : PolyExpr := .mul e5_21 e5_20
private def e5_23 : PolyExpr := .add e5_2 e5_22
private def e5_24 : PolyExpr := .const (113609 / 200000 : ℚ)
private def e5_25 : PolyExpr := .const (-113609 / 200000 : ℚ)
private def e5_26 : PolyExpr := .add e5_23 e5_25
private def expr5 : PolyExpr := e5_26
private def box5 : Box := ![⟨(21 / 100 : ℚ), (13 / 50 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩]
private def tree5 : BoundTree := (.face 0 true .direct)
private theorem checked5 : verifyTree expr5 box5 tree5 = true := by decide +kernel
private theorem valid5 : ValidBox box5 := by
  intro i
  fin_cases i <;> norm_num [box5]
private theorem identity5 (r : ℝ) :
    eval expr5 ![r,0,0,0] = r+eta 5*psiStar r-cStar := by
  norm_num [expr5,e5_0,e5_1,e5_2,e5_3,e5_4,e5_5,e5_6,e5_7,e5_8,e5_9,e5_10,e5_11,e5_12,e5_13,e5_14,e5_15,e5_16,e5_17,e5_18,e5_19,e5_20,e5_21,e5_22,e5_23,e5_24,e5_25,e5_26,
    eval,eta,etas,psiStar,muStar,phiStar,cStar]
  ring
private def e6_0 : PolyExpr := .const (0 / 1 : ℚ)
private def e6_1 : PolyExpr := .const (1 / 1 : ℚ)
private def e6_2 : PolyExpr := .var 0
private def e6_3 : PolyExpr := .const (1085 / 4818 : ℚ)
private def e6_4 : PolyExpr := .const (19 / 73 : ℚ)
private def e6_5 : PolyExpr := .mul e6_4 e6_2
private def e6_6 : PolyExpr := .mul e6_2 e6_2
private def e6_7 : PolyExpr := .const (35 / 146 : ℚ)
private def e6_8 : PolyExpr := .mul e6_7 e6_6
private def e6_9 : PolyExpr := .add e6_5 e6_8
private def e6_10 : PolyExpr := .mul e6_6 e6_6
private def e6_11 : PolyExpr := .mul e6_10 e6_10
private def e6_12 : PolyExpr := .mul e6_11 e6_11
private def e6_13 : PolyExpr := .mul e6_12 e6_12
private def e6_14 : PolyExpr := .const (1 / 2 : ℚ)
private def e6_15 : PolyExpr := .mul e6_14 e6_13
private def e6_16 : PolyExpr := .add e6_9 e6_15
private def e6_17 : PolyExpr := .neg e6_16
private def e6_18 : PolyExpr := .add e6_3 e6_17
private def e6_19 : PolyExpr := .const (4818 / 3733 : ℚ)
private def e6_20 : PolyExpr := .mul e6_19 e6_18
private def e6_21 : PolyExpr := .const (173014957 / 100000000 : ℚ)
private def e6_22 : PolyExpr := .mul e6_21 e6_20
private def e6_23 : PolyExpr := .add e6_2 e6_22
private def e6_24 : PolyExpr := .const (113609 / 200000 : ℚ)
private def e6_25 : PolyExpr := .const (-113609 / 200000 : ℚ)
private def e6_26 : PolyExpr := .add e6_23 e6_25
private def expr6 : PolyExpr := e6_26
private def box6 : Box := ![⟨(7 / 50 : ℚ), (21 / 100 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩]
private def tree6 : BoundTree := (.face 0 true .direct)
private theorem checked6 : verifyTree expr6 box6 tree6 = true := by decide +kernel
private theorem valid6 : ValidBox box6 := by
  intro i
  fin_cases i <;> norm_num [box6]
private theorem identity6 (r : ℝ) :
    eval expr6 ![r,0,0,0] = r+eta 6*psiStar r-cStar := by
  norm_num [expr6,e6_0,e6_1,e6_2,e6_3,e6_4,e6_5,e6_6,e6_7,e6_8,e6_9,e6_10,e6_11,e6_12,e6_13,e6_14,e6_15,e6_16,e6_17,e6_18,e6_19,e6_20,e6_21,e6_22,e6_23,e6_24,e6_25,e6_26,
    eval,eta,etas,psiStar,muStar,phiStar,cStar]
  ring
private def e7_0 : PolyExpr := .const (0 / 1 : ℚ)
private def e7_1 : PolyExpr := .const (1 / 1 : ℚ)
private def e7_2 : PolyExpr := .var 0
private def e7_3 : PolyExpr := .const (1085 / 4818 : ℚ)
private def e7_4 : PolyExpr := .const (19 / 73 : ℚ)
private def e7_5 : PolyExpr := .mul e7_4 e7_2
private def e7_6 : PolyExpr := .mul e7_2 e7_2
private def e7_7 : PolyExpr := .const (35 / 146 : ℚ)
private def e7_8 : PolyExpr := .mul e7_7 e7_6
private def e7_9 : PolyExpr := .add e7_5 e7_8
private def e7_10 : PolyExpr := .mul e7_6 e7_6
private def e7_11 : PolyExpr := .mul e7_10 e7_10
private def e7_12 : PolyExpr := .mul e7_11 e7_11
private def e7_13 : PolyExpr := .mul e7_12 e7_12
private def e7_14 : PolyExpr := .const (1 / 2 : ℚ)
private def e7_15 : PolyExpr := .mul e7_14 e7_13
private def e7_16 : PolyExpr := .add e7_9 e7_15
private def e7_17 : PolyExpr := .neg e7_16
private def e7_18 : PolyExpr := .add e7_3 e7_17
private def e7_19 : PolyExpr := .const (4818 / 3733 : ℚ)
private def e7_20 : PolyExpr := .mul e7_19 e7_18
private def e7_21 : PolyExpr := .const (44963517 / 25000000 : ℚ)
private def e7_22 : PolyExpr := .mul e7_21 e7_20
private def e7_23 : PolyExpr := .add e7_2 e7_22
private def e7_24 : PolyExpr := .const (113609 / 200000 : ℚ)
private def e7_25 : PolyExpr := .const (-113609 / 200000 : ℚ)
private def e7_26 : PolyExpr := .add e7_23 e7_25
private def expr7 : PolyExpr := e7_26
private def box7 : Box := ![⟨(3 / 100 : ℚ), (7 / 50 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩]
private def tree7 : BoundTree := (.face 0 true .direct)
private theorem checked7 : verifyTree expr7 box7 tree7 = true := by decide +kernel
private theorem valid7 : ValidBox box7 := by
  intro i
  fin_cases i <;> norm_num [box7]
private theorem identity7 (r : ℝ) :
    eval expr7 ![r,0,0,0] = r+eta 7*psiStar r-cStar := by
  norm_num [expr7,e7_0,e7_1,e7_2,e7_3,e7_4,e7_5,e7_6,e7_7,e7_8,e7_9,e7_10,e7_11,e7_12,e7_13,e7_14,e7_15,e7_16,e7_17,e7_18,e7_19,e7_20,e7_21,e7_22,e7_23,e7_24,e7_25,e7_26,
    eval,eta,etas,psiStar,muStar,phiStar,cStar]
  ring
private def e8_0 : PolyExpr := .const (0 / 1 : ℚ)
private def e8_1 : PolyExpr := .const (1 / 1 : ℚ)
private def e8_2 : PolyExpr := .var 0
private def e8_3 : PolyExpr := .const (1085 / 4818 : ℚ)
private def e8_4 : PolyExpr := .const (19 / 73 : ℚ)
private def e8_5 : PolyExpr := .mul e8_4 e8_2
private def e8_6 : PolyExpr := .mul e8_2 e8_2
private def e8_7 : PolyExpr := .const (35 / 146 : ℚ)
private def e8_8 : PolyExpr := .mul e8_7 e8_6
private def e8_9 : PolyExpr := .add e8_5 e8_8
private def e8_10 : PolyExpr := .mul e8_6 e8_6
private def e8_11 : PolyExpr := .mul e8_10 e8_10
private def e8_12 : PolyExpr := .mul e8_11 e8_11
private def e8_13 : PolyExpr := .mul e8_12 e8_12
private def e8_14 : PolyExpr := .const (1 / 2 : ℚ)
private def e8_15 : PolyExpr := .mul e8_14 e8_13
private def e8_16 : PolyExpr := .add e8_9 e8_15
private def e8_17 : PolyExpr := .neg e8_16
private def e8_18 : PolyExpr := .add e8_3 e8_17
private def e8_19 : PolyExpr := .const (4818 / 3733 : ℚ)
private def e8_20 : PolyExpr := .mul e8_19 e8_18
private def e8_21 : PolyExpr := .const (95893067 / 50000000 : ℚ)
private def e8_22 : PolyExpr := .mul e8_21 e8_20
private def e8_23 : PolyExpr := .add e8_2 e8_22
private def e8_24 : PolyExpr := .const (113609 / 200000 : ℚ)
private def e8_25 : PolyExpr := .const (-113609 / 200000 : ℚ)
private def e8_26 : PolyExpr := .add e8_23 e8_25
private def expr8 : PolyExpr := e8_26
private def box8 : Box := ![⟨(0 / 1 : ℚ), (3 / 100 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩, ⟨(0 / 1 : ℚ), (0 / 1 : ℚ)⟩]
private def tree8 : BoundTree := .centered
private theorem checked8 : verifyTree expr8 box8 tree8 = true := by decide +kernel
private theorem valid8 : ValidBox box8 := by
  intro i
  fin_cases i <;> norm_num [box8]
private theorem identity8 (r : ℝ) :
    eval expr8 ![r,0,0,0] = r+eta 8*psiStar r-cStar := by
  norm_num [expr8,e8_0,e8_1,e8_2,e8_3,e8_4,e8_5,e8_6,e8_7,e8_8,e8_9,e8_10,e8_11,e8_12,e8_13,e8_14,e8_15,e8_16,e8_17,e8_18,e8_19,e8_20,e8_21,e8_22,e8_23,e8_24,e8_25,e8_26,
    eval,eta,etas,psiStar,muStar,phiStar,cStar]
  ring

private theorem low_root_bound (h : Needs) (j : Fin 9) (r : ℝ) (hr : r ∈ root j) :
    r+eta j*psiStar r ≤ cStar := by
  fin_cases j
  · change r+eta (0 : Fin 9)*psiStar r ≤ cStar
    have hb : inBox box0 ![r,0,0,0] := by
      intro i
      fin_cases i
      · simpa [box0,root,rootLows,rootHighs] using hr
      · norm_num [box0]
      · norm_num [box0]
      · norm_num [box0]
    have hv := h.child_0 expr0 box0 tree0 valid0 checked0 _ hb
    rw [identity0] at hv
    linarith
  · change r+eta (1 : Fin 9)*psiStar r ≤ cStar
    have hb : inBox box1 ![r,0,0,0] := by
      intro i
      fin_cases i
      · simpa [box1,root,rootLows,rootHighs] using hr
      · norm_num [box1]
      · norm_num [box1]
      · norm_num [box1]
    have hv := h.child_0 expr1 box1 tree1 valid1 checked1 _ hb
    rw [identity1] at hv
    linarith
  · change r+eta (2 : Fin 9)*psiStar r ≤ cStar
    have hb : inBox box2 ![r,0,0,0] := by
      intro i
      fin_cases i
      · simpa [box2,root,rootLows,rootHighs] using hr
      · norm_num [box2]
      · norm_num [box2]
      · norm_num [box2]
    have hv := h.child_0 expr2 box2 tree2 valid2 checked2 _ hb
    rw [identity2] at hv
    linarith
  · change r+eta (3 : Fin 9)*psiStar r ≤ cStar
    have hb : inBox box3 ![r,0,0,0] := by
      intro i
      fin_cases i
      · simpa [box3,root,rootLows,rootHighs] using hr
      · norm_num [box3]
      · norm_num [box3]
      · norm_num [box3]
    have hv := h.child_0 expr3 box3 tree3 valid3 checked3 _ hb
    rw [identity3] at hv
    linarith
  · change r+eta (4 : Fin 9)*psiStar r ≤ cStar
    have hb : inBox box4 ![r,0,0,0] := by
      intro i
      fin_cases i
      · simpa [box4,root,rootLows,rootHighs] using hr
      · norm_num [box4]
      · norm_num [box4]
      · norm_num [box4]
    have hv := h.child_0 expr4 box4 tree4 valid4 checked4 _ hb
    rw [identity4] at hv
    linarith
  · change r+eta (5 : Fin 9)*psiStar r ≤ cStar
    have hb : inBox box5 ![r,0,0,0] := by
      intro i
      fin_cases i
      · simpa [box5,root,rootLows,rootHighs] using hr
      · norm_num [box5]
      · norm_num [box5]
      · norm_num [box5]
    have hv := h.child_0 expr5 box5 tree5 valid5 checked5 _ hb
    rw [identity5] at hv
    linarith
  · change r+eta (6 : Fin 9)*psiStar r ≤ cStar
    have hb : inBox box6 ![r,0,0,0] := by
      intro i
      fin_cases i
      · simpa [box6,root,rootLows,rootHighs] using hr
      · norm_num [box6]
      · norm_num [box6]
      · norm_num [box6]
    have hv := h.child_0 expr6 box6 tree6 valid6 checked6 _ hb
    rw [identity6] at hv
    linarith
  · change r+eta (7 : Fin 9)*psiStar r ≤ cStar
    have hb : inBox box7 ![r,0,0,0] := by
      intro i
      fin_cases i
      · simpa [box7,root,rootLows,rootHighs] using hr
      · norm_num [box7]
      · norm_num [box7]
      · norm_num [box7]
    have hv := h.child_0 expr7 box7 tree7 valid7 checked7 _ hb
    rw [identity7] at hv
    linarith
  · change r+eta (8 : Fin 9)*psiStar r ≤ cStar
    have hb : inBox box8 ![r,0,0,0] := by
      intro i
      fin_cases i
      · simpa [box8,root,rootLows,rootHighs] using hr
      · norm_num [box8]
      · norm_num [box8]
      · norm_num [box8]
    have hv := h.child_0 expr8 box8 tree8 valid8 checked8 _ hb
    rw [identity8] at hv
    linarith

private theorem high_base_bound (j : Fin 9) : bStar+eta j*psiStar bStar ≤ cStar := by
  fin_cases j <;> norm_num [bStar,eta,etas,psiStar,muStar,phiStar,cStar]

private theorem psi_antitone (a r : ℝ) (ha : 0 ≤ a) (har : a ≤ r) :
    psiStar r ≤ psiStar a := by
  have h2 := pow_le_pow_left₀ ha har 2
  have h32 := pow_le_pow_left₀ ha har 32
  unfold psiStar phiStar
  nlinarith

private theorem endpoint_scalar (h : Needs) (j : Fin 9) (r a : ℝ)
    (hr : r ∈ root j ∪ Icc bStar 1) (ha : 0 ≤ a) (har : a ≤ r) :
    a+eta j*psiStar r ≤ cStar-rankPotential j a := by
  have hs := h.child_5 j
  have heta : 0 ≤ eta j := by
    have ht := h.child_3.2.1 j 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    rw [(h.child_3.2.2.2.2 j).2] at ht
    exact ht
  by_cases hab : a ≤ bStar
  · simp only [rankPotential,hab,ite_true,sub_zero]
    rcases hr with hr | hr
    · have ht := low_root_bound h j r hr
      linarith
    · have ht := high_base_bound j
      have hp := mul_le_mul_of_nonneg_left (psi_antitone bStar r (by norm_num [bStar]) hr.1) heta
      linarith
  · have hp := mul_le_mul_of_nonneg_left (psi_antitone a r ha har) heta
    by_cases hah : a ≤ cutoff j
    · simp only [rankPotential,hab,ite_false,hah,ite_true]
      linarith [hs.2.2.2.1]
    · simp only [rankPotential,hab,ite_false,hah,sub_self]
      have ht := hs.2.2.2.2.2 a (le_of_not_ge hah)
      linarith

theorem from_children (h : Needs) : Statement := by
  intro j D hD r hr p hp a A ha hap hpA hA
  have hphi := h.child_2.2 D hD
  have ha1 : a ≤ 1 := (hap.trans (min_le_left _ _)).trans (hpA.trans hA)
  have har : a ≤ r := hap.trans (min_le_right _ _)
  have hr1 : r ≤ 1 := by
    rcases hr with hr | hr
    · exact ((h.child_7.2.1 j).2.2 hr).2.trans (by norm_num [bStar])
    · exact hr.2
  rcases hp with hp | hp
  · have hp0 : p = 0 := by simpa using hp
    subst p
    have ha0 : a = 0 := le_antisymm (hap.trans (min_le_left _ _)) ha
    subst a
    unfold LocalCut
    simp only [fixedWitness,h.child_3.2.2.1,(h.child_3.2.2.2.2 j).1,
      zero_mul,add_zero,zero_add]
    exact ENNReal.toReal_nonneg
  · have hp1 : p = 1 := by simpa using hp
    subst p
    have hA1 : A = 1 := le_antisymm hA hpA
    subst A
    have hd := h.child_6 a 1 1 r ⟨ha,hap,le_rfl,le_rfl⟩
    have hm : (nuStar j {z : ℝ | z ∈ Icc 0 1 ∧ a ≤ min z r ∧ min z r < 1}).toReal =
        cStar-rankPotential j a := by
      rw [hd]
      by_cases hrlt : r < 1
      · rw [if_pos hrlt]
        exact h.child_4.2 j a ha ha1
      · rw [if_neg hrlt,h.child_4.1 j a 1 ha ha1 le_rfl]
        have hb : ¬ (1 : ℝ) ≤ bStar := by norm_num [bStar]
        have hh : ¬ (1 : ℝ) ≤ cutoff j := not_le_of_gt (h.child_5 j).2.1
        simp [rankPotential,hb,hh]
    unfold LocalCut
    simp only [fixedWitness,h.child_3.2.2.2.1,(h.child_3.2.2.2.2 j).2,
      zero_mul,add_zero,hphi.1,hphi.2.2.1]
    rw [hm]
    exact endpoint_scalar h j r a hr ha har

#print axioms from_children
end MetricDistortion.Contracts.Numerics_EndpointBounds
