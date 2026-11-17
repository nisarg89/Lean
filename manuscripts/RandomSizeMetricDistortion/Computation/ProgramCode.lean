import RandomSizeMetricDistortion.Definitions

set_option maxRecDepth 10000

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion

def metricProgram : Program := [
  .natConst 2 0,
  .natConst 3 1,
  .rat 1 (0 : ℚ),
  .rat 2 (1 : ℚ),
  .rat 36 (32 : ℚ),
  .rat 37 (2 : ℚ),
  .rat 38 (4 : ℚ),
  .rat 20 (19/146 : ℚ),
  .rat 21 (35/438 : ℚ),
  .rat 22 (1/66 : ℚ),
  .natConst 4 0,
  .natConst 8 0,
  .leNat 0 8 16 13,
  .natAdd 4 4 1,
  .natAdd 8 8 3,
  .jump 12,
  .natAdd 20 4 2,
  .natAdd 21 4 4,
  .natAdd 22 21 1,
  .natAdd 23 22 1,
  .natAdd 24 23 1,
  .natAdd 26 1 2,
  .natAdd 27 26 1,
  .natAdd 28 27 1,
  .natAdd 29 28 1,
  .natConst 8 0,
  .natConst 10 0,
  .leNat 0 8 40 28,
  .natConst 6 0,
  .leNat 1 6 37 30,
  .natAdd 11 10 6,
  .loadNat 13 11,
  .natAdd 11 20 10,
  .natAdd 11 11 13,
  .storeNat 11 6,
  .natAdd 6 6 3,
  .jump 29,
  .natAdd 10 10 1,
  .natAdd 8 8 3,
  .jump 27,
  .natConst 6 0,
  .leNat 1 6 63 42,
  .natConst 19 1,
  .natConst 7 0,
  .leNat 1 7 59 45,
  .natConst 8 0,
  .natConst 10 0,
  .leNat 0 8 58 48,
  .natAdd 11 10 6,
  .loadNat 13 11,
  .natAdd 11 10 7,
  .loadNat 14 11,
  .leNat 14 13 56 53,
  .natAdd 10 10 1,
  .natAdd 8 8 3,
  .jump 47,
  .natAdd 7 7 3,
  .jump 44,
  .natConst 19 0,
  .natAdd 11 21 6,
  .storeNat 11 19,
  .natAdd 6 6 3,
  .jump 41,
  .natConst 5 0,
  .natConst 6 0,
  .leNat 1 6 76 66,
  .natAdd 11 21 6,
  .loadNat 19 11,
  .leNat 19 2 74 69,
  .natAdd 11 22 5,
  .storeNat 11 6,
  .natAdd 11 23 6,
  .storeNat 11 5,
  .natAdd 5 5 3,
  .natAdd 6 6 3,
  .jump 65,
  .natConst 8 0,
  .natConst 10 0,
  .natAdd 25 24 2,
  .leNat 0 8 100 80,
  .natConst 9 0,
  .natConst 16 0,
  .leNat 1 9 96 83,
  .natAdd 11 20 10,
  .natAdd 11 11 9,
  .loadNat 12 11,
  .natAdd 11 21 12,
  .loadNat 19 11,
  .leNat 19 2 94 89,
  .natAdd 11 23 12,
  .loadNat 15 11,
  .natAdd 11 25 16,
  .storeNat 11 15,
  .natAdd 16 16 3,
  .natAdd 9 9 3,
  .jump 82,
  .natAdd 10 10 1,
  .natAdd 25 25 5,
  .natAdd 8 8 3,
  .jump 79,
  .leNat 5 3 101 109,
  .natConst 6 0,
  .leNat 1 6 106 103,
  .store 6 1,
  .natAdd 6 6 3,
  .jump 102,
  .loadNat 12 22,
  .store 12 2,
  .jump 226,
  .castNat 7 0,
  .real .mul 10 36 7,
  .real .div 3 0 10,
  .real .mul 33 3 3,
  .real .mul 4 37 33,
  .real .mul 5 38 3,
  .castNat 6 5,
  .natConst 17 0,
  .real .add 8 1 1,
  .real .exp 9 8 1,
  .leReal 6 9 123 120,
  .natAdd 17 17 3,
  .real .add 8 8 4,
  .jump 118,
  .real .div 35 2 6,
  .natConst 15 0,
  .leNat 5 15 132 126,
  .natAdd 11 26 15,
  .store 11 35,
  .natAdd 11 28 15,
  .store 11 1,
  .natAdd 15 15 3,
  .jump 125,
  .natConst 18 0,
  .leNat 17 18 210 134,
  .natConst 15 0,
  .leNat 5 15 146 136,
  .natAdd 11 26 15,
  .load 13 11,
  .natAdd 11 28 15,
  .load 34 11,
  .real .add 34 34 13,
  .store 11 34,
  .natAdd 11 29 15,
  .store 11 1,
  .natAdd 15 15 3,
  .jump 135,
  .natConst 8 0,
  .natAdd 25 24 2,
  .leNat 0 8 182 149,
  .real .add 11 1 1,
  .real .add 12 1 1,
  .natConst 9 0,
  .leNat 5 9 179 153,
  .natAdd 11 25 9,
  .loadNat 15 11,
  .natAdd 11 26 15,
  .load 13 11,
  .real .add 14 11 13,
  .real .mul 23 14 14,
  .real .mul 24 23 14,
  .real .mul 25 23 23,
  .real .mul 26 25 25,
  .real .mul 27 26 26,
  .real .mul 28 27 27,
  .real .mul 29 28 14,
  .real .mul 30 20 23,
  .real .mul 31 21 24,
  .real .mul 32 22 29,
  .real .add 33 30 31,
  .real .add 15 33 32,
  .natAdd 11 29 15,
  .load 16 11,
  .real .sub 33 15 12,
  .real .add 16 16 33,
  .store 11 16,
  .real .add 11 14 1,
  .real .add 12 15 1,
  .natAdd 9 9 3,
  .jump 152,
  .natAdd 25 25 5,
  .natAdd 8 8 3,
  .jump 148,
  .real .add 10 1 1,
  .natConst 15 0,
  .leNat 5 15 199 185,
  .natAdd 11 26 15,
  .load 13 11,
  .natAdd 11 29 15,
  .load 16 11,
  .real .mul 33 7 13,
  .real .div 17 16 33,
  .real .mul 33 5 17,
  .real .exp 9 33 1,
  .real .mul 18 13 9,
  .natAdd 11 27 15,
  .store 11 18,
  .real .add 10 10 18,
  .natAdd 15 15 3,
  .jump 184,
  .natConst 15 0,
  .leNat 5 15 208 201,
  .natAdd 11 27 15,
  .load 18 11,
  .real .div 13 18 10,
  .natAdd 11 26 15,
  .store 11 13,
  .natAdd 15 15 3,
  .jump 200,
  .natAdd 18 18 3,
  .jump 133,
  .castNat 19 17,
  .natConst 6 0,
  .leNat 1 6 216 213,
  .store 6 1,
  .natAdd 6 6 3,
  .jump 212,
  .natConst 15 0,
  .leNat 5 15 226 218,
  .natAdd 11 28 15,
  .load 34 11,
  .real .div 18 34 19,
  .natAdd 11 22 15,
  .loadNat 12 11,
  .store 12 18,
  .natAdd 15 15 3,
  .jump 217,
  .halt
]

def ProgramLayout (n m r : ℕ) (s : MachineState) : Prop :=
  s.naturals 0 = n ∧ s.naturals 1 = m ∧ s.naturals 2 = 0 ∧ s.naturals 3 = 1 ∧
  s.naturals 4 = n*m ∧ s.naturals 5 = r ∧
  s.naturals 20 = n*m ∧ s.naturals 21 = 2*n*m ∧
  s.naturals 22 = 2*n*m+m ∧ s.naturals 23 = 2*n*m+2*m ∧
  s.naturals 24 = 2*n*m+3*m ∧
  s.naturals 26 = m ∧ s.naturals 27 = 2*m ∧
  s.naturals 28 = 3*m ∧ s.naturals 29 = 4*m

def ProgramConstants (ε : ℝ) (s : MachineState) : Prop :=
  s.reals 0 = ε ∧ s.reals 1 = 0 ∧ s.reals 2 = 1 ∧
  s.reals 20 = 19/146 ∧ s.reals 21 = 35/438 ∧ s.reals 22 = 1/66 ∧
  s.reals 36 = 32 ∧ s.reals 37 = 2 ∧ s.reals 38 = 4

def ProgramReductionMemory {n m : ℕ} {σ : Profile n m}
    (R : Reduction σ) (s : MachineState) : Prop :=
  (∀ c : Fin m, s.naturalMemory (2*n*m+c.val) = if Dominated σ c then 0 else 1) ∧
  (∀ j : Fin R.count, s.naturalMemory (2*n*m+m+j.val) = (R.embed j).val) ∧
  (∀ j : Fin R.count, s.naturalMemory (2*n*m+2*m+(R.embed j).val) = j.val) ∧
  (∀ v : Fin n, ∀ i : Fin R.count,
    s.naturalMemory (2*n*m+3*m+v.val*R.count+i.val) = ((R.profile v).symm i).val)

def ProgramPreprocessed {n m : ℕ} (σ : Profile n m) (ε : ℝ)
    (R : Reduction σ) (s : MachineState) : Prop :=
  s.pc = 100 ∧ R.count ≤ m ∧ ProgramLayout n m R.count s ∧
  ProgramConstants ε s ∧ ProgramReductionMemory R s

def ProgramScoresInput {n m : ℕ} {σ : Profile n m}
    (R : Reduction σ) (ε : ℝ) (P : Lottery R.count) (s : MachineState) : Prop :=
  s.pc = 146 ∧ ProgramLayout n m R.count s ∧ ProgramConstants ε s ∧
  ProgramReductionMemory R s ∧
  (∀ c, 0 < P.val c) ∧
  (∀ c, s.memory (m+c.val) = P.val c) ∧
  (∀ c : Fin R.count, s.memory (4*m+c.val) = 0)

def ProgramScoresFrame {n m : ℕ} {σ : Profile n m}
    (R : Reduction σ) (s t : MachineState) : Prop :=
  t.naturalMemory = s.naturalMemory ∧
  (∀ i, i ∉ ({8,9,11,15,25} : Finset ℕ) → t.naturals i = s.naturals i) ∧
  (∀ i, i ∉ ({11,12,13,14,15,16,23,24,25,26,27,28,29,30,31,32,33} : Finset ℕ) →
    t.reals i = s.reals i) ∧
  (∀ a, a < 4*m ∨ 4*m+R.count ≤ a → t.memory a = s.memory a)

def ProgramRoundInvariant {n m : ℕ} {σ : Profile n m}
    (R : Reduction σ) (ε : ℝ) (P : ℕ → Lottery R.count) (t : ℕ)
    (s : MachineState) : Prop :=
  s.pc = 133 ∧ ProgramLayout n m R.count s ∧ ProgramConstants ε s ∧
  ProgramReductionMemory R s ∧
  s.naturals 17 = Nat.ceil (Real.log R.count/(2*(ε/(32*n))^2)) ∧
  s.naturals 18 = t ∧ t ≤ s.naturals 17 ∧
  s.reals 3 = ε/(32*n) ∧ s.reals 4 = 2*(ε/(32*n))^2 ∧
  s.reals 5 = 4*(ε/(32*n)) ∧ s.reals 6 = R.count ∧ s.reals 7 = n ∧
  (∀ c, s.memory (m+c.val) = (P t).val c) ∧
  (∀ c, s.memory (3*m+c.val) = ∑ u ∈ Finset.range t, (P u).val c)

theorem metricProgram_length : metricProgram.length = 227 := by decide
#print axioms metricProgram_length
end MetricDistortion
