import Voting.Distortion.Basic


/-! Definitions interpreting the metric-distortion-v4 certificate.
Natural draw index k represents k+1 independent labeled draws.
Distances are pseudometrics; infinite-support draw laws are allowed.
-/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable

namespace MetricDistortion

def phiStar (t : ℝ) : ℝ := (19/73 : ℝ)*t + (35/146 : ℝ)*t^2 + t^32/2
def PhiStar (t : ℝ) : ℝ := (19/146 : ℝ)*t^2 + (35/438 : ℝ)*t^3 + t^33/66
def muStar : ℝ := 1085/4818
def bStar : ℝ := 2840189/5000000
def cStar : ℝ := 113609/200000
def IsStarLaw (D : DrawLaw) : Prop :=
  ∀ k, D k = ENNReal.ofReal (if k = 0 then (19/73 : ℝ) else
    if k = 1 then (35/146 : ℝ) else if k = 31 then (1/2 : ℝ) else 0)
def lowerGap (k : ℕ) : ℝ :=
  ((71/125 : ℝ)-1/52)*(3/4 : ℝ)^k + (1/52 : ℝ)^(k+1) -
    (7/26 : ℝ)^(k+1) - ((71/125 : ℝ)-7/26)*(k+1)*(71/125 : ℝ)^k

/- Exact rational polynomial certificate vocabulary. These are ordinary Lean
data, never a claim that a Python/Arb computation is trusted. -/
structure QInterval where
  lo : ℚ
  hi : ℚ
abbrev Box := Fin 4 → QInterval
inductive PolyExpr where
  | const : ℚ → PolyExpr
  | var : Fin 4 → PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | neg : PolyExpr → PolyExpr
deriving Inhabited
def eval : PolyExpr → (Fin 4 → ℝ) → ℝ
  | .const q, _ => q
  | .var i, x => x i
  | .add a b, x => eval a x + eval b x
  | .mul a b, x => eval a x * eval b x
  | .neg a, x => -eval a x
def inBox (B : Box) (x : Fin 4 → ℝ) : Prop := ∀ i, x i ∈ Icc ((B i).lo : ℝ) ((B i).hi : ℝ)
def ValidBox (B : Box) : Prop := ∀ i, (B i).lo ≤ (B i).hi
inductive BoundTree where
  | direct : BoundTree
  | centered : BoundTree
  | face : Fin 4 → Bool → BoundTree → BoundTree
  | split : Fin 4 → ℚ → BoundTree → BoundTree → BoundTree
deriving Inhabited
structure PolynomialTask where
  expression : PolyExpr
  box : Box
def TaskHolds (T : PolynomialTask) : Prop := ∀ x, inBox T.box x → eval T.expression x ≤ 0
def intervalAdd (a b : QInterval) : QInterval := ⟨a.lo+b.lo,a.hi+b.hi⟩
def intervalNeg (a : QInterval) : QInterval := ⟨-a.hi,-a.lo⟩
def intervalMul (a b : QInterval) : QInterval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
def intervalEval : PolyExpr → Box → QInterval
  | .const q, _ => ⟨q,q⟩
  | .var i, B => B i
  | .add a b, B => intervalAdd (intervalEval a B) (intervalEval b B)
  | .mul a b, B => intervalMul (intervalEval a B) (intervalEval b B)
  | .neg a, B => intervalNeg (intervalEval a B)
def derivative (i : Fin 4) : PolyExpr → PolyExpr
  | .const _ => .const 0
  | .var j => .const (if i=j then 1 else 0)
  | .add a b => .add (derivative i a) (derivative i b)
  | .mul a b => .add (.mul (derivative i a) b) (.mul a (derivative i b))
  | .neg a => .neg (derivative i a)
def qEval : PolyExpr → (Fin 4 → ℚ) → ℚ
  | .const q, _ => q
  | .var i, x => x i
  | .add a b, x => qEval a x + qEval b x
  | .mul a b, x => qEval a x * qEval b x
  | .neg a, x => -qEval a x
def centeredBound (e : PolyExpr) (B : Box) : ℚ :=
  qEval e (fun i => ((B i).lo+(B i).hi)/2) +
    ∑ i, max |(intervalEval (derivative i e) B).lo| |(intervalEval (derivative i e) B).hi| *
      ((B i).hi-(B i).lo)/2
def faceBox (B : Box) (i : Fin 4) (upper : Bool) : Box :=
  Function.update B i (let q := if upper then (B i).hi else (B i).lo; ⟨q,q⟩)
def splitBox (B : Box) (i : Fin 4) (q : ℚ) (right : Bool) : Box :=
  Function.update B i (if right then ⟨q,(B i).hi⟩ else ⟨(B i).lo,q⟩)
def verifyTree (e : PolyExpr) (B : Box) : BoundTree → Bool
  | .direct => decide ((intervalEval e B).hi ≤ 0)
  | .centered => decide (centeredBound e B ≤ 0)
  | .face i upper child =>
    (if upper then decide (0 ≤ (intervalEval (derivative i e) B).lo)
      else decide ((intervalEval (derivative i e) B).hi ≤ 0)) &&
        verifyTree e (faceBox B i upper) child
  | .split i q left right =>
    decide ((B i).lo ≤ q ∧ q ≤ (B i).hi) &&
      verifyTree e (splitBox B i q false) left && verifyTree e (splitBox B i q true) right

/- A register machine with separate natural and real registers. Arithmetic,
exp, comparison, memory and control steps have explicit unit costs. No log,
oracle, host-language function or uncharged semantic operation is an opcode. -/
inductive RealOp where
  | add | sub | mul | div | exp
deriving DecidableEq
inductive Instr where
  | rat : ℕ → ℚ → Instr
  | real : RealOp → ℕ → ℕ → ℕ → Instr
  | natConst : ℕ → ℕ → Instr
  | natAdd : ℕ → ℕ → ℕ → Instr
  | natSub : ℕ → ℕ → ℕ → Instr
  | castNat : ℕ → ℕ → Instr
  | load : ℕ → ℕ → Instr
  | store : ℕ → ℕ → Instr
  | loadNat : ℕ → ℕ → Instr
  | storeNat : ℕ → ℕ → Instr
  | jump : ℕ → Instr
  | leReal : ℕ → ℕ → ℕ → ℕ → Instr
  | leNat : ℕ → ℕ → ℕ → ℕ → Instr
  | halt : Instr
structure MachineState where
  pc : ℕ
  naturals : ℕ → ℕ
  reals : ℕ → ℝ
  memory : ℕ → ℝ
  naturalMemory : ℕ → ℕ
abbrev Program := List Instr
def applyRealOp (op : RealOp) (x y : ℝ) : ℝ :=
  match op with
  | .add => x+y | .sub => x-y | .mul => x*y | .div => x/y | .exp => Real.exp x
def step (P : Program) (s : MachineState) : Option MachineState :=
  match P[s.pc]? with
  | none => none
  | some .halt => none
  | some (.rat d q) => some {s with pc := s.pc+1, reals := Function.update s.reals d q}
  | some (.real op d a b) => some {s with pc := s.pc+1, reals := Function.update s.reals d (applyRealOp op (s.reals a) (s.reals b))}
  | some (.natConst d q) => some {s with pc := s.pc+1, naturals := Function.update s.naturals d q}
  | some (.natAdd d a b) => some {s with pc := s.pc+1, naturals := Function.update s.naturals d (s.naturals a+s.naturals b)}
  | some (.natSub d a b) => some {s with pc := s.pc+1, naturals := Function.update s.naturals d (s.naturals a-s.naturals b)}
  | some (.castNat d a) => some {s with pc := s.pc+1, reals := Function.update s.reals d (s.naturals a)}
  | some (.load d a) => some {s with pc := s.pc+1, reals := Function.update s.reals d (s.memory (s.naturals a))}
  | some (.store a b) => some {s with pc := s.pc+1, memory := Function.update s.memory (s.naturals a) (s.reals b)}
  | some (.loadNat d a) => some {s with pc := s.pc+1, naturals := Function.update s.naturals d (s.naturalMemory (s.naturals a))}
  | some (.storeNat a b) => some {s with pc := s.pc+1, naturalMemory := Function.update s.naturalMemory (s.naturals a) (s.naturals b)}
  | some (.jump q) => some {s with pc := q}
  | some (.leReal a b t f) => some {s with pc := if s.reals a ≤ s.reals b then t else f}
  | some (.leNat a b t f) => some {s with pc := if s.naturals a ≤ s.naturals b then t else f}
inductive Runs (P : Program) : ℕ → MachineState → MachineState → Prop where
  | zero (s) : Runs P 0 s s
  | succ {k s u t} : step P s = some u → Runs P k u t → Runs P (k+1) s t
def Halted (P : Program) (s : MachineState) : Prop := P[s.pc]? = some .halt
def inputState {n m : ℕ} (σ : Profile n m) (ε : ℝ) : MachineState :=
  {pc := 0, naturals := fun i => if i = 0 then n else if i = 1 then m else 0,
   reals := fun i => if i = 0 then ε else 0,
   naturalMemory := fun i => if hm : 0 < m then if hn : i/m < n then
     (σ ⟨i/m, hn⟩ ⟨i%m, Nat.mod_lt _ hm⟩).val else 0 else 0,
   memory := fun i => if hm : 0 < m then if hn : i/m < n then
     ((σ ⟨i/m, hn⟩ ⟨i%m, Nat.mod_lt _ hm⟩).val : ℝ) else 0 else 0}
def outputState {m : ℕ} (s : MachineState) (Q : Lottery m) : Prop := ∀ c, s.memory c.val = Q.val c
def computationBound (n m : ℕ) (ε : ℝ) : ℝ :=
  n*m^2 + n^3*m*Real.log m/ε^2

def Dominated {n m : ℕ} (σ : Profile n m) (c : Fin m) : Prop :=
  ∃ b, ∀ v, prefers (σ v) b c
structure Reduction {n m : ℕ} (σ : Profile n m) where
  count : ℕ
  count_pos : 0 < count
  embed : Fin count ↪ Fin m
  profile : Profile n count
  preserves : ∀ v a b, prefers (profile v) a b ↔ prefers (σ v) (embed a) (embed b)
  range_eq : Set.range embed = {c | ¬ Dominated σ c}
def Lifts {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (P : Lottery R.count) (Q : Lottery m) : Prop :=
  (∀ c, Q.val (R.embed c) = P.val c) ∧ (∀ c ∉ Set.range R.embed, Q.val c = 0)
def Reference {N : ℕ} (t : ℝ) (P : Lottery (N+1)) : Prop :=
  ∀ c, P.val c = if c.val = 0 then 1-t else t/N
def Symmetric {n N : ℕ} (σ : Profile n (N+1)) (k : ℕ) (z : ℝ) : Prop :=
  ∀ r : Ranking (N+1),
    ((Finset.univ.filter fun v => σ v = r).card : ℝ) / n =
      if (r 0).val = k then z/(Nat.factorial N) else
      if (r 0).val = N then (1-z)/(Nat.factorial N) else 0
def insertionOffsets (N : ℕ) (c : Fin (N+1)) : ℝ := if c.val = 0 then 0 else 1
def mwWeight {m : ℕ} (g : ℕ → Fin m → ℝ) (η : ℝ) (t : ℕ) (c : Fin m) : ℝ :=
  Real.exp (η * ∑ s ∈ Finset.range t, g s c)
def mwProbability {m : ℕ} (g : ℕ → Fin m → ℝ) (η : ℝ) (t : ℕ) (c : Fin m) : ℝ :=
  mwWeight g η t c / ∑ b, mwWeight g η t b
def Trajectory {n m : ℕ} (D : DrawLaw) (σ : Profile n m) (δ : ℝ)
    (P : ℕ → Lottery m) : Prop :=
  (∀ c, (P 0).val c = 1/(m : ℝ)) ∧
  ∀ t c, (P (t+1)).val c = (P t).val c * Real.exp (4*δ*score D σ (P t) c) /
    ∑ b, (P t).val b * Real.exp (4*δ*score D σ (P t) b)
def AverageLottery {m : ℕ} (P : ℕ → Lottery m) (N : ℕ) (Q : Lottery m) : Prop :=
  ∀ c, Q.val c = (∑ t ∈ Finset.range N, (P t).val c) / N
def RuntimeSpec (prog : Program) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ n m, 0 < n → 2 ≤ m → ∀ σ : Profile n m,
    ∀ ε ∈ Ioc (0 : ℝ) 1, ∃ Q : Lottery m, ∃ steps : ℕ, ∃ out : MachineState,
      Runs prog steps (inputState σ ε) out ∧ Halted prog out ∧ outputState out Q ∧
      distortion σ Q ≤ ENNReal.ofReal (213609/100000 + ε) ∧
      (steps : ℝ) ≤ K * computationBound n m ε
def AlgorithmOutput {n m : ℕ} (σ : Profile n m) (ε : ℝ) (Q : Lottery m) : Prop :=
  ∃ R : Reduction σ, ∃ Q' : Lottery R.count, Lifts R Q' Q ∧
    (R.count = 1 ∨ ∃ D, IsStarLaw D ∧ ∃ P : ℕ → Lottery R.count,
      Trajectory D R.profile (ε/(32*n)) P ∧
      AverageLottery P (Nat.ceil (Real.log R.count/(2*(ε/(32*n))^2))) Q')
def ImplementsAlgorithm (prog : Program) : Prop :=
  ∀ n m, 0 < n → 2 ≤ m → ∀ σ : Profile n m, ∀ ε ∈ Ioc (0 : ℝ) 1,
    ∃ k out Q, Runs prog k (inputState σ ε) out ∧ Halted prog out ∧
      outputState out Q ∧ AlgorithmOutput σ ε Q
def loopBudget (n m : ℕ) (ε : ℝ) : ℝ :=
  n*m^2 + n*m*(Nat.ceil (Real.log m/(2*(ε/(32*n))^2)) : ℕ) + 1
def LoopCost (prog : Program) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ n m, 0 < n → 2 ≤ m → ∀ σ : Profile n m,
    ∀ ε ∈ Ioc (0 : ℝ) 1, ∃ k out, Runs prog k (inputState σ ε) out ∧
      Halted prog out ∧ (k : ℝ) ≤ K*loopBudget n m ε
def CorrectOutput (prog : Program) : Prop :=
  ∀ n m, 0 < n → 2 ≤ m → ∀ σ : Profile n m, ∀ ε ∈ Ioc (0 : ℝ) 1,
    ∀ k out, Runs prog k (inputState σ ε) out → Halted prog out →
      ∃ Q, outputState out Q ∧ distortion σ Q ≤ ENNReal.ofReal (213609/100000+ε)

end MetricDistortion
