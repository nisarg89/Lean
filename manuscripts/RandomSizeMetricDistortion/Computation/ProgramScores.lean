import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace MetricDistortion.Contracts.Computation_ProgramScores

@[simp] private lemma code_146 : metricProgram[146]? = some (.natConst 8 0) := by rfl
@[simp] private lemma code_147 : metricProgram[147]? = some (.natAdd 25 24 2) := by rfl
@[simp] private lemma code_148 : metricProgram[148]? = some (.leNat 0 8 182 149) := by rfl
@[simp] private lemma code_149 : metricProgram[149]? = some (.real .add 11 1 1) := by rfl
@[simp] private lemma code_150 : metricProgram[150]? = some (.real .add 12 1 1) := by rfl
@[simp] private lemma code_151 : metricProgram[151]? = some (.natConst 9 0) := by rfl
@[simp] private lemma code_152 : metricProgram[152]? = some (.leNat 5 9 179 153) := by rfl
@[simp] private lemma code_153 : metricProgram[153]? = some (.natAdd 11 25 9) := by rfl
@[simp] private lemma code_154 : metricProgram[154]? = some (.loadNat 15 11) := by rfl
@[simp] private lemma code_155 : metricProgram[155]? = some (.natAdd 11 26 15) := by rfl
@[simp] private lemma code_156 : metricProgram[156]? = some (.load 13 11) := by rfl
@[simp] private lemma code_157 : metricProgram[157]? = some (.real .add 14 11 13) := by rfl
@[simp] private lemma code_158 : metricProgram[158]? = some (.real .mul 23 14 14) := by rfl
@[simp] private lemma code_159 : metricProgram[159]? = some (.real .mul 24 23 14) := by rfl
@[simp] private lemma code_160 : metricProgram[160]? = some (.real .mul 25 23 23) := by rfl
@[simp] private lemma code_161 : metricProgram[161]? = some (.real .mul 26 25 25) := by rfl
@[simp] private lemma code_162 : metricProgram[162]? = some (.real .mul 27 26 26) := by rfl
@[simp] private lemma code_163 : metricProgram[163]? = some (.real .mul 28 27 27) := by rfl
@[simp] private lemma code_164 : metricProgram[164]? = some (.real .mul 29 28 14) := by rfl
@[simp] private lemma code_165 : metricProgram[165]? = some (.real .mul 30 20 23) := by rfl
@[simp] private lemma code_166 : metricProgram[166]? = some (.real .mul 31 21 24) := by rfl
@[simp] private lemma code_167 : metricProgram[167]? = some (.real .mul 32 22 29) := by rfl
@[simp] private lemma code_168 : metricProgram[168]? = some (.real .add 33 30 31) := by rfl
@[simp] private lemma code_169 : metricProgram[169]? = some (.real .add 15 33 32) := by rfl
@[simp] private lemma code_170 : metricProgram[170]? = some (.natAdd 11 29 15) := by rfl
@[simp] private lemma code_171 : metricProgram[171]? = some (.load 16 11) := by rfl
@[simp] private lemma code_172 : metricProgram[172]? = some (.real .sub 33 15 12) := by rfl
@[simp] private lemma code_173 : metricProgram[173]? = some (.real .add 16 16 33) := by rfl
@[simp] private lemma code_174 : metricProgram[174]? = some (.store 11 16) := by rfl
@[simp] private lemma code_175 : metricProgram[175]? = some (.real .add 11 14 1) := by rfl
@[simp] private lemma code_176 : metricProgram[176]? = some (.real .add 12 15 1) := by rfl
@[simp] private lemma code_177 : metricProgram[177]? = some (.natAdd 9 9 3) := by rfl
@[simp] private lemma code_178 : metricProgram[178]? = some (.jump 152) := by rfl
@[simp] private lemma code_179 : metricProgram[179]? = some (.natAdd 25 25 5) := by rfl
@[simp] private lemma code_180 : metricProgram[180]? = some (.natAdd 8 8 3) := by rfl
@[simp] private lemma code_181 : metricProgram[181]? = some (.jump 148) := by rfl

private def blockRun : ℕ → MachineState → Option MachineState
  | 0, s => some s
  | k+1, s => (step metricProgram s).bind (blockRun k)

private lemma blockRun_sound {k : ℕ} {s t : MachineState} (h : blockRun k s=some t) :
    Runs metricProgram k s t := by
  induction k generalizing s with
  | zero =>
    simp only [blockRun,Option.some.injEq] at h
    subst t
    exact Runs.zero s
  | succ k ih =>
    cases hs : step metricProgram s with
    | none => simp [blockRun,hs] at h
    | some u =>
      simp only [blockRun,hs,Option.bind_some] at h
      exact Runs.succ hs (ih h)

private def scanPrefix {r : ℕ} (ρ : Ranking r) (P : Lottery r) (i : ℕ) : ℝ :=
  ∑ c, if (ρ c).val < i then P.val c else 0

private lemma prefix_zero {r : ℕ} (ρ : Ranking r) (P : Lottery r) : scanPrefix ρ P 0=0 := by
  simp [scanPrefix]

private lemma prefix_full {r : ℕ} (ρ : Ranking r) (P : Lottery r) : scanPrefix ρ P r=1 := by
  calc
    _ = ∑ c, P.val c := by
      apply Finset.sum_congr rfl
      intro c _
      exact if_pos (ρ c).isLt
    _ = 1 := P.property.2

private lemma prefix_at {r : ℕ} (ρ : Ranking r) (P : Lottery r) (i : Fin r) :
    scanPrefix ρ P i.val = below ρ P (ρ.symm i) := by
  unfold scanPrefix below mass
  apply Finset.sum_congr rfl
  intro c _
  simp only [Set.mem_ofPred_eq,prefers,Equiv.apply_symm_apply]
  rfl

private lemma prefix_step {r : ℕ} (ρ : Ranking r) (P : Lottery r) (i : ℕ) (hi : i < r) :
    scanPrefix ρ P (i+1) = scanPrefix ρ P i+P.val (ρ.symm ⟨i,hi⟩) := by
  let c := ρ.symm ⟨i,hi⟩
  have hc : (ρ c).val=i := by simp [c]
  calc
    _ = ∑ j, ((if (ρ j).val < i then P.val j else 0)+(if j=c then P.val j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j=c
      · subst j
        simp [hc]
      · have hr : (ρ j).val ≠ i := by
          intro he
          apply hj
          apply ρ.injective
          apply Fin.ext
          simpa [hc] using he
        have hequiv : (ρ j).val < i+1 ↔ (ρ j).val < i := by omega
        simp [hequiv,hj]
    _ = scanPrefix ρ P i+P.val c := by simp [scanPrefix,Finset.sum_add_distrib]

private def scoreDelta {n r : ℕ} (σ : Profile n r) (P : Lottery r) (v : Fin n) (c : Fin r) : ℝ :=
  PhiStar (below (σ v) P c+P.val c)-PhiStar (below (σ v) P c)

private lemma count_le {n m : ℕ} {σ : Profile n m} (R : Reduction σ) : R.count ≤ m := by
  simpa using Fintype.card_le_of_injective R.embed R.embed.injective

private lemma frame_trans {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    {s u t : MachineState} (hu : ProgramScoresFrame R s u) (ht : ProgramScoresFrame R u t) :
    ProgramScoresFrame R s t := by
  refine ⟨ht.1.trans hu.1,?_,?_,?_⟩
  · intro i hi
    exact (ht.2.1 i hi).trans (hu.2.1 i hi)
  · intro i hi
    exact (ht.2.2.1 i hi).trans (hu.2.2.1 i hi)
  · intro i hi
    exact (ht.2.2.2 i hi).trans (hu.2.2.2 i hi)

private lemma frame_layout {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    {s t : MachineState} (hf : ProgramScoresFrame R s t) (hl : ProgramLayout n m R.count s) :
    ProgramLayout n m R.count t := by
  rcases hl with ⟨h0,h1,h2,h3,h4,h5,h20,h21,h22,h23,h24,h26,h27,h28,h29⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hf.2.1 0 (by decide)] using h0
  · simpa only [hf.2.1 1 (by decide)] using h1
  · simpa only [hf.2.1 2 (by decide)] using h2
  · simpa only [hf.2.1 3 (by decide)] using h3
  · simpa only [hf.2.1 4 (by decide)] using h4
  · simpa only [hf.2.1 5 (by decide)] using h5
  · simpa only [hf.2.1 20 (by decide)] using h20
  · simpa only [hf.2.1 21 (by decide)] using h21
  · simpa only [hf.2.1 22 (by decide)] using h22
  · simpa only [hf.2.1 23 (by decide)] using h23
  · simpa only [hf.2.1 24 (by decide)] using h24
  · simpa only [hf.2.1 26 (by decide)] using h26
  · simpa only [hf.2.1 27 (by decide)] using h27
  · simpa only [hf.2.1 28 (by decide)] using h28
  · simpa only [hf.2.1 29 (by decide)] using h29

private lemma frame_constants {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    {s t : MachineState} (hf : ProgramScoresFrame R s t) {ε : ℝ} (hc : ProgramConstants ε s) :
    ProgramConstants ε t := by
  rcases hc with ⟨h0,h1,h2,h20,h21,h22,h36,h37,h38⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hf.2.2.1 0 (by decide)] using h0
  · simpa only [hf.2.2.1 1 (by decide)] using h1
  · simpa only [hf.2.2.1 2 (by decide)] using h2
  · simpa only [hf.2.2.1 20 (by decide)] using h20
  · simpa only [hf.2.2.1 21 (by decide)] using h21
  · simpa only [hf.2.2.1 22 (by decide)] using h22
  · simpa only [hf.2.2.1 36 (by decide)] using h36
  · simpa only [hf.2.2.1 37 (by decide)] using h37
  · simpa only [hf.2.2.1 38 (by decide)] using h38

/-- The polynomial evaluator is checked one actual instruction at a time.
Explicit powers prevent later state simplification from expanding its repeated
squaring expressions into one large symbolic register dictionary. -/
private lemma phi_eval {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (s : MachineState) (x : ℝ) (hpc : s.pc=158) (hx : s.reals 14=x)
    (hA : s.reals 20=19/146) (hB : s.reals 21=35/438) (hC : s.reals 22=1/66) :
    ∃ t, Runs metricProgram 12 s t ∧ t.pc=170 ∧ ProgramScoresFrame R s t ∧
      t.naturals=s.naturals ∧ t.memory=s.memory ∧ t.reals 15=PhiStar x ∧
      (∀ i ∈ ({1,11,12,13,14} : Finset ℕ), t.reals i=s.reals i) := by
  let a1 : MachineState := {s with pc := 159, reals := Function.update s.reals 23 (x^2)}
  let a2 : MachineState := {a1 with pc := 160, reals := Function.update a1.reals 24 (x^3)}
  let a3 : MachineState := {a2 with pc := 161, reals := Function.update a2.reals 25 (x^4)}
  let a4 : MachineState := {a3 with pc := 162, reals := Function.update a3.reals 26 (x^8)}
  let a5 : MachineState := {a4 with pc := 163, reals := Function.update a4.reals 27 (x^16)}
  let a6 : MachineState := {a5 with pc := 164, reals := Function.update a5.reals 28 (x^32)}
  let a7 : MachineState := {a6 with pc := 165, reals := Function.update a6.reals 29 (x^33)}
  let a8 : MachineState := {a7 with pc := 166, reals := Function.update a7.reals 30 ((19/146 : ℝ)*x^2)}
  let a9 : MachineState := {a8 with pc := 167, reals := Function.update a8.reals 31 ((35/438 : ℝ)*x^3)}
  let a10 : MachineState := {a9 with pc := 168, reals := Function.update a9.reals 32 ((1/66 : ℝ)*x^33)}
  let a11 : MachineState := {a10 with pc := 169, reals := Function.update a10.reals 33 ((19/146 : ℝ)*x^2+(35/438 : ℝ)*x^3)}
  let a12 : MachineState := {a11 with pc := 170, reals := Function.update a11.reals 15 (PhiStar x)}
  have hp2 : x*x=x^2 := by ring
  have hp3 : x^2*x=x^3 := by ring
  have hp4 : x^2*x^2=x^4 := by ring
  have hp8 : x^4*x^4=x^8 := by ring
  have hp16 : x^8*x^8=x^16 := by ring
  have hp32 : x^16*x^16=x^32 := by ring
  have hp33 : x^32*x=x^33 := by ring
  have hphi : (19/146 : ℝ)*x^2+(35/438 : ℝ)*x^3+(66 : ℝ)⁻¹*x^33=PhiStar x := by unfold PhiStar; ring
  have h1 : step metricProgram s=some a1 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h2 : step metricProgram a1=some a2 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h3 : step metricProgram a2=some a3 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a3,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h4 : step metricProgram a3=some a4 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a4,a3,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h5 : step metricProgram a4=some a5 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a5,a4,a3,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h6 : step metricProgram a5=some a6 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a6,a5,a4,a3,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h7 : step metricProgram a6=some a7 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a7,a6,a5,a4,a3,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h8 : step metricProgram a7=some a8 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a8,a7,a6,a5,a4,a3,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h9 : step metricProgram a8=some a9 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a9,a8,a7,a6,a5,a4,a3,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h10 : step metricProgram a9=some a10 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h11 : step metricProgram a10=some a11 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  have h12 : step metricProgram a11=some a12 := by
    simp (config := { maxSteps := 1000000 }) [step,applyRealOp,hpc,hx,hA,hB,hC,a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,hp2,hp3,hp4,hp8,hp16,hp32,hp33,hphi]
  refine ⟨a12,Runs.succ h1 (Runs.succ h2 (Runs.succ h3 (Runs.succ h4 (Runs.succ h5 (Runs.succ h6 (Runs.succ h7 (Runs.succ h8 (Runs.succ h9 (Runs.succ h10 (Runs.succ h11 (Runs.succ h12 (Runs.zero a12)))))))))))),rfl,?_,rfl,rfl,?_,?_⟩
  · refine ⟨rfl,fun _ _ => rfl,?_,fun _ _ => rfl⟩
    intro i hi
    have hn15 : i ≠ 15 := by intro he; subst i; simp at hi
    have hn23 : i ≠ 23 := by intro he; subst i; simp at hi
    have hn24 : i ≠ 24 := by intro he; subst i; simp at hi
    have hn25 : i ≠ 25 := by intro he; subst i; simp at hi
    have hn26 : i ≠ 26 := by intro he; subst i; simp at hi
    have hn27 : i ≠ 27 := by intro he; subst i; simp at hi
    have hn28 : i ≠ 28 := by intro he; subst i; simp at hi
    have hn29 : i ≠ 29 := by intro he; subst i; simp at hi
    have hn30 : i ≠ 30 := by intro he; subst i; simp at hi
    have hn31 : i ≠ 31 := by intro he; subst i; simp at hi
    have hn32 : i ≠ 32 := by intro he; subst i; simp at hi
    have hn33 : i ≠ 33 := by intro he; subst i; simp at hi
    simp only [a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,Function.update_apply,hn15,hn23,hn24,hn25,hn26,hn27,hn28,hn29,hn30,hn31,hn32,hn33,ite_false]
  · simp only [a12,Function.update_self]
  · intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    all_goals simp [a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1]

private lemma fetch {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (P : Lottery R.count)
    (ε : ℝ) (s : MachineState) (v : Fin n) (i : Fin R.count) (b : ℝ)
    (hpc : s.pc=153) (hL : ProgramLayout n m R.count s) (hC : ProgramConstants ε s)
    (hR : ProgramReductionMemory R s) (hP : ∀ c, s.memory (m+c.val)=P.val c)
    (hi : s.naturals 9=i.val) (hrow : s.naturals 25=2*n*m+3*m+v.val*R.count)
    (hb : s.reals 11=b) (hprev : s.reals 12=PhiStar b) :
    let c := (R.profile v).symm i;
    ∃ t, Runs metricProgram 5 s t ∧ t.pc=158 ∧ ProgramScoresFrame R s t ∧
      t.naturals 9=s.naturals 9 ∧ t.naturals 8=s.naturals 8 ∧ t.naturals 25=s.naturals 25 ∧
      t.naturals 15=c.val ∧ t.reals 11=b ∧ t.reals 12=PhiStar b ∧
      t.reals 14=b+P.val c ∧ t.memory=s.memory := by
  dsimp only
  let c := (R.profile v).symm i
  let t := (blockRun 5 s).getD s
  have htrace : blockRun 5 s=some t := by simp [t,blockRun,step,hpc]
  rcases hL with ⟨h0,h1,h2,h3,h4,h5,h20,h21,h22,h23,h24,h26,h27,h28,h29⟩
  have hc : s.naturalMemory (2*n*m+3*m+v.val*R.count+i.val)=c.val := hR.2.2.2 v i
  refine ⟨t,blockRun_sound htrace,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [t,blockRun,step,hpc]
  · refine ⟨?_,?_,?_,?_⟩
    · simp [t,blockRun,step,hpc]
    · intro j hj
      have h11 : j ≠ 11 := by intro he; subst j; simp at hj
      have h15 : j ≠ 15 := by intro he; subst j; simp at hj
      simp [t,blockRun,step,hpc,Function.update_apply,h11,h15]
    · intro j hj
      have h13 : j ≠ 13 := by intro he; subst j; simp at hj
      have h14 : j ≠ 14 := by intro he; subst j; simp at hj
      simp [t,blockRun,step,hpc,Function.update_apply,h13,h14]
    · intro j _
      simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc,hrow,hi,hc,c]
  · simp [t,blockRun,step,hpc,hb]
  · simp [t,blockRun,step,hpc,hprev]
  · simp [t,blockRun,step,hpc,applyRealOp,hrow,hi,hc,h26,hb,hP c,c]
  · simp [t,blockRun,step,hpc]

private lemma store_advance {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (s : MachineState) (c : Fin R.count) (i : ℕ) (x F G : ℝ)
    (hpc : s.pc=170) (hc : s.naturals 15=c.val) (hi : s.naturals 9=i)
    (hbase : s.naturals 29=4*m) (hone : s.naturals 3=1) (hz : s.reals 1=0)
    (hx : s.reals 14=x) (hF : s.reals 12=F) (hG : s.reals 15=G) :
    ∃ t, Runs metricProgram 9 s t ∧ t.pc=152 ∧ ProgramScoresFrame R s t ∧
      t.naturals 9=i+1 ∧ t.naturals 8=s.naturals 8 ∧ t.naturals 25=s.naturals 25 ∧
      t.reals 11=x ∧ t.reals 12=G ∧
      t.memory=Function.update s.memory (4*m+c.val) (s.memory (4*m+c.val)+G-F) := by
  let t := (blockRun 9 s).getD s
  have htrace : blockRun 9 s=some t := by simp [t,blockRun,step,hpc]
  have hmemory : t.memory=Function.update s.memory (4*m+c.val) (s.memory (4*m+c.val)+G-F) := by
    funext j
    simp [t,blockRun,step,hpc,applyRealOp,hc,hi,hbase,hF,hG,Function.update_apply]
    split_ifs <;> ring
  refine ⟨t,blockRun_sound htrace,?_,?_,?_,?_,?_,?_,?_,hmemory⟩
  · simp [t,blockRun,step,hpc]
  · refine ⟨?_,?_,?_,?_⟩
    · simp [t,blockRun,step,hpc]
    · intro j hj
      have h9 : j ≠ 9 := by intro he; subst j; simp at hj
      have h11 : j ≠ 11 := by intro he; subst j; simp at hj
      simp [t,blockRun,step,hpc,Function.update_apply,h9,h11]
    · intro j hj
      have h11 : j ≠ 11 := by intro he; subst j; simp at hj
      have h12 : j ≠ 12 := by intro he; subst j; simp at hj
      have h16 : j ≠ 16 := by intro he; subst j; simp at hj
      have h33 : j ≠ 33 := by intro he; subst j; simp at hj
      simp [t,blockRun,step,hpc,Function.update_apply,h11,h12,h16,h33]
    · intro j hj
      rw [hmemory]
      have hne : j ≠ 4*m+c.val := by have hbound := c.isLt; omega
      simp [Function.update_apply,hne]
  · simp [t,blockRun,step,hpc,hi,hone]
  · simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc,applyRealOp,hx,hz]
  · simp [t,blockRun,step,hpc,applyRealOp,hG,hz]

/-- Fetch the ranked candidate, evaluate PhiStar, and store its endpoint
contribution. All three blocks are traces of the actual instruction list. -/
private lemma body (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (P : Lottery R.count)
    (ε : ℝ) (s : MachineState) (v : Fin n) (i : Fin R.count) (b : ℝ)
    (hpc : s.pc=153) (hL : ProgramLayout n m R.count s) (hC : ProgramConstants ε s)
    (hR : ProgramReductionMemory R s) (hP : ∀ c, s.memory (m+c.val)=P.val c)
    (hi : s.naturals 9=i.val) (hrow : s.naturals 25=2*n*m+3*m+v.val*R.count)
    (hb : s.reals 11=b) (hprev : s.reals 12=PhiStar b) :
    let c := (R.profile v).symm i;
    ∃ t, Runs metricProgram 26 s t ∧ t.pc=152 ∧ ProgramScoresFrame R s t ∧
      t.naturals 9=i.val+1 ∧ t.naturals 8=s.naturals 8 ∧ t.naturals 25=s.naturals 25 ∧
      t.reals 11=b+P.val c ∧ t.reals 12=PhiStar (b+P.val c) ∧
      t.memory=Function.update s.memory (4*m+c.val)
        (s.memory (4*m+c.val)+PhiStar (b+P.val c)-PhiStar b) := by
  obtain ⟨u,hu,hupc,huFrame,hu9,hu8,hu25,huc,hub,huF,hux,huMem⟩ :=
    fetch R P ε s v i b hpc hL hC hR hP hi hrow hb hprev
  have hCu := frame_constants R huFrame hC
  obtain ⟨z,hz,hzpc,hzFrame,hzNat,hzMem,hzG,hzRegs⟩ :=
    phi_eval R u (b+P.val ((R.profile v).symm i)) hupc hux
      hCu.2.2.2.1 hCu.2.2.2.2.1 hCu.2.2.2.2.2.1
  have hzFrame0 := frame_trans R huFrame hzFrame
  have hLz := frame_layout R hzFrame0 hL
  have hCz := frame_constants R hzFrame0 hC
  have hzc : z.naturals 15=((R.profile v).symm i).val := by rw [hzNat]; exact huc
  have hz9 : z.naturals 9=i.val := by rw [hzNat,hu9]; exact hi
  have hzx : z.reals 14=b+P.val ((R.profile v).symm i) := (hzRegs 14 (by decide)).trans hux
  have hzF : z.reals 12=PhiStar b := (hzRegs 12 (by decide)).trans huF
  obtain ⟨t,ht,htpc,htFrame,ht9,ht8,ht25,htx,htG,htMem⟩ :=
    store_advance R z ((R.profile v).symm i) i.val (b+P.val ((R.profile v).symm i))
      (PhiStar b) (PhiStar (b+P.val ((R.profile v).symm i))) hzpc hzc hz9
      hLz.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hLz.2.2.2.1 hCz.2.1 hzx hzF hzG
  refine ⟨t,?_,htpc,frame_trans R hzFrame0 htFrame,ht9,?_,?_,htx,htG,?_⟩
  · have h₁ := h.child_0.1 metricProgram 5 12 s u z hu hz
    simpa using h.child_0.1 metricProgram 17 9 s z t h₁ ht
  · rw [ht8,hzNat]
    exact hu8
  · rw [ht25,hzNat]
    exact hu25
  · simpa only [hzMem,huMem] using htMem

private def accumulated {n r : ℕ} (σ : Profile n r) (P : Lottery r) (i : ℕ) (c : Fin r) : ℝ :=
  ∑ v, if v.val < i then scoreDelta σ P v c else 0

private lemma accumulated_zero {n r : ℕ} (σ : Profile n r) (P : Lottery r) (c : Fin r) :
    accumulated σ P 0 c=0 := by simp [accumulated]

private lemma accumulated_full {n r : ℕ} (σ : Profile n r) (P : Lottery r) (c : Fin r) :
    accumulated σ P n c=∑ v, scoreDelta σ P v c := by
  apply Finset.sum_congr rfl
  intro v _
  exact if_pos v.isLt

private lemma accumulated_step {n r : ℕ} (σ : Profile n r) (P : Lottery r)
    (i : ℕ) (hi : i < n) (c : Fin r) :
    accumulated σ P (i+1) c=accumulated σ P i c+scoreDelta σ P ⟨i,hi⟩ c := by
  calc
    _ = ∑ v, ((if v.val < i then scoreDelta σ P v c else 0)+
        (if v=⟨i,hi⟩ then scoreDelta σ P v c else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v=⟨i,hi⟩
      · subst v
        simp
      · have hvval : v.val ≠ i := fun he => hv (Fin.ext he)
        have hequiv : v.val < i+1 ↔ v.val < i := by omega
        simp [hequiv,hv]
    _ = _ := by simp [accumulated,Finset.sum_add_distrib]

private lemma pc_frame {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (s : MachineState) (q : ℕ) :
    ProgramScoresFrame R s {s with pc := q} := by
  exact ⟨rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩

private lemma one_step {s t : MachineState} (h : step metricProgram s=some t) :
    Runs metricProgram 1 s t := Runs.succ h (Runs.zero t)

private lemma setup {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (s : MachineState)
    (hpc : s.pc=149) (hz : s.reals 1=0) :
    ∃ t, Runs metricProgram 3 s t ∧ t.pc=152 ∧ ProgramScoresFrame R s t ∧
      t.naturals 9=0 ∧ t.naturals 8=s.naturals 8 ∧ t.naturals 25=s.naturals 25 ∧
      t.reals 11=0 ∧ t.reals 12=0 ∧ t.memory=s.memory := by
  let t := (blockRun 3 s).getD s
  have htrace : blockRun 3 s=some t := by simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
  refine ⟨t,blockRun_sound htrace,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
  · refine ⟨?_,?_,?_,?_⟩
    · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
    · intro a ha
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha
      simp_all [t,blockRun,step,Function.update_apply]
    · intro a ha
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha
      simp_all [t,blockRun,step,Function.update_apply]
    · intro a _
      simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc,applyRealOp,hz]
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc,applyRealOp,hz]
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]

private lemma advance {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (s : MachineState)
    (hpc : s.pc=179) (hr : s.naturals 5=R.count) (hone : s.naturals 3=1) :
    ∃ t, Runs metricProgram 3 s t ∧ t.pc=148 ∧ ProgramScoresFrame R s t ∧
      t.naturals 8=s.naturals 8+1 ∧ t.naturals 25=s.naturals 25+R.count ∧ t.memory=s.memory := by
  let t := (blockRun 3 s).getD s
  have htrace : blockRun 3 s=some t := by simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
  refine ⟨t,blockRun_sound htrace,?_,?_,?_,?_,?_⟩
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
  · refine ⟨?_,?_,?_,?_⟩
    · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
    · intro a ha
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha
      simp_all [t,blockRun,step,Function.update_apply]
    · intro a _
      simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
    · intro a _
      simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc,hone]
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc,hr]
  · simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]

private def Inner {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (P : Lottery R.count)
    (s0 : MachineState) (v : Fin n) (i : ℕ) (s : MachineState) : Prop :=
  s.pc=152 ∧ ProgramScoresFrame R s0 s ∧ s.naturals 8=v.val ∧
  s.naturals 25=2*n*m+3*m+v.val*R.count ∧ s.naturals 9=i ∧ i ≤ R.count ∧
  s.reals 11=scanPrefix (R.profile v) P i ∧ s.reals 12=PhiStar (scanPrefix (R.profile v) P i) ∧
  ∀ c, s.memory (4*m+c.val)=accumulated R.profile P v.val c+
    if (R.profile v c).val < i then scoreDelta R.profile P v c else 0

private def Outer {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (P : Lottery R.count)
    (s0 : MachineState) (i : ℕ) (s : MachineState) : Prop :=
  s.pc=148 ∧ ProgramScoresFrame R s0 s ∧ s.naturals 8=i ∧
  s.naturals 25=2*n*m+3*m+i*R.count ∧ i ≤ n ∧
  ∀ c, s.memory (4*m+c.val)=accumulated R.profile P i c

private lemma frame_probability {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (P : Lottery R.count) {s0 s : MachineState} (hf : ProgramScoresFrame R s0 s)
    (hP : ∀ c, s0.memory (m+c.val)=P.val c) : ∀ c, s.memory (m+c.val)=P.val c := by
  intro c
  have hrm := count_le R
  have hm : 0 < m := R.count_pos.trans_le hrm
  have hc := c.isLt
  exact (hf.2.2.2 _ (Or.inl (by omega))).trans (hP c)

private lemma frame_reduction {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    {s0 s : MachineState} (hf : ProgramScoresFrame R s0 s) (hR : ProgramReductionMemory R s0) :
    ProgramReductionMemory R s := by
  simpa only [ProgramReductionMemory,hf.1] using hR

private lemma inner_step (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (P : Lottery R.count) (ε : ℝ) (s0 : MachineState)
    (hL : ProgramLayout n m R.count s0) (hC : ProgramConstants ε s0)
    (hR : ProgramReductionMemory R s0) (hP : ∀ c, s0.memory (m+c.val)=P.val c)
    (v : Fin n) (i : ℕ) (hi : i < R.count) (s : MachineState) (hs : Inner R P s0 v i s) :
    ∃ t, Runs metricProgram 27 s t ∧ Inner R P s0 v (i+1) t := by
  rcases hs with ⟨hpc,hframe,hv,hrow,hindex,hbound,hprefix,hprevious,hscore⟩
  let u : MachineState := {s with pc := 153}
  have huFrame := frame_trans R hframe (pc_frame R s 153)
  have hLu := frame_layout R huFrame hL
  have hCu := frame_constants R huFrame hC
  have hcount : s.naturals 5=R.count := (frame_layout R hframe hL).2.2.2.2.2.1
  have hbranch : step metricProgram s=some u := by
    simp [step,hpc,hcount,hindex,show ¬R.count ≤ i from Nat.not_le.mpr hi,u]
  obtain ⟨t,htRun,htpc,htFrame,htindex,htv,htrow,htprefix,htprevious,htmemory⟩ :=
    body h R P ε u v ⟨i,hi⟩ (scanPrefix (R.profile v) P i) rfl hLu hCu
      (frame_reduction R huFrame hR) (frame_probability R P huFrame hP)
      hindex hrow hprefix hprevious
  refine ⟨t,?_,htpc,frame_trans R huFrame htFrame,?_,?_,htindex,by omega,?_,?_,?_⟩
  · simpa using h.child_0.1 metricProgram 1 26 s u t (one_step hbranch) htRun
  · exact htv.trans hv
  · exact htrow.trans hrow
  · rw [prefix_step (R.profile v) P i hi]
    exact htprefix
  · rw [prefix_step (R.profile v) P i hi]
    exact htprevious
  · intro c
    let c0 := (R.profile v).symm ⟨i,hi⟩
    have hc0 : (R.profile v c0).val=i := by simp [c0]
    have hp0 : scanPrefix (R.profile v) P i=below (R.profile v) P c0 := prefix_at _ _ ⟨i,hi⟩
    change t.memory=Function.update s.memory (4*m+c0.val)
      (s.memory (4*m+c0.val)+PhiStar (scanPrefix (R.profile v) P i+P.val c0)-
        PhiStar (scanPrefix (R.profile v) P i)) at htmemory
    by_cases hc : c=c0
    · subst c
      rw [htmemory]
      simp only [Function.update_self,u,hscore,hc0,lt_self_iff_false,ite_false,add_zero,
        Nat.lt_succ_self,ite_true]
      unfold scoreDelta
      rw [← hp0]
      ring
    · have haddr : 4*m+c.val ≠ 4*m+c0.val := by
        intro he
        apply hc
        apply Fin.ext
        omega
      rw [htmemory,Function.update_of_ne haddr]
      change s.memory (4*m+c.val) = _
      rw [hscore]
      have hval : (R.profile v c).val ≠ i := by
        intro he
        apply hc
        apply (R.profile v).injective
        apply Fin.ext
        simpa [hc0] using he
      have heq : (R.profile v c).val < i+1 ↔ (R.profile v c).val < i := by omega
      simp only [heq]

private lemma inner_loop (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (P : Lottery R.count) (ε : ℝ) (s0 : MachineState)
    (hL : ProgramLayout n m R.count s0) (hC : ProgramConstants ε s0)
    (hR : ProgramReductionMemory R s0) (hP : ∀ c, s0.memory (m+c.val)=P.val c)
    (v : Fin n) (s : MachineState) (hs : Inner R P s0 v 0 s) :
    ∃ t, Runs metricProgram (27*R.count) s t ∧ Inner R P s0 v R.count t := by
  have go : ∀ i, i ≤ R.count → ∃ t, Runs metricProgram (27*i) s t ∧ Inner R P s0 v i t := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨s,by simpa using Runs.zero (P := metricProgram) s,hs⟩
    | succ i ih =>
      intro hi
      obtain ⟨u,hu,hI⟩ := ih (by omega)
      obtain ⟨t,ht,hIt⟩ := inner_step h R P ε s0 hL hC hR hP v i (by omega) u hI
      refine ⟨t,?_,hIt⟩
      simpa [Nat.mul_add] using h.child_0.1 metricProgram (27*i) 27 s u t hu ht
  exact go R.count le_rfl

private lemma outer_step (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (P : Lottery R.count) (ε : ℝ) (s0 : MachineState)
    (hL : ProgramLayout n m R.count s0) (hC : ProgramConstants ε s0)
    (hR : ProgramReductionMemory R s0) (hP : ∀ c, s0.memory (m+c.val)=P.val c)
    (i : ℕ) (hi : i < n) (s : MachineState) (hs : Outer R P s0 i s) :
    ∃ t, Runs metricProgram (8+27*R.count) s t ∧ Outer R P s0 (i+1) t := by
  rcases hs with ⟨hpc,hframe,hindex,hrow,hbound,hscore⟩
  let u : MachineState := {s with pc := 149}
  have huFrame := frame_trans R hframe (pc_frame R s 149)
  have hn : s.naturals 0=n := (frame_layout R hframe hL).1
  have hbranch : step metricProgram s=some u := by
    simp [step,hpc,hn,hindex,show ¬n ≤ i from Nat.not_le.mpr hi,u]
  have hz : u.reals 1=0 := (frame_constants R huFrame hC).2.1
  obtain ⟨b,hbRun,hbpc,hbFrame,hbi,hbv,hbrow,hbprefix,hbprevious,hbmemory⟩ := setup R u rfl hz
  have hbFrame0 := frame_trans R huFrame hbFrame
  have hbInner : Inner R P s0 ⟨i,hi⟩ 0 b := by
    refine ⟨hbpc,hbFrame0,?_,?_,hbi,by omega,?_,?_,?_⟩
    · exact hbv.trans hindex
    · exact hbrow.trans hrow
    · simpa only [prefix_zero] using hbprefix
    · simpa only [prefix_zero,PhiStar,zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 3 ≠ 0),
        zero_pow (by decide : 33 ≠ 0),mul_zero,add_zero,zero_div] using hbprevious
    · intro c
      rw [hbmemory]
      simpa using hscore c
  obtain ⟨e,heRun,heInner⟩ := inner_loop h R P ε s0 hL hC hR hP ⟨i,hi⟩ b hbInner
  rcases heInner with ⟨hepc,heFrame,hev,herow,hei,hebound,heprefix,heprevious,hescore⟩
  let z : MachineState := {e with pc := 179}
  have hzFrame := frame_trans R heFrame (pc_frame R e 179)
  have her : e.naturals 5=R.count := (frame_layout R heFrame hL).2.2.2.2.2.1
  have hebranch : step metricProgram e=some z := by
    simp [step,hepc,her,hei,z]
  have hzL := frame_layout R hzFrame hL
  have hzOne : z.naturals 3=1 := hzL.2.2.2.1
  have hzr : z.naturals 5=R.count := hzL.2.2.2.2.2.1
  obtain ⟨t,htRun,htpc,htFrame,hti,htrow,htmemory⟩ := advance R z rfl hzr hzOne
  refine ⟨t,?_,htpc,frame_trans R hzFrame htFrame,?_,?_,by omega,?_⟩
  · have h₁ := h.child_0.1 metricProgram 1 3 s u b (one_step hbranch) hbRun
    have h₂ := h.child_0.1 metricProgram 4 (27*R.count) s b e h₁ heRun
    have h₃ := h.child_0.1 metricProgram (4+27*R.count) 1 s e z h₂ (one_step hebranch)
    have hcost : (4+27*R.count+1)+3=8+27*R.count := by omega
    simpa only [hcost] using h.child_0.1 metricProgram (4+27*R.count+1) 3 s z t h₃ htRun
  · simpa only [z,hev] using hti
  · rw [htrow]
    change e.naturals 25+R.count=2*n*m+3*m+(i+1)*R.count
    rw [herow]
    ring
  · intro c
    rw [htmemory]
    change e.memory (4*m+c.val)=_
    rw [hescore,accumulated_step R.profile P i hi]
    simp only [Fin.isLt,ite_true]

private lemma start_scan {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (P : Lottery R.count)
    (s : MachineState) (hpc : s.pc=146) (hL : ProgramLayout n m R.count s)
    (hzero : ∀ c : Fin R.count, s.memory (4*m+c.val)=0) :
    ∃ t, Runs metricProgram 2 s t ∧ Outer R P s 0 t := by
  let t := (blockRun 2 s).getD s
  have htrace : blockRun 2 s=some t := by simp [t,blockRun,step,hpc]
  rcases hL with ⟨h0,h1,h2,h3,h4,h5,h20,h21,h22,h23,h24,h26,h27,h28,h29⟩
  refine ⟨t,blockRun_sound htrace,?_,?_,?_,?_,by omega,?_⟩
  · simp [t,blockRun,step,hpc]
  · refine ⟨?_,?_,?_,?_⟩
    · simp [t,blockRun,step,hpc]
    · intro a ha
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha
      simp_all [t,blockRun,step,Function.update_apply]
    · intro a _
      simp [t,blockRun,step,hpc]
    · intro a _
      simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc,h24,h2]
  · intro c
    simpa [t,blockRun,step,hpc,accumulated] using hzero c

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ R hr ε P s hs
  rcases hs with ⟨hpc,hL,hC,hR,hpositive,hP,hzero⟩
  obtain ⟨b,hbRun,hbOuter⟩ := start_scan R P s hpc hL hzero
  have go : ∀ i, i ≤ n → ∃ t, Runs metricProgram ((8+27*R.count)*i) b t ∧ Outer R P s i t := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨b,by simpa using Runs.zero (P := metricProgram) b,hbOuter⟩
    | succ i ih =>
      intro hi
      obtain ⟨u,hu,hI⟩ := ih (by omega)
      obtain ⟨t,ht,hIt⟩ := outer_step h R P ε s hL hC hR hP i (by omega) u hI
      refine ⟨t,?_,hIt⟩
      simpa [Nat.mul_add] using h.child_0.1 metricProgram ((8+27*R.count)*i) (8+27*R.count) b u t hu ht
  obtain ⟨e,heRun,heOuter⟩ := go n le_rfl
  rcases heOuter with ⟨hepc,heFrame,hen,herow,hebound,hescore⟩
  let t : MachineState := {e with pc := 182}
  have hNe : e.naturals 0=n := (frame_layout R heFrame hL).1
  have hfinish : step metricProgram e=some t := by simp [step,hepc,hNe,hen,t]
  have h₁ := h.child_0.1 metricProgram 2 ((8+27*R.count)*n) s b e hbRun heRun
  have hrun := h.child_0.1 metricProgram (2+(8+27*R.count)*n) 1 s e t h₁ (one_step hfinish)
  refine ⟨2+(8+27*R.count)*n+1,t,hrun,rfl,?_,frame_trans R heFrame (pc_frame R e 182),?_,?_⟩
  · have hprod : 2*n ≤ n*R.count := by nlinarith [Nat.mul_le_mul_left n hr]
    nlinarith
  · intro c
    change e.memory (4*m+c.val)=_
    rw [hescore,accumulated_full]
    rfl
  · intro D hD c
    change e.memory (4*m+c.val)/(n*P.val c)=_
    rw [hescore,accumulated_full]
    exact (h.child_1 n R.count hn R.count_pos D hD R.profile P c (hpositive c)).symm

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramScores
