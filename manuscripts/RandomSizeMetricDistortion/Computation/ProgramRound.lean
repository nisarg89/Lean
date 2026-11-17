import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace MetricDistortion.Contracts.Computation_ProgramRound

@[simp] private lemma code_133 : metricProgram[133]? = some (.leNat 17 18 210 134) := by rfl
@[simp] private lemma code_134 : metricProgram[134]? = some (.natConst 15 0) := by rfl
@[simp] private lemma code_135 : metricProgram[135]? = some (.leNat 5 15 146 136) := by rfl
@[simp] private lemma code_136 : metricProgram[136]? = some (.natAdd 11 26 15) := by rfl
@[simp] private lemma code_137 : metricProgram[137]? = some (.load 13 11) := by rfl
@[simp] private lemma code_138 : metricProgram[138]? = some (.natAdd 11 28 15) := by rfl
@[simp] private lemma code_139 : metricProgram[139]? = some (.load 34 11) := by rfl
@[simp] private lemma code_140 : metricProgram[140]? = some (.real .add 34 34 13) := by rfl
@[simp] private lemma code_141 : metricProgram[141]? = some (.store 11 34) := by rfl
@[simp] private lemma code_142 : metricProgram[142]? = some (.natAdd 11 29 15) := by rfl
@[simp] private lemma code_143 : metricProgram[143]? = some (.store 11 1) := by rfl
@[simp] private lemma code_144 : metricProgram[144]? = some (.natAdd 15 15 3) := by rfl
@[simp] private lemma code_145 : metricProgram[145]? = some (.jump 135) := by rfl
@[simp] private lemma code_182 : metricProgram[182]? = some (.real .add 10 1 1) := by rfl
@[simp] private lemma code_183 : metricProgram[183]? = some (.natConst 15 0) := by rfl
@[simp] private lemma code_184 : metricProgram[184]? = some (.leNat 5 15 199 185) := by rfl
@[simp] private lemma code_185 : metricProgram[185]? = some (.natAdd 11 26 15) := by rfl
@[simp] private lemma code_186 : metricProgram[186]? = some (.load 13 11) := by rfl
@[simp] private lemma code_187 : metricProgram[187]? = some (.natAdd 11 29 15) := by rfl
@[simp] private lemma code_188 : metricProgram[188]? = some (.load 16 11) := by rfl
@[simp] private lemma code_189 : metricProgram[189]? = some (.real .mul 33 7 13) := by rfl
@[simp] private lemma code_190 : metricProgram[190]? = some (.real .div 17 16 33) := by rfl
@[simp] private lemma code_191 : metricProgram[191]? = some (.real .mul 33 5 17) := by rfl
@[simp] private lemma code_192 : metricProgram[192]? = some (.real .exp 9 33 1) := by rfl
@[simp] private lemma code_193 : metricProgram[193]? = some (.real .mul 18 13 9) := by rfl
@[simp] private lemma code_194 : metricProgram[194]? = some (.natAdd 11 27 15) := by rfl
@[simp] private lemma code_195 : metricProgram[195]? = some (.store 11 18) := by rfl
@[simp] private lemma code_196 : metricProgram[196]? = some (.real .add 10 10 18) := by rfl
@[simp] private lemma code_197 : metricProgram[197]? = some (.natAdd 15 15 3) := by rfl
@[simp] private lemma code_198 : metricProgram[198]? = some (.jump 184) := by rfl
@[simp] private lemma code_199 : metricProgram[199]? = some (.natConst 15 0) := by rfl
@[simp] private lemma code_200 : metricProgram[200]? = some (.leNat 5 15 208 201) := by rfl
@[simp] private lemma code_201 : metricProgram[201]? = some (.natAdd 11 27 15) := by rfl
@[simp] private lemma code_202 : metricProgram[202]? = some (.load 18 11) := by rfl
@[simp] private lemma code_203 : metricProgram[203]? = some (.real .div 13 18 10) := by rfl
@[simp] private lemma code_204 : metricProgram[204]? = some (.natAdd 11 26 15) := by rfl
@[simp] private lemma code_205 : metricProgram[205]? = some (.store 11 13) := by rfl
@[simp] private lemma code_206 : metricProgram[206]? = some (.natAdd 15 15 3) := by rfl
@[simp] private lemma code_207 : metricProgram[207]? = some (.jump 200) := by rfl
@[simp] private lemma code_208 : metricProgram[208]? = some (.natAdd 18 18 3) := by rfl
@[simp] private lemma code_209 : metricProgram[209]? = some (.jump 133) := by rfl

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

private lemma one_step {s t : MachineState} (h : step metricProgram s=some t) :
    Runs metricProgram 1 s t := Runs.succ h (Runs.zero t)

private def sumPrefix {r : ℕ} (f : Fin r → ℝ) (i : ℕ) : ℝ :=
  ∑ c, if c.val < i then f c else 0

private lemma sumPrefix_zero {r : ℕ} (f : Fin r → ℝ) : sumPrefix f 0=0 := by simp [sumPrefix]

private lemma sumPrefix_full {r : ℕ} (f : Fin r → ℝ) : sumPrefix f r=∑ c, f c := by
  apply Finset.sum_congr rfl
  intro c _
  exact if_pos c.isLt

private lemma sumPrefix_step {r : ℕ} (f : Fin r → ℝ) (i : ℕ) (hi : i < r) :
    sumPrefix f (i+1)=sumPrefix f i+f ⟨i,hi⟩ := by
  calc
    _ = ∑ c, ((if c.val < i then f c else 0)+(if c=⟨i,hi⟩ then f c else 0)) := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : c=⟨i,hi⟩
      · subst c
        simp
      · have hval : c.val ≠ i := fun he => hc (Fin.ext he)
        have heq : c.val < i+1 ↔ c.val < i := by omega
        simp [heq,hc]
    _ = _ := by simp [sumPrefix,Finset.sum_add_distrib]

private def Core {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (ε : ℝ)
    (rounds index : ℕ) (s : MachineState) : Prop :=
  ProgramLayout n m R.count s ∧ ProgramConstants ε s ∧ ProgramReductionMemory R s ∧
  s.naturals 17=rounds ∧ s.naturals 18=index ∧
  s.reals 3=ε/(32*n) ∧ s.reals 4=2*(ε/(32*n))^2 ∧
  s.reals 5=4*(ε/(32*n)) ∧ s.reals 6=R.count ∧ s.reals 7=n

private lemma count_le {n m : ℕ} {σ : Profile n m} (R : Reduction σ) : R.count ≤ m := by
  simpa using Fintype.card_le_of_injective R.embed R.embed.injective

private def coreNat : Finset ℕ := {0,1,2,3,4,5,17,20,21,22,23,24,26,27,28,29}
private def coreReal : Finset ℕ := {0,1,2,3,4,5,6,7,20,21,22,36,37,38}
private def CoreFrame (s t : MachineState) : Prop :=
  t.naturalMemory=s.naturalMemory ∧
  (∀ i ∈ coreNat, t.naturals i=s.naturals i) ∧
  (∀ i ∈ coreReal, t.reals i=s.reals i)

private lemma core_frame_refl (s : MachineState) : CoreFrame s s :=
  ⟨rfl,fun _ _ => rfl,fun _ _ => rfl⟩

private lemma core_frame_trans {s u t : MachineState} (hu : CoreFrame s u) (ht : CoreFrame u t) :
    CoreFrame s t :=
  ⟨ht.1.trans hu.1,fun i hi => (ht.2.1 i hi).trans (hu.2.1 i hi),
    fun i hi => (ht.2.2 i hi).trans (hu.2.2 i hi)⟩

private lemma scores_core_frame {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    {s t : MachineState} (hf : ProgramScoresFrame R s t) : CoreFrame s t := by
  refine ⟨hf.1,?_,?_⟩
  · intro i hi
    apply hf.2.1
    have hd : Disjoint coreNat ({8,9,11,15,25} : Finset ℕ) := by decide
    exact fun hn => Finset.disjoint_left.mp hd hi hn
  · intro i hi
    apply hf.2.2.1
    have hd : Disjoint coreReal ({11,12,13,14,15,16,23,24,25,26,27,28,29,30,31,32,33} : Finset ℕ) := by decide
    exact fun hn => Finset.disjoint_left.mp hd hi hn

private lemma core_transport {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (ε : ℝ)
    (rounds index next : ℕ) {s t : MachineState} (hs : Core R ε rounds index s)
    (hf : CoreFrame s t) (hnext : t.naturals 18=next) : Core R ε rounds next t := by
  rcases hs with ⟨hL,hC,hR,h17,h18,hη,hη2,hη4,hr,hn⟩
  have hLt : ProgramLayout n m R.count t := by
    rcases hL with ⟨h0,h1,h2,h3,h4,h5,h20,h21,h22,h23,h24,h26,h27,h28,h29⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hf.2.1 0 (by decide)]
      exact h0
    · rw [hf.2.1 1 (by decide)]
      exact h1
    · rw [hf.2.1 2 (by decide)]
      exact h2
    · rw [hf.2.1 3 (by decide)]
      exact h3
    · rw [hf.2.1 4 (by decide)]
      exact h4
    · rw [hf.2.1 5 (by decide)]
      exact h5
    · rw [hf.2.1 20 (by decide)]
      exact h20
    · rw [hf.2.1 21 (by decide)]
      exact h21
    · rw [hf.2.1 22 (by decide)]
      exact h22
    · rw [hf.2.1 23 (by decide)]
      exact h23
    · rw [hf.2.1 24 (by decide)]
      exact h24
    · rw [hf.2.1 26 (by decide)]
      exact h26
    · rw [hf.2.1 27 (by decide)]
      exact h27
    · rw [hf.2.1 28 (by decide)]
      exact h28
    · rw [hf.2.1 29 (by decide)]
      exact h29
  have hCt : ProgramConstants ε t := by
    rcases hC with ⟨h0,h1,h2,h20,h21,h22,h36,h37,h38⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hf.2.2 0 (by decide)]
      exact h0
    · rw [hf.2.2 1 (by decide)]
      exact h1
    · rw [hf.2.2 2 (by decide)]
      exact h2
    · rw [hf.2.2 20 (by decide)]
      exact h20
    · rw [hf.2.2 21 (by decide)]
      exact h21
    · rw [hf.2.2 22 (by decide)]
      exact h22
    · rw [hf.2.2 36 (by decide)]
      exact h36
    · rw [hf.2.2 37 (by decide)]
      exact h37
    · rw [hf.2.2 38 (by decide)]
      exact h38
  have hRt : ProgramReductionMemory R t := by simpa only [ProgramReductionMemory,hf.1] using hR
  refine ⟨hLt,hCt,hRt,?_,hnext,?_,?_,?_,?_,?_⟩
  · rw [hf.2.1 17 (by decide)]
    exact h17
  · rw [hf.2.2 3 (by decide)]
    exact hη
  · rw [hf.2.2 4 (by decide)]
    exact hη2
  · rw [hf.2.2 5 (by decide)]
    exact hη4
  · rw [hf.2.2 6 (by decide)]
    exact hr
  · rw [hf.2.2 7 (by decide)]
    exact hn

/-- One charged iteration adds the current lottery to its averaging cell and
clears the score cell for that candidate. The temporary real register34 is
outside the persistent round core. -/
private lemma prepare_body {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (P : Lottery R.count) (rounds index : ℕ) (s : MachineState) (i : Fin R.count)
    (hpc : s.pc=136) (hcore : Core R ε rounds index s)
    (hP : ∀ c, s.memory (m+c.val)=P.val c) (hi : s.naturals 15=i.val) :
    ∃ t, Runs metricProgram 10 s t ∧ t.pc=135 ∧ CoreFrame s t ∧
      t.naturals 18=s.naturals 18 ∧ t.naturals 15=i.val+1 ∧
      t.memory=Function.update (Function.update s.memory (3*m+i.val)
        (s.memory (3*m+i.val)+P.val i)) (4*m+i.val) 0 := by
  let t := (blockRun 10 s).getD s
  have htrace : blockRun 10 s=some t := by
    simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc]
  have hL := hcore.1
  rcases hL with ⟨h0,h1,h2,h3,h4,h5,h20,h21,h22,h23,h24,h26,h27,h28,h29⟩
  have hz : s.reals 1=0 := hcore.2.1.2.1
  refine ⟨t,blockRun_sound htrace,?_,?_,?_,?_,?_⟩
  · simp [t,blockRun,step,hpc]
  · refine ⟨?_,?_,?_⟩
    · simp [t,blockRun,step,hpc]
    · intro a ha
      simp only [coreNat,Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [t,blockRun,step,hpc]
    · intro a ha
      simp only [coreReal,Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc,hi,h3]
  · funext a
    simp (config := { maxSteps := 1000000 }) [t,blockRun,step,hpc,applyRealOp,hi,h26,h28,h29,hP i,hz]

private lemma pc_core_frame (s : MachineState) (q : ℕ) : CoreFrame s {s with pc := q} :=
  ⟨rfl,fun _ _ => rfl,fun _ _ => rfl⟩

private def Preparing {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (ε : ℝ)
    (P : Lottery R.count) (rounds index : ℕ) (initial : MachineState)
    (average : Fin R.count → ℝ) (i : ℕ) (s : MachineState) : Prop :=
  s.pc=135 ∧ Core R ε rounds index s ∧ s.naturals 15=i ∧ i ≤ R.count ∧
  (∀ c, s.memory (m+c.val)=P.val c) ∧
  (∀ c, s.memory (3*m+c.val)=average c+(if c.val < i then P.val c else 0)) ∧
  (∀ c : Fin R.count, s.memory (4*m+c.val)=if c.val < i then 0 else initial.memory (4*m+c.val))

private lemma preparing_step (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (P : Lottery R.count) (rounds index : ℕ) (initial : MachineState)
    (average : Fin R.count → ℝ) (i : ℕ) (hi : i < R.count)
    (s : MachineState) (hs : Preparing R ε P rounds index initial average i s) :
    ∃ t, Runs metricProgram 11 s t ∧ Preparing R ε P rounds index initial average (i+1) t := by
  rcases hs with ⟨hpc,hcore,hindex,hbound,hP,haverage,hscore⟩
  let u : MachineState := {s with pc := 136}
  have hcoreu : Core R ε rounds index u :=
    core_transport R ε rounds index index hcore (pc_core_frame s 136) hcore.2.2.2.2.1
  have hr : s.naturals 5=R.count := hcore.1.2.2.2.2.2.1
  have hbranch : step metricProgram s=some u := by
    simp [step,hpc,hr,hindex,show ¬R.count ≤ i from Nat.not_le.mpr hi,u]
  obtain ⟨t,htRun,htpc,htFrame,htindex18,hti,htmemory⟩ :=
    prepare_body R ε P rounds index u ⟨i,hi⟩ rfl hcoreu hP hindex
  have hcounter : t.naturals 18=index := htindex18.trans hcore.2.2.2.2.1
  have hcoret := core_transport R ε rounds index index hcoreu htFrame hcounter
  have hrm := count_le R
  have hm : 0 < m := R.count_pos.trans_le hrm
  refine ⟨t,?_,htpc,hcoret,hti,by omega,?_,?_,?_⟩
  · simpa using h.child_0.1 metricProgram 1 10 s u t (one_step hbranch) htRun
  · intro c
    have hc := c.isLt
    have hne1 : m+c.val ≠ 4*m+i := by omega
    have hne2 : m+c.val ≠ 3*m+i := by omega
    rw [htmemory,Function.update_of_ne hne1,Function.update_of_ne hne2]
    exact hP c
  · intro c
    have hc := c.isLt
    have hne : 3*m+c.val ≠ 4*m+i := by omega
    rw [htmemory,Function.update_of_ne hne]
    by_cases he : c=⟨i,hi⟩
    · subst c
      have ha : s.memory (3*m+i)=average ⟨i,hi⟩ := by simpa using haverage ⟨i,hi⟩
      simp only [Function.update_self,u,ha,Nat.lt_succ_self,ite_true]
    · have hval : c.val ≠ i := fun hx => he (Fin.ext hx)
      have ha : 3*m+c.val ≠ 3*m+i := by omega
      rw [Function.update_of_ne ha]
      change s.memory (3*m+c.val)=_
      rw [haverage]
      have heq : c.val < i+1 ↔ c.val < i := by omega
      simp only [heq]
  · intro c
    have hc := c.isLt
    by_cases he : c=⟨i,hi⟩
    · subst c
      rw [htmemory]
      simp only [Function.update_self,Nat.lt_succ_self,ite_true]
    · have hval : c.val ≠ i := fun hx => he (Fin.ext hx)
      have ha1 : 4*m+c.val ≠ 4*m+i := by omega
      have ha2 : 4*m+c.val ≠ 3*m+i := by omega
      rw [htmemory,Function.update_of_ne ha1,Function.update_of_ne ha2]
      change s.memory (4*m+c.val)=_
      rw [hscore]
      have heq : c.val < i+1 ↔ c.val < i := by omega
      simp only [heq]

private lemma preparing_loop (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (P : Lottery R.count) (rounds index : ℕ) (initial : MachineState)
    (average : Fin R.count → ℝ) (s : MachineState)
    (hs : Preparing R ε P rounds index initial average 0 s) :
    ∃ t, Runs metricProgram (11*R.count) s t ∧
      Preparing R ε P rounds index initial average R.count t := by
  have go : ∀ i, i ≤ R.count → ∃ t, Runs metricProgram (11*i) s t ∧
      Preparing R ε P rounds index initial average i t := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨s,by simpa using Runs.zero (P := metricProgram) s,hs⟩
    | succ i ih =>
      intro hi
      obtain ⟨u,hu,hI⟩ := ih (by omega)
      obtain ⟨t,ht,hIt⟩ := preparing_step h R ε P rounds index initial average i (by omega) u hI
      refine ⟨t,?_,hIt⟩
      simpa [Nat.mul_add] using h.child_0.1 metricProgram (11*i) 11 s u t hu ht
  exact go R.count le_rfl

private lemma cursor_frame (s : MachineState) (q v : ℕ) :
    CoreFrame s {s with pc := q, naturals := Function.update s.naturals 15 v} := by
  refine ⟨rfl,?_,fun _ _ => rfl⟩
  intro i hi
  have hne : i ≠ 15 := by intro he; subst i; simp [coreNat] at hi
  simp [Function.update_apply,hne]

private lemma prepare_phase (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (P : Lottery R.count) (rounds index : ℕ) (s : MachineState)
    (average : Fin R.count → ℝ) (hpc : s.pc=133) (hcore : Core R ε rounds index s)
    (hindex : index < rounds) (hP : ∀ c, s.memory (m+c.val)=P.val c)
    (haverage : ∀ c, s.memory (3*m+c.val)=average c) :
    ∃ t, Runs metricProgram (3+11*R.count) s t ∧ t.pc=146 ∧ Core R ε rounds index t ∧
      (∀ c, t.memory (m+c.val)=P.val c) ∧
      (∀ c : Fin R.count, t.memory (4*m+c.val)=0) ∧
      (∀ c, t.memory (3*m+c.val)=average c+P.val c) := by
  let u : MachineState := {s with pc := 134}
  have h17 : s.naturals 17=rounds := hcore.2.2.2.1
  have h18 : s.naturals 18=index := hcore.2.2.2.2.1
  have huRun : step metricProgram s=some u := by
    simp [step,hpc,h17,h18,show ¬rounds ≤ index from Nat.not_le.mpr hindex,u]
  let b : MachineState := {u with pc := 135, naturals := Function.update u.naturals 15 0}
  have hbRun : step metricProgram u=some b := by simp [step,u,b]
  have hframeb : CoreFrame s b := core_frame_trans (pc_core_frame s 134) (cursor_frame u 135 0)
  have hbCore : Core R ε rounds index b := by
    apply core_transport R ε rounds index index hcore hframeb
    simpa [b,u] using h18
  have hbPreparing : Preparing R ε P rounds index s average 0 b := by
    refine ⟨rfl,hbCore,rfl,Nat.zero_le _,?_,?_,?_⟩
    · intro c
      exact hP c
    · intro c
      simpa only [Nat.not_lt_zero,ite_false,add_zero] using haverage c
    · intro c
      simp [b,u]
  obtain ⟨e,heRun,hePreparing⟩ := preparing_loop h R ε P rounds index s average b hbPreparing
  rcases hePreparing with ⟨hepc,heCore,heIndex,heBound,heP,heAvg,heScores⟩
  let t : MachineState := {e with pc := 146}
  have her : e.naturals 5=R.count := heCore.1.2.2.2.2.2.1
  have htRun : step metricProgram e=some t := by simp [step,hepc,her,heIndex,t]
  have htCore : Core R ε rounds index t :=
    core_transport R ε rounds index index heCore (pc_core_frame e 146) heCore.2.2.2.2.1
  refine ⟨t,?_,rfl,htCore,heP,?_,?_⟩
  · have h₁ := h.child_0.1 metricProgram 1 1 s u b (one_step huRun) (one_step hbRun)
    have h₂ := h.child_0.1 metricProgram 2 (11*R.count) s b e h₁ heRun
    have hcost : (2+11*R.count)+1=3+11*R.count := by omega
    simpa only [hcost] using h.child_0.1 metricProgram (2+11*R.count) 1 s e t h₂ (one_step htRun)
  · intro c
    simpa only [if_pos c.isLt] using heScores c
  · intro c
    simpa only [if_pos c.isLt] using heAvg c

private def mwValue (n : ℕ) (ε probability score : ℝ) : ℝ :=
  probability*Real.exp (4*(ε/(32*n))*score)

/-- Each actual instruction in the weight block has its own transition
proof. Closed register values keep the score and exponential opaque in the
subsequent frame and loop arguments. -/
private lemma weight_body {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (P : Lottery R.count) (rounds index : ℕ) (s : MachineState) (c : Fin R.count)
    (g : ℝ) (hpc : s.pc=185) (hcore : Core R ε rounds index s)
    (hP : s.memory (m+c.val)=P.val c)
    (hscore : s.memory (4*m+c.val)/(n*P.val c)=g) (hi : s.naturals 15=c.val) :
    ∃ t, Runs metricProgram 14 s t ∧ t.pc=184 ∧ CoreFrame s t ∧
      t.naturals 18=s.naturals 18 ∧ t.naturals 15=c.val+1 ∧
      t.reals 10=s.reals 10+mwValue n ε (P.val c) g ∧
      t.memory=Function.update s.memory (2*m+c.val) (mwValue n ε (P.val c) g) := by
  rcases hcore with ⟨hL,hC,hR,h17,h18,hη,hη2,hη4,hr,hn⟩
  rcases hL with ⟨h0,h1,h2,honeNat,h4,h5,h20,h21,h22,h23,h24,h26,h27,h28,h29⟩
  let a1 : MachineState := {s with pc := 186, naturals := Function.update s.naturals 11 (m+c.val)}
  let a2 : MachineState := {a1 with pc := 187, reals := Function.update a1.reals 13 (P.val c)}
  let a3 : MachineState := {a2 with pc := 188, naturals := Function.update a2.naturals 11 (4*m+c.val)}
  let a4 : MachineState := {a3 with pc := 189, reals := Function.update a3.reals 16 (s.memory (4*m+c.val))}
  let a5 : MachineState := {a4 with pc := 190, reals := Function.update a4.reals 33 ((n : ℝ)*P.val c)}
  let a6 : MachineState := {a5 with pc := 191, reals := Function.update a5.reals 17 g}
  let a7 : MachineState := {a6 with pc := 192, reals := Function.update a6.reals 33 (4*(ε/(32*n))*g)}
  let a8 : MachineState := {a7 with pc := 193, reals := Function.update a7.reals 9 (Real.exp (4*(ε/(32*n))*g))}
  let a9 : MachineState := {a8 with pc := 194, reals := Function.update a8.reals 18 (mwValue n ε (P.val c) g)}
  let a10 : MachineState := {a9 with pc := 195, naturals := Function.update a9.naturals 11 (2*m+c.val)}
  let a11 : MachineState := {a10 with pc := 196, memory := Function.update a10.memory (2*m+c.val) (mwValue n ε (P.val c) g)}
  let a12 : MachineState := {a11 with pc := 197, reals := Function.update a11.reals 10 (s.reals 10+mwValue n ε (P.val c) g)}
  let a13 : MachineState := {a12 with pc := 198, naturals := Function.update a12.naturals 15 (c.val+1)}
  let a14 : MachineState := {a13 with pc := 184}
  have h1 : step metricProgram s=some a1 := by
    simp [step,applyRealOp,hpc,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h2 : step metricProgram a1=some a2 := by
    simp [step,applyRealOp,hpc,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h3 : step metricProgram a2=some a3 := by
    simp [step,applyRealOp,hpc,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h4 : step metricProgram a3=some a4 := by
    simp [step,applyRealOp,hpc,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h5 : step metricProgram a4=some a5 := by
    simp [step,applyRealOp,hpc,a5,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h6 : step metricProgram a5=some a6 := by
    simp [step,applyRealOp,hpc,a6,a5,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h7 : step metricProgram a6=some a7 := by
    simp [step,applyRealOp,hpc,a7,a6,a5,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h8 : step metricProgram a7=some a8 := by
    simp [step,applyRealOp,hpc,a8,a7,a6,a5,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h9 : step metricProgram a8=some a9 := by
    simp [step,applyRealOp,hpc,a9,a8,a7,a6,a5,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h10 : step metricProgram a9=some a10 := by
    simp [step,applyRealOp,hpc,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h11 : step metricProgram a10=some a11 := by
    simp [step,applyRealOp,hpc,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h12 : step metricProgram a11=some a12 := by
    simp [step,applyRealOp,hpc,a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h13 : step metricProgram a12=some a13 := by
    simp [step,applyRealOp,hpc,a13,a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  have h14 : step metricProgram a13=some a14 := by
    simp [step,applyRealOp,hpc,a14,a13,a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,hi,h26,h27,h29,hP,hn,hη4,hscore,mwValue,honeNat]
  refine ⟨a14,Runs.succ h1 (Runs.succ h2 (Runs.succ h3 (Runs.succ h4 (Runs.succ h5 (Runs.succ h6 (Runs.succ h7 (Runs.succ h8 (Runs.succ h9 (Runs.succ h10 (Runs.succ h11 (Runs.succ h12 (Runs.succ h13 (Runs.succ h14 (Runs.zero a14)))))))))))))),rfl,?_,?_,rfl,rfl,rfl⟩
  · refine ⟨rfl,?_,?_⟩
    · intro i hi
      have hn11 : i ≠ 11 := by intro he; subst i; simp [coreNat] at hi
      have hn15 : i ≠ 15 := by intro he; subst i; simp [coreNat] at hi
      simp only [a14,a13,a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,Function.update_apply,hn11,hn15,ite_false]
    · intro i hi
      have hr9 : i ≠ 9 := by intro he; subst i; simp [coreReal] at hi
      have hr10 : i ≠ 10 := by intro he; subst i; simp [coreReal] at hi
      have hr13 : i ≠ 13 := by intro he; subst i; simp [coreReal] at hi
      have hr16 : i ≠ 16 := by intro he; subst i; simp [coreReal] at hi
      have hr17 : i ≠ 17 := by intro he; subst i; simp [coreReal] at hi
      have hr18 : i ≠ 18 := by intro he; subst i; simp [coreReal] at hi
      have hr33 : i ≠ 33 := by intro he; subst i; simp [coreReal] at hi
      simp only [a14,a13,a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,Function.update_apply,hr9,hr10,hr13,hr16,hr17,hr18,hr33,ite_false]
  · simp [a14,a13,a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1]

private lemma normalize_body {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (rounds index : ℕ) (s : MachineState) (c : Fin R.count) (weight total : ℝ)
    (hpc : s.pc=201) (hcore : Core R ε rounds index s)
    (hweight : s.memory (2*m+c.val)=weight) (htotal : s.reals 10=total)
    (hi : s.naturals 15=c.val) :
    ∃ t, Runs metricProgram 7 s t ∧ t.pc=200 ∧ CoreFrame s t ∧
      t.naturals 18=s.naturals 18 ∧ t.naturals 15=c.val+1 ∧ t.reals 10=s.reals 10 ∧
      t.memory=Function.update s.memory (m+c.val) (weight/total) := by
  let t := (blockRun 7 s).getD s
  have htrace : blockRun 7 s=some t := by simp [t,blockRun,step,hpc]
  have hL := hcore.1
  rcases hL with ⟨h0,h1,h2,h3,h4,h5,h20,h21,h22,h23,h24,h26,h27,h28,h29⟩
  refine ⟨t,blockRun_sound htrace,?_,?_,?_,?_,?_,?_⟩
  · simp [t,blockRun,step,hpc]
  · refine ⟨?_,?_,?_⟩
    · simp [t,blockRun,step,hpc]
    · intro a ha
      simp only [coreNat,Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [t,blockRun,step,hpc]
    · intro a ha
      simp only [coreReal,Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc,hi,h3]
  · simp [t,blockRun,step,hpc]
  · funext a
    simp [t,blockRun,step,hpc,applyRealOp,hi,h26,h27,hweight,htotal]

private def Weighting {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (ε : ℝ)
    (P : Lottery R.count) (rounds index : ℕ) (g average : Fin R.count → ℝ)
    (i : ℕ) (s : MachineState) : Prop :=
  s.pc=184 ∧ Core R ε rounds index s ∧ s.naturals 15=i ∧ i ≤ R.count ∧
  s.reals 10=sumPrefix (fun c => mwValue n ε (P.val c) (g c)) i ∧
  (∀ c, s.memory (m+c.val)=P.val c) ∧
  (∀ c, s.memory (4*m+c.val)/(n*P.val c)=g c) ∧
  (∀ c, s.memory (3*m+c.val)=average c) ∧
  (∀ c, c.val < i → s.memory (2*m+c.val)=mwValue n ε (P.val c) (g c))

private lemma weighting_step (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (P : Lottery R.count) (rounds index : ℕ) (g average : Fin R.count → ℝ)
    (i : ℕ) (hi : i < R.count) (s : MachineState)
    (hs : Weighting R ε P rounds index g average i s) :
    ∃ t, Runs metricProgram 15 s t ∧ Weighting R ε P rounds index g average (i+1) t := by
  rcases hs with ⟨hpc,hcore,hindex,hbound,htotal,hP,hscore,haverage,hweights⟩
  let u : MachineState := {s with pc := 185}
  have hcoreu : Core R ε rounds index u :=
    core_transport R ε rounds index index hcore (pc_core_frame s 185) hcore.2.2.2.2.1
  have hr : s.naturals 5=R.count := hcore.1.2.2.2.2.2.1
  have hbranch : step metricProgram s=some u := by
    simp [step,hpc,hr,hindex,show ¬R.count ≤ i from Nat.not_le.mpr hi,u]
  obtain ⟨t,htRun,htpc,htFrame,htindex18,hti,htotal',htmemory⟩ :=
    weight_body R ε P rounds index u ⟨i,hi⟩ (g ⟨i,hi⟩) rfl hcoreu
      (hP ⟨i,hi⟩) (hscore ⟨i,hi⟩) hindex
  have hcounter : t.naturals 18=index := htindex18.trans hcore.2.2.2.2.1
  have hcoret := core_transport R ε rounds index index hcoreu htFrame hcounter
  have hrm := count_le R
  have hm : 0 < m := R.count_pos.trans_le hrm
  refine ⟨t,?_,htpc,hcoret,hti,by omega,?_,?_,?_,?_,?_⟩
  · simpa using h.child_0.1 metricProgram 1 14 s u t (one_step hbranch) htRun
  · rw [sumPrefix_step _ i hi]
    exact htotal'.trans (congrArg (fun z => z+mwValue n ε (P.val ⟨i,hi⟩) (g ⟨i,hi⟩)) htotal)
  · intro c
    have hc := c.isLt
    have ha : m+c.val ≠ 2*m+i := by omega
    rw [htmemory,Function.update_of_ne ha]
    exact hP c
  · intro c
    have hc := c.isLt
    have ha : 4*m+c.val ≠ 2*m+i := by omega
    rw [htmemory,Function.update_of_ne ha]
    exact hscore c
  · intro c
    have hc := c.isLt
    have ha : 3*m+c.val ≠ 2*m+i := by omega
    rw [htmemory,Function.update_of_ne ha]
    exact haverage c
  · intro c hc
    by_cases he : c=⟨i,hi⟩
    · subst c
      rw [htmemory,Function.update_self]
    · have hval : c.val ≠ i := fun hx => he (Fin.ext hx)
      have ha : 2*m+c.val ≠ 2*m+i := by omega
      rw [htmemory,Function.update_of_ne ha]
      exact hweights c (by omega)

private lemma weighting_loop (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (P : Lottery R.count) (rounds index : ℕ) (g average : Fin R.count → ℝ)
    (s : MachineState) (hs : Weighting R ε P rounds index g average 0 s) :
    ∃ t, Runs metricProgram (15*R.count) s t ∧ Weighting R ε P rounds index g average R.count t := by
  have go : ∀ i, i ≤ R.count → ∃ t, Runs metricProgram (15*i) s t ∧
      Weighting R ε P rounds index g average i t := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨s,by simpa using Runs.zero (P := metricProgram) s,hs⟩
    | succ i ih =>
      intro hi
      obtain ⟨u,hu,hI⟩ := ih (by omega)
      obtain ⟨t,ht,hIt⟩ := weighting_step h R ε P rounds index g average i (by omega) u hI
      refine ⟨t,?_,hIt⟩
      simpa [Nat.mul_add] using h.child_0.1 metricProgram (15*i) 15 s u t hu ht
  exact go R.count le_rfl

private def Normalizing {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (ε : ℝ)
    (Q : Lottery R.count) (rounds index : ℕ) (weights average : Fin R.count → ℝ)
    (total : ℝ) (i : ℕ) (s : MachineState) : Prop :=
  s.pc=200 ∧ Core R ε rounds index s ∧ s.naturals 15=i ∧ i ≤ R.count ∧ s.reals 10=total ∧
  (∀ c, s.memory (2*m+c.val)=weights c) ∧ (∀ c, s.memory (3*m+c.val)=average c) ∧
  (∀ c, c.val < i → s.memory (m+c.val)=Q.val c)

private lemma normalizing_step (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (Q : Lottery R.count) (rounds index : ℕ) (weights average : Fin R.count → ℝ)
    (total : ℝ) (hQ : ∀ c, Q.val c=weights c/total) (i : ℕ) (hi : i < R.count)
    (s : MachineState) (hs : Normalizing R ε Q rounds index weights average total i s) :
    ∃ t, Runs metricProgram 8 s t ∧ Normalizing R ε Q rounds index weights average total (i+1) t := by
  rcases hs with ⟨hpc,hcore,hindex,hbound,htotal,hweights,haverage,houtput⟩
  let u : MachineState := {s with pc := 201}
  have hcoreu : Core R ε rounds index u :=
    core_transport R ε rounds index index hcore (pc_core_frame s 201) hcore.2.2.2.2.1
  have hr : s.naturals 5=R.count := hcore.1.2.2.2.2.2.1
  have hbranch : step metricProgram s=some u := by
    simp [step,hpc,hr,hindex,show ¬R.count ≤ i from Nat.not_le.mpr hi,u]
  obtain ⟨t,htRun,htpc,htFrame,htindex18,hti,htotal',htmemory⟩ :=
    normalize_body R ε rounds index u ⟨i,hi⟩ (weights ⟨i,hi⟩) total rfl hcoreu
      (hweights ⟨i,hi⟩) htotal hindex
  have hcounter : t.naturals 18=index := htindex18.trans hcore.2.2.2.2.1
  have hcoret := core_transport R ε rounds index index hcoreu htFrame hcounter
  have hmem : t.memory=Function.update s.memory (m+i) (Q.val ⟨i,hi⟩) := by
    simpa only [← hQ ⟨i,hi⟩] using htmemory
  have hrm := count_le R
  have hm : 0 < m := R.count_pos.trans_le hrm
  refine ⟨t,?_,htpc,hcoret,hti,by omega,htotal'.trans htotal,?_,?_,?_⟩
  · simpa using h.child_0.1 metricProgram 1 7 s u t (one_step hbranch) htRun
  · intro c
    have hc := c.isLt
    have ha : 2*m+c.val ≠ m+i := by omega
    rw [hmem,Function.update_of_ne ha]
    exact hweights c
  · intro c
    have hc := c.isLt
    have ha : 3*m+c.val ≠ m+i := by omega
    rw [hmem,Function.update_of_ne ha]
    exact haverage c
  · intro c hc
    by_cases he : c=⟨i,hi⟩
    · subst c
      rw [hmem,Function.update_self]
    · have hval : c.val ≠ i := fun hx => he (Fin.ext hx)
      have ha : m+c.val ≠ m+i := by omega
      rw [hmem,Function.update_of_ne ha]
      exact houtput c (by omega)

private lemma normalizing_loop (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (Q : Lottery R.count) (rounds index : ℕ) (weights average : Fin R.count → ℝ)
    (total : ℝ) (hQ : ∀ c, Q.val c=weights c/total)
    (s : MachineState) (hs : Normalizing R ε Q rounds index weights average total 0 s) :
    ∃ t, Runs metricProgram (8*R.count) s t ∧
      Normalizing R ε Q rounds index weights average total R.count t := by
  have go : ∀ i, i ≤ R.count → ∃ t, Runs metricProgram (8*i) s t ∧
      Normalizing R ε Q rounds index weights average total i t := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨s,by simpa using Runs.zero (P := metricProgram) s,hs⟩
    | succ i ih =>
      intro hi
      obtain ⟨u,hu,hI⟩ := ih (by omega)
      obtain ⟨t,ht,hIt⟩ := normalizing_step h R ε Q rounds index weights average total hQ i (by omega) u hI
      refine ⟨t,?_,hIt⟩
      simpa [Nat.mul_add] using h.child_0.1 metricProgram (8*i) 8 s u t hu ht
  exact go R.count le_rfl

private lemma start_weights {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (rounds index : ℕ) (s : MachineState) (hpc : s.pc=182)
    (hcore : Core R ε rounds index s) :
    ∃ t, Runs metricProgram 2 s t ∧ t.pc=184 ∧ CoreFrame s t ∧
      t.naturals 18=s.naturals 18 ∧ t.naturals 15=0 ∧ t.reals 10=0 ∧ t.memory=s.memory := by
  let t := (blockRun 2 s).getD s
  have htrace : blockRun 2 s=some t := by simp [t,blockRun,step,hpc]
  have hz : s.reals 1=0 := hcore.2.1.2.1
  refine ⟨t,blockRun_sound htrace,?_,?_,?_,?_,?_,?_⟩
  · simp [t,blockRun,step,hpc]
  · refine ⟨?_,?_,?_⟩
    · simp [t,blockRun,step,hpc]
    · intro a ha
      have hne : a ≠ 15 := by intro he; subst a; simp [coreNat] at ha
      simp [t,blockRun,step,hpc,Function.update_apply,hne]
    · intro a ha
      have hne : a ≠ 10 := by intro he; subst a; simp [coreReal] at ha
      simp [t,blockRun,step,hpc,Function.update_apply,hne]
  · simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc,applyRealOp,hz]
  · simp [t,blockRun,step,hpc]

private lemma finish_round {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (rounds index : ℕ) (s : MachineState) (hpc : s.pc=208)
    (hcore : Core R ε rounds index s) :
    ∃ t, Runs metricProgram 2 s t ∧ t.pc=133 ∧ CoreFrame s t ∧
      t.naturals 18=index+1 ∧ t.memory=s.memory := by
  let t := (blockRun 2 s).getD s
  have htrace : blockRun 2 s=some t := by simp [t,blockRun,step,hpc]
  have hone : s.naturals 3=1 := hcore.1.2.2.2.1
  have hindex : s.naturals 18=index := hcore.2.2.2.2.1
  refine ⟨t,blockRun_sound htrace,?_,?_,?_,?_⟩
  · simp [t,blockRun,step,hpc]
  · refine ⟨?_,?_,?_⟩
    · simp [t,blockRun,step,hpc]
    · intro a ha
      have hne : a ≠ 18 := by intro he; subst a; simp [coreNat] at ha
      simp [t,blockRun,step,hpc,Function.update_apply,hne]
    · intro a _
      simp [t,blockRun,step,hpc]
  · simp [t,blockRun,step,hpc,hone,hindex]
  · simp [t,blockRun,step,hpc]

private lemma update_phase (h : Needs) {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (P Q : Lottery R.count) (rounds index : ℕ) (g average : Fin R.count → ℝ)
    (hQ : ∀ c, Q.val c=mwValue n ε (P.val c) (g c)/(∑ b, mwValue n ε (P.val b) (g b)))
    (s : MachineState) (hpc : s.pc=182) (hcore : Core R ε rounds index s)
    (hP : ∀ c, s.memory (m+c.val)=P.val c)
    (hscore : ∀ c, s.memory (4*m+c.val)/(n*P.val c)=g c)
    (haverage : ∀ c, s.memory (3*m+c.val)=average c) :
    ∃ t, Runs metricProgram (7+23*R.count) s t ∧ t.pc=133 ∧ Core R ε rounds (index+1) t ∧
      (∀ c, t.memory (m+c.val)=Q.val c) ∧ (∀ c, t.memory (3*m+c.val)=average c) := by
  obtain ⟨b,hbRun,hbpc,hbFrame,hb18,hb15,hb10,hbMem⟩ := start_weights R ε rounds index s hpc hcore
  have hbCore := core_transport R ε rounds index index hcore hbFrame (hb18.trans hcore.2.2.2.2.1)
  have hbWeighting : Weighting R ε P rounds index g average 0 b := by
    refine ⟨hbpc,hbCore,hb15,Nat.zero_le _,?_,?_,?_,?_,?_⟩
    · simpa only [sumPrefix_zero] using hb10
    · intro c
      rw [hbMem]
      exact hP c
    · intro c
      rw [hbMem]
      exact hscore c
    · intro c
      rw [hbMem]
      exact haverage c
    · intro c hc
      omega
  obtain ⟨e,heRun,heWeighting⟩ := weighting_loop h R ε P rounds index g average b hbWeighting
  rcases heWeighting with ⟨hepc,heCore,heIndex,heBound,heTotal,heP,heScores,heAvg,heWeights⟩
  let u : MachineState := {e with pc := 199}
  have her : e.naturals 5=R.count := heCore.1.2.2.2.2.2.1
  have huRun : step metricProgram e=some u := by simp [step,hepc,her,heIndex,u]
  let z : MachineState := {u with pc := 200, naturals := Function.update u.naturals 15 0}
  have hzRun : step metricProgram u=some z := by simp [step,u,z]
  have hzFrame := core_frame_trans (pc_core_frame e 199) (cursor_frame u 200 0)
  have hzCore : Core R ε rounds index z := by
    apply core_transport R ε rounds index index heCore hzFrame
    simpa [z,u] using heCore.2.2.2.2.1
  have hzNormalizing : Normalizing R ε Q rounds index
      (fun c => mwValue n ε (P.val c) (g c)) average (∑ c, mwValue n ε (P.val c) (g c)) 0 z := by
    refine ⟨rfl,hzCore,?_,Nat.zero_le _,?_,?_,?_,?_⟩
    · simp [z]
    · simpa only [sumPrefix_full] using heTotal
    · intro c
      exact heWeights c c.isLt
    · exact heAvg
    · intro c hc
      omega
  obtain ⟨f,hfRun,hfNormalizing⟩ := normalizing_loop h R ε Q rounds index
    (fun c => mwValue n ε (P.val c) (g c)) average (∑ c, mwValue n ε (P.val c) (g c)) hQ z hzNormalizing
  rcases hfNormalizing with ⟨hfpc,hfCore,hfIndex,hfBound,hfTotal,hfWeights,hfAvg,hfOutput⟩
  let w : MachineState := {f with pc := 208}
  have hfr : f.naturals 5=R.count := hfCore.1.2.2.2.2.2.1
  have hwRun : step metricProgram f=some w := by simp [step,hfpc,hfr,hfIndex,w]
  have hwCore : Core R ε rounds index w :=
    core_transport R ε rounds index index hfCore (pc_core_frame f 208) hfCore.2.2.2.2.1
  obtain ⟨t,htRun,htpc,htFrame,htIndex,htMem⟩ := finish_round R ε rounds index w rfl hwCore
  have htCore := core_transport R ε rounds index (index+1) hwCore htFrame htIndex
  refine ⟨t,?_,htpc,htCore,?_,?_⟩
  · have h₁ := h.child_0.1 metricProgram 2 (15*R.count) s b e hbRun heRun
    have h₂ := h.child_0.1 metricProgram 1 1 e u z (one_step huRun) (one_step hzRun)
    have h₃ := h.child_0.1 metricProgram (2+15*R.count) 2 s e z h₁ h₂
    have h₄ := h.child_0.1 metricProgram (2+15*R.count+2) (8*R.count) s z f h₃ hfRun
    have h₅ := h.child_0.1 metricProgram 1 2 f w t (one_step hwRun) htRun
    have hcost : (2+15*R.count+2+8*R.count)+3=7+23*R.count := by omega
    simpa only [hcost] using h.child_0.1 metricProgram (2+15*R.count+2+8*R.count) 3 s f t h₄ h₅
  · intro c
    rw [htMem]
    exact hfOutput c c.isLt
  · intro c
    rw [htMem]
    exact hfAvg c

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ R hr ε hε D hD P hTrajectory hPositive index s hs hindex
  rcases hs with ⟨hpc,hL,hC,hR,h17,h18,hbound,hη,hη2,hη4,hcount,hnReal,hP,hAverage⟩
  let N := Nat.ceil (Real.log R.count/(2*(ε/(32*n))^2))
  have hcore : Core R ε N index s := ⟨hL,hC,hR,h17,h18,hη,hη2,hη4,hcount,hnReal⟩
  obtain ⟨b,hbRun,hbpc,hbCore,hbP,hbZero,hbAvg⟩ :=
    prepare_phase h R ε (P index) N index s
      (fun c => ∑ u ∈ Finset.range index, (P u).val c) hpc hcore hindex hP hAverage
  have hInput : ProgramScoresInput R ε (P index) b :=
    ⟨hbpc,hbCore.1,hbCore.2.1,hbCore.2.2.1,hPositive index,hbP,hbZero⟩
  obtain ⟨k,e,heRun,hepc,heCost,heFrame,heSums,heScores⟩ :=
    h.child_1 n m hn (by omega) σ R hr ε (P index) b hInput
  have heCounter : e.naturals 18=index :=
    (heFrame.2.1 18 (by decide)).trans hbCore.2.2.2.2.1
  have heCore := core_transport R ε N index index hbCore (scores_core_frame R heFrame) heCounter
  have hrm := count_le R
  have hm0 : 0 < m := by omega
  have heP : ∀ c, e.memory (m+c.val)=(P index).val c := by
    intro c
    have hc := c.isLt
    exact (heFrame.2.2.2 _ (Or.inl (by omega))).trans (hbP c)
  let average : Fin R.count → ℝ := fun c => ∑ u ∈ Finset.range (index+1), (P u).val c
  have heAvg : ∀ c, e.memory (3*m+c.val)=average c := by
    intro c
    have hc := c.isLt
    have H := (heFrame.2.2.2 (3*m+c.val) (Or.inl (by omega))).trans (hbAvg c)
    simpa only [average,Finset.sum_range_succ] using H
  let g : Fin R.count → ℝ := fun c => score D R.profile (P index) c
  have hQ : ∀ c, (P (index+1)).val c=
      mwValue n ε ((P index).val c) (g c)/(∑ b, mwValue n ε ((P index).val b) (g b)) := by
    intro c
    simpa only [mwValue,g] using hTrajectory.2 index c
  obtain ⟨out,houtRun,houtpc,houtCore,houtP,houtAvg⟩ :=
    update_phase h R ε (P index) (P (index+1)) N index g average hQ e hepc heCore heP
      (heScores D hD) heAvg
  have h₁ := h.child_0.1 metricProgram (3+11*R.count) k s b e hbRun heRun
  have hRun := h.child_0.1 metricProgram (3+11*R.count+k) (7+23*R.count) s e out h₁ houtRun
  refine ⟨(3+11*R.count+k)+(7+23*R.count),out,hRun,?_,?_⟩
  · rcases houtCore with ⟨hL',hC',hR',h17',h18',hη',hη2',hη4',hcount',hnReal'⟩
    exact ⟨houtpc,hL',hC',hR',h17',h18',by omega,hη',hη2',hη4',hcount',hnReal',houtP,houtAvg⟩
  · have hnr : R.count ≤ n*R.count := by
      nlinarith [Nat.mul_le_mul_right R.count (show 1 ≤ n by omega)]
    nlinarith

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramRound
