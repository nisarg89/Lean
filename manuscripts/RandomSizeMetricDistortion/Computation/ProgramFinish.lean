import RandomSizeMetricDistortion.Statements
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramFinish

private def chunk : ℕ → MachineState → Option MachineState
  | 0,s => some s
  | k+1,s => (step metricProgram s).bind (chunk k)
private theorem chunk_sound {k : ℕ} {s t : MachineState}
    (he : chunk k s=some t) : Runs metricProgram k s t := by
  induction k generalizing s with
  | zero => simp only [chunk,Option.some.injEq] at he; subst t; exact Runs.zero s
  | succ k ih =>
    cases hs : step metricProgram s with
    | none => simp [chunk,hs] at he
    | some u => apply Runs.succ hs; apply ih; simpa only [chunk,hs,Option.bind_some] using he

private def cleared (mem : ℕ → ℝ) (i : ℕ) : ℕ → ℝ :=
  fun a => if a < i then 0 else mem a
private theorem cleared_zero (mem : ℕ → ℝ) : cleared mem 0=mem := by
  funext a; simp [cleared]
private theorem cleared_update (mem : ℕ → ℝ) (i : ℕ) :
    Function.update (cleared mem i) i 0=cleared mem (i+1) := by
  funext a
  by_cases hai : a=i
  · subst a; simp [cleared]
  · have he : a < i+1 ↔ a < i := by omega
    simp [cleared,hai,he]
private def clearState (s : MachineState) (i : ℕ) : MachineState :=
  {s with pc := 212, naturals := Function.update s.naturals 6 i, memory := cleared s.memory i}
private def clearExit (s : MachineState) (m : ℕ) : MachineState :=
  {s with pc := 216, naturals := Function.update s.naturals 6 m, memory := cleared s.memory m}
private def finalState (s : MachineState) (m e : ℕ) : MachineState :=
  {s with pc := 226, naturals := Function.update (Function.update s.naturals 6 m) 12 e, memory := Function.update (cleared s.memory m) e 1}

private theorem clear_step (s : MachineState) (m i : ℕ) (hm : s.naturals 1=m)
    (h1 : s.naturals 3=1) (hz : s.reals 1=0) (hi : i < m) :
    Runs metricProgram 4 (clearState s i) (clearState s (i+1)) := by
  apply chunk_sound
  simp [chunk,step,metricProgram,clearState,hm,h1,hz,not_le.mpr hi,cleared_update]
private theorem clear_done (s : MachineState) (m : ℕ) (hm : s.naturals 1=m) :
    Runs metricProgram 1 (clearState s m) (clearExit s m) := by
  apply chunk_sound
  simp [chunk,step,metricProgram,clearState,clearExit,hm]

private theorem clear_loop (h : Computation_RunRules.Statement) (s : MachineState) (m : ℕ)
    (hm : s.naturals 1=m) (h1 : s.naturals 3=1) (hz : s.reals 1=0) :
    Runs metricProgram (4*m+1) (clearState s 0) (clearExit s m) := by
  have run : ∀ b i : ℕ, b=m-i → i ≤ m →
      Runs metricProgram (4*b+1) (clearState s i) (clearExit s m) := by
    intro b
    induction b with
    | zero =>
      intro i hb hi
      have him : i=m := by omega
      rw [him]
      exact clear_done s m hm
    | succ b ih =>
      intro i hb hi
      have him : i < m := by omega
      have ht := clear_step s m i hm h1 hz him
      have hu := ih (i+1) (by omega) (by omega)
      have hc := h.1 metricProgram 4 (4*b+1) _ _ _ ht hu
      convert hc using 1 <;> omega
  exact run m 0 (by omega) (by omega)

private theorem average_exists {r : ℕ} (P : ℕ → Lottery r) (N : ℕ) (hN : 0 < N) :
    ∃ Q : Lottery r, AverageLottery P N Q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let q : Fin r → ℝ := fun c => (∑ t ∈ Finset.range N, (P t).val c)/(N : ℝ)
  have hnonneg (c : Fin r) : 0 ≤ q c :=
    div_nonneg (Finset.sum_nonneg (fun t _ => (P t).property.1 c)) hNr.le
  have htotal : ∑ c, q c=1 := by
    dsimp only [q]
    rw [← Finset.sum_div,Finset.sum_comm]
    simp_rw [(P _).property.2]
    simp [ne_of_gt hNr]
  exact ⟨⟨q,hnonneg,htotal⟩,fun c => rfl⟩

private theorem lift_exists {n m : ℕ} {σ : Profile n m}
    (R : Reduction σ) (P : Lottery R.count) : ∃ Q : Lottery m, Lifts R P Q := by
  let q : Fin m → ℝ := fun c => ∑ j, if R.embed j=c then P.val j else 0
  have hnonneg (c : Fin m) : 0 ≤ q c := by
    exact Finset.sum_nonneg (fun j _ => by split_ifs; exact P.property.1 j; exact le_rfl)
  have htotal : ∑ c, q c=1 := by
    dsimp only [q]
    rw [Finset.sum_comm]
    have he (j : Fin R.count) : (∑ c, if R.embed j=c then P.val j else 0)=P.val j := by
      simp [eq_comm]
    simp_rw [he]
    exact P.property.2
  refine ⟨⟨q,hnonneg,htotal⟩,?_,?_⟩
  · intro c
    change (∑ j, if R.embed j=R.embed c then P.val j else 0)=P.val c
    have he (j : Fin R.count) : R.embed j=R.embed c ↔ j=c := R.embed.injective.eq_iff
    simp_rw [he]
    simp
  · intro c hc
    change (∑ j, if R.embed j=c then P.val j else 0)=0
    apply Finset.sum_eq_zero
    intro j _
    have hj : R.embed j≠c := fun he => hc ⟨j,he⟩
    simp [hj]

private structure ScatterData {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (Q : Lottery R.count) (N i : ℕ) (t : MachineState) : Prop where
  one : t.naturals 3=1
  count : t.naturals 5=R.count
  index : t.naturals 15=i
  base : t.naturals 28=3*m
  denominator : t.reals 19=N
  map : ∀ c : Fin R.count, t.naturalMemory (t.naturals 22+c.val)=(R.embed c).val
  accumulated : ∀ c : Fin R.count, t.memory (3*m+c.val)/(N : ℝ)=Q.val c
  written : ∀ c : Fin R.count, c.val < i → t.memory (R.embed c).val=Q.val c
  unwritten : ∀ c : Fin m, (∀ j : Fin R.count, j.val < i → R.embed j≠c) → t.memory c.val=0

private theorem scatter_pc {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (Q : Lottery R.count) (N i : ℕ) (t : MachineState) (pc : ℕ)
    (h : ScatterData R Q N i t) : ScatterData R Q N i {t with pc := pc} := by
  exact ⟨h.one,h.count,h.index,h.base,h.denominator,h.map,h.accumulated,h.written,h.unwritten⟩

private theorem code217 : metricProgram[217]?=some (.leNat 5 15 226 218) := by rfl
private theorem code218 : metricProgram[218]?=some (.natAdd 11 28 15) := by rfl
private theorem code219 : metricProgram[219]?=some (.load 34 11) := by rfl
private theorem code220 : metricProgram[220]?=some (.real .div 18 34 19) := by rfl
private theorem code221 : metricProgram[221]?=some (.natAdd 11 22 15) := by rfl
private theorem code222 : metricProgram[222]?=some (.loadNat 12 11) := by rfl
private theorem code223 : metricProgram[223]?=some (.store 12 18) := by rfl
private theorem code224 : metricProgram[224]?=some (.natAdd 15 15 3) := by rfl
private theorem code225 : metricProgram[225]?=some (.jump 217) := by rfl
attribute [local simp] code217 code218 code219 code220 code221 code222 code223 code224 code225

private theorem scatter_step {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (Q : Lottery R.count) (N i : ℕ) (t : MachineState)
    (hpc : t.pc=217) (h : ScatterData R Q N i t) (hi : i < R.count) :
    ∃ u, Runs metricProgram 9 t u ∧ u.pc=217 ∧ ScatterData R Q N (i+1) u := by
  let j : Fin R.count := ⟨i,hi⟩
  let e := R.embed j
  let u : MachineState :=
    {t with pc := 217, naturals := Function.update (Function.update (Function.update t.naturals 11 (t.naturals 22+i)) 12 e.val) 15 (i+1), reals := Function.update (Function.update t.reals 34 (t.memory (3*m+i))) 18 (Q.val j), memory := Function.update t.memory e.val (Q.val j)}
  have hmap : t.naturalMemory (t.naturals 22+i)=e.val := h.map j
  have hvalue : t.memory (3*m+i)/t.reals 19=Q.val j := by
    rw [h.denominator]
    exact h.accumulated j
  refine ⟨u,?_,rfl,?_⟩
  · apply chunk_sound
    simp [chunk,step,hpc,h.count,h.index,h.base,h.one,hmap,hvalue,not_le.mpr hi,u,applyRealOp]
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [u] using h.one
    · simpa [u] using h.count
    · simp [u]
    · simpa [u] using h.base
    · simpa [u] using h.denominator
    · intro c; simpa [u] using h.map c
    · intro c
      have he := e.isLt
      have hne : 3*m+c.val≠e.val := by omega
      simpa [u,hne] using h.accumulated c
    · intro c hc
      by_cases hcj : c=j
      · subst c; simp [u,e]
      · have hcval : c.val≠i := fun he => hcj (Fin.ext he)
        have hprev : c.val < i := by omega
        have hne : (R.embed c).val≠e.val := fun he => hcj (R.embed.injective (Fin.ext he))
        simpa [u,hne] using h.written c hprev
    · intro c hc
      have hec : e≠c := hc j (by dsimp [j]; omega)
      have hne : c.val≠e.val := fun he => hec (Fin.ext he.symm)
      have hprev := h.unwritten c (fun j hj => hc j (by omega))
      simpa [u,hne] using hprev

private theorem scatter_loop (h : Computation_RunRules.Statement)
    {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (Q : Lottery R.count)
    (N : ℕ) (t : MachineState) (hpc : t.pc=217) (hdata : ScatterData R Q N 0 t) :
    ∃ k out, Runs metricProgram k t out ∧ out.pc=226 ∧
      ScatterData R Q N R.count out ∧ k ≤ 9*(R.count+1) := by
  let Inv : MachineState → Prop := fun u => u.pc=217 ∧ ∃ i, i ≤ R.count ∧ ScatterData R Q N i u
  let Done : MachineState → Prop := fun u => u.pc=226 ∧ ScatterData R Q N R.count u
  let rank : MachineState → ℕ := fun u => R.count-u.naturals 15
  have body : ∀ u, Inv u → ∃ k out, Runs metricProgram k u out ∧ k ≤ 9 ∧
      (Done out ∨ (Inv out ∧ rank out < rank u)) := by
    intro u hu
    obtain ⟨hupc,i,hi,hd⟩ := hu
    by_cases hir : i=R.count
    · let out : MachineState := {u with pc := 226}
      have hrun : Runs metricProgram 1 u out := by
        apply chunk_sound
        simp [chunk,step,hupc,hd.count,hd.index,hir,out]
      have hdf : ScatterData R Q N R.count u := by simpa [hir] using hd
      exact ⟨1,out,hrun,by norm_num,Or.inl ⟨rfl,scatter_pc R Q N R.count u 226 hdf⟩⟩
    · have hir' : i < R.count := by omega
      obtain ⟨out,hrun,houtpc,hout⟩ := scatter_step R Q N i u hupc hd hir'
      refine ⟨9,out,hrun,le_rfl,Or.inr ⟨⟨houtpc,i+1,by omega,hout⟩,?_⟩⟩
      have hidx := hd.index
      have hidx' := hout.index
      dsimp [rank]
      omega
  obtain ⟨k,out,hrun,hout,hcost⟩ := h.2 metricProgram Inv Done rank 9 body t ⟨hpc,0,by omega,hdata⟩
  exact ⟨k,out,hrun,hout.1,hout.2,by simpa [rank,hdata.index] using hcost⟩

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ R ε D hD P htraj
  dsimp only
  let N := Nat.ceil (Real.log R.count/(2*(ε/(32*n))^2))
  intro hN s hInv
  obtain ⟨Q',haverage⟩ := average_exists P N hN
  obtain ⟨Q,hlift⟩ := lift_exists R Q'
  rcases hInv with ⟨hpc,hLayout,hConst,hMemory,hNreg,hindex,hbound,hdelta,ha,heta,hr,hv,hP,hsum⟩
  rcases hLayout with ⟨hn0,hm1,hn2,hn3,hn4,hn5,hn20,hn21,hn22,hn23,hn24,hn26,hn27,hn28,hn29⟩
  rcases hConst with ⟨heps,hz,hOne,h20,h21,h22,h36,h37,h38⟩
  rcases hMemory with ⟨hkeep,hmap,hreverse,hranks⟩
  have haccum (c : Fin R.count) : s.memory (3*m+c.val)/(N : ℝ)=Q'.val c := by
    rw [hsum c]
    exact (haverage c).symm
  let b : MachineState := {s with reals := Function.update s.reals 19 (N : ℝ)}
  have hstart : Runs metricProgram 3 s (clearState b 0) := by
    apply chunk_sound
    simp [N,chunk,step,metricProgram,hpc,hNreg,hindex,b,clearState,cleared_zero]
  have hclear : Runs metricProgram (4*m+1) (clearState b 0) (clearExit b m) :=
    clear_loop h.child_0 b m hm1 hn3 (by simpa [b] using hz)
  let t : MachineState := {clearExit b m with pc := 217, naturals := Function.update (clearExit b m).naturals 15 0}
  have hinit : Runs metricProgram 1 (clearExit b m) t := by
    apply chunk_sound
    simp [chunk,step,metricProgram,clearExit,t]
  have hdata : ScatterData R Q' N 0 t := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [t,clearExit,b] using hn3
    · simpa [t,clearExit,b] using hn5
    · simp [t]
    · simpa [t,clearExit,b] using hn28
    · simp [t,clearExit,b]
    · intro c
      simpa [t,clearExit,b,hn22] using hmap c
    · intro c
      have hnot : ¬3*m+c.val < m := by omega
      simpa [t,clearExit,b,cleared,hnot] using haccum c
    · intro c hc; omega
    · intro c hc
      simp [t,clearExit,b,cleared,c.isLt]
  obtain ⟨k,out,hrun,houtpc,hout,hk⟩ := scatter_loop h.child_0 R Q' N t rfl hdata
  refine ⟨3+(4*m+1)+1+k,out,Q,?_,?_,?_,?_,?_⟩
  · apply h.child_0.1 metricProgram (3+(4*m+1)+1) k _ _ _ _ hrun
    apply h.child_0.1 metricProgram (3+(4*m+1)) 1 _ _ _ _ hinit
    exact h.child_0.1 metricProgram 3 (4*m+1) _ _ _ hstart hclear
  · simp [Halted,houtpc,metricProgram]
  · intro c
    by_cases hc : c ∈ Set.range R.embed
    · obtain ⟨j,rfl⟩ := hc
      exact (hout.written j j.isLt).trans (hlift.1 j).symm
    · have hzero : out.memory c.val=0 :=
        hout.unwritten c (fun j _ he => hc ⟨j,he⟩)
      exact hzero.trans (hlift.2 c hc).symm
  · exact ⟨R,Q',hlift,Or.inr ⟨D,hD,P,htraj,haverage⟩⟩
  · have hRm : R.count ≤ m := by
      simpa using Fintype.card_le_of_injective R.embed R.embed.injective
    nlinarith

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramFinish
