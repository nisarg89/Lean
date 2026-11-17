import RandomSizeMetricDistortion.Statements
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramRanking

private def chargedTick (s : MachineState) : MachineState := (step metricProgram s).getD s
private def chargedReplay : ℕ → MachineState → MachineState
  | 0,s => s
  | k+1,s => chargedReplay k (chargedTick s)
private theorem chargedReplay_trace (k : ℕ) (s : MachineState)
    (hs : ∀ j < k, ∃ t, step metricProgram (chargedReplay j s) = some t) :
    Runs metricProgram k s (chargedReplay k s) := by
  induction k generalizing s with
  | zero => exact Runs.zero s
  | succ k ih =>
    obtain ⟨t,ht⟩ := hs 0 (by omega)
    change step metricProgram s = some t at ht
    have he : chargedTick s = t := by simp [chargedTick,ht]
    change Runs metricProgram (k+1) s (chargedReplay k (chargedTick s))
    apply Runs.succ (show step metricProgram s = some (chargedTick s) by simpa [he] using ht)
    apply ih
    intro j hj
    exact hs (j+1) (by omega)

private structure RowData {n m r : ℕ} (σ : Profile n m) (emb : Fin r ↪ Fin m)
    (v : Fin n) (i q : ℕ) (a : ℕ → ℕ) : Prop where
  count : q ≤ r
  steps : q ≤ i
  bound : ∀ j, j < q → a j < r
  injective : ∀ j, j < q → ∀ k, k < q → a j = a k → j = k
  sorted : ∀ j (hj : j < q) k (hk : k < q), j < k →
    (σ v) (emb ⟨a j,bound j hj⟩) < (σ v) (emb ⟨a k,bound k hk⟩)
  cover : ∀ c : Fin r, ((σ v) (emb c)).val < i ↔ ∃ j, j < q ∧ a j = c.val

private theorem RowData.skip {n m r i q : ℕ} {σ : Profile n m}
    {emb : Fin r ↪ Fin m} {v : Fin n} {a : ℕ → ℕ} {x : Fin m}
    (h : RowData σ emb v i q a) (hx : ((σ v) x).val = i)
    (hmissing : x ∉ Set.range emb) : RowData σ emb v (i+1) q a := by
  refine ⟨h.count,by have := h.steps; omega,h.bound,h.injective,h.sorted,?_⟩
  intro c
  have hne : ((σ v) (emb c)).val ≠ i := by
    intro he
    have hemb : emb c = x := (σ v).injective (Fin.ext (he.trans hx.symm))
    exact hmissing ⟨c,hemb⟩
  constructor
  · intro hc
    exact (h.cover c).1 (by omega)
  · intro hc
    have hp := (h.cover c).2 hc
    omega

private theorem RowData.keep {n m r i q : ℕ} {σ : Profile n m}
    {emb : Fin r ↪ Fin m} {v : Fin n} {a : ℕ → ℕ} (c : Fin r)
    (h : RowData σ emb v i q a) (hc : ((σ v) (emb c)).val = i) :
    RowData σ emb v (i+1) (q+1) (fun j => if j = q then c.val else a j) := by
  have hmissing (j : ℕ) (hj : j < q) : a j ≠ c.val := by
    intro he
    have hp := (h.cover c).2 ⟨j,hj,he⟩
    omega
  let f : Fin q → Fin r := fun j => ⟨a j.val,h.bound j.val j.isLt⟩
  have hfinj : Function.Injective f := by
    intro j k he
    exact Fin.ext (h.injective j.val j.isLt k.val k.isLt (congrArg Fin.val he))
  have hfnot : ¬ Function.Surjective f := by
    intro hs
    obtain ⟨j,hj⟩ := hs c
    exact hmissing j.val j.isLt (congrArg Fin.val hj)
  have hroom : q < r := by
    simpa only [Fintype.card_fin] using Fintype.card_lt_of_injective_not_surjective f hfinj hfnot
  let a' := fun j => if j = q then c.val else a j
  have hb : ∀ j, j < q+1 → a' j < r := by
    intro j hj
    by_cases heq : j = q
    · simpa only [a',if_pos heq] using c.isLt
    · simpa only [a',if_neg heq] using h.bound j (by omega)
  refine ⟨by omega,by have := h.steps; omega,hb,?_,?_,?_⟩
  · intro j hj k hk he
    by_cases hjEq : j = q <;> by_cases hkEq : k = q
    · omega
    · have hkr : k < q := by omega
      simp only [a',if_pos hjEq,if_neg hkEq] at he
      exact (hmissing k hkr he.symm).elim
    · have hjr : j < q := by omega
      simp only [a',if_neg hjEq,if_pos hkEq] at he
      exact (hmissing j hjr he).elim
    · simp only [a',if_neg hjEq,if_neg hkEq] at he
      exact h.injective j (by omega) k (by omega) he
  · intro j hj k hk hjk
    have hjold : j < q := by omega
    have hjne : j ≠ q := by omega
    have hJ : (⟨a' j,hb j hj⟩ : Fin r) = ⟨a j,h.bound j hjold⟩ := by
      apply Fin.ext
      simp [a',hjne]
    by_cases hkEq : k = q
    · have hK : (⟨a' k,hb k hk⟩ : Fin r) = c := by apply Fin.ext; simp [a',hkEq]
      rw [hJ,hK]
      have hp := (h.cover (⟨a j,h.bound j hjold⟩ : Fin r)).2 ⟨j,hjold,rfl⟩
      change ((σ v) (emb ⟨a j,h.bound j hjold⟩)).val < ((σ v) (emb c)).val
      omega
    · have hkold : k < q := by omega
      have hK : (⟨a' k,hb k hk⟩ : Fin r) = ⟨a k,h.bound k hkold⟩ := by
        apply Fin.ext
        simp [a',hkEq]
      rw [hJ,hK]
      exact h.sorted j hjold k hkold hjk
  · intro d
    constructor
    · intro hd
      by_cases hprev : ((σ v) (emb d)).val < i
      · obtain ⟨j,hj,hjd⟩ := (h.cover d).1 hprev
        refine ⟨j,by omega,?_⟩
        simpa only [a',if_neg (by omega : j ≠ q)] using hjd
      · have he : ((σ v) (emb d)).val = i := by omega
        have hdc : d = c := emb.injective ((σ v).injective (Fin.ext (he.trans hc.symm)))
        subst d
        exact ⟨q,by omega,by simp [a']⟩
    · rintro ⟨j,hj,hjd⟩
      by_cases hjEq : j = q
      · simp only [a',if_pos hjEq] at hjd
        have hdc : d = c := Fin.ext hjd.symm
        subst d
        omega
      · have hjold : j < q := by omega
        simp only [a',if_neg hjEq] at hjd
        have hp := (h.cover d).2 ⟨j,hjold,hjd⟩
        omega

private theorem RowData.congr {n m r i q : ℕ} {σ : Profile n m}
    {emb : Fin r ↪ Fin m} {v : Fin n} {a b : ℕ → ℕ}
    (h : RowData σ emb v i q a) (heq : ∀ j, j < q → a j = b j) :
    RowData σ emb v i q b := by
  have hb : ∀ j, j < q → b j < r := by intro j hj; rw [← heq j hj]; exact h.bound j hj
  refine ⟨h.count,h.steps,hb,?_,?_,?_⟩
  · intro j hj k hk he
    apply h.injective j hj k hk
    rwa [heq j hj,heq k hk]
  · intro j hj k hk hjk
    have hJ : (⟨b j,hb j hj⟩ : Fin r) = ⟨a j,h.bound j hj⟩ := Fin.ext (heq j hj).symm
    have hK : (⟨b k,hb k hk⟩ : Fin r) = ⟨a k,h.bound k hk⟩ := Fin.ext (heq k hk).symm
    rw [hJ,hK]
    exact h.sorted j hj k hk hjk
  · intro c
    constructor
    · intro hc
      obtain ⟨j,hj,hjc⟩ := (h.cover c).1 hc
      exact ⟨j,hj,(heq j hj).symm.trans hjc⟩
    · rintro ⟨j,hj,hjc⟩
      exact (h.cover c).2 ⟨j,hj,(heq j hj).trans hjc⟩

private theorem RowData.full_count {n m r q : ℕ} {σ : Profile n m}
    {emb : Fin r ↪ Fin m} {v : Fin n} {a : ℕ → ℕ}
    (h : RowData σ emb v m q a) : q = r := by
  let f : Fin q → Fin r := fun j => ⟨a j.val,h.bound j.val j.isLt⟩
  have hfinj : Function.Injective f := by
    intro j k he
    exact Fin.ext (h.injective j.val j.isLt k.val k.isLt (congrArg Fin.val he))
  have hfsurj : Function.Surjective f := by
    intro c
    obtain ⟨j,hj,hjc⟩ := (h.cover c).1 ((σ v) (emb c)).isLt
    exact ⟨⟨j,hj⟩,Fin.ext hjc⟩
  simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective f ⟨hfinj,hfsurj⟩)

private def A (n m r : ℕ) (v : Fin n) (s : MachineState) (j : ℕ) : ℕ :=
  s.naturalMemory (2*n*m+3*m+v.val*r+j)
private structure Core {n m r : ℕ} (σ : Profile n m) (ε : ℝ)
    (emb : Fin r ↪ Fin m) (s : MachineState) : Prop where
  bases : ProgramBases n m s
  constants : ProgramConstants ε s
  ranks : ProgramRanks σ s
  inverse : ProgramInverse σ s
  keep : ProgramKeep σ s
  count : s.naturals 5 = r
  map : ∀ j, s.naturalMemory (2*n*m+m+j.val) = (emb j).val
  reverse : ∀ j, s.naturalMemory (2*n*m+2*m+(emb j).val) = j.val
private theorem core_frame {n m r : ℕ} (σ : Profile n m) (ε : ℝ) (emb : Fin r ↪ Fin m)
    (s t : MachineState) (hs : Core σ ε emb s) (hb : ProgramBases n m t)
    (hr : t.reals = s.reals) (hmem : t.naturalMemory = s.naturalMemory)
    (hR : t.naturals 5 = s.naturals 5) : Core σ ε emb t := by
  refine ⟨hb,?_,?_,?_,?_,hR.trans hs.count,?_,?_⟩
  · simpa only [ProgramConstants,hr] using hs.constants
  · simpa only [ProgramRanks,hmem] using hs.ranks
  · simpa only [ProgramInverse,hmem] using hs.inverse
  · simpa only [ProgramKeep,hmem] using hs.keep
  · simpa only [hmem] using hs.map
  · simpa only [hmem] using hs.reverse
private def Rows {n m r : ℕ} (σ : Profile n m) (emb : Fin r ↪ Fin m)
    (cut : ℕ) (s : MachineState) : Prop :=
  ∀ v : Fin n, v.val < cut → RowData σ emb v m r (A n m r v s)
private theorem row_address_lt {n m : ℕ} (v : Fin n) (c : Fin m) :
    v.val*m+c.val < n*m := by
  have hh : v.val*m+m ≤ n*m := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right m (Nat.succ_le_of_lt v.isLt)
  omega
private structure InnerInv {n m r : ℕ} (σ : Profile n m) (ε : ℝ)
    (emb : Fin r ↪ Fin m) (v : Fin n) (s : MachineState) : Prop where
  pc : s.pc = 82
  core : Core σ ε emb s
  voter : s.naturals 8 = v.val
  row : s.naturals 10 = v.val*m
  orderRow : s.naturals 25 = 2*n*m+3*m+v.val*r
  bound : s.naturals 9 ≤ m
  rows : Rows σ emb v.val s
  data : RowData σ emb v (s.naturals 9) (s.naturals 16) (A n m r v s)
private structure InnerDone {n m r : ℕ} (σ : Profile n m) (ε : ℝ)
    (emb : Fin r ↪ Fin m) (v : Fin n) (s : MachineState) : Prop where
  pc : s.pc = 96
  core : Core σ ε emb s
  voter : s.naturals 8 = v.val
  row : s.naturals 10 = v.val*m
  orderRow : s.naturals 25 = 2*n*m+3*m+v.val*r
  rows : Rows σ emb v.val s
  data : RowData σ emb v m r (A n m r v s)

private theorem inner_body {n m r : ℕ} (σ : Profile n m) (ε : ℝ)
    (emb : Fin r ↪ Fin m) (hrm : r ≤ m) (hret : Set.range emb = {c | ¬ Dominated σ c})
    (v : Fin n) (s : MachineState) (hs : InnerInv σ ε emb v s) (hi : s.naturals 9 < m) :
    ∃ k t, Runs metricProgram k s t ∧ k ≤ 14 ∧ InnerInv σ ε emb v t ∧
      t.naturals 9 = s.naturals 9+1 := by
  let i : Fin m := ⟨s.naturals 9,hi⟩
  let x := (σ v).symm i
  have hx : ((σ v) x).val = s.naturals 9 := congrArg Fin.val ((σ v).apply_symm_apply i)
  obtain ⟨hN,hM,hZ,hO,hL,hI,hK,hMap,hRev,hOrd,hPB,hTB,hAB,hSB⟩ := hs.core.bases
  have hstop : ¬ m ≤ s.naturals 9 := by omega
  have hread : s.naturalMemory (n*m+v.val*m+s.naturals 9) = x.val := by
    have hh := hs.core.inverse v x
    rw [hx] at hh
    exact hh
  by_cases hdom : Dominated σ x
  · have hkeep : s.naturalMemory (2*n*m+x.val) = 0 := by
      simpa only [if_pos hdom] using hs.core.keep x
    let t := chargedReplay 9 s
    have htRun : Runs metricProgram 9 s t := by
      apply chargedReplay_trace
      intro j hj
      interval_cases j <;>
        simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep]
    have htBase : ProgramBases n m t := by
      simpa [ProgramBases,t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep] using hs.core.bases
    have htR : t.reals = s.reals := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep]
    have htMem : t.naturalMemory = s.naturalMemory := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep]
    have hR : t.naturals 5 = s.naturals 5 := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep]
    have htCore := core_frame σ ε emb s t hs.core htBase htR htMem hR
    have hInew : t.naturals 9 = s.naturals 9+1 := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hO,hI,hK,hstop,hs.row,hread,hkeep]
    have hQnew : t.naturals 16 = s.naturals 16 := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep]
    have hxmissing : x ∉ Set.range emb := by rw [hret]; exact fun h => h hdom
    have htData : RowData σ emb v (t.naturals 9) (t.naturals 16) (A n m r v t) := by
      rw [hInew,hQnew]
      apply (hs.data.skip hx hxmissing).congr
      intro j hj
      unfold A
      rw [htMem]
    refine ⟨9,t,htRun,by norm_num,⟨?_,htCore,?_,?_,?_,?_,?_,htData⟩,hInew⟩
    · simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep]
    · simpa [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep] using hs.voter
    · simpa [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep] using hs.row
    · simpa [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep] using hs.orderRow
    · rw [hInew]
      omega
    · intro u hu
      apply (hs.rows u hu).congr
      intro j hj
      unfold A
      rw [htMem]
  · have hkeep : s.naturalMemory (2*n*m+x.val) = 1 := by
      simpa only [if_neg hdom] using hs.core.keep x
    have hxrange : x ∈ Set.range emb := by rw [hret]; exact hdom
    obtain ⟨c,hcx⟩ := hxrange
    have hcRank : ((σ v) (emb c)).val = s.naturals 9 := by rw [hcx]; exact hx
    have hrev : s.naturalMemory (2*n*m+2*m+x.val) = c.val := by
      simpa only [hcx] using hs.core.reverse c
    let t := chargedReplay 14 s
    let w := 2*n*m+3*m+v.val*r+s.naturals 16
    have htRun : Runs metricProgram 14 s t := by
      apply chargedReplay_trace
      intro j hj
      interval_cases j <;>
        simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep]
    have htBase : ProgramBases n m t := by
      simpa [ProgramBases,t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep] using hs.core.bases
    have htR : t.reals = s.reals := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep]
    have hInew : t.naturals 9 = s.naturals 9+1 := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hO,hI,hK,hstop,hs.row,hread,hkeep]
    have hQnew : t.naturals 16 = s.naturals 16+1 := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hO,hI,hK,hstop,hs.row,hread,hkeep]
    have htCount : t.naturals 5 = r := by
      simpa [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep] using hs.core.count
    have htMem : t.naturalMemory = Function.update s.naturalMemory w c.val := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hRev,hstop,hs.row,hs.orderRow,hread,hkeep,hrev,w]
    have hUntouched (a : ℕ) (ha : a < 2*n*m+3*m) : t.naturalMemory a = s.naturalMemory a := by
      rw [htMem,Function.update_of_ne (by dsimp [w]; omega : a ≠ w)]
    have hdouble : 2*n*m = n*m+n*m := by ring
    have htCore : Core σ ε emb t := by
      refine ⟨htBase,?_,?_,?_,?_,htCount,?_,?_⟩
      · have transport {a b : MachineState} (he : a.reals = b.reals)
            (hc : ProgramConstants ε b) : ProgramConstants ε a := by
          unfold ProgramConstants at hc ⊢
          rw [he]
          exact hc
        exact transport htR hs.core.constants
      · intro u d
        rw [hUntouched _ (by have hh := row_address_lt u d; rw [hdouble]; omega)]
        exact hs.core.ranks u d
      · intro u d
        rw [hUntouched _ (by have hh := row_address_lt u ((σ u) d); rw [hdouble]; omega)]
        exact hs.core.inverse u d
      · intro d
        rw [hUntouched _ (by omega)]
        exact hs.core.keep d
      · intro j
        rw [hUntouched _ (by have := j.isLt; omega)]
        exact hs.core.map j
      · intro j
        rw [hUntouched _ (by have := (emb j).isLt; omega)]
        exact hs.core.reverse j
    have hArray (j : ℕ) : A n m r v t j = if j = s.naturals 16 then c.val else A n m r v s j := by
      unfold A
      rw [htMem]
      by_cases heq : j = s.naturals 16
      · subst j
        simp [w]
      · rw [Function.update_of_ne (by dsimp [w]; omega : 2*n*m+3*m+v.val*r+j ≠ w),if_neg heq]
    have htData : RowData σ emb v (t.naturals 9) (t.naturals 16) (A n m r v t) := by
      rw [hInew,hQnew]
      apply (hs.data.keep c hcRank).congr
      intro j hj
      exact (hArray j).symm
    have htRows : Rows σ emb v.val t := by
      intro u hu
      apply (hs.rows u hu).congr
      intro j hj
      have hsmall : u.val*r+j < v.val*r := row_address_lt (n := v.val) ⟨u.val,hu⟩ ⟨j,hj⟩
      unfold A
      rw [htMem,Function.update_of_ne (by dsimp [w]; omega : 2*n*m+3*m+u.val*r+j ≠ w)]
    refine ⟨14,t,htRun,le_rfl,⟨?_,htCore,?_,?_,?_,?_,htRows,htData⟩,hInew⟩
    · simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep]
    · simpa [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep] using hs.voter
    · simpa [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep] using hs.row
    · simpa [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hI,hK,hstop,hs.row,hread,hkeep] using hs.orderRow
    · rw [hInew]
      omega

private theorem inner_loop (hloop : Computation_RunRules.Statement)
    {n m r : ℕ} (σ : Profile n m) (ε : ℝ) (emb : Fin r ↪ Fin m)
    (hrm : r ≤ m) (hret : Set.range emb = {c | ¬ Dominated σ c})
    (v : Fin n) (s : MachineState) (hs : InnerInv σ ε emb v s) :
    ∃ k t, Runs metricProgram k s t ∧ InnerDone σ ε emb v t ∧
      k ≤ 14*(m-s.naturals 9+1) := by
  apply hloop.2 metricProgram (InnerInv σ ε emb v) (InnerDone σ ε emb v)
    (fun u => m-u.naturals 9) 14 ?_ s hs
  intro u hu
  have hM : u.naturals 1 = m := hu.core.bases.2.1
  by_cases hstop : m ≤ u.naturals 9
  · have heq : u.naturals 9 = m := le_antisymm hu.bound hstop
    let t : MachineState := {u with pc := 96}
    have hstep : step metricProgram u = some t := by simp [step,metricProgram,hu.pc,hM,hstop,t]
    have hcore : Core σ ε emb t :=
      ⟨hu.core.bases,hu.core.constants,hu.core.ranks,hu.core.inverse,hu.core.keep,
        hu.core.count,hu.core.map,hu.core.reverse⟩
    have hdata : RowData σ emb v m (u.naturals 16) (A n m r v u) := by
      simpa only [heq] using hu.data
    have hqeq : u.naturals 16 = r := hdata.full_count
    have htData : RowData σ emb v m r (A n m r v t) := by
      have hd : RowData σ emb v m r (A n m r v u) := by simpa only [hqeq] using hdata
      apply hd.congr
      intro j hj
      rfl
    refine ⟨1,t,Runs.succ hstep (Runs.zero t),by norm_num,Or.inl ?_⟩
    exact ⟨rfl,hcore,hu.voter,hu.row,hu.orderRow,hu.rows,htData⟩
  · have hgo : u.naturals 9 < m := Nat.lt_of_not_ge hstop
    obtain ⟨k,t,ht,hcost,hinv,hinc⟩ := inner_body σ ε emb hrm hret v u hu hgo
    refine ⟨k,t,ht,hcost,Or.inr ⟨hinv,?_⟩⟩
    change m-t.naturals 9 < m-u.naturals 9
    rw [hinc]
    omega

private structure OuterInv {n m r : ℕ} (σ : Profile n m) (ε : ℝ)
    (emb : Fin r ↪ Fin m) (s : MachineState) : Prop where
  pc : s.pc = 79
  core : Core σ ε emb s
  bound : s.naturals 8 ≤ n
  row : s.naturals 10 = s.naturals 8*m
  orderRow : s.naturals 25 = 2*n*m+3*m+s.naturals 8*r
  rows : Rows σ emb (s.naturals 8) s
private structure OuterDone {n m r : ℕ} (σ : Profile n m) (ε : ℝ)
    (emb : Fin r ↪ Fin m) (s : MachineState) : Prop where
  pc : s.pc = 100
  core : Core σ ε emb s
  rows : Rows σ emb n s

private theorem outer_body (hloop : Computation_RunRules.Statement)
    {n m r : ℕ} (σ : Profile n m) (ε : ℝ) (emb : Fin r ↪ Fin m)
    (hrm : r ≤ m) (hret : Set.range emb = {c | ¬ Dominated σ c})
    (s : MachineState) (hs : OuterInv σ ε emb s) (hv : s.naturals 8 < n) :
    ∃ k t, Runs metricProgram k s t ∧ k ≤ 14*(m+1)+7 ∧
      OuterInv σ ε emb t ∧ t.naturals 8 = s.naturals 8+1 := by
  let v : Fin n := ⟨s.naturals 8,hv⟩
  let u := chargedReplay 3 s
  have hN : s.naturals 0 = n := hs.core.bases.1
  have hstop : ¬ n ≤ s.naturals 8 := by omega
  have huRun : Runs metricProgram 3 s u := by
    apply chargedReplay_trace
    intro j hj
    interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop]
  have huBase : ProgramBases n m u := by
    simpa [ProgramBases,u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop] using hs.core.bases
  have huR : u.reals = s.reals := by simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop]
  have huMem : u.naturalMemory = s.naturalMemory := by simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop]
  have huCount : u.naturals 5 = s.naturals 5 := by simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop]
  have huCore := core_frame σ ε emb s u hs.core huBase huR huMem huCount
  have hI0 : u.naturals 9 = 0 := by simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop]
  have hQ0 : u.naturals 16 = 0 := by simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop]
  have huInv : InnerInv σ ε emb v u := by
    refine ⟨?_,huCore,?_,?_,?_,?_,?_,?_⟩
    · simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop]
    · simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop,v]
    · simpa [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop,v] using hs.row
    · simpa [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hN,hstop,v] using hs.orderRow
    · rw [hI0]
      omega
    · intro w hw
      apply (hs.rows w hw).congr
      intro j hj
      unfold A
      rw [huMem]
    · rw [hI0,hQ0]
      refine ⟨by omega,le_rfl,?_,?_,?_,?_⟩
      · intro j hj
        omega
      · intro j hj
        omega
      · intro j hj
        omega
      · intro c
        constructor
        · intro hc
          omega
        · rintro ⟨j,hj,hjc⟩
          omega
  obtain ⟨ki,q,hqi,hq,hqcost⟩ := inner_loop hloop σ ε emb hrm hret v u huInv
  have hqcost' : ki ≤ 14*(m+1) := by simpa only [hI0,Nat.sub_zero] using hqcost
  let t := chargedReplay 4 q
  have hM : q.naturals 1 = m := hq.core.bases.2.1
  have hO : q.naturals 3 = 1 := hq.core.bases.2.2.2.1
  have htRun : Runs metricProgram 4 q t := by
    apply chargedReplay_trace
    intro j hj
    interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hq.pc]
  have htBase : ProgramBases n m t := by
    simpa [ProgramBases,t,chargedReplay,chargedTick,step,metricProgram,hq.pc] using hq.core.bases
  have htR : t.reals = q.reals := by simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc]
  have htMem : t.naturalMemory = q.naturalMemory := by simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc]
  have htCount : t.naturals 5 = q.naturals 5 := by simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc]
  have htCore := core_frame σ ε emb q t hq.core htBase htR htMem htCount
  have hV : t.naturals 8 = s.naturals 8+1 := by
    simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc,hO,hq.voter,v]
  have ht : OuterInv σ ε emb t := by
    refine ⟨?_,htCore,?_,?_,?_,?_⟩
    · simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc]
    · rw [hV]
      omega
    · simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc,hM,hO,hq.voter,hq.row,Nat.add_mul]
    · simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc,hM,hO,hq.core.count,
        hq.voter,hq.orderRow,Nat.add_mul,Nat.add_assoc]
    · intro w hw
      have hw' : w.val < v.val+1 := by simpa [hV,v] using hw
      by_cases heq : w.val = v.val
      · have hwv : w = v := Fin.ext heq
        subst w
        apply hq.data.congr
        intro j hj
        unfold A
        rw [htMem]
      · have hprev : w.val < v.val := by omega
        apply (hq.rows w hprev).congr
        intro j hj
        unfold A
        rw [htMem]
  have hr1 := hloop.1 metricProgram 3 ki s u q huRun hqi
  refine ⟨3+ki+4,t,hloop.1 metricProgram (3+ki) 4 s q t hr1 htRun,by omega,ht,hV⟩

private theorem outer_loop (hloop : Computation_RunRules.Statement)
    {n m r : ℕ} (σ : Profile n m) (ε : ℝ) (emb : Fin r ↪ Fin m)
    (hrm : r ≤ m) (hret : Set.range emb = {c | ¬ Dominated σ c})
    (s : MachineState) (hs : OuterInv σ ε emb s) :
    ∃ k t, Runs metricProgram k s t ∧ OuterDone σ ε emb t ∧
      k ≤ (14*(m+1)+7)*(n-s.naturals 8)+1 := by
  have loop : ∀ d : ℕ, ∀ u, n-u.naturals 8 = d → OuterInv σ ε emb u →
      ∃ k t, Runs metricProgram k u t ∧ OuterDone σ ε emb t ∧
        k ≤ (14*(m+1)+7)*d+1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro u hrem hu
      have hN : u.naturals 0 = n := hu.core.bases.1
      by_cases hstop : n ≤ u.naturals 8
      · have heq : u.naturals 8 = n := le_antisymm hu.bound hstop
        let t : MachineState := {u with pc := 100}
        have hstep : step metricProgram u = some t := by simp [step,metricProgram,hu.pc,hN,hstop,t]
        have hc : Core σ ε emb t :=
          ⟨hu.core.bases,hu.core.constants,hu.core.ranks,hu.core.inverse,hu.core.keep,
            hu.core.count,hu.core.map,hu.core.reverse⟩
        have hrows : Rows σ emb n t := by
          intro v hv
          apply (hu.rows v (by rw [heq]; exact hv)).congr
          intro j hj
          rfl
        exact ⟨1,t,Runs.succ hstep (Runs.zero t),⟨rfl,hc,hrows⟩,by omega⟩
      · have hgo : u.naturals 8 < n := Nat.lt_of_not_ge hstop
        obtain ⟨k,v,hk,hcost,hv,hinc⟩ := outer_body hloop σ ε emb hrm hret u hu hgo
        have hlt : n-v.naturals 8 < d := by rw [hinc]; omega
        obtain ⟨l,t,hl,ht,hlcost⟩ := ih (n-v.naturals 8) hlt v rfl hv
        refine ⟨k+l,t,hloop.1 metricProgram k l u v t hk hl,ht,?_⟩
        have heq : n-v.naturals 8+1 = d := by rw [hinc]; omega
        nlinarith
  exact loop (n-s.naturals 8) s rfl hs

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ ε r s hpc hb hc hranks hinverse hkeep hmaps
  obtain ⟨hCount,hr,hrm,hBound,hInj,hCover,hRev⟩ := hmaps
  let emb : Fin r ↪ Fin m :=
    {toFun := fun j => ⟨s.naturalMemory (2*n*m+m+j.val),hBound j⟩
     inj' := by intro i j he; exact hInj (congrArg Fin.val he)}
  have hret : Set.range emb = {c | ¬ Dominated σ c} := by
    ext c
    constructor
    · rintro ⟨j,rfl⟩
      exact (hCover (emb j)).2 ⟨j,rfl⟩
    · intro hretc
      obtain ⟨j,hj⟩ := (hCover c).1 hretc
      exact ⟨j,Fin.ext hj⟩
  have hcore : Core σ ε emb s := ⟨hb,hc,hranks,hinverse,hkeep,hCount,fun _ => rfl,hRev⟩
  let u := chargedReplay 3 s
  have huRun : Runs metricProgram 3 s u := by
    apply chargedReplay_trace
    intro j hj
    interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hpc]
  have huBase : ProgramBases n m u := by
    simpa [ProgramBases,u,chargedReplay,chargedTick,step,metricProgram,hpc] using hb
  have huR : u.reals = s.reals := by simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
  have huMem : u.naturalMemory = s.naturalMemory := by simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
  have huCount : u.naturals 5 = s.naturals 5 := by simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
  have huCore := core_frame σ ε emb s u hcore huBase huR huMem huCount
  have hV0 : u.naturals 8 = 0 := by simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
  obtain ⟨hN,hM,hZ,hO,hL,hI,hK,hMap,hReverse,hOrd,hPB,hTB,hAB,hSB⟩ := hb
  have hu : OuterInv σ ε emb u := by
    refine ⟨?_,huCore,?_,?_,?_,?_⟩
    · simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
    · rw [hV0]
      omega
    · simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
    · simp [u,chargedReplay,chargedTick,step,metricProgram,hpc,hOrd,hZ]
    · intro v hv
      rw [hV0] at hv
      omega
  obtain ⟨k,t,hk,ht,hcost⟩ := outer_loop h.child_0 σ ε emb hrm hret u hu
  let inv (v : Fin n) : Equiv.Perm (Fin r) := by
    let f : Fin r → Fin r := fun j => ⟨A n m r v t j.val,(ht.rows v v.isLt).bound j.val j.isLt⟩
    have hf : Function.Injective f := by
      intro j k he
      exact Fin.ext ((ht.rows v v.isLt).injective j.val j.isLt k.val k.isLt (congrArg Fin.val he))
    exact Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩
  have hinv (v : Fin n) (j : Fin r) : (inv v j).val = A n m r v t j.val := rfl
  have hsorted (v : Fin n) : StrictMono (fun j => (σ v) (emb (inv v j))) := by
    intro j k hjk
    exact (ht.rows v v.isLt).sorted j.val j.isLt k.val k.isLt hjk
  let R : Reduction σ :=
    {count := r
     count_pos := hr
     embed := emb
     profile := fun v => (inv v).symm
     preserves := by
       intro v a b
       have hh := (hsorted v).lt_iff_lt (a := (inv v).symm b) (b := (inv v).symm a)
       simpa only [prefers,(inv v).apply_symm_apply] using hh.symm
     range_eq := hret}
  have hlayout : ProgramLayout n m R.count t := by
    obtain ⟨hN,hM,hZ,hO,hL,hI,hK,hMap,hReverse,hOrd,hPB,hTB,hAB,hSB⟩ := ht.core.bases
    exact ⟨hN,hM,hZ,hO,hL,ht.core.count,hI,hK,hMap,hReverse,hOrd,hPB,hTB,hAB,hSB⟩
  have hmemory : ProgramReductionMemory R t := by
    refine ⟨ht.core.keep,ht.core.map,ht.core.reverse,?_⟩
    intro v j
    change A n m r v t j.val = (inv v j).val
    exact (hinv v j).symm
  have hpre : ProgramPreprocessed σ ε R t := ⟨ht.pc,hrm,hlayout,ht.core.constants,hmemory⟩
  refine ⟨R,3+k,t,h.child_0.1 metricProgram 3 k s u t huRun hk,rfl,hpre,?_⟩
  have hcost' : k ≤ (14*(m+1)+7)*n+1 := by simpa only [hV0,Nat.sub_zero] using hcost
  have hNM : 2*n ≤ n*m := by nlinarith [Nat.mul_le_mul_left n hm]
  nlinarith

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramRanking
