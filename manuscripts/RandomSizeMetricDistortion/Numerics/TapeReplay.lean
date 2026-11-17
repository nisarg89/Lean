import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_TapeReplay
set_option maxHeartbeats 8000000

private def Contains (I : QInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)
private def RowSound (B : Box) (e : PolyExpr) (row : TapeBounds) : Prop :=
  ∀ x, inBox B x → Contains row.value (eval e x) ∧
    ∀ i, Contains (row.gradient i) (eval (derivative i e) x)

private theorem binary_box {A C : QInterval} {a c : ℝ} (ha : Contains A a) (hc : Contains C c) :
    ValidBox (![A,C,⟨0,0⟩,⟨0,0⟩] : Box) ∧
      inBox (![A,C,⟨0,0⟩,⟨0,0⟩] : Box) ![a,c,0,0] := by
  constructor
  · intro i
    fin_cases i
    · change A.lo ≤ A.hi
      exact_mod_cast ha.1.trans ha.2
    · change C.lo ≤ C.hi
      exact_mod_cast hc.1.trans hc.2
    · norm_num
    · norm_num
  · intro i
    fin_cases i
    · exact ha
    · exact hc
    · norm_num
    · norm_num

private theorem add_sound (h : Needs) {A C : QInterval} {a c : ℝ}
    (ha : Contains A a) (hc : Contains C c) : Contains (intervalAdd A C) (a+c) := by
  have hb := binary_box ha hc
  simpa only [Contains,intervalEval,eval,Matrix.cons_val_zero,Matrix.cons_val_one,mem_Icc] using
    h.child_1 (.add (.var 0) (.var 1)) _ hb.1 _ hb.2

private theorem mul_sound (h : Needs) {A C : QInterval} {a c : ℝ}
    (ha : Contains A a) (hc : Contains C c) : Contains (intervalMul A C) (a*c) := by
  have hb := binary_box ha hc
  simpa only [Contains,intervalEval,eval,Matrix.cons_val_zero,Matrix.cons_val_one,mem_Icc] using
    h.child_1 (.mul (.var 0) (.var 1)) _ hb.1 _ hb.2

private theorem neg_sound (h : Needs) {A : QInterval} {a : ℝ}
    (ha : Contains A a) : Contains (intervalNeg A) (-a) := by
  have hb := binary_box ha (show Contains ⟨0,0⟩ (0 : ℝ) from by norm_num [Contains])
  simpa only [Contains,intervalEval,eval,Matrix.cons_val_zero,mem_Icc] using
    h.child_1 (.neg (.var 0)) _ hb.1 _ hb.2

private theorem enlarge {outer inner : QInterval} {v : ℝ}
    (he : intervalEncloses outer inner = true) (hi : Contains inner v) : Contains outer v := by
  have hb : outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi := of_decide_eq_true he
  have h0 : (outer.lo : ℝ) ≤ inner.lo := by exact_mod_cast hb.1
  have h1 : (inner.hi : ℝ) ≤ outer.hi := by exact_mod_cast hb.2
  exact ⟨h0.trans hi.1,hi.2.trans h1⟩

private theorem row_enlarge {B : Box} {e : PolyExpr} {outer inner : TapeBounds}
    (he : tapeBoundsEnclose outer inner = true) (hi : RowSound B e inner) : RowSound B e outer := by
  have hb : intervalEncloses outer.value inner.value = true ∧
      (List.finRange 4).all (fun i => intervalEncloses (outer.gradient i) (inner.gradient i)) = true := by
    simpa only [tapeBoundsEnclose,Bool.and_eq_true_iff] using he
  intro x hx
  have hv := hi x hx
  refine ⟨enlarge hb.1 hv.1,?_⟩
  intro i
  have hg := List.all_eq_true.mp hb.2 i (by simp)
  exact enlarge hg (hv.2 i)

private theorem history_get {B : Box} {es : List PolyExpr} {done : List TapeBounds}
    (hh : List.Forall₂ (RowSound B) es done) (i : ℕ) (hi : i < es.length) :
    RowSound B (es.getD i (.const 0)) (done.getD i zeroTapeBounds) := by
  have hi' : i < done.length := by simpa only [← hh.length_eq] using hi
  rw [List.getD_eq_get es (.const 0) ⟨i,hi⟩,
    List.getD_eq_get done zeroTapeBounds ⟨i,hi'⟩]
  exact hh.get hi hi'

private theorem expected_sound (h : Needs) {B : Box} {es : List PolyExpr} {done : List TapeBounds}
    (hB : ValidBox B) (hh : List.Forall₂ (RowSound B) es done) (op : TapeOp)
    (href : tapeRefsValid done.length op = true) :
    RowSound B (tapeCompileStep es op) (tapeExpected B done op) := by
  cases op with
  | const q =>
    intro x hx
    constructor
    · simp [Contains,tapeCompileStep,tapeExpected,eval]
    · intro i; simp [Contains,tapeCompileStep,tapeExpected,derivative,eval]
  | var v =>
    intro x hx
    constructor
    · exact hx v
    · intro i
      by_cases hi : v = i
      · subst i; simp [Contains,tapeCompileStep,tapeExpected,derivative,eval]
      · simp [Contains,tapeCompileStep,tapeExpected,derivative,eval,hi,Ne.symm hi]
  | add a b =>
    have hab : a < done.length ∧ b < done.length := of_decide_eq_true href
    have ha := history_get hh a (by simpa only [hh.length_eq] using hab.1)
    have hb := history_get hh b (by simpa only [hh.length_eq] using hab.2)
    intro x hx
    have hva := ha x hx; have hvb := hb x hx
    refine ⟨?_,?_⟩
    · exact add_sound h hva.1 hvb.1
    · intro i
      exact add_sound h (hva.2 i) (hvb.2 i)
  | mul a b =>
    have hab : a < done.length ∧ b < done.length := of_decide_eq_true href
    have ha := history_get hh a (by simpa only [hh.length_eq] using hab.1)
    have hb := history_get hh b (by simpa only [hh.length_eq] using hab.2)
    intro x hx
    have hva := ha x hx; have hvb := hb x hx
    refine ⟨?_,?_⟩
    · exact mul_sound h hva.1 hvb.1
    · intro i
      exact add_sound h (mul_sound h (hva.2 i) hvb.1) (mul_sound h hva.1 (hvb.2 i))
  | neg a =>
    have hab : a < done.length := of_decide_eq_true href
    have ha := history_get hh a (by simpa only [hh.length_eq] using hab)
    intro x hx
    have hva := ha x hx
    refine ⟨?_,?_⟩
    · exact neg_sound h hva.1
    · intro i; exact neg_sound h (hva.2 i)

private theorem tapeCheck_sound (h : Needs) {B : Box} (hB : ValidBox B)
    (ops : List TapeOp) (es : List PolyExpr) (done rows : List TapeBounds)
    (hh : List.Forall₂ (RowSound B) es done) (hc : tapeCheckAux B done ops rows = true) :
    List.Forall₂ (RowSound B)
      (ops.foldl (fun es op => es ++ [tapeCompileStep es op]) es) (done++rows) := by
  induction ops generalizing es done rows with
  | nil =>
    cases rows with
    | nil => simpa using hh
    | cons row rows => simp [tapeCheckAux] at hc
  | cons op ops ih =>
    cases rows with
    | nil => simp [tapeCheckAux] at hc
    | cons row rows =>
      have hb : tapeRefsValid done.length op = true ∧
          tapeBoundsEnclose row (tapeExpected B done op) = true ∧
          tapeCheckAux B (done++[row]) ops rows = true := by
        simpa only [tapeCheckAux,Bool.and_eq_true_iff,and_assoc] using hc
      have hrow := row_enlarge hb.2.1 (expected_sound h hB hh op hb.1)
      have hh' := List.rel_append hh (List.Forall₂.cons hrow List.Forall₂.nil)
      have ht := ih (es++[tapeCompileStep es op]) (done++[row]) rows hh' hb.2.2
      simpa only [List.foldl_cons,List.append_assoc,List.singleton_append] using ht

private theorem compile_length (ops : List TapeOp) (es : List PolyExpr) :
    (ops.foldl (fun es op => es ++ [tapeCompileStep es op]) es).length = es.length+ops.length := by
  induction ops generalizing es with
  | nil => simp
  | cons op ops ih =>
    rw [List.foldl_cons,ih]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem root_sound (h : Needs) {B : Box} (hB : ValidBox B)
    (tape : List TapeOp) (root : ℕ) (rows : List TapeBounds)
    (hr : root < tape.length) (hc : tapeCheck B tape rows = true) :
    RowSound B (tapeExpr tape root) (rows.getD root zeroTapeBounds) := by
  have hh := tapeCheck_sound h hB tape [] [] rows List.Forall₂.nil hc
  have hlen : (tapeCompile tape).length = tape.length := by
    simpa [tapeCompile] using compile_length tape []
  have hh' : List.Forall₂ (RowSound B) (tapeCompile tape) rows := by
    simpa [tapeCompile] using hh
  exact history_get hh' root (by rwa [hlen])

private theorem update_in_box {B : Box} {y : Fin 4 → ℝ} (hy : inBox B y)
    (i : Fin 4) (t : ℝ) (ht : t ∈ Icc ((B i).lo : ℝ) ((B i).hi : ℝ)) :
    inBox B (Function.update y i t) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using ht
  · simpa [Function.update_of_ne hji] using hy j

private theorem centered_upper (h : Needs) (e : PolyExpr) (B : Box) (G : Fin 4 → QInterval)
    (upper : ℚ) (hB : ValidBox B)
    (hgrad : ∀ x, inBox B x → ∀ i, Contains (G i) (eval (derivative i e) x))
    (hmid : eval e (fun i => ((((B i).lo+(B i).hi)/2 : ℚ) : ℝ)) ≤ (upper : ℝ))
    (x : Fin 4 → ℝ) (hx : inBox B x) :
    eval e x ≤ ((upper+∑ i, max |(G i).lo| |(G i).hi| * ((B i).hi-(B i).lo)/2 : ℚ) : ℝ) := by
  let c : Fin 4 → ℝ := fun i => (((B i).lo+(B i).hi)/2 : ℚ)
  let r : Fin 4 → ℝ := fun i => (((B i).hi : ℝ)-(B i).lo)/2
  let C : Fin 4 → ℝ := fun i =>
    max |((G i).lo : ℝ)| |((G i).hi : ℝ)|
  have hc : inBox B c := by
    intro i
    have hle : ((B i).lo : ℝ) ≤ (B i).hi := by exact_mod_cast hB i
    dsimp [c]
    push_cast
    constructor <;> linarith
  have hC : ∀ i, 0 ≤ C i := by
    intro i
    exact (abs_nonneg _).trans (le_max_left _ _)
  have step_bound : ∀ y : Fin 4 → ℝ, inBox B y → ∀ i : Fin 4, y i = c i →
      eval e (Function.update y i (x i)) ≤ eval e y+C i*r i := by
    intro y hy i hmid
    let f : ℝ → ℝ := fun t => eval e (Function.update y i t)
    let g : ℝ → ℝ := fun t => eval (derivative i e) (Function.update y i t)
    have hd : ∀ t, HasDerivAt f (g t) t := by
      intro t
      simpa only [Function.update_self,Function.update_idem] using
        h.child_0 e i (Function.update y i t)
    have hg : ∀ t ∈ Icc ((B i).lo : ℝ) ((B i).hi : ℝ), ‖g t‖ ≤ C i := by
      intro t ht
      have ht' := hgrad _ (update_in_box hy i t ht) i
      rw [Real.norm_eq_abs,abs_le]
      constructor
      · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans ht'.1)
      · exact ht'.2.trans ((le_abs_self _).trans (le_max_right _ _))
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hd t).hasDerivWithinAt) hg
        (convex_Icc ((B i).lo : ℝ) ((B i).hi : ℝ)) (hc i) (hx i)
    have hdist : ‖x i-c i‖ ≤ r i := by
      rw [Real.norm_eq_abs,abs_le]
      dsimp [c,r]
      push_cast
      constructor <;> linarith [(hx i).1,(hx i).2]
    have hnorm : f (x i)-f (c i) ≤ C i*‖x i-c i‖ :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hmvt)
    have hdiff : f (x i)-f (c i) ≤ C i*r i :=
      hnorm.trans (mul_le_mul_of_nonneg_left hdist (hC i))
    have hbase : f (c i) = eval e y := by
      dsimp [f]
      rw [← hmid,Function.update_eq_self]
    have hfinal : f (x i) ≤ f (c i)+C i*r i := by linarith
    rw [hbase] at hfinal
    exact hfinal
  let y1 := Function.update c (0 : Fin 4) (x 0)
  let y2 := Function.update y1 (1 : Fin 4) (x 1)
  let y3 := Function.update y2 (2 : Fin 4) (x 2)
  let y4 := Function.update y3 (3 : Fin 4) (x 3)
  have hy1 : inBox B y1 := update_in_box hc 0 (x 0) (hx 0)
  have hy2 : inBox B y2 := update_in_box hy1 1 (x 1) (hx 1)
  have hy3 : inBox B y3 := update_in_box hy2 2 (x 2) (hx 2)
  have h0 : eval e y1 ≤ eval e c+C 0*r 0 := step_bound c hc 0 rfl
  have h1 : eval e y2 ≤ eval e y1+C 1*r 1 := by
    apply step_bound y1 hy1 1
    simp [y1]
  have h2 : eval e y3 ≤ eval e y2+C 2*r 2 := by
    apply step_bound y2 hy2 2
    simp [y2,y1]
  have h3 : eval e y4 ≤ eval e y3+C 3*r 3 := by
    apply step_bound y3 hy3 3
    simp [y3,y2,y1]
  have hy4 : y4 = x := by
    ext i
    fin_cases i <;> simp [y4,y3,y2,y1]
  have hsum : ((upper+∑ i, max |(G i).lo| |(G i).hi| * ((B i).hi-(B i).lo)/2 : ℚ) : ℝ) =
      (upper : ℝ)+(C 0*r 0+C 1*r 1+C 2*r 2+C 3*r 3) := by
    simp [Fin.sum_univ_succ,C,r,Rat.cast_max,Rat.cast_abs] <;> ring
  rw [hsum]
  rw [hy4] at h3
  have hcenter : eval e c ≤ (upper : ℝ) := hmid
  linarith


private theorem slice_derivative (hd : Numerics_DerivativeBounds.Statement)
    (e : PolyExpr) (i : Fin 4) (x : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (fun u => eval e (Function.update x i u))
      (eval (derivative i e) (Function.update x i t)) t := by
  simpa only [Function.update_self,Function.update_idem] using hd e i (Function.update x i t)

private theorem slice_in_box {B : Box} {x : Fin 4 → ℝ} (hx : inBox B x)
    (i : Fin 4) (t : ℝ) (ht : t ∈ Icc ((B i).lo : ℝ) ((B i).hi : ℝ)) :
    inBox B (Function.update x i t) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using ht
  · simpa [Function.update_of_ne hji] using hx j

private theorem face_bound (h : Needs) (e : PolyExpr) (B : Box) (i : Fin 4)
    (upper : Bool) (G : Fin 4 → QInterval) (hB : ValidBox B)
    (hG : ∀ x, inBox B x → ∀ j, Contains (G j) (eval (derivative j e) x))
    (hsign : if upper then 0 ≤ (G i).lo else (G i).hi ≤ 0)
    (hface : ∀ x, inBox (faceBox B i upper) x → eval e x ≤ 0)
    (x : Fin 4 → ℝ) (hx : inBox B x) : eval e x ≤ 0 := by
  let L : ℝ := (B i).lo
  let U : ℝ := (B i).hi
  let f : ℝ → ℝ := fun t => eval e (Function.update x i t)
  let g : ℝ → ℝ := fun t => eval (derivative i e) (Function.update x i t)
  have hd : ∀ t, HasDerivAt f (g t) t := fun t => slice_derivative h.child_0 e i x t
  have hcont : ContinuousOn f (Icc L U) :=
    (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn
  have hdiff : DifferentiableOn ℝ f (interior (Icc L U)) :=
    fun t _ => (hd t).differentiableAt.differentiableWithinAt
  have hLU : L ≤ U := by
    change ((B i).lo : ℝ) ≤ ((B i).hi : ℝ)
    exact_mod_cast hB i
  have hgrad : ∀ t ∈ Icc L U,
      g t ∈ Icc ((G i).lo : ℝ)
        ((G i).hi : ℝ) := by
    intro t ht
    exact hG _ (slice_in_box hx i t ht) i
  have hxi : x i ∈ Icc L U := hx i
  cases upper
  · have hs : ((G i).hi : ℝ) ≤ 0 := by exact_mod_cast hsign
    have hanti : AntitoneOn f (Icc L U) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc L U) hcont hdiff
      intro t ht
      rw [(hd t).deriv]
      exact (hgrad t (interior_subset ht)).2.trans hs
    have hle : f (x i) ≤ f L := hanti ⟨le_rfl,hLU⟩ hxi hxi.1
    have hb : eval e (Function.update x i L) ≤ 0 := by
      apply hface
      intro j
      by_cases hji : j = i
      · subst j
        simp [faceBox,L]
      · simpa [faceBox,Function.update_of_ne hji] using hx j
    simpa [f,Function.update_eq_self] using hle.trans hb
  · have hs : 0 ≤ ((G i).lo : ℝ) := by exact_mod_cast hsign
    have hmono : MonotoneOn f (Icc L U) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc L U) hcont hdiff
      intro t ht
      rw [(hd t).deriv]
      exact hs.trans (hgrad t (interior_subset ht)).1
    have hle : f (x i) ≤ f U := hmono hxi ⟨hLU,le_rfl⟩ hxi.2
    have hb : eval e (Function.update x i U) ≤ 0 := by
      apply hface
      intro j
      by_cases hji : j = i
      · subst j
        simp [faceBox,U]
      · simpa [faceBox,Function.update_of_ne hji] using hx j
    simpa [f,Function.update_eq_self] using hle.trans hb


private theorem valid_face {B : Box} (hB : ValidBox B) (i : Fin 4) (upper : Bool) :
    ValidBox (faceBox B i upper) := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [faceBox]
  · simpa [faceBox,Function.update_of_ne hji] using hB j

private theorem valid_split {B : Box} (hB : ValidBox B) (i : Fin 4) (q : ℚ)
    (hq : (B i).lo ≤ q ∧ q ≤ (B i).hi) (right : Bool) :
    ValidBox (splitBox B i q right) := by
  intro j
  by_cases hji : j = i
  · subst j
    cases right
    · simpa [splitBox] using hq.1
    · simpa [splitBox] using hq.2
  · simpa [splitBox,Function.update_of_ne hji] using hB j

theorem from_children (h : Needs) : Statement := by
  intro tape root B tree
  induction tree generalizing B with
  | direct rows =>
    intro hB hok x hx
    have hh : root < tape.length ∧ tapeCheck B tape rows = true ∧
        (rows.getD root zeroTapeBounds).value.hi ≤ 0 := by
      simpa only [verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq] using hok
    have hr := root_sound h hB tape root rows hh.1 hh.2.1 x hx
    exact hr.1.2.trans (by exact_mod_cast hh.2.2)
  | centered rows centers =>
    intro hB hok x hx
    have hh : root < tape.length ∧ tapeCheck B tape rows = true ∧
        tapeCheck (midpointBox B) tape centers = true ∧
        tapeCenteredBound B root rows centers ≤ 0 := by
      simpa only [verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq] using hok
    have hr := root_sound h hB tape root rows hh.1 hh.2.1
    have hmidvalid : ValidBox (midpointBox B) := by
      intro i; exact le_rfl
    have hmidin : inBox (midpointBox B)
        (fun i => ((((B i).lo+(B i).hi)/2 : ℚ) : ℝ)) := by
      intro i; exact ⟨le_rfl,le_rfl⟩
    have hm := root_sound h hmidvalid tape root centers hh.1 hh.2.2.1 _ hmidin
    have hu := centered_upper h (tapeExpr tape root) B
      (rows.getD root zeroTapeBounds).gradient
      (centers.getD root zeroTapeBounds).value.hi hB (fun y hy => (hr y hy).2)
      hm.1.2 x hx
    exact hu.trans (by exact_mod_cast hh.2.2.2)
  | face i upper rows child ih =>
    intro hB hok x hx
    have hh : root < tape.length ∧ tapeCheck B tape rows = true ∧
        (if upper then 0 ≤ ((rows.getD root zeroTapeBounds).gradient i).lo
          else ((rows.getD root zeroTapeBounds).gradient i).hi ≤ 0) ∧
        verifyTapeTree tape root (faceBox B i upper) child = true := by
      cases upper <;>
        simpa [verifyTapeTree,Bool.and_eq_true_iff,and_assoc] using hok
    have hr := root_sound h hB tape root rows hh.1 hh.2.1
    exact face_bound h (tapeExpr tape root) B i upper
      (rows.getD root zeroTapeBounds).gradient hB (fun y hy => (hr y hy).2) hh.2.2.1
      (ih (faceBox B i upper) (valid_face hB i upper) hh.2.2.2) x hx
  | split i q left right ihl ihr =>
    intro hB hok x hx
    have hh : ((B i).lo ≤ q ∧ q ≤ (B i).hi) ∧
        verifyTapeTree tape root (splitBox B i q false) left = true ∧
        verifyTapeTree tape root (splitBox B i q true) right = true := by
      simpa only [verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq] using hok
    have hq := hh.1
    by_cases hxq : x i ≤ (q : ℝ)
    · apply ihl (splitBox B i q false) (valid_split hB i q hq false) hh.2.1 x
      intro j
      by_cases hji : j = i
      · subst j
        simpa [splitBox,inBox] using
          (show x i ∈ Icc ((B i).lo : ℝ) (q : ℝ) from ⟨(hx i).1,hxq⟩)
      · simpa [splitBox,Function.update_of_ne hji] using hx j
    · apply ihr (splitBox B i q true) (valid_split hB i q hq true) hh.2.2 x
      intro j
      by_cases hji : j = i
      · subst j
        simpa [splitBox,inBox] using
          (show x i ∈ Icc (q : ℝ) ((B i).hi : ℝ) from ⟨le_of_not_ge hxq,(hx i).2⟩)
      · simpa [splitBox,Function.update_of_ne hji] using hx j

#print axioms from_children
end MetricDistortion.Contracts.Numerics_TapeReplay

