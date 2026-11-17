import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_ThresholdStepFunctions

/-- A threshold map with finitely many tests is a finite measurable step map.
The values need not have any continuity as a function of the marked set. -/
private lemma measurable_shape {m : ℕ} (x : Fin m → ℝ) (G : Finset (Fin m) → ℝ) :
    Measurable (fun t => G (Finset.univ.filter (fun c => t < x c))) := by
  let S : ℝ → Finset (Fin m) := fun t => Finset.univ.filter (fun c => t < x c)
  have hcell (T : Finset (Fin m)) : MeasurableSet {t | S t=T} := by
    have heq : {t | S t=T} = {t | ∀ c, (t < x c ↔ c ∈ T)} := by
      ext t
      simp [S,Finset.ext_iff]
    rw [heq]
    simp_rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro c
    by_cases hc : c ∈ T
    · have he : {t | t < x c ↔ c ∈ T} = Iio (x c) := by ext t; simp [hc]
      rw [he]
      exact measurableSet_Iio
    · have he : {t | t < x c ↔ c ∈ T} = Ici (x c) := by ext t; simp [hc,not_lt]
      rw [he]
      exact measurableSet_Ici
  have heq : (fun t => G (S t)) =
      fun t => ∑ T : Finset (Fin m), {u | S u=T}.indicator (fun _ => G T) t := by
    funext t
    symm
    rw [Finset.sum_eq_single (S t)]
    · simp
    · intro T _ hT
      simp only [Set.indicator_of_notMem (show t ∉ {u | S u=T} from Ne.symm hT)]
    · simp
  change Measurable (fun t => G (S t))
  rw [heq]
  exact Finset.measurable_sum _ (fun T _ => measurable_const.indicator (hcell T))

theorem from_children (h : Needs) : Statement := by
  intro n m σ P d o v
  let x : Fin m → ℝ := fun c => distance d (.inr o) (.inr c)
  let M := sSup (Set.range x)
  let r := σ v
  have hbelow (c : Fin m) : 0 ≤ below r P c := by
    unfold below mass
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact P.property.1 j
    · exact le_rfl
  have hempty : ∀ t, M ≤ t → marked d o t=∅ := by
    intro t ht
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hxc : x c ≤ M := le_csSup (Set.finite_range x).bddAbove ⟨c,rfl⟩
    exact (lt_of_lt_of_le hc hxc).not_ge ht
  have hvanish : ∀ t, M ≤ t → lowerCut σ P d o v t=0 ∧ upperCut σ P d o v t=0 := by
    intro t ht
    have hmarked := hempty t ht
    have hm : 0 < m := Nat.zero_lt_of_lt o.isLt
    let c0 : Fin m := r.symm ⟨0,hm⟩
    have hc0 : below r P c0=0 := by simp [below,mass,prefers,c0,Fin.lt_def]
    constructor
    · change sInf {z | ∃ c, c ∉ marked d o t ∧ z=below r P c} = 0
      apply IsLeast.csInf_eq
      refine ⟨⟨c0,by simp [hmarked],hc0.symm⟩,?_⟩
      rintro z ⟨c,_,rfl⟩
      exact hbelow c
    · simp [upperCut,hmarked]
  let L : Finset (Fin m) → ℝ := fun T => sInf {z | ∃ c, c ∉ T ∧ z=below r P c}
  let U : Finset (Fin m) → ℝ := fun T =>
    if ∃ c, c ∈ T ∧ 0 < P.val c then
      sSup {z | ∃ c, c ∈ T ∧ 0 < P.val c ∧ z=below r P c+P.val c} else 0
  have hLeq : lowerCut σ P d o v = fun t => L (Finset.univ.filter (fun c => t < x c)) := by
    funext t
    simp [lowerCut,L,marked,x,r]
  have hUeq : upperCut σ P d o v = fun t => U (Finset.univ.filter (fun c => t < x c)) := by
    funext t
    simp [upperCut,U,marked,x,r]
    by_cases hpos : ∃ c : Fin m, t < distance d (.inr o) (.inr c) ∧ 0 < P.val c <;> simp [hpos]
  have hL : Measurable (lowerCut σ P d o v) := by
    rw [hLeq]
    exact measurable_shape x L
  have hU : Measurable (upperCut σ P d o v) := by
    rw [hUeq]
    exact measurable_shape x U
  refine ⟨?_,?_,hvanish,?_⟩
  · have hdom : Integrable ((Ioc (0 : ℝ) M).indicator (fun _ => (1 : ℝ))) volume :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp [Real.volume_Ioc]))
    apply hdom.restrict.mono' hL.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp := h.child_0 n m σ P d o v t ht.le
    by_cases htM : t ≤ M
    · have hmem : t ∈ Ioc (0 : ℝ) M := ⟨ht,htM⟩
      rw [Set.indicator_of_mem hmem,Real.norm_eq_abs,abs_of_nonneg hp.1]
      exact hp.2.1.trans (min_le_left _ _) |>.trans (hp.2.2.1.trans hp.2.2.2.1)
    · rw [(hvanish t (le_of_not_ge htM)).1]
      simp only [norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · intro q
    exact (measurableSet_le measurable_const measurable_id).inter
      ((measurableSet_le hL measurable_const).inter (measurableSet_lt measurable_const hU))

  · intro F
    let G : Finset (Fin m) → ℝ := fun T => F (T : Set (Fin m))
    have heq : (fun t => F (marked d o t)) =
        fun t => G (Finset.univ.filter (fun c => t < x c)) := by
      funext t
      change F (marked d o t) = F (↑(Finset.univ.filter (fun c => t < x c)))
      congr 1
      ext c
      simp [marked,x]
    have hmeas : Measurable (fun t => F (marked d o t)) := by
      rw [heq]
      exact measurable_shape x G
    refine ⟨hmeas,?_⟩
    intro hF
    let C : ℝ := ∑ T : Finset (Fin m), |G T|
    have hbound (t : ℝ) : ‖F (marked d o t)‖ ≤ C := by
      change ‖(fun u => F (marked d o u)) t‖ ≤ C
      rw [heq]
      exact Finset.single_le_sum (fun T _ => abs_nonneg (G T))
        (Finset.mem_univ (Finset.univ.filter (fun c => t < x c)))
    have hdom : Integrable ((Ioc (0 : ℝ) M).indicator (fun _ => C)) volume :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp [Real.volume_Ioc]))
    apply hdom.restrict.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases htM : t ≤ M
    · rw [Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) M from ⟨ht,htM⟩)]
      exact hbound t
    · rw [hempty t (le_of_not_ge htM),hF]
      simp [Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) M from fun hx => htM hx.2)]

#print axioms from_children
end MetricDistortion.Contracts.Geometry_ThresholdStepFunctions
