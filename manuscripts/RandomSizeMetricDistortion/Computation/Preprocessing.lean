import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_Preprocessing

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ
  have hkeep (c : Fin m) : ∃ u, ¬ Dominated σ u ∧ ∀ v, (σ v) c ≤ (σ v) u := by
    let S : Finset (Fin m) := Finset.univ.filter fun u => ∀ v, (σ v) c ≤ (σ v) u
    have hS : S.Nonempty := ⟨c,by simp [S]⟩
    obtain ⟨u,hu,hmax⟩ := S.exists_max_image (fun u => ∑ v, ((σ v) u).val) hS
    have huc : ∀ v, (σ v) c ≤ (σ v) u := (Finset.mem_filter.mp hu).2
    refine ⟨u,?_,huc⟩
    rintro ⟨b,hb⟩
    have hbc : b ∈ S := by
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
      intro v
      exact (huc v).trans (le_of_lt (hb v))
    have hlt : (∑ v, ((σ v) u).val) < ∑ v, ((σ v) b).val := by
      have hpoint (v : Fin n) : ((σ v) u).val < ((σ v) b).val := hb v
      exact Finset.sum_lt_sum (fun v hv => le_of_lt (hpoint v))
        ⟨⟨0,hn⟩,Finset.mem_univ _,hpoint ⟨0,hn⟩⟩
    exact not_lt_of_ge (hmax b hbc) hlt
  let U := {c : Fin m // ¬ Dominated σ c}
  have hUne : Nonempty U := by
    obtain ⟨u,hu,huc⟩ := hkeep ⟨0,hm⟩
    exact ⟨⟨u,hu⟩⟩
  letI : Nonempty U := hUne
  let count := Fintype.card U
  have hcount : 0 < count := Fintype.card_pos
  let e : Fin count ≃ U := (Fintype.equivFin U).symm
  let emb : Fin count ↪ Fin m :=
    {toFun := fun i => (e i).val
     inj' := by intro i j hij; exact e.injective (Subtype.ext hij)}
  let ranked (v : Fin n) := {j : Fin m // ¬ Dominated σ ((σ v).symm j)}
  let E (v : Fin n) : U ≃ ranked v :=
    {toFun := fun u => ⟨(σ v) u.val,by simpa only [(σ v).symm_apply_apply] using u.property⟩
     invFun := fun j => ⟨(σ v).symm j.val,j.property⟩
     left_inv := by intro u; apply Subtype.ext; exact (σ v).symm_apply_apply u.val
     right_inv := by intro j; apply Subtype.ext; exact (σ v).apply_symm_apply j.val}
  have hcard (v : Fin n) : Fintype.card (ranked v) = count :=
    Fintype.card_congr (E v).symm
  let O (v : Fin n) := Fintype.orderIsoFinOfCardEq (ranked v) (hcard v)
  let ranks : Profile n count := fun v => (e.trans (E v)).trans (O v).symm.toEquiv
  have hpreserves : ∀ v a b, prefers (ranks v) a b ↔ prefers (σ v) (emb a) (emb b) := by
    intro v a b
    change (O v).symm (E v (e b)) < (O v).symm (E v (e a)) ↔
      (σ v) (e b).val < (σ v) (e a).val
    exact (O v).symm.lt_iff_lt
  have hrange : Set.range emb = {c | ¬ Dominated σ c} := by
    ext c
    constructor
    · rintro ⟨i,rfl⟩
      exact (e i).property
    · intro hc
      refine ⟨e.symm ⟨c,hc⟩,?_⟩
      change (e (e.symm ⟨c,hc⟩)).val = c
      exact congrArg Subtype.val (e.apply_symm_apply ⟨c,hc⟩)
  let R : Reduction σ := ⟨count,hcount,emb,ranks,hpreserves,hrange⟩
  refine ⟨R,?_⟩
  intro d hcons
  have hweak_cost (c u : Fin m) (hcu : ∀ v, (σ v) c ≤ (σ v) u) : sc d u ≤ sc d c := by
    apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    apply Finset.sum_le_sum
    intro v hv
    rcases lt_or_eq_of_le (hcu v) with hh | hh
    · exact hcons v u c hh
    · have he : c = u := (σ v).injective hh
      simp [he]
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  letI : Nonempty (Fin count) := ⟨⟨0,hcount⟩⟩
  have hAll : (Set.range (sc d)).Nonempty := Set.range_nonempty _
  have hRet : (Set.range fun c => sc d (R.embed c)).Nonempty := Set.range_nonempty _
  apply le_antisymm
  · apply le_csInf hAll
    rintro t ⟨c,rfl⟩
    obtain ⟨u,hu,huc⟩ := hkeep c
    obtain ⟨i,hi⟩ : ∃ i, R.embed i = u := by
      have hu' : u ∈ Set.range R.embed := by rw [R.range_eq]; exact hu
      exact hu'
    have hh : sInf (Set.range fun c => sc d (R.embed c)) ≤ sc d u := by
      rw [← hi]
      exact csInf_le (Set.finite_range (fun c => sc d (R.embed c))).bddBelow ⟨i,rfl⟩
    exact hh.trans (hweak_cost c u huc)
  · apply le_csInf hRet
    rintro t ⟨i,rfl⟩
    exact csInf_le (Set.finite_range (sc d)).bddBelow ⟨R.embed i,rfl⟩

#print axioms from_children
end MetricDistortion.Contracts.Computation_Preprocessing
