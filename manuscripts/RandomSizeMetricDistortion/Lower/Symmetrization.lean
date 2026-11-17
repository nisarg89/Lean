import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_Symmetrization

theorem from_children (h : Needs) : Statement := by
  intro n N k hn hk hkN z hz D σ hσ Q hQ
  let G := Equiv.Perm (Fin N)
  let M : ℝ := Fintype.card G
  have hMp : 0 < M := by dsimp [M]; exact_mod_cast Fintype.card_pos (α := G)
  have hM0 : M ≠ 0 := ne_of_gt hMp
  let lift : G → Ranking (N+1) := fun g => Equiv.Perm.decomposeFin.symm (0,g)
  have hl0 (g : G) : lift g 0 = 0 := by simp [lift]
  have hls (g : G) (i : Fin N) : lift g i.succ = (g i).succ := by simp [lift]
  have hlmul (g t : G) (c : Fin (N+1)) : lift g (lift t c) = lift (g*t) c := by
    refine Fin.cases ?_ (fun i => ?_) c
    · simp [hl0]
    · simp only [hls]; rfl
  let R : G → Lottery (N+1) := fun g =>
    ⟨fun c => Q.val (lift g c),
      (fun c => Q.property.1 (lift g c)),
      (Equiv.sum_comp (lift g) Q.val).trans Q.property.2⟩
  let a : Fin (N+1) → ℝ := fun c => (∑ g : G, (R g).val c)/M
  have han : ∀ c, 0 ≤ a c := by
    intro c
    exact div_nonneg (Finset.sum_nonneg fun g _ => (R g).property.1 c) hMp.le
  have hatotal : ∑ c, a c = 1 := by
    dsimp [a]
    rw [← Finset.sum_div,Finset.sum_comm]
    simp_rw [(R _).property.2]
    simp [M,hM0]
  let A : Lottery (N+1) := ⟨a,han,hatotal⟩
  have ha0 : a 0 = Q.val 0 := by
    simp [a,R,hl0,M,hM0]
  have hai (t : G) (c : Fin (N+1)) : a (lift t c) = a c := by
    let T : G ≃ G :=
      {toFun := fun g => g*t
       invFun := fun g => g*t⁻¹
       left_inv := by
         intro g
         apply Equiv.ext
         intro j
         change g (t (t.symm j)) = g j
         exact congrArg g (t.apply_symm_apply j)
       right_inv := by
         intro g
         apply Equiv.ext
         intro j
         change g (t.symm (t j)) = g j
         exact congrArg g (t.symm_apply_apply j)}
    have he := T.sum_comp (fun g => Q.val (lift g c))
    dsimp [a,R]
    simp_rw [hlmul]
    exact congrArg (fun y : ℝ => y/M) he
  have hN : 0 < N := hk.trans hkN
  let i0 : Fin N := ⟨0,hN⟩
  have hasame (i : Fin N) : a i.succ = a i0.succ := by
    have hh := hai (Equiv.swap i i0) i.succ
    rw [hls] at hh
    have hswap : (Equiv.swap i i0) i = i0 := Equiv.swap_apply_left i i0
    rw [hswap] at hh
    exact hh.symm
  have hasum : a 0+(N : ℝ)*a i0.succ = 1 := by
    have hh := hatotal
    rw [Fin.sum_univ_succ] at hh
    simpa only [hasame,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have haref : Reference (1-Q.val 0) A := by
    intro c
    refine Fin.cases ?_ (fun i => ?_) c
    · simp [A,ha0]
    · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      change a i.succ = _
      rw [hasame]
      simp only [Fin.val_succ,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
      apply (eq_div_iff (ne_of_gt hNr)).2
      rw [ha0] at hasum
      linarith
  have hweights : ∑ _g : G, (1/M : ℝ) = 1 := by simp [M,hM0]
  have hvec : (∑ g : G, (1/M : ℝ) • (R g).val) = A.val := by
    ext c
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    change (∑ g : G, (1/M)*(R g).val c) = (∑ g : G, (R g).val c)/M
    rw [← Finset.mul_sum]
    ring
  have hpoint (v : Fin n) (c : Fin (N+1)) :
      compare D (σ v) A c ≤ ∑ g : G, (1/M)*compare D (σ v) (R g) c := by
    have hc := (h.child_0 (N+1) D (σ v) A c).2.2.2
    have hj := hc.map_sum_le (t := Finset.univ) (w := fun _ : G => (1/M : ℝ))
      (p := fun g => (R g).val) (by intro g hg; positivity) hweights
      (by intro g hg; exact (R g).property)
    rw [hvec] at hj
    rw [← (h.child_0 (N+1) D (σ v) A c).1] at hj
    simpa only [smul_eq_mul,← (h.child_0 (N+1) D (σ v) (R _) c).1] using hj
  have hstable : Stable D σ A := by
    intro c
    have hh := div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hpoint v c)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have he : ((∑ v : Fin n, ∑ g : G, (1/M)*compare D (σ v) (R g) c)/(n : ℝ)) =
        ∑ g : G, (1/M)*score D σ (R g) c := by
      rw [Finset.sum_comm,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro g hg
      unfold score avg
      rw [← Finset.mul_sum]
      ring
    rw [he] at hh
    change score D σ A c ≤ _ at hh
    apply hh.trans
    calc
      (∑ g : G, (1/M)*score D σ (R g) c) ≤ ∑ _g : G, (1/M)*mu D := by
        apply Finset.sum_le_sum
        intro g hg
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hinv := h.child_4 n N k hn hk hkN z hz D σ hσ (lift g) (hl0 g) Q (R g)
          (fun j => rfl) c
        rw [hinv]
        exact hQ (lift g c)
      _ = mu D := by rw [← Finset.sum_mul,hweights,one_mul]
  exact ⟨A,haref,hstable⟩

#print axioms from_children
end MetricDistortion.Contracts.Lower_Symmetrization
