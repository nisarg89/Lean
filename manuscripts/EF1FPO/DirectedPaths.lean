import Mathlib

/-! Directed path facts used for the recovery and repair arguments. -/

set_option autoImplicit false

namespace EF1FPO.DirectedPaths

variable {V M : Type*} [Quiver V] [Monoid M]

theorem exists_nodup_path_weight_le [Preorder M]
    (w : ∀ {a b : V}, (a ⟶ b) → M)
    (leftMono : ∀ x : M, Monotone (x * ·)) (rightMono : ∀ x : M, Monotone (· * x))
    (hcycles : ∀ {a b : V} (q : Quiver.Path a b) (e : b ⟶ a),
      q.vertices.Nodup → 1 ≤ (q.cons e).weight w)
    {a b : V} (p : Quiver.Path a b) :
    ∃ q : Quiver.Path a b, q.vertices.Nodup ∧ q.weight w ≤ p.weight w := by
  classical
  induction p with
  | nil => exact ⟨Quiver.Path.nil, List.nodup_singleton _, le_rfl⟩
  | @cons b c p e ih =>
    obtain ⟨q, hq, hweight⟩ := ih
    by_cases hc : c ∈ q.vertices
    · obtain ⟨r, s, heq⟩ := q.exists_eq_comp_of_mem_vertices hc
      have hsplit : (r.vertices.dropLast ++ s.vertices).Nodup := by
        simpa only [heq, Quiver.Path.vertices_comp] using hq
      have hs := hsplit.of_append_right
      have hr : r.vertices.Nodup := by
        cases h : s.vertices with
        | nil => exact (s.vertices_ne_nil h).elim
        | cons x l =>
          have hx : x = c := by simpa [h] using s.vertices_head?
          subst x
          rw [h, show c :: l = [c] ++ l by rfl, ← List.append_assoc,
            r.dropLast_append_end_eq] at hsplit
          exact hsplit.of_append_left
      refine ⟨r, hr, ?_⟩
      calc
        r.weight w = r.weight w * 1 := (mul_one _).symm
        _ ≤ r.weight w * (s.cons e).weight w := leftMono _ (hcycles s e hs)
        _ = q.weight w * w e := by
          rw [heq, Quiver.Path.weight_comp, Quiver.Path.weight_cons, mul_assoc]
        _ ≤ p.weight w * w e := rightMono (w e) hweight
        _ = (p.cons e).weight w := (Quiver.Path.weight_cons w p e).symm
    · refine ⟨q.cons e, ?_, ?_⟩
      · rw [Quiver.Path.vertices_cons, List.nodup_concat]
        exact ⟨hc, hq⟩
      · simpa only [Quiver.Path.weight_cons] using rightMono (w e) hweight

theorem finite_bounded_weights [Finite V] [∀ a b : V, Finite (a ⟶ b)]
    (w : ∀ {a b : V}, (a ⟶ b) → M) (a b : V) (k : ℕ) :
    {x : M | ∃ p : Quiver.Path a b, p.length ≤ k ∧ p.weight w = x}.Finite := by
  classical
  induction k generalizing b with
  | zero =>
    refine (Set.finite_singleton (1 : M)).subset (fun x hx => ?_)
    obtain ⟨p, hp, heq⟩ := hx
    cases p with
    | nil => simpa using heq.symm
    | cons q e => simp [Quiver.Path.length_cons] at hp
  | succ k ih =>
    let W : Set M := {1} ∪ ⋃ c : V, ⋃ e : c ⟶ b,
      (fun y : M => y * w e) '' {y : M | ∃ p : Quiver.Path a c,
        p.length ≤ k ∧ p.weight w = y}
    have hW : W.Finite := (Set.finite_singleton _).union <|
      Set.finite_iUnion (fun c => Set.finite_iUnion (fun e => (ih c).image (fun y => y * w e)))
    refine hW.subset (fun x hx => ?_)
    obtain ⟨p, hp, heq⟩ := hx
    cases p with
    | nil => exact Or.inl (by simpa using heq.symm)
    | @cons c b q e =>
      apply Or.inr
      refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨e, q.weight w, ?_, ?_⟩⟩
      · exact ⟨q, by simpa only [Quiver.Path.length_cons, Nat.succ_le_succ_iff] using hp, rfl⟩
      · simpa only [Quiver.Path.weight_cons] using heq

end EF1FPO.DirectedPaths
