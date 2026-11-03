import FairDivision.Topology.AAK.ZeroFreePoleHomotopy
import Mathlib.Algebra.Field.ZMod

/-!
# Prime-cyclic stabilizers of the finite bipyramid target

Coordinate translation fixes the two poles. Every other nonempty target face
contains a base vertex and omits another base vertex. A nonzero translation
of a prime cyclic group generates every label, so such a face has trivial
stabilizer. These are concrete face/action facts for the relative chain
obstruction; no topological no-map or homotopy-invariance result is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.ZeroFreeBipyramid

open scoped Classical

/-- Additive label translation on the prime cyclic coordinate set. -/
def cyclicPerm {p : ℕ} (a : ZMod p) : Equiv.Perm (ZMod p) := Equiv.addLeft a

/-- The induced vertex permutation fixes the poles and translates base labels. -/
def translateFace {p : ℕ} (a : ZMod p) (S : Finset (Vertex (ZMod p))) :
    Finset (Vertex (ZMod p)) :=
  S.image (vertexPerm (cyclicPerm a))

@[simp] theorem cyclicPerm_apply {p : ℕ} (a v : ZMod p) : cyclicPerm a v = a + v := rfl

@[simp] theorem translateFace_pole {p : ℕ} (a : ZMod p) (b : Bool) :
    translateFace a {pole b} = {pole b} := by
  simp [translateFace, vertexPerm]

@[simp] theorem translateFace_zero {p : ℕ} (S : Finset (Vertex (ZMod p))) :
    translateFace 0 S = S := by
  have he : (vertexPerm (cyclicPerm (0 : ZMod p)) : Vertex (ZMod p) → Vertex (ZMod p)) = id := by
    funext v
    cases v <;> simp [vertexPerm, cyclicPerm]
  simp [translateFace, he]

theorem translateFace_add {p : ℕ} (a b : ZMod p) (S : Finset (Vertex (ZMod p))) :
    translateFace (a + b) S = translateFace a (translateFace b S) := by
  unfold translateFace
  rw [Finset.image_image]
  congr 1
  funext v
  cases v <;> simp [vertexPerm, cyclicPerm, add_assoc]

theorem mem_translateFace_iff {p : ℕ} (a : ZMod p)
    (S : Finset (Vertex (ZMod p))) (v : Vertex (ZMod p)) :
    vertexPerm (cyclicPerm a) v ∈ translateFace a S ↔ v ∈ S := by
  simp only [translateFace,Finset.mem_image,
    (vertexPerm (cyclicPerm a)).injective.eq_iff,exists_eq_right]

/-- Translation preserves the literal finite target complex. -/
theorem translateFace_mem_complex {p : ℕ} [Fact p.Prime]
    (a : ZMod p) {S : Finset (Vertex (ZMod p))} (hS : S ∈ complex (ZMod p)) :
    translateFace a S ∈ complex (ZMod p) := by
  refine ⟨hS.1.image _, ?_, ?_⟩
  · intro h
    have hn : pole true ∈ S :=
      (mem_translateFace_iff a S (pole true)).1 (by simpa [vertexPerm] using h.1)
    have hs : pole false ∈ S :=
      (mem_translateFace_iff a S (pole false)).1 (by simpa [vertexPerm] using h.2)
    exact hS.2.1 ⟨hn, hs⟩
  · obtain ⟨v, hv⟩ := hS.2.2
    refine ⟨a + v, ?_⟩
    intro hm
    apply hv
    exact (mem_translateFace_iff a S (base v)).1 (by simpa [vertexPerm] using hm)

/-- An invariant face containing one base label contains every translate
of that label, by literal iteration of the same face action. -/
theorem base_mem_iterate_translate {p : ℕ} [Fact p.Prime]
    (a : ZMod p) {S : Finset (Vertex (ZMod p))}
    (hfixed : translateFace a S = S) {v : ZMod p} (hv : base v ∈ S) :
    ∀ k : ℕ, base ((k : ZMod p) * a + v) ∈ S := by
  intro k
  induction k with
  | zero => simpa using hv
  | succ k ih =>
      have hnext : vertexPerm (cyclicPerm a) (base ((k : ZMod p) * a + v)) ∈ S := by
        rw [← hfixed]
        exact Finset.mem_image.mpr ⟨_, ih, rfl⟩
      have he : a + ((k : ZMod p) * a + v) = ((k + 1 : ℕ) : ZMod p) * a + v := by
        push_cast
        ring
      simpa [vertexPerm, he] using hnext

/-- For a prime cyclic label group, any nonzero invariant translation
forces the base labels of a nonempty base face to be the whole group. -/
theorem invariant_base_is_all {p : ℕ} [Fact p.Prime]
    (a : ZMod p) (ha : a ≠ 0) {S : Finset (Vertex (ZMod p))}
    (hfixed : translateFace a S = S) {v : ZMod p} (hv : base v ∈ S) :
    ∀ w : ZMod p, base w ∈ S := by
  intro w
  let z : ZMod p := (w - v) / a
  have hz : (z.val : ZMod p) = z := ZMod.natCast_zmod_val z
  have he : (z.val : ZMod p) * a + v = w := by
    rw [hz]
    dsimp only [z]
    rw [div_mul_cancel₀ _ ha,sub_add_cancel]
  exact he ▸ base_mem_iterate_translate a hfixed hv z.val

/-- Every face containing a base vertex has trivial cyclic stabilizer. -/
theorem face_stabilizer_eq_zero {p : ℕ} [Fact p.Prime]
    {S : Finset (Vertex (ZMod p))} (hS : S ∈ complex (ZMod p))
    (hbase : ∃ v : ZMod p, base v ∈ S)
    (a : ZMod p) (hfixed : translateFace a S = S) : a = 0 := by
  by_contra ha
  obtain ⟨v, hv⟩ := hbase
  obtain ⟨w, hw⟩ := hS.2.2
  exact hw (invariant_base_is_all a ha hfixed hv w)

/-- A nonempty target face without a base vertex is precisely one fixed pole. -/
theorem face_pole_or_base {p : ℕ} [Fact p.Prime]
    {S : Finset (Vertex (ZMod p))} (hS : S ∈ complex (ZMod p)) :
    (∃ b : Bool, S = {pole b}) ∨ ∃ v : ZMod p, base v ∈ S := by
  classical
  by_cases hb : ∃ v : ZMod p, base v ∈ S
  · exact Or.inr hb
  · left
    obtain ⟨z, hz⟩ := hS.1
    cases z with
    | inr v => exact False.elim (hb ⟨v, hz⟩)
    | inl b =>
        refine ⟨b, ?_⟩
        ext w
        simp only [Finset.mem_singleton]
        constructor
        · intro hw
          cases w with
          | inr v => exact False.elim (hb ⟨v, hw⟩)
          | inl c =>
              have he : c = b := by
                cases b with
                | false =>
                  cases c with
                  | false => rfl
                  | true => exact (hS.2.1 ⟨hw,hz⟩).elim
                | true =>
                  cases c with
                  | false => exact (hS.2.1 ⟨hz,hw⟩).elim
                  | true => rfl
              exact congrArg Sum.inl he
        · rintro rfl
          exact hz

/-- The ONLY exceptional stabilizers are the two fixed vertices. -/
theorem translateFace_fixed_iff {p : ℕ} [Fact p.Prime]
    {S : Finset (Vertex (ZMod p))} (hS : S ∈ complex (ZMod p)) (a : ZMod p) :
    translateFace a S = S ↔ a = 0 ∨ ∃ b : Bool, S = {pole b} := by
  constructor
  · intro hfixed
    rcases face_pole_or_base hS with hpole | hbase
    · exact Or.inr hpole
    · exact Or.inl (face_stabilizer_eq_zero hS hbase a hfixed)
  · rintro (rfl | ⟨b, rfl⟩) <;> simp

/-- Different group elements give different translates of every nonpole
face. This provides actual free face orbits for chain fundamental domains. -/
theorem translateFace_injective {p : ℕ} [Fact p.Prime]
    {S : Finset (Vertex (ZMod p))} (hS : S ∈ complex (ZMod p))
    (hbase : ∃ v : ZMod p, base v ∈ S) :
    Function.Injective (fun a : ZMod p => translateFace a S) := by
  intro a b hab
  have hfixed : translateFace (a - b) S = S := by
    have h := congrArg (translateFace (-b)) hab
    rw [← translateFace_add, ← translateFace_add] at h
    simpa [sub_eq_add_neg, add_comm] using h
  exact sub_eq_zero.mp (face_stabilizer_eq_zero hS hbase (a - b) hfixed)

end FairDivision.Topology.AAK.ZeroFreeBipyramid
