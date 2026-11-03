import FairDivision.BF.Recording.ChildProfiles

/-!
# The actual continuous child-score map T

Each auxiliary vertex supplies the SAME recording vertex (real bundle,
dummy count) at each child position. Scores are averaged with the literal
simplex weights, and t remains a common input. The map is continuous jointly
in the auxiliary point and t, equivariant, and has strict coordinate signs
at the two target boundaries. No equalization or zero theorem is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology

/-- Literal expected child scores at the common target t. -/
def childScores {p a q m:ℕ} {v:Finset (Fin m)→ℝ} {L H:ℝ} {hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH)
    (z:stdSimplex ℝ (ChildProfile p a q m)×Set.Icc L H):Fin p→ℝ:=
  fun i=>∑b:ChildProfile p a q m,z.1.1 b*Φ.phi (vertexPoint (b i),z.2)

theorem continuous_childScores {p a q m:ℕ} {v:Finset (Fin m)→ℝ}
    {L H:ℝ} {hLH:L≤H} (Φ:RecordingFunction a q m v L H hLH):
    Continuous (childScores (p:=p) Φ):=by
  apply continuous_pi
  intro i
  apply continuous_finset_sum
  intro b hb
  exact (((continuous_apply b).comp continuous_subtype_val).comp continuous_fst).mul
    (Φ.phi.continuous.comp (continuous_const.prodMk continuous_snd))

/-- Coordinate equality for the actual simplex pushforward by a permutation. -/
theorem relabelChildLottery_coordinate {p a q m:ℕ} (σ:Equiv.Perm (Fin p))
    (x:stdSimplex ℝ (ChildProfile p a q m)) (b:ChildProfile p a q m):
    (relabelChildLottery σ x).1 (relabelChildProfile σ b)=x.1 b:=by
  classical
  change FunOnFinite.linearMap ℝ ℝ (relabelChildProfile σ) x.1 (relabelChildProfile σ b)=_
  rw [FunOnFinite.linearMap_apply_apply]
  have hInject:Function.Injective (relabelChildProfile (a:=a) (q:=q) (m:=m) σ):=
    (relabelChildProfileEquiv σ).injective
  have hFiber:Finset.univ.filter (fun c:ChildProfile p a q m=>
      relabelChildProfile σ c=relabelChildProfile σ b)={b}:=by
    ext c
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact hInject.eq_iff
  rw [hFiber,Finset.sum_singleton]

/-- A permutation pushforward preserves exactly the positive-supported
profiles, not merely an ambient face containing them. -/
theorem finiteSimplexSupport_relabelChildLottery {p a q m:ℕ}
    (σ:Equiv.Perm (Fin p)) (x:stdSimplex ℝ (ChildProfile p a q m)):
    finiteSimplexSupport (relabelChildLottery σ x)=
      (finiteSimplexSupport x).image (relabelChildProfile σ):=by
  classical
  apply Finset.Subset.antisymm
  ·exact NerveConnectivity.finiteSimplexSupport_map_subset (relabelChildProfile σ) x
  ·intro b hb
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hb
   apply (mem_finiteSimplexSupport_iff _ _).mpr
   rw [relabelChildLottery_coordinate]
   exact (mem_finiteSimplexSupport_iff x c).mp hc

/-- The action transports the ACTUAL real pool at position i to position
σ(i), with no extra items acquired from zero-weight profiles. -/
theorem childRealPool_relabelChildLottery {p a q m:ℕ}
    (σ:Equiv.Perm (Fin p)) (x:stdSimplex ℝ (ChildProfile p a q m)) (i:Fin p):
    childRealPool (finiteSimplexSupport (relabelChildLottery σ x)) (σ i)=
      childRealPool (finiteSimplexSupport x) i:=by
  rw [finiteSimplexSupport_relabelChildLottery,childRealPool_relabel]
  rw [σ.symm_apply_apply]

/-- The corresponding maximum needed dummy count also follows the SAME
child position permutation, independently of any choice of dummy labels. -/
theorem childDummyMax_relabelChildLottery {p a q m:ℕ}
    (σ:Equiv.Perm (Fin p)) (x:stdSimplex ℝ (ChildProfile p a q m)) (i:Fin p):
    childDummyMax (finiteSimplexSupport (relabelChildLottery σ x)) (σ i)=
      childDummyMax (finiteSimplexSupport x) i:=by
  rw [finiteSimplexSupport_relabelChildLottery,childDummyMax_relabel]
  rw [σ.symm_apply_apply]

theorem childScores_equivariant {p a q m:ℕ} {v:Finset (Fin m)→ℝ}
    {L H:ℝ} {hLH:L≤H} (Φ:RecordingFunction a q m v L H hLH)
    (σ:Equiv.Perm (Fin p)) (x:stdSimplex ℝ (ChildProfile p a q m))
    (t:Set.Icc L H) (i:Fin p):
    childScores Φ (relabelChildLottery σ x,t) (σ i)=childScores Φ (x,t) i:=by
  classical
  change (∑b:ChildProfile p a q m,(relabelChildLottery σ x).1 b*
    Φ.phi (vertexPoint (b (σ i)),t))=
      ∑b:ChildProfile p a q m,x.1 b*Φ.phi (vertexPoint (b i),t)
  calc
    (∑b:ChildProfile p a q m,(relabelChildLottery σ x).1 b*
        Φ.phi (vertexPoint (b (σ i)),t))=
      ∑b:ChildProfile p a q m,
        (relabelChildLottery σ x).1 (relabelChildProfile σ b)*
          Φ.phi (vertexPoint ((relabelChildProfile σ b) (σ i)),t):=
      (Equiv.sum_comp (relabelChildProfileEquiv (a:=a) (q:=q) (m:=m) σ)
        (fun c=>(relabelChildLottery σ x).1 c*Φ.phi (vertexPoint (c (σ i)),t))).symm
    _=∑b:ChildProfile p a q m,x.1 b*Φ.phi (vertexPoint (b i),t):=by
      apply Finset.sum_congr rfl
      intro b _
      rw [relabelChildLottery_coordinate]
      simp only [relabelChildProfile,σ.symm_apply_apply]

theorem childScores_lower {p a q m:ℕ} {v:Finset (Fin m)→ℝ}
    {L H:ℝ} {hLH:L≤H} (Φ:RecordingFunction a q m v L H hLH)
    (x:stdSimplex ℝ (ChildProfile p a q m)) (i:Fin p):
    childScores Φ (x,lowerTarget hLH) i<0:=by
  classical
  obtain ⟨b,hb⟩:=finiteSimplexSupport_nonempty x
  have hbpos:0<x.1 b:=(mem_finiteSimplexSupport_iff x b).mp hb
  have hStrict:(∑c:ChildProfile p a q m,x.1 c*Φ.phi (vertexPoint (c i),lowerTarget hLH))<
      ∑c:ChildProfile p a q m,(0:ℝ):=by
    apply Finset.sum_lt_sum
    ·intro c hc
     exact mul_nonpos_of_nonneg_of_nonpos (x.2.1 c) (Φ.negative (vertexPoint (c i))).le
    ·exact ⟨b,Finset.mem_univ _,mul_neg_of_pos_of_neg hbpos (Φ.negative (vertexPoint (b i)))⟩
  simpa only [childScores,Finset.sum_const_zero] using hStrict

theorem childScores_upper {p a q m:ℕ} {v:Finset (Fin m)→ℝ}
    {L H:ℝ} {hLH:L≤H} (Φ:RecordingFunction a q m v L H hLH)
    (x:stdSimplex ℝ (ChildProfile p a q m)) (i:Fin p):
    0<childScores Φ (x,upperTarget hLH) i:=by
  classical
  obtain ⟨b,hb⟩:=finiteSimplexSupport_nonempty x
  have hbpos:0<x.1 b:=(mem_finiteSimplexSupport_iff x b).mp hb
  have hStrict:(∑c:ChildProfile p a q m,(0:ℝ))<
      ∑c:ChildProfile p a q m,x.1 c*Φ.phi (vertexPoint (c i),upperTarget hLH):=by
    apply Finset.sum_lt_sum
    ·intro c hc
     exact mul_nonneg (x.2.1 c) (Φ.positive (vertexPoint (c i))).le
    ·exact ⟨b,Finset.mem_univ _,mul_pos hbpos (Φ.positive (vertexPoint (b i)))⟩
  simpa only [childScores,Finset.sum_const_zero] using hStrict

/-- Compose the actual graph-family map with the joint expected-score map.
Only the concrete family is an input to this composition lemma; the later
construction supplies it from the stated connectivity bounds. -/
def childT {p a q m:ℕ} {v:Finset (Fin m)→ℝ} {L H:ℝ} {hLH:L≤H}
    {Q J:Type*} [TopologicalSpace Q] [TopologicalSpace J]
    (Φ:RecordingFunction a q m v L H hLH)
    (family:C(Q×J,stdSimplex ℝ (ChildProfile p a q m))):
    C((Q×J)×Set.Icc L H,Fin p→ℝ):=
  ⟨fun z=>childScores Φ (family z.1,z.2),
    (continuous_childScores Φ).comp ((family.continuous.comp continuous_fst).prodMk continuous_snd)⟩

@[simp] theorem childT_lower {p a q m:ℕ} {v:Finset (Fin m)→ℝ}
    {L H:ℝ} {hLH:L≤H} {Q J:Type*} [TopologicalSpace Q] [TopologicalSpace J]
    (Φ:RecordingFunction a q m v L H hLH)
    (family:C(Q×J,stdSimplex ℝ (ChildProfile p a q m))) (x:Q×J) (i:Fin p):
    childT Φ family (x,lowerTarget hLH) i<0:=childScores_lower Φ (family x) i

@[simp] theorem childT_upper {p a q m:ℕ} {v:Finset (Fin m)→ℝ}
    {L H:ℝ} {hLH:L≤H} {Q J:Type*} [TopologicalSpace Q] [TopologicalSpace J]
    (Φ:RecordingFunction a q m v L H hLH)
    (family:C(Q×J,stdSimplex ℝ (ChildProfile p a q m))) (x:Q×J) (i:Fin p):
    0<childT Φ family (x,upperTarget hLH) i:=childScores_upper Φ (family x) i

theorem childT_equivariant {p a q m:ℕ} {v:Finset (Fin m)→ℝ}
    {L H:ℝ} {hLH:L≤H} {Q J:Type*} [TopologicalSpace Q] [TopologicalSpace J]
    (Φ:RecordingFunction a q m v L H hLH)
    (family:C(Q×J,stdSimplex ℝ (ChildProfile p a q m)))
    (act:Equiv.Perm (Fin p)→Q→Q)
    (hFamily:∀σ x b,family (act σ x,b)=relabelChildLottery σ (family (x,b)))
    (σ:Equiv.Perm (Fin p)) (x:Q) (b:J) (t:Set.Icc L H) (i:Fin p):
    childT Φ family ((act σ x,b),t) (σ i)=childT Φ family ((x,b),t) i:=by
  change childScores Φ (family (act σ x,b),t) (σ i)=_
  rw [hFamily]
  exact childScores_equivariant Φ σ (family (x,b)) t i

end FairDivision.BF.Recording
