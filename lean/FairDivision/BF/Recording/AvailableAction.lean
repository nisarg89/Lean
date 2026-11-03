import FairDivision.BF.Recording.AvailableConnectivity

/-! Continuous child-permutation action on each exact available auxiliary
complex, in the same finite profile coordinates for every real/dummy stock. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology FairDivision.Topology.NerveConnectivity
open FairDivision.Topology.Volovikov

/-- Additive notation is only a wrapper around the manuscript's symmetric
group; its addition is permutation composition. -/
abbrev ChildGroup (p:ℕ):=Additive (Equiv.Perm (Fin p))

/-- The fixed Qp used at every graph point: p discrete copies of S_p. -/
abbrev Q (p:ℕ):=simplicialRealization (universalJoinComplex p (ChildGroup p))

/-- Reindex a realized child profile by the SAME position permutation. -/
def availableChildAction {p a q m d:ℕ} (E:Finset (Fin m))
    (g:ChildGroup p):
    simplicialRealization (availableAuxiliaryComplex p a q m E d)≃ₜ
      simplicialRealization (availableAuxiliaryComplex p a q m E d):=
  realizationHomeomorphOfVertexEquiv _ _ (relabelChildProfileEquiv g.toMul)
    (availableAuxiliary_relabel E g.toMul) (availableAuxiliary_relabel E g.toMul.symm)

theorem availableChildAction_laws {p a q m d:ℕ} (E:Finset (Fin m)):
    IsContinuousAddAction (availableChildAction (p:=p) (a:=a) (q:=q) (d:=d) E):=by
  constructor
  ·intro x
   apply Subtype.ext
   change relabelChildLottery (1:Equiv.Perm (Fin p)) x.1=x.1
   exact relabelChildLottery_one x.1
  ·intro g h x
   apply Subtype.ext
   change relabelChildLottery (g.toMul*h.toMul) x.1=
     relabelChildLottery g.toMul (relabelChildLottery h.toMul x.1)
   exact relabelChildLottery_mul g.toMul h.toMul x.1

/-- Local-stock inclusion commutes literally with the common profile action. -/
theorem availableChildAction_coordinate {p a q m d:ℕ} (E:Finset (Fin m))
    (g:ChildGroup p)
    (x:simplicialRealization (availableAuxiliaryComplex p a q m E d)):
    (availableChildAction E g x).1=relabelChildLottery g.toMul x.1:=rfl

/-- Canonical inclusion of a smaller stock, equivariant without relabeling
any item or changing any simplex weight. -/
def availableStockInclude {p a q m d e:ℕ}{E F:Finset (Fin m)}
    (hEF:E⊆F) (hde:d≤e):
    C(simplicialRealization (availableAuxiliaryComplex p a q m E d),
      simplicialRealization (availableAuxiliaryComplex p a q m F e)):=
  ContinuousMap.inclusion (simplicialRealization_mono (availableAuxiliaryComplex_mono hEF hde))

theorem availableStockInclude_action {p a q m d e:ℕ}{E F:Finset (Fin m)}
    (hEF:E⊆F) (hde:d≤e) (g:ChildGroup p)
    (x:simplicialRealization (availableAuxiliaryComplex p a q m E d)):
    availableStockInclude hEF hde (availableChildAction E g x)=
      availableChildAction F g (availableStockInclude hEF hde x):=by
  apply Subtype.ext
  rfl

end FairDivision.BF.Recording
