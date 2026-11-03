import FairDivision.BF.Recording.StockProfileRealization
import FairDivision.Topology.VariableDummyUniformConnectivityFinal

/-!
# The two connectivity bounds used by the SAME recording construction

A full edge stock has apq items and is (p−1)-connected. A vertex stock has
one fewer real item and is (p−2)-connected. Both are specializations of the
existing manuscript variable-stock induction, transported through the exact
profile-coordinate homeomorphism. The parameter z records that one excluded
real item; no valuation for it or continuously chosen dummy labels is needed.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology FairDivision.Topology.NerveConnectivity

/-- Reuse the already proved general stock theorem at total apq−z. -/
theorem localStock_nullConnected {p a q m d z:ℕ}
    (ha:0<a) (hq:2≤q) (hz:z<p) (E:Finset (Fin m))
    (hTotal:E.card+d+z=(a*p)*q) (hD:d≤a*p):
    NullConnectedSet (p-z-1) (simplicialRealization (localStockComplex p a q m E d)):=by
  have hReq:p*(a*q-1)+p=(a*p)*q:=by
    have hAq:1≤a*q:=by have h:=Nat.mul_pos ha (by omega:0<q);omega
    calc
      p*(a*q-1)+p=p*((a*q-1)+1):=by ring
      _=p*(a*q):=by rw [Nat.sub_add_cancel hAq]
      _=(a*p)*q:=by ring
  have hUseful:variableUsefulDummyTotal (fun _:Fin p=>a*q-1) (fun _=>a)=a*p:=by
    simp [variableUsefulDummyTotal,variableUniform_useful_at a q ha hq,Nat.mul_comm]
  have hRequirement:variableRequirementTotal (fun _:Fin p=>a*q-1)=p*(a*q-1):=by
    simp [variableRequirementTotal]
  have hAd:VariableSlackAdmissible
      ((E.map (realEmbedding m d)).card) ((dummyLabels m d).card)
      (fun _:Fin p=>a*q-1) (fun _=>a):=by
    unfold VariableSlackAdmissible
    rw [Finset.card_map,card_dummyLabels,hUseful,hRequirement,Nat.min_eq_left hD]
    omega
  have hSlack:variableSlack
      ((E.map (realEmbedding m d)).card) ((dummyLabels m d).card)
      (fun _:Fin p=>a*q-1) (fun _=>a)=p-z:=by
    unfold variableSlack
    rw [Finset.card_map,card_dummyLabels,hUseful,hRequirement,Nat.min_eq_left hD]
    omega
  have hConnected:=variableStock_nullConnected_of_binaryGluing
    (by intro D r c;exact operationalBinaryGluing_of_openCover)
    (dummyLabels m d) (E.map (realEmbedding m d))
    (fun _:Fin p=>a*q-1) (fun _=>a) (realImage_disjoint_dummies E)
    hAd (by rw [hSlack];omega)
  simpa only [hSlack,localStockComplex] using hConnected

/-- Exact existing stock connectivity, in the common profile coordinates. -/
theorem availableAuxiliary_nullConnected {p a q m d z:ℕ}
    (ha:0<a) (hq:2≤q) (hz:z<p) (E:Finset (Fin m))
    (hTotal:E.card+d+z=(a*p)*q) (hD:d≤a*p):
    NullConnectedSet (p-z-1)
      (simplicialRealization (availableAuxiliaryComplex p a q m E d)):=by
  have hLocal:=localStock_nullConnected ha hq hz E hTotal hD
  exact NullConnectedSpace.ofHomotopyEquiv (stockProfileHomeomorph E hLocal.1).toHomotopyEquiv hLocal

/-- Vertex maps need only p−2 connectivity, with one unavailable real item. -/
theorem availableVertex_nullConnected {p a q m:ℕ}
    (hp:2≤p) (ha:0<a) (hq:2≤q) (b:Vertex (a*p) q m):
    NullConnectedSet (p-2)
      (simplicialRealization (availableAuxiliaryComplex p a q m (real b) (dummyCount b))):=by
  have hPos:0<(a*p)*q:=Nat.mul_pos (Nat.mul_pos ha (by omega)) (by omega)
  have hTotal:(real b).card+dummyCount b+1=(a*p)*q:=by
    have h:=vertex_card b
    omega
  have h:=availableAuxiliary_nullConnected ha hq (by omega:1<p) (real b) hTotal (dummyCount_le b)
  simpa only [Nat.sub_sub] using h

/-- Full edge stocks use the stronger p−1 bound needed for a homotopy. -/
theorem availableEdge_nullConnected {p a q m:ℕ}
    (hp:2≤p) (ha:0<a) (hq:2≤q) (E:Finset (Fin m)) (d:ℕ)
    (hTotal:E.card+d=(a*p)*q) (hD:d≤a*p):
    NullConnectedSet (p-1)
      (simplicialRealization (availableAuxiliaryComplex p a q m E d)):=by
  simpa only [Nat.sub_zero] using availableAuxiliary_nullConnected ha hq
    (by omega:0<p) E (by simpa only [Nat.add_zero] using hTotal) hD

end FairDivision.BF.Recording
