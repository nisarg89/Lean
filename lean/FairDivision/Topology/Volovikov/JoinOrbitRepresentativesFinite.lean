import FairDivision.Topology.Volovikov.JoinOrbitPastedMap

/-!
# Finite orbit representatives at one join-skeleton level

The vertices and group are finite, so each fixed-cardinality layer has
finitely many free face orbits. One chosen representative per orbit gives the
finite induction index for equivariant cell attachment.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open scoped Classical

/-- The finite set of chosen orbit representatives of join faces with
`d + 1` vertices. -/
noncomputable def newJoinOrbitRepresentatives
    (m d : ℕ) (G : Type*) [AddGroup G] [Fintype G] :
    Finset (UniversalJoinFace m G) := by
  classical
  exact (Finset.univ.filter
    (fun S : UniversalJoinFace m G => S.1.card = d + 1)).image
      universalJoinFaceOrbitRep

/-- A fixed-cardinality face's canonical representative occurs in the
finite representative list. -/
theorem orbitRep_mem_newJoinOrbitRepresentatives
    {m d : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (S : UniversalJoinFace m G) (hcard : S.1.card = d + 1) :
    universalJoinFaceOrbitRep S ∈ newJoinOrbitRepresentatives m d G := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨S, ?_, rfl⟩
  simp [newJoinOrbitRepresentatives, hcard]

/-- Every face at the new cardinality is a translate of a listed
representative. -/
theorem newJoinFace_from_representative
    {m d : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (S : UniversalJoinFace m G) (hcard : S.1.card = d + 1) :
    ∃ R ∈ newJoinOrbitRepresentatives m d G,
      ∃ a : G, translateJoinFace a R.1 = S.1 := by
  exact ⟨universalJoinFaceOrbitRep S,
    orbitRep_mem_newJoinOrbitRepresentatives S hcard,
    universalJoinFaceTranslator S, universalJoinFaceTranslator_spec S⟩

/-- Listed representatives have the declared face cardinality. -/
theorem newJoinOrbitRepresentative_card
    {m d : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    {R : UniversalJoinFace m G}
    (hR : R ∈ newJoinOrbitRepresentatives m d G) :
    R.1.card = d + 1 := by
  classical
  obtain ⟨S, hS, hSR⟩ := Finset.mem_image.mp hR
  have hcard : S.1.card = d + 1 :=
    (Finset.mem_filter.mp hS).2
  rw [← hSR, universalJoinFaceOrbitRep_card, hcard]

end FairDivision.Topology.Volovikov
