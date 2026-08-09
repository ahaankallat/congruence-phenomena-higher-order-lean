import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aBlockPermutation
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentHom
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**Orbit-stabilizer at the component level, for an arbitrary subgroup `A'` fixing block `u`
setwise.** `componentHom` lets `A'` act on `BlockComponent V g u` via `MulAction.compHom`;
`nat_card_orbit_mul_stabilizer` then bounds `Nat.card A'` by the orbit size of any component `c1`
times the stabilizer's cardinality — the mechanism for (A2a)'s cut-vertex case's remaining
rooted-isomorphism-type branches: the *orbit* of `c1` under the leftover kernel is exactly the set
of components isomorphic to `c1` that the kernel can swap it with (multiplicity `m_τ`), and the
*stabilizer* is what's left to peel `c1`'s own attachment/block factor from, via
`card_le_ambientAttach_mul_card_ptStab_of_component_fixed`.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- `A'` acts on `BlockComponent V g u` via `componentHom`. -/
noncomputable def componentMulAction {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) :
    MulAction ↥A' (BlockComponent V g u) :=
  MulAction.compHom _ (componentHom hpart hne hcent' hperm' hblock_u')

theorem componentMulAction_smul_eq {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (ψ : ↥A') (c : BlockComponent V g u) :
    letI := componentMulAction hpart hne hcent' hperm' hblock_u'
    ψ • c = componentHom hpart hne hcent' hperm' hblock_u' ψ c := rfl

/-- The ambient re-embedding of the stabilizer, under `componentMulAction`, of a component `c1`. -/
noncomputable def StabAmbient {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (c1 : BlockComponent V g u) :
    Subgroup (Equiv.Perm Ω) :=
  letI := componentMulAction hpart hne hcent' hperm' hblock_u'
  (MulAction.stabilizer ↥A' c1).map A'.subtype

theorem card_stabAmbient {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (c1 : BlockComponent V g u) :
    letI := componentMulAction hpart hne hcent' hperm' hblock_u'
    Nat.card (StabAmbient hpart hne hcent' hperm' hblock_u' c1) =
      Nat.card (MulAction.stabilizer ↥A' c1) := by
  letI := componentMulAction hpart hne hcent' hperm' hblock_u'
  unfold StabAmbient
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective _ _ A'.subtype_injective).symm.toEquiv

theorem stabAmbient_le {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (c1 : BlockComponent V g u) :
    StabAmbient hpart hne hcent' hperm' hblock_u' c1 ≤ A' := by
  letI := componentMulAction hpart hne hcent' hperm' hblock_u'
  unfold StabAmbient
  rintro ψ ⟨φ, -, rfl⟩
  exact φ.2

/-- The defining property of `StabAmbient`: every element's component-permutation fixes `c1`. -/
theorem stabAmbient_fixes_component {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (c1 : BlockComponent V g u) (φ : Equiv.Perm Ω)
    (hφ : φ ∈ StabAmbient hpart hne hcent' hperm' hblock_u' c1) :
    componentPermOfMem hpart hne hcent' hperm' (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1
      hφ) (hblock_u' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ)) c1 = c1 := by
  letI := componentMulAction hpart hne hcent' hperm' hblock_u'
  obtain ⟨ψ, hψstab, rfl⟩ := hφ
  have := MulAction.mem_stabilizer_iff.mp hψstab
  rwa [componentMulAction_smul_eq] at this

/-- **Orbit-stabilizer at the component level.** -/
theorem card_eq_orbit_mul_stabAmbient {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (c1 : BlockComponent V g u) :
    letI := componentMulAction hpart hne hcent' hperm' hblock_u'
    Nat.card A' = Nat.card (MulAction.orbit ↥A' c1) *
      Nat.card (StabAmbient hpart hne hcent' hperm' hblock_u' c1) := by
  letI := componentMulAction hpart hne hcent' hperm' hblock_u'
  rw [card_stabAmbient hpart hne hcent' hperm' hblock_u' c1]
  exact (nat_card_orbit_mul_stabilizer c1).symm
