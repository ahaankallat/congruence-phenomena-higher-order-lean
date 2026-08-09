import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aBlockPermutation
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The component-permutation `MonoidHom`.** Bundles `componentPermOfMem` (which already has its
composition law `componentPermOfMem_mul`) into a genuine
`componentHom : A →* Equiv.Perm(BlockComponent V g u)` — needed to apply orbit-stabilizer at the
*component* level for (A2a)'s cut-vertex case's remaining rooted-isomorphism-type branches: after
peeling the distinguished component `C_0`, the leftover kernel still acts on the *other*
components by permuting them (potentially swapping isomorphic branches), and this action's orbits
are exactly the "rooted-isomorphism types `τ`" with multiplicity `m_τ` the orbit size.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

theorem componentPermOfMem_one {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hu1 : (V u).image (1 : Equiv.Perm Ω) = V u) :
    componentPermOfMem hpart hne hcent hperm (Subgroup.one_mem A) hu1 = 1 := by
  apply Equiv.ext
  intro c
  refine Quot.inductionOn c (fun x => ?_)
  show componentPermOfMem hpart hne hcent hperm (Subgroup.one_mem A) hu1 (Quot.mk _ x) =
    Quot.mk _ x
  rw [componentPermOfMem_mk]
  congr 1
  apply Subtype.ext
  rw [blockPermSub_coe]
  exact blockOfElt_one hpart hne hperm (Subgroup.one_mem A) x.1

/-- The component-permutation `MonoidHom`, given `A` fixes block `u` setwise. -/
noncomputable def componentHom {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) :
    ↥A →* Equiv.Perm (BlockComponent V g u) where
  toFun φ := componentPermOfMem hpart hne hcent hperm φ.2 (hblock_u φ.1 φ.2)
  map_one' := componentPermOfMem_one hpart hne hcent hperm (hblock_u 1 (Subgroup.one_mem A))
  map_mul' a b := componentPermOfMem_mul hpart hne hcent hperm b.2 a.2 (hblock_u b.1 b.2)
    (hblock_u a.1 a.2) (hblock_u (a.1 * b.1) (A.mul_mem a.2 b.2))

theorem componentHom_apply {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) (φ : ↥A) :
    componentHom hpart hne hcent hperm hblock_u φ =
      componentPermOfMem hpart hne hcent hperm φ.2 (hblock_u φ.1 φ.2) := rfl
