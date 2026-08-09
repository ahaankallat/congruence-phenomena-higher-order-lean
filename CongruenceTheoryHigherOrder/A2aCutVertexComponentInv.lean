import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentHom
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**`componentPermOfMem` respects inverses**, via `componentHom`'s `MonoidHom` structure (`map_inv`
is free for a hom between groups). Needed to invert "`φ` moves `c1` to `c2`" into "`φ⁻¹` moves `c2`
back to `c1`".
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

theorem componentPermOfMem_inv {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {φ : Equiv.Perm Ω} (hφ : φ ∈ A) :
    componentPermOfMem hpart hne hcent hperm (A.inv_mem hφ) (hblock_u φ⁻¹ (A.inv_mem hφ)) =
      (componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ))⁻¹ := by
  have h3 : componentHom hpart hne hcent hperm hblock_u (⟨φ, hφ⟩ : ↥A)⁻¹ =
      (componentHom hpart hne hcent hperm hblock_u ⟨φ, hφ⟩)⁻¹ := map_inv _ _
  have h1 := componentHom_apply hpart hne hcent hperm hblock_u (⟨φ, hφ⟩ : ↥A)⁻¹
  have h2 := componentHom_apply hpart hne hcent hperm hblock_u (⟨φ, hφ⟩ : ↥A)
  rw [h1, h2] at h3
  exact h3
