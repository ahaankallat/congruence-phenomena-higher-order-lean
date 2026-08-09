import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexFixesC0
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The island permutation of `PtStab A p₀`**, packaging `inComponentPlus_apply_of_fixes` into a
genuine `Equiv.Perm` of `p₀`'s island (`{x // InComponentPlus g u c0 x}`) for each
`φ ∈ PtStab A p₀`. This is the object the restriction homomorphism (next) will be built from,
letting `card_le_root_bound` eventually be applied to its image to get (A2a)'s per-component
cut-vertex factor.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The permutation of `p₀`'s island induced by `φ ∈ PtStab A p₀`. -/
noncomputable def islandPermOfPtStab {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) (φ : Equiv.Perm Ω) (hφ : φ ∈ PtStab A p₀) :
    Equiv.Perm {x : Ω // InComponentPlus g u c0 x} :=
  have hφA : φ ∈ A := (mem_PtStab.mp hφ).1
  have hφp₀ : φ p₀ = p₀ := (mem_PtStab.mp hφ).2
  have hφinv : φ⁻¹ ∈ PtStab A p₀ := (PtStab A p₀).inv_mem hφ
  have hφinvA : φ⁻¹ ∈ A := (mem_PtStab.mp hφinv).1
  have hφinvp₀ : φ⁻¹ p₀ = p₀ := (mem_PtStab.mp hφinv).2
  φ.subtypePerm (fun x =>
    Iff.intro
      (fun hgx => by
        have h := inComponentPlus_apply_of_fixes hpart hne hcent hperm hφinvA
          (hblock_u φ⁻¹ hφinvA) hφinvp₀ hreach hgx
        simpa using h)
      (inComponentPlus_apply_of_fixes hpart hne hcent hperm hφA (hblock_u φ hφA) hφp₀ hreach))
