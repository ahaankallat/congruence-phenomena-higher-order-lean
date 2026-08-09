import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexFixesC0
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPermMul
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**`g` restricted to the island, and that the island permutation commutes with it.** This supplies
the `hcent` hypothesis `card_le_root_bound` will eventually need for the smaller, self-contained
island instance.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- `g` restricted to the island. -/
noncomputable def islandG {V : ι → Finset Ω} (hpart : IsPartition V) (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) : Equiv.Perm {x : Ω // InComponentPlus g u c0 x} :=
  g.subtypePerm (fun x => (inComponentPlus_iff hpart x).symm)

theorem islandG_coe {V : ι → Finset Ω} (hpart : IsPartition V) (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) (x : {x : Ω // InComponentPlus g u c0 x}) :
    (islandG hpart g u c0 x : Ω) = g x.1 := rfl

/-- The island permutation commutes with the island's own `g`, since restriction preserves
commutation. -/
theorem islandPermOfPtStab_commute {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) (φ : Equiv.Perm Ω) (hφ : φ ∈ PtStab A p₀) :
    Commute (islandPermOfPtStab hpart hne hcent hperm hblock_u hreach φ hφ)
      (islandG hpart g u c0) := by
  have hφA : φ ∈ A := (mem_PtStab.mp hφ).1
  have hcommute : ∀ y : Ω, φ (g y) = g (φ y) := fun y => by
    have h := congrArg (fun e : Equiv.Perm Ω => e y) (hcent φ hφA)
    simpa [Equiv.Perm.mul_apply] using h
  apply Equiv.ext
  intro x
  apply Subtype.ext
  show (islandPermOfPtStab hpart hne hcent hperm hblock_u hreach φ hφ
      (islandG hpart g u c0 x) : Ω) =
    (islandG hpart g u c0 (islandPermOfPtStab hpart hne hcent hperm hblock_u hreach φ hφ x) : Ω)
  rw [islandPermOfPtStab_coe, islandG_coe, islandG_coe, islandPermOfPtStab_coe]
  exact hcommute x.1
