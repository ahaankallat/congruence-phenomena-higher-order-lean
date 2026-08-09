import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.GeneralizedConnectivity
import CongruenceTheoryHigherOrder.GeneralizedConnectivityTransport
import CongruenceTheoryHigherOrder.A3Final

/-!
**`genPiOf g = ⊤` iff `g`'s cycle-support graph is fully connected**, and this transports along
any index-relabeling equivalence. The key remaining building block toward (A4)'s local/global
connectivity comparison.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {q : ℕ}

theorem genPiOf_eq_top_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (g : Equiv.Perm (ι × Fin q)) :
    genPiOf g = (⊤ : GenPartLat ι) ↔ ∀ a b : ι, (genGraphOf g).Reachable a b := by
  constructor
  · intro htop a b
    have hmem : (genPiOf g).part a ∈ (genPiOf g).parts :=
      (genPiOf g).part_mem.mpr (Finset.mem_univ a)
    have hparts_eq : (genPiOf g).parts = (⊤ : GenPartLat ι).parts := congrArg Finpartition.parts htop
    rw [hparts_eq] at hmem
    have hsub' : (genPiOf g).part a ∈ ({Finset.univ} : Finset (Finset ι)) :=
      Finpartition.parts_top_subset (Finset.univ : Finset ι) hmem
    rw [Finset.mem_singleton] at hsub'
    have hbmem : b ∈ (genPiOf g).part a := hsub'.symm ▸ Finset.mem_univ b
    exact Finpartition.mem_part_ofSetoid_iff_rel.mp hbmem
  · intro hreach
    apply le_antisymm le_top
    intro p hp
    obtain ⟨a0, ha0⟩ := (⊤ : GenPartLat ι).nonempty_of_mem_parts hp
    refine ⟨(genPiOf g).part a0, (genPiOf g).part_mem.mpr (Finset.mem_univ a0), ?_⟩
    intro x _
    exact Finpartition.mem_part_ofSetoid_iff_rel.mpr (hreach a0 x)

/-- **`genPiOf g = ⊤` transports along any index-relabeling equivalence.** -/
theorem genPiOf_top_permCongr_iff {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι ≃ ι') (g : Equiv.Perm (ι × Fin q)) :
    genPiOf ((e.prodCongr (Equiv.refl (Fin q))).permCongr g) = (⊤ : GenPartLat ι') ↔
      genPiOf g = (⊤ : GenPartLat ι) := by
  rw [genPiOf_eq_top_iff, genPiOf_eq_top_iff]
  constructor
  · intro h a b
    exact (genGraphOf_reachable_permCongr_iff e g a b).mp (by simpa using h (e a) (e b))
  · intro h a' b'
    obtain ⟨a, rfl⟩ := e.surjective a'
    obtain ⟨b, rfl⟩ := e.surjective b'
    exact (genGraphOf_reachable_permCongr_iff e g a b).mpr (h a b)

end CongruenceTheory
