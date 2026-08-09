import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.GeneralizedConnectivity
import CongruenceTheoryHigherOrder.GeneralizedConnectivityTransport
import CongruenceTheoryHigherOrder.GeneralizedConnectivityTop
import CongruenceTheoryHigherOrder.GeneralizedPartitionGluing
import CongruenceTheoryHigherOrder.GeneralizedAssembleTop
import CongruenceTheoryHigherOrder.GeneralizedPiOfAssemble
import CongruenceTheoryHigherOrder.GeneralizedGfunTopK
import CongruenceTheoryHigherOrder.GeneralizedGfunProd
import CongruenceTheoryHigherOrder.MacroMicroRelabel
import CongruenceTheoryHigherOrder.MacroMicroReach
import CongruenceTheoryHigherOrder.A3Final

/-!
**The "touches-via-partition" hypergraph**: for a microblock partition `τ'` of `Fin r × Fin Q`,
builds the induced graph `H` on macroblocks `Fin r` (`i ∼ j` iff some part of `τ'` touches both),
and shows macroblock `⊤`-connectivity matches `H` being connected — the key remaining mechanism
for (A4)'s concrete instantiation.
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {r Q p : ℕ}

/-- Macroblocks `i, j` are touched by a common part of the microblock partition `τ'`. -/
def partTouches (τ' : GenPartLat (Fin r × Fin Q)) (i j : Fin r) : Prop :=
  ∃ C ∈ τ'.parts, (∃ mb ∈ C, mb.1 = i) ∧ (∃ mb ∈ C, mb.1 = j)

noncomputable instance (τ' : GenPartLat (Fin r × Fin Q)) : DecidableRel (partTouches τ') :=
  Classical.decRel _

/-- The induced hypergraph-connectivity graph on macroblocks. -/
def partGraphOf (τ' : GenPartLat (Fin r × Fin Q)) : SimpleGraph (Fin r) :=
  SimpleGraph.fromRel (partTouches τ')

/-- A part touching two macroblocks forces them macroblock-reachable, via the (already-proven)
fact that same-part microblocks are micro-reachable, hence macro-reachable. -/
theorem genGraphOf_reachable_of_partTouches {g : Equiv.Perm (Fin r × Fin (Q * p))} {i j : Fin r}
    (h : partTouches (genPiOf ((macroMicroEquiv r Q p).permCongr g)) i j) :
    (genGraphOf g).Reachable i j := by
  obtain ⟨C, hC, ⟨mb1, hmb1C, hmb1i⟩, ⟨mb2, hmb2C, hmb2j⟩⟩ := h
  set g' := (macroMicroEquiv r Q p).permCongr g with hg'_def
  have hreach : (genGraphOf g').Reachable mb1 mb2 := by
    have hmem : mb2 ∈ (genPiOf g').part mb1 := by
      rw [(genPiOf g').part_eq_of_mem hC hmb1C]
      exact hmb2C
    exact Finpartition.mem_part_ofSetoid_iff_rel.mp hmem
  have := genGraphOf_reachable_macro_of_micro_adj (g := g) hreach
  rwa [hmb1i, hmb2j] at this

/-- `H := partGraphOf τ'` reachability implies macroblock reachability. -/
theorem genGraphOf_reachable_of_partGraphOf_reachable {g : Equiv.Perm (Fin r × Fin (Q * p))}
    {i j : Fin r}
    (h : (partGraphOf (genPiOf ((macroMicroEquiv r Q p).permCongr g))).Reachable i j) :
    (genGraphOf g).Reachable i j := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    refine ih.trans ?_
    unfold partGraphOf at hbc
    rw [SimpleGraph.fromRel_adj] at hbc
    rcases hbc.2 with h1 | h2
    · exact genGraphOf_reachable_of_partTouches h1
    · exact (genGraphOf_reachable_of_partTouches h2).symm

/-- Macroblock reachability implies `H := partGraphOf τ'` reachability (the harder direction):
one macro-touching step is witnessed by a micro-*adjacent* pair, which is a fortiori
micro-*reachable*, hence lies in a common `τ'`-part. -/
theorem partGraphOf_reachable_of_genGraphOf_reachable {g : Equiv.Perm (Fin r × Fin (Q * p))}
    {i j : Fin r} (h : (genGraphOf g).Reachable i j) :
    (partGraphOf (genPiOf ((macroMicroEquiv r Q p).permCongr g))).Reachable i j := by
  set g' := (macroMicroEquiv r Q p).permCongr g with hg'_def
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    refine ih.trans ?_
    unfold genGraphOf at hbc
    rw [SimpleGraph.fromRel_adj] at hbc
    have hstep : partTouches (genPiOf g') b c ∨ partTouches (genPiOf g') c b := by
      have hmk : ∀ {x y : Fin r}, genTouches g x y →
          partTouches (genPiOf g') x y := by
        intro x y hxy
        obtain ⟨mb1, mb2, hmb1, hmb2, hmicro⟩ := (genTouches_macro_iff_micro' g x y).mp hxy
        by_cases hmeq : mb1 = mb2
        · exact ⟨(genPiOf g').part mb1, (genPiOf g').part_mem.mpr (Finset.mem_univ mb1),
            ⟨mb1, (genPiOf g').mem_part_self.mpr (Finset.mem_univ mb1), hmb1⟩,
            ⟨mb1, (genPiOf g').mem_part_self.mpr (Finset.mem_univ mb1), by rw [hmeq]; exact hmb2⟩⟩
        · refine ⟨(genPiOf g').part mb1, (genPiOf g').part_mem.mpr (Finset.mem_univ mb1),
            ⟨mb1, (genPiOf g').mem_part_self.mpr (Finset.mem_univ mb1), hmb1⟩, ⟨mb2, ?_, hmb2⟩⟩
          have hadj : (genGraphOf g').Adj mb1 mb2 := by
            unfold genGraphOf
            rw [SimpleGraph.fromRel_adj]
            exact ⟨hmeq, Or.inl hmicro⟩
          exact Finpartition.mem_part_ofSetoid_iff_rel.mpr hadj.reachable
      rcases hbc.2 with h1 | h2
      · exact Or.inl (hmk h1)
      · exact Or.inr (hmk h2)
    rcases hstep with h1 | h2
    · exact SimpleGraph.Adj.reachable (by
        unfold partGraphOf; rw [SimpleGraph.fromRel_adj]; exact ⟨hbc.1, Or.inl h1⟩)
    · exact SimpleGraph.Adj.reachable (by
        unfold partGraphOf; rw [SimpleGraph.fromRel_adj]; exact ⟨hbc.1, Or.inr h2⟩)

/-- **Macroblock `⊤`-connectivity matches `H := partGraphOf τ'` being connected.** -/
theorem genPiOf_macro_eq_top_iff_partGraphOf_connected {g : Equiv.Perm (Fin r × Fin (Q * p))} :
    genPiOf g = (⊤ : GenPartLat (Fin r)) ↔
      ∀ i j : Fin r, (partGraphOf (genPiOf ((macroMicroEquiv r Q p).permCongr g))).Reachable i j := by
  rw [genPiOf_eq_top_iff]
  constructor
  · intro h i j
    exact partGraphOf_reachable_of_genGraphOf_reachable (h i j)
  · intro h i j
    exact genGraphOf_reachable_of_partGraphOf_reachable (h i j)

end CongruenceTheory
