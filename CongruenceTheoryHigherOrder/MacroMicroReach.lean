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
import CongruenceTheoryHigherOrder.A3Final

/-!
**Macroblock touches, restated at microblock-index level, and lifted to reachability.**
-/

namespace CongruenceTheory

open Equiv

open scoped Classical

variable {r Q p : ℕ}

/-- `genTouches_macro_iff_micro`, restated with the witness at microblock-*index* level
(`Fin r × Fin Q`) rather than point level. -/
theorem genTouches_macro_iff_micro' (g : Equiv.Perm (Fin r × Fin (Q * p))) (i j : Fin r) :
    genTouches g i j ↔ ∃ mb1 mb2 : Fin r × Fin Q, mb1.1 = i ∧ mb2.1 = j ∧
      genTouches ((macroMicroEquiv r Q p).permCongr g) mb1 mb2 := by
  rw [genTouches_macro_iff_micro]
  constructor
  · rintro ⟨y, hy1, hy2⟩
    exact ⟨y.1, ((macroMicroEquiv r Q p).permCongr g) y |>.1, hy1, hy2, ⟨y, rfl, rfl⟩⟩
  · rintro ⟨mb1, mb2, hmb1, hmb2, z, hz1, hz2⟩
    exact ⟨z, hz1 ▸ hmb1, hz2 ▸ hmb2⟩

/-- Macroblock reachability implies "coarsened" reachability: there exist microblock lifts
`mb1, mb2` of `i, j`, and a *sequence* of macroblock-touching steps (built from the microblock
graph's adjacency) connecting them, in particular `Prod.fst`-image reachability in the microblock
graph, coarsened by projection. Concretely: reachability transports along the projection
`Prod.fst : Fin r × Fin Q → Fin r`, from the microblock graph to a "coarsened" graph on `Fin r`
whose adjacency is `∃` a microblock-adjacent lift. -/
theorem genGraphOf_reachable_macro_of_micro_adj {g : Equiv.Perm (Fin r × Fin (Q * p))}
    {mb1 mb2 : Fin r × Fin Q}
    (h : (genGraphOf ((macroMicroEquiv r Q p).permCongr g)).Reachable mb1 mb2) :
    (genGraphOf g).Reachable mb1.1 mb2.1 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    rcases eq_or_ne b.1 c.1 with heq | hne
    · rwa [heq] at ih
    · refine ih.trans (SimpleGraph.Adj.reachable ?_)
      unfold genGraphOf
      rw [SimpleGraph.fromRel_adj]
      refine ⟨hne, ?_⟩
      unfold genGraphOf at hbc
      rw [SimpleGraph.fromRel_adj] at hbc
      rcases hbc.2 with h1 | h2
      · left; exact (genTouches_macro_iff_micro' g b.1 c.1).mpr ⟨b, c, rfl, rfl, h1⟩
      · right; exact (genTouches_macro_iff_micro' g c.1 b.1).mpr ⟨c, b, rfl, rfl, h2⟩

end CongruenceTheory
