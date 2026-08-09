import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.FullCycleConnected

/-!
**A full-support cycle's cycle-indicator monomial is the bare `X_{rq}`.** The second building
block toward (A3)'s combinatorial claim (alongside `FullCycleConnected.lean`'s
`piOf_eq_top_of_isCycle_of_support_eq_univ`): combined, these two show every full `rq`-cycle
`g : Equiv.Perm (Fin r × Fin q)` contributes to `Gfun ⊤`'s sum with exactly the monomial
`X (r*q)`, matching the manuscript's "the coefficient of `X_{jp}` in `K_j(p)` is `(jp-1)!`" claim
(with `r:=j`, `q:=p`) at the level of *which* monomial a full cycle contributes.
-/

namespace CongruenceTheory

open Equiv

theorem ci_eq_X_of_isCycle_of_support_eq_univ {r q : ℕ} {g : Equiv.Perm (Fin r × Fin q)}
    (hcyc : g.IsCycle) (hsupp : g.support = Finset.univ) : ci g = MvPolynomial.X (r * q) := by
  unfold ci
  have hct : g.cycleType = {r * q} := by
    rw [hcyc.cycleType, hsupp, Finset.card_univ]
    simp [Fintype.card_prod]
  rw [hct]
  simp

#print axioms ci_eq_X_of_isCycle_of_support_eq_univ

end CongruenceTheory
