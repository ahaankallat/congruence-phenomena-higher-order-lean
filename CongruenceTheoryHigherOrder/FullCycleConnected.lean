import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount

/-!
**A full-support cycle is always macroblock-connected.** One building block toward (A3)'s
combinatorial claim ("the coefficient of `X_{jp}` in `K_j(p)` is `(jp-1)!`," needed to connect
the already-proven Legendre's-formula identity `LegendreA3.lean` to the actual `K` polynomial):
since `ci g` is a *single* monomial, the coefficient of `X_{jp}` in `K_j(p) = Gfun ⊤` (via
`K_eq_Gfun_top`) counts exactly the permutations `g` with `piOf g = ⊤` *and* `ci g = X_{jp}`
(i.e. a single full `jp`-cycle). This file shows the `piOf g = ⊤` condition is *automatic* for
full cycles — so the count reduces to "how many full `jp`-cycles are there," a separate,
self-contained combinatorial count (not attempted here).
-/

namespace CongruenceTheory

open Equiv Classical

variable {r q : ℕ}

theorem piOf_eq_top_of_isCycle_of_support_eq_univ {g : Equiv.Perm (Fin r × Fin q)}
    (hcyc : g.IsCycle) (hsupp : g.support = Finset.univ) : piOf g = (⊤ : PartLat r) := by
  have hmoves : ∀ x : Fin r × Fin q, g x ≠ x := by
    intro x
    have : x ∈ g.support := hsupp ▸ Finset.mem_univ x
    exact (Equiv.Perm.mem_support.mp this)
  have hreach_step : ∀ x : Fin r × Fin q, (graphOf g).Reachable x.1 (g x).1 := by
    intro x
    by_cases heq : x.1 = (g x).1
    · rw [heq]
    · exact SimpleGraph.Adj.reachable
        (SimpleGraph.fromRel_adj (touches (q := q) g) _ _ |>.mpr ⟨heq, Or.inl ⟨x, rfl, rfl⟩⟩)
  have hreach_pow : ∀ (x0 : Fin r × Fin q) (k : ℕ), (graphOf g).Reachable x0.1 ((g ^ k) x0).1 := by
    intro x0 k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : (graphOf g).Reachable ((g ^ k) x0).1 (g ((g ^ k) x0)).1 := hreach_step _
      have hpoweq : (g ^ (k + 1)) x0 = g ((g ^ k) x0) := by
        rw [pow_succ']; rfl
      rw [hpoweq]
      exact ih.trans hstep
  have hcyc' := hcyc
  obtain ⟨x0, hx0, -⟩ := hcyc'
  have hreach_all : ∀ y : Fin r × Fin q, (graphOf g).Reachable x0.1 y.1 := by
    intro y
    obtain ⟨k, hk⟩ := hcyc.exists_pow_eq hx0 (hmoves y)
    rw [← hk]
    exact hreach_pow x0 k
  have hpart_x0 : (piOf g).part x0.1 = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    obtain ⟨y, hy⟩ : ∃ y : Fin r × Fin q, y.1 = j := ⟨(j, x0.2), rfl⟩
    have hreach : (graphOf g).Reachable x0.1 j := hy ▸ hreach_all y
    exact Finpartition.mem_part_ofSetoid_iff_rel.mpr hreach
  have htop_le : (⊤ : PartLat r) ≤ piOf g := by
    intro p _
    refine ⟨(piOf g).part x0.1, (piOf g).part_mem.mpr (Finset.mem_univ x0.1), ?_⟩
    rw [hpart_x0]
    exact Finset.subset_univ p
  exact le_antisymm le_top htop_le

#print axioms piOf_eq_top_of_isCycle_of_support_eq_univ

end CongruenceTheory
