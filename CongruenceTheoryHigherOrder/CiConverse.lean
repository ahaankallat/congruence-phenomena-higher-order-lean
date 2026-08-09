import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.FullCycleConnected
import CongruenceTheoryHigherOrder.CiFullCycle

/-!
**The converse of `ci_eq_X_of_isCycle_of_support_eq_univ`**: if a permutation's cycle-indicator
monomial is a *bare* variable `X n` with `n ≥ 2`, the permutation must be a full `n`-cycle. The
third building block toward (A3)'s combinatorial claim, completing the exact characterization
`ci g = X n ↔ g.IsCycle ∧ g.support = Finset.univ` (for `n ≥ 2`; the `n = 1` case is genuinely
different, matching a single *fixed point*, not a cycle — irrelevant to the manuscript's
application since there `n = jp` for a prime `p ≥ 2`).
-/

namespace CongruenceTheory

open Equiv MvPolynomial

/-- **A product of `X`-monomials over a multiset is the monomial at the multiset's own count
Finsupp.** -/
theorem multiset_map_X_prod_eq_monomial (m : Multiset ℕ) :
    (m.map (X : ℕ → MvPolynomial ℕ ℤ)).prod = monomial (Multiset.toFinsupp m) (1 : ℤ) := by
  induction m using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, Multiset.toFinsupp_zero,
      congrFun monomial_zero' (1 : ℤ), C_1]
  | cons a m ih =>
    have hcons : (a ::ₘ m) = {a} + m := by simp
    rw [Multiset.map_cons, Multiset.prod_cons, ih, hcons, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton]
    rw [show (X a : MvPolynomial ℕ ℤ) = monomial (Finsupp.single a 1) (1 : ℤ) from rfl,
      monomial_mul, mul_one]

/-- **The converse characterization**: a permutation whose cycle-indicator monomial is a bare
`X n` (`n ≥ 2`) is a full `n`-cycle. -/
theorem isCycle_and_support_eq_univ_of_ci_eq_X {r q n : ℕ} {g : Equiv.Perm (Fin r × Fin q)}
    (hn : 2 ≤ n) (h : ci g = X n) : g.IsCycle ∧ g.support = Finset.univ := by
  unfold ci at h
  rw [X_pow_eq_monomial, multiset_map_X_prod_eq_monomial, monomial_mul, mul_one,
    show (X n : MvPolynomial ℕ ℤ) = monomial (Finsupp.single n 1) (1 : ℤ) from rfl] at h
  rw [monomial_eq_monomial_iff] at h
  have heq : Finsupp.single 1 (Fintype.card (Fin r × Fin q) - g.cycleType.sum) +
      g.cycleType.toFinsupp = Finsupp.single n 1 := by
    rcases h with ⟨he, -⟩ | ⟨hz, -⟩
    · exact he
    · norm_num at hz
  have h1notin : (1 : ℕ) ∉ g.cycleType := by
    intro hmem
    have := Equiv.Perm.two_le_of_mem_cycleType hmem
    omega
  have hcount1 : g.cycleType.toFinsupp 1 = 0 := by
    rw [Multiset.toFinsupp_apply]
    exact Multiset.count_eq_zero_of_notMem h1notin
  have hat1 := DFunLike.congr_fun heq 1
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, hcount1, add_zero] at hat1
  have hn1 : n ≠ 1 := by omega
  rw [Finsupp.single_apply, if_neg hn1] at hat1
  have hsingle0 : Finsupp.single (1 : ℕ) (Fintype.card (Fin r × Fin q) - g.cycleType.sum) = 0 := by
    rw [hat1]; exact Finsupp.single_zero 1
  rw [hsingle0, zero_add] at heq
  rw [← Multiset.toFinsupp_singleton n] at heq
  have hct : g.cycleType = {n} := Multiset.toFinsupp.injective heq
  have hcard1 : Multiset.card g.cycleType = 1 := by rw [hct]; simp
  have hiscyc : g.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp hcard1
  have hsum : g.cycleType.sum = n := by rw [hct]; simp
  have hsupcard : g.support.card = n := by rw [← Equiv.Perm.sum_cycleType, hsum]
  have hle : g.cycleType.sum ≤ Fintype.card (Fin r × Fin q) := g.sum_cycleType_le
  have hcardeq : Fintype.card (Fin r × Fin q) = n := by omega
  have hsupp : g.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hsupcard, hcardeq]
  exact ⟨hiscyc, hsupp⟩

#print axioms isCycle_and_support_eq_univ_of_ci_eq_X

end CongruenceTheory
