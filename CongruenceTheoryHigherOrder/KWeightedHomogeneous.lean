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
import CongruenceTheoryHigherOrder.CiConverse
import CongruenceTheoryHigherOrder.FullCycleCount
import CongruenceTheoryHigherOrder.A3Final

/-!
**`K_r(q)` is weighted homogeneous of weighted degree `r*q`**, weighting each variable `X_k` by
`k` itself. This is the precise sense in which "`K_r(q)` is built from permutations of `r*q`
labelled points": every monomial `X_1^{a}\prod X_{\ell_i}` occurring in `ci g` for some
permutation `g` of an `rq`-point set satisfies `a+\sum \ell_i=rq` (the point count), and
`K_r(q)=\sum_{g:\pi(g)=\top}ci(g)` (`K_eq_Gfun_top`) is a sum of such terms, all of the same
weighted degree.

This is exactly the "total-degree grading" fact used informally in
`cor:triangular-independence`'s manuscript proof ("`z_m` cannot occur in `L_j` when `m>j`, since
`K_j(p)` is a sum over partitions of only `j` blocks") — formalized here as a clean, reusable,
self-contained fact about `K_r(q)` on its own, independent of the specialization it will later be
combined with.
-/

namespace CongruenceTheory

open MvPolynomial

/-- The weight of a multiset's Finsupp-of-multiplicities encoding equals the multiset's own sum
of weighted values. -/
theorem weight_toFinsupp {σ M : Type*} [DecidableEq σ] [AddCommMonoid M] (w : σ → M)
    (m : Multiset σ) : Finsupp.weight w m.toFinsupp = (m.map w).sum := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, map_add, Finsupp.weight_single, one_smul, ih]

/-- `ci g` is weighted homogeneous of weighted degree `Fintype.card α`, weighting `X_k` by `k`. -/
theorem isWeightedHomogeneous_ci {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    IsWeightedHomogeneous (fun k : ℕ => k) (ci g) (Fintype.card α) := by
  rw [ci_eq_monomial_toFinsupp]
  apply isWeightedHomogeneous_monomial
  rw [map_add, Finsupp.weight_single, smul_eq_mul, mul_one, weight_toFinsupp]
  have hle : g.cycleType.sum ≤ Fintype.card α := g.sum_cycleType_le
  have hmap : (g.cycleType.map (fun k : ℕ => k)).sum = g.cycleType.sum := by simp
  rw [hmap]
  omega

/-- **`K_r(q)` is weighted homogeneous of weighted degree `r*q`**, weighting `X_k` by `k`. -/
theorem isWeightedHomogeneous_K (r q : ℕ) :
    IsWeightedHomogeneous (fun k : ℕ => k) (K r q) (r * q) := by
  rw [K_eq_Gfun_top]
  unfold Gfun
  have hcard : Fintype.card (Fin r × Fin q) = r * q := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [← hcard]
  apply IsWeightedHomogeneous.sum
  intro g _
  exact isWeightedHomogeneous_ci g

#print axioms isWeightedHomogeneous_K

/-- **Variable `0` never occurs in `K_r(q)`**: `ci g`'s exponent vanishes at index `0`, since it
is built from index-`1` fixed points and cycle lengths `\ge2` only. Weighting index `0` by `1` and
everything else by `0` makes this a second weighted-homogeneity fact, of degree `0`. -/
theorem isWeightedHomogeneous_ci_zero {α : Type*} [Fintype α] [DecidableEq α]
    (g : Equiv.Perm α) :
    IsWeightedHomogeneous (fun k : ℕ => if k = 0 then (1 : ℕ) else 0) (ci g) 0 := by
  rw [ci_eq_monomial_toFinsupp]
  apply isWeightedHomogeneous_monomial
  rw [map_add, Finsupp.weight_single, weight_toFinsupp]
  simp only [if_neg (one_ne_zero), smul_eq_mul, mul_zero, zero_add]
  have hmap : g.cycleType.map (fun k : ℕ => if k = 0 then (1 : ℕ) else 0) =
      Multiset.replicate (Multiset.card g.cycleType) 0 := by
    rw [← Multiset.map_const' g.cycleType (0 : ℕ)]
    apply Multiset.map_congr rfl
    intro x hx
    have := Equiv.Perm.two_le_of_mem_cycleType hx
    rw [if_neg (by omega)]
  rw [hmap, Multiset.sum_replicate, smul_zero]

/-- **`K_r(q)`'s coefficient support never touches variable `0`.** -/
theorem isWeightedHomogeneous_K_zero (r q : ℕ) :
    IsWeightedHomogeneous (fun k : ℕ => if k = 0 then (1 : ℕ) else 0) (K r q) 0 := by
  rw [K_eq_Gfun_top]
  unfold Gfun
  apply IsWeightedHomogeneous.sum
  intro g _
  exact isWeightedHomogeneous_ci_zero g

end CongruenceTheory
