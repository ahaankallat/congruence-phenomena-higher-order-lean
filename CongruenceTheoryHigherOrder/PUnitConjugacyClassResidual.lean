import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PUnitConjugacyClass

/-!
**`thm:complete-prime-local`(iii)'s Sylow-subgroup witness, the "no-carry" (residual-cycle)
branch.** For `N=hp+s` with `2\le s<p`, there is a permutation `g\in S_N` with cycle type "`h`
disjoint `p`-cycles plus one further `s`-cycle" whose conjugacy class size in `S_N` is coprime to
`p` — the manuscript's "on the fixed points use at most one residual cycle." Mirrors
`not_dvd_card_isConj_replicate_cycleType`, folding in the extra `s`-cycle (itself a `p`-unit,
since `2\le s<p`).
-/

namespace CongruenceTheory

open Equiv.Perm Subgroup Nat

/-- **There is a permutation of `Fin N` with `h` disjoint `p`-cycles plus one `s`-cycle**,
`N=hp+s`, `2\le s<p`. -/
theorem exists_perm_replicate_add_singleton_cycleType {N p h s : ℕ} (hp : p.Prime)
    (hs2 : 2 ≤ s) (hspN : N = h * p + s) :
    ∃ g : Equiv.Perm (Fin N), g.cycleType = Multiset.replicate h p + {s} := by
  apply (exists_with_cycleType_iff (α := Fin N)).mpr
  refine ⟨?_, ?_⟩
  · rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, Multiset.sum_singleton,
      Fintype.card_fin, hspN]
  · intro a ha
    rw [Multiset.mem_add] at ha
    rcases ha with ha | ha
    · rw [Multiset.eq_of_mem_replicate ha]; exact hp.two_le
    · rw [Multiset.mem_singleton.mp ha]; exact hs2

/-- **The conjugacy class of a permutation of `Fin N` with `h\ge1` disjoint `p`-cycles plus one
`s`-cycle (`N=hp+s`, `2\le s<p`) has size coprime to `p`.** -/
theorem not_dvd_card_isConj_replicate_add_singleton_cycleType {N p h s : ℕ} (hp : p.Prime)
    (hh1 : 1 ≤ h) (hs2 : 2 ≤ s) (hslt : s < p) (hspN : N = h * p + s)
    {g : Equiv.Perm (Fin N)} (hg : g.cycleType = Multiset.replicate h p + {s}) :
    ¬ p ∣ Nat.card {x : Equiv.Perm (Fin N) | IsConj g x} := by
  haveI := Fact.mk hp
  have hcentral : Nat.card (centralizer {g}) =
      (Fintype.card (Fin N) - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!) :=
    Equiv.Perm.nat_card_centralizer g
  have hclasseq : Nat.card {x : Equiv.Perm (Fin N) | IsConj g x} *
      ((Fintype.card (Fin N) - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!)) = (Fintype.card (Fin N))! :=
    Equiv.Perm.card_isConj_mul_eq g
  rw [hg] at hclasseq
  have hsum : (Multiset.replicate h p + ({s} : Multiset ℕ)).sum = h * p + s := by
    rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, Multiset.sum_singleton]
  have hprod : (Multiset.replicate h p + ({s} : Multiset ℕ)).prod = p ^ h * s := by
    rw [Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_singleton]
  have hpsne : p ≠ s := hslt.ne'
  have htoFinset : (Multiset.replicate h p + ({s} : Multiset ℕ)).toFinset = {p, s} := by
    rw [Multiset.toFinset_add, Multiset.toFinset_replicate, if_neg (by omega : h ≠ 0)]
    simp
  have hcountp : (Multiset.replicate h p + ({s} : Multiset ℕ)).count p = h := by
    simp [Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton, hpsne,
      Ne.symm hpsne]
  have hcounts : (Multiset.replicate h p + ({s} : Multiset ℕ)).count s = 1 := by
    simp [Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton, hpsne,
      Ne.symm hpsne]
  rw [Fintype.card_fin, hsum, hprod, htoFinset] at hclasseq
  rw [Finset.prod_pair hpsne, hcountp, hcounts] at hclasseq
  have hNs : N - (h * p + s) = 0 := by omega
  rw [hNs] at hclasseq
  simp only [Nat.factorial_zero, one_mul, Nat.factorial_one, mul_one] at hclasseq
  intro hpdvd
  obtain ⟨k, hk⟩ := hpdvd
  have hppowne : (p ^ h : ℕ) ≠ 0 := pow_ne_zero h hp.pos.ne'
  have hsne : s ≠ 0 := by omega
  have hspne : p ^ h * s * Nat.factorial h ≠ 0 :=
    mul_ne_zero (mul_ne_zero hppowne hsne) (Nat.factorial_ne_zero h)
  have hNne : Nat.factorial N ≠ 0 := Nat.factorial_ne_zero N
  have hclassne : Nat.card {x : Equiv.Perm (Fin N) | IsConj g x} ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hclasseq
    exact hNne hclasseq.symm
  have hval : (Nat.factorial N).factorization p =
      (Nat.card {x : Equiv.Perm (Fin N) | IsConj g x}).factorization p +
        (p ^ h * s * Nat.factorial h).factorization p := by
    rw [← hclasseq, Nat.factorization_mul hclassne hspne, Finsupp.coe_add, Pi.add_apply]
  have hspfact : (p ^ h * s * Nat.factorial h).factorization p =
      h + (Nat.factorial h).factorization p := by
    rw [Nat.factorization_mul (mul_ne_zero hppowne hsne) (Nat.factorial_ne_zero h),
      Nat.factorization_mul hppowne hsne,
      Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply]
    have hsval0 : s.factorization p = 0 := by
      rw [Nat.factorization_def s hp]
      exact padicValNat.eq_zero_of_not_dvd (fun hdvd =>
        absurd (Nat.le_of_dvd (by omega) hdvd) (by omega))
    have hppow : (p ^ h).factorization p = h := by
      rw [Nat.Prime.factorization_pow hp]; simp
    rw [hsval0, hppow]
    ring
  have hheq : N / p = h := by
    rw [hspN, mul_comm h p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hslt, add_zero]
  have hfact : padicValNat p (Nat.factorial N) = h + padicValNat p (Nat.factorial h) := by
    rw [← hheq]; exact padicValNat_factorial_div N p
  have hNfact' : (Nat.factorial N).factorization p = h + (Nat.factorial h).factorization p := by
    rw [Nat.factorization_def N.factorial hp, Nat.factorization_def h.factorial hp]
    exact hfact
  rw [hspfact] at hval
  have hclassval0 : (Nat.card {x : Equiv.Perm (Fin N) | IsConj g x}).factorization p = 0 := by
    omega
  have hdvd1 : p ∣ Nat.card {x : Equiv.Perm (Fin N) | IsConj g x} := ⟨k, hk⟩
  have := (Nat.Prime.dvd_iff_one_le_factorization hp hclassne).mp hdvd1
  omega

#print axioms exists_perm_replicate_add_singleton_cycleType
#print axioms not_dvd_card_isConj_replicate_add_singleton_cycleType

end CongruenceTheory
