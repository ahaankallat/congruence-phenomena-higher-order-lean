import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant

/-!
**`thm:complete-prime-local`(iii)'s Sylow-subgroup witness, the group-theory core.** For
`N=hp+s` (`s<p`), there is a permutation `g\in S_N` with cycle type "`h` copies of `p`" (`h`
disjoint `p`-cycles, the rest fixed points) whose conjugacy class size in `S_N` is coprime to
`p` — matching the manuscript's "the resulting permutation centralizes a Sylow subgroup, so its
conjugacy-class size is a `p`-unit." Uses Mathlib's own `Equiv.Perm.exists_with_cycleType_iff`
(existence of a permutation with prescribed cycle type), `Equiv.Perm.nat_card_centralizer` /
`Equiv.Perm.card_isConj_mul_eq` (the exact centralizer/conjugacy-class-size formulas), and
Legendre's theorem for `v_p(N!)` (`padicValNat_factorial_mul`, `padicValNat_factorial_mul_add`).
-/

namespace CongruenceTheory

open Equiv.Perm Subgroup Nat

/-- **Legendre's recursion for `v_p(N!)`**: `v_p(N!) = h+v_p(h!)`, `h:=N/p`. -/
theorem padicValNat_factorial_div (N p : ℕ) [hp : Fact p.Prime] :
    padicValNat p (Nat.factorial N) = N / p + padicValNat p (Nat.factorial (N / p)) := by
  conv_lhs => rw [← Nat.div_add_mod N p]
  rw [padicValNat_factorial_mul_add (N / p) (Nat.mod_lt N hp.out.pos), padicValNat_factorial_mul]
  omega

/-- **There is a permutation of `Fin N` with `h` disjoint `p`-cycles**, `h:=N/p`, provided
`p\le N`. -/
theorem exists_perm_replicate_cycleType {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) :
    ∃ g : Equiv.Perm (Fin N), g.cycleType = Multiset.replicate (N / p) p := by
  apply (exists_with_cycleType_iff (α := Fin N)).mpr
  refine ⟨?_, ?_⟩
  · rw [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin]
    exact Nat.div_mul_le_self N p
  · intro a ha
    rw [Multiset.eq_of_mem_replicate ha]
    exact hp.two_le

/-- **The conjugacy class of a permutation of `Fin N` with `h` disjoint `p`-cycles (`h:=N/p`) has
size coprime to `p`.** This is the manuscript's "the resulting permutation centralizes a Sylow
subgroup, so its conjugacy-class size is a `p`-unit." -/
theorem not_dvd_card_isConj_replicate_cycleType {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    {g : Equiv.Perm (Fin N)} (hg : g.cycleType = Multiset.replicate (N / p) p) :
    ¬ p ∣ Nat.card {h : Equiv.Perm (Fin N) | IsConj g h} := by
  haveI := Fact.mk hp
  set h := N / p with hhdef
  set s := N % p with hsdef
  have hNhs : N = p * h + s := (Nat.div_add_mod N p).symm
  have hslt : s < p := Nat.mod_lt N hp.pos
  have hcentral : Nat.card (centralizer {g}) =
      (Fintype.card (Fin N) - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!) :=
    Equiv.Perm.nat_card_centralizer g
  have hclasseq : Nat.card {x : Equiv.Perm (Fin N) | IsConj g x} *
      ((Fintype.card (Fin N) - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!)) = (Fintype.card (Fin N))! :=
    Equiv.Perm.card_isConj_mul_eq g
  rw [hg] at hclasseq
  have hsum : (Multiset.replicate h p).sum = h * p := by
    rw [Multiset.sum_replicate, smul_eq_mul]
  have hprod : (Multiset.replicate h p).prod = p ^ h := by
    rw [Multiset.prod_replicate]
  rcases Nat.eq_zero_or_pos h with hh0 | hhpos
  · -- h = 0: N < p, contradicting hpN and hslt/hNhs is trivial; handle directly via hpN
    rw [hh0] at hNhs
    simp at hNhs
    omega
  have htoFinset : (Multiset.replicate h p).toFinset = {p} := by
    rw [Multiset.toFinset_replicate, if_neg (by omega : h ≠ 0)]
  have hcount : (Multiset.replicate h p).count p = h := by
    rw [Multiset.count_replicate_self]
  rw [Fintype.card_fin, hsum, hprod, htoFinset, Finset.prod_singleton, hcount] at hclasseq
  have hNs : N - h * p = s := by rw [mul_comm]; omega
  rw [hNs] at hclasseq
  intro hpdvd
  obtain ⟨k, hk⟩ := hpdvd
  have hfact : padicValNat p (Nat.factorial N) = h + padicValNat p (Nat.factorial h) :=
    padicValNat_factorial_div N p
  have hlhsfact : Nat.factorial N = (Nat.card {x : Equiv.Perm (Fin N) | IsConj g x}) *
      (Nat.factorial s * p ^ h * Nat.factorial h) :=
    hclasseq.symm
  have hNfactne : Nat.factorial N ≠ 0 := Nat.factorial_ne_zero N
  have hppowne : p ^ h ≠ 0 := pow_ne_zero h hp.pos.ne'
  have hspne : Nat.factorial s * p ^ h * Nat.factorial h ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero s) hppowne) (Nat.factorial_ne_zero h)
  have hclassne : Nat.card {x : Equiv.Perm (Fin N) | IsConj g x} ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hlhsfact
    exact hNfactne hlhsfact
  have hval : (Nat.factorial N).factorization p =
      (Nat.card {x : Equiv.Perm (Fin N) | IsConj g x}).factorization p +
        (Nat.factorial s * p ^ h * Nat.factorial h).factorization p := by
    rw [hlhsfact, Nat.factorization_mul hclassne hspne, Finsupp.coe_add, Pi.add_apply]
  have hspfact : (Nat.factorial s * p ^ h * Nat.factorial h).factorization p =
      h + (Nat.factorial h).factorization p := by
    rw [Nat.factorization_mul (mul_ne_zero (Nat.factorial_ne_zero s) hppowne)
        (Nat.factorial_ne_zero h),
      Nat.factorization_mul (Nat.factorial_ne_zero s) hppowne,
      Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply]
    have hsfact0 : (Nat.factorial s).factorization p = 0 := by
      rw [Nat.factorization_def s.factorial hp]
      exact padicValNat.eq_zero_of_not_dvd (fun hdvd =>
        absurd (Nat.Prime.dvd_factorial hp |>.mp hdvd) (by omega))
    have hppow : (p ^ h).factorization p = h := by
      rw [Nat.Prime.factorization_pow hp]
      simp
    rw [hsfact0, hppow]
    ring
  have hNfact' : (Nat.factorial N).factorization p = h + (Nat.factorial h).factorization p := by
    rw [Nat.factorization_def N.factorial hp, Nat.factorization_def h.factorial hp]
    exact hfact
  rw [hspfact] at hval
  have hclassval0 : (Nat.card {x : Equiv.Perm (Fin N) | IsConj g x}).factorization p = 0 := by
    omega
  have hdvd1 : p ∣ Nat.card {x : Equiv.Perm (Fin N) | IsConj g x} := ⟨k, hk⟩
  have := (Nat.Prime.dvd_iff_one_le_factorization hp hclassne).mp hdvd1
  omega

#print axioms padicValNat_factorial_div
#print axioms exists_perm_replicate_cycleType
#print axioms not_dvd_card_isConj_replicate_cycleType

end CongruenceTheory
