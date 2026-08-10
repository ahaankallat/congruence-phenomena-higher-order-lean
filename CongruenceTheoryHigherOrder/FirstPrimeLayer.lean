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
import CongruenceTheoryHigherOrder.WreathProduct
import CongruenceTheoryHigherOrder.Semiregularity
import CongruenceTheoryHigherOrder.ConjugationInvariance
import CongruenceTheoryHigherOrder.StabilizerBound
import CongruenceTheoryHigherOrder.OrbitCounting
import CongruenceTheoryHigherOrder.InequalityA1
import CongruenceTheoryHigherOrder.A3Final
import CongruenceTheoryHigherOrder.LegendreA3

/-!
**`prop:first-prime-layer`, fully assembled**: "at the first prime layer put
`e_p(j) = j - 1 + v_p((j-1)!)`... `v_p(cont K_j(p)) = e_p(j)`."

This file combines three ingredients that were each proved separately elsewhere in this
project, into one theorem matching the manuscript statement:

1. **`coeff_K_dvd_general`**: generalizes `InequalityA1.lean`'s `coeff_K_dvd` (which is stated
   for a monomial coming from a specific connected permutation `g`'s own cycle type) to an
   *arbitrary* multiset `m` of parts `≥ 2`, i.e. to every coefficient of `K r q` that can
   possibly be nonzero (every nonzero coefficient of `K r q` sits at a `ciExp _ m` monomial for
   some permutation's cycle type, by `K_eq_Gfun_top`/`Gfun`, and every cycle type has parts
   `≥ 2` by `Equiv.Perm.two_le_of_mem_cycleType`). This is exactly the divisibility half of
   "content," applied coefficientwise rather than through an abstract gcd object, matching this
   project's established idiom (`OptimalDivisorC.lean`'s `treeM`/`treeM_dvd_defect` pattern):
   state a fact for *every* coefficient rather than defining a `content` function that nothing
   else in the codebase needs.

2. **`firstPrimeLayerExponent_dvd_base`**: the purely arithmetic fact that
   `p ^ e_p(j) ∣ p^{j-1} (j-1)!`, i.e. the divisor `q^{r-1}(r-1)!` from (A1) is itself already a
   multiple of `p^{e_p(j)}` once `q = p` , `r = j`. Combined with 1, every coefficient of
   `K_j(p)` is divisible by `p^{e_p(j)}` — the lower bound on the content's valuation.

3. **The witnessed sharpness half**, combining `A3Final.lean`'s `A3_coeff_eq_factorial`
   (`[X_{jp}] K_j(p) = (jp-1)!`) with `LegendreA3.lean`'s `factorization_factorial_mul_sub_one`
   (`v_p((jp-1)!) = e_p(j)`): the coefficient of `K_j(p)` at the full-cycle monomial `X_{jp}` has
   `p`-adic valuation *exactly* `e_p(j)`, witnessing that the divisibility bound from 1-2 cannot
   be improved, i.e. `p^{e_p(j)+1}` does **not** divide `cont K_j(p)`.

**`firstPrimeLayer_valuation`** packages 1-3 as the two-sided statement matching the manuscript:
every coefficient has valuation `≥ e_p(j)` (equivalently, is divisible by `p^{e_p(j)}`), and
there is a specific coefficient — the full-cycle one — whose valuation is *exactly* `e_p(j)`,
so `e_p(j)` is the best (largest) such uniform bound.

**Honest scope note**: this assembles `prop:first-prime-layer` itself completely, given the
constituent parts already proved in `InequalityA1.lean`, `A3Final.lean`, and `LegendreA3.lean`.
It does **not** touch `cor:triangular-independence` (the noncancellation ingredient needed for
the common-prime classification theorem beyond this first layer) nor the rest of
`thm:complete-prime-local`.
-/

namespace CongruenceTheory

open scoped Classical
open MvPolynomial

variable {r q : ℕ} [NeZero r] [NeZero q]

/-- **Generalizes `coeff_K_dvd` from a specific connected permutation's own cycle type to an
arbitrary cycle-type multiset `m` with parts `≥ 2`** — i.e. to every monomial at which `K r q`
can possibly have a nonzero coefficient. -/
theorem coeff_K_dvd_general (hq : 2 ≤ q) (m : Multiset ℕ) (hm2 : ∀ x ∈ m, 2 ≤ x) :
    ∃ M, MvPolynomial.coeff (ciExp (Fintype.card (Fin r × Fin q) - m.sum) m) (K r q) =
      M * (q ^ (r - 1) * (r - 1).factorial) := by
  have hcoeff : MvPolynomial.coeff (ciExp (Fintype.card (Fin r × Fin q) - m.sum) m) (K r q) =
      (((Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter
          (fun h => piOf h = ⊤)).filter (fun h => h.cycleType = m)).card := by
    rw [K_eq_Gfun_top]
    unfold Gfun
    exact coeff_sum_ci_eq_card_cycleType_filter
      (Finset.univ.filter (fun h : Equiv.Perm (Fin r × Fin q) => piOf h = ⊤)) m hm2
  by_cases hne : ((Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter
      (fun h => piOf h = ⊤)).filter (fun h => h.cycleType = m) = ∅
  · refine ⟨0, ?_⟩
    rw [hcoeff, hne]
    simp
  · obtain ⟨g0, hg0⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hg0mem := Finset.mem_filter.mp hg0
    have hg0cyc : g0.cycleType = m := hg0mem.2
    have hset_eq : ((Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter
        (fun h => piOf h = ⊤)).filter (fun h => h.cycleType = m) = connSameTypeFinset g0 := by
      rw [← hg0cyc]
      unfold connSameTypeFinset
      rw [Finset.filter_filter]
    rw [hcoeff, hset_eq]
    obtain ⟨M, hM⟩ := card_connSameTypeFinset_dvd hq g0
    exact ⟨M, by exact_mod_cast hM⟩

/-- **`e_p(j) = j - 1 + v_p((j-1)!)`**, the manuscript's exact first-prime-layer exponent. -/
def firstPrimeLayerExponent (p j : ℕ) : ℕ := (j - 1) + (Nat.factorial (j - 1)).factorization p

/-- **The arithmetic content of (A1) specialized to `q = p`**: `p^{e_p(j)} ∣ p^{j-1}(j-1)!`. This
is exactly `p`'s contribution to the divisor `q^{r-1}(r-1)!` produced by (A1), computed via
Legendre's formula. -/
theorem firstPrimeLayerExponent_dvd_base {p j : ℕ} (hp : p.Prime) :
    p ^ (firstPrimeLayerExponent p j) ∣ p ^ (j - 1) * (j - 1).factorial := by
  have hne : p ^ (j - 1) * (j - 1).factorial ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ hp.pos.ne') (Nat.factorial_ne_zero _)
  have hpself : p.factorization p = 1 := hp.factorization_self
  have hfact : (p ^ (j - 1) * (j - 1).factorial).factorization p =
      firstPrimeLayerExponent p j := by
    rw [Nat.factorization_mul (pow_ne_zero _ hp.pos.ne') (Nat.factorial_ne_zero _),
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, hpself, smul_eq_mul,
      mul_one]
    rfl
  exact (hp.pow_dvd_iff_le_factorization hne).mpr hfact.ge

/-- **Lower bound half of `prop:first-prime-layer`**: every coefficient of `K_j(p)` is
divisible by `p^{e_p(j)}`. -/
theorem firstPrimeLayer_dvd {p j : ℕ} (hp : p.Prime) [NeZero j]
    (m : Multiset ℕ) (hm2 : ∀ x ∈ m, 2 ≤ x) :
    (p : ℤ) ^ (firstPrimeLayerExponent p j) ∣
      MvPolynomial.coeff (ciExp (Fintype.card (Fin j × Fin p) - m.sum) m) (K j p) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  obtain ⟨M, hM⟩ := coeff_K_dvd_general (r := j) (q := p) hp.two_le m hm2
  obtain ⟨N, hN⟩ := firstPrimeLayerExponent_dvd_base (j := j) hp
  have hN' : (p : ℤ) ^ (j - 1) * (j - 1).factorial =
      (p : ℤ) ^ (firstPrimeLayerExponent p j) * N := by exact_mod_cast hN
  refine ⟨M * (N : ℤ), ?_⟩
  rw [hM, hN']
  ring

/-- **Sharpness half of `prop:first-prime-layer`**: the `X_{jp}`-coefficient of `K_j(p)` has
`p`-adic valuation *exactly* `e_p(j)`, witnessing that the divisibility bound of
`firstPrimeLayer_dvd` cannot be improved. -/
theorem firstPrimeLayer_sharp {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) (hn : 2 ≤ j * p) :
    (Nat.factorial (j * p - 1)).factorization p = firstPrimeLayerExponent p j ∧
      MvPolynomial.coeff (Finsupp.single (j * p) 1) (K j p) =
        (Nat.factorial (j * p - 1) : ℤ) := by
  refine ⟨?_, A3_coeff_eq_factorial hn⟩
  rw [factorization_factorial_mul_sub_one hp hj]
  rfl

/-- **`prop:first-prime-layer`, fully assembled.** For `j ≥ 1` and `p` prime with `2 ≤ jp`: every
coefficient of `K_j(p)` is divisible by `p^{e_p(j)}` (`firstPrimeLayer_dvd`), and the coefficient
at the full-cycle monomial `X_{jp}` equals `(jp-1)!`, whose `p`-adic valuation is exactly
`e_p(j)` (`firstPrimeLayer_sharp`) — so `e_p(j)` is exactly the largest power of `p` dividing
every coefficient of `K_j(p)`, matching the manuscript's `v_p(cont K_j(p)) = e_p(j)`. -/
theorem firstPrimeLayer {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) (hn : 2 ≤ j * p) :
    (∀ m : Multiset ℕ, (∀ x ∈ m, 2 ≤ x) →
        (p : ℤ) ^ (firstPrimeLayerExponent p j) ∣
          MvPolynomial.coeff (ciExp (Fintype.card (Fin j × Fin p) - m.sum) m) (K j p)) ∧
      MvPolynomial.coeff (Finsupp.single (j * p) 1) (K j p) =
        (Nat.factorial (j * p - 1) : ℤ) ∧
      (Nat.factorial (j * p - 1)).factorization p = firstPrimeLayerExponent p j := by
  haveI : NeZero j := ⟨by omega⟩
  refine ⟨fun m hm2 => firstPrimeLayer_dvd hp m hm2, ?_, ?_⟩
  · exact (firstPrimeLayer_sharp hp hj hn).2
  · exact (firstPrimeLayer_sharp hp hj hn).1

#print axioms firstPrimeLayer

end CongruenceTheory
