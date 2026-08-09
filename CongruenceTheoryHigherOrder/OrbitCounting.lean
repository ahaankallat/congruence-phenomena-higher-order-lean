import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.WreathProduct
import CongruenceTheoryHigherOrder.Semiregularity
import CongruenceTheoryHigherOrder.ConjugationInvariance
import CongruenceTheoryHigherOrder.StabilizerBound

/-!
**The numeric conclusion of inequality (A1)**: the manuscript's argument ends "Hence the
stabilizer order divides `rq`, and `(r-1)!q^{r-1}∣K_r(q)`." `StabilizerBound.lean` proved the
first half; this file proves the arithmetic core of the second: **`index_wreathStab_dvd_mul`**,
for `g` connected, the index of its wreath-centralizer subgroup (i.e. the number of distinct
wreath-conjugates of `g` — its orbit size) is a multiple of `q^{r-1}(r-1)!`.

**Proof**: purely arithmetic, given what's already built. Mathlib's `Subgroup.index_mul_card`
gives `index(wreathStab g) · |wreathStab g| = |Wreath r q| = q^r·r!` (the last equality via
`WreathProduct.lean`'s `card_wreath`). `StabilizerBound.lean`'s `card_wreathStab_dvd` gives
`|wreathStab g| ∣ rq`, say `rq = |wreathStab g|·m`. Since `q^r·r! = (rq)·(q^{r-1}(r-1)!)`
(elementary, via `Nat.factorial_succ`/`pow_succ` after writing `r = r'+1`), substituting gives
`index(wreathStab g)·|wreathStab g| = (m·q^{r-1}(r-1)!)·|wreathStab g|`, and cancelling the
(positive) stabilizer order gives the result.

**Honest scope note**: this is the numeric heart of (A1)'s conclusion, but doesn't yet identify
the index with a literal `MvPolynomial.coeff` of `K_r(q)` — that final identification needs: a
genuine bijection between cosets of `wreathStab g` and an explicit `Finset` of permutations (the
orbit itself, as a subset of `Equiv.Perm(Fin r×Fin q)`), showing this orbit sits inside
`{h : π(h)=⊤ ∧ cycleType h = cycleType g}` (via `ConjugationInvariance.lean`'s
`piOf_conj_eq_top` and Mathlib's `Equiv.Perm.cycleType_conj`), a coefficient-extraction lemma for
`ConnectedCount.lean`'s `Gfun ⊤` (analogous to the existing `coeff_sum_ci_eq_card_cycleType` in
`ContentBounds.lean`, but for the `π(h)=⊤`-filtered sum), and a union-of-orbits argument (via a
`Finpartition.ofSetSetoid` on that coefficient-counting set, mirroring `StabilizerBound.lean`'s
own `card_dvd_of_free_action` pattern) to sum divisibility across every orbit inside it. None of
that is attempted here, nor is any of (A2) through (A6) or Lucas' theorem.
-/

namespace CongruenceTheory

open scoped Classical

variable {r q : ℕ} [NeZero r] [NeZero q] (hq : 2 ≤ q)

/-- **Inequality (A1), index form**: for `g` connected, the index of its wreath-centralizer
subgroup is a multiple of `q^{r-1}(r-1)!` — the number of wreath-conjugates of `g` (i.e. the
orbit size, `Wreath r q ⧸ wreathStab hq g`) is divisible by `q^{r-1}(r-1)!`. -/
theorem index_wreathStab_dvd_mul {g : Equiv.Perm (Fin r × Fin q)} (hg : piOf g = ⊤) :
    ∃ M, (wreathStab hq g).index = M * (q ^ (r - 1) * (r - 1).factorial) := by
  have hidx := (wreathStab hq g).index_mul_card
  have hdvd := card_wreathStab_dvd hq hg
  obtain ⟨m, hm⟩ := hdvd
  have hstabpos : 0 < Nat.card (wreathStab hq g) := Nat.card_pos
  refine ⟨m, ?_⟩
  obtain ⟨r', hr'⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne r)
  have hstep : q ^ r * r.factorial = (r * q) * (q ^ (r - 1) * (r - 1).factorial) := by
    subst hr'
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    rw [Nat.factorial_succ, pow_succ]
    ring
  have key : (wreathStab hq g).index * Nat.card (wreathStab hq g) =
      (m * (q ^ (r - 1) * (r - 1).factorial)) * Nat.card (wreathStab hq g) := by
    rw [hidx, card_wreath, hstep, hm]
    ring
  exact Nat.eq_of_mul_eq_mul_right hstabpos key

end CongruenceTheory
