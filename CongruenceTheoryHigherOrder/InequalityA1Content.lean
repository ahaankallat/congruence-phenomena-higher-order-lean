import Mathlib
import CongruenceTheoryHigherOrder.InequalityA1
import CongruenceTheoryHigherOrder.CycleDepthHierarchy

/-!
**Inequality (A1) of `thm:atomic-connected-content`, upgraded to `cont`-level.**
`InequalityA1.lean`'s `coeff_K_dvd` proves `(r-1)!q^{r-1} \mid [\text{monomial of }g]K_r(q)` for a
*single* connected permutation `g`, already stated for an *arbitrary* such `g` — so combined with
`K_eq_Gfun_top` (`K_r(q)=\sum_{g:\pi(g)=\top}\operatorname{ci}(g)`, a sum of single-coefficient-1
monomials over exactly the connected permutations), every nonzero coefficient of `K_r(q)` is the
coefficient at *some* connected `g`'s own monomial, hence itself divisible by `(r-1)!q^{r-1}$ by
`coeff_K_dvd` applied to that `g`. Since `cont` is the gcd of all coefficients, a divisor of every
coefficient divides the gcd, giving the manuscript's actual `(r-1)!q^{r-1}\mid\operatorname{cont}
K_r(q)` — the literal statement of inequality (A1), not just a single-coefficient instance.
-/

namespace CongruenceTheory

open MvPolynomial

variable {r q : ℕ} [NeZero r] [NeZero q]

/-- **The coefficient of `\operatorname{ci}(g)` at `d`**, as an explicit `if`. -/
theorem coeff_ci_eq_ite {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α)
    (d : ℕ →₀ ℕ) :
    coeff d (ci g) =
      if ciExp (Fintype.card α - g.cycleType.sum) g.cycleType = d then 1 else 0 := by
  rw [ci_eq_monomial', coeff_monomial]

/-- **Every nonzero-coefficient monomial of `K_r(q)` is the monomial of some connected `g`.** -/
theorem exists_connected_ci_eq_of_coeff_ne_zero {d : ℕ →₀ ℕ}
    (hd : coeff d (K r q) ≠ 0) :
    ∃ g : Equiv.Perm (Fin r × Fin q), piOf g = ⊤ ∧
      ciExp (Fintype.card (Fin r × Fin q) - g.cycleType.sum) g.cycleType = d := by
  rw [K_eq_Gfun_top, Gfun, coeff_sum] at hd
  by_contra hcon
  push_neg at hcon
  apply hd
  apply Finset.sum_eq_zero
  intro g hg
  have hpiOf : piOf g = ⊤ := (Finset.mem_filter.mp hg).2
  rw [coeff_ci_eq_ite, if_neg (hcon g hpiOf)]

/-- **Inequality (A1), fully assembled at `cont`-level**: `(r-1)!q^{r-1}\mid\operatorname{cont}
K_r(q)`, the manuscript's own statement (not just a single coefficient's divisibility). -/
theorem content_dvd_K (hq : 2 ≤ q) :
    ((r - 1).factorial * q ^ (r - 1) : ℕ) ∣ cont (K r q) := by
  apply Finset.dvd_gcd
  intro d hd
  rw [MvPolynomial.mem_support_iff] at hd
  obtain ⟨g, hpiOf, hdeq⟩ := exists_connected_ci_eq_of_coeff_ne_zero hd
  obtain ⟨M, hM⟩ := coeff_K_dvd hq g hpiOf
  rw [hdeq] at hM
  have habs : (coeff d (K r q)).natAbs = M.natAbs * (q ^ (r - 1) * (r - 1).factorial) := by
    rw [hM]; push_cast; simp [Int.natAbs_mul]
  rw [habs, mul_comm (q ^ (r - 1)) ((r - 1).factorial)]
  exact Dvd.intro_left _ rfl

#print axioms coeff_ci_eq_ite
#print axioms exists_connected_ci_eq_of_coeff_ne_zero
#print axioms content_dvd_K

end CongruenceTheory
