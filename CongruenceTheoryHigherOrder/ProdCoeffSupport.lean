import Mathlib
import CongruenceTheory.Basic

/-!
**The support of a coefficient of a finite product of `MvPolynomial`s decomposes additively.**
If `d = \sum_i e_i` is the *only* way (up to the constraint that each `e_i` lies in `f_i`'s
support) to write a target monomial `d` as a sum of per-factor contributions, then
`\text{coeff}_d\bigl(\prod_if_i\bigr)` is determined by those `e_i`'s. We only need the
*vanishing* direction here: if **no** family `(e_i)_{i\in s}` with `e_i\in\text{support}(f_i)`
sums to `d`, the coefficient is `0` — the key fact behind `thm:complete-prime-local`(iii)'s
"cannot be allocated among two or more blocks" obstruction (no block-respecting permutation can
realize a monomial that isn't a sum of the blocks' own achievable monomials).
-/

namespace CongruenceTheory

open MvPolynomial

/-- **If no family of per-factor exponents (each in the corresponding factor's support) sums to
`d`, the product's coefficient at `d` vanishes.** -/
theorem coeff_finset_prod_eq_zero_of_forall_ne {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial ℕ ℤ) (d : ℕ →₀ ℕ)
    (hnone : ¬ ∃ e : ι → ℕ →₀ ℕ, (∀ i ∈ s, e i ∈ (f i).support) ∧ ∑ i ∈ s, e i = d) :
    coeff d (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction generalizing d with
  | empty =>
    rw [Finset.prod_empty, coeff_one]
    have hdne : d ≠ 0 := by
      intro hd0
      apply hnone
      exact ⟨fun _ => 0, fun i hi => absurd hi (Finset.notMem_empty i), by simp [hd0]⟩
    simp [hdne.symm]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨d1, d2⟩ hd12
    rw [Finset.mem_antidiagonal] at hd12
    dsimp only at hd12
    by_cases hd1 : d1 ∈ (f a).support
    · have hd2zero : coeff d2 (∏ i ∈ s, f i) = 0 := by
        apply ih
        intro ⟨e, hemem, hesum⟩
        apply hnone
        refine ⟨Function.update e a d1, ?_, ?_⟩
        · intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · rwa [Function.update_self]
          · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
            exact hemem i hi
        · rw [Finset.sum_insert ha, Function.update_self]
          rw [Finset.sum_congr rfl (fun i hi => by
            rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)])]
          rw [hesum, hd12]
      rw [hd2zero, mul_zero]
    · rw [mem_support_iff, not_not] at hd1
      rw [hd1, zero_mul]

#print axioms coeff_finset_prod_eq_zero_of_forall_ne

end CongruenceTheory
