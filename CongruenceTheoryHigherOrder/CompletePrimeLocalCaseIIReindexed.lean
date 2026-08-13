import Mathlib
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseIIFull
import CongruenceTheoryHigherOrder.DeltaPermInvariance
import CongruenceTheoryHigherOrder.FinSwapCons

/-!
**`thm:complete-prime-local`, case (ii), reindexed to allow the `p`-coprime index anywhere.**
`complete_prime_local_case_ii` is stated for the canonical shape `Fin.cons a (fun i => p*u i)`
(the coprime entry fixed at position `0`). This wraps it for a tuple `n` whose `p`-coprime index
`i0` may be anywhere, *given* that swapping `0` and `i0` puts `n` into the canonical shape
(`hswap`) — via `FinSwapCons.lean`'s `comp_swap_eq_cons` (always true definitionally for *some*
`u`; deriving that decomposition from raw divisibility hypotheses on `n` is a further step, not
attempted here) and `DeltaPermInvariance.lean`'s `Delta_comp_equiv`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`thm:complete-prime-local`(ii), reindexed**: given `n`'s `(0,i0)`-swap already has the
canonical `\operatorname{cons} a\,(p\cdot u)` shape, the conclusion transports to `n` itself. -/
theorem complete_prime_local_case_ii_reindexed {t : ℕ} {a : ℕ} (n : Fin (t + 1) → ℕ)
    (i0 : Fin (t + 1)) (u : Fin t → ℕ) (hu : ∀ i, 0 < u i)
    {p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (ha1 : 1 ≤ a)
    (hswap : n ∘ Equiv.swap 0 i0 = Fin.cons a (fun i => p * u i))
    {E : ℕ} (hE1 : 1 ≤ E) (hE : (cont (Delta (fun i => p * u i))).factorization p = E)
    (hmne : Delta (fun i => p * u i) ≠ 0)
    {d : ℕ} (hleast : IsLeast
      {s : ℕ | 1 ≤ s ∧ (Dgcd (Delta (fun i => p * u i)) s).factorization p = E} d) :
    (cont (Delta n)).factorization p = min (padicValNat p (∑ i, p * u i)) E ∧
      IsLeast {s : ℕ | 1 ≤ s ∧ (Dgcd (Delta n) s).factorization p =
            min (padicValNat p (∑ i, p * u i)) E}
        (if padicValNat p (∑ i, p * u i) ≤ E then 1 else d) := by
  have hDeq : Delta n = Delta (Fin.cons a (fun i => p * u i) : Fin (t + 1) → ℕ) := by
    rw [← hswap, Delta_comp_equiv]
  rw [hDeq]
  exact complete_prime_local_case_ii u hu hp hpa ha1 hE1 hE hmne hleast

#print axioms complete_prime_local_case_ii_reindexed

end CongruenceTheory
