import Mathlib
import CongruenceTheoryHigherOrder.CompletePrimeLocalCaseIIReindexed

/-!
**`thm:complete-prime-local`, case (ii), for a fully general tuple `n`** — `U_p(\mathbf
n)=\{i_0\}$ for *any* index `i_0`, not just position `0`. Derives
`complete_prime_local_case_ii_reindexed`'s `hswap` hypothesis from raw pointwise divisibility on
`n` itself, via `FinSwapCons.lean`'s `swapConsRest_ne_root` (the "rest" tuple read through the
swap never touches `i_0`, so it inherits `p`-divisibility from `n`'s own hypothesis) and the same
`n=p\cdot(n/p)` trick `CompletePrimeLocalCaseIDispatch.lean` used for case (i). Since `p` divides
every entry of the "rest" tuple exactly, `\operatorname{Delta}(\text{rest})` itself (undivided)
is already the `\operatorname{Delta}(p\cdot u)` `complete_prime_local_case_ii_reindexed` needs —
no `/p` appears anywhere except internally, to supply the underlying `u`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`thm:complete-prime-local`(ii), fully general**: for `U_p(\mathbf n)=\{i_0\}` at *any*
index `i_0`. -/
theorem complete_prime_local_case_ii_general {t : ℕ} (n : Fin (t + 1) → ℕ) (hn : ∀ i, 0 < n i)
    (i0 : Fin (t + 1)) {p : ℕ} (hp : p.Prime) (hpi0 : ¬ p ∣ n i0) (hni0 : 1 ≤ n i0)
    (hpa : ∀ i, i ≠ i0 → p ∣ n i)
    {E : ℕ} (hE1 : 1 ≤ E)
    (hE : (cont (Delta (fun j : Fin t => n (Equiv.swap 0 i0 j.succ)))).factorization p = E)
    (hmne : Delta (fun j : Fin t => n (Equiv.swap 0 i0 j.succ)) ≠ 0)
    {d : ℕ} (hleast : IsLeast {s : ℕ | 1 ≤ s ∧
        (Dgcd (Delta (fun j : Fin t => n (Equiv.swap 0 i0 j.succ))) s).factorization p = E} d) :
    (cont (Delta n)).factorization p =
        min (padicValNat p (∑ j : Fin t, n (Equiv.swap 0 i0 j.succ))) E ∧
      IsLeast {s : ℕ | 1 ≤ s ∧ (Dgcd (Delta n) s).factorization p =
            min (padicValNat p (∑ j : Fin t, n (Equiv.swap 0 i0 j.succ))) E}
        (if padicValNat p (∑ j : Fin t, n (Equiv.swap 0 i0 j.succ)) ≤ E then 1 else d) := by
  set u : Fin t → ℕ := fun j => n (Equiv.swap 0 i0 j.succ) / p with hu_def
  have hupos : ∀ j, 0 < u j := fun j =>
    Nat.div_pos (Nat.le_of_dvd (hn _) (hpa _ (swapConsRest_ne_root i0 j))) hp.pos
  have heq : (fun j : Fin t => n (Equiv.swap 0 i0 j.succ)) = fun j => p * u j := by
    funext j
    exact (Nat.mul_div_cancel' (hpa _ (swapConsRest_ne_root i0 j))).symm
  have hswap : n ∘ Equiv.swap 0 i0 = Fin.cons (n i0) (fun j => p * u j) := by
    rw [comp_swap_eq_cons n i0, heq]
  rw [heq]
  rw [heq] at hE hmne hleast
  exact complete_prime_local_case_ii_reindexed n i0 u hupos hp hpi0 hni0 hswap hE1 hE hmne hleast

#print axioms complete_prime_local_case_ii_general

end CongruenceTheory
