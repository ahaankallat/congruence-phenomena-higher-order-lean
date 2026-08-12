import Mathlib
import CongruenceTheory.Basic

/-!
**Floor subadditivity for `\lfloor\cdot/p\rfloor`.** For `n:\text{Fin }r\to\Bbb N` and
`N=\sum_in_i`, `\sum_i\lfloor n_i/p\rfloor\le\lfloor N/p\rfloor` always, and strictly so whenever
the residues
`n_i\bmod p` accumulate to `\ge p` in total. This is the arithmetic fact behind
`thm:complete-prime-local`(iii)'s "cannot be allocated among two or more blocks of nonzero
residue" obstruction: the number of `p`-cycles a block-respecting permutation of
`n_1,\ldots,n_r` elements can form is capped at `\sum_i\lfloor n_i/p\rfloor`, which is strictly
less than the maximum `\lfloor N/p\rfloor` a permutation of *all* `N` elements can form exactly
when the residues carry. Proved via the trivial exact identity `N=p\cdot\sum_i\lfloor
n_i/p\rfloor+\sum_i(n_i\bmod p)`, reducing everything to single-variable Euclidean division.
-/

namespace CongruenceTheory

/-- **The exact identity** `N = p\cdot\sum_i\lfloor n_i/p\rfloor+\sum_i(n_i\bmod p)`. -/
theorem sum_eq_mul_sum_div_add_sum_mod {r : ℕ} (n : Fin r → ℕ) (p : ℕ) :
    ∑ i, n i = p * (∑ i, (n i / p)) + ∑ i, (n i % p) := by
  have step : ∀ i, n i = p * (n i / p) + n i % p := fun i => (Nat.div_add_mod (n i) p).symm
  calc ∑ i, n i = ∑ i, (p * (n i / p) + n i % p) := Finset.sum_congr rfl (fun i _ => step i)
    _ = ∑ i, p * (n i / p) + ∑ i, n i % p := Finset.sum_add_distrib
    _ = p * ∑ i, (n i / p) + ∑ i, n i % p := by rw [Finset.mul_sum]

/-- **`\lfloor N/p\rfloor = \sum_i\lfloor n_i/p\rfloor + \lfloor(\sum_i(n_i\bmod p))/p\rfloor`.** -/
theorem div_sum_eq_sum_div_add_div_sum_mod {r : ℕ} (n : Fin r → ℕ) (p : ℕ) (hp : 0 < p) :
    (∑ i, n i) / p = (∑ i, (n i / p)) + (∑ i, (n i % p)) / p := by
  rw [sum_eq_mul_sum_div_add_sum_mod n p, Nat.mul_add_div hp]

/-- **Floor subadditivity**: `\sum_i\lfloor n_i/p\rfloor\le\lfloor N/p\rfloor`. -/
theorem sum_div_le_div_sum {r : ℕ} (n : Fin r → ℕ) (p : ℕ) :
    ∑ i, (n i / p) ≤ (∑ i, n i) / p := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · simp [hp0]
  · rw [div_sum_eq_sum_div_add_div_sum_mod n p hp]
    exact Nat.le_add_right _ _

/-- **Strict floor subadditivity iff the residues carry**: `\sum_i\lfloor n_i/p\rfloor<
\lfloor N/p\rfloor \iff p\le\sum_i(n_i\bmod p)`. -/
theorem sum_div_lt_div_sum_iff {r : ℕ} (n : Fin r → ℕ) (p : ℕ) (hp : 0 < p) :
    ∑ i, (n i / p) < (∑ i, n i) / p ↔ p ≤ ∑ i, (n i % p) := by
  rw [div_sum_eq_sum_div_add_div_sum_mod n p hp, Nat.lt_add_right_iff_pos]
  rw [Nat.div_pos_iff]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨hp, h⟩

#print axioms sum_eq_mul_sum_div_add_sum_mod
#print axioms div_sum_eq_sum_div_add_div_sum_mod
#print axioms sum_div_le_div_sum
#print axioms sum_div_lt_div_sum_iff

end CongruenceTheory
