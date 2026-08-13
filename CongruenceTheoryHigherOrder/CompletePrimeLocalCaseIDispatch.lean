import Mathlib
import CongruenceTheoryHigherOrder.CompletePrimeLocalDefect

/-!
**`thm:complete-prime-local`, case (i), dispatched from a general tuple.** `complete_prime_
local_case_i`/`_depth` are stated for the canonical shape `n = fun i => p * u i`. This file
removes that restriction: given *any* tuple `n` with `p ∣ n i` for every `i` (i.e.
`U_p(\mathbf n)=\varnothing`), setting `u i := n i / p` recovers `n = fun i => p * u i` exactly
(`Nat.mul_div_cancel'`), so the case-(i) theorems apply directly to `n` itself, without any
reindexing (unlike case (ii), which needs to relocate its unique `p`-coprime index to position
`0` to match `Fin.cons`'s shape — not attempted here).
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`n` in the case-(i) shape, from `U_p(\mathbf n)=\varnothing`.** -/
theorem eq_p_mul_div_of_forall_dvd {r : ℕ} (n : Fin r → ℕ) {p : ℕ} (_hp : p ≠ 0)
    (hdvd : ∀ i, p ∣ n i) : n = fun i => p * (n i / p) := by
  funext i
  exact (Nat.mul_div_cancel' (hdvd i)).symm

/-- **`thm:complete-prime-local`, case (i), for a general tuple `n` with `U_p(\mathbf
n)=\varnothing`.** -/
theorem complete_prime_local_case_i_general {r : ℕ} (hr : 0 < r) (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) {p : ℕ} [hpf : Fact (Nat.Prime p)] (hdvd : ∀ i, p ∣ n i)
    (hne : ((nonRefiningPartitions (fun i => n i / p)).image GenPartLatShape).Nonempty) :
    (∀ d, (p : ℤ) ^ ((((nonRefiningPartitions (fun i => n i / p)).image GenPartLatShape).image
          (Wp (fun i => n i / p) p)).min' (hne.image _)) ∣ coeff d (Delta n)) ∧
      ∃ d, ¬ ((p : ℤ) ^ ((((nonRefiningPartitions (fun i => n i / p)).image
              GenPartLatShape).image (Wp (fun i => n i / p) p)).min' (hne.image _) + 1) ∣
            coeff d (Delta n)) := by
  set u : Fin r → ℕ := fun i => n i / p with hu_def
  have hupos : ∀ i, 0 < u i := fun i => Nat.div_pos (Nat.le_of_dvd (hn i) (hdvd i)) hpf.out.pos
  have heq : n = fun i => p * u i := eq_p_mul_div_of_forall_dvd n hpf.out.ne_zero hdvd
  have hkey := complete_prime_local_case_i hr u hupos (p := p) hne
  rwa [← heq] at hkey

#print axioms eq_p_mul_div_of_forall_dvd
#print axioms complete_prime_local_case_i_general

end CongruenceTheory
