import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.CompletePrimeLocalDefect
import CongruenceTheoryHigherOrder.PUnitDefectCoefficientCarry
import CongruenceTheoryHigherOrder.PUnitDefectCoefficientResidual
import CongruenceTheoryHigherOrder.FloorSubadditivity
import CongruenceTheoryHigherOrder.GaussLemmaModP

/-!
**`thm:complete-prime-local`(iii), the valuation claim, fully assembled.** For `|U_p(\mathbf
n)|\ge2` (at least two indices with `p\nmid n_i`), `v_p(\operatorname{cont}\Delta_{\mathbf n})=0`.
Assembled from `exists_coeff_not_dvd_of_carry` (`\sum_i(n_i\bmod p)\ge p`) and
`exists_coeff_not_dvd_of_no_carry` (`\sum_i(n_i\bmod p)<p`) via a single case split on the total
residue; in the no-carry case, the exact identity `\sum_i(n_i\bmod p)=N\bmod p` (from
`sum_eq_mul_sum_div_add_sum_mod`, since no carry means `\sum_i\lfloor n_i/p\rfloor=\lfloor
N/p\rfloor` exactly) supplies the `2\le s` hypothesis directly from the two witnessing indices.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`thm:complete-prime-local`(iii), the valuation claim.** For `|U_p(\mathbf n)|\ge2`,
`v_p(\operatorname{cont}\Delta_{\mathbf n})=0`. -/
theorem complete_prime_local_case_iii_valuation {r : ℕ} (n : Fin r → ℕ) (hn : ∀ i, 0 < n i)
    {p : ℕ} (hp : p.Prime) (hU2 : ∃ i0 i1 : Fin r, i0 ≠ i1 ∧ ¬ p ∣ n i0 ∧ ¬ p ∣ n i1) :
    (cont (Delta n)).factorization p = 0 := by
  obtain ⟨i0, i1, hi01, hni0, hni1⟩ := hU2
  obtain ⟨d, hd⟩ : ∃ d, ¬ (p : ℤ) ∣ coeff d (Delta n) := by
    by_cases hcarry : p ≤ ∑ i, (n i % p)
    · exact exists_coeff_not_dvd_of_carry n hn hp hcarry
    · push_neg at hcarry
      set N := ∑ i, n i with hNdef
      set s := N % p with hsdef
      set h := N / p with hhdef
      have hdm := Nat.div_add_mod N p
      have hspN : N = h * p + s := by
        rw [hhdef, hsdef, mul_comm]; omega
      have hslt : s < p := Nat.mod_lt N hp.pos
      have hnocarry : ∑ i, (n i / p) = h := by
        have hle := sum_div_le_div_sum n p
        have hnlt : ¬ (∑ i, (n i / p) < N / p) :=
          fun hlt => absurd ((sum_div_lt_div_sum_iff n p hp.pos).mp hlt) (not_le.mpr hcarry)
        rw [← hNdef] at hle
        rw [hhdef]
        omega
      have hsumeq : ∑ i, (n i % p) = s := by
        have hkey := sum_eq_mul_sum_div_add_sum_mod n p
        rw [hnocarry] at hkey
        have hdm := Nat.div_add_mod N p
        rw [hhdef, hsdef] at *
        omega
      have hs2 : 2 ≤ s := by
        rw [← hsumeq]
        have h0pos : 1 ≤ n i0 % p := Nat.one_le_iff_ne_zero.mpr
          (fun h0 => hni0 (Nat.dvd_of_mod_eq_zero h0))
        have h1pos : 1 ≤ n i1 % p := Nat.one_le_iff_ne_zero.mpr
          (fun h1 => hni1 (Nat.dvd_of_mod_eq_zero h1))
        have hle : (n i0 % p) + (n i1 % p) ≤ ∑ i, (n i % p) := by
          have hsub : ({i0, i1} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
          have hss := Finset.sum_le_sum_of_subset (f := fun i => n i % p) hsub
          rwa [Finset.sum_pair hi01] at hss
        omega
      exact exists_coeff_not_dvd_of_no_carry n hp hs2 hslt hspN ⟨i0, i1, hi01, hni0, hni1⟩
  have hcontne : cont (Delta n) ≠ 0 := by
    intro h0
    apply hd
    have hzero : Delta n = 0 := by
      by_contra hne
      exact (cont_ne_zero_of_ne_zero hne) h0
    rw [hzero, coeff_zero]
    exact dvd_zero _
  by_contra hne0
  have hdvd : p ∣ cont (Delta n) :=
    (Nat.Prime.dvd_iff_one_le_factorization hp hcontne).mpr (by omega)
  have hdvd2 : (p : ℤ) ∣ coeff d (Delta n) := by
    have hcdvd : cont (Delta n) ∣ (coeff d (Delta n)).natAbs := by
      by_cases hdmem : d ∈ (Delta n).support
      · unfold cont; exact Finset.gcd_dvd hdmem
      · rw [mem_support_iff, not_not] at hdmem; rw [hdmem]; simp
    have hh2 := hdvd.trans hcdvd
    have h2 := Int.natCast_dvd_natCast.mpr hh2
    rwa [Int.dvd_natAbs] at h2
  exact hd hdvd2

#print axioms complete_prime_local_case_iii_valuation

end CongruenceTheory
