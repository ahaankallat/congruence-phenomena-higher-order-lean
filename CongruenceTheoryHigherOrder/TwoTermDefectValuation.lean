import Mathlib
import CongruenceTheory.OptimalDivisorC
import CongruenceTheory.PrimeWitness
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.CycleDepthHierarchy

/-!
**The exact `p`-adic content valuation of the two-term defect `C_{n+k}-C_nC_k` when `p` divides
only one of `n,k`** — matching Part I's `thm:optimal-divisor` (the manuscript's `[Theorem~4.6]`
cited in `thm:complete-prime-local`(ii)). Uses `CongruenceTheory.OptimalDivisorC`'s
`treeM_dvd_defect` (already-proven lower bound, imported from the `congruencetheory` package)
for the lower bound, and a direct Vandermonde computation of the `X_2X_1^{n+k-2}` coefficient
(exactly `nk`) for the matching upper bound.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **Vandermonde at `k=2`**: `(n+k).choose 2 = n.choose 2 + n*k + k.choose 2`. -/
theorem choose_two_add (n k : ℕ) :
    (n + k).choose 2 = n.choose 2 + n * k + k.choose 2 := by
  have hvdm := Nat.add_choose_eq n k 2
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hvdm
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hvdm
  norm_num [Nat.choose_zero_right, Nat.choose_one_right] at hvdm
  omega

/-- **The `X_2X_1^{n+k-2}` coefficient of `C_{n+k}-C_nC_k` equals `nk` exactly.** -/
theorem coeff_defect_two_eq_mul (n k : ℕ) :
    coeff (ciExp (n + k - 2) {2}) (C (n + k) - C n * C k) = (n * k : ℤ) := by
  rw [← Cperm_eq_C, ← Cperm_eq_C, ← Cperm_eq_C, ← CpermPair_eq_Cperm]
  rw [coeff_defect_singleCycle n k 2 (by norm_num)]
  rw [choose_two_add]
  push_cast
  ring

/-- **`treeM n k`'s content-divisibility, transported to `cont`.** -/
theorem treeM_dvd_cont (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    treeM n k ∣ cont (C (n + k) - C n * C k) := by
  unfold cont
  apply Finset.dvd_gcd
  intro d _
  have h := treeM_dvd_defect n k hn hk d
  have h2 := Int.natAbs_dvd_natAbs.mpr h
  rwa [Int.natAbs_natCast] at h2

/-- **`cont(C_{n+k}-C_nC_k)` divides `nk`.** -/
theorem cont_dvd_mul (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    cont (C (n + k) - C n * C k) ∣ n * k := by
  have hcoeff := coeff_defect_two_eq_mul n k
  have hne : coeff (ciExp (n + k - 2) {2}) (C (n + k) - C n * C k) ≠ 0 := by
    rw [hcoeff]
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    exact mul_ne_zero hn0 hk0
  have hmem : ciExp (n + k - 2) {2} ∈ (C (n + k) - C n * C k).support := mem_support_iff.mpr hne
  unfold cont
  have hdvd := Finset.gcd_dvd (f := fun d => (coeff d (C (n + k) - C n * C k)).natAbs) hmem
  rw [hcoeff, show ((n : ℤ) * k).natAbs = n * k from by rw [Int.natAbs_mul]; simp] at hdvd
  exact hdvd

/-- **The exact `p`-adic content valuation of the two-term defect when `p\nmid n`.** -/
theorem padicValNat_cont_two_term_of_not_dvd_left {p n k : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hpn : ¬ p ∣ n) :
    (cont (C (n + k) - C n * C k)).factorization p = padicValNat p k := by
  have hcontne : cont (C (n + k) - C n * C k) ≠ 0 := by
    intro h0
    have hd := cont_dvd_mul n k hn hk
    rw [h0, Nat.zero_dvd] at hd
    exact (Nat.mul_ne_zero (by omega) (by omega)) hd
  have hle : (cont (C (n + k) - C n * C k)).factorization p ≤ padicValNat p k := by
    have hdvd := cont_dvd_mul n k hn hk
    have hmulne : n * k ≠ 0 := by positivity
    have h1 := (Nat.factorization_le_iff_dvd hcontne hmulne).mpr hdvd
    have h2 := h1 p
    rw [Nat.factorization_mul (by omega) (by omega)] at h2
    simp only [Finsupp.coe_add, Pi.add_apply] at h2
    rw [Nat.factorization_eq_zero_of_not_dvd hpn, Nat.factorization_def k hp] at h2
    simpa using h2
  have hge : padicValNat p k ≤ (cont (C (n + k) - C n * C k)).factorization p := by
    have hdvd := treeM_dvd_cont n k hn hk
    have h1 := (Nat.factorization_le_iff_dvd (treeM_ne_zero n k hn hk) hcontne).mpr hdvd
    have h2 := h1 p
    have hgcd1 : ¬ p ∣ Nat.gcd n k := fun hc => hpn (hc.trans (Nat.gcd_dvd_left n k))
    rw [treeM_factorization n k (by omega) (by omega) p hp, if_neg hgcd1] at h2
    have hn0 : padicValNat p n = 0 := by
      rw [← Nat.factorization_def n hp]
      exact Nat.factorization_eq_zero_of_not_dvd hpn
    omega
  omega

#print axioms choose_two_add
#print axioms coeff_defect_two_eq_mul
#print axioms treeM_dvd_cont
#print axioms padicValNat_cont_two_term_of_not_dvd_left

end CongruenceTheory
