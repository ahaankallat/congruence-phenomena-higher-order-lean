import Mathlib
import CongruenceTheoryHigherOrder.LiftAllPrimes
import CongruenceTheory.CpermEqC
import CongruenceTheory.StrongWeighted
import CongruenceTheory.WeightedSpecialization
import CongruenceTheory.PrimeValue

/-!
**Closed formula at odd prime powers** (main paper, Corollary `cor:odd-prime-power`, in
Section "Closed formulas for `A_w(p^r)` modulo `p^r`", together with Lemma `lem:pth-power`).

* `pth_power_congr` is Lemma `lem:pth-power`: `x ≡ y (mod p^r)` with `r ≥ 1` implies
  `x^p ≡ y^p (mod p^(r+1))`.
* `Aw_lift_odd` is the evaluated lifting theorem: `A_w(p^(r+1)) ≡ A_w(p^r)^p (mod p^(2r))`
  for odd `p` (Theorem `thm:strong-all-primes` with `k = p^r`, evaluated at the weights `w`).
* `Aw_prime_cong` is the base case `A_w(p) ≡ w_1 + (p-1) w_p (mod p)`.
* `odd_prime_power_residue` is Corollary `cor:odd-prime-power`:
  `A_w(p^r) ≡ (w_1 + (p-1) w_p)^(p^(r-1)) (mod p^r)` for odd `p`, `r ≥ 1`.

Here `Aw` is the recurrence-defined `A_w(n) = C_n(w)` of Part I.  The namespace is
`CongruenceTheory.Shift`, so `C` is still `CongruenceTheory.C`.
-/

namespace CongruenceTheory.Shift

open MvPolynomial

/-- `A_w(n) = C_n(w)` agrees with the permutation-native `AwPerm` (the proof in Part I,
`Aw_eq_AwPerm`, is repeated here because the pinned Part I dependency predates that file). -/
theorem Aw_eq_AwPerm (w : ℕ → ℤ) (n : ℕ) : Aw w n = AwPerm w n := by
  rw [Aw, AwPerm, Cperm_eq_C]

/-- Coefficientwise divisibility passes to evaluations. -/
theorem dvd_eval_of_dvd_coeff {m : ℤ} {P : MvPolynomial ℕ ℤ} (h : ∀ d, m ∣ coeff d P)
    (w : ℕ → ℤ) : m ∣ MvPolynomial.eval w P := by
  rw [MvPolynomial.eval_eq]
  exact Finset.dvd_sum fun d _ => (h d).mul_right _

/-- Lemma `lem:pth-power`: if `x ≡ y (mod p^r)` with `r ≥ 1` then `x^p ≡ y^p (mod p^(r+1))`. -/
theorem pth_power_congr {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {x y : ℤ}
    (h : (p : ℤ) ^ r ∣ x - y) : (p : ℤ) ^ (r + 1) ∣ x ^ p - y ^ p := by
  haveI := Fact.mk hp
  have hpxy : (p : ℤ) ∣ x - y := (dvd_pow_self (p : ℤ) (by omega)).trans h
  have hsum : (p : ℤ) ∣ ∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hxy : (x : ZMod p) = y := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpxy
      push_cast at this
      exact sub_eq_zero.mp this
    push_cast
    rw [hxy]
    have : ∀ i ∈ Finset.range p, (y : ZMod p) ^ i * (y : ZMod p) ^ (p - 1 - i) = (y : ZMod p) ^ (p - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl this]
    simp
  have e : x ^ p - y ^ p = (∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)) * (x - y) :=
    (geom_sum₂_mul x y p).symm
  rw [e, pow_succ']
  exact mul_dvd_mul hsum h

/-- The lifting theorem evaluated at weights, for odd `p`:
`A_w(p^(r+1)) ≡ A_w(p^r)^p (mod p^(2r))`. -/
theorem Aw_lift_odd {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (w : ℕ → ℤ) {r : ℕ} (hr : 1 ≤ r) :
    (p : ℤ) ^ (2 * r) ∣ Aw w (p ^ (r + 1)) - Aw w (p ^ r) ^ p := by
  have hk : 0 < p ^ r := pow_pos hp.pos r
  have hpk : p ∣ p ^ r := dvd_pow_self p (by omega)
  have hfac : (p ^ r).factorization p = r := by
    rw [Nat.Prime.factorization_pow hp]; simp
  have h := dvd_eval_of_dvd_coeff (lift_all_primes hp hk hpk) w
  rw [hfac, if_neg hodd] at h
  have e : p * p ^ r = p ^ (r + 1) := by ring
  rw [e] at h
  simpa [Aw, map_sub, map_pow] using h

/-- Base case: `A_w(p) ≡ w_1 + (p-1) w_p (mod p)`. -/
theorem Aw_prime_cong {p : ℕ} (hp : p.Prime) (w : ℕ → ℤ) :
    (p : ℤ) ∣ Aw w p - (w 1 + ((p : ℤ) - 1) * w p) := by
  have h := AwPerm_prime_cong w p hp
  rw [← Aw_eq_AwPerm] at h
  have e : Aw w p - (w 1 + ((p : ℤ) - 1) * w p) =
      (Aw w p - (w 1 - w p)) - (p : ℤ) * w p := by ring
  rw [e]
  exact dvd_sub h (dvd_mul_right _ _)

/-- **Corollary `cor:odd-prime-power`.**  For an odd prime `p`, an integral weight sequence `w`
and `r ≥ 1`, `A_w(p^r) ≡ (w_1 + (p-1) w_p)^(p^(r-1)) (mod p^r)`. -/
theorem odd_prime_power_residue {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (w : ℕ → ℤ) :
    ∀ r : ℕ, 1 ≤ r →
      (p : ℤ) ^ r ∣ Aw w (p ^ r) - (w 1 + ((p : ℤ) - 1) * w p) ^ (p ^ (r - 1)) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => simpa using Aw_prime_cong hp w
  | succ r hr ih =>
    have h1 := Aw_lift_odd hp hodd w hr
    have h2 := pth_power_congr hp hr ih
    have hle : (p : ℤ) ^ (r + 1) ∣ (p : ℤ) ^ (2 * r) := pow_dvd_pow _ (by omega)
    have e : (w 1 + ((p : ℤ) - 1) * w p) ^ (p ^ (r + 1 - 1)) =
        ((w 1 + ((p : ℤ) - 1) * w p) ^ (p ^ (r - 1))) ^ p := by
      rw [← pow_mul, ← pow_succ]
      congr 2
      omega
    rw [e]
    have key : Aw w (p ^ (r + 1)) - ((w 1 + ((p : ℤ) - 1) * w p) ^ (p ^ (r - 1))) ^ p
        = (Aw w (p ^ (r + 1)) - Aw w (p ^ r) ^ p)
          + (Aw w (p ^ r) ^ p - ((w 1 + ((p : ℤ) - 1) * w p) ^ (p ^ (r - 1))) ^ p) := by ring
    rw [key]
    exact dvd_add (hle.trans h1) h2

end CongruenceTheory.Shift
