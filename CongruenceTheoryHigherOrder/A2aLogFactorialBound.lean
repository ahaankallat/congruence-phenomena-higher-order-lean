import Mathlib

open Nat

/-!
**The missing valuation lemma for (A2a)'s non-cut-vertex case, closing the gap identified in
review**: the manuscript's proof of the non-cut-vertex case obtains the cardinality bound
`|A|≤R_u∏_{i≠u}(R_i-1)!` (`card_le_root_bound`, `A2aRootBound.lean`) and then asserts this implies
the valuation bound `v_p(|A|)≤1+Σv_p((R_i-1)!)` "since `v_p(R_u)≤1+v_p((R_u-1)!)`". That inference
is invalid as stated: `a≤b` does not imply `v_p(a)≤v_p(b)` in general (e.g. `8<10` but
`v_2(8)=3>1=v_2(10)`). The correct replacement bounds the orbit size (which only satisfies `≤R_u`,
not a divisibility relation to `R_u`) via `Nat.log p R_u` instead of `v_p(R_u)` directly: for any
positive integer `n` with `p^k∣n`, `n≤R` forces `p^k≤R`, so `k≤Nat.log p R`. This file proves the
numeric fact that closes the resulting estimate: `Nat.log p R ≤ 1+v_p((R-1)!)`.
-/

/-- **The replacement valuation lemma.** For `p` prime and `R≥1`, `Nat.log p R ≤
1+(R-1)!.factorization p`. Proof: put `k=Nat.log p R`. If `k=0` the bound is immediate since the
right side is always `≥0` and in fact `≥1`... but we only need `≥0`. If `k≥1`, then `p^k≤R` (by
definition of `Nat.log`), so `p^(k-1)≤p^k-1≤R-1` (since `p≥2` gives `p^(k-1)(p-1)≥p^(k-1)≥1`).
Hence `p^(k-1)` is itself one of the factors `1,…,R-1` multiplied together in `(R-1)!`, so
`p^(k-1)∣(R-1)!`, giving `(R-1)!.factorization p ≥ k-1`, i.e. `k≤1+(R-1)!.factorization p`. -/
theorem log_le_one_add_factorization_factorial_pred {p : ℕ} (hp : p.Prime) (R : ℕ) (hR : 1 ≤ R) :
    Nat.log p R ≤ 1 + (R - 1).factorial.factorization p := by
  set k := Nat.log p R with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · omega
  have hpk_le_R : p ^ k ≤ R := Nat.pow_log_le_self p (by omega)
  have hpk_eq : p ^ k = p * p ^ (k - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have h1le : 1 ≤ p ^ (k - 1) := Nat.one_le_pow _ _ hp.pos
  have hstep : p ^ (k - 1) ≤ p ^ k - 1 := by
    have h2 : 2 * p ^ (k - 1) ≤ p * p ^ (k - 1) := Nat.mul_le_mul_right _ hp.two_le
    omega
  have hRm1 : p ^ (k - 1) ≤ R - 1 := by omega
  have hpos : 0 < p ^ (k - 1) := Nat.pow_pos hp.pos
  have hdvd : p ^ (k - 1) ∣ (R - 1).factorial :=
    Nat.dvd_factorial hpos hRm1
  have hval : (k - 1) ≤ (R - 1).factorial.factorization p := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.factorial_ne_zero (R - 1))).mp hdvd
    exact this
  omega
