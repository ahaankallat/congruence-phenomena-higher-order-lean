import Mathlib

open Nat

/-!
**Two self-contained valuation facts from (A2a)'s cut-vertex case.** The manuscript's proof of
(A2a) when the root block `u` *is* a cut vertex needs, among other things, two elementary `p`-adic
valuation bounds to close its final estimate: "`v_p(a_0)≤1+v_p((a_0-1)!)`" and
"`v_p(a_τ)≤v_p(a_τ!)`" (where `a_0`,`a_τ` are attachment numbers of tree components). Both are
pure number-theoretic facts about `Nat.factorization`, independent of the surrounding
graph-component/rooted-isomorphism-type machinery (components of the incidence graph minus `u`,
grouping into isomorphism types `τ` with multiplicities `m_τ`, and the accompanying multinomial
divisibility `(R_u-1)!/((a_0-1)!∏_τ(a_τ!)^{m_τ}m_τ!)∈ℕ`) — that combinatorial machinery is a
further substantial undertaking, comparable in scope to the wreath-product argument for (A1), and
is not attempted here.
-/

/-- `v_p(n) ≤ v_p(n!)`, immediate from `n! = n·(n-1)!`. This is the manuscript's
"`v_p(a_τ)≤v_p(a_τ!)`" fact from (A2a)'s cut-vertex case. -/
theorem factorization_le_factorization_factorial (p n : ℕ) :
    n.factorization p ≤ n.factorial.factorization p := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · have hfact : n.factorial = n * (n - 1).factorial := (Nat.mul_factorial_pred hn.ne').symm
    rw [hfact, Nat.factorization_mul hn.ne' (Nat.factorial_ne_zero _)]
    simp

/-- A division identity used below: for `p>0` and `m≥1`, `(p·m-1)/p = m-1`. -/
theorem aux_div_pred (p m : ℕ) (hp : 0 < p) (hm : 1 ≤ m) : (p * m - 1) / p = m - 1 := by
  have hpm : p * (m - 1) = p * m - p := Nat.mul_pred p m
  have hcp : p ≤ p * m := Nat.le_mul_of_pos_right p hm
  have hsplit : p * m - 1 = (p - 1) + p * (m - 1) := by
    rw [hpm]; omega
  rw [hsplit, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega), zero_add]

/-- `v_p(n) ≤ 1+v_p((n-1)!)` for `n≥1`. This is the manuscript's "`v_p(a_0)≤1+v_p((a_0-1)!)`" fact
from (A2a)'s cut-vertex case (and is exactly the same shape as the non-cut-vertex case's own
"`v_p(R_u)≤1+v_p((R_u-1)!)`" remark, which `card_le_root_bound`, `A2aRootBound.lean`, bypasses by
working with the literal `Nat` inequality `|A|≤R_u∏(R_i-1)!` directly rather than through
valuations). Proof: writing `k=v_p(n)`, `p^k∣n` gives `n≥p^k≥2p` (using `k≥2`; the case `k≤1` is
immediate), so `(n-1)/p ≥ p-1` is too coarse — instead the single Legendre-sum term at `i=1` gives
`v_p((n-1)!)≥(n-1)/p≥(p^k-1)/p=p^{k-1}-1` (via `aux_div_pred`), and `p^{k-1}≥k` (`Nat.lt_pow_self`)
finishes: `k≤p^{k-1}≤1+(p^{k-1}-1)≤1+(n-1)/p≤1+v_p((n-1)!)`. -/
theorem factorization_le_one_add_factorization_factorial_pred {p : ℕ} (hp : p.Prime) (n : ℕ)
    (hn : 1 ≤ n) : n.factorization p ≤ 1 + (n - 1).factorial.factorization p := by
  set k := n.factorization p with hk
  by_cases hk1 : k ≤ 1
  · omega
  have hk1' : 1 < k := by omega
  have hpk : p ^ k ∣ n := Nat.ordProj_dvd n p
  have hnpk : p ^ k ≤ n := Nat.le_of_dvd (by omega) hpk
  have hp2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.one_le (by omega)
  have hpp : p * p ≤ p ^ k := by rw [sq] at hp2; exact hp2
  have hn2p : 2 * p ≤ n := (Nat.mul_le_mul hp.two_le (le_refl p)).trans (hpp.trans hnpk)
  have hnge : p ≤ n - 1 := by omega
  have hpk1 : p ^ k = p * p ^ (k - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hge1 : 1 ≤ p ^ (k - 1) := Nat.one_le_pow _ _ hp.pos
  have hlegendre : (n - 1).factorial.factorization p =
      ∑ i ∈ Finset.Ico 1 (Nat.log p (n - 1) + 1), (n - 1) / p ^ i :=
    Nat.factorization_factorial hp (Nat.lt_add_one _)
  have hmem : (1 : ℕ) ∈ Finset.Ico 1 (Nat.log p (n - 1) + 1) := by
    simp only [Finset.mem_Ico]
    refine ⟨le_refl 1, ?_⟩
    have h1 : 1 ≤ Nat.log p (n - 1) := Nat.le_log_of_pow_le hp.one_lt (by simpa using hnge)
    omega
  have hterm : (n - 1) / p ≤ (n - 1).factorial.factorization p := by
    rw [hlegendre]
    have := Finset.single_le_sum (f := fun i => (n - 1) / p ^ i)
      (fun i _ => Nat.zero_le ((n - 1) / p ^ i)) hmem
    simpa using this
  have hexact : p ^ (k - 1) - 1 ≤ (n - 1) / p := by
    calc p ^ (k - 1) - 1 = (p ^ k - 1) / p := by rw [hpk1, aux_div_pred p (p ^ (k - 1)) hp.pos hge1]
      _ ≤ (n - 1) / p := Nat.div_le_div_right (by omega)
  have hpow : k ≤ p ^ (k - 1) := by
    have hlt : k - 1 < p ^ (k - 1) := Nat.lt_pow_self hp.one_lt
    omega
  calc k ≤ p ^ (k - 1) := hpow
    _ ≤ 1 + (p ^ (k - 1) - 1) := by omega
    _ ≤ 1 + (n - 1) / p := by omega
    _ ≤ 1 + (n - 1).factorial.factorization p := by omega
