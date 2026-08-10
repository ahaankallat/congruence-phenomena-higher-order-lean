import Mathlib

/-!
**The root multinomial absorption, closing (H-cut).** The manuscript's cut-vertex proof of (A2a)
needs, purely arithmetically, that
`(a_0-1)! * ∏_τ (a_τ!)^{m_τ} * m_τ! ∣ (a_0 + Σ_τ m_τ a_τ - 1)!` for arbitrary positive integers
`a_0` and, for each `τ` in a finite index set, `a_τ,m_τ`. This is a standard "labeled items into
one distinguished group plus repeated-size unordered groups" multinomial fact, with **no
dependence on what the index set `τ` denotes** — in particular, it holds whether or not the `τ`
range over the manuscript's rooted-isomorphism types or merely `compType`-fibers (`compType`'s two
numeric invariants determine `a_τ`; whether it also captures true rooted-isomorphism is irrelevant
to this identity, since `Nat.uniformBell_mul_eq` treats each `τ`'s `m_τ` same-size groups as
interchangeable labels regardless of what "type" they represent).

Built from two standard facts already in Mathlib: `Nat.uniformBell_mul_eq` (`n!^m·m! ∣ (mn)!`, the
single-size case, via the Bell-number identity for a replicated multiset) and
`Nat.factorial_mul_factorial_dvd_factorial` (`k!·(n-k)! ∣ n!`, ordinary binomial divisibility, used
to combine sizes one `τ` at a time and to split off the distinguished `a_0-1` group at the end).
-/

open Finset Nat

/-- **Single-type case**: `m` unordered groups of the same positive size `n` fit inside `(mn)!`. -/
theorem factorial_pow_mul_factorial_dvd_factorial_mul (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    n ! ^ m * m ! ∣ (m * n)! :=
  ⟨Nat.uniformBell m n, by rw [← Nat.uniformBell_mul_eq m hn]; ring⟩

/-- **Multiple types**: summing the single-type case across a finite index set `T`, via ordinary
binomial divisibility to combine the running total with each newly peeled type. -/
theorem prod_factorial_pow_mul_factorial_dvd_factorial {γ : Type*} [DecidableEq γ]
    (T : Finset γ) (a m : γ → ℕ) (ha : ∀ τ ∈ T, a τ ≠ 0) :
    (∏ τ ∈ T, (a τ)! ^ (m τ) * (m τ)!) ∣ (∑ τ ∈ T, m τ * a τ)! := by
  induction T using Finset.induction with
  | empty => simp
  | insert τ1 T hτ1 ih =>
    rw [Finset.prod_insert hτ1, Finset.sum_insert hτ1]
    have h1 : (a τ1)! ^ (m τ1) * (m τ1)! ∣ (m τ1 * a τ1)! :=
      factorial_pow_mul_factorial_dvd_factorial_mul (m τ1) (ha τ1 (Finset.mem_insert_self τ1 T))
    have hIH : (∏ τ ∈ T, (a τ)! ^ (m τ) * (m τ)!) ∣ (∑ τ ∈ T, m τ * a τ)! :=
      ih (fun τ hτ => ha τ (Finset.mem_insert_of_mem hτ))
    have h2 : (m τ1 * a τ1)! * (∑ τ ∈ T, m τ * a τ)! ∣ (m τ1 * a τ1 + ∑ τ ∈ T, m τ * a τ)! := by
      simpa using Nat.factorial_mul_factorial_dvd_factorial
        (Nat.le_add_right (m τ1 * a τ1) (∑ τ ∈ T, m τ * a τ))
    calc (a τ1)! ^ (m τ1) * (m τ1)! * ∏ τ ∈ T, (a τ)! ^ (m τ) * (m τ)!
        ∣ (m τ1 * a τ1)! * ∏ τ ∈ T, (a τ)! ^ (m τ) * (m τ)! := mul_dvd_mul_right h1 _
      _ ∣ (m τ1 * a τ1)! * (∑ τ ∈ T, m τ * a τ)! := mul_dvd_mul_left _ hIH
      _ ∣ (m τ1 * a τ1 + ∑ τ ∈ T, m τ * a τ)! := h2

/-- **The full root multinomial absorption.** -/
theorem multinomial_absorption {γ : Type*} [DecidableEq γ] (T : Finset γ) (a0 : ℕ) (a m : γ → ℕ)
    (ha0 : a0 ≠ 0) (ha : ∀ τ ∈ T, a τ ≠ 0) :
    (a0 - 1)! * ∏ τ ∈ T, (a τ)! ^ (m τ) * (m τ)! ∣ (a0 + ∑ τ ∈ T, m τ * a τ - 1)! := by
  have hrest : (∏ τ ∈ T, (a τ)! ^ (m τ) * (m τ)!) ∣ (∑ τ ∈ T, m τ * a τ)! :=
    prod_factorial_pow_mul_factorial_dvd_factorial T a m ha
  have hsplit : (a0 - 1)! * (∑ τ ∈ T, m τ * a τ)! ∣ (a0 - 1 + ∑ τ ∈ T, m τ * a τ)! := by
    simpa using Nat.factorial_mul_factorial_dvd_factorial
      (Nat.le_add_right (a0 - 1) (∑ τ ∈ T, m τ * a τ))
  have heq : a0 - 1 + ∑ τ ∈ T, m τ * a τ = a0 + ∑ τ ∈ T, m τ * a τ - 1 := by omega
  rw [← heq]
  calc (a0 - 1)! * ∏ τ ∈ T, (a τ)! ^ (m τ) * (m τ)!
      ∣ (a0 - 1)! * (∑ τ ∈ T, m τ * a τ)! := mul_dvd_mul_left _ hrest
    _ ∣ (a0 - 1 + ∑ τ ∈ T, m τ * a τ)! := hsplit
