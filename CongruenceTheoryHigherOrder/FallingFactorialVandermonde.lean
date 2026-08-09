import Mathlib

/-!
**The binary falling-factorial Vandermonde identity** — the base case of the manuscript's own
"multivariate falling-factorial Vandermonde identity" ((A6) in `thm:atomic-connected-content`'s
proof, used together with `hypertree_enumerator` to evaluate the Prüfer enumerator in closed
form). Mathlib has Vandermonde's identity for ordinary binomial coefficients
(`Nat.add_choose_eq`); combined with the descFactorial/choose relation
(`Nat.descFactorial_eq_factorial_mul_choose`, `n.descFactorial k = k! * n.choose k`), it converts
directly into the analogous identity for falling factorials, `Nat.descFactorial`:
`(m+n)_k = Σ_{i+j=k} C(k,i)·(m)_i·(n)_j`. **Honest scope note**: this is one self-contained
ingredient the manuscript's (A6) derivation needs (the two-variable case); the full application
needs the *multivariate* (`r`-ary) generalization, applied to `r` equal falling factorials
against the `hypertree_enumerator`'s Prüfer sum — that further assembly is not attempted here.
-/

/-- **The falling-factorial Vandermonde identity** (binary case): `(m+n)_k = Σ_{i+j=k}
C(k,i)·(m)_i·(n)_j`, matching ordinary Vandermonde's identity one level up the
descFactorial/choose correspondence. -/
theorem descFactorial_add_eq (m n k : ℕ) :
    (m + n).descFactorial k =
      ∑ ij ∈ Finset.antidiagonal k,
        k.choose ij.1 * m.descFactorial ij.1 * n.descFactorial ij.2 := by
  have hfact : (m + n).descFactorial k = Nat.factorial k * (m + n).choose k :=
    Nat.descFactorial_eq_factorial_mul_choose (m + n) k
  rw [hfact, Nat.add_choose_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hijk : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
  have hm : m.descFactorial ij.1 = Nat.factorial ij.1 * m.choose ij.1 :=
    Nat.descFactorial_eq_factorial_mul_choose m ij.1
  have hn : n.descFactorial ij.2 = Nat.factorial ij.2 * n.choose ij.2 :=
    Nat.descFactorial_eq_factorial_mul_choose n ij.2
  rw [hm, hn]
  have hkfact : k.choose ij.1 * Nat.factorial ij.1 * Nat.factorial ij.2 = Nat.factorial k := by
    have h := Nat.choose_mul_factorial_mul_factorial (show ij.1 ≤ k by omega)
    rwa [show k - ij.1 = ij.2 by omega] at h
  rw [show k.choose ij.1 * (Nat.factorial ij.1 * m.choose ij.1) *
      (Nat.factorial ij.2 * n.choose ij.2) =
      (k.choose ij.1 * Nat.factorial ij.1 * Nat.factorial ij.2) *
        (m.choose ij.1 * n.choose ij.2) by ring]
  rw [hkfact]

#print axioms descFactorial_add_eq
