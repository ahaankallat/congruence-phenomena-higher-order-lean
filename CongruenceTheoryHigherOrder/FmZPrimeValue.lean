import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.PrimeValue
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.FmDef
import CongruenceTheoryHigherOrder.FmModP

/-!
**`F_p\equiv1-X_p\pmod p`.** Mirrors `PrimeShiftCongruence.lean`'s `map_C_p_eq` (`C_p\equiv
X_1^p-X_p\pmod p`), but for `F_p:=$X_1\mapsto1$ specialization of `C_p`: since `\text{bind₁}` is
a ring hom, applying it to `Cperm_prime_decomp`'s `C_p=X_1^p+(p-1)!X_p+pQ` and reducing `X_1\to1`
turns the `X_1^p` term into `1`, giving `F_p\equiv1+(p-1)!X_p\equiv1-X_p\pmod p` (Wilson). This
identifies `D_{\mathbf c}`'s own `(1-X_p)^h` term with `F_p^h`, closing the loop between
`\Delta_{\mathbf n}`'s factorization (`DeltaFactorization.lean`) and `D_{\mathbf c}`
(`DcDef.lean`).
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`F_p\equiv1-X_p\pmod p`**, as an equality in `\text{MvPolynomial}\;\N\;(\Z/p)`. -/
theorem FmZ_p_eq (p : ℕ) (hp : p.Prime) : FmZ p p = 1 - MvPolynomial.X p := by
  haveI := Fact.mk hp
  obtain ⟨Q, hQ⟩ := Cperm_prime_decomp p hp
  have hCp : C p = MvPolynomial.X 1 ^ p +
      (Nat.factorial (p - 1) : MvPolynomial ℕ ℤ) * MvPolynomial.X p +
        (p : MvPolynomial ℕ ℤ) * Q := by
    rw [← Cperm_eq_C]; exact hQ
  have hpne1 : p ≠ 1 := hp.ne_one
  unfold FmZ Fm
  rw [hCp]
  simp only [map_add, map_mul, map_pow, map_natCast, MvPolynomial.bind₁_X_right, if_neg hpne1,
    reduceIte, one_pow, map_one]
  have hwilson : ((Nat.factorial (p - 1) : ℕ) : MvPolynomial ℕ (ZMod p)) =
      MvPolynomial.C (-1 : ZMod p) := by
    rw [← map_natCast (MvPolynomial.C : ZMod p →+* MvPolynomial ℕ (ZMod p))
      (Nat.factorial (p - 1))]
    exact congrArg MvPolynomial.C (ZMod.wilsons_lemma p)
  have hpz : (↑p : MvPolynomial ℕ (ZMod p)) = 0 := by
    rw [← map_natCast (MvPolynomial.C : ZMod p →+* MvPolynomial ℕ (ZMod p)) p, ZMod.natCast_self]
    exact map_zero _
  rw [hwilson, hpz, zero_mul, add_zero]
  simp only [MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.map_X]
  ring

#print axioms FmZ_p_eq

end CongruenceTheory
