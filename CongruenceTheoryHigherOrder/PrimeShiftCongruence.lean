import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.PrimeValue
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant

/-!
**`thm:complete-prime-local`(iii)'s `(A10)` shift congruence, the prime-value half**:
`C_p\equiv X_1^p-X_p\pmod p`. Transports `CongruenceTheory.PrimeValue`'s `Cperm_prime_decomp`
(`Cperm p = X_1^p+(p-1)!X_p+pQ`, from Part I) to `C p` via `Cperm_eq_C`, then uses Wilson's
lemma `(p-1)!\equiv-1\pmod p` to identify the coefficient of `X_p`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`C_p\equiv X_1^p-X_p\pmod p`**, as an equality in `MvPolynomial ℕ (ZMod p)`. -/
theorem map_C_p_eq (p : ℕ) (hp : p.Prime) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (C p) =
      (MvPolynomial.X 1 : MvPolynomial ℕ (ZMod p)) ^ p - MvPolynomial.X p := by
  haveI := Fact.mk hp
  obtain ⟨Q, hQ⟩ := Cperm_prime_decomp p hp
  rw [← Cperm_eq_C, hQ]
  simp only [map_add, map_mul, map_pow, MvPolynomial.map_X]
  have hpz : (MvPolynomial.map (Int.castRingHom (ZMod p)) (p : MvPolynomial ℕ ℤ)) = 0 := by
    rw [map_natCast]
    simp
  have hwilson : (MvPolynomial.map (Int.castRingHom (ZMod p))
      ((Nat.factorial (p - 1) : ℕ) : MvPolynomial ℕ ℤ)) =
      MvPolynomial.C (-1 : ZMod p) := by
    rw [map_natCast]
    rw [(map_natCast (MvPolynomial.C : ZMod p →+* MvPolynomial ℕ (ZMod p))
      (Nat.factorial (p - 1))).symm]
    exact congrArg MvPolynomial.C (ZMod.wilsons_lemma p)
  rw [hpz, hwilson]
  simp
  ring

#print axioms map_C_p_eq

end CongruenceTheory
