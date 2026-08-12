import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ShiftCongruenceGeneralQ
import CongruenceTheoryHigherOrder.PrimeShiftCongruence

/-!
**`thm:complete-prime-local`(iii)'s `(A10)` shift congruence, transported from `Cperm` to `C`.**
`Cperm_shift_cong` (`ShiftCongruenceGeneralQ.lean`) is stated for `Cperm`; `Delta` (this
project's actual defect notation) is built from `C` directly. Transports via `Cperm_eq_C`, and
converts the `\Z`-divisibility statement into a clean equality in `\text{MvPolynomial}\;\N\;(\Z
/p)`, matching how `map_C_p_eq` is already phrased.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`(A10)`, transported to `C`**: `C(pq+r)\equiv C(r)C(p)^q\pmod p`. -/
theorem C_shift_cong {p : ℕ} (hp : p.Prime) (q r : ℕ) :
    (p : MvPolynomial ℕ ℤ) ∣ (C (p * q + r) - C r * C p ^ q) := by
  have h := Cperm_shift_cong hp q r
  rwa [Cperm_eq_C, Cperm_eq_C, Cperm_eq_C] at h

/-- **A `\Z`-multiple of `p` maps to `0` in `\text{MvPolynomial}\;\N\;(\Z/p)`.** -/
theorem map_eq_zero_of_dvd (p : ℕ) (x : MvPolynomial ℕ ℤ) (hdvd : (p : MvPolynomial ℕ ℤ) ∣ x) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) x = 0 := by
  obtain ⟨y, rfl⟩ := hdvd
  rw [map_mul]
  have hpz : MvPolynomial.map (Int.castRingHom (ZMod p)) (p : MvPolynomial ℕ ℤ) = 0 := by
    rw [map_natCast]
    simp
  rw [hpz, zero_mul]

/-- **`(A10)`, as an equality in `\text{MvPolynomial}\;\N\;(\Z/p)`**:
`C(pq+r)\equiv C(r)C(p)^q\pmod p`. -/
theorem map_C_shift_cong {p : ℕ} (hp : p.Prime) (q r : ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (C (p * q + r)) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) (C r) *
        MvPolynomial.map (Int.castRingHom (ZMod p)) (C p) ^ q := by
  have hz := map_eq_zero_of_dvd p _ (C_shift_cong hp q r)
  rw [map_sub, map_mul, map_pow] at hz
  exact sub_eq_zero.mp hz

#print axioms C_shift_cong
#print axioms map_eq_zero_of_dvd
#print axioms map_C_shift_cong

end CongruenceTheory
