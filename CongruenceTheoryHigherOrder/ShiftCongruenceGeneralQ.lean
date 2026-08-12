import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.ShiftCongruenceSetup
import CongruenceTheoryHigherOrder.ShiftCongruenceOrbit
import CongruenceTheoryHigherOrder.ShiftCongruenceOrbitSize
import CongruenceTheoryHigherOrder.ShiftCongruenceCentralizerSum
import CongruenceTheoryHigherOrder.ShiftCongruenceCentralizerFinal
import CongruenceTheoryHigherOrder.ShiftCongruenceQ1

/-!
**`thm:complete-prime-local`(iii)'s `(A10)` shift congruence, general `q`.**
`\text{Cperm}(pq+r)\equiv\text{Cperm}(r)\cdot\text{Cperm}(p)^q\pmod p`, by induction on `q`
using the `q=1` case (`Cperm_shift_cong_q1`) as the inductive step.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm

variable {p : ℕ}

/-- **The full `(A10)` shift congruence**:
`\text{Cperm}(pq+r)\equiv\text{Cperm}(r)\cdot\text{Cperm}(p)^q\pmod p`. -/
theorem Cperm_shift_cong (hp : p.Prime) (q r : ℕ) :
    (p : MvPolynomial ℕ ℤ) ∣ (Cperm (p * q + r) - Cperm r * Cperm p ^ q) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 := Cperm_shift_cong_q1 (M := p * q + r) hp
    have h2 : (p : MvPolynomial ℕ ℤ) ∣
        (Cperm p * Cperm (p * q + r) - Cperm p * (Cperm r * Cperm p ^ q)) := by
      have := ih.mul_left (Cperm p)
      rwa [mul_sub] at this
    have h3 : (p : MvPolynomial ℕ ℤ) ∣
        (Cperm (p + (p * q + r)) - Cperm p * (Cperm r * Cperm p ^ q)) := by
      have hsum := dvd_add h1 h2
      rwa [sub_add_sub_cancel] at hsum
    have heq1 : p + (p * q + r) = p * (q + 1) + r := by ring
    have heq2 : Cperm p * (Cperm r * Cperm p ^ q) = Cperm r * Cperm p ^ (q + 1) := by
      rw [pow_succ]; ring
    rw [heq1, heq2] at h3
    exact h3

#print axioms Cperm_shift_cong

end CongruenceTheory
