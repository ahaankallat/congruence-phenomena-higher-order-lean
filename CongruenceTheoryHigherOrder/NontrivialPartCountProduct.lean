import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.NontrivialPartCountK

/-!
**`nontrivialPartCount` accumulates additively across products.** If every nonzero-coefficient
monomial of `P` (resp. `Q`) has `nontrivialPartCount \ge a` (resp. `\ge b`), the same holds for
`P*Q` with bound `a+b`. Applied to the multiset-product `\prod_{j\in\lambda}K_j(p)` (`\lambda` a
shape from (A7)), this shows every nonzero-coefficient monomial has `nontrivialPartCount \ge
k(\lambda)` — the "no early witness" half of the witness-depth (`\delta_p`) argument: no
coefficient of `\Delta_{p\mathbf u}` with fewer than `k(\lambda)` nontrivial parts receives any
contribution from the shape-`\lambda` term of (A7).
-/

namespace CongruenceTheory

open MvPolynomial

/-- **Additivity of the `nontrivialPartCount` lower bound across products.** -/
theorem nontrivialPartCount_ge_of_coeff_mul_ne_zero {P Q : MvPolynomial ℕ ℤ} {a b : ℕ}
    (hP : ∀ d, coeff d P ≠ 0 → a ≤ nontrivialPartCount d)
    (hQ : ∀ d, coeff d Q ≠ 0 → b ≤ nontrivialPartCount d) :
    ∀ d, coeff d (P * Q) ≠ 0 → a + b ≤ nontrivialPartCount d := by
  intro d hd
  rw [coeff_mul] at hd
  by_contra hlt
  push_neg at hlt
  apply hd
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  by_cases hx1 : coeff x.1 P = 0
  · rw [hx1, zero_mul]
  by_cases hx2 : coeff x.2 Q = 0
  · rw [hx2, mul_zero]
  exfalso
  have h1 := hP x.1 hx1
  have h2 := hQ x.2 hx2
  have hsum : a + b ≤ nontrivialPartCount x.1 + nontrivialPartCount x.2 := by omega
  rw [← nontrivialPartCount_add, hx] at hsum
  omega

/-- **Every nonzero coefficient of `P^m` has `nontrivialPartCount \ge m\cdot a`**, given every
nonzero coefficient of `P` has `nontrivialPartCount \ge a`. -/
theorem nontrivialPartCount_ge_of_coeff_pow_ne_zero {P : MvPolynomial ℕ ℤ} {a : ℕ}
    (hP : ∀ d, coeff d P ≠ 0 → a ≤ nontrivialPartCount d) (m : ℕ) :
    ∀ d, coeff d (P ^ m) ≠ 0 → m * a ≤ nontrivialPartCount d := by
  induction m with
  | zero =>
    intro d hd
    simp only [pow_zero] at hd
    simp
  | succ m ih =>
    intro d hd
    rw [pow_succ] at hd
    have := nontrivialPartCount_ge_of_coeff_mul_ne_zero ih hP d hd
    have heq : m * a + a = (m + 1) * a := by ring
    omega

/-- **The multiset-product bound**: every nonzero-coefficient monomial of `\prod_{j\in\lambda}
K_j(p)` (`\lambda` a multiset of block sizes `\ge1`) has `nontrivialPartCount` at least the
number of `\lambda`'s parts `\ge2` — the manuscript's `k(\lambda)`. -/
theorem nontrivialPartCount_ge_of_coeff_prod_K_ne_zero {p : ℕ} (lam : Multiset ℕ)
    (hlam : ∀ j ∈ lam, 1 ≤ j) :
    ∀ d, coeff d ((lam.map (fun j => K j p)).prod) ≠ 0 →
      (lam.filter (2 ≤ ·)).card ≤ nontrivialPartCount d := by
  induction lam using Multiset.induction with
  | empty => intro d hd; simp
  | cons j s ih =>
    intro d hd
    rw [Multiset.map_cons, Multiset.prod_cons] at hd
    have hj1 : 1 ≤ j := hlam j (Multiset.mem_cons_self j s)
    have hs1 : ∀ j' ∈ s, 1 ≤ j' := fun j' hj' => hlam j' (Multiset.mem_cons_of_mem hj')
    by_cases hj2 : 2 ≤ j
    · haveI : NeZero j := ⟨by omega⟩
      have hbound := nontrivialPartCount_ge_of_coeff_mul_ne_zero
        (a := 1) (b := (s.filter (2 ≤ ·)).card)
        (fun d' hd' => nontrivialPartCount_pos_of_coeff_K_ne_zero hj2 hd') (ih hs1) d hd
      rw [Multiset.filter_cons_of_pos (p := fun x => 2 ≤ x) s hj2, Multiset.card_cons]
      omega
    · have hbound := nontrivialPartCount_ge_of_coeff_mul_ne_zero
        (a := 0) (b := (s.filter (2 ≤ ·)).card)
        (fun d' _ => Nat.zero_le _) (ih hs1) d hd
      rw [Multiset.filter_cons_of_neg (p := fun x => 2 ≤ x) s hj2]
      omega

#print axioms nontrivialPartCount_ge_of_coeff_mul_ne_zero
#print axioms nontrivialPartCount_ge_of_coeff_pow_ne_zero
#print axioms nontrivialPartCount_ge_of_coeff_prod_K_ne_zero

end CongruenceTheory
