import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.TranspositionCoefficientDelta

/-!
**The closed form of the transposition coefficient**: unfolding `coeff_transposition_cons`'s
recursion all the way down gives `[X_2X_1^{N-2}]\Delta_{\mathbf n} = \sum_{i<j}n_in_j` for a
general tuple `\mathbf n` of any length `r` with every entry `\ge2`, matching the manuscript's
"transposition coefficient in the full defect" formula used throughout
`thm:complete-prime-local`(ii).
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`C_0=1`.** -/
theorem C_zero_eq_one : C 0 = (1 : MvPolynomial ℕ ℤ) := by rw [← Cperm_eq_C]; exact Cperm_zero

/-- **The pairwise cross-sum** `\sum_{i<j}n_in_j`, defined recursively via `Fin.cons`
(`pairSum(\text{cons}\ a\ n) = a\cdot\sum n_i + \text{pairSum}(n)`, `\text{pairSum}(\text{empty})
= 0`) to match `coeff_transposition_cons`'s own recursive shape exactly. -/
noncomputable def pairSum : ∀ {r : ℕ}, (Fin r → ℕ) → ℤ
  | 0, _ => 0
  | t + 1, n => (n 0 : ℤ) * (∑ i : Fin t, (n i.succ : ℤ)) + pairSum (Fin.tail n)

theorem pairSum_cons {t : ℕ} (a : ℕ) (m : Fin t → ℕ) :
    pairSum (Fin.cons a m : Fin (t + 1) → ℕ) = (a : ℤ) * (∑ i, m i : ℤ) + pairSum m := by
  show (Fin.cons a m : Fin (t + 1) → ℕ) 0 *
      (∑ i : Fin t, ((Fin.cons a m : Fin (t + 1) → ℕ) i.succ : ℤ)) +
      pairSum (Fin.tail (Fin.cons a m : Fin (t + 1) → ℕ)) = _
  simp [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons]

/-- **`\Delta_{\mathbf n}=0` for a `1`-block tuple.** -/
theorem Delta_eq_zero_of_one (n : Fin 1 → ℕ) : Delta n = 0 := by
  unfold Delta
  rw [Fin.sum_univ_one, Fin.prod_univ_one]
  ring

/-- **`\text{pairSum}=0` for a `1`-block tuple.** -/
theorem pairSum_eq_zero_of_one (n : Fin 1 → ℕ) : pairSum n = 0 := by
  have hn0 : n = Fin.cons (n 0) (Fin.tail n : Fin 0 → ℕ) := (Fin.cons_self_tail n).symm
  rw [hn0, pairSum_cons]
  simp [pairSum]

/-- **The transposition coefficient of `\Delta_{\mathbf n}` equals `\text{pairSum}(\mathbf n)`
exactly**, for any tuple `\mathbf n` with every entry `\ge2`. -/
theorem coeff_transposition_eq_pairSum {r : ℕ} (n : Fin r → ℕ) (hn2 : ∀ i, 2 ≤ n i) :
    coeff (ciExp ((∑ i, n i) - 2) {2}) (Delta n) = pairSum n := by
  induction r with
  | zero =>
    unfold Delta pairSum
    simp [C_zero_eq_one]
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      rw [Delta_eq_zero_of_one n, pairSum_eq_zero_of_one n]
      simp
    · set a := n 0 with ha
      set m := Fin.tail n with hm
      have hn0 : n = Fin.cons a m := (Fin.cons_self_tail n).symm
      have htail2 : ∀ i, 2 ≤ m i := fun i => hn2 i.succ
      obtain ⟨i0⟩ : Nonempty (Fin t) := ⟨⟨0, htpos⟩⟩
      have hB2 : 2 ≤ ∑ i, m i :=
        calc 2 ≤ m i0 := htail2 i0
          _ ≤ ∑ i, m i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)
      rw [hn0]
      rw [Fin.sum_cons, coeff_transposition_cons a m hB2, pairSum_cons, ih m htail2]

#print axioms C_zero_eq_one
#print axioms pairSum_cons
#print axioms Delta_eq_zero_of_one
#print axioms pairSum_eq_zero_of_one
#print axioms coeff_transposition_eq_pairSum

end CongruenceTheory
