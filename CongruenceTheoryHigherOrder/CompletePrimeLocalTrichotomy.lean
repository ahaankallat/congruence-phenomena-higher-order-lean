import Mathlib

/-!
**`thm:complete-prime-local`'s own case trichotomy**: `U_p(\mathbf n):=\{i : p\nmid n_i\}$ is
either empty (case i), a singleton (case ii), or has at least two elements (case iii) — no other
possibility. This is the purely combinatorial fact selecting which of
`complete_prime_local_case_i_general`/`_case_ii_general`/`_case_iii_valuation` applies to a given
tuple `n`; each of those theorems still needs its own further hypotheses (an achieved shape for
case (i), the depth witnesses `E,d` for case (ii)) supplied separately, so this is stated on its
own rather than folded into one monolithic dispatch.
-/

namespace CongruenceTheory

/-- **`U_p(\mathbf n)` is empty, a singleton, or has `\ge 2` elements — no other case.** -/
theorem Up_trichotomy {r : ℕ} (n : Fin r → ℕ) (p : ℕ) :
    (∀ i, p ∣ n i) ∨ (∃ i0, ¬ p ∣ n i0 ∧ ∀ i, i ≠ i0 → p ∣ n i) ∨
      (∃ i0 i1, i0 ≠ i1 ∧ ¬ p ∣ n i0 ∧ ¬ p ∣ n i1) := by
  by_cases h2 : ∃ i0 i1, i0 ≠ i1 ∧ ¬ p ∣ n i0 ∧ ¬ p ∣ n i1
  · exact Or.inr (Or.inr h2)
  · push_neg at h2
    by_cases h1 : ∃ i0, ¬ p ∣ n i0
    · obtain ⟨i0, hi0⟩ := h1
      refine Or.inr (Or.inl ⟨i0, hi0, ?_⟩)
      intro i hi
      have := h2 i0 i (Ne.symm hi)
      tauto
    · push_neg at h1
      exact Or.inl h1

#print axioms Up_trichotomy

end CongruenceTheory
