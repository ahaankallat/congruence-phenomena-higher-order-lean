import Mathlib
import CongruenceTheoryHigherOrder.CZeroFree
import CongruenceTheoryHigherOrder.CompletePrimeLocalDefect

/-!
**`\Delta_{\mathbf n}` never has an `X_0` component.** `X_0`-freeness (`CZeroFree.lean`) is
closed under subtraction and finite products, and `\Delta_{\mathbf n}=C(\sum n_i)-\prod_iC(n_i)`
is built from exactly these operations on `C`'s. Needed to identify
`\text{nontrivialPartCount}` with `\text{wDeg nontrivialWeight}` on `\Delta_{\mathbf n}`'s own
support (`DeltaOrderAssembly.lean`'s final link to `Dgcd`/`IsLeast`).
-/

namespace CongruenceTheory

open MvPolynomial

theorem apply_zero_eq_zero_of_mul {A B : MvPolynomial ℕ ℤ}
    (hA : ∀ d ∈ A.support, d 0 = 0) (hB : ∀ d ∈ B.support, d 0 = 0) :
    ∀ d ∈ (A * B).support, d 0 = 0 := by
  intro d hd
  by_contra hd0
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hd
  apply hd
  apply Finset.sum_eq_zero
  rintro ⟨d1, d2⟩ hmem
  simp only [Finset.mem_antidiagonal] at hmem
  by_cases hd1 : MvPolynomial.coeff d1 A = 0
  · simp [hd1]
  by_cases hd2 : MvPolynomial.coeff d2 B = 0
  · simp [hd2]
  exfalso
  apply hd0
  have h1 : d1 ∈ A.support := MvPolynomial.mem_support_iff.mpr hd1
  have h2 : d2 ∈ B.support := MvPolynomial.mem_support_iff.mpr hd2
  have e1 := hA d1 h1
  have e2 := hB d2 h2
  rw [← hmem, Finsupp.add_apply, e1, e2]

theorem apply_zero_eq_zero_of_sub {A B : MvPolynomial ℕ ℤ}
    (hA : ∀ d ∈ A.support, d 0 = 0) (hB : ∀ d ∈ B.support, d 0 = 0) :
    ∀ d ∈ (A - B).support, d 0 = 0 := by
  intro d hd
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub] at hd
  by_contra hd0
  apply hd
  have h1 : MvPolynomial.coeff d A = 0 := by
    by_contra hne
    exact hd0 (hA d (MvPolynomial.mem_support_iff.mpr hne))
  have h2 : MvPolynomial.coeff d B = 0 := by
    by_contra hne
    exact hd0 (hB d (MvPolynomial.mem_support_iff.mpr hne))
  rw [h1, h2]
  ring

theorem apply_zero_eq_zero_of_finset_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial ℕ ℤ)
    (hf : ∀ i ∈ s, ∀ d ∈ (f i).support, d 0 = 0) :
    ∀ d ∈ (∏ i ∈ s, f i).support, d 0 = 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro d hd
    rw [Finset.prod_empty, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hd
    by_contra hd0
    apply hd
    rw [if_neg]
    intro heq
    apply hd0
    rw [← heq]
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    apply apply_zero_eq_zero_of_mul (hf a (Finset.mem_insert_self a s))
    apply ih
    intro i hi
    exact hf i (Finset.mem_insert_of_mem hi)

/-- **`\Delta_{\mathbf n}` never has an `X_0` component.** -/
theorem apply_zero_eq_zero_of_mem_support_Delta {r : ℕ} (n : Fin r → ℕ) :
    ∀ d ∈ (Delta n).support, d 0 = 0 := by
  unfold Delta
  apply apply_zero_eq_zero_of_sub
  · exact apply_zero_eq_zero_of_mem_support_C _
  · apply apply_zero_eq_zero_of_finset_prod
    intro i _
    exact apply_zero_eq_zero_of_mem_support_C _

#print axioms apply_zero_eq_zero_of_mul
#print axioms apply_zero_eq_zero_of_sub
#print axioms apply_zero_eq_zero_of_finset_prod
#print axioms apply_zero_eq_zero_of_mem_support_Delta

end CongruenceTheory
