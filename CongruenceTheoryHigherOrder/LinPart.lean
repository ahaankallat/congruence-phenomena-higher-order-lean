import Mathlib
import CongruenceTheoryHigherOrder.PolyOrder

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: the degree-one "linearization" of a product.**
For `a,b` with ordinary degree `\ge1` throughout (`a,b\in J`), `(1+a)(1+b) = 1+a+b+ab` and `ab`
has degree `\ge2`, so **the degree-one part of a product of `1+J`-units is the sum of the
degree-one parts of the factors** — the elementary, log-free fact behind the manuscript's
degree-one coefficient matching for `D_{\mathbf c}`. This is a much more direct route to the
"order = 1 when the digit conditions fail" direction than building the full truncated-log
isomorphism.
-/

namespace CongruenceTheory

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- If every support-monomial of `a` and of `b` has ordinary degree `\ge m`, so does every
support-monomial of `a+b`. -/
theorem deg_ge_add {a b : MvPolynomial ℕ R} {m : ℕ} (ha : ∀ d ∈ a.support, m ≤ monoDeg d)
    (hb : ∀ d ∈ b.support, m ≤ monoDeg d) : ∀ d ∈ (a + b).support, m ≤ monoDeg d := by
  intro d hd
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at hd
  by_cases hda : MvPolynomial.coeff d a = 0
  · have hdb : MvPolynomial.coeff d b ≠ 0 := by intro h; rw [hda, h] at hd; simp at hd
    exact hb d (MvPolynomial.mem_support_iff.mpr hdb)
  · exact ha d (MvPolynomial.mem_support_iff.mpr hda)

/-- If every support-monomial of `a` and of `b` has ordinary degree `\ge1`, so does every
support-monomial of `a*b` (in fact `\ge2`, but `\ge1` is all that is needed here). -/
theorem deg_ge_one_mul {a b : MvPolynomial ℕ R} (ha : ∀ d ∈ a.support, 1 ≤ monoDeg d)
    (hb : ∀ d ∈ b.support, 1 ≤ monoDeg d) : ∀ d ∈ (a * b).support, 1 ≤ monoDeg d := by
  intro d hd
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hd
  by_contra hcon
  push_neg at hcon
  interval_cases hdz : monoDeg d
  apply hd
  apply Finset.sum_eq_zero
  rintro ⟨d1, d2⟩ hmem2
  simp only [Finset.mem_antidiagonal] at hmem2
  by_cases hd1 : MvPolynomial.coeff d1 a = 0
  · simp [hd1]
  by_cases hd2 : MvPolynomial.coeff d2 b = 0
  · simp [hd2]
  exfalso
  have hge1 : 1 ≤ monoDeg d1 := ha d1 (MvPolynomial.mem_support_iff.mpr hd1)
  have hge2 : 1 ≤ monoDeg d2 := hb d2 (MvPolynomial.mem_support_iff.mpr hd2)
  have hdeq : monoDeg d = monoDeg d1 + monoDeg d2 := by rw [← hmem2, monoDeg_add]
  omega

/-- `a,b\in J` (ordinary degree `\ge1` throughout) `\implies ab\in J^2` (degree `\ge2`
throughout), hence `ab` contributes nothing to any degree-one coefficient. -/
theorem coeff_single_mul_eq_zero_of_deg_ge_one {a b : MvPolynomial ℕ R}
    (ha : ∀ d ∈ a.support, 1 ≤ monoDeg d) (hb : ∀ d ∈ b.support, 1 ≤ monoDeg d)
    {t : ℕ} : MvPolynomial.coeff (Finsupp.single t 1) (a * b) = 0 := by
  by_contra hne
  have hmem : (Finsupp.single t 1 : ℕ →₀ ℕ) ∈ (a * b).support :=
    MvPolynomial.mem_support_iff.mpr hne
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hmem
  apply hmem
  apply Finset.sum_eq_zero
  rintro ⟨d1, d2⟩ hmem2
  simp only [Finset.mem_antidiagonal] at hmem2
  by_cases hd1 : MvPolynomial.coeff d1 a = 0
  · simp [hd1]
  by_cases hd2 : MvPolynomial.coeff d2 b = 0
  · simp [hd2]
  exfalso
  have hge1 : 1 ≤ monoDeg d1 := ha d1 (MvPolynomial.mem_support_iff.mpr hd1)
  have hge2 : 1 ≤ monoDeg d2 := hb d2 (MvPolynomial.mem_support_iff.mpr hd2)
  have hdeq : monoDeg (Finsupp.single t 1 : ℕ →₀ ℕ) = monoDeg d1 + monoDeg d2 := by
    rw [← hmem2, monoDeg_add]
  have hsingle : monoDeg (Finsupp.single t 1 : ℕ →₀ ℕ) = 1 := by
    rw [monoDeg_eq_sum]; simp
  omega

/-- **The degree-one part of a product is the sum of the degree-one parts**, for `1+J`-units. -/
theorem coeff_single_mul_add_one (a b : MvPolynomial ℕ R)
    (ha : ∀ d ∈ a.support, 1 ≤ monoDeg d) (hb : ∀ d ∈ b.support, 1 ≤ monoDeg d) {t : ℕ} :
    MvPolynomial.coeff (Finsupp.single t 1) ((1 + a) * (1 + b)) =
      MvPolynomial.coeff (Finsupp.single t 1) a + MvPolynomial.coeff (Finsupp.single t 1) b := by
  have hexpand : (1 + a) * (1 + b) = 1 + a + b + a * b := by ring
  rw [hexpand]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
  rw [coeff_single_mul_eq_zero_of_deg_ge_one ha hb]
  have hsingle_ne : (Finsupp.single t 1 : ℕ →₀ ℕ) ≠ 0 := by
    intro h
    have := DFunLike.congr_fun h t
    simp at this
  rw [MvPolynomial.coeff_one, if_neg (Ne.symm hsingle_ne)]
  ring

/-- `\prod_{i\in s}(1+f_i) - 1` lies in `J` (ordinary degree `\ge1` throughout), given each
`f_i\in J`. -/
theorem prod_one_add_sub_one_deg_ge_one {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial ℕ R)
    (hf : ∀ i ∈ s, ∀ d ∈ (f i).support, 1 ≤ monoDeg d) :
    ∀ d ∈ (∏ i ∈ s, (1 + f i) - 1).support, 1 ≤ monoDeg d := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    have hfi : ∀ d ∈ (f i).support, 1 ≤ monoDeg d := hf i (Finset.mem_insert_self i s)
    have hih : ∀ d ∈ (∏ j ∈ s, (1 + f j) - 1).support, 1 ≤ monoDeg d :=
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hrw : ∏ j ∈ insert i s, (1 + f j) - 1 =
        f i + (∏ j ∈ s, (1 + f j) - 1) + f i * (∏ j ∈ s, (1 + f j) - 1) := by
      rw [Finset.prod_insert hi]; ring
    rw [hrw]
    exact deg_ge_add (deg_ge_add hfi hih) (deg_ge_one_mul hfi hih)

/-- **Degree-one linearization of a finite product of `1+J`-units.** -/
theorem coeff_single_finset_prod_add_one {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial ℕ R)
    (hf : ∀ i ∈ s, ∀ d ∈ (f i).support, 1 ≤ monoDeg d) {t : ℕ} :
    MvPolynomial.coeff (Finsupp.single t 1) (∏ i ∈ s, (1 + f i)) =
      ∑ i ∈ s, MvPolynomial.coeff (Finsupp.single t 1) (f i) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    have hsingle_ne : (Finsupp.single t 1 : ℕ →₀ ℕ) ≠ 0 := by
      intro h
      have := DFunLike.congr_fun h t
      simp at this
    rw [MvPolynomial.coeff_one, if_neg (Ne.symm hsingle_ne)]
  | insert i s hi ih =>
    have hfi : ∀ d ∈ (f i).support, 1 ≤ monoDeg d := hf i (Finset.mem_insert_self i s)
    have hprodm1 : ∀ d ∈ (∏ j ∈ s, (1 + f j) - 1).support, 1 ≤ monoDeg d :=
      prod_one_add_sub_one_deg_ge_one s f (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hrw1 : ∏ j ∈ insert i s, (1 + f j) = (1 + f i) * (1 + (∏ j ∈ s, (1 + f j) - 1)) := by
      rw [Finset.prod_insert hi]; ring
    rw [hrw1, coeff_single_mul_add_one (f i) _ hfi hprodm1, Finset.sum_insert hi]
    congr 1
    have hsingle_ne : (Finsupp.single t 1 : ℕ →₀ ℕ) ≠ 0 := by
      intro h
      have := DFunLike.congr_fun h t
      simp at this
    have hsub : MvPolynomial.coeff (Finsupp.single t 1) (∏ j ∈ s, (1 + f j) - 1) =
        MvPolynomial.coeff (Finsupp.single t 1) (∏ j ∈ s, (1 + f j)) := by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, if_neg (Ne.symm hsingle_ne)]
      ring
    rw [hsub, ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

#print axioms deg_ge_add
#print axioms deg_ge_one_mul
#print axioms coeff_single_mul_eq_zero_of_deg_ge_one
#print axioms coeff_single_mul_add_one
#print axioms prod_one_add_sub_one_deg_ge_one
#print axioms coeff_single_finset_prod_add_one

end CongruenceTheory
