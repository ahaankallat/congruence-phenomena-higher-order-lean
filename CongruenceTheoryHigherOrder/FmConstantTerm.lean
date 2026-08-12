import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheory.CoeffExtraction
import CongruenceTheory.PrimeWitness
import CongruenceTheoryHigherOrder.FmDef
import CongruenceTheoryHigherOrder.FmModP
import CongruenceTheoryHigherOrder.PolyOrder
import CongruenceTheoryHigherOrder.KOneAllFixedCoeff

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: `F_m`'s constant term is `1`.**
Needed so that `F_m - 1` (and `F_mZ - 1`) lies in `J` (ordinary degree `\ge1` throughout),
letting `LinPart.lean`'s machinery apply to `F_m` as a `1+J`-unit.
-/

namespace CongruenceTheory

open MvPolynomial

theorem coeff_zero_Fm (m : ℕ) : MvPolynomial.coeff 0 (Fm m) = 1 := by
  unfold Fm
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.coeff_sum]
  have hterm : ∀ d ∈ (C m).support,
      MvPolynomial.coeff (0 : ℕ →₀ ℕ)
        (algebraMap ℤ (MvPolynomial ℕ ℤ) (MvPolynomial.coeff d (C m)) *
          ∏ i ∈ d.support, (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ d i) =
        if d = Finsupp.single 1 m then MvPolynomial.coeff d (C m) else 0 := by
    intro d hdmem
    have halg : algebraMap ℤ (MvPolynomial ℕ ℤ) (MvPolynomial.coeff d (C m)) =
        MvPolynomial.C (MvPolynomial.coeff d (C m)) := rfl
    rw [halg, MvPolynomial.coeff_C_mul]
    have hprodeq : (∏ i ∈ d.support,
        (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ d i) =
        d.prod fun i e => (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ e := rfl
    rw [hprodeq, prod_subst_eq_monomial_erase, MvPolynomial.coeff_monomial]
    by_cases hd : d = Finsupp.single 1 m
    · rw [hd]
      have herase0 : (Finsupp.single 1 m : ℕ →₀ ℕ).erase 1 = 0 := by
        ext j
        rw [Finsupp.erase_apply]
        rcases eq_or_ne j 1 with hj | hj
        · rw [if_pos hj]; simp
        · rw [if_neg hj]; simp [Finsupp.single_apply, Ne.symm hj]
      rw [herase0]
      simp
    · rw [if_neg hd]
      by_cases herase : d.erase 1 = (0 : ℕ →₀ ℕ)
      · exfalso
        apply hd
        have hw : Finsupp.weight (fun k : ℕ => k) d = m :=
          CongruenceTheory.isWeightedHomogeneous_C m (MvPolynomial.mem_support_iff.mp hdmem)
        have hrecon : d = d.erase 1 + Finsupp.single 1 (d 1) := by
          ext i
          rw [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply]
          rcases eq_or_ne i 1 with rfl | hi
          · simp
          · simp [hi, Ne.symm hi]
        rw [herase, zero_add] at hrecon
        have hweq : Finsupp.weight (fun k : ℕ => k) d =
            Finsupp.weight (fun k : ℕ => k) (Finsupp.single 1 (d 1)) := by
          conv_lhs => rw [hrecon]
        rw [Finsupp.weight_single, smul_eq_mul, mul_one] at hweq
        rw [hw] at hweq
        rw [hrecon, hweq]
      · rw [if_neg herase, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite_eq' (C m).support (Finsupp.single 1 m) (MvPolynomial.coeff · (C m))]
  split_ifs with hmem
  · rw [← K_one]
    exact coeff_single_one_K_one m
  · exfalso
    apply hmem
    rw [MvPolynomial.mem_support_iff, ← K_one, coeff_single_one_K_one m]
    norm_num

theorem Fm_sub_one_deg_ge_one (m : ℕ) :
    ∀ d ∈ (Fm m - 1).support, 1 ≤ monoDeg d := by
  intro d hd
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub] at hd
  by_contra hcon
  push_neg at hcon
  have hdeg0 : monoDeg d = 0 := by omega
  have hd0 : d = 0 := by
    rw [monoDeg_eq_sum, Finsupp.sum] at hdeg0
    by_contra hne
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
    have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hle : d i ≤ ∑ a ∈ d.support, d a :=
      Finset.single_le_sum (fun a _ => Nat.zero_le (d a)) hi
    omega
  apply hd
  rw [hd0, coeff_zero_Fm, MvPolynomial.coeff_one]
  simp

#print axioms coeff_zero_Fm
#print axioms Fm_sub_one_deg_ge_one

end CongruenceTheory
