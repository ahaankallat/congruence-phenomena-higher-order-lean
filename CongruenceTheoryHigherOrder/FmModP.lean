import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheory.CoeffExtraction
import CongruenceTheory.PrimeWitness
import CongruenceTheoryHigherOrder.FmDef
import CongruenceTheoryHigherOrder.PolyOrder
import CongruenceTheoryHigherOrder.DefectWeightedHomogeneous

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`: `F_m` reduced mod `p`, and its linear coefficient.**
Reduces `Fm` to `\mathbb F_p[X_2,X_3,\ldots]` and shows the coefficient of `X_m` (the
"linear-in-`y_m`" term, matching `\log F_m`'s degree-one part in the manuscript) is `(m-1)!`,
nonzero whenever `m<p` (since `(m-1)!` is then a product of nonzero residues mod `p`).
-/

namespace CongruenceTheory

open MvPolynomial

/-- `F_m` reduced mod `p`. -/
noncomputable def FmZ (p m : ℕ) : MvPolynomial ℕ (ZMod p) :=
  MvPolynomial.map (Int.castRingHom (ZMod p)) (Fm m)

/-- The substitution product for a monomial `d`, with `X_1` set to `1`, is the monomial
`d.erase 1` (zeroing out the `X_1`-exponent). -/
theorem prod_subst_eq_monomial_erase (d : ℕ →₀ ℕ) :
    (d.prod fun i e => (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ e) =
      MvPolynomial.monomial (d.erase 1) (1 : ℤ) := by
  rw [MvPolynomial.monomial_eq]
  simp only [MvPolynomial.C_1, one_mul]
  unfold Finsupp.prod
  rw [Finsupp.support_erase]
  by_cases h1 : 1 ∈ d.support
  · rw [← Finset.prod_erase_mul _ _ h1]
    simp only [reduceIte, one_pow, mul_one]
    apply Finset.prod_congr rfl
    intro i hi
    have hine1 : i ≠ 1 := (Finset.mem_erase.mp hi).1
    simp [hine1, Finsupp.erase_ne hine1]
  · have herase_eq : d.support.erase 1 = d.support := Finset.erase_eq_self.mpr h1
    rw [herase_eq]
    apply Finset.prod_congr rfl
    intro i hi
    have hine1 : i ≠ 1 := fun heq => h1 (heq ▸ hi)
    simp [hine1, Finsupp.erase_ne hine1]

theorem coeff_single_Fm (m : ℕ) (hm : 2 ≤ m) :
    MvPolynomial.coeff (Finsupp.single m 1) (Fm m) = (Nat.factorial (m - 1) : ℤ) := by
  rw [← coeff_single_C m hm]
  unfold Fm
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  rw [MvPolynomial.coeff_sum]
  have hterm : ∀ d ∈ (C m).support,
      MvPolynomial.coeff (Finsupp.single m 1)
        (algebraMap ℤ (MvPolynomial ℕ ℤ) (MvPolynomial.coeff d (C m)) *
          ∏ i ∈ d.support, (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ d i) =
        if d = Finsupp.single m 1 then MvPolynomial.coeff d (C m) else 0 := by
    intro d hdmem
    have halg : algebraMap ℤ (MvPolynomial ℕ ℤ) (MvPolynomial.coeff d (C m)) =
        MvPolynomial.C (MvPolynomial.coeff d (C m)) := rfl
    rw [halg, MvPolynomial.coeff_C_mul]
    have hprodeq : (∏ i ∈ d.support,
        (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ d i) =
        d.prod fun i e => (if i = 1 then (1 : MvPolynomial ℕ ℤ) else MvPolynomial.X i) ^ e := rfl
    rw [hprodeq, prod_subst_eq_monomial_erase, MvPolynomial.coeff_monomial]
    by_cases hd : d = Finsupp.single m 1
    · rw [hd]
      have : (Finsupp.single m 1 : ℕ →₀ ℕ).erase 1 = Finsupp.single m 1 := by
        ext j
        rw [Finsupp.erase_apply]
        rcases eq_or_ne j 1 with hj | hj
        · rw [if_pos hj, hj, Finsupp.single_apply, if_neg (by omega)]
        · rw [if_neg hj]
      rw [this, if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg hd]
      by_cases herase : d.erase 1 = Finsupp.single m 1
      · exfalso
        apply hd
        have hw : Finsupp.weight (fun k : ℕ => k) d = m :=
          CongruenceTheory.isWeightedHomogeneous_C m (MvPolynomial.mem_support_iff.mp hdmem)
        have hrecon : d = d.erase 1 + Finsupp.single 1 (d 1) := by
          ext j
          rw [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply]
          rcases eq_or_ne j 1 with rfl | hj
          · simp
          · simp [hj, Ne.symm hj]
        have hweq : Finsupp.weight (fun k : ℕ => k) d =
            Finsupp.weight (fun k : ℕ => k) (d.erase 1) +
              Finsupp.weight (fun k : ℕ => k) (Finsupp.single 1 (d 1)) := by
          conv_lhs => rw [hrecon]
          exact map_add _ _ _
        rw [herase, Finsupp.weight_single, Finsupp.weight_single, smul_eq_mul, smul_eq_mul,
          one_mul, mul_one] at hweq
        rw [hw] at hweq
        have hd1 : d 1 = 0 := by omega
        rw [hrecon, herase, hd1]
        simp
      · rw [if_neg herase, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite_eq' (C m).support (Finsupp.single m 1) (MvPolynomial.coeff · (C m))]
  split_ifs with hmem
  · rfl
  · rw [MvPolynomial.mem_support_iff, not_not] at hmem
    rw [hmem]

theorem coeff_single_FmZ (p m : ℕ) (hm : 2 ≤ m) :
    MvPolynomial.coeff (Finsupp.single m 1) (FmZ p m) =
      ((Nat.factorial (m - 1) : ℕ) : ZMod p) := by
  unfold FmZ
  rw [MvPolynomial.coeff_map, coeff_single_Fm m hm, map_natCast]

/-- `(m-1)!` is nonzero mod `p` whenever `m \le p` and `p` is prime (its factors are all
`<p`, hence coprime to `p`). -/
theorem factorial_ne_zero_mod_p {p m : ℕ} (hp : p.Prime) (hm : m ≤ p) :
    ((Nat.factorial (m - 1) : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hle : p ≤ m - 1 := (Nat.Prime.dvd_factorial (n := m - 1) hp).mp hdvd
  have hp2 := hp.two_le
  omega

#print axioms prod_subst_eq_monomial_erase
#print axioms coeff_single_Fm
#print axioms coeff_single_FmZ
#print axioms factorial_ne_zero_mod_p

end CongruenceTheory
