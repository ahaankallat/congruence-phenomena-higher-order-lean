import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.FirstPrimeLayer
import CongruenceTheoryHigherOrder.NormalizedLayerIdentity
import CongruenceTheoryHigherOrder.DefectValuationExactWeight

/-!
**The exact "leading term + `p`-divisible remainder" decomposition of `\Delta_{p\mathbf u}`.**
Writing `A_\lambda(\mathbf u)=p^{v_p(A_\lambda)}\cdot a_\lambda` (`a_\lambda` a `p`-unit) and
`K_j(p)=p^{e_p(j)}\cdot\text{normalizedLayer}(p,j)` exactly, each shape-`\lambda` term of (A7)
factors *exactly* as `p^{W_p(\lambda)}\cdot a_\lambda\cdot\prod_j\text{normalizedLayer}(p,j)`.
Splitting the (A7) sum at the minimum weight `E` gives an exact polynomial identity
`\Delta_{p\mathbf u}=p^E\cdot(\text{LeadingSum}+p\cdot\text{Remainder})`, the form
`thm:common-prime-classification`'s sharpness argument needs before applying `specialize`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **A multiset-product version of `K_eq_pow_mul_normalizedLayer`.** -/
theorem prod_K_eq_pow_mul_prod_normalizedLayer {p : ℕ} (hp : p.Prime) (lam : Multiset ℕ)
    (hlam : ∀ j ∈ lam, 1 ≤ j) :
    (lam.map (fun j => K j p)).prod =
      MvPolynomial.C ((p : ℤ) ^ ((lam.map (firstPrimeLayerExponent p)).sum)) *
        (lam.map (fun j => normalizedLayer p j)).prod := by
  induction lam using Multiset.induction with
  | empty => simp
  | cons j s ih =>
    have hj1 : 1 ≤ j := hlam j (Multiset.mem_cons_self j s)
    haveI : NeZero j := ⟨by omega⟩
    have hs : ∀ j' ∈ s, 1 ≤ j' := fun j' hj' => hlam j' (Multiset.mem_cons_of_mem hj')
    rw [Multiset.map_cons (fun j => K j p), Multiset.prod_cons,
      Multiset.map_cons (firstPrimeLayerExponent p), Multiset.sum_cons,
      Multiset.map_cons (fun j => normalizedLayer p j), Multiset.prod_cons,
      ih hs, K_eq_pow_mul_normalizedLayer hp, pow_add]
    simp only [MvPolynomial.C_mul]
    ring

/-- **The `A_\lambda(\mathbf u)`-scalar times the shape-`\lambda` block-product factors exactly as
`p^{W_p(\lambda)}` times a `p`-unit times a product of normalized layers.** -/
theorem Alam_smul_prod_K_eq {r : ℕ} (u : Fin r → ℕ) {p : ℕ} (hp : p.Prime) (lam : Multiset ℕ)
    (hlam : ∀ j ∈ lam, 1 ≤ j) :
    (Alam u lam) • ((lam.map (fun j => K j p)).prod) =
      MvPolynomial.C ((p : ℤ) ^ (Wp u p lam)) *
        (MvPolynomial.C ((ordCompl[p] (Alam u lam) : ℕ) : ℤ) *
          (lam.map (fun j => normalizedLayer p j)).prod) := by
  rw [prod_K_eq_pow_mul_prod_normalizedLayer hp lam hlam, nsmul_eq_mul]
  have hcast : ((Alam u lam : ℕ) : MvPolynomial ℕ ℤ) =
      MvPolynomial.C ((Alam u lam : ℕ) : ℤ) := (map_natCast MvPolynomial.C (Alam u lam)).symm
  rw [hcast]
  have hsplit : ((Alam u lam : ℕ) : ℤ) =
      (p : ℤ) ^ ((Alam u lam).factorization p) * ((ordCompl[p] (Alam u lam) : ℕ) : ℤ) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  rw [hsplit]
  unfold Wp
  rw [pow_add]
  simp only [MvPolynomial.C_mul]
  ring

/-- **The exact leading-term/remainder decomposition of `\Delta_{p\mathbf u}`.** Writing `E` for a
lower bound on every achieved shape's `W_p`-weight, `\Delta_{p\mathbf u}` equals `p^E` times the
sum of `p`-unit-weighted normalized-layer products over the minimum-weight shapes, plus `p^{E+1}`
times a remainder. -/
theorem defect_eq_leading_add_remainder {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ)
    (hu : ∀ i, 0 < u i) {p : ℕ} (hp : p.Prime) (E : ℕ)
    (hE : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, E ≤ Wp u p lam) :
    C ((∑ i, u i) * p) - ∏ i, C (u i * p) =
      MvPolynomial.C ((p : ℤ) ^ E) *
        ((∑ lam ∈ ((nonRefiningPartitions u).image GenPartLatShape).filter
              (fun lam => Wp u p lam = E),
            MvPolynomial.C ((ordCompl[p] (Alam u lam) : ℕ) : ℤ) *
              (lam.map (fun j => normalizedLayer p j)).prod) +
          MvPolynomial.C (p : ℤ) *
            (∑ lam ∈ ((nonRefiningPartitions u).image GenPartLatShape).filter
                  (fun lam => E < Wp u p lam),
                MvPolynomial.C ((p : ℤ) ^ (Wp u p lam - E - 1) *
                  ((ordCompl[p] (Alam u lam) : ℕ) : ℤ)) *
                  (lam.map (fun j => normalizedLayer p j)).prod)) := by
  rw [defect_eq_sum_Alam_smul hr u hu p]
  have hshape1 : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, ∀ j ∈ lam, 1 ≤ j := by
    intro lam hlam j hj
    obtain ⟨π, -, hπ⟩ := Finset.mem_image.mp hlam
    rw [← hπ] at hj
    obtain ⟨B, hB, hBj⟩ := Multiset.mem_map.mp hj
    have hBmem : B ∈ π.parts := hB
    have := Finset.card_pos.mpr (π.nonempty_of_mem_parts hBmem)
    omega
  rw [mul_add]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((nonRefiningPartitions u).image GenPartLatShape) (fun lam => Wp u p lam = E)]
  have hsplit : ((nonRefiningPartitions u).image GenPartLatShape).filter
      (fun lam => ¬ Wp u p lam = E) =
      ((nonRefiningPartitions u).image GenPartLatShape).filter (fun lam => E < Wp u p lam) := by
    apply Finset.filter_congr
    intro lam hlam
    have := hE lam hlam
    omega
  rw [hsplit]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lam hlam
    rw [Finset.mem_filter] at hlam
    rw [Alam_smul_prod_K_eq u hp lam (hshape1 lam hlam.1), hlam.2]
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lam hlam
    rw [Finset.mem_filter] at hlam
    rw [Alam_smul_prod_K_eq u hp lam (hshape1 lam hlam.1)]
    have hlt : E < Wp u p lam := hlam.2
    have hpow : (p : ℤ) ^ (Wp u p lam) =
        (p : ℤ) ^ E * (p : ℤ) * (p : ℤ) ^ (Wp u p lam - E - 1) := by
      have hWE : Wp u p lam = E + 1 + (Wp u p lam - E - 1) := by omega
      conv_lhs => rw [hWE]
      rw [pow_add, pow_add, pow_one]
    rw [hpow]
    simp only [MvPolynomial.C_mul]
    ring

#print axioms prod_K_eq_pow_mul_prod_normalizedLayer
#print axioms Alam_smul_prod_K_eq
#print axioms defect_eq_leading_add_remainder

end CongruenceTheory
