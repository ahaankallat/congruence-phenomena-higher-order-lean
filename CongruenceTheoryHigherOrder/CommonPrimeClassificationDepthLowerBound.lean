import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.DefectValuationExactWeight
import CongruenceTheoryHigherOrder.CycleDepthHierarchy
import CongruenceTheoryHigherOrder.NontrivialPartCountProduct

/-!
**The "no early witness" half of the witness-depth (`\delta_p`) argument.** If every shape
`\lambda` achieved by a non-refining partition with `k(\lambda)\le s` has `W_p(\lambda)\ge E+1`,
then `p^{E+1}` divides every coefficient of `\Delta_{p\mathbf u}$ indexed by a monomial with at
most `s` nontrivial parts — hence `p^{E+1}\mid D_s(\Delta_{p\mathbf u})`. Combined with
`exists_coeff_not_dvd_pow_succ`'s witness at `s=k_{\min}`, this pins down
`\delta_p(p\mathbf u)=k_{\min}` via `def:prime-cycle-depth`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **No coefficient of `\Delta_{p\mathbf u}` indexed by a monomial with at most `s` nontrivial
parts fails to be divisible by `p^{E+1}`**, provided every achieved shape with `k(\lambda)\le s`
already has `W_p(\lambda)\ge E+1`. -/
theorem dvd_coeff_defect_of_nontrivialPartCount_le {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ)
    (hu : ∀ i, 0 < u i) {p : ℕ} (hp : p.Prime) (E s : ℕ)
    (hs : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape,
        (lam.filter (2 ≤ ·)).card ≤ s → E + 1 ≤ Wp u p lam)
    {d : ℕ →₀ ℕ} (hd : nontrivialPartCount d ≤ s) :
    (p : ℤ) ^ (E + 1) ∣ coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) := by
  rw [defect_eq_sum_Alam_smul hr u hu p, coeff_sum]
  apply Finset.dvd_sum
  intro lam hlam
  have hshape1 : ∀ j ∈ lam, 1 ≤ j := by
    intro j hj
    obtain ⟨π, -, hπ⟩ := Finset.mem_image.mp hlam
    rw [← hπ] at hj
    obtain ⟨B, hB, hBj⟩ := Multiset.mem_map.mp hj
    have hBmem : B ∈ π.parts := hB
    have := Finset.card_pos.mpr (π.nonempty_of_mem_parts hBmem)
    omega
  by_cases hk : (lam.filter (2 ≤ ·)).card ≤ s
  · have hWp := hs lam hlam hk
    have hn2 : ∀ j ∈ lam, 2 ≤ j * p := by
      intro j hj
      have h1 := hshape1 j hj
      have h2 : 2 ≤ p := hp.two_le
      nlinarith
    exact dvd_trans (pow_dvd_pow (p : ℤ) hWp) (dvd_coeff_Alam_smul u hp lam hshape1 hn2 d)
  · push_neg at hk
    rw [coeff_smul, nsmul_eq_mul]
    have hzero : coeff d ((lam.map (fun j => K j p)).prod) = 0 := by
      by_contra hne
      have := nontrivialPartCount_ge_of_coeff_prod_K_ne_zero lam hshape1 d hne
      omega
    rw [hzero, mul_zero]
    exact dvd_zero _

/-- **`p^{E+1}\mid D_s(\Delta_{p\mathbf u})`**, provided every achieved shape with `k(\lambda)
\le s` already has `W_p(\lambda)\ge E+1`. -/
theorem dvd_Dgcd_of_kmin_gt {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ) (hu : ∀ i, 0 < u i) {p : ℕ}
    (hp : p.Prime) (E s : ℕ)
    (hs : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape,
        (lam.filter (2 ≤ ·)).card ≤ s → E + 1 ≤ Wp u p lam) :
    p ^ (E + 1) ∣ Dgcd (C ((∑ i, u i) * p) - ∏ i, C (u i * p)) s := by
  unfold Dgcd
  apply Finset.dvd_gcd
  intro d hd
  rw [Finset.mem_filter] at hd
  have hbound := dvd_coeff_defect_of_nontrivialPartCount_le hr u hu hp E s hs hd.2
  have h1 := Int.natAbs_dvd_natAbs.mpr hbound
  rwa [Int.natAbs_pow, Int.natAbs_natCast] at h1

#print axioms dvd_coeff_defect_of_nontrivialPartCount_le
#print axioms dvd_Dgcd_of_kmin_gt

end CongruenceTheory
