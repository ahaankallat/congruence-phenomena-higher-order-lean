import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.DefectValuationExactWeight
import CongruenceTheoryHigherOrder.DefectSharpness
import CongruenceTheoryHigherOrder.NontrivialPartCountProduct
import CongruenceTheoryHigherOrder.CanonicalMonomialCoefficientExact
import CongruenceTheoryHigherOrder.CanonTargetInjective
import CongruenceTheoryHigherOrder.CycleDepthHierarchy
import CongruenceTheoryHigherOrder.FirstPrimeLayer

/-!
**The sharpness half of `thm:common-prime-classification`'s witness-depth (`\delta_p`) formula.**
An elementary (independence-free) argument: among the shapes achieving the minimum weight `E` and
the minimum nontrivial-part count `k_{\min}` among those, choosing the one `\lambda_0` minimizing
its own singleton-part count `m_1` rules out contamination from every other such shape at
`\lambda_0`'s own canonical monomial (`coeff_canonSum_prod_K_strong`'s forced-minimality, plus
`canonTarget_sum_injOn`'s injectivity, pin the contributor down to `\lambda_0` alone). Combined
with `coeff_canonSum_prod_K_eq`'s exact coefficient value and `firstPrimeLayer_sharp`'s exact
`p`-adic valuation of `(jp-1)!`, this produces a coefficient of `\Delta_{p\mathbf u}`, indexed by a
monomial with exactly `k_{\min}` nontrivial parts, whose valuation is exactly `E` -- giving
`p^{E+1}\nmid D_{k_{\min}}(\Delta_{p\mathbf u})`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- The `p`-coprime cofactor of `canonCoeff p j`: `1` for `j=1`, `\text{ordCompl}_p((jp-1)!)` for
`j\ge2`. -/
noncomputable def canonCoeffOrdCompl (p j : ℕ) : ℕ :=
  if j = 1 then 1 else ordCompl[p] (Nat.factorial (j * p - 1))

/-- **`canonCoeff`'s exact `p`-power decomposition.** -/
theorem canonCoeff_eq_pow_mul_ordCompl {p j : ℕ} (hp : p.Prime) (hj1 : 1 ≤ j) :
    canonCoeff p j = (p : ℤ) ^ (firstPrimeLayerExponent p j) * (canonCoeffOrdCompl p j : ℤ) := by
  unfold canonCoeff canonCoeffOrdCompl
  by_cases hj : j = 1
  · subst hj
    simp [firstPrimeLayerExponent, Nat.factorization_one]
  · rw [if_neg hj, if_neg hj]
    have hj2 : 2 ≤ j := by omega
    have hp2 := hp.two_le
    have hjp2 : 2 ≤ j * p := by nlinarith
    have hfact := (firstPrimeLayer_sharp hp hj1 hjp2).1
    have hnat : Nat.factorial (j * p - 1) =
        p ^ (firstPrimeLayerExponent p j) * ordCompl[p] (Nat.factorial (j * p - 1)) := by
      rw [← hfact]
      exact (Nat.ordProj_mul_ordCompl_eq_self _ p).symm
    exact_mod_cast hnat

/-- **`canonCoeffOrdCompl` is coprime to `p`.** -/
theorem not_dvd_canonCoeffOrdCompl {p j : ℕ} (hp : p.Prime) (hj1 : 1 ≤ j) :
    ¬ p ∣ canonCoeffOrdCompl p j := by
  unfold canonCoeffOrdCompl
  by_cases hj : j = 1
  · simp [hj, hp.ne_one]
  · rw [if_neg hj]
    exact Nat.not_dvd_ordCompl hp (Nat.factorial_ne_zero _)

/-- **A multiset product of `p`-coprime naturals is `p`-coprime.** -/
theorem not_dvd_multiset_prod_of_forall {p : ℕ} (hp : p.Prime) :
    ∀ m : Multiset ℕ, (∀ x ∈ m, ¬ p ∣ x) → ¬ p ∣ m.prod := by
  intro m
  induction m using Multiset.induction with
  | empty =>
    intro _
    rw [Multiset.prod_zero]
    intro hdvd
    have h1 := Nat.le_of_dvd one_pos hdvd
    have h2 := hp.one_lt
    omega
  | cons x s ih =>
    intro h
    rw [Multiset.prod_cons, hp.dvd_mul]
    push_neg
    exact ⟨h x (Multiset.mem_cons_self x s), ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))⟩

/-- **The shape-product decomposition**: a shape's canonical coefficient product decomposes as
`p^{\sum e_p(j)}` times a `p`-coprime cofactor. -/
theorem canonCoeff_prod_eq_pow_mul_ordCompl {p : ℕ} (hp : p.Prime) :
    ∀ lam : Multiset ℕ, (∀ j ∈ lam, 1 ≤ j) →
      (lam.map (canonCoeff p)).prod =
        (p : ℤ) ^ ((lam.map (firstPrimeLayerExponent p)).sum) *
          ((lam.map (canonCoeffOrdCompl p)).prod : ℤ) := by
  intro lam
  induction lam using Multiset.induction with
  | empty => simp
  | cons j s ih =>
    intro hlam
    have hj1 : 1 ≤ j := hlam j (Multiset.mem_cons_self j s)
    have hs1 : ∀ j' ∈ s, 1 ≤ j' := fun j' hj' => hlam j' (Multiset.mem_cons_of_mem hj')
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [ih hs1, canonCoeff_eq_pow_mul_ordCompl hp hj1]
    push_cast
    ring

/-- **The exact `p^E`-decomposition of `\lambda_0`'s own contribution**: `A_{\lambda_0}\cdot
\prod_{j\in\lambda_0}\text{canonCoeff}(p,j)=p^{W_p(\lambda_0)}\cdot V` for a `p`-coprime natural
`V`. -/
theorem alam_canonCoeff_prod_eq_pow_mul_ordCompl {r : ℕ} (u : Fin r → ℕ) {p : ℕ} (hp : p.Prime)
    {lam : Multiset ℕ} (hlam : ∀ j ∈ lam, 1 ≤ j) (hpos : 0 < Alam u lam) :
    ∃ V : ℕ, ¬ p ∣ V ∧
      ((Alam u lam : ℤ) * (lam.map (canonCoeff p)).prod) =
        (p : ℤ) ^ (Wp u p lam) * (V : ℤ) := by
  refine ⟨(ordCompl[p] (Alam u lam)) * (lam.map (canonCoeffOrdCompl p)).prod, ?_, ?_⟩
  · rw [hp.dvd_mul]
    push_neg
    refine ⟨Nat.not_dvd_ordCompl hp hpos.ne', ?_⟩
    exact not_dvd_multiset_prod_of_forall hp _
        (fun x hx => by
          obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hx
          exact not_dvd_canonCoeffOrdCompl hp (hlam j hj))
  · rw [canonCoeff_prod_eq_pow_mul_ordCompl hp lam hlam]
    unfold Wp
    rw [pow_add]
    have hAlamNat : Alam u lam =
        p ^ ((Alam u lam).factorization p) * ordCompl[p] (Alam u lam) :=
      (Nat.ordProj_mul_ordCompl_eq_self (Alam u lam) p).symm
    generalize hW : ordCompl[p] (Alam u lam) = W at hAlamNat ⊢
    generalize hF : (Alam u lam).factorization p = F at hAlamNat ⊢
    rw [hAlamNat]
    push_cast
    ring

/-- A non-refining shape's parts are all `\ge1`. -/
theorem nonRefiningShape_ge_one {r : ℕ} (u : Fin r → ℕ) {lam : Multiset ℕ}
    (hlam : lam ∈ (nonRefiningPartitions u).image GenPartLatShape) : ∀ j ∈ lam, 1 ≤ j := by
  intro j hj
  obtain ⟨π, -, hπ⟩ := Finset.mem_image.mp hlam
  rw [← hπ] at hj
  obtain ⟨B, hB, hBj⟩ := Multiset.mem_map.mp hj
  have hBmem : B ∈ π.parts := hB
  have := Finset.card_pos.mpr (π.nonempty_of_mem_parts hBmem)
  omega

/-- **No contamination**: any other achieved shape of weight `E` (distinct from `\lambda_0`)
contributes zero to `\lambda_0`'s own canonical monomial, provided `\lambda_0` minimizes both
`k(\lambda)` and (among those) `m_1(\lambda)` among the weight-`E` achievers. -/
theorem coeff_canonSum_lam0_eq_zero_of_ne {r : ℕ} (u : Fin r → ℕ) {p : ℕ} (hp : p.Prime)
    {E kmin : ℕ} (lam0 : Multiset ℕ)
    (hlam0mem : lam0 ∈ (nonRefiningPartitions u).image GenPartLatShape)
    (hlam0k : (lam0.filter (2 ≤ ·)).card = kmin)
    (hlam0m1 : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, Wp u p lam = E →
        (lam.filter (2 ≤ ·)).card = kmin → Multiset.count 1 lam0 ≤ Multiset.count 1 lam)
    (hkmin_le : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, Wp u p lam = E →
        kmin ≤ (lam.filter (2 ≤ ·)).card)
    {lam : Multiset ℕ} (hlammem : lam ∈ (nonRefiningPartitions u).image GenPartLatShape)
    (hlamE : Wp u p lam = E) (hne : lam ≠ lam0) :
    coeff ((lam0.map (canonTarget p)).sum) ((lam.map (fun j => K j p)).prod) = 0 := by
  by_contra hcoeff
  apply hne
  have hlam0s1 := nonRefiningShape_ge_one u hlam0mem
  have hlams1 := nonRefiningShape_ge_one u hlammem
  have hy0np : nontrivialPartCount ((lam0.map (canonTarget p)).sum) = kmin := by
    rw [nontrivialPartCount_canonSum_eq_card hp.two_le lam0 hlam0s1, hlam0k]
  have hbound :=
    nontrivialPartCount_ge_of_coeff_prod_K_ne_zero lam hlams1 _ hcoeff
  have hklam_le : (lam.filter (2 ≤ ·)).card ≤ kmin := by rw [← hy0np]; exact hbound
  have hklam_ge : kmin ≤ (lam.filter (2 ≤ ·)).card := hkmin_le lam hlammem hlamE
  have hklam_eq : (lam.filter (2 ≤ ·)).card = kmin := le_antisymm hklam_le hklam_ge
  obtain ⟨-, hpos1_s, huniq_s⟩ :=
    coeff_canonSum_prod_K_strong hp.two_le lam hlams1 _ hcoeff
  have hnpeqk : nontrivialPartCount ((lam0.map (canonTarget p)).sum) =
      (lam.filter (2 ≤ ·)).card := by rw [hy0np, hklam_eq]
  have hpos1 := hpos1_s hnpeqk
  have hcanonlam1 : (lam.map (canonTarget p)).sum 1 = p * Multiset.count 1 lam :=
    canonSum_apply_one_eq_mul_count hp.two_le lam
  have hcanonlam01 : (lam0.map (canonTarget p)).sum 1 = p * Multiset.count 1 lam0 :=
    canonSum_apply_one_eq_mul_count hp.two_le lam0
  rw [hcanonlam1, hcanonlam01] at hpos1
  have hcount_le : Multiset.count 1 lam ≤ Multiset.count 1 lam0 := by
    by_contra hcon
    push_neg at hcon
    have : p * Multiset.count 1 lam0 < p * Multiset.count 1 lam :=
      (Nat.mul_lt_mul_left hp.pos).mpr hcon
    omega
  have hcount_ge : Multiset.count 1 lam0 ≤ Multiset.count 1 lam :=
    hlam0m1 lam hlammem hlamE hklam_eq
  have hcounteq : Multiset.count 1 lam = Multiset.count 1 lam0 := le_antisymm hcount_le hcount_ge
  have hy0eq : (lam0.map (canonTarget p)).sum 1 = (lam.map (canonTarget p)).sum 1 := by
    rw [hcanonlam01, hcanonlam1, hcounteq]
  have heq := huniq_s ⟨hnpeqk, hy0eq⟩
  exact (canonTarget_sum_injOn hp.two_le hlam0s1 hlams1 heq).symm

/-- **The depth-sharpness witness**: given `E`, `kmin`, and a shape `\lambda_0` minimizing `k`
then `m_1` among the weight-`E` achievers, `\lambda_0`'s own canonical monomial has exactly
`kmin` nontrivial parts and its `\Delta_{p\mathbf u}`-coefficient is not divisible by `p^{E+1}`. -/
theorem exists_coeff_nontrivialPartCount_eq_not_dvd_pow_succ {r : ℕ} (hr : 0 < r) (u : Fin r → ℕ)
    (hu : ∀ i, 0 < u i) {p : ℕ} [Fact (Nat.Prime p)] (E kmin : ℕ)
    (hE : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, E ≤ Wp u p lam)
    (hkmin_le : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, Wp u p lam = E →
        kmin ≤ (lam.filter (2 ≤ ·)).card)
    (lam0 : Multiset ℕ) (hlam0mem : lam0 ∈ (nonRefiningPartitions u).image GenPartLatShape)
    (hlam0E : Wp u p lam0 = E) (hlam0k : (lam0.filter (2 ≤ ·)).card = kmin)
    (hlam0m1 : ∀ lam ∈ (nonRefiningPartitions u).image GenPartLatShape, Wp u p lam = E →
        (lam.filter (2 ≤ ·)).card = kmin → Multiset.count 1 lam0 ≤ Multiset.count 1 lam) :
    ∃ d, nontrivialPartCount d = kmin ∧
      ¬ ((p : ℤ) ^ (E + 1) ∣ coeff d (C ((∑ i, u i) * p) - ∏ i, C (u i * p))) := by
  have hp : p.Prime := Fact.out
  have hlam0s1 := nonRefiningShape_ge_one u hlam0mem
  refine ⟨(lam0.map (canonTarget p)).sum, ?_, ?_⟩
  · rw [nontrivialPartCount_canonSum_eq_card hp.two_le lam0 hlam0s1, hlam0k]
  · rw [defect_eq_sum_Alam_smul hr u hu p, coeff_sum]
    have hsplit : ∑ lam ∈ (nonRefiningPartitions u).image GenPartLatShape,
        coeff ((lam0.map (canonTarget p)).sum) ((Alam u lam) • (lam.map (fun j => K j p)).prod) =
        coeff ((lam0.map (canonTarget p)).sum)
            ((Alam u lam0) • (lam0.map (fun j => K j p)).prod) +
        ∑ lam ∈ ((nonRefiningPartitions u).image GenPartLatShape).erase lam0,
          coeff ((lam0.map (canonTarget p)).sum) ((Alam u lam) • (lam.map (fun j => K j p)).prod) :=
      (Finset.add_sum_erase _ _ hlam0mem).symm
    rw [hsplit]
    have hAlam0pos : 0 < Alam u lam0 := Alam_pos_of_mem_image u hlam0mem
    obtain ⟨V, hVndvd, hVeq⟩ :=
      alam_canonCoeff_prod_eq_pow_mul_ordCompl u hp hlam0s1 hAlam0pos
    have hlam0term : coeff ((lam0.map (canonTarget p)).sum)
        ((Alam u lam0) • (lam0.map (fun j => K j p)).prod) = (p : ℤ) ^ E * (V : ℤ) := by
      rw [coeff_smul, nsmul_eq_mul, coeff_canonSum_prod_K_eq hp.two_le lam0 hlam0s1, hVeq, hlam0E]
    rw [hlam0term]
    have herase_dvd : (p : ℤ) ^ (E + 1) ∣
        ∑ lam ∈ ((nonRefiningPartitions u).image GenPartLatShape).erase lam0,
          coeff ((lam0.map (canonTarget p)).sum)
            ((Alam u lam) • (lam.map (fun j => K j p)).prod) := by
      apply Finset.dvd_sum
      intro lam hlam
      rw [Finset.mem_erase] at hlam
      obtain ⟨hlamne, hlammem⟩ := hlam
      have hlams1 := nonRefiningShape_ge_one u hlammem
      by_cases hlamE : Wp u p lam = E
      · rw [coeff_smul, nsmul_eq_mul,
          coeff_canonSum_lam0_eq_zero_of_ne u hp lam0 hlam0mem hlam0k hlam0m1 hkmin_le
            hlammem hlamE hlamne,
          mul_zero]
        exact dvd_zero _
      · have hWlam : E + 1 ≤ Wp u p lam := by
          have := hE lam hlammem
          omega
        exact dvd_trans (pow_dvd_pow (p : ℤ) hWlam)
          (dvd_coeff_Alam_smul u hp lam hlams1 (fun j hj => by
            have h1 := hlams1 j hj
            have h2 := hp.two_le
            nlinarith) _)
    intro hcontra
    have hterm_dvd : (p : ℤ) ^ (E + 1) ∣ (p : ℤ) ^ E * (V : ℤ) := by
      have h := dvd_sub hcontra herase_dvd
      simpa using h
    rw [pow_succ] at hterm_dvd
    rw [mul_dvd_mul_iff_left (pow_ne_zero E (show (p : ℤ) ≠ 0 by exact_mod_cast hp.pos.ne'))]
      at hterm_dvd
    apply hVndvd
    exact_mod_cast hterm_dvd

#print axioms canonCoeff_eq_pow_mul_ordCompl
#print axioms not_dvd_canonCoeffOrdCompl
#print axioms not_dvd_multiset_prod_of_forall
#print axioms canonCoeff_prod_eq_pow_mul_ordCompl
#print axioms alam_canonCoeff_prod_eq_pow_mul_ordCompl
#print axioms nonRefiningShape_ge_one
#print axioms coeff_canonSum_lam0_eq_zero_of_ne
#print axioms exists_coeff_nontrivialPartCount_eq_not_dvd_pow_succ

end CongruenceTheory
