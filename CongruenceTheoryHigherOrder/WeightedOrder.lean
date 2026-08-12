import Mathlib
import CongruenceTheoryHigherOrder.PolyOrder
import CongruenceTheoryHigherOrder.WeightedSubst1

/-!
**A weight-parametrized order-of-vanishing notion**, generalizing `PolyOrder.lean`'s `MinDeg`
(which fixes the all-ones weight) to an arbitrary `w:\N\to\N`. Applied with `w=\text{nontrivial}`
(`w\,1=0`, `w\,k=1` for `k\ne1`), `WOrder` recovers `\text{nontrivialPartCount}`'s own order
notion directly as a `Finsupp.weight`, letting `thm:complete-prime-local`(iii)'s final assembly
reuse `MinDeg.mul_ge`-style reasoning for `\Delta_{\mathbf n}`'s own `X_1`-graded structure.
-/

namespace CongruenceTheory

open MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- The `w`-weighted degree of a monomial exponent `d`. -/
noncomputable def wDeg (w : ℕ → ℕ) (d : ℕ →₀ ℕ) : ℕ := Finsupp.weight w d

theorem wDeg_eq_sum (w : ℕ → ℕ) (d : ℕ →₀ ℕ) : wDeg w d = d.sum fun i e => w i * e := by
  unfold wDeg
  rw [Finsupp.weight_apply]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_eq_mul]
  ring

theorem wDeg_add (w : ℕ → ℕ) (d₁ d₂ : ℕ →₀ ℕ) : wDeg w (d₁ + d₂) = wDeg w d₁ + wDeg w d₂ := by
  unfold wDeg
  exact map_add (Finsupp.weight w) d₁ d₂

/-- **The "nontrivial" weight**: `0` at index `1`, `1` elsewhere. -/
def nontrivialWeight : ℕ → ℕ := fun i => if i = 1 then 0 else 1

theorem wDeg_nontrivialWeight_eq (d : ℕ →₀ ℕ) (hd0 : d 0 = 0) :
    wDeg nontrivialWeight d = nontrivialPartCount d := by
  rw [wDeg_eq_sum]
  unfold nontrivialPartCount nontrivialWeight
  rw [Finsupp.sum]
  have hfiltereq : d.support.filter (fun k => ¬ k = 1) = d.support.filter (2 ≤ ·) := by
    ext k
    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨hk, hk1⟩
      refine ⟨hk, ?_⟩
      by_contra hlt
      push_neg at hlt
      interval_cases k
      · exact hk hd0
      · exact hk1 rfl
    · rintro ⟨hk, hk2⟩
      exact ⟨hk, by omega⟩
  rw [show (∑ i ∈ d.support, (if i = 1 then 0 else 1) * d i) =
      ∑ i ∈ d.support.filter (fun k => ¬ k = 1), d i from by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk1 : k = 1
    · simp [hk1]
    · simp [hk1]]
  rw [hfiltereq]

/-- **`\text{wDeg nontrivialWeight}\,e=\text{monoDeg}\,e`, given `e\,1=0`** — a cleaner, more
directly usable fact than `wDeg_nontrivialWeight_eq` (no `e\,0=0` hypothesis needed): since
`e\,1=0`, index `1` never contributes to either sum, so `\text{nontrivialWeight}` (which is `1`
everywhere except index `1`) agrees with the all-ones weight on `e`'s entire support. -/
theorem wDeg_nontrivialWeight_eq_monoDeg_of_apply_one_eq_zero (e : ℕ →₀ ℕ) (he1 : e 1 = 0) :
    wDeg nontrivialWeight e = monoDeg e := by
  rw [wDeg_eq_sum, monoDeg_eq_sum]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : k ≠ 1 := by
    intro hEq
    subst hEq
    rw [Finsupp.mem_support_iff] at hk
    exact hk he1
  simp only [nontrivialWeight, if_neg hk1, one_mul]

/-- **`w`-order of `\varphi` is exactly `k`**: every nonzero-coefficient monomial has `w`-degree
`\ge k`, and some nonzero-coefficient monomial has `w`-degree exactly `k`. -/
def WOrder (w : ℕ → ℕ) (φ : MvPolynomial ℕ R) (k : ℕ) : Prop :=
  (∀ d ∈ φ.support, k ≤ wDeg w d) ∧ ∃ d ∈ φ.support, wDeg w d = k

theorem WOrder.ne_zero {w : ℕ → ℕ} {φ : MvPolynomial ℕ R} {k : ℕ} (h : WOrder w φ k) : φ ≠ 0 := by
  obtain ⟨d, hd, -⟩ := h.2
  intro hφ
  rw [hφ] at hd
  simp at hd

theorem WOrder.le {w : ℕ → ℕ} {φ : MvPolynomial ℕ R} {k : ℕ} (h : WOrder w φ k) {d : ℕ →₀ ℕ}
    (hd : d ∈ φ.support) : k ≤ wDeg w d := h.1 d hd

/-- **`w`-order of a product is `\ge` the sum of the orders**, always. -/
theorem WOrder.mul_ge {w : ℕ → ℕ} {φ ψ : MvPolynomial ℕ R} {k₁ k₂ : ℕ} (h1 : WOrder w φ k₁)
    (h2 : WOrder w ψ k₂) : ∀ d ∈ (φ * ψ).support, k₁ + k₂ ≤ wDeg w d := by
  intro d hd
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hd
  by_contra hcon
  push_neg at hcon
  apply hd
  apply Finset.sum_eq_zero
  rintro ⟨d1, d2⟩ hmem
  simp only [Finset.mem_antidiagonal] at hmem
  by_cases hd1 : coeff d1 φ = 0
  · simp [hd1]
  by_cases hd2 : coeff d2 ψ = 0
  · simp [hd2]
  exfalso
  have hge1 : k₁ ≤ wDeg w d1 := h1.le (MvPolynomial.mem_support_iff.mpr hd1)
  have hge2 : k₂ ≤ wDeg w d2 := h2.le (MvPolynomial.mem_support_iff.mpr hd2)
  have hdeq : wDeg w d = wDeg w d1 + wDeg w d2 := by rw [← hmem, wDeg_add]
  omega

/-- **Exact order of a product**, given an "isolated" degree-`k_1` witness `d_1` in `\varphi`'s
support: if `d_1` is the *unique* `w`-degree-`k_1` element of `\varphi`'s support, and `\psi` has
order exactly `k_2`, then `\varphi\psi` has order exactly `k_1+k_2`, witnessed at `d_1+d_2`
(`d_2`, `\psi`'s own witness). -/
theorem WOrder.mul_exact [NoZeroDivisors R] {w : ℕ → ℕ} {φ ψ : MvPolynomial ℕ R} {k₁ k₂ : ℕ}
    (h1 : WOrder w φ k₁) (h1u : ∀ d ∈ φ.support, wDeg w d = k₁ → d = Classical.choose h1.2)
    (h2 : WOrder w ψ k₂) : WOrder w (φ * ψ) (k₁ + k₂) := by
  set d₁ := Classical.choose h1.2 with hd₁def
  have hd₁spec := Classical.choose_spec h1.2
  obtain ⟨d₁mem, hd₁deg⟩ := hd₁spec
  obtain ⟨d₂, hd₂mem, hd₂deg⟩ := h2.2
  have hcoeff : MvPolynomial.coeff (d₁ + d₂) (φ * ψ) =
      MvPolynomial.coeff d₁ φ * MvPolynomial.coeff d₂ ψ := by
    rw [MvPolynomial.coeff_mul]
    rw [Finset.sum_eq_single (d₁, d₂)]
    · intro b hbmem hbne
      simp only [Finset.mem_antidiagonal] at hbmem
      by_cases hb2 : MvPolynomial.coeff b.2 ψ = 0
      · rw [hb2, mul_zero]
      · by_cases hb1 : MvPolynomial.coeff b.1 φ = 0
        · rw [hb1, zero_mul]
        · exfalso
          have hb2mem : b.2 ∈ ψ.support := MvPolynomial.mem_support_iff.mpr hb2
          have hb2deg : k₂ ≤ wDeg w b.2 := h2.le hb2mem
          have hb1mem : b.1 ∈ φ.support := MvPolynomial.mem_support_iff.mpr hb1
          have hb1deg : k₁ ≤ wDeg w b.1 := h1.le hb1mem
          have hdeq : wDeg w (d₁ + d₂) = wDeg w b.1 + wDeg w b.2 := by
            rw [← hbmem, wDeg_add]
          rw [wDeg_add, hd₁deg, hd₂deg] at hdeq
          have hb1eq : wDeg w b.1 = k₁ := by omega
          have hb1eqd₁ : b.1 = d₁ := h1u b.1 hb1mem hb1eq
          apply hbne
          have hd₂eqb2 : d₂ = b.2 := by
            have hh := hbmem
            rw [hb1eqd₁] at hh
            exact ((add_right_inj d₁).mp hh).symm
          exact Prod.ext hb1eqd₁ hd₂eqb2.symm
    · intro hnotmem
      exfalso
      apply hnotmem
      simp [Finset.mem_antidiagonal]
  refine ⟨?_, d₁ + d₂, ?_, ?_⟩
  · intro d hd
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hd
    by_contra hlt
    push_neg at hlt
    apply hd
    apply Finset.sum_eq_zero
    rintro ⟨d1, d2⟩ hmem
    simp only [Finset.mem_antidiagonal] at hmem
    by_cases hd1 : coeff d1 φ = 0
    · simp [hd1]
    by_cases hd2 : coeff d2 ψ = 0
    · simp [hd2]
    exfalso
    have hge1 : k₁ ≤ wDeg w d1 := h1.le (MvPolynomial.mem_support_iff.mpr hd1)
    have hge2 : k₂ ≤ wDeg w d2 := h2.le (MvPolynomial.mem_support_iff.mpr hd2)
    have hdeq : wDeg w d = wDeg w d1 + wDeg w d2 := by rw [← hmem, wDeg_add]
    omega
  · rw [MvPolynomial.mem_support_iff, hcoeff]
    exact mul_ne_zero (MvPolynomial.mem_support_iff.mp d₁mem)
      (MvPolynomial.mem_support_iff.mp hd₂mem)
  · rw [wDeg_add, hd₁deg, hd₂deg]

#print axioms wDeg_add
#print axioms wDeg_nontrivialWeight_eq
#print axioms wDeg_nontrivialWeight_eq_monoDeg_of_apply_one_eq_zero
#print axioms WOrder.ne_zero
#print axioms WOrder.mul_ge
#print axioms WOrder.mul_exact

end CongruenceTheory
