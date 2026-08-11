import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.CycleDepthHierarchy
import CongruenceTheoryHigherOrder.SpecializationUnitCoeff

/-!
**Gauss's lemma mod `p` for `MvPolynomial ℕ ℤ`'s content.** If `f`'s reduction mod `p` is
nonzero (equivalently `p \nmid \operatorname{cont} f`), then multiplying by `f` preserves the
exact `p`-adic valuation of the content: `v_p(\operatorname{cont}(fg)) = v_p(\operatorname{cont}
g)`. Proved via `\text{MvPolynomial}\ \Bbb N\ (\Bbb Z/p)` being an integral domain (`p` prime),
combined with `divPoly`'s exact coefficientwise division.
-/

namespace CongruenceTheory

open MvPolynomial

variable {p : ℕ}

/-- **`\operatorname{cont}\varphi \ne 0` whenever `\varphi\ne0`.** -/
theorem cont_ne_zero_of_ne_zero {φ : MvPolynomial ℕ ℤ} (hφ : φ ≠ 0) : cont φ ≠ 0 := by
  have hex : ∃ d, coeff d φ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hφ (MvPolynomial.ext _ _ (fun d => by rw [hcon d, coeff_zero]))
  obtain ⟨d, hd⟩ := hex
  unfold cont
  rw [Ne, Finset.gcd_eq_zero_iff]
  intro hall
  exact hd (Int.natAbs_eq_zero.mp (hall d (mem_support_iff.mpr hd)))

/-- **`\text{map}(f) = 0 \iff p \mid \operatorname{cont} f`.** -/
theorem map_eq_zero_iff_dvd_cont (hp : p.Prime) (f : MvPolynomial ℕ ℤ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) f = 0 ↔ p ∣ cont f := by
  haveI := Fact.mk hp
  constructor
  · intro h0
    unfold cont
    apply Finset.dvd_gcd
    intro d hd
    have h1 : coeff d (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = 0 := by
      rw [h0, coeff_zero]
    rw [MvPolynomial.coeff_map] at h1
    have hdvd : (p : ℤ) ∣ coeff d f := by
      rwa [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
    rwa [Int.natAbs_natCast] at h2
  · intro hdvd
    apply MvPolynomial.ext
    intro d
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    by_cases hd : d ∈ f.support
    · have hcdvd : p ∣ (coeff d f).natAbs := by
        unfold cont at hdvd
        exact dvd_trans hdvd (Finset.gcd_dvd hd)
      have hcdvd' : (p : ℤ) ∣ coeff d f := by
        have h2 := Int.natCast_dvd_natCast.mpr hcdvd
        rwa [Int.dvd_natAbs] at h2
      simp only [eq_intCast]
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
    · rw [mem_support_iff, not_not] at hd
      simp [hd]

/-- **`\operatorname{cont}(C(p)\cdot h) = p \cdot \operatorname{cont} h`.** -/
theorem cont_C_p_mul (hp : p.Prime) (h : MvPolynomial ℕ ℤ) :
    cont (MvPolynomial.C (p : ℤ) * h) = p * cont h := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hsupp : (MvPolynomial.C (p : ℤ) * h).support = h.support := by
    ext d
    rw [mem_support_iff, mem_support_iff, coeff_C_mul]
    constructor
    · intro hne heq
      exact hne (by rw [heq, mul_zero])
    · intro hne heq
      exact hne ((mul_eq_zero.mp heq).resolve_left hp0)
  have heqf : (fun d => (coeff d (MvPolynomial.C (p : ℤ) * h)).natAbs) = (fun d => p * (coeff d h).natAbs) := by
    funext d
    rw [coeff_C_mul, Int.natAbs_mul, Int.natAbs_natCast]
  unfold cont
  rw [hsupp, heqf, Finset.gcd_mul_left]
  simp

/-- **`C(p) \cdot \text{divPoly}\ h\ p = h`** when `p \mid \operatorname{cont} h`. -/
theorem C_p_mul_divPoly_eq (hp : p.Prime) {h : MvPolynomial ℕ ℤ} (hdvd : p ∣ cont h) :
    MvPolynomial.C (p : ℤ) * divPoly h p = h := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_C_mul, coeff_divPoly]
  by_cases hd : d ∈ h.support
  · have hcdvd : p ∣ (coeff d h).natAbs := dvd_trans hdvd (by unfold cont; exact Finset.gcd_dvd hd)
    have hcdvd' : (p : ℤ) ∣ coeff d h := by
      have h2 := Int.natCast_dvd_natCast.mpr hcdvd
      rwa [Int.dvd_natAbs] at h2
    exact Int.mul_ediv_cancel' hcdvd'
  · rw [mem_support_iff, not_not] at hd
    rw [hd]; simp

/-- **Gauss's lemma mod `p`, exact valuation form.** If `\text{map}(f) \ne 0` (i.e.
`p \nmid \operatorname{cont} f`), multiplying by `f` preserves the `p`-adic valuation of the
content exactly. -/
theorem factorization_cont_mul_of_map_ne_zero (hp : p.Prime) {f : MvPolynomial ℕ ℤ}
    (hf : MvPolynomial.map (Int.castRingHom (ZMod p)) f ≠ 0) :
    ∀ n : ℕ, ∀ g : MvPolynomial ℕ ℤ, (cont g).factorization p = n → g ≠ 0 →
      (cont (f * g)).factorization p = n := by
  haveI := Fact.mk hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hgn hgne
    have hcgne : cont g ≠ 0 := cont_ne_zero_of_ne_zero hgne
    by_cases hn0 : n = 0
    · subst hn0
      have hndvd : ¬ p ∣ cont g := by
        intro hc
        have := (Nat.Prime.dvd_iff_one_le_factorization hp hcgne).mp hc
        omega
      have hgmapne : MvPolynomial.map (Int.castRingHom (ZMod p)) g ≠ 0 :=
        fun h0 => hndvd ((map_eq_zero_iff_dvd_cont hp g).mp h0)
      have hfgmapne : MvPolynomial.map (Int.castRingHom (ZMod p)) (f * g) ≠ 0 := by
        rw [map_mul]
        exact mul_ne_zero hf hgmapne
      have hndvd2 : ¬ p ∣ cont (f * g) := fun hc =>
        hfgmapne ((map_eq_zero_iff_dvd_cont hp (f * g)).mpr hc)
      rw [Nat.factorization_eq_zero_iff]
      right; left; exact hndvd2
    · have hpdvd : p ∣ cont g := by
        rw [Nat.Prime.dvd_iff_one_le_factorization hp hcgne]
        omega
      set g' := divPoly g p with hg'
      have hgeq : MvPolynomial.C (p : ℤ) * g' = g := C_p_mul_divPoly_eq hp hpdvd
      have hg'ne : g' ≠ 0 := by
        intro h0
        apply hgne
        rw [← hgeq, h0, mul_zero]
      have hcontg : cont g = p * cont g' := by rw [← hgeq, cont_C_p_mul hp]
      have hg'ne' : cont g' ≠ 0 := cont_ne_zero_of_ne_zero hg'ne
      have hfactg : (cont g).factorization p = 1 + (cont g').factorization p := by
        rw [hcontg, Nat.factorization_mul hp.pos.ne' hg'ne']
        simp [Nat.Prime.factorization_self hp]
      have hg'n : (cont g').factorization p = n - 1 := by omega
      have hihg' := ih (n - 1) (by omega) g' hg'n hg'ne
      have hfgeq : MvPolynomial.C (p : ℤ) * (f * g') = f * g := by rw [← hgeq]; ring
      have hfgne : f * g' ≠ 0 := by
        intro h0
        rcases mul_eq_zero.mp h0 with hf0 | hg'0
        · apply hf; rw [hf0]; simp
        · exact hg'ne hg'0
      have hcontfg : cont (f * g) = p * cont (f * g') := by rw [← hfgeq, cont_C_p_mul hp]
      have hfgne' : cont (f * g') ≠ 0 := cont_ne_zero_of_ne_zero hfgne
      rw [hcontfg, Nat.factorization_mul hp.pos.ne' hfgne']
      simp only [Nat.Prime.factorization_self hp, Finsupp.coe_add, Pi.add_apply]
      omega

#print axioms cont_ne_zero_of_ne_zero
#print axioms map_eq_zero_iff_dvd_cont
#print axioms cont_C_p_mul
#print axioms C_p_mul_divPoly_eq
#print axioms factorization_cont_mul_of_map_ne_zero

end CongruenceTheory
