import Mathlib
import CongruenceTheoryHigherOrder.PolyOrder

/-!
**`thm:complete-prime-local`(iii)'s `(A11)`/`(A12)`: exact order of a `p`-th power.**
In characteristic `p`, `f^p` is literally `f` with every monomial exponent scaled by `p`
(`MvPolynomial.expand`, since the Frobenius on `\mathbb F_p` is the identity by Fermat), so its
`J`-adic order is *exactly* `p` times `f`'s own order — no cancellation is possible, unlike a
general product. This is the key fact turning the Frobenius factorization
(`DcFrobenius.lean`) into an *exact* order computation.
-/

namespace CongruenceTheory

open MvPolynomial

variable {p : ℕ}

/-- **`f^p` is `f` with every exponent scaled by `p`**, since Frobenius is the identity on
`\mathbb F_p`. -/
theorem pow_p_eq_expand (hp : p.Prime) (f : MvPolynomial ℕ (ZMod p)) :
    f ^ p = MvPolynomial.expand p f := by
  haveI := Fact.mk hp
  have hfrob : frobenius (ZMod p) p = RingHom.id (ZMod p) := by
    ext x
    exact ZMod.pow_card x
  have hkey := MvPolynomial.map_frobenius_expand (R := ZMod p) (σ := ℕ) (p := p) (f := f)
  rw [hfrob, MvPolynomial.map_id] at hkey
  exact hkey.symm

/-- **`\text{monoDeg}(p\bullet d) = p\cdot\text{monoDeg}(d)`.** -/
theorem monoDeg_smul (p : ℕ) (d : ℕ →₀ ℕ) : monoDeg (p • d) = p * monoDeg d := by
  rw [monoDeg_eq_sum, monoDeg_eq_sum]
  rw [Finsupp.sum, Finsupp.sum]
  by_cases hp0 : p = 0
  · subst hp0; simp
  · rw [Finsupp.support_smul_eq hp0]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finsupp.smul_apply]
    ring

/-- **The `J`-adic order of `f^p` is exactly `p` times `f`'s own order.** -/
theorem MinDeg_pow_p (hp : p.Prime) {f : MvPolynomial ℕ (ZMod p)} {m : ℕ} (hf : MinDeg f m) :
    MinDeg (f ^ p) (p * m) := by
  rw [pow_p_eq_expand hp]
  constructor
  · intro d hd
    rw [MvPolynomial.support_expand (hp := hp.pos.ne')] at hd
    rw [Finset.mem_image] at hd
    obtain ⟨d', hd', hd'eq⟩ := hd
    rw [← hd'eq, monoDeg_smul]
    have := hf.le hd'
    exact Nat.mul_le_mul_left p this
  · obtain ⟨d₀, hd₀mem, hd₀deg⟩ := hf.2
    refine ⟨p • d₀, ?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff, coeff_expand_smul p hp.pos.ne']
      exact MvPolynomial.mem_support_iff.mp hd₀mem
    · rw [monoDeg_smul, hd₀deg]

/-- **Multiplying by a `J`-adic unit (nonzero constant term) does not change order.** -/
theorem MinDeg_unit_mul (hp : p.Prime) {u X : MvPolynomial ℕ (ZMod p)} {m : ℕ}
    (hu0 : MvPolynomial.coeff 0 u ≠ 0) (hX : MinDeg X m) :
    MinDeg (u * X) m := by
  haveI := Fact.mk hp
  obtain ⟨d₀, hd₀mem, hd₀deg⟩ := hX.2
  have hcoeff : MvPolynomial.coeff d₀ (u * X) = MvPolynomial.coeff 0 u * MvPolynomial.coeff d₀ X := by
    rw [MvPolynomial.coeff_mul]
    rw [Finset.sum_eq_single (0, d₀)]
    · intro b hbmem hbne
      simp only [Finset.mem_antidiagonal] at hbmem
      by_cases hb2 : MvPolynomial.coeff b.2 X = 0
      · rw [hb2, mul_zero]
      · exfalso
        have hb2mem : b.2 ∈ X.support := MvPolynomial.mem_support_iff.mpr hb2
        have hb2deg : m ≤ monoDeg b.2 := hX.le hb2mem
        have hdeq : monoDeg d₀ = monoDeg b.1 + monoDeg b.2 := by
          rw [← hbmem, monoDeg_add]
        rw [hd₀deg] at hdeq
        have hb1deg0 : monoDeg b.1 = 0 := by omega
        have hb1zero : b.1 = 0 := by
          rw [monoDeg_eq_sum, Finsupp.sum] at hb1deg0
          by_contra hne
          obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
          have hbi : b.1 i ≠ 0 := Finsupp.mem_support_iff.mp hi
          have hle : b.1 i ≤ ∑ a ∈ b.1.support, b.1 a :=
            Finset.single_le_sum (fun a _ => Nat.zero_le (b.1 a)) hi
          omega
        apply hbne
        have hb2eq : b.2 = d₀ := by
          rw [hb1zero, zero_add] at hbmem
          exact hbmem
        exact Prod.ext hb1zero hb2eq
    · intro hnotmem
      exfalso
      apply hnotmem
      simp [Finset.mem_antidiagonal]
  constructor
  · intro d hd
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hd
    by_contra hlt
    push_neg at hlt
    apply hd
    apply Finset.sum_eq_zero
    rintro ⟨d1, d2⟩ hmem
    simp only [Finset.mem_antidiagonal] at hmem
    by_cases hd2 : MvPolynomial.coeff d2 X = 0
    · simp [hd2]
    · exfalso
      have hd2mem : d2 ∈ X.support := MvPolynomial.mem_support_iff.mpr hd2
      have hd2deg : m ≤ monoDeg d2 := hX.le hd2mem
      have hdeq : monoDeg d = monoDeg d1 + monoDeg d2 := by rw [← hmem, monoDeg_add]
      omega
  · refine ⟨d₀, ?_, hd₀deg⟩
    rw [MvPolynomial.mem_support_iff, hcoeff]
    exact mul_ne_zero hu0 (MvPolynomial.mem_support_iff.mp hd₀mem)

#print axioms pow_p_eq_expand
#print axioms monoDeg_smul
#print axioms MinDeg_pow_p
#print axioms MinDeg_unit_mul

end CongruenceTheory
