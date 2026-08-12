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

#print axioms pow_p_eq_expand
#print axioms monoDeg_smul
#print axioms MinDeg_pow_p

end CongruenceTheory
