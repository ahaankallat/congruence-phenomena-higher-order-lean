import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheory.OrbitSum
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.ShiftCongruenceSetup
import CongruenceTheoryHigherOrder.ShiftCongruenceOrbit

/-!
**`thm:complete-prime-local`(iii)'s `(A10)` shift congruence: orbit sizes and the
centralizer-sum decomposition.** Every `\sigma_0`-conjugation orbit of a non-centralizing
element has size exactly `p` (via a from-scratch "cyclic group of prime order acts freely away
from fixed points" argument), so `dvd_sum_of_const_on_classes` splits `\text{Cperm}(p+M)` into
the centralizer-of-`\sigma_0` sum plus a multiple of `p`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm

variable {p M : ℕ}

open scoped Classical

/-- **Prime-order generation**: if `a^d` commutes with `x`, `orderOf a = p` is prime, and
`0 < d < p`, then `a` itself commutes with `x`. -/
theorem commute_of_pow_commute_of_orderOf_prime {G : Type*} [Group G] (a x : G) (p d : ℕ)
    (hp : p.Prime) (ha : orderOf a = p) (hd0 : 0 < d) (hdp : d < p)
    (h : Commute (a ^ d) x) : Commute a x := by
  have hnd : ¬ p ∣ d := by
    intro hdvd
    have hle := Nat.le_of_dvd hd0 hdvd
    omega
  have hcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hnd).symm
  have hpow1 : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb := Nat.gcd_eq_gcd_ab d p
  rw [hcop] at hb
  have hkey : a ^ ((d : ℤ) * Nat.gcdA d p) = a := by
    have hb1 : (1 : ℤ) = (p : ℤ) * Nat.gcdB d p + (d : ℤ) * Nat.gcdA d p := by
      rw [add_comm]; exact_mod_cast hb
    have h1 : a ^ (1 : ℤ) = a ^ ((p : ℤ) * Nat.gcdB d p + (d : ℤ) * Nat.gcdA d p) := by
      rw [hb1]
    rw [zpow_one, zpow_add, zpow_mul, zpow_natCast a p, hpow1, one_zpow, one_mul] at h1
    exact h1.symm
  have heq2 : (a ^ d : G) ^ (Nat.gcdA d p) = a ^ ((d : ℤ) * Nat.gcdA d p) := by
    rw [← zpow_natCast a d, ← zpow_mul]
  have hcomm3 : Commute ((a ^ d : G) ^ (Nat.gcdA d p)) x := h.zpow_left (Nat.gcdA d p)
  rw [heq2, hkey] at hcomm3
  exact hcomm3

/-- Conjugation by a power of `\sigma_0` fixes `\sigma_0` itself, so it preserves whether an
element commutes with `\sigma_0`. -/
theorem commute_sigma0_conj_iff (x : Equiv.Perm (Fin (p + M))) (k : ℕ) :
    Commute (sigma0 p M) (sigma0 p M ^ k * x * (sigma0 p M ^ k)⁻¹) ↔
      Commute (sigma0 p M) x := by
  have hself : Commute (sigma0 p M ^ k) (sigma0 p M) := (Commute.refl (sigma0 p M)).pow_left k
  have hfix : sigma0 p M ^ k * sigma0 p M * (sigma0 p M ^ k)⁻¹ = sigma0 p M := by
    rw [hself]; group
  have hiff := Commute.conj_iff (a := sigma0 p M) (b := x) (sigma0 p M ^ k)
  rw [hfix] at hiff
  exact hiff

/-- `sigma0ConjRel`-related elements agree on whether they commute with `\sigma_0`. -/
theorem commute_sigma0_iff_of_rel {x y : Equiv.Perm (Fin (p + M))} (h : sigma0ConjRel p M x y) :
    Commute (sigma0 p M) x ↔ Commute (sigma0 p M) y := by
  obtain ⟨k, -, hk⟩ := h
  rw [hk]
  exact (commute_sigma0_conj_iff x k).symm

/-- **Orbit rigidity**: if two conjugates by powers of `\sigma_0` below `p` coincide, either the
exponents agree or `x` commutes with `\sigma_0`. -/
theorem commute_of_orbit_eq (hp : p.Prime) (x : Equiv.Perm (Fin (p + M))) {k1 k2 : ℕ}
    (hk1 : k1 < p) (hk2 : k2 < p) (hle : k2 ≤ k1)
    (heq : sigma0 p M ^ k1 * x * (sigma0 p M ^ k1)⁻¹ =
        sigma0 p M ^ k2 * x * (sigma0 p M ^ k2)⁻¹) :
    k1 = k2 ∨ Commute (sigma0 p M) x := by
  rcases eq_or_lt_of_le hle with heq2 | hlt
  · left; omega
  · right
    set d := k1 - k2 with hddef
    have hd0 : 0 < d := by omega
    have hdp : d < p := by omega
    have hsplit : sigma0 p M ^ k1 = sigma0 p M ^ k2 * sigma0 p M ^ d := by
      rw [← pow_add]; congr 1; omega
    have hcancel : (sigma0 p M ^ k2)⁻¹ * (sigma0 p M ^ k1 * x * (sigma0 p M ^ k1)⁻¹) *
        sigma0 p M ^ k2 = x := by
      rw [heq]; group
    rw [hsplit] at hcancel
    have heq3 : sigma0 p M ^ d * x * (sigma0 p M ^ d)⁻¹ = x := by
      calc sigma0 p M ^ d * x * (sigma0 p M ^ d)⁻¹
          = (sigma0 p M ^ k2)⁻¹ * ((sigma0 p M ^ k2 * sigma0 p M ^ d) * x *
              (sigma0 p M ^ k2 * sigma0 p M ^ d)⁻¹) * sigma0 p M ^ k2 := by group
        _ = x := hcancel
    have hcommd : Commute (sigma0 p M ^ d) x := by
      have h2 := congrArg (· * sigma0 p M ^ d) heq3
      simp only [mul_assoc, inv_mul_cancel, mul_one] at h2
      exact h2
    exact commute_of_pow_commute_of_orderOf_prime (sigma0 p M) x p d hp
      (orderOf_sigma0 (M := M) hp.two_le) hd0 hdp hcommd

/-- The `sigma0ConjRel`-class of `x` is exactly the image of `Finset.range p` under
conjugation-by-`\sigma_0^k`. -/
theorem sigma0ConjRel_filter_eq_image (x : Equiv.Perm (Fin (p + M))) :
    Finset.univ.filter (sigma0ConjRel p M x) =
      (Finset.range p).image (fun k => sigma0 p M ^ k * x * (sigma0 p M ^ k)⁻¹) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hklt, hk⟩
    exact ⟨k, hklt, hk.symm⟩
  · rintro ⟨k, hklt, hk⟩
    exact ⟨k, hklt, hk.symm⟩

/-- **Every non-centralizing orbit has size exactly `p`.** -/
theorem card_sigma0ConjRel_class_eq_p_of_noncentral (hp : p.Prime)
    {x : Equiv.Perm (Fin (p + M))} (hx : ¬ Commute (sigma0 p M) x) :
    (Finset.univ.filter (sigma0ConjRel p M x)).card = p := by
  rw [sigma0ConjRel_filter_eq_image]
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range p
  · intro k1 hk1 k2 hk2 heq
    simp only [Finset.coe_range, Set.mem_Iio] at hk1 hk2
    rcases Nat.le_total k2 k1 with hle | hle
    · rcases commute_of_orbit_eq hp x hk1 hk2 hle heq with h | h
      · exact h
      · exact absurd h hx
    · rcases commute_of_orbit_eq hp x hk2 hk1 hle heq.symm with h | h
      · exact h.symm
      · exact absurd h hx

/-- The `sigma0ConjRel`-class of a non-centralizing `x`, filtered within the non-centralizing
set `s`, is the same as the class filtered within the whole space. -/
theorem sigma0ConjRel_filter_noncentral_eq (hp : p.Prime)
    (s : Finset (Equiv.Perm (Fin (p + M))))
    (hs : s = Finset.univ.filter (fun g : Equiv.Perm (Fin (p + M)) => ¬ Commute (sigma0 p M) g))
    {x : Equiv.Perm (Fin (p + M))} (hx : x ∈ s) :
    s.filter (sigma0ConjRel p M x) = Finset.univ.filter (sigma0ConjRel p M x) := by
  ext y
  simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  constructor
  · rintro ⟨-, hy⟩
    exact hy
  · intro hy
    refine ⟨?_, hy⟩
    rw [← commute_sigma0_iff_of_rel hy]
    exact hx

/-- **Key divisibility hypothesis** for `dvd_sum_of_const_on_classes`: every `sigma0ConjRel`
class within the non-centralizing set has size divisible by `p`. -/
theorem sigma0ConjRel_key (hp : p.Prime)
    (s : Finset (Equiv.Perm (Fin (p + M))))
    (hs : s = Finset.univ.filter (fun g : Equiv.Perm (Fin (p + M)) => ¬ Commute (sigma0 p M) g)) :
    ∀ x ∈ s, (p : ℤ) ∣ ((s.filter (sigma0ConjRel p M x)).card : ℤ) := by
  intro x hx
  rw [sigma0ConjRel_filter_noncentral_eq hp s hs hx]
  have hxnc : ¬ Commute (sigma0 p M) x := by
    rw [hs] at hx
    exact (Finset.mem_filter.mp hx).2
  rw [card_sigma0ConjRel_class_eq_p_of_noncentral hp hxnc]

/-- **`\text{Cperm}(p+M)` splits into the centralizer-of-`\sigma_0` sum plus a multiple of
`p`.** -/
theorem Cperm_eq_centralizer_sum_add_mul (hp : p.Prime) :
    ∃ Q : MvPolynomial ℕ ℤ, Cperm (p + M) =
      (∑ g ∈ Finset.univ.filter
          (fun g : Equiv.Perm (Fin (p + M)) => Commute (sigma0 p M) g), ci g)
        + (p : MvPolynomial ℕ ℤ) * Q := by
  set s := Finset.univ.filter
    (fun g : Equiv.Perm (Fin (p + M)) => ¬ Commute (sigma0 p M) g) with hs
  obtain ⟨Q, hQ⟩ := dvd_sum_of_const_on_classes (sigma0ConjRel p M)
    (fun x => sigma0ConjRel_refl x hp.pos)
    (fun x y h => sigma0ConjRel_symm hp h)
    (fun x y z h1 h2 => sigma0ConjRel_trans hp h1 h2)
    ci (fun x y hxy => ci_const_sigma0ConjRel hxy) p s (sigma0ConjRel_key hp s hs)
  refine ⟨Q, ?_⟩
  rw [Cperm, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun g : Equiv.Perm (Fin (p + M)) => Commute (sigma0 p M) g)]
  rw [← hs, hQ]

#print axioms commute_of_pow_commute_of_orderOf_prime
#print axioms commute_sigma0_conj_iff
#print axioms commute_sigma0_iff_of_rel
#print axioms commute_of_orbit_eq
#print axioms sigma0ConjRel_filter_eq_image
#print axioms card_sigma0ConjRel_class_eq_p_of_noncentral
#print axioms sigma0ConjRel_filter_noncentral_eq
#print axioms sigma0ConjRel_key
#print axioms Cperm_eq_centralizer_sum_add_mul

end CongruenceTheory
