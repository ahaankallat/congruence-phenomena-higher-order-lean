import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.ShiftCongruenceSetup
import CongruenceTheoryHigherOrder.ShiftCongruenceOrbit
import CongruenceTheoryHigherOrder.ShiftCongruenceOrbitSize

/-!
**`thm:complete-prime-local`(iii)'s `(A10)` shift congruence: the centralizer sum.**
Every element commuting with `\sigma_0` (the distinguished `p`-cycle on the first `p`
coordinates of `\text{Fin}(p+M)`) factors uniquely as `\sigma_0^k` times a permutation of the
last `M` coordinates, so the centralizer-of-`\sigma_0` sum from `ShiftCongruenceOrbitSize.lean`
equals `(\sum_{k<p} \text{ci}(\text{finRotate }p)^k) \cdot \text{Cperm}(M)`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm

variable {p M : ℕ}

open scoped Classical

/-- The "last `M` coordinates" subtype of `\text{Fin}(p+M)`, the complement of `firstP`. -/
def lastM (p M : ℕ) : Fin (p + M) → Prop := fun x => p ≤ x.val

/-- `\text{Fin }M\simeq\{x:\text{Fin}(p+M)\mid p\le x\}`. -/
def complementIncl (p M : ℕ) : Fin M ≃ Subtype (lastM p M) where
  toFun i := ⟨⟨p + i.val, by omega⟩, by simp [lastM]⟩
  invFun x := ⟨x.1.val - p, by have := x.2; simp only [lastM] at this; omega⟩
  left_inv i := by ext; simp
  right_inv x := by ext; have := x.2; simp only [lastM] at this; simp; omega

/-- A permutation of `\text{Fin }M`, extended to `\text{Fin}(p+M)` by fixing the first `p`
coordinates. -/
noncomputable def tauExt (p M : ℕ) (τ : Equiv.Perm (Fin M)) : Equiv.Perm (Fin (p + M)) :=
  τ.extendDomain (complementIncl p M)

theorem cycleType_tauExt (τ : Equiv.Perm (Fin M)) :
    (tauExt p M τ).cycleType = τ.cycleType :=
  Equiv.Perm.cycleType_extendDomain (complementIncl p M)

theorem cycleType_sigma0_pow_eq (k : ℕ) :
    (sigma0 p M ^ k).cycleType = ((finRotate p) ^ k).cycleType := by
  unfold sigma0
  rw [← Equiv.Perm.extendDomain_pow, Equiv.Perm.cycleType_extendDomain]

/-- `\sigma_0^k` and any extended `\tau` have disjoint support. -/
theorem disjoint_sigma0_pow_tauExt (k : ℕ) (τ : Equiv.Perm (Fin M)) :
    Equiv.Perm.Disjoint (sigma0 p M ^ k) (tauExt p M τ) := by
  intro x
  by_cases hx : firstP p M x
  · right
    apply Equiv.Perm.extendDomain_apply_not_subtype
    simp only [lastM]
    have := hx
    simp only [firstP] at this
    omega
  · left
    unfold sigma0
    rw [← Equiv.Perm.extendDomain_pow]
    apply Equiv.Perm.extendDomain_apply_not_subtype
    exact hx

theorem commute_sigma0_tauExt (τ : Equiv.Perm (Fin M)) :
    Commute (sigma0 p M) (tauExt p M τ) := by
  have h := (disjoint_sigma0_pow_tauExt (p := p) (M := M) 1 τ).commute
  rwa [pow_one] at h

/-- **Cross-domain multiplicativity of `ci`** for `\sigma_0^k` times an extended `\tau`. -/
theorem ci_sigma0_pow_mul_tauExt (hp : 0 < p) (k : ℕ) (τ : Equiv.Perm (Fin M)) :
    ci (sigma0 p M ^ k * tauExt p M τ) = ci ((finRotate p) ^ k) * ci τ := by
  have hle1 : ((finRotate p) ^ k).cycleType.sum ≤ p := by
    have := Equiv.Perm.sum_cycleType_le ((finRotate p) ^ k)
    simpa using this
  have hle2 : τ.cycleType.sum ≤ M := by
    have := Equiv.Perm.sum_cycleType_le τ
    simpa using this
  have hcyc : (sigma0 p M ^ k * tauExt p M τ).cycleType =
      ((finRotate p) ^ k).cycleType + τ.cycleType := by
    rw [(disjoint_sigma0_pow_tauExt k τ).cycleType_mul, cycleType_sigma0_pow_eq,
      cycleType_tauExt]
  simp only [ci, hcyc, Multiset.sum_add, Multiset.map_add, Multiset.prod_add,
    Fintype.card_fin]
  rw [show p + M - (((finRotate p) ^ k).cycleType.sum + τ.cycleType.sum) =
      (p - ((finRotate p) ^ k).cycleType.sum) + (M - τ.cycleType.sum) by omega,
    pow_add]
  ring

/-- `\text{finRotate }p` has `p` elements in its support. -/
theorem card_support_finRotate_of_le (hp : 2 ≤ p) : (finRotate p).support.card = p := by
  have h1 := (isCycle_finRotate_of_le hp).cycleType
  rw [cycleType_finRotate_of_le hp] at h1
  exact (Multiset.singleton_inj.mp h1).symm

/-- `\text{finRotate }p` has order `p`. -/
theorem orderOf_finRotate (hp : 2 ≤ p) : orderOf (finRotate p) = p := by
  rw [(isCycle_finRotate_of_le hp).orderOf, card_support_finRotate_of_le hp]

theorem ci_finRotate_pow_of_ne_zero (hp : p.Prime) {k : ℕ} (hk0 : 0 < k) (hklt : k < p) :
    ci ((finRotate p) ^ k) = (MvPolynomial.X p : MvPolynomial ℕ ℤ) := by
  have hcyc : ((finRotate p) ^ k).cycleType = ({p} : Multiset ℕ) := by
    have hic := (isCycle_finRotate_of_le hp.two_le).isCycle_pow_pos_of_lt_prime_order
      (by rw [orderOf_finRotate hp.two_le]; exact hp) k hk0
      (by rwa [orderOf_finRotate hp.two_le])
    have hsupp : ((finRotate p) ^ k).support = (finRotate p).support :=
      (isCycle_finRotate_of_le hp.two_le).support_pow_of_pos_of_lt_orderOf hk0
        (by rwa [orderOf_finRotate hp.two_le])
    rw [hic.cycleType, hsupp, card_support_finRotate_of_le hp.two_le]
  simp only [ci, hcyc, Fintype.card_fin, Multiset.sum_singleton, Multiset.map_singleton,
    Multiset.prod_singleton]
  have : p - p = 0 := by omega
  rw [this, pow_zero, one_mul]

theorem ci_finRotate_zero (p : ℕ) :
    ci ((finRotate p) ^ 0) = (MvPolynomial.X 1 : MvPolynomial ℕ ℤ) ^ p := by
  simp [ci, Equiv.Perm.cycleType_one]

/-- **The rotation sum**: `\sum_{k<p}\text{ci}((\text{finRotate }p)^k) = X_1^p + (p-1)\cdot X_p`. -/
theorem sum_ci_finRotate_pow (hp : p.Prime) :
    ∑ k ∈ Finset.range p, ci ((finRotate p) ^ k) =
      (MvPolynomial.X 1 : MvPolynomial ℕ ℤ) ^ p +
        ((p - 1 : ℕ) : MvPolynomial ℕ ℤ) * MvPolynomial.X p := by
  have hp1 : p = (p - 1) + 1 := by have := hp.two_le; omega
  have hrange : Finset.range p = Finset.range ((p - 1) + 1) := congrArg Finset.range hp1
  rw [hrange, Finset.sum_range_succ']
  have hterm : ∀ k ∈ Finset.range (p - 1),
      ci ((finRotate p) ^ (k + 1)) = (MvPolynomial.X p : MvPolynomial ℕ ℤ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact ci_finRotate_pow_of_ne_zero hp (Nat.succ_pos k) (by omega)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, ci_finRotate_zero,
    nsmul_eq_mul]
  ring

#print axioms cycleType_tauExt
#print axioms cycleType_sigma0_pow_eq
#print axioms disjoint_sigma0_pow_tauExt
#print axioms commute_sigma0_tauExt
#print axioms ci_sigma0_pow_mul_tauExt
#print axioms card_support_finRotate_of_le
#print axioms orderOf_finRotate
#print axioms ci_finRotate_pow_of_ne_zero
#print axioms ci_finRotate_zero
#print axioms sum_ci_finRotate_pow

end CongruenceTheory
