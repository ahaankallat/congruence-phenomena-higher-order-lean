import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant

/-!
**`thm:complete-prime-local`(iii)'s `(A10)` shift congruence, foundational setup.** For
`N=p+M`, fixing a "distinguished `p`-cycle" `\sigma_0` supported on the first `p` coordinates of
`\text{Fin}(p+M)` (via `Equiv.Perm.extendDomain`) and identity on the rest: `\sigma_0` and all its
nonzero powers up to `p-1` are `p`-cycles. This is the group-theory core the conjugation-orbit
argument for `C_{p+M}\equiv C_p\cdot C_M\pmod p` is built from.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm

variable {p M : ℕ}

/-- **The "first `p` coordinates" subtype of `\text{Fin}(p+M)$.** -/
def firstP (p M : ℕ) : Fin (p + M) → Prop := fun x => x.val < p

instance (p M : ℕ) : DecidablePred (firstP p M) := fun x => Nat.decLt x.val p

/-- **`\text{Fin }p\simeq\{x:\text{Fin}(p+M)\mid x<p\}`.** -/
def inclEquiv (p M : ℕ) : Fin p ≃ Subtype (firstP p M) where
  toFun i := ⟨Fin.castLE (by omega) i, by simp [firstP]⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv i := by simp
  right_inv x := by ext; simp

/-- **The distinguished `p`-cycle `\sigma_0`**, acting as `finRotate p` on the first `p`
coordinates and as the identity on the rest. -/
noncomputable def sigma0 (p M : ℕ) : Equiv.Perm (Fin (p + M)) :=
  (finRotate p).extendDomain (inclEquiv p M)

theorem cycleType_sigma0 (hp : 2 ≤ p) : (sigma0 p M).cycleType = {p} := by
  unfold sigma0
  rw [Equiv.Perm.cycleType_extendDomain, cycleType_finRotate_of_le hp]

theorem isCycle_sigma0 (hp : 2 ≤ p) : (sigma0 p M).IsCycle :=
  (isCycle_finRotate_of_le hp).extendDomain (inclEquiv p M)

theorem card_support_sigma0 (hp : 2 ≤ p) : (sigma0 p M).support.card = p := by
  have h1 := (isCycle_sigma0 (M := M) hp).cycleType
  rw [cycleType_sigma0 (M := M) hp] at h1
  exact (Multiset.singleton_inj.mp h1).symm

theorem orderOf_sigma0 (hp : 2 ≤ p) : orderOf (sigma0 p M) = p := by
  rw [(isCycle_sigma0 (M := M) hp).orderOf, card_support_sigma0 (M := M) hp]

/-- **All nonzero powers of `\sigma_0` below `p` are `p`-cycles too.** -/
theorem isCycle_sigma0_pow (hp : p.Prime) {k : ℕ} (hk0 : 0 < k) (hklt : k < p) :
    (sigma0 p M ^ k).IsCycle :=
  (isCycle_sigma0 (M := M) hp.two_le).isCycle_pow_pos_of_lt_prime_order
    (by rw [orderOf_sigma0 (M := M) hp.two_le]; exact hp) k hk0
    (by rwa [orderOf_sigma0 (M := M) hp.two_le])

theorem cycleType_sigma0_pow (hp : p.Prime) {k : ℕ} (hk0 : 0 < k) (hklt : k < p) :
    (sigma0 p M ^ k).cycleType = {p} := by
  have hic := isCycle_sigma0_pow (M := M) hp hk0 hklt
  have hsupp : (sigma0 p M ^ k).support = (sigma0 p M).support :=
    (isCycle_sigma0 (M := M) hp.two_le).support_pow_of_pos_of_lt_orderOf hk0
      (by rwa [orderOf_sigma0 (M := M) hp.two_le])
  rw [hic.cycleType, hsupp, card_support_sigma0 (M := M) hp.two_le]

#print axioms cycleType_sigma0
#print axioms isCycle_sigma0
#print axioms card_support_sigma0
#print axioms orderOf_sigma0
#print axioms isCycle_sigma0_pow
#print axioms cycleType_sigma0_pow

end CongruenceTheory
