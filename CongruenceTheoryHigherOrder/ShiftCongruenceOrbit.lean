import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheory.OrbitSum
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.ShiftCongruenceSetup

/-!
**`thm:complete-prime-local`(iii)'s `(A10)` shift congruence: the orbit-counting step.**
Conjugation by powers of `\sigma_0` (`sigma0 p M`, a distinguished `p`-cycle on the first `p`
coordinates of `\text{Fin}(p+M)`) is a `\Bbb Z/p`-orbit relation on `\text{Perm}(\text{Fin}(p+M))`
under which `ci` is constant; every non-fixed element has an orbit of size exactly `p`. Grouping
`\text{Cperm}(p+M)=\sum_gci(g)` by this relation, via `dvd_sum_of_const_on_classes`, shows
`\text{Cperm}(p+M)` is congruent mod `p` to the sum of `ci` over the elements commuting with
`\sigma_0` (`Subgroup.centralizer\{\sigma_0\}`) — mirroring `CongruenceTheory.Cperm_prime_decomp`'s
own technique.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm

variable {p M : ℕ}

/-- **The conjugation-by-`\sigma_0^k`-relation.** -/
def sigma0ConjRel (p M : ℕ) (g1 g2 : Equiv.Perm (Fin (p + M))) : Prop :=
  ∃ k < p, g2 = sigma0 p M ^ k * g1 * (sigma0 p M ^ k)⁻¹

theorem sigma0ConjRel_refl (g : Equiv.Perm (Fin (p + M))) (hp : 0 < p) :
    sigma0ConjRel p M g g :=
  ⟨0, hp, by simp⟩

theorem sigma0ConjRel_symm (hp : p.Prime) {g1 g2 : Equiv.Perm (Fin (p + M))}
    (h : sigma0ConjRel p M g1 g2) : sigma0ConjRel p M g2 g1 := by
  obtain ⟨k, hklt, hk⟩ := h
  refine ⟨(p - k) % p, Nat.mod_lt _ hp.pos, ?_⟩
  have horder := orderOf_sigma0 (M := M) hp.two_le
  have hpow : sigma0 p M ^ p = 1 := by
    have hp1 := pow_orderOf_eq_one (sigma0 p M)
    rwa [horder] at hp1
  have step1 : sigma0 p M ^ ((p - k) % orderOf (sigma0 p M)) = sigma0 p M ^ (p - k) :=
    pow_mod_orderOf _ _
  rw [horder] at step1
  have hkey : sigma0 p M ^ ((p - k) % p) = (sigma0 p M ^ k)⁻¹ := by
    rw [step1, eq_comm, inv_eq_iff_mul_eq_one, ← pow_add]
    have hsum : k + (p - k) = p := by omega
    rw [hsum, hpow]
  rw [hkey, hk]
  group

theorem sigma0ConjRel_trans (hp : p.Prime) {g1 g2 g3 : Equiv.Perm (Fin (p + M))}
    (h1 : sigma0ConjRel p M g1 g2) (h2 : sigma0ConjRel p M g2 g3) :
    sigma0ConjRel p M g1 g3 := by
  obtain ⟨k1, hk1lt, hk1⟩ := h1
  obtain ⟨k2, hk2lt, hk2⟩ := h2
  refine ⟨(k2 + k1) % p, Nat.mod_lt _ hp.pos, ?_⟩
  have horder := orderOf_sigma0 (M := M) hp.two_le
  have step1 : sigma0 p M ^ ((k2 + k1) % orderOf (sigma0 p M)) = sigma0 p M ^ (k2 + k1) :=
    pow_mod_orderOf _ _
  rw [horder] at step1
  have hkey : sigma0 p M ^ ((k2 + k1) % p) = sigma0 p M ^ k2 * sigma0 p M ^ k1 := by
    rw [step1, pow_add]
  rw [hkey, hk2, hk1]
  group

theorem ci_const_sigma0ConjRel {g1 g2 : Equiv.Perm (Fin (p + M))}
    (h : sigma0ConjRel p M g1 g2) : ci g1 = ci g2 := by
  obtain ⟨k, -, hk⟩ := h
  rw [hk, ci_conj]

#print axioms sigma0ConjRel_refl
#print axioms sigma0ConjRel_symm
#print axioms sigma0ConjRel_trans
#print axioms ci_const_sigma0ConjRel

end CongruenceTheory
