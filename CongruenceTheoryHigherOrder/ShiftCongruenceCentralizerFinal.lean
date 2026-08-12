import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.ShiftCongruenceSetup
import CongruenceTheoryHigherOrder.ShiftCongruenceOrbit
import CongruenceTheoryHigherOrder.ShiftCongruenceOrbitSize
import CongruenceTheoryHigherOrder.ShiftCongruenceCentralizerSum

/-!
**`thm:complete-prime-local`(iii)'s `(A10)` shift congruence: the centralizer sum,
assembled.** The map `(k,\tau)\mapsto\sigma_0^k\cdot\tau'` is a bijection from
`\text{Fin }p\times\text{Perm}(\text{Fin }M)` onto the centralizer of `\sigma_0`, so the
centralizer sum equals `(\sum_{k<p}\text{ci}((\text{finRotate }p)^k))\cdot\text{Cperm}(M)`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm

variable {p M : ℕ}

open scoped Classical

/-- The centralizer-of-`\sigma_0` Finset has cardinality `p\cdot M!`. -/
theorem card_centralizer_sigma0 (hp : p.Prime) :
    (Finset.univ.filter (fun g : Equiv.Perm (Fin (p + M)) => Commute (sigma0 p M) g)).card =
      p * (Nat.factorial M) := by
  have hpred : ∀ g : Equiv.Perm (Fin (p + M)),
      g ∈ Subgroup.centralizer ({sigma0 p M} : Set (Equiv.Perm (Fin (p + M)))) ↔
        Commute (sigma0 p M) g := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact Iff.rfl
  have hcardeq : Nat.card (Subgroup.centralizer ({sigma0 p M} : Set (Equiv.Perm (Fin (p + M))))) =
      (Finset.univ.filter (fun g : Equiv.Perm (Fin (p + M)) => Commute (sigma0 p M) g)).card := by
    have hequiv : ↥(Subgroup.centralizer ({sigma0 p M} : Set (Equiv.Perm (Fin (p + M))))) ≃
        {g // g ∈ Finset.univ.filter
          (fun g : Equiv.Perm (Fin (p + M)) => Commute (sigma0 p M) g)} := by
      refine Equiv.subtypeEquivRight (fun g => ?_)
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      exact hpred g
    rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [← hcardeq, Equiv.Perm.nat_card_centralizer, cycleType_sigma0 (M := M) hp.two_le,
    Fintype.card_fin]
  simp only [Multiset.sum_singleton, Multiset.prod_singleton, Multiset.toFinset_singleton,
    Finset.prod_singleton, Multiset.count_singleton_self]
  have : p + M - p = M := by omega
  rw [this]
  ring

/-- **Injectivity** of `(k,\tau)\mapsto\sigma_0^k\cdot\tau'`. -/
theorem injOn_sigma0_pow_mul_tauExt (hp : p.Prime) :
    Function.Injective (fun x : Fin p × Equiv.Perm (Fin M) =>
      sigma0 p M ^ (x.1 : ℕ) * tauExt p M x.2) := by
  rintro ⟨k1, τ1⟩ ⟨k2, τ2⟩ heq
  simp only at heq
  have hsig : sigma0 p M ^ (k1 : ℕ) = sigma0 p M ^ (k2 : ℕ) := by
    refine Equiv.ext (fun x => ?_)
    by_cases hx : firstP p M x
    · have e1 : tauExt p M τ1 x = x := by
        apply Equiv.Perm.extendDomain_apply_not_subtype
        simp only [lastM]
        simp only [firstP] at hx
        omega
      have e2 : tauExt p M τ2 x = x := by
        apply Equiv.Perm.extendDomain_apply_not_subtype
        simp only [lastM]
        simp only [firstP] at hx
        omega
      have hxx : (sigma0 p M ^ (k1 : ℕ) * tauExt p M τ1) x =
          (sigma0 p M ^ (k2 : ℕ) * tauExt p M τ2) x := by rw [heq]
      simpa only [Equiv.Perm.mul_apply, e1, e2] using hxx
    · have e1 : (sigma0 p M ^ (k1 : ℕ)) x = x := by
        unfold sigma0
        rw [← Equiv.Perm.extendDomain_pow]
        exact Equiv.Perm.extendDomain_apply_not_subtype _ (inclEquiv p M) hx
      have e2 : (sigma0 p M ^ (k2 : ℕ)) x = x := by
        unfold sigma0
        rw [← Equiv.Perm.extendDomain_pow]
        exact Equiv.Perm.extendDomain_apply_not_subtype _ (inclEquiv p M) hx
      rw [e1, e2]
  have htau : tauExt p M τ1 = tauExt p M τ2 := by
    rw [hsig] at heq
    exact mul_left_cancel heq
  have hkeq : k1 = k2 := by
    apply Fin.ext
    exact pow_injOn_Iio_orderOf
      (Set.mem_Iio.mpr (by rw [orderOf_sigma0 (M := M) hp.two_le]; exact k1.isLt))
      (Set.mem_Iio.mpr (by rw [orderOf_sigma0 (M := M) hp.two_le]; exact k2.isLt)) hsig
  have hτeq : τ1 = τ2 := by
    have h' : Equiv.Perm.extendDomainHom (complementIncl p M) τ1 =
        Equiv.Perm.extendDomainHom (complementIncl p M) τ2 := htau
    exact Equiv.Perm.extendDomainHom_injective (complementIncl p M) h'
  exact Prod.ext hkeq hτeq

/-- The image of `(k,\tau)\mapsto\sigma_0^k\cdot\tau'` lies in the centralizer. -/
theorem sigma0_pow_mul_tauExt_mem_centralizer (τ : Equiv.Perm (Fin M)) (k : ℕ) :
    Commute (sigma0 p M) (sigma0 p M ^ k * tauExt p M τ) := by
  have h1 : Commute (sigma0 p M) (sigma0 p M ^ k) := (Commute.refl _).pow_right _
  have h2 : Commute (sigma0 p M) (tauExt p M τ) := commute_sigma0_tauExt τ
  exact h1.mul_right h2

/-- **The image equals the centralizer**: every commuting element factors as
`\sigma_0^k\cdot\tau'`. -/
theorem image_sigma0_pow_mul_tauExt_eq_centralizer (hp : p.Prime) :
    Finset.image (fun x : Fin p × Equiv.Perm (Fin M) =>
        sigma0 p M ^ (x.1 : ℕ) * tauExt p M x.2) Finset.univ =
      Finset.univ.filter (fun g : Equiv.Perm (Fin (p + M)) => Commute (sigma0 p M) g) := by
  apply Finset.eq_of_subset_of_card_le
  · intro g hg
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hg
    obtain ⟨x, hx⟩ := hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hx]
    exact sigma0_pow_mul_tauExt_mem_centralizer x.2 x.1
  · rw [card_centralizer_sigma0 hp]
    rw [Finset.card_image_of_injective _ (injOn_sigma0_pow_mul_tauExt hp)]
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_perm,
      Fintype.card_fin]

/-- **The centralizer sum**, assembled: `\sum_{g\in\text{centralizer}(\sigma_0)}\text{ci}(g) =
(\sum_{k<p}\text{ci}((\text{finRotate }p)^k))\cdot\text{Cperm}(M)`. -/
theorem ci_centralizer_sum_eq (hp : p.Prime) :
    (∑ g ∈ Finset.univ.filter (fun g : Equiv.Perm (Fin (p + M)) => Commute (sigma0 p M) g), ci g)
      = (∑ k ∈ Finset.range p, ci ((finRotate p) ^ k)) * Cperm M := by
  rw [← image_sigma0_pow_mul_tauExt_eq_centralizer hp]
  rw [Finset.sum_image (fun x _ y _ h => injOn_sigma0_pow_mul_tauExt hp h)]
  have hterm : ∀ x : Fin p × Equiv.Perm (Fin M),
      ci (sigma0 p M ^ (x.1 : ℕ) * tauExt p M x.2) = ci ((finRotate p) ^ (x.1 : ℕ)) * ci x.2 :=
    fun x => ci_sigma0_pow_mul_tauExt hp.pos x.1 x.2
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [Fintype.sum_prod_type]
  rw [show (∑ a : Fin p, ∑ b : Equiv.Perm (Fin M), ci ((finRotate p) ^ (a : ℕ)) * ci b) =
      ∑ a : Fin p, ci ((finRotate p) ^ (a : ℕ)) * ∑ b : Equiv.Perm (Fin M), ci b from
      Finset.sum_congr rfl (fun a _ => (Finset.mul_sum _ _ _).symm)]
  rw [← Finset.sum_mul]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => ci ((finRotate p) ^ k)) p

#print axioms card_centralizer_sigma0
#print axioms injOn_sigma0_pow_mul_tauExt
#print axioms sigma0_pow_mul_tauExt_mem_centralizer
#print axioms image_sigma0_pow_mul_tauExt_eq_centralizer
#print axioms ci_centralizer_sum_eq

end CongruenceTheory
