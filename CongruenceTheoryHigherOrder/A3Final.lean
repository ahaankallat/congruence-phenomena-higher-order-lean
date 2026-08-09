import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.Perm
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.FullCycleConnected
import CongruenceTheoryHigherOrder.CiFullCycle
import CongruenceTheoryHigherOrder.CiConverse
import CongruenceTheoryHigherOrder.FullCycleCount

/-!
**(A3) fully assembled**: "the coefficient of `X_{jp}` in `K_j(p)` is `(jp-1)!`," combining every
building block proved so far — `K_eq_Gfun_top`, `piOf_eq_top_of_isCycle_of_support_eq_univ`,
`ci_eq_X_of_isCycle_of_support_eq_univ`, `isCycle_and_support_eq_univ_of_ci_eq_X`, and
`card_fullCycle` — via a `Fin r × Fin q ≃ Fin (r*q)` transport of the full-cycle count.
-/

namespace CongruenceTheory

open Equiv MvPolynomial

open scoped Classical

/-- `ci g` is always a bare monomial with coefficient `1`. -/
theorem ci_eq_monomial_toFinsupp {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    ci g = monomial (Finsupp.single 1 (Fintype.card α - g.cycleType.sum) +
      g.cycleType.toFinsupp) (1 : ℤ) := by
  unfold ci
  rw [multiset_map_X_prod_eq_monomial,
    show (X 1 : MvPolynomial ℕ ℤ) ^ (Fintype.card α - g.cycleType.sum) =
      monomial (Finsupp.single 1 (Fintype.card α - g.cycleType.sum)) (1 : ℤ) from
      X_pow_eq_monomial, monomial_mul, mul_one]

/-- The coefficient of `X n` in `ci g` is `1` if `ci g = X n`, else `0`. -/
theorem coeff_X_ci_eq_ite {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) (n : ℕ) :
    coeff (Finsupp.single n 1) (ci g) = if ci g = X n then 1 else 0 := by
  have hmono := ci_eq_monomial_toFinsupp g
  conv_lhs => rw [hmono, coeff_monomial]
  by_cases hD : Finsupp.single 1 (Fintype.card α - g.cycleType.sum) + g.cycleType.toFinsupp =
      Finsupp.single n 1
  · rw [if_pos hD]
    have hciX : ci g = X n := by rw [hmono, hD]; rfl
    rw [if_pos hciX]
  · rw [if_neg hD]
    have hciX : ci g ≠ X n := by
      intro hcontra
      apply hD
      have hXmono : (X n : MvPolynomial ℕ ℤ) = monomial (Finsupp.single n 1) (1 : ℤ) := rfl
      rw [hmono, hXmono] at hcontra
      exact monomial_left_injective (one_ne_zero) hcontra
    rw [if_neg hciX]

/-- Support transports along an `Equiv` conjugation. -/
theorem support_permCongr {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
    (e : α ≃ β) (g : Equiv.Perm α) :
    (e.permCongr g).support = g.support.map e.toEmbedding := by
  apply Finset.ext
  intro x
  rw [Finset.mem_map, Equiv.Perm.mem_support]
  constructor
  · intro hne
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Equiv.Perm.mem_support]
    intro hcontra
    apply hne
    show e (g (e.symm x)) = x
    rw [hcontra, Equiv.apply_symm_apply]
  · rintro ⟨y, hy, rfl⟩
    rw [Equiv.Perm.mem_support] at hy
    show e (g (e.symm (e y))) ≠ e y
    rw [Equiv.symm_apply_apply]
    exact fun hc => hy (e.injective hc)

theorem permCongr_zpow {α β : Type*} (e : α ≃ β) (g : Equiv.Perm α) (n : ℤ) :
    e.permCongr (g ^ n) = (e.permCongr g) ^ n :=
  map_zpow (e.permCongrHom) g n

theorem permCongr_zpow_apply {α β : Type*} (e : α ≃ β) (g : Equiv.Perm α) (n : ℤ) (x : α) :
    ((e.permCongr g) ^ n) (e x) = e ((g ^ n) x) := by
  rw [← permCongr_zpow]
  show e ((g ^ n) (e.symm (e x))) = e ((g ^ n) x)
  rw [Equiv.symm_apply_apply]

theorem sameCycle_permCongr_iff {α β : Type*} (e : α ≃ β) (g : Equiv.Perm α) (x y : α) :
    (e.permCongr g).SameCycle (e x) (e y) ↔ g.SameCycle x y := by
  constructor
  · rintro ⟨n, hn⟩
    rw [permCongr_zpow_apply] at hn
    exact ⟨n, e.injective hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [permCongr_zpow_apply, hn]⟩

theorem isCycle_permCongr_iff {α β : Type*} (e : α ≃ β) (g : Equiv.Perm α) :
    (e.permCongr g).IsCycle ↔ g.IsCycle := by
  constructor
  · rintro ⟨x', hx', hy'⟩
    refine ⟨e.symm x', ?_, ?_⟩
    · intro hcontra
      apply hx'
      show e (g (e.symm x')) = x'
      rw [hcontra, Equiv.apply_symm_apply]
    · intro y hy
      have hy'' : e.permCongr g (e y) ≠ e y := by
        show e (g (e.symm (e y))) ≠ e y
        rw [Equiv.symm_apply_apply]
        exact fun hc => hy (e.injective hc)
      have hsc : (e.permCongr g).SameCycle x' (e y) := hy' hy''
      rw [show x' = e (e.symm x') from (Equiv.apply_symm_apply e x').symm] at hsc
      exact (sameCycle_permCongr_iff e g (e.symm x') y).mp hsc
  · rintro ⟨x, hx, hy⟩
    refine ⟨e x, ?_, ?_⟩
    · show e (g (e.symm (e x))) ≠ e x
      rw [Equiv.symm_apply_apply]
      exact fun hc => hx (e.injective hc)
    · intro y' hy'
      obtain ⟨y, rfl⟩ := e.surjective y'
      have hy'' : g y ≠ y := by
        intro hc
        apply hy'
        show e (g (e.symm (e y))) = e y
        rw [Equiv.symm_apply_apply, hc]
      exact (sameCycle_permCongr_iff e g x y).mpr (hy hy'')

theorem permCongr_symm_permCongr {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α) :
    e.symm.permCongr (e.permCongr p) = p := by
  have h1 : (e.permCongrHom).symm = e.symm.permCongrHom := Equiv.permCongrHom_symm e
  have h2 := (e.permCongrHom).symm_apply_apply p
  rw [h1] at h2
  exact h2

/-- **The count of full cycles transports along `Fin r × Fin q ≃ Fin (r*q)`.** -/
theorem card_fullCycle_prod (r q : ℕ) :
    Fintype.card {g : Equiv.Perm (Fin r × Fin q) // g.IsCycle ∧ g.support = Finset.univ} =
      Fintype.card {g : Equiv.Perm (Fin (r * q)) // g.IsCycle ∧ g.support = Finset.univ} := by
  set e := finProdFinEquiv (m := r) (n := q) with he_def
  have hforward : ∀ g : Equiv.Perm (Fin r × Fin q), g.IsCycle → g.support = Finset.univ →
      (e.permCongr g).IsCycle ∧ (e.permCongr g).support = Finset.univ := by
    intro g hcyc hsupp
    refine ⟨(isCycle_permCongr_iff e g).mpr hcyc, ?_⟩
    rw [support_permCongr, hsupp]
    apply Finset.eq_univ_of_card
    rw [Finset.card_map, Finset.card_univ]
    simp [Fintype.card_prod]
  have hbackward : ∀ g : Equiv.Perm (Fin (r * q)), g.IsCycle → g.support = Finset.univ →
      (e.symm.permCongr g).IsCycle ∧ (e.symm.permCongr g).support = Finset.univ := by
    intro g hcyc hsupp
    refine ⟨(isCycle_permCongr_iff e.symm g).mpr hcyc, ?_⟩
    rw [support_permCongr, hsupp]
    apply Finset.eq_univ_of_card
    rw [Finset.card_map, Finset.card_univ]
    simp [Fintype.card_prod]
  apply Fintype.card_congr
  refine ⟨fun t => ⟨e.permCongr t.1, hforward t.1 t.2.1 t.2.2⟩,
    fun t => ⟨e.symm.permCongr t.1, hbackward t.1 t.2.1 t.2.2⟩, ?_, ?_⟩
  · intro t
    apply Subtype.ext
    exact permCongr_symm_permCongr e t.1
  · intro t
    apply Subtype.ext
    have := permCongr_symm_permCongr e.symm t.1
    rwa [Equiv.symm_symm] at this

/-- **(A3), fully assembled**: the coefficient of `X_{jp}` in `K_j(p)` is `(jp-1)!`. -/
theorem A3_coeff_eq_factorial {r q : ℕ} (hn : 2 ≤ r * q) :
    coeff (Finsupp.single (r * q) 1) (K r q) = (Nat.factorial (r * q - 1) : ℤ) := by
  rw [K_eq_Gfun_top]
  unfold Gfun
  rw [coeff_sum]
  have hstep : ∀ g ∈ (Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter
      (fun g => piOf g = (⊤ : PartLat r)),
      coeff (Finsupp.single (r * q) 1) (ci g) =
        if (g.IsCycle ∧ g.support = Finset.univ) then (1 : ℤ) else 0 := by
    intro g _
    rw [coeff_X_ci_eq_ite]
    by_cases hfc : g.IsCycle ∧ g.support = Finset.univ
    · rw [if_pos (ci_eq_X_of_isCycle_of_support_eq_univ hfc.1 hfc.2), if_pos hfc]
    · rw [if_neg (fun heq => hfc (isCycle_and_support_eq_univ_of_ci_eq_X hn heq)), if_neg hfc]
  rw [Finset.sum_congr rfl hstep, Finset.sum_boole]
  have hsub : ((Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter
      (fun g => piOf g = (⊤ : PartLat r))).filter (fun g => g.IsCycle ∧ g.support = Finset.univ) =
      (Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter
        (fun g => g.IsCycle ∧ g.support = Finset.univ) := by
    apply Finset.ext
    intro g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hfc⟩; exact hfc
    · intro hfc
      exact ⟨piOf_eq_top_of_isCycle_of_support_eq_univ hfc.1 hfc.2, hfc⟩
  rw [hsub]
  have hcardeq : ((Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter
      (fun g => g.IsCycle ∧ g.support = Finset.univ)).card =
      Fintype.card {g : Equiv.Perm (Fin r × Fin q) // g.IsCycle ∧ g.support = Finset.univ} := by
    rw [Fintype.card_subtype]
  rw [hcardeq, card_fullCycle_prod]
  obtain ⟨m, hm⟩ : ∃ m, r * q = m + 1 := ⟨r * q - 1, by omega⟩
  rw [hm]
  have hm1 : 1 ≤ m := by omega
  rw [card_fullCycle m hm1]
  congr 1

#print axioms A3_coeff_eq_factorial

end CongruenceTheory
