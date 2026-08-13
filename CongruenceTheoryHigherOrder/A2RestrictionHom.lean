import Mathlib
import CongruenceTheoryHigherOrder.A2MixedPoints

/-!
**`thm:atomic-connected-content`'s (A2): the restriction homomorphism.** Given a centralizing,
block-permuting subgroup `A ≤ \operatorname{Perm}(\Omega)$ and `\sigma`, `A` acts on the set of
mixed points (`A2MixedPoints.lean`'s `IsMixed`) via `subtypePerm`, giving a genuine `MonoidHom`
`restrictToMixed : A →* \operatorname{Perm}\{x // \mathrm{IsMixed}\ V\ \sigma\ x\}$. The first
isomorphism theorem then gives the *exact* factorization `|A| = |\mathrm{range}|\cdot|\mathrm{ker}|`
that the rest of (A2)'s argument bounds each factor of.
-/

namespace CongruenceTheory

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
  {V : ι → Finset Ω} {A : Subgroup (Equiv.Perm Ω)} {σ : Equiv.Perm Ω}

/-- **The mixedness-invariance hypothesis `subtypePerm` needs**, for a single `φ ∈ A`. -/
theorem isMixed_apply_iff (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (φ : Equiv.Perm Ω) (hφ : φ ∈ A) (x : Ω) :
    IsMixed V σ (φ x) ↔ IsMixed V σ x := by
  constructor
  · intro hx'
    have h := isMixed_apply_of_commute_of_permBlocks hpart hne hperm hcent
      (A.inv_mem hφ) hx'
    simpa using h
  · intro hx
    exact isMixed_apply_of_commute_of_permBlocks hpart hne hperm hcent hφ hx

/-- **`A` acting on the mixed points.** -/
noncomputable def restrictToMixed (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ) :
    A →* Equiv.Perm {x // IsMixed V σ x} where
  toFun φ := Equiv.Perm.subtypePerm (φ : Equiv.Perm Ω)
    (isMixed_apply_iff hpart hne hperm hcent φ.1 φ.2)
  map_one' := by
    apply Equiv.ext; intro x; apply Subtype.ext
    simp [Equiv.Perm.subtypePerm_apply]
  map_mul' := by
    intro φ ψ
    apply Equiv.ext; intro x; apply Subtype.ext
    rfl

@[simp]
theorem restrictToMixed_apply (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (φ : A) (x : {x // IsMixed V σ x}) :
    (restrictToMixed hpart hne hperm hcent φ x : Ω) = (φ : Equiv.Perm Ω) x := rfl

/-- **The exact `|A| = |range| \cdot |ker|` factorization**, via the first isomorphism theorem. -/
theorem card_eq_card_range_mul_card_ker (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ) :
    Nat.card A = Nat.card (MonoidHom.range (restrictToMixed hpart hne hperm hcent)) *
      Nat.card (MonoidHom.ker (restrictToMixed hpart hne hperm hcent)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MonoidHom.ker (restrictToMixed hpart hne hperm hcent)),
    Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (restrictToMixed hpart hne hperm hcent)).toEquiv]

/-- **Kernel membership**: `\varphi` fixes every mixed point pointwise. -/
theorem mem_ker_restrictToMixed (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ) (φ : A) :
    φ ∈ MonoidHom.ker (restrictToMixed hpart hne hperm hcent) ↔
      ∀ x : Ω, IsMixed V σ x → (φ : Equiv.Perm Ω) x = x := by
  constructor
  · intro hφ x hx
    have h := congrArg
      (fun e : Equiv.Perm {x // IsMixed V σ x} => (e ⟨x, hx⟩ : {x // IsMixed V σ x})) hφ
    simpa [restrictToMixed] using h
  · intro hfix
    apply Equiv.ext
    intro x
    apply Subtype.ext
    simp only [restrictToMixed, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.Perm.subtypePerm_apply]
    exact hfix x.1 x.2

#print axioms isMixed_apply_iff
#print axioms restrictToMixed_apply
#print axioms card_eq_card_range_mul_card_ker
#print axioms mem_ker_restrictToMixed

end CongruenceTheory
