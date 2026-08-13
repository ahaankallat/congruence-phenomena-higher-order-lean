import Mathlib
import CongruenceTheoryHigherOrder.A2RestrictionHom

/-!
**`thm:atomic-connected-content`'s (A2): the kernel bound.** An element of
`\ker(\mathrm{restrictToMixed})` fixes every mixed point pointwise (`A2RestrictionHom.lean`'s
`mem_ker_restrictToMixed`). Provided every block contains at least one mixed point, such an
element must therefore fix every block *setwise* (a mixed witness point pins the block), hence
acts only on each block's *non-mixed* points — giving an injective homomorphism from the kernel
into `\prod_i\operatorname{Perm}(V_i\smallsetminus\mathrm{Mixed})`, and so, by Lagrange,
`|\ker|\mid\prod_i(R_i-M_i)!` where `M_i` is the number of mixed points in block `i`.
-/

namespace CongruenceTheory

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
  {V : ι → Finset Ω} {A : Subgroup (Equiv.Perm Ω)} {σ : Equiv.Perm Ω}

open scoped Classical in
/-- **The non-mixed points of block `i`.** -/
noncomputable def NonMixed (V : ι → Finset Ω) (σ : Equiv.Perm Ω) (i : ι) : Finset Ω :=
  (V i).filter (fun x => ¬ IsMixed V σ x)

open scoped Classical in
theorem mem_NonMixed {V : ι → Finset Ω} {σ : Equiv.Perm Ω} {i : ι} {x : Ω} :
    x ∈ NonMixed V σ i ↔ x ∈ V i ∧ ¬ IsMixed V σ x := by
  simp [NonMixed]

/-- **Kernel elements fix every block setwise**, given a mixed witness point in each block. -/
theorem image_eq_of_mem_ker (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (hMixedNe : ∀ i, ∃ x ∈ V i, IsMixed V σ x)
    {φ : A} (hφ : φ ∈ MonoidHom.ker (restrictToMixed hpart hne hperm hcent)) (i : ι) :
    (V i).image (φ : Equiv.Perm Ω) = V i := by
  obtain ⟨x₀, hx₀mem, hx₀mixed⟩ := hMixedNe i
  obtain ⟨j, hj⟩ := hperm φ.1 φ.2 i
  have hfix : (φ : Equiv.Perm Ω) x₀ = x₀ :=
    (mem_ker_restrictToMixed hpart hne hperm hcent φ).mp hφ x₀ hx₀mixed
  have hx₀in : (φ : Equiv.Perm Ω) x₀ ∈ (V i).image (φ : Equiv.Perm Ω) :=
    Finset.mem_image_of_mem _ hx₀mem
  rw [hfix, hj] at hx₀in
  obtain ⟨i0, hi0, huniq⟩ := hpart x₀
  have hij : i = j := (huniq i hx₀mem).trans (huniq j hx₀in).symm
  rw [hij] at hj ⊢
  exact hj

/-- **Kernel elements permute the non-mixed points of each block among themselves.** -/
theorem restrict_iff (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (hMixedNe : ∀ i, ∃ x ∈ V i, IsMixed V σ x)
    {φ : A} (hφ : φ ∈ MonoidHom.ker (restrictToMixed hpart hne hperm hcent)) (i : ι) (x : Ω) :
    (φ : Equiv.Perm Ω) x ∈ NonMixed V σ i ↔ x ∈ NonMixed V σ i := by
  rw [mem_NonMixed, mem_NonMixed]
  have hblock := image_eq_of_mem_ker hpart hne hperm hcent hMixedNe hφ i
  have hmiff : IsMixed V σ ((φ : Equiv.Perm Ω) x) ↔ IsMixed V σ x :=
    isMixed_apply_iff hpart hne hperm hcent (φ : Equiv.Perm Ω) φ.2 x
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨x', hx'mem, hx'eq⟩ := Finset.mem_image.mp (hblock ▸ h1)
    have hxx' : x' = x := φ.1.injective hx'eq
    exact ⟨hxx' ▸ hx'mem, fun hmx => h2 (hmiff.mpr hmx)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hblock ▸ Finset.mem_image_of_mem _ h1, fun hmphi => h2 (hmiff.mp hmphi)⟩

/-- **The kernel, acting on the non-mixed points of each block.** -/
noncomputable def kernelToProd (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (hMixedNe : ∀ i, ∃ x ∈ V i, IsMixed V σ x) :
    ↥(MonoidHom.ker (restrictToMixed hpart hne hperm hcent)) →*
      ∀ i, Equiv.Perm ↥(NonMixed V σ i) where
  toFun φ := fun i => Equiv.Perm.subtypePerm (φ.1 : Equiv.Perm Ω)
    (restrict_iff hpart hne hperm hcent hMixedNe φ.2 i)
  map_one' := by
    funext i; apply Equiv.ext; intro x; apply Subtype.ext; rfl
  map_mul' := by
    intro φ ψ
    funext i; apply Equiv.ext; intro x; apply Subtype.ext; rfl

theorem kernelToProd_injective (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (hMixedNe : ∀ i, ∃ x ∈ V i, IsMixed V σ x) :
    Function.Injective (kernelToProd hpart hne hperm hcent hMixedNe) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ1
  apply Subtype.ext; apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨i, hi, -⟩ := hpart x
  by_cases hmx : IsMixed V σ x
  · exact (mem_ker_restrictToMixed hpart hne hperm hcent φ.1).mp φ.2 x hmx
  · have hxnm : x ∈ NonMixed V σ i := mem_NonMixed.mpr ⟨hi, hmx⟩
    have h := congrArg
      (fun e : ∀ i, Equiv.Perm ↥(NonMixed V σ i) => (e i ⟨x, hxnm⟩ : {y // y ∈ NonMixed V σ i}))
      hφ1
    simpa [kernelToProd] using h

/-- **(A2)'s kernel bound**: `|\ker(\mathrm{restrictToMixed})| \mid \prod_i (R_i - M_i)!`. -/
theorem card_ker_dvd_prod_factorial (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (hMixedNe : ∀ i, ∃ x ∈ V i, IsMixed V σ x) :
    Nat.card (MonoidHom.ker (restrictToMixed hpart hne hperm hcent)) ∣
      ∏ i, Nat.factorial (NonMixed V σ i).card := by
  have hinj := kernelToProd_injective hpart hne hperm hcent hMixedNe
  have hcard2 : Nat.card ↥(MonoidHom.ker (restrictToMixed hpart hne hperm hcent)) =
      Nat.card (MonoidHom.range (kernelToProd hpart hne hperm hcent hMixedNe)) *
        Nat.card (MonoidHom.ker (kernelToProd hpart hne hperm hcent hMixedNe)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MonoidHom.ker (kernelToProd hpart hne hperm hcent hMixedNe)),
      Nat.card_congr (QuotientGroup.quotientKerEquivRange
        (kernelToProd hpart hne hperm hcent hMixedNe)).toEquiv]
  have hkertriv : MonoidHom.ker (kernelToProd hpart hne hperm hcent hMixedNe) = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr hinj
  rw [hkertriv, Subgroup.card_bot, mul_one] at hcard2
  rw [hcard2]
  have hdvd : Nat.card (MonoidHom.range (kernelToProd hpart hne hperm hcent hMixedNe)) ∣
      Nat.card (∀ i, Equiv.Perm ↥(NonMixed V σ i)) :=
    Subgroup.card_subgroup_dvd_card _
  have heq : Nat.card (∀ i, Equiv.Perm ↥(NonMixed V σ i)) =
      ∏ i, Nat.factorial (NonMixed V σ i).card := by
    rw [Nat.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe]
  rwa [heq] at hdvd

#print axioms mem_NonMixed
#print axioms image_eq_of_mem_ker
#print axioms restrict_iff
#print axioms kernelToProd_injective
#print axioms card_ker_dvd_prod_factorial

end CongruenceTheory
