import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexFiberPermHom
import CongruenceTheoryHigherOrder.A2aCutVertexBranchConfinement

/-!
**The fiberwise attachment homomorphism** (replacing the componentwise-peeling plan): after
`fiberHom`'s single-shot Lagrange step accounts for the `m!` factor of a `compType`-fiber `S`, its
kernel `KerFiberAmbient` fixes every component of `S` setwise. Chaining
`factorization_card_le_component_fixed_bound` across `S` from here, one component at a time, would
be *valid* but too weak: each peel pays `1+v_p((a-1)!)` for a component of attachment count `a`,
while the manuscript's target needs exactly `v_p(a!) = v_p((a-1)!)+v_p(a)`, a full unit tighter
whenever `p∤a` (e.g. `p=2,a=3`: `1+v_2(2!)=2` but `v_2(3!)=1`). The fix is to pay for *all* of `S`'s
attachment orbits at once via a single Lagrange step, exactly mirroring `fiberHom` itself: build a
`MonoidHom` from `KerFiberAmbient` into `∀ c:S, Equiv.Perm ↥(AmbientC0Attach g u c.1)` (well-defined
since a component fixed setwise also fixes its attachment set setwise, by
`ambientAttach_image_eq_of_component_fixed`), whose range divides `∏_{c∈S}(AmbientC0Attach(c).card)!`
by Lagrange directly — no orbit, no log-factorial, no telescoping loss anywhere.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **`fiberHom`'s kernel, re-embedded as a genuine `Subgroup (Equiv.Perm Ω)`.** -/
noncomputable def KerFiberAmbient {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S) :
    Subgroup (Equiv.Perm Ω) :=
  (MonoidHom.ker (fiberHom hpart hne hcent' hperm' hblock_u' S hSinv)).map A'.subtype

theorem card_kerFiberAmbient {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S) :
    Nat.card (KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv) =
      Nat.card (MonoidHom.ker (fiberHom hpart hne hcent' hperm' hblock_u' S hSinv)) := by
  unfold KerFiberAmbient
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ A'.subtype_injective).symm.toEquiv

theorem kerFiberAmbient_le_A' {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S) :
    KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv ≤ A' := by
  unfold KerFiberAmbient
  rintro ψ ⟨φ, -, rfl⟩
  exact φ.2

/-- Elements of `KerFiberAmbient` fix every component of `S` setwise. -/
theorem kerFiberAmbient_fixes_components {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S)
    (ψ : Equiv.Perm Ω) (hψ : ψ ∈ KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv)
    {c : BlockComponent V g u} (hc : c ∈ S) : componentPermOfMem hpart hne hcent' hperm'
      (kerFiberAmbient_le_A' hpart hne hcent' hperm' hblock_u' S hSinv hψ)
      (hblock_u' ψ (kerFiberAmbient_le_A' hpart hne hcent' hperm' hblock_u' S hSinv hψ)) c = c := by
  obtain ⟨φ, hφker, rfl⟩ := hψ
  have heq1 : fiberHom hpart hne hcent' hperm' hblock_u' S hSinv φ = 1 := hφker
  have happly := congrArg (fun e : Equiv.Perm ↥S => (e ⟨c, hc⟩ : ↥S)) heq1
  simp only [Equiv.Perm.one_apply] at happly
  have hcoe : (fiberHom hpart hne hcent' hperm' hblock_u' S hSinv φ ⟨c, hc⟩ : ↥S).1 =
      componentHom hpart hne hcent' hperm' hblock_u' φ c := rfl
  have hcoe2 : componentHom hpart hne hcent' hperm' hblock_u' φ c =
      componentPermOfMem hpart hne hcent' hperm' φ.2 (hblock_u' φ.1 φ.2) c := rfl
  have := congrArg Subtype.val happly
  rw [hcoe, hcoe2] at this
  exact this

/-- **The fiberwise attachment homomorphism.** -/
noncomputable def attachmentFiberHom {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S) :
    KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv →*
      ∀ c : (S : Finset (BlockComponent V g u)), Equiv.Perm ↥(AmbientC0Attach g u c.1) where
  toFun φ c := Equiv.Perm.subtypePerm φ.1 (by
    intro x
    set hcentKF := fun ψ (hψ : ψ ∈ KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv) =>
      hcent' ψ (kerFiberAmbient_le_A' hpart hne hcent' hperm' hblock_u' S hSinv hψ)
      with hcentKF_def
    set hpermKF := fun ψ (hψ : ψ ∈ KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv) =>
      hperm' ψ (kerFiberAmbient_le_A' hpart hne hcent' hperm' hblock_u' S hSinv hψ)
      with hpermKF_def
    set hblockKF := fun ψ (hψ : ψ ∈ KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv) =>
      hblock_u' ψ (kerFiberAmbient_le_A' hpart hne hcent' hperm' hblock_u' S hSinv hψ)
      with hblockKF_def
    have hfixc : ∀ (ψ : Equiv.Perm Ω)
        (hψ : ψ ∈ KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv),
        componentPermOfMem hpart hne hcentKF hpermKF hψ (hblockKF ψ hψ) c.1 = c.1 := by
      intro ψ hψ
      rw [hcentKF_def, hpermKF_def, hblockKF_def]
      exact kerFiberAmbient_fixes_components hpart hne hcent' hperm' hblock_u' S hSinv ψ hψ c.2
    have himg := ambientAttach_image_eq_of_component_fixed hpart hne hcentKF hpermKF hblockKF
      hfixc φ.2
    constructor
    · intro hxin
      have hmem : φ.1 x ∈ (AmbientC0Attach g u c.1).image φ.1 := by rw [himg]; exact hxin
      obtain ⟨x', hx'mem, hx'eq⟩ := Finset.mem_image.mp hmem
      rwa [φ.1.injective hx'eq] at hx'mem
    · intro hxin
      rw [← himg]
      exact Finset.mem_image_of_mem φ.1 hxin)
  map_one' := by
    funext c
    apply Equiv.ext
    intro x
    apply Subtype.ext
    simp [Equiv.Perm.subtypePerm_apply]
  map_mul' a b := by
    funext c
    apply Equiv.ext
    intro x
    apply Subtype.ext
    simp only [Equiv.Perm.subtypePerm_apply]
    show (↑(a * b) : Equiv.Perm Ω) x.1 = (↑a : Equiv.Perm Ω) ((↑b : Equiv.Perm Ω) x.1)
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply]

/-- **The attachment-fiber divisibility fact, single-shot via Lagrange.** -/
theorem card_dvd_attachmentFiberHom_range_prod {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S) :
    Nat.card (MonoidHom.range (attachmentFiberHom hpart hne hcent' hperm' hblock_u' S hSinv)) ∣
      ∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card := by
  have hdvd : Nat.card
      (MonoidHom.range (attachmentFiberHom hpart hne hcent' hperm' hblock_u' S hSinv)) ∣
      Nat.card (∀ c : (S : Finset (BlockComponent V g u)), Equiv.Perm ↥(AmbientC0Attach g u c.1)) :=
    Subgroup.card_subgroup_dvd_card _
  have heq : Nat.card (∀ c : (S : Finset (BlockComponent V g u)),
      Equiv.Perm ↥(AmbientC0Attach g u c.1)) =
      ∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card := by
    rw [Nat.card_pi, ← Finset.prod_coe_sort S (fun c => Nat.factorial (AmbientC0Attach g u c).card)]
    apply Finset.prod_congr rfl
    intro c _
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe]
  rwa [heq] at hdvd
