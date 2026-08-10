import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexIslandFiberInduction

/-!
**Assembling the four pieces into one per-`compType`-fiber divisibility bound.** Chains
`fiberHom` (the `m!` factor), `attachmentFiberHom` (the `(a!)^m` factor), and
`key_induction_island_dvd` (the `B^m` factor) through two more kernel re-embeddings
(`KerAttachmentAmbient`, mirroring `KerFiberAmbient`), giving, for a single `compType`-fiber `S`,
`Nat.card A' ∣ S.card! · ∏_{c∈S}(AmbientC0Attach(c).card)! · ∏_{c∈S}(island-product(c))` — pure
wiring of already-proved pieces, no new mathematics.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **`attachmentFiberHom`'s kernel, re-embedded as a genuine `Subgroup (Equiv.Perm Ω)`.** -/
noncomputable def KerAttachmentAmbient {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S) :
    Subgroup (Equiv.Perm Ω) :=
  (MonoidHom.ker (attachmentFiberHom hpart hne hcent' hperm' hblock_u' S hSinv)).map
    (KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv).subtype

theorem card_kerAttachmentAmbient {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S) :
    Nat.card (KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv) =
      Nat.card (MonoidHom.ker (attachmentFiberHom hpart hne hcent' hperm' hblock_u' S hSinv)) := by
  unfold KerAttachmentAmbient
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv).subtype_injective).symm.toEquiv

theorem kerAttachmentAmbient_le_kerFiberAmbient {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S) :
    KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv ≤
      KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv := by
  unfold KerAttachmentAmbient
  rintro ψ ⟨φ, -, rfl⟩
  exact φ.2

/-- Elements of `KerAttachmentAmbient` fix every attachment point of every component of `S`
pointwise. -/
theorem kerAttachmentAmbient_fixes_attach {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S)
    (ψ : Equiv.Perm Ω) (hψ : ψ ∈ KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv)
    {c : BlockComponent V g u} (hc : c ∈ S) {x : Ω} (hx : x ∈ AmbientC0Attach g u c) :
    ψ x = x := by
  obtain ⟨φ, hφker, rfl⟩ := hψ
  have heq1 := congrFun hφker (⟨c, hc⟩ : (S : Finset (BlockComponent V g u)))
  have happly := congrArg
    (fun e : Equiv.Perm ↥(AmbientC0Attach g u c) => (e ⟨x, hx⟩ : ↥(AmbientC0Attach g u c))) heq1
  simp only [Pi.one_apply, Equiv.Perm.one_apply] at happly
  have hcoe : ((attachmentFiberHom hpart hne hcent' hperm' hblock_u' S hSinv φ ⟨c, hc⟩)
      ⟨x, hx⟩ : Ω) = φ.1 x := rfl
  have hval := congrArg Subtype.val happly
  rw [hcoe] at hval
  exact hval

/-- **The per-`compType`-fiber divisibility bound**, chaining all four pieces. -/
theorem card_dvd_fiber_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S)
    (hne_attach : ∀ c ∈ S, (AmbientC0Attach g u c).Nonempty) :
    Nat.card A' ∣ Nat.factorial S.card *
      (∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card) *
      (∏ c ∈ S, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
        Nat.factorial ((IslandV g u c i).card - 1)) *
      Nat.card (FixIslands (KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv)
        g u S) := by
  set f1 := fiberHom hpart hne hcent' hperm' hblock_u' S hSinv with hf1def
  set f2 := attachmentFiberHom hpart hne hcent' hperm' hblock_u' S hSinv with hf2def
  have hcardA' : Nat.card A' = Nat.card (MonoidHom.range f1) * Nat.card (MonoidHom.ker f1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker f1),
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f1).toEquiv]
  have hrange1dvd : Nat.card (MonoidHom.range f1) ∣ Nat.factorial S.card :=
    card_dvd_fiberHom_range_factorial hpart hne hcent' hperm' hblock_u' S hSinv
  have hker1eq : Nat.card (MonoidHom.ker f1) =
      Nat.card (KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv) :=
    (card_kerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv).symm
  have hcardKFA : Nat.card (KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv) =
      Nat.card (MonoidHom.range f2) * Nat.card (MonoidHom.ker f2) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker f2),
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f2).toEquiv]
  have hrange2dvd : Nat.card (MonoidHom.range f2) ∣ ∏ c ∈ S, Nat.factorial
      (AmbientC0Attach g u c).card :=
    card_dvd_attachmentFiberHom_range_prod hpart hne hcent' hperm' hblock_u' S hSinv
  have hker2eq : Nat.card (MonoidHom.ker f2) =
      Nat.card (KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv) :=
    (card_kerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv).symm
  have hKAle : KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv ≤ A' :=
    (kerAttachmentAmbient_le_kerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv).trans
      (kerFiberAmbient_le_A' hpart hne hcent' hperm' hblock_u' S hSinv)
  have hcentKA : ∀ φ ∈ KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv,
      Commute φ g := fun φ hφ => hcent' φ (hKAle hφ)
  have hpermKA : ∀ φ ∈ KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv,
      ∀ i, ∃ j, (V i).image φ = V j := fun φ hφ => hperm' φ (hKAle hφ)
  have hblockKA : ∀ φ ∈ KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv,
      (V u).image φ = V u := fun φ hφ => hblock_u' φ (hKAle hφ)
  have hfixattachKA : ∀ φ ∈ KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv,
      ∀ c ∈ S, ∀ x ∈ AmbientC0Attach g u c, φ x = x :=
    fun φ hφ c hc x hx => kerAttachmentAmbient_fixes_attach hpart hne hcent' hperm' hblock_u' S
      hSinv φ hφ hc hx
  have hislanddvd := key_induction_island_dvd hpart hne S.card S le_rfl
    (KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv) hcentKA hpermKA hblockKA
    hfixattachKA hne_attach
  calc Nat.card A' = Nat.card (MonoidHom.range f1) * Nat.card (MonoidHom.ker f1) := hcardA'
    _ ∣ Nat.factorial S.card * Nat.card (MonoidHom.ker f1) :=
        mul_dvd_mul_right hrange1dvd _
    _ = Nat.factorial S.card * Nat.card (KerFiberAmbient hpart hne hcent' hperm' hblock_u' S
        hSinv) := by rw [hker1eq]
    _ = Nat.factorial S.card * (Nat.card (MonoidHom.range f2) * Nat.card (MonoidHom.ker f2)) := by
        rw [hcardKFA]
    _ ∣ Nat.factorial S.card * ((∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card) *
          Nat.card (MonoidHom.ker f2)) :=
        mul_dvd_mul_left _ (mul_dvd_mul_right hrange2dvd _)
    _ = Nat.factorial S.card * ((∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card) *
          Nat.card (KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv)) := by
        rw [hker2eq]
    _ ∣ Nat.factorial S.card * ((∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card) *
          ((∏ c ∈ S, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1)) *
            Nat.card (FixIslands (KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv)
              g u S))) :=
        mul_dvd_mul_left _ (mul_dvd_mul_left _ hislanddvd)
    _ = Nat.factorial S.card * (∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card) *
          (∏ c ∈ S, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
            Nat.factorial ((IslandV g u c i).card - 1)) *
          Nat.card (FixIslands (KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv)
            g u S) := by ring
