import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexFiberAttachmentHom
import CongruenceTheoryHigherOrder.A2aCutVertexC0Valuation
import CongruenceTheoryHigherOrder.A2aCutVertexIslandFactor
import CongruenceTheoryHigherOrder.A2aCutVertexKerAmbient

/-!
**The island-kernel induction, once every attachment point of a `compType`-fiber is already
fixed.** After `attachmentFiberHom`'s Lagrange step, its kernel fixes every attachment point of
every component of the fiber pointwise. From here, peeling one component's island at a time is
*lossless*: each peel is `Nat.card K = Nat.card (PtStab K p₀)` outright (`p₀` already fixed, so no
orbit-stabilizer factor at all), composed with the exact `range·ker` factorization and the already
proved `card_dvd_island_tight_bound`. No log-factorial, no value-only step anywhere in the chain,
so — unlike the componentwise plan this replaces — the induction does not lose anything peel to
peel.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The subgroup of `A` fixing every island of every component in `T` pointwise. -/
noncomputable def FixIslands {V : ι → Finset Ω} (A : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω)
    (u : ι) (T : Finset (BlockComponent V g u)) : Subgroup (Equiv.Perm Ω) :=
  A ⊓ fixingSubgroup (Equiv.Perm Ω) (⋃ c ∈ T, {x : Ω | InComponentPlus g u c x})

theorem mem_FixIslands {V : ι → Finset Ω} {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω} {u : ι}
    {T : Finset (BlockComponent V g u)} {φ : Equiv.Perm Ω} :
    φ ∈ FixIslands A g u T ↔ φ ∈ A ∧ ∀ c ∈ T, ∀ x, InComponentPlus g u c x → φ x = x := by
  simp only [FixIslands, Subgroup.mem_inf, mem_fixingSubgroup_iff, Set.mem_iUnion,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hA, hfix⟩
    exact ⟨hA, fun c hc x hx => hfix x ⟨c, hc, hx⟩⟩
  · rintro ⟨hA, hfix⟩
    exact ⟨hA, fun x ⟨c, hc, hx⟩ => hfix c hc x hx⟩

theorem fixIslands_empty {V : ι → Finset Ω} (A : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω)
    (u : ι) : FixIslands A g u (∅ : Finset (BlockComponent V g u)) = A := by
  apply le_antisymm
  · intro φ hφ; exact (mem_FixIslands.mp hφ).1
  · intro φ hφ; exact mem_FixIslands.mpr ⟨hφ, fun c hc => absurd hc (Finset.notMem_empty c)⟩

/-- **The island-kernel induction.** Given `K` fixes every attachment point of every component in
`T` pointwise, `Nat.card K` divides `(∏_{c∈T} island-product(c)) * Nat.card (FixIslands K g u T)`.
-/
theorem key_induction_island_dvd {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {g : Equiv.Perm Ω} {u : ι} :
    ∀ n : ℕ, ∀ T : Finset (BlockComponent V g u), T.card ≤ n →
    ∀ K : Subgroup (Equiv.Perm Ω), ∀ (hcentK : ∀ φ ∈ K, Commute φ g),
    ∀ (hpermK : ∀ φ ∈ K, ∀ i, ∃ j, (V i).image φ = V j),
    ∀ (hblockK : ∀ φ ∈ K, (V u).image φ = V u),
    (∀ φ ∈ K, ∀ c ∈ T, ∀ p₀ ∈ AmbientC0Attach g u c, φ p₀ = p₀) →
    (∀ c ∈ T, (AmbientC0Attach g u c).Nonempty) →
    Nat.card K ∣
      (∏ c ∈ T, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
          Nat.factorial ((IslandV g u c i).card - 1)) *
        Nat.card (FixIslands K g u T) := by
  intro n
  induction n with
  | zero =>
    intro T hTcard K hcentK hpermK hblockK _ _
    have hTempty : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hTcard)
    subst hTempty
    rw [fixIslands_empty]
    simp
  | succ n ih =>
    intro T hTcard K hcentK hpermK hblockK hfixattach hne_attach
    rcases T.eq_empty_or_nonempty with hTempty | hTne
    · subst hTempty
      rw [fixIslands_empty]
      simp
    · obtain ⟨c1, hc1T⟩ := hTne
      obtain ⟨p₀, hp₀mem⟩ := hne_attach c1 hc1T
      have hp₀u : p₀ ∈ V u := ((mem_ambientC0Attach g u c1 p₀).mp hp₀mem).1
      have hp₀reach : Reaches g u p₀ c1 := ((mem_ambientC0Attach g u c1 p₀).mp hp₀mem).2
      have hptstab_eq : PtStab K p₀ = K := by
        apply le_antisymm
        · intro φ hφ; exact (mem_PtStab.mp hφ).1
        · intro φ hφ
          exact mem_PtStab.mpr ⟨hφ, hfixattach φ hφ c1 hc1T p₀ hp₀mem⟩
      have hcardKeq : Nat.card K = Nat.card (PtStab K p₀) := by rw [hptstab_eq]
      have hrangedvd := card_dvd_island_tight_bound hpart hne hcentK hpermK hblockK hp₀u hp₀reach
      have hrangeker := card_ptStab_eq_range_mul_ker hpart hne hcentK hpermK hblockK hp₀reach
      have hKeqRangeKer : Nat.card K =
          Nat.card (MonoidHom.range (islandHom hpart hne hcentK hpermK hblockK hp₀reach)) *
            Nat.card (MonoidHom.ker (islandHom hpart hne hcentK hpermK hblockK hp₀reach)) :=
        hcardKeq.trans hrangeker
      have hcardker : Nat.card (KerAmbient hpart hne hcentK hpermK hblockK hp₀reach) =
          Nat.card (MonoidHom.ker (islandHom hpart hne hcentK hpermK hblockK hp₀reach)) :=
        card_kerAmbient hpart hne hcentK hpermK hblockK hp₀reach
      have hKle : KerAmbient hpart hne hcentK hpermK hblockK hp₀reach ≤ K :=
        kerAmbient_le_A hpart hne hcentK hpermK hblockK hp₀reach
      have hcentK' : ∀ φ ∈ KerAmbient hpart hne hcentK hpermK hblockK hp₀reach, Commute φ g :=
        fun φ hφ => hcentK φ (hKle hφ)
      have hpermK' : ∀ φ ∈ KerAmbient hpart hne hcentK hpermK hblockK hp₀reach,
          ∀ i, ∃ j, (V i).image φ = V j := fun φ hφ => hpermK φ (hKle hφ)
      have hblockK' : ∀ φ ∈ KerAmbient hpart hne hcentK hpermK hblockK hp₀reach,
          (V u).image φ = V u := fun φ hφ => hblockK φ (hKle hφ)
      have hfixattach' : ∀ φ ∈ KerAmbient hpart hne hcentK hpermK hblockK hp₀reach,
          ∀ c ∈ T.erase c1, ∀ q ∈ AmbientC0Attach g u c, φ q = q :=
        fun φ hφ c hc q hq => hfixattach φ (hKle hφ) c (Finset.mem_of_mem_erase hc) q hq
      have hne_attach' : ∀ c ∈ T.erase c1, (AmbientC0Attach g u c).Nonempty :=
        fun c hc => hne_attach c (Finset.mem_of_mem_erase hc)
      have hcardTerase : (T.erase c1).card ≤ n := by
        have := Finset.card_erase_of_mem hc1T
        omega
      have hIH := ih (T.erase c1) hcardTerase
        (KerAmbient hpart hne hcentK hpermK hblockK hp₀reach) hcentK' hpermK' hblockK'
        hfixattach' hne_attach'
      have hFixEq : FixIslands (KerAmbient hpart hne hcentK hpermK hblockK hp₀reach) g u
          (T.erase c1) = FixIslands K g u T := by
        apply le_antisymm
        · intro φ hφ
          rw [mem_FixIslands] at hφ ⊢
          refine ⟨hKle hφ.1, ?_⟩
          intro c hc x hx
          by_cases hcc1 : c = c1
          · subst hcc1
            exact kerAmbient_fixes_island hpart hne hcentK hpermK hblockK hp₀reach φ hφ.1 hx
          · exact hφ.2 c (Finset.mem_erase.mpr ⟨hcc1, hc⟩) x hx
        · intro φ hφ
          rw [mem_FixIslands] at hφ
          have hφK1 : ∀ x, InComponentPlus g u c1 x → φ x = x := fun x hx => hφ.2 c1 hc1T x hx
          have hφPtStab : φ ∈ PtStab K p₀ :=
            mem_PtStab.mpr ⟨hφ.1, hφK1 p₀ (Or.inr ⟨hp₀u, hp₀reach⟩)⟩
          have hφmemKer : φ ∈ KerAmbient hpart hne hcentK hpermK hblockK hp₀reach := by
            refine ⟨⟨φ, hφPtStab⟩, ?_, rfl⟩
            apply Equiv.ext
            intro ⟨x, hx⟩
            apply Subtype.ext
            show (islandPermOfPtStab hpart hne hcentK hpermK hblockK hp₀reach φ hφPtStab
              ⟨x, hx⟩ : Ω) = x
            rw [islandPermOfPtStab_coe]
            exact hφK1 x hx
          rw [mem_FixIslands]
          refine ⟨hφmemKer, ?_⟩
          intro c hc x hx
          exact hφ.2 c (Finset.mem_of_mem_erase hc) x hx
      rw [hFixEq] at hIH
      have hkerdvd : Nat.card K ∣
          (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
              Nat.factorial ((IslandV g u c1 i).card - 1)) *
            Nat.card (KerAmbient hpart hne hcentK hpermK hblockK hp₀reach) := by
        rw [hcardker, hKeqRangeKer]
        exact mul_dvd_mul_right hrangedvd _
      calc Nat.card K ∣
          (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
              Nat.factorial ((IslandV g u c1 i).card - 1)) *
            Nat.card (KerAmbient hpart hne hcentK hpermK hblockK hp₀reach) := hkerdvd
        _ ∣ (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
              Nat.factorial ((IslandV g u c1 i).card - 1)) *
            ((∏ c ∈ T.erase c1, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
                Nat.factorial ((IslandV g u c i).card - 1)) * Nat.card (FixIslands K g u T)) :=
            mul_dvd_mul_left _ hIH
        _ = (∏ c ∈ T, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1)) * Nat.card (FixIslands K g u T) := by
            rw [← mul_assoc, ← Finset.mul_prod_erase T
              (fun c => ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
                Nat.factorial ((IslandV g u c i).card - 1)) hc1T]
