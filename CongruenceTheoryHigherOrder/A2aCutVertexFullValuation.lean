import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexOuterFiberInduction
import CongruenceTheoryHigherOrder.A2aCutVertexC0Valuation
import CongruenceTheoryHigherOrder.A2aCutVertexBaseCase

/-!
**The final assembly: the full cut-vertex valuation bound.** Combines
`factorization_card_le_cutVertex_c0_bound` (the `C0` branch) with `key_induction_fiber_dvd`
applied to the leftover kernel from the `C0` step, over the pool `Finset.univ.erase c0` — matching
the manuscript's own strategy exactly (`R_u=a_0+Σ_τ m_τ a_τ`, i.e. `C0` first, then every other
component grouped by `compType`). The invariance fact `key_induction_fiber_dvd` needs (that the
`C0`-kernel maps `univ.erase c0` to itself) is a direct consequence of `kerAmbient_fixes_island`
plus the two small lemmas from `A2aCutVertexOuterFiberInduction.lean` — no new arithmetic.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- Elements of `KerAmbient` fix `c0` itself as a component (not just its island pointwise). -/
theorem kerAmbient_fixes_c0_component {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} (hp₀u : p₀ ∈ V u)
    {c0 : BlockComponent V g u} (hp₀reach : Reaches g u p₀ c0)
    {ψ : Equiv.Perm Ω} (hψ : ψ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach) :
    componentPermOfMem hpart hne hcent hperm (kerAmbient_le_A hpart hne hcent hperm hblock_u
      hp₀reach hψ) (hblock_u ψ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ)) c0 =
      c0 := by
  have hfixp₀ : ψ p₀ = p₀ :=
    kerAmbient_fixes_island hpart hne hcent hperm hblock_u hp₀reach ψ hψ (Or.inr ⟨hp₀u, hp₀reach⟩)
  exact componentPermOfMem_fixed_of_islandFixed hpart hne hcent hperm hblock_u
    (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ) hp₀reach hfixp₀

/-- `KerAmbient` maps `Finset.univ.erase c0` to itself. -/
theorem kerAmbient_mapsTo_compl_c0 {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} (hp₀u : p₀ ∈ V u)
    {c0 : BlockComponent V g u} (hp₀reach : Reaches g u p₀ c0) :
    ∀ φ : KerAmbient hpart hne hcent hperm hblock_u hp₀reach,
      ∀ c ∈ Finset.univ.erase c0,
        componentHom hpart hne
          (fun ψ hψ => hcent ψ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ))
          (fun ψ hψ => hperm ψ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ))
          (fun ψ hψ => hblock_u ψ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ))
          φ c ∈ Finset.univ.erase c0 := by
  intro φ c hc
  rw [Finset.mem_erase] at hc ⊢
  refine ⟨?_, Finset.mem_univ _⟩
  have heq : componentHom hpart hne
      (fun ψ hψ => hcent ψ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ))
      (fun ψ hψ => hperm ψ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ))
      (fun ψ hψ => hblock_u ψ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ)) φ c =
      componentPermOfMem hpart hne hcent hperm
        (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach φ.2)
        (hblock_u φ.1 (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach φ.2)) c := rfl
  rw [heq]
  exact componentPermOfMem_ne_of_fixed hpart hne hcent hperm hblock_u
    (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach φ.2)
    (kerAmbient_fixes_c0_component hpart hne hcent hperm hblock_u hp₀u hp₀reach φ.2) hc.1

/-- **The full cut-vertex valuation bound.** -/
theorem factorization_card_le_cutVertex_full_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {j2 : ι} (hj2u : j2 ≠ u)
    (hblock_j2 : ∀ φ ∈ A, (V j2).image φ = V j2) {p₀ : Ω} (hp₀u : p₀ ∈ V u)
    (hp₀reach : Reaches g u p₀ (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩))
    (hne_attach : ∀ c : BlockComponent V g u, (AmbientC0Attach g u c).Nonempty)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    {p : ℕ} (hp : p.Prime) :
    (Nat.card A).factorization p ≤
      1 + ((AmbientC0Attach g u
              (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).card - 1).factorial.factorization p +
        (∏ i ∈ Finset.univ.erase
              (none : IslandBlockIdx g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)),
            Nat.factorial
              ((IslandV g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩) i).card - 1)).factorization p +
        (∏ τ ∈ (Finset.univ.erase (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).image (compType g u),
          (Nat.factorial ((Finset.univ.erase (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).filter
                (fun c => compType g u c = τ)).card *
            (∏ c ∈ (Finset.univ.erase (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).filter
                (fun c => compType g u c = τ), Nat.factorial (AmbientC0Attach g u c).card) *
            (∏ c ∈ (Finset.univ.erase (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).filter
                (fun c => compType g u c = τ),
              ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
                Nat.factorial ((IslandV g u c i).card - 1)))).factorization p := by
  set c0 := Quot.mk (BlockReach V g u) (⟨j2, hj2u⟩ : {i : ι // i ≠ u}) with hc0def
  have hc0bound : (Nat.card A).factorization p ≤
      1 + ((AmbientC0Attach g u c0).card - 1).factorial.factorization p +
        (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
            Nat.factorial ((IslandV g u c0 i).card - 1)).factorization p +
        (Nat.card
            (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach))).factorization
          p :=
    factorization_card_le_cutVertex_c0_bound hpart hne hcent hperm hblock_u hj2u hblock_j2 hp₀u
      hp₀reach hp
  have hcentK := fun ψ (hψ : ψ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach) =>
    hcent ψ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ)
  have hpermK := fun ψ (hψ : ψ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach) =>
    hperm ψ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ)
  have hblockK := fun ψ (hψ : ψ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach) =>
    hblock_u ψ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hψ)
  have hMinv := kerAmbient_mapsTo_compl_c0 hpart hne hcent hperm hblock_u hp₀u hp₀reach
  have hne_attach' : ∀ c ∈ Finset.univ.erase c0, (AmbientC0Attach g u c).Nonempty :=
    fun c _ => hne_attach c
  have houter := key_induction_fiber_dvd hpart hne (Finset.univ.erase c0).card
    (Finset.univ.erase c0) le_rfl (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) hcentK
    hpermK hblockK hMinv hne_attach'
  have houter_val : (Nat.card (KerAmbient hpart hne hcent hperm hblock_u hp₀reach)).factorization
      p ≤ (∏ τ ∈ (Finset.univ.erase c0).image (compType g u),
        (Nat.factorial ((Finset.univ.erase c0).filter (fun c => compType g u c = τ)).card *
          (∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
            Nat.factorial (AmbientC0Attach g u c).card) *
          (∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
            ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1)))).factorization p := by
    have hpos : 0 < Nat.card (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) := Nat.card_pos
    have hprodpos : 0 < (∏ τ ∈ (Finset.univ.erase c0).image (compType g u),
        (Nat.factorial ((Finset.univ.erase c0).filter (fun c => compType g u c = τ)).card *
          (∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
            Nat.factorial (AmbientC0Attach g u c).card) *
          (∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
            ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1)))) := by
      apply Finset.prod_pos
      intro τ _
      have h1 : 0 < Nat.factorial ((Finset.univ.erase c0).filter
          (fun c => compType g u c = τ)).card := Nat.factorial_pos _
      have h2 : 0 < ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
          Nat.factorial (AmbientC0Attach g u c).card :=
        Finset.prod_pos (fun c _ => Nat.factorial_pos _)
      have h3 : 0 < ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
          ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
            Nat.factorial ((IslandV g u c i).card - 1) :=
        Finset.prod_pos (fun c _ => Finset.prod_pos (fun i _ => Nat.factorial_pos _))
      positivity
    have hfixblocks : ∀ i, i ≠ u → ∀ x ∈ V i,
        ∀ φ ∈ FixIslands (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) g u
          (Finset.univ.erase c0), φ x = x := by
      intro i hiu x hx φ hφ
      set c := Quot.mk (BlockReach V g u) (⟨i, hiu⟩ : {k : ι // k ≠ u}) with hcdef
      have hxc : InComponentPlus g u c x := Or.inl ⟨⟨i, hiu⟩, rfl, hx⟩
      by_cases hcc0 : c = c0
      · rw [hcc0] at hxc
        exact kerAmbient_fixes_island hpart hne hcent hperm hblock_u hp₀reach φ
          (mem_FixIslands.mp hφ).1 hxc
      · have hcM : c ∈ Finset.univ.erase c0 := Finset.mem_erase.mpr ⟨hcc0, Finset.mem_univ c⟩
        exact (mem_FixIslands.mp hφ).2 c hcM x hxc
    have htrivial : Nat.card (FixIslands (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) g u
        (Finset.univ.erase c0)) ≤ 1 :=
      card_le_one_of_fixes_all_blocks
        (fun φ hφ => hcent φ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach
          (mem_FixIslands.mp hφ).1))
        hmixed hpart hfixblocks
    have hcard1 : Nat.card (FixIslands (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) g u
        (Finset.univ.erase c0)) = 1 := le_antisymm htrivial Nat.card_pos
    have hdvd : Nat.card (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) ∣
        (∏ τ ∈ (Finset.univ.erase c0).image (compType g u),
          (Nat.factorial ((Finset.univ.erase c0).filter (fun c => compType g u c = τ)).card *
            (∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
              Nat.factorial (AmbientC0Attach g u c).card) *
            (∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
              ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
                Nat.factorial ((IslandV g u c i).card - 1)))) := by
      have := houter
      rw [hcard1, mul_one] at this
      exact this
    exact (Nat.factorization_le_iff_dvd hpos.ne' hprodpos.ne').mpr hdvd p
  have hkereq : (Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u
      hp₀reach))).factorization p =
      (Nat.card (KerAmbient hpart hne hcent hperm hblock_u hp₀reach)).factorization p := by
    rw [card_kerAmbient]
  change (Nat.card A).factorization p ≤
    1 + ((AmbientC0Attach g u c0).card - 1).factorial.factorization p +
      (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
          Nat.factorial ((IslandV g u c0 i).card - 1)).factorization p +
      (∏ τ ∈ (Finset.univ.erase c0).image (compType g u),
        (Nat.factorial ((Finset.univ.erase c0).filter (fun c => compType g u c = τ)).card *
          (∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
            Nat.factorial (AmbientC0Attach g u c).card) *
          (∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
            ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1)))).factorization p
  omega
