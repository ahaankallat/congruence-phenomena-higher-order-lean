import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentHom
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandHom
import CongruenceTheoryHigherOrder.A2aCutVertexDistinguished
import CongruenceTheoryHigherOrder.A2aCutVertexC0Bound
import CongruenceTheoryHigherOrder.A2aCutVertexBranchConfinement
import CongruenceTheoryHigherOrder.A2aCutVertexBranchOrbitStab
import CongruenceTheoryHigherOrder.A2aCutVertexBranchBound
import CongruenceTheoryHigherOrder.A2aCutVertexKerAmbient
import CongruenceTheoryHigherOrder.A2aCutVertexComponentComplement
import CongruenceTheoryHigherOrder.A2aCutVertexBaseCase
import CongruenceTheoryHigherOrder.A2aCutVertexOrbitEqual
import CongruenceTheoryHigherOrder.A2aCutVertexOuterInduction
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**(A2a)'s full cut-vertex bound, unrefined form.** Combines the distinguished component's bound
(`card_le_cutVertex_c0_bound`) with the outer induction across every other component
(`key_induction_cutVertex_components`) into a single literal `Nat` inequality bounding `|A|`. This
is genuinely weaker than the manuscript's exact grouped `a_0·∏_τ(a_τ)^{m_τ}·m_τ!` bound (see
`A2aCutVertexOuterInduction.lean`'s docstring for exactly why, and what refining this would need),
but it is a complete, fully proved, honestly-stated theorem for the cut-vertex case as a whole.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **(A2a)'s full cut-vertex bound.** -/
theorem card_le_cutVertex_full_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    (hreach_all : ∀ c : BlockComponent V g u, ∃ q ∈ V u, Reaches g u q c)
    {j2 : ι} (hj2u : j2 ≠ u) (hblock_j2 : ∀ φ ∈ A, (V j2).image φ = V j2) {p₀ : Ω}
    (hp₀u : p₀ ∈ V u)
    (hp₀reach : Reaches g u p₀ (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)) :
    Nat.card A ≤
      (AmbientC0Attach g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).card *
        (∏ i ∈ Finset.univ.erase
              (none : IslandBlockIdx g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)),
            Nat.factorial
              ((IslandV g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩) i).card - 1)) *
        ((Fintype.card (BlockComponent V g u)) ^
            (Finset.univ.erase (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).card *
          ∏ c ∈ Finset.univ.erase (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩),
            ((AmbientC0Attach g u c).card *
              ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1))) := by
  set c0 := Quot.mk (BlockReach V g u) (⟨j2, hj2u⟩ : {i : ι // i ≠ u}) with hc0def
  have hc0bound := card_le_cutVertex_c0_bound hpart hne hcent hperm hblock_u hj2u hblock_j2 hp₀u
    hp₀reach
  have hcentK : ∀ φ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach, Commute φ g :=
    fun φ hφ => hcent φ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hφ)
  have hpermK : ∀ φ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach,
      ∀ i, ∃ j, (V i).image φ = V j :=
    fun φ hφ => hperm φ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hφ)
  have hblockK : ∀ φ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach,
      (V u).image φ = V u :=
    fun φ hφ => hblock_u φ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hφ)
  have hfixedK : ∀ c, c ∉ Finset.univ.erase c0 → ∀ x, InComponentPlus g u c x →
      ∀ φ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach, φ x = x := by
    intro c hc x hx φ hφ
    have hcc0 : c = c0 := by
      by_contra hne'
      exact hc (Finset.mem_erase.mpr ⟨hne', Finset.mem_univ c⟩)
    subst hcc0
    exact kerAmbient_fixes_island hpart hne hcent hperm hblock_u hp₀reach φ hφ hx
  have hker_bound := key_induction_cutVertex_components hpart hne hmixed hreach_all
    (Finset.univ.erase c0).card (Finset.univ.erase c0) (le_refl _)
    (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) hcentK hpermK hblockK hfixedK
  have hcardker : Nat.card (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) =
      Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach)) :=
    card_kerAmbient hpart hne hcent hperm hblock_u hp₀reach
  rw [← hcardker] at hc0bound
  calc Nat.card A ≤ (AmbientC0Attach g u c0).card *
        (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
            Nat.factorial ((IslandV g u c0 i).card - 1)) *
        Nat.card (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) := hc0bound
    _ ≤ (AmbientC0Attach g u c0).card *
          (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
              Nat.factorial ((IslandV g u c0 i).card - 1)) *
          ((Fintype.card (BlockComponent V g u)) ^ (Finset.univ.erase c0).card *
            ∏ c ∈ Finset.univ.erase c0, ((AmbientC0Attach g u c).card *
              ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1))) :=
        Nat.mul_le_mul_left _ hker_bound

/-- **(A2a)'s full cut-vertex bound, sharper form**: identical to `card_le_cutVertex_full_bound`
except using `key_induction_cutVertex_components'` (confining each step's orbit to the *remaining*
pool `M`, giving `M.card !`) instead of the crude `Fintype.card(BlockComponent)^{M.card}`
accumulation — a strictly tighter, still fully proved bound. -/
theorem card_le_cutVertex_full_bound' {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    (hreach_all : ∀ c : BlockComponent V g u, ∃ q ∈ V u, Reaches g u q c)
    {j2 : ι} (hj2u : j2 ≠ u) (hblock_j2 : ∀ φ ∈ A, (V j2).image φ = V j2) {p₀ : Ω}
    (hp₀u : p₀ ∈ V u)
    (hp₀reach : Reaches g u p₀ (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)) :
    Nat.card A ≤
      (AmbientC0Attach g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).card *
        (∏ i ∈ Finset.univ.erase
              (none : IslandBlockIdx g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)),
            Nat.factorial
              ((IslandV g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩) i).card - 1)) *
        (Nat.factorial
            (Finset.univ.erase (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).card *
          ∏ c ∈ Finset.univ.erase (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩),
            ((AmbientC0Attach g u c).card *
              ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1))) := by
  set c0 := Quot.mk (BlockReach V g u) (⟨j2, hj2u⟩ : {i : ι // i ≠ u}) with hc0def
  have hc0bound := card_le_cutVertex_c0_bound hpart hne hcent hperm hblock_u hj2u hblock_j2 hp₀u
    hp₀reach
  have hcentK : ∀ φ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach, Commute φ g :=
    fun φ hφ => hcent φ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hφ)
  have hpermK : ∀ φ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach,
      ∀ i, ∃ j, (V i).image φ = V j :=
    fun φ hφ => hperm φ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hφ)
  have hblockK : ∀ φ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach,
      (V u).image φ = V u :=
    fun φ hφ => hblock_u φ (kerAmbient_le_A hpart hne hcent hperm hblock_u hp₀reach hφ)
  have hfixedK : ∀ c, c ∉ Finset.univ.erase c0 → ∀ x, InComponentPlus g u c x →
      ∀ φ ∈ KerAmbient hpart hne hcent hperm hblock_u hp₀reach, φ x = x := by
    intro c hc x hx φ hφ
    have hcc0 : c = c0 := by
      by_contra hne'
      exact hc (Finset.mem_erase.mpr ⟨hne', Finset.mem_univ c⟩)
    subst hcc0
    exact kerAmbient_fixes_island hpart hne hcent hperm hblock_u hp₀reach φ hφ hx
  have hker_bound := key_induction_cutVertex_components' hpart hne hmixed hreach_all
    (Finset.univ.erase c0).card (Finset.univ.erase c0) (le_refl _)
    (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) hcentK hpermK hblockK hfixedK
  have hcardker : Nat.card (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) =
      Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach)) :=
    card_kerAmbient hpart hne hcent hperm hblock_u hp₀reach
  rw [← hcardker] at hc0bound
  calc Nat.card A ≤ (AmbientC0Attach g u c0).card *
        (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
            Nat.factorial ((IslandV g u c0 i).card - 1)) *
        Nat.card (KerAmbient hpart hne hcent hperm hblock_u hp₀reach) := hc0bound
    _ ≤ (AmbientC0Attach g u c0).card *
          (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
              Nat.factorial ((IslandV g u c0 i).card - 1)) *
          (Nat.factorial (Finset.univ.erase c0).card *
            ∏ c ∈ Finset.univ.erase c0, ((AmbientC0Attach g u c).card *
              ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1))) :=
        Nat.mul_le_mul_left _ hker_bound
