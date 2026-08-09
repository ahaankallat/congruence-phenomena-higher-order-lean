import Mathlib
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aLayerInduction
import CongruenceTheoryHigherOrder.A2aRootBound

/-!
**`card_le_root_bound`'s internal `PtStab`-only bound, exposed standalone.** `card_le_root_bound`
computes `Nat.card (PtStab A p₀) ≤ ∏_{i≠u}(R_i-1)!` as an intermediate step, before the final
`(V u).card * ·` wrapper (which needs `hblock_u`). Exposing this intermediate step *without* that
wrapper (and without needing `hblock_u` at all) is exactly what's needed to apply it directly to
`range(islandHom)` in (A2a)'s cut-vertex case: since every element of `range(islandHom)` already
fixes the island's own seed point `p₀` by construction (it descends from `PtStab A p₀`), re-wrapping
with another `(V u).card`-style factor would double-count — this lemma gives the tight block-product
bound alone.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

theorem card_le_ptStab_prod_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    {A : Subgroup (Perm Ω)} {g : Perm Ω} (hcent : ∀ φ ∈ A, Commute φ g)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (u : ι) (p₀ : Ω) (hp₀ : p₀ ∈ V u)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    {j₀ : ι} (hj₀u : j₀ ≠ u) {y₀ : Ω} (hy₀ : y₀ ∈ V j₀) (hp₀y₀ : g.SameCycle p₀ y₀)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y) :
    Nat.card (PtStab A p₀) ≤ ∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1) := by
  set Apt := PtStab A p₀ with hApt
  have hcent_pt : ∀ φ ∈ Apt, Commute φ g := fun φ hφ => hcent φ (mem_PtStab.mp hφ).1
  have hperm_pt : ∀ φ ∈ Apt, ∀ i, ∃ j, (V i).image φ = V j :=
    fun φ hφ => hperm φ (mem_PtStab.mp hφ).1
  have hstep0 := card_le_prod_factorial_mul_card_fixBlocks hpart hperm_pt ({j₀} : Finset ι)
    (fun _ => y₀)
    (by intro i0 hi0; rw [Finset.mem_singleton.mp hi0]; exact hy₀)
    (by
      intro i0 hi0 φ hφ
      obtain ⟨hφA, hφp₀⟩ := mem_PtStab.mp hφ
      exact Perm.fixed_of_commute_of_fixed_point (hcent φ hφA) hφp₀ hp₀y₀)
  simp only [Finset.prod_singleton] at hstep0
  have hj₀mem : j₀ ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hj₀u, Finset.mem_univ j₀⟩
  have hrec := key_induction_rooted hpart hmixed hconn
    (((Finset.univ.erase u) \ ({j₀} : Finset ι)).card) ({j₀} : Finset ι)
    (by intro k hk; rw [Finset.mem_singleton.mp hk]; exact hj₀mem)
    (le_refl _) ⟨j₀, Finset.mem_singleton_self j₀⟩ (FixBlocks Apt V {j₀})
    (fun φ hφ => hcent_pt φ (mem_FixBlocks.mp hφ).1)
    (fun φ hφ => hperm_pt φ (mem_FixBlocks.mp hφ).1)
    (by
      intro i0 hi0 x0 hx0 φ hφ
      obtain ⟨-, hφfix⟩ := mem_FixBlocks.mp hφ
      rw [Finset.mem_singleton] at hi0
      subst hi0
      exact hφfix i0 (Finset.mem_singleton_self i0) x0 hx0)
  have hcompl : (Finset.univ.erase u) \ ({j₀} : Finset ι) = (Finset.univ.erase u).erase j₀ := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_erase]
    tauto
  rw [hcompl] at hrec
  rw [← Finset.mul_prod_erase (Finset.univ.erase u) (fun i => Nat.factorial ((V i).card - 1))
    hj₀mem]
  calc Nat.card Apt ≤ Nat.factorial ((V j₀).card - 1) * Nat.card (FixBlocks Apt V {j₀}) := hstep0
    _ ≤ Nat.factorial ((V j₀).card - 1) *
          ∏ i ∈ (Finset.univ.erase u).erase j₀, Nat.factorial ((V i).card - 1) :=
        Nat.mul_le_mul_left _ hrec

/-- `card_le_root_bound` follows from `card_le_ptStab_prod_bound` plus the top-level
orbit-stabilizer step. -/
theorem card_le_root_bound' {V : ι → Finset Ω} (hpart : IsPartition V) {A : Subgroup (Perm Ω)}
    {g : Perm Ω} (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j)
    (u : ι) (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) (p₀ : Ω) (hp₀ : p₀ ∈ V u)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    {j₀ : ι} (hj₀u : j₀ ≠ u) {y₀ : Ω} (hy₀ : y₀ ∈ V j₀) (hp₀y₀ : g.SameCycle p₀ y₀)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y) :
    Nat.card A ≤ (V u).card * ∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1) := by
  have htotal := card_le_ptStab_prod_bound hpart hcent hperm u p₀ hp₀ hmixed hj₀u hy₀ hp₀y₀ hconn
  have hfinal := card_le_card_block_mul_card_ptStab hpart u p₀ hp₀ hblock_u
  calc Nat.card A ≤ (V u).card * Nat.card (PtStab A p₀) := hfinal
    _ ≤ (V u).card * ∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1) :=
        Nat.mul_le_mul_left _ htotal
