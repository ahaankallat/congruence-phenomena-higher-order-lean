import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMap
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPerm
import CongruenceTheoryHigherOrder.A2aCutVertexIslandPermMul
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandG
import CongruenceTheoryHigherOrder.A2aCutVertexIslandHperm
import CongruenceTheoryHigherOrder.A2aCutVertexIslandHom
import CongruenceTheoryHigherOrder.A2aCutVertexIslandNone
import CongruenceTheoryHigherOrder.A2aCutVertexIslandMixed
import CongruenceTheoryHigherOrder.A2aCutVertexIslandConn
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInitEdge
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.PtStabProdBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The tight island bound, without the redundant `a_0` factor.** Every element of
`range(islandHom)` already fixes the island's seed point `p₀` (it descends from `PtStab A p₀`), so
`PtStab (range(islandHom)) p₀ = range(islandHom)` outright — applying `card_le_ptStab_prod_bound`
with this equality gives `Nat.card(range(islandHom)) ≤ ∏_{i∈c0}(R_i-1)!` directly, with no extra
`a_0`-sized orbit-stabilizer factor (unlike `card_le_island_range_bound`, which re-applied the full
`card_le_root_bound` wrapper and so double-counted `a_0`).
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

noncomputable instance instFintypeInComponentPlus' {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    {c0 : BlockComponent V g u} : Fintype {x : Ω // InComponentPlus g u c0 x} :=
  Fintype.ofFinite _

/-- Every element of `range(islandHom)` fixes the island point corresponding to `p₀`. -/
theorem islandHom_range_fixes_p₀ {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} (hp₀u : p₀ ∈ V u)
    {c0 : BlockComponent V g u} (hreach : Reaches g u p₀ c0)
    (ψ : Equiv.Perm {x : Ω // InComponentPlus g u c0 x})
    (hψ : ψ ∈ MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hreach)) :
    ψ ⟨p₀, Or.inr ⟨hp₀u, hreach⟩⟩ = ⟨p₀, Or.inr ⟨hp₀u, hreach⟩⟩ := by
  obtain ⟨a, rfl⟩ := hψ
  apply Subtype.ext
  show islandPermOfPtStab hpart hne hcent hperm hblock_u hreach a.1 a.2 ⟨p₀, _⟩ = p₀
  rw [islandPermOfPtStab_coe]
  exact (mem_PtStab.mp a.2).2

/-- `PtStab (range(islandHom)) p₀ = range(islandHom)` outright, since the whole range already
fixes `p₀`. -/
theorem ptStab_islandHom_range_eq {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} (hp₀u : p₀ ∈ V u)
    {c0 : BlockComponent V g u} (hreach : Reaches g u p₀ c0) :
    PtStab (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hreach))
        (⟨p₀, Or.inr ⟨hp₀u, hreach⟩⟩ : {x : Ω // InComponentPlus g u c0 x}) =
      MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hreach) := by
  unfold PtStab
  apply inf_eq_left.mpr
  intro ψ hψ
  exact MulAction.mem_stabilizer_iff.mpr (islandHom_range_fixes_p₀ hpart hne hcent hperm
    hblock_u hp₀u hreach ψ hψ)

/-- **The tight island block-product bound**: `Nat.card(range(islandHom)) ≤ ∏_{i∈c0}(R_i-1)!`,
with no `a_0` factor. -/
theorem card_le_island_tight_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} (hp₀u : p₀ ∈ V u)
    {c0 : BlockComponent V g u} (hreach : Reaches g u p₀ c0) :
    Nat.card (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hreach)) ≤
      ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
        Nat.factorial ((IslandV g u c0 i).card - 1) := by
  obtain ⟨j₀, hj₀ne, y₀, hy₀mem, hp₀y₀⟩ := island_init_edge hpart g u hp₀u hreach
  have hbound := card_le_ptStab_prod_bound (islandV_isPartition hpart g u c0)
    (A := MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hreach))
    (g := islandG hpart g u c0)
    (by rintro φ ⟨a, rfl⟩
        exact islandPermOfPtStab_commute hpart hne hcent hperm hblock_u hreach a.1 a.2)
    (by rintro φ ⟨a, rfl⟩ i
        exact islandPermOfPtStab_perm hpart hne hcent hperm hblock_u hreach a.1 a.2 i)
    none ⟨p₀, Or.inr ⟨hp₀u, hreach⟩⟩ ((mem_islandV_none g u c0 _).mpr hp₀u)
    (island_hmixed hpart g u c0) hj₀ne hy₀mem hp₀y₀ (island_hconn hpart g u c0)
  rwa [ptStab_islandHom_range_eq hpart hne hcent hperm hblock_u hp₀u hreach] at hbound
