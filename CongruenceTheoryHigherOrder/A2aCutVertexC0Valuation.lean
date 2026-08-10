import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexC0Bound
import CongruenceTheoryHigherOrder.IslandTightBound
import CongruenceTheoryHigherOrder.PtStabProdBound
import CongruenceTheoryHigherOrder.A2aValuationBound
import CongruenceTheoryHigherOrder.A2aCutVertexIslandFactor
import CongruenceTheoryHigherOrder.A2aCutVertexDistinguished
import CongruenceTheoryHigherOrder.A2aOrbitBound

/-!
**Valuation-level upgrade of (A2a)'s cut-vertex distinguished-component (`C0`) branch.**
`card_le_cutVertex_c0_bound` gives only a cardinality-level `≤`. This file upgrades it to the
valuation-level statement the manuscript's cut-vertex derivation actually needs, using the same
strategy `A2aValuationBound.lean` used for the non-cut-vertex root step: an exact orbit-stabilizer
factorization of `A` (not merely a bound), the log-factorial lemma for the one genuinely
value-only piece (the orbit of `p₀` has size `≤ a_0`, not a divisor of `a_0`), and genuine
divisibility (via Lagrange, through `card_dvd_ptStab_prod`) for everything else.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **Divisibility upgrade of `card_le_island_tight_bound`.** Identical proof, but built on
`card_dvd_ptStab_prod` instead of `card_le_ptStab_prod_bound`. -/
theorem card_dvd_island_tight_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} (hp₀u : p₀ ∈ V u)
    {c0 : BlockComponent V g u} (hreach : Reaches g u p₀ c0) :
    Nat.card (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hreach)) ∣
      ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
        Nat.factorial ((IslandV g u c0 i).card - 1) := by
  obtain ⟨j₀, hj₀ne, y₀, hy₀mem, hp₀y₀⟩ := island_init_edge hpart g u hp₀u hreach
  have hbound := card_dvd_ptStab_prod (islandV_isPartition hpart g u c0)
    (A := MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hreach))
    (g := islandG hpart g u c0)
    (by rintro φ ⟨a, rfl⟩
        exact islandPermOfPtStab_commute hpart hne hcent hperm hblock_u hreach a.1 a.2)
    (by rintro φ ⟨a, rfl⟩ i
        exact islandPermOfPtStab_perm hpart hne hcent hperm hblock_u hreach a.1 a.2 i)
    none ⟨p₀, Or.inr ⟨hp₀u, hreach⟩⟩
    (island_hmixed hpart g u c0) hj₀ne hy₀mem hp₀y₀ (island_hconn hpart g u c0)
  rwa [ptStab_islandHom_range_eq hpart hne hcent hperm hblock_u hp₀u hreach] at hbound

/-- **Valuation-level bound for the cut-vertex case's `C0` branch.** Gives
`v_p(Nat.card A) ≤ 1+v_p((a_0-1)!) + v_p(∏_{i∈c0}(R_i-1)!) + v_p(Nat.card(ker(islandHom)))`,
the manuscript's `C0`-branch valuation contribution, with no unjustified `≤`-to-`v_p` step. -/
theorem factorization_card_le_cutVertex_c0_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {j2 : ι} (hj2u : j2 ≠ u)
    (hblock_j2 : ∀ φ ∈ A, (V j2).image φ = V j2) {p₀ : Ω} (hp₀u : p₀ ∈ V u)
    (hp₀reach : Reaches g u p₀ (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩))
    {p : ℕ} (hp : p.Prime) :
    (Nat.card A).factorization p ≤
      1 + ((AmbientC0Attach g u
              (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).card - 1).factorial.factorization p +
        (∏ i ∈ Finset.univ.erase
              (none : IslandBlockIdx g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)),
            Nat.factorial
              ((IslandV g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩) i).card - 1)).factorization p +
        (Nat.card
            (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach))).factorization p := by
  set c0 := Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩ with hc0def
  have horbstab : Nat.card (MulAction.orbit A p₀) * Nat.card (MulAction.stabilizer A p₀) =
      Nat.card A := nat_card_orbit_mul_stabilizer p₀
  have hEquiv : MulAction.stabilizer A p₀ ≃ PtStab A p₀ :=
  { toFun := fun a => ⟨a.1.1, mem_PtStab.mpr ⟨a.1.2, a.2⟩⟩
    invFun := fun a => ⟨⟨a.1, (mem_PtStab.mp a.2).1⟩, (mem_PtStab.mp a.2).2⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }
  rw [Nat.card_congr hEquiv] at horbstab
  have horb_le : Nat.card (MulAction.orbit A p₀) ≤ (AmbientC0Attach g u c0).card := by
    have h := card_le_card_block_mul_card_stabilizer (G := A)
      (fun _ : Unit => AmbientC0Attach g u c0) ()
      p₀ ((mem_ambientC0Attach g u _ p₀).mpr ⟨hp₀u, hp₀reach⟩)
      (fun φ => ambientC0Attach_image_eq hpart hne hcent hperm hblock_u hj2u hblock_j2 φ.2)
    rw [Nat.card_congr hEquiv, ← horbstab] at h
    exact Nat.le_of_mul_le_mul_right (by rwa [mul_comm] at h) Nat.card_pos
  haveI : Nonempty (MulAction.orbit A p₀) := ⟨⟨p₀, MulAction.mem_orbit_self p₀⟩⟩
  have horbpos : 0 < Nat.card (MulAction.orbit A p₀) := Nat.card_pos
  have hstabpos : 0 < Nat.card (PtStab A p₀) := Nat.card_pos
  have hval : (Nat.card A).factorization p =
      (Nat.card (MulAction.orbit A p₀)).factorization p +
        (Nat.card (PtStab A p₀)).factorization p := by
    rw [← horbstab, Nat.factorization_mul horbpos.ne' hstabpos.ne']
    rfl
  rw [hval]
  have hRpos : 1 ≤ (AmbientC0Attach g u c0).card :=
    Finset.card_pos.mpr ⟨p₀, (mem_ambientC0Attach g u _ p₀).mpr ⟨hp₀u, hp₀reach⟩⟩
  have hpk : p ^ ((Nat.card (MulAction.orbit A p₀)).factorization p) ≤
      (AmbientC0Attach g u c0).card := by
    have hpk' : p ^ ((Nat.card (MulAction.orbit A p₀)).factorization p) ∣
        Nat.card (MulAction.orbit A p₀) := Nat.ordProj_dvd _ p
    exact (Nat.le_of_dvd horbpos hpk').trans horb_le
  have horb_bound : (Nat.card (MulAction.orbit A p₀)).factorization p ≤
      1 + ((AmbientC0Attach g u c0).card - 1).factorial.factorization p :=
    pow_le_imp_le_one_add_factorization_factorial_pred hp (AmbientC0Attach g u c0).card _ hRpos hpk
  have hrangeker := card_ptStab_eq_range_mul_ker hpart hne hcent hperm hblock_u hp₀reach
  have hrangedvd := card_dvd_island_tight_bound hpart hne hcent hperm hblock_u hp₀u hp₀reach
  have hrangepos : 0 <
      Nat.card (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hp₀reach)) :=
    Nat.card_pos
  have hkerpos : 0 <
      Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach)) :=
    Nat.card_pos
  have hptstab_val : (Nat.card (PtStab A p₀)).factorization p =
      (Nat.card
          (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hp₀reach))).factorization p +
        (Nat.card
          (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach))).factorization p := by
    rw [hrangeker, Nat.factorization_mul hrangepos.ne' hkerpos.ne']
    rfl
  have hprodpos : 0 < ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
      Nat.factorial ((IslandV g u c0 i).card - 1) :=
    Finset.prod_pos (fun i _ => Nat.factorial_pos _)
  have hrange_bound : (Nat.card
      (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hp₀reach))).factorization p ≤
      (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
        Nat.factorial ((IslandV g u c0 i).card - 1)).factorization p := by
    have h := (Nat.factorization_le_iff_dvd hrangepos.ne' hprodpos.ne').mpr hrangedvd
    exact h p
  change (Nat.card (MulAction.orbit A p₀)).factorization p +
      (Nat.card (PtStab A p₀)).factorization p ≤
    1 + ((AmbientC0Attach g u c0).card - 1).factorial.factorization p +
        (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
          Nat.factorial ((IslandV g u c0 i).card - 1)).factorization p +
      (Nat.card
        (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach))).factorization p
  omega
