import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexBranchConfinement
import CongruenceTheoryHigherOrder.A2aCutVertexC0Valuation
import CongruenceTheoryHigherOrder.A2aCutVertexIslandFactor

/-!
**Valuation-level bound for an arbitrary component fixed setwise (not just the manuscript's
distinguished `C_0`).** `A2aCutVertexC0Valuation.lean` upgraded the `C_0`-specific cardinality
bound to a valuation-level one. This file gives the same upgrade for *any* component `c` that a
subgroup `A` fixes setwise (the situation that arises after peeling `C_0` and, per-`compType`-fiber,
after the single-shot Lagrange step in `A2aCutVertexFiberPermHom.lean` has already accounted for
which branch goes where — every element of the relevant kernel then fixes each remaining branch
setwise, with no orbit-among-branches left to bound). The proof is the same
exact-orbit-stabilizer-plus-log-factorial strategy, using `card_le_ambientAttach_mul_card_ptStab_
of_component_fixed` in place of the `C_0`-specific confinement lemma, and the already-proved
`card_dvd_island_tight_bound` (generic in the component) for the island/range part unchanged.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **Valuation-level bound for a single, already-fixed component `c`.** Gives
`v_p(Nat.card A) ≤ 1+v_p((AmbientC0Attach(c).card-1)!) + v_p(∏_{i∈c}(R_i-1)!) +
v_p(Nat.card(ker(islandHom)))`, with no unjustified `≤`-to-`v_p` step. -/
theorem factorization_card_le_component_fixed_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {c : BlockComponent V g u}
    (hfix : ∀ (φ : Equiv.Perm Ω) (hφ : φ ∈ A),
      componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c = c)
    {p₀ : Ω} (hp₀ : p₀ ∈ V u) (hp₀reach : Reaches g u p₀ c)
    {p : ℕ} (hp : p.Prime) :
    (Nat.card A).factorization p ≤
      1 + ((AmbientC0Attach g u c).card - 1).factorial.factorization p +
        (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
            Nat.factorial ((IslandV g u c i).card - 1)).factorization p +
        (Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach))).factorization
          p := by
  have horbstab : Nat.card (MulAction.orbit A p₀) * Nat.card (MulAction.stabilizer A p₀) =
      Nat.card A := nat_card_orbit_mul_stabilizer p₀
  have hEquiv : MulAction.stabilizer A p₀ ≃ PtStab A p₀ :=
  { toFun := fun a => ⟨a.1.1, mem_PtStab.mpr ⟨a.1.2, a.2⟩⟩
    invFun := fun a => ⟨⟨a.1, (mem_PtStab.mp a.2).1⟩, (mem_PtStab.mp a.2).2⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }
  rw [Nat.card_congr hEquiv] at horbstab
  have horb_le : Nat.card (MulAction.orbit A p₀) ≤ (AmbientC0Attach g u c).card := by
    have h := card_le_ambientAttach_mul_card_ptStab_of_component_fixed hpart hne hcent hperm
      hblock_u hfix hp₀ hp₀reach
    rw [← horbstab] at h
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
  have hRpos : 1 ≤ (AmbientC0Attach g u c).card :=
    Finset.card_pos.mpr ⟨p₀, (mem_ambientC0Attach g u c p₀).mpr ⟨hp₀, hp₀reach⟩⟩
  have hpk : p ^ ((Nat.card (MulAction.orbit A p₀)).factorization p) ≤
      (AmbientC0Attach g u c).card := by
    have hpk' : p ^ ((Nat.card (MulAction.orbit A p₀)).factorization p) ∣
        Nat.card (MulAction.orbit A p₀) := Nat.ordProj_dvd _ p
    exact (Nat.le_of_dvd horbpos hpk').trans horb_le
  have horb_bound : (Nat.card (MulAction.orbit A p₀)).factorization p ≤
      1 + ((AmbientC0Attach g u c).card - 1).factorial.factorization p :=
    pow_le_imp_le_one_add_factorization_factorial_pred hp (AmbientC0Attach g u c).card _ hRpos hpk
  have hrangeker := card_ptStab_eq_range_mul_ker hpart hne hcent hperm hblock_u hp₀reach
  have hrangedvd := card_dvd_island_tight_bound hpart hne hcent hperm hblock_u hp₀ hp₀reach
  have hrangepos : 0 < Nat.card (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u
      hp₀reach)) := Nat.card_pos
  have hkerpos : 0 < Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u
      hp₀reach)) := Nat.card_pos
  have hptstab_val : (Nat.card (PtStab A p₀)).factorization p =
      (Nat.card (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u
          hp₀reach))).factorization p +
        (Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u
          hp₀reach))).factorization p := by
    rw [hrangeker, Nat.factorization_mul hrangepos.ne' hkerpos.ne']
    rfl
  have hprodpos : 0 < ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
      Nat.factorial ((IslandV g u c i).card - 1) :=
    Finset.prod_pos (fun i _ => Nat.factorial_pos _)
  have hrange_bound : (Nat.card (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u
      hp₀reach))).factorization p ≤
      (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
        Nat.factorial ((IslandV g u c i).card - 1)).factorization p := by
    have h := (Nat.factorization_le_iff_dvd hrangepos.ne' hprodpos.ne').mpr hrangedvd
    exact h p
  omega
