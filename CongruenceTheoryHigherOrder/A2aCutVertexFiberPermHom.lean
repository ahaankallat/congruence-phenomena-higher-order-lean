import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexComponentHom
import CongruenceTheoryHigherOrder.A2aCutVertexComponentType

/-!
**The "which-branch-goes-where" divisibility fact for (A2a)'s cut-vertex `m_τ!` factor.**
`key_induction_cutVertex_components''`'s iterative orbit-peeling gives a valid *cardinality*
bound whose factors telescope to `classFactorialProd = ∏_τ(fiber_τ.card)!`, but converting that
telescoping to a *valuation* bound termwise is invalid (the same `≤`-does-not-imply-`v_p`-`≤`
issue the non-cut-vertex fix addressed): bounding each peeled orbit's size by the shrinking fiber
and applying the log-factorial lemma at every step gives a bound strictly looser than
`v_p(m_τ!)`.

The fix is a genuinely different, single-shot argument: for any `A' : Subgroup (Equiv.Perm Ω)`
fixing block `u` setwise, and any `A'`-invariant `S : Finset (BlockComponent V g u)` (in
particular, a `compType`-fiber, invariant since `compType` is preserved by every `φ ∈ A'`),
restricting `componentHom`'s action to `S` gives a genuine `MonoidHom A' →* Equiv.Perm ↥S`, whose
*image* is a subgroup of `Equiv.Perm ↥S`, so its order *divides* `Nat.card (Equiv.Perm ↥S) =
S.card!` by Lagrange directly — no induction, no telescoping, and no value-only bound anywhere.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **The restriction-to-a-fixed-subset homomorphism.** Given `A'` fixes block `u` setwise and
`S` is invariant under every `φ ∈ A'`'s component-permutation action, `A'` acts on `↥S` too. -/
noncomputable def fiberHom {V : ι → Finset Ω} (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S) :
    A' →* Equiv.Perm ↥S where
  toFun φ := (componentHom hpart hne hcent' hperm' hblock_u' φ).subtypePerm (by
    intro c
    constructor
    · intro hc
      have hstep := hSinv φ⁻¹ (componentHom hpart hne hcent' hperm' hblock_u' φ c) hc
      have hcomb : componentHom hpart hne hcent' hperm' hblock_u' φ⁻¹ *
          componentHom hpart hne hcent' hperm' hblock_u' φ = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      have heq : componentHom hpart hne hcent' hperm' hblock_u' φ⁻¹
          (componentHom hpart hne hcent' hperm' hblock_u' φ c) = c := by
        have happly := congrArg (fun e : Equiv.Perm (BlockComponent V g u) => e c) hcomb
        simpa [Equiv.Perm.mul_apply] using happly
      rwa [heq] at hstep
    · intro hc
      exact hSinv φ c hc)
  map_one' := by
    apply Equiv.ext
    intro c
    apply Subtype.ext
    show (componentHom hpart hne hcent' hperm' hblock_u' 1) c.1 = c.1
    rw [map_one]
    rfl
  map_mul' a b := by
    apply Equiv.ext
    intro c
    apply Subtype.ext
    show (componentHom hpart hne hcent' hperm' hblock_u' (a * b)) c.1 =
      (componentHom hpart hne hcent' hperm' hblock_u' a)
        ((componentHom hpart hne hcent' hperm' hblock_u' b) c.1)
    rw [map_mul]
    rfl

/-- **The `m_τ!` divisibility fact, single-shot via Lagrange.** No induction, no telescoping. -/
theorem card_dvd_fiberHom_range_factorial {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S) :
    Nat.card (MonoidHom.range (fiberHom hpart hne hcent' hperm' hblock_u' S hSinv)) ∣
      Nat.factorial S.card := by
  have hcard : Nat.card (Equiv.Perm ↥S) = Nat.factorial S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe]
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card _

/-- **Every `φ ∈ A'` preserves `compType`**, hence every `compType`-fiber is `fiberHom`-invariant.
Uses `card_ambientAttach_eq_of_moved`/`prod_blockSet_eq_of_moved` (already proven for same-orbit
components) applied directly with `hmove := rfl`, since `φ • c` is by definition
`componentHom hpart hne hcent' hperm' hblock_u' φ c` and these lemmas hold for *any* `φ`, not just
orbit witnesses. -/
theorem compType_fiber_invariant {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) (τ : ℕ × ℕ) :
    ∀ φ : A', ∀ c ∈ Finset.univ.filter (fun c => compType g u c = τ),
      componentHom hpart hne hcent' hperm' hblock_u' φ c ∈
        Finset.univ.filter (fun c => compType g u c = τ) := by
  intro φ c hc
  rw [Finset.mem_filter] at hc
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hmove : componentPermOfMem hpart hne hcent' hperm' φ.2 (hblock_u' φ.1 φ.2) c =
      componentHom hpart hne hcent' hperm' hblock_u' φ c := rfl
  have h1 : (AmbientC0Attach g u c).card =
      (AmbientC0Attach g u (componentHom hpart hne hcent' hperm' hblock_u' φ c)).card :=
    card_ambientAttach_eq_of_moved hpart hne hcent' hperm' hblock_u' φ.2 hmove
  have h2 : ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1) =
      ∏ i ∈ BlockSet g u (componentHom hpart hne hcent' hperm' hblock_u' φ c),
        Nat.factorial ((V i.1).card - 1) :=
    prod_blockSet_eq_of_moved hpart hne hcent' hperm' hblock_u' φ.2 hmove
  rw [← hc.2]
  unfold compType
  rw [← h1, ← h2]
