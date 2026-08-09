import Mathlib
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aLayerInduction

/-!
**Closing (A2a)'s remaining gap**: `A2aFullInduction.lean`'s `key_induction` needed its seed block
to already be fixed *pointwise in full*, which the natural starting group `Stab_A(p₀)` (fixing only
`p₀ ∈ V_u`) doesn't provide. This file resolves that by never seeding the induction at `u` at all:
`key_induction_rooted` is a variant of `key_induction` whose domain of blocks excludes the root `u`
entirely, closed at the far end via the "mixed cycle" trick
(`eq_on_block_of_eq_off_block_of_commute`) instead of direct pointwise agreement. One bootstrap
peel from `p₀` to a first block `j₀` (via `card_le_prod_factorial_mul_card_fixBlocks`) produces a
genuine fully-fixed seed block for `key_induction_rooted` to start from. `card_le_root_bound`
assembles all of this into the manuscript's literal `|A|≤R_u∏_{i≠u}(R_i-1)!`.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- Point-stabilizer of `p` inside `A`, as a subgroup of the *ambient* `Equiv.Perm Ω` (avoiding
subgroup-of-subgroup nesting, same trick as `FixBlocks`): `A ⊓ Stab_{Perm Ω}(p)`. -/
def PtStab (A : Subgroup (Perm Ω)) (p : Ω) : Subgroup (Perm Ω) :=
  A ⊓ MulAction.stabilizer (Perm Ω) p

theorem mem_PtStab {A : Subgroup (Perm Ω)} {p : Ω} {φ : Perm Ω} :
    φ ∈ PtStab A p ↔ φ ∈ A ∧ φ p = p := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp h
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.mpr ⟨h1, h2⟩

theorem card_le_card_block_mul_card_ptStab {V : ι → Finset Ω} (hpart : IsPartition V)
    {A : Subgroup (Perm Ω)} (u : ι) (p₀ : Ω) (hp₀ : p₀ ∈ V u)
    (hblock : ∀ φ ∈ A, (V u).image φ = V u) :
    Nat.card A ≤ (V u).card * Nat.card (PtStab A p₀) := by
  have h := card_le_card_block_mul_card_stabilizer (G := A) V u p₀ hp₀ (fun φ => hblock φ.1 φ.2)
  have hEquiv : MulAction.stabilizer A p₀ ≃ PtStab A p₀ :=
  { toFun := fun a => ⟨a.1.1, mem_PtStab.mpr ⟨a.1.2, a.2⟩⟩
    invFun := fun a => ⟨⟨a.1, (mem_PtStab.mp a.2).1⟩, (mem_PtStab.mp a.2).2⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }
  rw [Nat.card_congr hEquiv] at h
  exact h

/-- **The rooted well-founded induction closing (A2a)'s remaining gap.** Just like `key_induction`,
except the domain of blocks being processed excludes a designated root `u` entirely, and instead of
a base case that requires literally *all* blocks (including `u`) to be pinned down, the base case
`L = Finset.univ.erase u` is closed via `eq_on_block_of_eq_off_block_of_commute`'s "mixed cycle"
trick: once every block *other than* `u` is fixed pointwise, any `φ ∈ A` agrees with the identity
everywhere outside `V u`, and the mixed-cycle hypothesis `hmixed` then forces agreement on `V u`
too (with no separate factor for `u`) — so `A` is trivial. This is exactly the mechanism
`card_le_prod_factorial_of_fixed_points` uses for the depth-1 case, now composed with the
genuine per-layer kernel recursion for arbitrary depth. -/
theorem key_induction_rooted {V : ι → Finset Ω} (hpart : IsPartition V) {g : Perm Ω} {u : ι}
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y) :
    ∀ n : ℕ, ∀ L : Finset ι, L ⊆ Finset.univ.erase u →
      ((Finset.univ.erase u) \ L).card ≤ n → L.Nonempty →
    ∀ A : Subgroup (Perm Ω), (∀ φ ∈ A, Commute φ g) →
    (∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) →
    (∀ i ∈ L, ∀ x ∈ V i, ∀ φ ∈ A, φ x = x) →
    Nat.card A ≤ ∏ i ∈ (Finset.univ.erase u) \ L, Nat.factorial ((V i).card - 1) := by
  intro n
  induction n with
  | zero =>
    intro L hLsub hLcard hLne A hcent hperm hfix
    have hLuniv : L = Finset.univ.erase u := by
      have h0 : ((Finset.univ.erase u) \ L).card = 0 := Nat.le_zero.mp hLcard
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at h0
      exact hLsub.antisymm h0
    have hAtriv : ∀ φ ∈ A, φ = 1 := by
      intro φ hφ
      apply Equiv.Perm.ext
      intro x
      by_cases hxu : x ∈ V u
      · have heqoff : ∀ y ∉ V u, φ y = (1 : Perm Ω) y := by
          intro y hy
          obtain ⟨i, hi, -⟩ := hpart y
          have hiu : i ≠ u := by intro h; subst h; exact hy hi
          have hiL : i ∈ L := by rw [hLuniv]; exact Finset.mem_erase.mpr ⟨hiu, Finset.mem_univ i⟩
          simpa using hfix i hiL y hi φ hφ
        have hon := eq_on_block_of_eq_off_block_of_commute (V := V) (u := u) (hcent φ hφ)
          (Commute.one_right g) heqoff hmixed
        simpa using hon x hxu
      · obtain ⟨i, hi, -⟩ := hpart x
        have hiu : i ≠ u := by intro h; subst h; exact hxu hi
        have hiL : i ∈ L := by rw [hLuniv]; exact Finset.mem_erase.mpr ⟨hiu, Finset.mem_univ i⟩
        simpa using hfix i hiL x hi φ hφ
    have hLc : ((Finset.univ.erase u) \ L : Finset ι) = ∅ := by rw [hLuniv]; simp
    rw [hLc]
    simp only [Finset.prod_empty]
    haveI : Subsingleton A := ⟨fun a b => Subtype.ext ((hAtriv a a.2).trans (hAtriv b b.2).symm)⟩
    calc Nat.card A ≤ Nat.card Unit := Nat.card_le_card_of_injective (fun _ => ())
          (fun a b _ => Subsingleton.elim a b)
      _ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨()⟩⟩
  | succ n ih =>
    intro L hLsub hLcard hLne A hcent hperm hfix
    by_cases hLuniv : L = Finset.univ.erase u
    · have hAtriv : ∀ φ ∈ A, φ = 1 := by
        intro φ hφ
        apply Equiv.Perm.ext
        intro x
        by_cases hxu : x ∈ V u
        · have heqoff : ∀ y ∉ V u, φ y = (1 : Perm Ω) y := by
            intro y hy
            obtain ⟨i, hi, -⟩ := hpart y
            have hiu : i ≠ u := by intro h; subst h; exact hy hi
            have hiL : i ∈ L := by
              rw [hLuniv]; exact Finset.mem_erase.mpr ⟨hiu, Finset.mem_univ i⟩
            simpa using hfix i hiL y hi φ hφ
          have hon := eq_on_block_of_eq_off_block_of_commute (V := V) (u := u) (hcent φ hφ)
            (Commute.one_right g) heqoff hmixed
          simpa using hon x hxu
        · obtain ⟨i, hi, -⟩ := hpart x
          have hiu : i ≠ u := by intro h; subst h; exact hxu hi
          have hiL : i ∈ L := by rw [hLuniv]; exact Finset.mem_erase.mpr ⟨hiu, Finset.mem_univ i⟩
          simpa using hfix i hiL x hi φ hφ
      have hLc : ((Finset.univ.erase u) \ L : Finset ι) = ∅ := by rw [hLuniv]; simp
      rw [hLc]
      simp only [Finset.prod_empty]
      haveI : Subsingleton A :=
        ⟨fun a b => Subtype.ext ((hAtriv a a.2).trans (hAtriv b b.2).symm)⟩
      calc Nat.card A ≤ Nat.card Unit := Nat.card_le_card_of_injective (fun _ => ())
            (fun a b _ => Subsingleton.elim a b)
        _ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨()⟩⟩
    · obtain ⟨i, hiL, j, hjL, hjune, x, hx, y, hy, hxy⟩ := hconn L hLne hLuniv hLsub
      have hfixx : ∀ φ ∈ A, φ x = x := hfix i hiL x hx
      have hfixy : ∀ φ ∈ A, φ y = y := by
        intro φ hφ
        exact Perm.fixed_of_commute_of_fixed_point (hcent φ hφ) (hfixx φ hφ) hxy
      have hstep := card_le_prod_factorial_mul_card_fixBlocks hpart hperm ({j} : Finset ι)
        (fun _ => y)
        (by intro i0 hi0; rw [Finset.mem_singleton.mp hi0]; exact hy)
        (by intro i0 hi0 φ hφ; exact hfixy φ hφ)
      simp only [Finset.prod_singleton] at hstep
      have hfix' : ∀ i0 ∈ insert j L, ∀ x0 ∈ V i0, ∀ φ ∈ FixBlocks A V {j}, φ x0 = x0 := by
        intro i0 hi0 x0 hx0 φ hφ
        obtain ⟨hφA, hφfix⟩ := mem_FixBlocks.mp hφ
        rcases Finset.mem_insert.mp hi0 with hi0j | hi0L
        · rw [hi0j] at hx0
          exact hφfix j (Finset.mem_singleton_self j) x0 hx0
        · exact hfix i0 hi0L x0 hx0 φ hφA
      have hjmemU : j ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hjune, Finset.mem_univ j⟩
      have hLsub' : insert j L ⊆ Finset.univ.erase u := by
        intro k hk
        rcases Finset.mem_insert.mp hk with hkj | hkL
        · rw [hkj]; exact hjmemU
        · exact hLsub hkL
      have hcard' : ((Finset.univ.erase u) \ (insert j L)).card ≤ n := by
        have hsub : (Finset.univ.erase u) \ (insert j L) = ((Finset.univ.erase u) \ L).erase j := by
          ext k
          simp only [Finset.mem_sdiff, Finset.mem_insert, not_or, Finset.mem_erase]
          tauto
        rw [hsub]
        have hjmem : j ∈ (Finset.univ.erase u) \ L := by
          simp only [Finset.mem_sdiff]; exact ⟨hjmemU, hjL⟩
        have := Finset.card_erase_of_mem hjmem
        omega
      have hLne' : (insert j L).Nonempty := ⟨j, Finset.mem_insert_self j L⟩
      have hcentker : ∀ φ ∈ FixBlocks A V ({j} : Finset ι), Commute φ g := fun φ hφ =>
        hcent φ (mem_FixBlocks.mp hφ).1
      have hpermker : ∀ φ ∈ FixBlocks A V ({j} : Finset ι), ∀ i0, ∃ j0, (V i0).image φ = V j0 :=
        fun φ hφ => hperm φ (mem_FixBlocks.mp hφ).1
      have hrec := ih (insert j L) hLsub' hcard' hLne' (FixBlocks A V {j}) hcentker hpermker hfix'
      have hcompl : (Finset.univ.erase u) \ (insert j L) = ((Finset.univ.erase u) \ L).erase j := by
        ext k
        simp only [Finset.mem_sdiff, Finset.mem_insert, not_or, Finset.mem_erase]
        tauto
      rw [hcompl] at hrec
      have hjLc : j ∈ (Finset.univ.erase u) \ L := by
        simp only [Finset.mem_sdiff]; exact ⟨hjmemU, hjL⟩
      rw [← Finset.mul_prod_erase ((Finset.univ.erase u) \ L)
        (fun i0 => Nat.factorial ((V i0).card - 1)) hjLc]
      calc Nat.card A ≤ Nat.factorial ((V j).card - 1) * Nat.card (FixBlocks A V {j}) := hstep
        _ ≤ Nat.factorial ((V j).card - 1) *
              ∏ i0 ∈ ((Finset.univ.erase u) \ L).erase j, Nat.factorial ((V i0).card - 1) :=
            Nat.mul_le_mul_left _ hrec

/-- **The full literal bound for (A2a)'s "`u` not a cut vertex" case**:
`|A| ≤ R_u·∏_{i≠u}(R_i-1)!`, exactly as the manuscript states it — closing the gap left open in
`A2aFullInduction.lean`. Given `A` fixes root block `u` setwise, a chosen point `p₀ ∈ V_u`, the
mixed-cycle hypothesis for `V_u`, an initial edge from `p₀` to some other block `j₀` via a shared
`g`-cycle, and connectivity among the remaining blocks (`hconn`, as in `key_induction_rooted`):
the orbit-stabilizer step (`card_le_card_block_mul_card_ptStab`) gives the `R_u` factor and reduces
to `PtStab A p₀`; one bootstrap application of `card_le_prod_factorial_mul_card_fixBlocks` (using
`j₀`'s point `y₀`, uniformly fixed by all of `PtStab A p₀` via
`Perm.fixed_of_commute_of_fixed_point` propagating from `p₀`) reaches a genuine subgroup
`FixBlocks (PtStab A p₀) V {j₀}` that fixes *all*
of `V j₀` pointwise — exactly the seed `key_induction_rooted` needs; that theorem then finishes the
job for every other block. -/
theorem card_le_root_bound {V : ι → Finset Ω} (hpart : IsPartition V) {A : Subgroup (Perm Ω)}
    {g : Perm Ω} (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j)
    (u : ι) (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) (p₀ : Ω) (hp₀ : p₀ ∈ V u)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    {j₀ : ι} (hj₀u : j₀ ≠ u) {y₀ : Ω} (hy₀ : y₀ ∈ V j₀) (hp₀y₀ : g.SameCycle p₀ y₀)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y) :
    Nat.card A ≤ (V u).card * ∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1) := by
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
  have htotal : Nat.card Apt ≤ ∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1) := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase u) (fun i => Nat.factorial ((V i).card - 1))
      hj₀mem]
    calc Nat.card Apt ≤ Nat.factorial ((V j₀).card - 1) * Nat.card (FixBlocks Apt V {j₀}) := hstep0
      _ ≤ Nat.factorial ((V j₀).card - 1) *
            ∏ i ∈ (Finset.univ.erase u).erase j₀, Nat.factorial ((V i).card - 1) :=
          Nat.mul_le_mul_left _ hrec
  have hfinal := card_le_card_block_mul_card_ptStab hpart u p₀ hp₀ hblock_u
  calc Nat.card A ≤ (V u).card * Nat.card Apt := hfinal
    _ ≤ (V u).card * ∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1) :=
        Nat.mul_le_mul_left _ htotal
