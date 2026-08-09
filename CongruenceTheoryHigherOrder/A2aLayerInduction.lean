import Mathlib
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful
import CongruenceTheoryHigherOrder.A2aOrbitBound

/-!
**The genuine recursive step of (A2a)'s general-depth tree-rooted counting bound.**
`A2aOrbitBound.lean`'s `card_le_prod_factorial_of_fixed_points`/`_layer` prove the *depth-1* case
directly, and correctly diagnose that the general-depth case needs a well-founded induction
peeling one layer of the spanning tree at a time, threading a *shrinking subgroup* through the
recursion — but stop short of that shrinking subgroup, since a plain cardinality bound doesn't
give one to recurse on. This file supplies exactly that missing piece: a genuine `Subgroup`
(not just a cardinality bound) to recurse into, and the propagation fact showing it correctly
carries forward to the next layer.

**`FixBlocks A V L`**: the subgroup of `A` fixing every block in the Finset `L` pointwise, as a
subgroup of the ambient `Equiv.Perm Ω` (via `fixingSubgroup`, avoiding subgroup-of-subgroup
nesting so it composes with itself across layers without accumulating wrapper types).

**`card_le_prod_factorial_mul_card_fixBlocks`**: given `A` fixes a designated point `q i` in every
block `i∈L` and permutes blocks, the map `φ↦(φ restricted to `V i∖{q i}`)_{i∈L}` is a genuine
`MonoidHom` `A →* ∀i∈L,Equiv.Perm↥(V i∖{q i})` (built from `Equiv.Perm.subtypePerm`, verified to
respect multiplication), whose kernel is *exactly* `FixBlocks A V L` (elements fixing every point,
not just the designated ones) — giving, via Noether's first isomorphism theorem
(`QuotientGroup.quotientKerEquivRange`) plus Lagrange (`Subgroup.card_eq_card_quotient_mul_card_
subgroup`), `|A| ≤ (∏i∈L,(R_i-1)!)·|FixBlocks A V L|`. This is the correct per-layer step: unlike
the cardinality-only version in `A2aOrbitBound.lean`, `FixBlocks A V L` is an actual subgroup ready
to feed into the *next* application.

**`FixBlocks_fixes_of_sameCycle`**: elements of `FixBlocks A V L` fix every point reachable via a
`g`-cycle from any already-fixed block in `L` (via `Perm.fixed_of_commute_of_fixed_point`) — so the
*next* layer's designated points are uniformly fixed by `FixBlocks A V L`, exactly the hypothesis
`card_le_prod_factorial_mul_card_fixBlocks` needs to apply again, one layer further out.

**Honest scope note**: together these two theorems give every ingredient the recursion needs —
what's *not* assembled here is the well-founded recursion itself (peeling the spanning tree from
`SpanningTreeLeaf.lean` layer by layer, calling these two theorems at each step, and multiplying
the resulting bounds telescopically down to `R_u∏_{i≠u}(R_i-1)!`), nor the "`u` is a cut vertex"
case of (A2a).
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω]

/-- The subgroup of `A` fixing every block in `L` pointwise, kept as a subgroup of the ambient
`Equiv.Perm Ω` so repeated applications compose without nesting subgroup types. -/
def FixBlocks (A : Subgroup (Perm Ω)) (V : ι → Finset Ω) (L : Finset ι) : Subgroup (Perm Ω) :=
  A ⊓ fixingSubgroup (Perm Ω) (⋃ i ∈ L, (V i : Set Ω))

theorem mem_FixBlocks {A : Subgroup (Perm Ω)} {V : ι → Finset Ω} {L : Finset ι} {φ : Perm Ω} :
    φ ∈ FixBlocks A V L ↔ φ ∈ A ∧ ∀ i ∈ L, ∀ x ∈ V i, φ x = x := by
  simp only [FixBlocks, Subgroup.mem_inf, mem_fixingSubgroup_iff, Set.mem_iUnion, Finset.mem_coe]
  constructor
  · rintro ⟨hA, hfix⟩
    exact ⟨hA, fun i hi x hx => hfix x ⟨i, hi, hx⟩⟩
  · rintro ⟨hA, hfix⟩
    exact ⟨hA, fun x ⟨i, hi, hx⟩ => hfix i hi x hx⟩

/-- One genuine layer step, via an actual `MonoidHom`, giving a real remaining subgroup to
recurse on: given `A` fixes `q i` for every `i∈L`, and permutes blocks, `A` embeds into
`∏i:L,Perm(Vi∖{qi})` with kernel exactly `FixBlocks A V L`, giving
`|A| ≤ (∏i∈L,(Ri-1)!)·|FixBlocks A V L|`. -/
theorem card_le_prod_factorial_mul_card_fixBlocks {V : ι → Finset Ω}
    (hpart : IsPartition V) {A : Subgroup (Perm Ω)}
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (L : Finset ι) (q : ι → Ω)
    (hq : ∀ i ∈ L, q i ∈ V i) (hfixq : ∀ i ∈ L, ∀ φ ∈ A, φ (q i) = q i) :
    Nat.card A ≤ (∏ i ∈ L, Nat.factorial ((V i).card - 1)) * Nat.card (FixBlocks A V L) := by
  have hfixblock : ∀ i ∈ L, ∀ φ ∈ A, (V i).image φ = V i := by
    intro i hi φ hφ
    obtain ⟨j, hj⟩ := hperm φ hφ i
    have hpj : q i ∈ V j := hj ▸ Finset.mem_image.mpr ⟨q i, hq i hi, hfixq i hi φ hφ⟩
    obtain ⟨i0, -, hunique⟩ := hpart (q i)
    have heq : i = j := (hunique i (hq i hi)).trans (hunique j hpj).symm
    subst heq; exact hj
  have hiff : ∀ i ∈ L, ∀ φ ∈ A, ∀ x : Ω,
      (φ x ∈ V i ∧ φ x ≠ q i) ↔ (x ∈ V i ∧ x ≠ q i) := by
    intro i hi φ hφ x
    have hbl := hfixblock i hi φ hφ
    have hqf := hfixq i hi φ hφ
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x', hx'mem, hx'eq⟩ := Finset.mem_image.mp (hbl ▸ h1)
      refine ⟨(φ.injective hx'eq) ▸ hx'mem, ?_⟩
      intro heq; apply h2; rw [heq]; exact hqf
    · rintro ⟨h1, h2⟩
      refine ⟨hbl ▸ Finset.mem_image_of_mem φ h1, ?_⟩
      intro heq; exact h2 (φ.injective (heq.trans hqf.symm))
  set restrict : ∀ φ ∈ A, ∀ i ∈ L, Equiv.Perm ↥((V i).erase (q i)) := fun φ hφ i hi =>
    Equiv.Perm.subtypePerm φ (by
      intro x; simpa [Finset.mem_erase, and_comm] using hiff i hi φ hφ x) with hrestrictDef
  set f : A →* ∀ i : (L : Finset ι), Equiv.Perm ↥((V i.1).erase (q i.1)) :=
    { toFun := fun φ i => restrict φ.1 φ.2 i.1 i.2
      map_one' := by
        funext i
        apply Equiv.ext
        intro x
        simp [hrestrictDef]
      map_mul' := by
        intro φ ψ
        funext i
        apply Equiv.ext
        intro x
        simp only [hrestrictDef, Equiv.Perm.subtypePerm_apply, Pi.mul_apply]
        rfl } with hfDef
  have hker : ∀ φ : A, f φ = 1 ↔ φ.1 ∈ FixBlocks A V L := by
    intro φ
    rw [mem_FixBlocks]
    constructor
    · intro hf
      refine ⟨φ.2, ?_⟩
      intro i hi x hx
      have hfi : f φ ⟨i, hi⟩ = 1 := by rw [hf]; rfl
      by_cases hxq : x = q i
      · rw [hxq]; exact hfixq i hi φ.1 φ.2
      · have hxe : x ∈ (V i).erase (q i) := Finset.mem_erase.mpr ⟨hxq, hx⟩
        have := congrArg (fun e : Equiv.Perm ↥((V i).erase (q i)) => (e ⟨x, hxe⟩ : Ω)) hfi
        simpa [hfDef, hrestrictDef, Equiv.Perm.subtypePerm_apply] using this
    · rintro ⟨-, hfix⟩
      funext i
      apply Equiv.ext
      intro x
      have hxi : (x : Ω) ∈ V i.1 := by
        have := x.2
        rw [Finset.mem_erase] at this
        exact this.2
      show restrict φ.1 φ.2 i.1 i.2 x = x
      apply Subtype.ext
      simp only [hrestrictDef, Equiv.Perm.subtypePerm_apply]
      exact hfix i.1 i.2 x.1 hxi
  have hcard : Nat.card A = Nat.card (MonoidHom.range f) * Nat.card (MonoidHom.ker f) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker f),
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hkereq : Nat.card (MonoidHom.ker f) = Nat.card (FixBlocks A V L) := by
    apply Nat.card_congr
    refine ⟨fun x => ⟨x.1.1, (hker x.1).mp x.2⟩, fun y => ⟨⟨y.1, ((mem_FixBlocks).mp y.2).1⟩,
      (hker ⟨y.1, ((mem_FixBlocks).mp y.2).1⟩).mpr y.2⟩, ?_, ?_⟩
    · intro x; rfl
    · intro y; rfl
  have hrange : Nat.card (MonoidHom.range f) ≤ ∏ i ∈ L, Nat.factorial ((V i).card - 1) := by
    calc Nat.card (MonoidHom.range f)
        ≤ Nat.card (∀ i : (L : Finset ι), Equiv.Perm ↥((V i.1).erase (q i.1))) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = ∏ i ∈ L, Nat.factorial ((V i).card - 1) := by
          rw [Nat.card_pi, ← Finset.prod_coe_sort L (fun i => Nat.factorial ((V i).card - 1))]
          apply Finset.prod_congr rfl
          intro i hi
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe,
            Finset.card_erase_of_mem (hq i.1 i.2)]
  rw [hcard, hkereq]
  exact Nat.mul_le_mul_right _ hrange

/-- The propagation fact enabling the layer induction: elements of `FixBlocks A V L` fix every
point reachable via a `g`-cycle from an already-fixed block in `L` — so the *next* layer's
designated points are uniformly fixed by `FixBlocks A V L`, letting
`card_le_prod_factorial_mul_card_fixBlocks` apply again at the next layer. -/
theorem FixBlocks_fixes_of_sameCycle {A : Subgroup (Perm Ω)} {g : Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) {V : ι → Finset Ω} {L : Finset ι} {i : ι} (hi : i ∈ L)
    {p q : Ω} (hp : p ∈ V i) (hpq : g.SameCycle p q) :
    ∀ φ ∈ FixBlocks A V L, φ q = q := by
  intro φ hφ
  obtain ⟨hφA, hfix⟩ := mem_FixBlocks.mp hφ
  exact Perm.fixed_of_commute_of_fixed_point (hcent φ hφA) (hfix i hi p hp) hpq
