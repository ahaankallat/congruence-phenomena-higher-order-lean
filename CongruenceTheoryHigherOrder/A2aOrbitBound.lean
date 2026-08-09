import Mathlib
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**Toward (A2a)'s tree-rooted counting bound.** The manuscript bounds `|A|` (a subgroup of the
centralizer of `g` permuting the blocks of a partition, fixing `V_1,V_2` setwise) by
`R_u∏_{i≠u}(R_i-1)!`, via a recursive "peel off a leaf of the spanning tree" argument: at the
root block `u`, the orbit of a chosen point is bounded by `R_u` (Lagrange/orbit-stabilizer), and
the argument then recurses into the point-stabilizer, which — because it fixes a point on the
root's cycle, and hence (`Perm.fixed_of_commute_of_fixed_point` in `CentralizerCycleFaithful.lean`)
every point on that cycle — is forced to fix the next block setwise too, restarting the same
orbit-stabilizer step one block further out along the tree.

This file states the two reusable building blocks for **any acting group** `G` with
`MulAction G Ω` (not just a subgroup of `Equiv.Perm Ω` directly), precisely so that the *same*
theorem can be re-applied to the point-stabilizer produced by the previous step — that is what
makes the argument genuinely recursive in Lean, not just a single instantiation:

- **`fixed_block_of_fixed_point`**: if every element of `G` maps each block of a partition onto
  some block, and `g:G` fixes a point of block `i`, then `g` fixes block `i` setwise. (So knowing
  a group element fixes *one* point of a block already pins the whole block.)
- **`card_le_card_block_mul_card_stabilizer`**: orbit-stabilizer instantiated at a block: if every
  element of `G` fixes block `i` setwise, and `p∈V_i`, then `|G|≤|V_i|·|Stab_G(p)|`.

`card_stabilizer_le_of_sameCycle` chains one *full* recursive step end-to-end: starting from
`A≤Centralizer(g)` fixing root block `u`, and a point `p₀∈V_u` on a cycle also meeting block `j` at
a point `q`, it derives `|Stab_A(p₀)|≤|V_j|·|Stab_{Stab_A(p₀)}(q)|` — i.e. the "propagate through a
shared cycle, then re-open orbit-stabilizer at the next block" step, exactly as the manuscript's
proof of (A2a) describes it. Because the two lemmas above are genuinely stated for an arbitrary
acting group, this composes with itself (apply it again to `Stab_{Stab_A(p₀)}(q)` and the next
shared cycle, and so on) — but the full assembly into `R_u∏_{i≠u}(R_i-1)!`, which needs this step
threaded through an explicit spanning tree with careful bookkeeping of which points have already
been visited, is not attempted here: it needs a well-founded recursion over the spanning tree built
in `SpanningTreeLeaf.lean` (peeling leaves one at a time, in the same spirit as that file's own
construction), substantially more scaffolding than these self-contained, reusable steps.
-/

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]

/-- `V : ι → Finset Ω` partitions `Ω`: every point lies in exactly one block. -/
def IsPartition (V : ι → Finset Ω) : Prop := ∀ x : Ω, ∃! i : ι, x ∈ V i

/-- If every element of `G` maps each block of a partition `V` onto some block, and `g:G` fixes a
point `p` of block `i`, then `g` fixes block `i` setwise. -/
theorem fixed_block_of_fixed_point {G : Type*} [Group G] [MulAction G Ω] {V : ι → Finset Ω}
    (hpart : IsPartition V) (hperm : ∀ g : G, ∀ i, ∃ j, (V i).image (g • ·) = V j)
    (g : G) {i : ι} {p : Ω} (hp : p ∈ V i) (hfix : g • p = p) :
    (V i).image (g • ·) = V i := by
  obtain ⟨j, hj⟩ := hperm g i
  have hpj : p ∈ V j := hj ▸ Finset.mem_image.mpr ⟨p, hp, hfix⟩
  obtain ⟨i0, -, hunique⟩ := hpart p
  have heq : i = j := (hunique i hp).trans (hunique j hpj).symm
  subst heq
  exact hj

/-- Orbit-stabilizer, in `Nat.card` form (matching this project's convention elsewhere, e.g.
`OrbitCounting.lean`), for an arbitrary group action. -/
theorem nat_card_orbit_mul_stabilizer {G β : Type*} [Group G] [MulAction G β] (b : β) :
    Nat.card (MulAction.orbit G b) * Nat.card (MulAction.stabilizer G b) = Nat.card G := by
  have h1 : Nat.card (MulAction.orbit G b) = (MulAction.stabilizer G b).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G b)
  rw [h1]
  exact Subgroup.index_mul_card _

/-- Orbit-stabilizer instantiated at a block: if every element of `G` fixes block `i` setwise, and
`p` is a point of block `i`, then `|G|≤|V_i|·|Stab_G(p)|`. -/
theorem card_le_card_block_mul_card_stabilizer {G : Type*} [Group G] [MulAction G Ω]
    (V : ι → Finset Ω) (i : ι) (p : Ω) (hp : p ∈ V i)
    (hfixblock : ∀ g : G, (V i).image (g • ·) = V i) :
    Nat.card G ≤ (V i).card * Nat.card (MulAction.stabilizer G p) := by
  rw [← nat_card_orbit_mul_stabilizer p]
  apply Nat.mul_le_mul_right
  have horb : MulAction.orbit G p ⊆ (V i : Set Ω) := by
    rintro q ⟨g, hg⟩
    have hmem : g • p ∈ (V i).image (g • ·) := Finset.mem_image_of_mem _ hp
    rw [hfixblock g] at hmem
    have hg' : g • p = q := hg
    rwa [hg'] at hmem
  have hle : (MulAction.orbit G p).ncard ≤ ((V i : Set Ω)).ncard :=
    Set.ncard_le_ncard horb (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hle
  exact hle

/-- One full recursive step of (A2a)'s counting argument, chained end-to-end: given `A` permuting
the blocks of `V` and fixing block `u` setwise, a point `p₀∈V_u`, and a point `q` of another block
`j` on `p₀`'s cycle under some `g` centralized by every element of `A`, the stabilizer of `p₀` in
`A` is bounded via block `j`'s orbit-stabilizer step: `|Stab_A(p₀)|≤|V_j|·|Stab_{Stab_A(p₀)}(q)|`.
The chain is: `φ∈Stab_A(p₀)` fixes `p₀`, hence (commuting with `g`) fixes all of `p₀`'s cycle,
hence fixes `q`, hence (`fixed_block_of_fixed_point`) fixes block `j` setwise — so
`card_le_card_block_mul_card_stabilizer` applies again, one block further out. -/
theorem card_stabilizer_le_of_sameCycle {V : ι → Finset Ω} (hpart : IsPartition V)
    {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω} (hcent : ∀ φ ∈ A, Commute φ g)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (p₀ : Ω) {j : ι} {q : Ω} (hq : q ∈ V j)
    (hpq : g.SameCycle p₀ q) :
    Nat.card (MulAction.stabilizer A p₀) ≤
      (V j).card * Nat.card (MulAction.stabilizer (MulAction.stabilizer A p₀) q) := by
  apply card_le_card_block_mul_card_stabilizer V j q hq
  intro ψ
  have hψA : (ψ : Equiv.Perm Ω) ∈ A := ψ.1.2
  have hψp₀ : (ψ : Equiv.Perm Ω) p₀ = p₀ := ψ.2
  have hψq : (ψ : Equiv.Perm Ω) q = q :=
    Perm.fixed_of_commute_of_fixed_point (hcent _ hψA) hψp₀ hpq
  exact fixed_block_of_fixed_point (G := MulAction.stabilizer A p₀) hpart
    (fun φ i => hperm φ φ.1.2 i) ψ hq hψq

/-- If `φ,ψ` both commute with `g` and agree everywhere outside block `V u`, and every point of
`V u` lies on a `g`-cycle also meeting some point outside `V u` (the "mixed cycle" hypothesis of
(A2a)), then `φ,ψ` agree on `V u` too — hence everywhere. This is what lets the tree-rooted
counting injection skip tracking the root block's own residual freedom: every point of `V u`
beyond the one tracked via `card_le_card_block_mul_card_stabilizer` is pinned for free by
propagation from whichever other block its own cycle happens to reach, exactly as
`proofs/ATOMIC_TWO_ROOT_REPAIR.md`'s "an automorphism is determined by the image of the decorated
spanning tree" remark describes. -/
theorem eq_on_block_of_eq_off_block_of_commute {g φ ψ : Equiv.Perm Ω} (hφ : Commute φ g)
    (hψ : Commute ψ g) {V : ι → Finset Ω} {u : ι} (heq : ∀ x ∉ V u, φ x = ψ x)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y) :
    ∀ p ∈ V u, φ p = ψ p := by
  intro p hp
  obtain ⟨y, hy, i, hi⟩ := hmixed p hp
  have hφy : φ y = ψ y := heq y hy
  have h1 : (φ * g ^ i) p = (g ^ i * φ) p := by rw [(hφ.zpow_right i).eq]
  have h2 : (ψ * g ^ i) p = (g ^ i * ψ) p := by rw [(hψ.zpow_right i).eq]
  simp only [Equiv.Perm.mul_apply] at h1 h2
  rw [hi] at h1 h2
  rw [hφy] at h1
  exact (g ^ i).injective (h1.symm.trans h2)

/-- **(A2a)'s tree-rooted counting bound, second half**: given a specific point `q i` in every
block `i≠u`, uniformly fixed by every element of `A`, `A` embeds into the product, over every
other block, of permutations of that block minus its fixed point — giving `|A|≤∏_{i≠u}(R_i-1)!`
directly (with no separate factor for `u`, by `eq_on_block_of_eq_off_block_of_commute` above).
Combined with `card_le_card_block_mul_card_stabilizer` (the `R_u` factor, applied first to reduce
to `A=Stab(p₀)` for a chosen `p₀∈V_u`), this gives the full `|A|≤R_u∏_{i≠u}(R_i-1)!`. What's
still needed to use this in general: establishing the `q i`/`hfixq` hypotheses themselves for
every block, which needs the well-founded spanning-tree induction described above. -/
theorem card_le_prod_factorial_of_fixed_points [Fintype ι] [DecidableEq ι] {V : ι → Finset Ω}
    (hpart : IsPartition V) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j)
    (u : ι) (q : ι → Ω) (hq : ∀ i ≠ u, q i ∈ V i) (hfixq : ∀ i ≠ u, ∀ φ ∈ A, φ (q i) = q i)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y) :
    Nat.card A ≤ ∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1) := by
  have hfixblock : ∀ i ≠ u, ∀ φ ∈ A, (V i).image φ = V i := by
    intro i hi φ hφ
    exact fixed_block_of_fixed_point (G := A) hpart (fun ψ j => hperm ψ ψ.2 j) ⟨φ, hφ⟩
      (hq i hi) (hfixq i hi φ hφ)
  have hiff : ∀ i, i ≠ u → ∀ φ ∈ A, ∀ x : Ω,
      (φ x ∈ V i ∧ φ x ≠ q i) ↔ (x ∈ V i ∧ x ≠ q i) := by
    intro i hi φ hφ x
    have hbl := hfixblock i hi φ hφ
    have hqf := hfixq i hi φ hφ
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x', hx'mem, hx'eq⟩ := Finset.mem_image.mp (hbl ▸ h1)
      refine ⟨(φ.injective hx'eq) ▸ hx'mem, ?_⟩
      intro heq
      apply h2
      rw [heq]
      exact hqf
    · rintro ⟨h1, h2⟩
      refine ⟨hbl ▸ Finset.mem_image_of_mem φ h1, ?_⟩
      intro heq
      exact h2 (φ.injective (heq.trans hqf.symm))
  set toPerm : ∀ φ ∈ A, ∀ i : ι, i ≠ u → Equiv.Perm ↥((V i).erase (q i)) :=
    fun φ hφ i hi => Equiv.Perm.subtypePerm φ (by
      intro x
      simpa [Finset.mem_erase, and_comm] using hiff i hi φ hφ x) with htoPermDef
  have hinj : Function.Injective (fun (φ : A) (i : (Finset.univ.erase u : Finset ι)) =>
      toPerm φ.1 φ.2 i.1 (Finset.mem_erase.mp i.2).1) := by
    rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ hEq
    simp only at hEq
    apply Subtype.ext
    have heqoff : ∀ x ∉ V u, φ x = ψ x := by
      intro x hx
      obtain ⟨i, hxi, -⟩ := hpart x
      have hiu : i ≠ u := by intro h; subst h; exact hx hxi
      by_cases hxq : x = q i
      · rw [hxq]
        exact (hfixq i hiu φ hφ).trans (hfixq i hiu ψ hψ).symm
      · have hxe : x ∈ (V i).erase (q i) := Finset.mem_erase.mpr ⟨hxq, hxi⟩
        have hfun := congrFun hEq ⟨i, Finset.mem_erase.mpr ⟨hiu, Finset.mem_univ i⟩⟩
        have hpt := congrArg (fun e : Equiv.Perm ↥((V i).erase (q i)) => (e ⟨x, hxe⟩ : Ω))
          hfun
        simpa [htoPermDef, Equiv.Perm.subtypePerm_apply] using hpt
    have hon := eq_on_block_of_eq_off_block_of_commute (V := V) (u := u) (hcent φ hφ)
      (hcent ψ hψ) heqoff hmixed
    ext x
    by_cases hxu : x ∈ V u
    · exact hon x hxu
    · exact heqoff x hxu
  have hcardle : Nat.card A ≤
      Nat.card (∀ i : (Finset.univ.erase u : Finset ι), Equiv.Perm ↥((V i.1).erase (q i.1))) :=
    Nat.card_le_card_of_injective _ hinj
  have hcardeq : Nat.card (∀ i : (Finset.univ.erase u : Finset ι),
      Equiv.Perm ↥((V i.1).erase (q i.1))) =
      ∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1) := by
    rw [Nat.card_pi, ← Finset.prod_coe_sort (Finset.univ.erase u)
      (fun i => Nat.factorial ((V i).card - 1))]
    apply Finset.prod_congr rfl
    intro i _
    have hi : i.1 ≠ u := (Finset.mem_erase.mp i.2).1
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe,
      Finset.card_erase_of_mem (hq i.1 hi)]
  rw [← hcardeq]
  exact hcardle

/-- Generalization of `eq_on_block_of_eq_off_block_of_commute` to a *set* `S` of already-fixed
blocks: if `φ,ψ` commute with `g` and agree everywhere outside `⋃i∈S,V i`, and every point of
every block in `S` lies on a `g`-cycle also meeting a point outside `⋃i∈S,V i`, then `φ,ψ` agree
on all of `⋃i∈S,V i` too — hence everywhere. This is what lets the tree-rooted counting induction
process one *layer* of newly-reached blocks at a time, folding them into `S` for the next layer,
instead of needing a single fixed root block. -/
theorem eq_on_blocks_of_eq_off_blocks_of_commute {g φ ψ : Equiv.Perm Ω} (hφ : Commute φ g)
    (hψ : Commute ψ g) {V : ι → Finset Ω} {S : Set ι}
    (heq : ∀ x, (∀ i ∈ S, x ∉ V i) → φ x = ψ x)
    (hmixed : ∀ i ∈ S, ∀ p ∈ V i, ∃ y, (∀ j ∈ S, y ∉ V j) ∧ g.SameCycle p y) :
    ∀ i ∈ S, ∀ p ∈ V i, φ p = ψ p := by
  intro i hi p hp
  obtain ⟨y, hy, k, hk⟩ := hmixed i hi p hp
  have hφy : φ y = ψ y := heq y hy
  have h1 : (φ * g ^ k) p = (g ^ k * φ) p := by rw [(hφ.zpow_right k).eq]
  have h2 : (ψ * g ^ k) p = (g ^ k * ψ) p := by rw [(hψ.zpow_right k).eq]
  simp only [Equiv.Perm.mul_apply] at h1 h2
  rw [hk] at h1 h2
  rw [hφy] at h1
  exact (g ^ k).injective (h1.symm.trans h2)

/-- Generalization of `card_le_prod_factorial_of_fixed_points` to a set `S` of already-processed
blocks: given a specific point `q i` in every block `i∉S`, uniformly fixed by `A`, `A` embeds into
the product of permutations of each block minus its fixed point, provided every point of every
block in `S` also propagates outward (`hmixed`), so agreement on every block outside `S` forces
agreement on `S`'s blocks too via `eq_on_blocks_of_eq_off_blocks_of_commute`. This is the true
per-layer step of (A2a)'s tree-rooted counting bound: `S` plays the role of "everything visited so
far" (initially `{u}`), and each application grows `S` by one layer, shrinking `A` to whatever
fixes the new layer's chosen points, ready for the next application. -/
theorem card_le_prod_factorial_of_fixed_points_layer [Fintype ι] [DecidableEq ι] {V : ι → Finset Ω}
    (hpart : IsPartition V) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j)
    (S : Finset ι) (q : ι → Ω) (hq : ∀ i ∉ S, q i ∈ V i)
    (hfixq : ∀ i ∉ S, ∀ φ ∈ A, φ (q i) = q i)
    (hmixed : ∀ i ∈ S, ∀ p ∈ V i, ∃ y, (∀ j ∈ S, y ∉ V j) ∧ g.SameCycle p y) :
    Nat.card A ≤ ∏ i ∈ Sᶜ, Nat.factorial ((V i).card - 1) := by
  have hfixblock : ∀ i ∉ S, ∀ φ ∈ A, (V i).image φ = V i := by
    intro i hi φ hφ
    exact fixed_block_of_fixed_point (G := A) hpart (fun ψ j => hperm ψ ψ.2 j) ⟨φ, hφ⟩
      (hq i hi) (hfixq i hi φ hφ)
  have hiff : ∀ i, i ∉ S → ∀ φ ∈ A, ∀ x : Ω,
      (φ x ∈ V i ∧ φ x ≠ q i) ↔ (x ∈ V i ∧ x ≠ q i) := by
    intro i hi φ hφ x
    have hbl := hfixblock i hi φ hφ
    have hqf := hfixq i hi φ hφ
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x', hx'mem, hx'eq⟩ := Finset.mem_image.mp (hbl ▸ h1)
      refine ⟨(φ.injective hx'eq) ▸ hx'mem, ?_⟩
      intro heq
      apply h2
      rw [heq]
      exact hqf
    · rintro ⟨h1, h2⟩
      refine ⟨hbl ▸ Finset.mem_image_of_mem φ h1, ?_⟩
      intro heq
      exact h2 (φ.injective (heq.trans hqf.symm))
  set toPerm : ∀ φ ∈ A, ∀ i : ι, i ∉ S → Equiv.Perm ↥((V i).erase (q i)) :=
    fun φ hφ i hi => Equiv.Perm.subtypePerm φ (by
      intro x
      simpa [Finset.mem_erase, and_comm] using hiff i hi φ hφ x) with htoPermDef
  have hinj : Function.Injective (fun (φ : A) (i : (Sᶜ : Finset ι)) =>
      toPerm φ.1 φ.2 i.1 (Finset.mem_compl.mp i.2)) := by
    rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ hEq
    simp only at hEq
    apply Subtype.ext
    have heqoff : ∀ x, (∀ i ∈ S, x ∉ V i) → φ x = ψ x := by
      intro x hx
      obtain ⟨i, hxi, -⟩ := hpart x
      have hiS : i ∉ S := by
        intro hiS
        exact hx i hiS hxi
      by_cases hxq : x = q i
      · rw [hxq]
        exact (hfixq i hiS φ hφ).trans (hfixq i hiS ψ hψ).symm
      · have hxe : x ∈ (V i).erase (q i) := Finset.mem_erase.mpr ⟨hxq, hxi⟩
        have hfun := congrFun hEq ⟨i, Finset.mem_compl.mpr hiS⟩
        have hpt := congrArg (fun e : Equiv.Perm ↥((V i).erase (q i)) => (e ⟨x, hxe⟩ : Ω))
          hfun
        simpa [htoPermDef, Equiv.Perm.subtypePerm_apply] using hpt
    have hon := eq_on_blocks_of_eq_off_blocks_of_commute (V := V) (S := S) (hcent φ hφ)
      (hcent ψ hψ) heqoff hmixed
    ext x
    obtain ⟨i, hxi, hu⟩ := hpart x
    by_cases hiS : i ∈ S
    · exact hon i hiS x hxi
    · apply heqoff x
      intro j hj hxj
      exact hiS ((hu j hxj) ▸ hj)
  have hcardle : Nat.card A ≤
      Nat.card (∀ i : (Sᶜ : Finset ι), Equiv.Perm ↥((V i.1).erase (q i.1))) :=
    Nat.card_le_card_of_injective _ hinj
  have hcardeq : Nat.card (∀ i : (Sᶜ : Finset ι), Equiv.Perm ↥((V i.1).erase (q i.1))) =
      ∏ i ∈ Sᶜ, Nat.factorial ((V i).card - 1) := by
    rw [Nat.card_pi, ← Finset.prod_coe_sort (Sᶜ : Finset ι)
      (fun i => Nat.factorial ((V i).card - 1))]
    apply Finset.prod_congr rfl
    intro i _
    have hi : i.1 ∉ S := Finset.mem_compl.mp i.2
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe,
      Finset.card_erase_of_mem (hq i.1 hi)]
  rw [← hcardeq]
  exact hcardle
