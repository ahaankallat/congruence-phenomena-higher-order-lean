import Mathlib
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aLayerInduction

/-!
**The complete general-depth well-founded induction for (A2a)'s tree-rooted counting bound.**
`A2aLayerInduction.lean` supplied every ingredient the recursion needs — the kernel-factorization
layer step and the propagation fact showing the resulting subgroup uniformly fixes the next
layer's points — but stopped short of actually assembling them into an induction. This file
supplies that assembly: **`key_induction`**, proved by well-founded induction on the number of
unprocessed blocks, is a complete, general theorem (not tied to a single root `u`):

Given a partition `V` of `Ω`, a permutation `g`, and connectivity (`hconn`: every proper nonempty
"processed" set `L` of blocks has an edge leaving it — some block `i∈L` and `j∉L` linked by a
shared `g`-cycle), if a subgroup `A` (permuting blocks, commuting with `g`) fixes every point of
every block already in a nonempty `L`, then `|A|≤∏_{i∉L}(R_i-1)!`.

**Proof**: well-founded induction on `(Finset.univ∖L).card`. Base case `L=univ`: `A` fixes every
point of `Ω`, hence (`Equiv.Perm.ext`) `A` is trivial, and the empty product is `1`. Inductive
step: `hconn` gives a boundary edge `(i,j,x,y)` with `i∈L`, `j∉L`, `x∈V i`, `y∈V j`,
`g.SameCycle x y`; since `A` fixes `x` (as `x∈V i`, `i∈L`), `Perm.fixed_of_commute_of_fixed_point`
gives `A` fixes `y` too; `card_le_prod_factorial_mul_card_fixBlocks` (with the singleton layer
`{j}`) gives `|A|≤(R_j-1)!·|FixBlocks A V {j}|`; `FixBlocks A V {j}` still fixes everything `L`
fixed (being `≤A`) plus all of `V j` (by construction) — exactly the invariant needed to recurse
into `L∪{j}`, one block closer to `Finset.univ`. The telescoping product
`(R_j-1)!·∏_{i∈(L∪{j})ᶜ}(R_i-1)! = ∏_{i∈Lᶜ}(R_i-1)!` closes the step.

**Honest scope note — precisely what remains to reach the manuscript's literal
`|A|≤R_u∏_{i≠u}(R_i-1)!`**: `key_induction`'s invariant requires `A` to fix *every* point of the
seed block(s) in `L`, not just one. Instantiating with `L={u}` therefore needs `A` to already fix
all of `V_u` pointwise — but the natural starting group after orbit-stabilizer
(`card_le_card_block_mul_card_stabilizer`) is `Stab_A(p₀)`, which only fixes the single point
`p₀∈V_u`, not the rest of `V_u`. Resolving this needs the same "residual root freedom is pinned
for free by propagation from elsewhere" argument that
`eq_on_block_of_eq_off_block_of_commute`/`card_le_prod_factorial_of_fixed_points` use for the
depth-1 case, adapted to feed into `key_induction` rather than replace it — not attempted here.
`key_induction` itself is nonetheless a complete, general, and substantial theorem in its own
right, independent of this remaining connective step. Also not attempted: establishing `hconn`
from the manuscript's "connected block-support hypergraph" hypothesis (a translation step, not a
new mathematical difficulty), and the "`u` is a cut vertex" case of (A2a) (component-type
grouping).
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **The complete general-depth tree-rooted counting bound for (A2a)'s "not a cut vertex" case.**
Given `A` fixes every point of every block already in `L`, and connectivity (`hconn`: every proper
nonempty processed set `L` has an edge leaving it, via a shared cycle), `|A| ≤ ∏_{i∉L}(R_i-1)!`.
Proved by strong induction on the number of unprocessed blocks: peel one edge (block `j`) off via
`hconn`, propagate `A`'s fixed points to `j` via `Perm.fixed_of_commute_of_fixed_point`, apply
`card_le_prod_factorial_mul_card_fixBlocks` to bound `|A|` by `(R_j-1)!·|FixBlocks A V {j}|`, and
recurse into `FixBlocks A V {j}` (which still fixes everything `L` fixed, plus `j`) with `L∪{j}`. -/
theorem key_induction {V : ι → Finset Ω} (hpart : IsPartition V) {g : Perm Ω}
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y) :
    ∀ n : ℕ, ∀ L : Finset ι, (Finset.univ \ L).card ≤ n → L.Nonempty →
    ∀ A : Subgroup (Perm Ω), (∀ φ ∈ A, Commute φ g) →
    (∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) →
    (∀ i ∈ L, ∀ x ∈ V i, ∀ φ ∈ A, φ x = x) →
    Nat.card A ≤ ∏ i ∈ Lᶜ, Nat.factorial ((V i).card - 1) := by
  intro n
  induction n with
  | zero =>
    intro L hLcard hLne A hcent hperm hfix
    have hLuniv : L = Finset.univ := by
      have h0 : (Finset.univ \ L).card = 0 := Nat.le_zero.mp hLcard
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at h0
      exact (Finset.subset_univ L).antisymm h0
    have hAtriv : ∀ φ ∈ A, φ = 1 := by
      intro φ hφ
      apply Equiv.Perm.ext
      intro x
      obtain ⟨i, hi, -⟩ := hpart x
      exact hfix i (hLuniv ▸ Finset.mem_univ i) x hi φ hφ
    have hLc : (Lᶜ : Finset ι) = ∅ := by rw [hLuniv]; simp
    rw [hLc]
    simp only [Finset.prod_empty]
    haveI : Subsingleton A := ⟨fun a b => Subtype.ext ((hAtriv a a.2).trans (hAtriv b b.2).symm)⟩
    calc Nat.card A ≤ Nat.card Unit := Nat.card_le_card_of_injective (fun _ => ())
          (fun a b _ => Subsingleton.elim a b)
      _ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨()⟩⟩
  | succ n ih =>
    intro L hLcard hLne A hcent hperm hfix
    by_cases hLuniv : L = Finset.univ
    · have hAtriv : ∀ φ ∈ A, φ = 1 := by
        intro φ hφ
        apply Equiv.Perm.ext
        intro x
        obtain ⟨i, hi, -⟩ := hpart x
        exact hfix i (hLuniv ▸ Finset.mem_univ i) x hi φ hφ
      have hLc : (Lᶜ : Finset ι) = ∅ := by rw [hLuniv]; simp
      rw [hLc]
      simp only [Finset.prod_empty]
      haveI : Subsingleton A :=
        ⟨fun a b => Subtype.ext ((hAtriv a a.2).trans (hAtriv b b.2).symm)⟩
      calc Nat.card A ≤ Nat.card Unit := Nat.card_le_card_of_injective (fun _ => ())
            (fun a b _ => Subsingleton.elim a b)
        _ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨()⟩⟩
    · obtain ⟨i, hiL, j, hjL, x, hx, y, hy, hxy⟩ := hconn L hLne hLuniv
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
      have hcard' : (Finset.univ \ (insert j L)).card ≤ n := by
        have hsub : Finset.univ \ (insert j L) = (Finset.univ \ L).erase j := by
          ext k
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
            not_or, Finset.mem_erase]
        rw [hsub]
        have hjmem : j ∈ Finset.univ \ L := by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]; exact hjL
        have := Finset.card_erase_of_mem hjmem
        omega
      have hLne' : (insert j L).Nonempty := ⟨j, Finset.mem_insert_self j L⟩
      have hcentker : ∀ φ ∈ FixBlocks A V ({j} : Finset ι), Commute φ g := fun φ hφ =>
        hcent φ (mem_FixBlocks.mp hφ).1
      have hpermker : ∀ φ ∈ FixBlocks A V ({j} : Finset ι), ∀ i0, ∃ j0, (V i0).image φ = V j0 :=
        fun φ hφ => hperm φ (mem_FixBlocks.mp hφ).1
      have hrec := ih (insert j L) hcard' hLne' (FixBlocks A V {j}) hcentker hpermker hfix'
      have hcompl : (insert j L)ᶜ = Lᶜ.erase j := by
        ext k
        simp only [Finset.mem_compl, Finset.mem_insert, not_or, Finset.mem_erase]
      rw [hcompl] at hrec
      have hjLc : j ∈ Lᶜ := by simp only [Finset.mem_compl]; exact hjL
      rw [← Finset.mul_prod_erase Lᶜ (fun i0 => Nat.factorial ((V i0).card - 1)) hjLc]
      calc Nat.card A ≤ Nat.factorial ((V j).card - 1) * Nat.card (FixBlocks A V {j}) := hstep
        _ ≤ Nat.factorial ((V j).card - 1) * ∏ i0 ∈ Lᶜ.erase j, Nat.factorial ((V i0).card - 1) :=
            Nat.mul_le_mul_left _ hrec
