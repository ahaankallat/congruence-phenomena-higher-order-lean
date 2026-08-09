import Mathlib

/-!
**Lemma `lem:uniform-hypertree-enumerator`** ("Uniform-hypertree Prüfer enumerator"), the key
combinatorial tool `thm:atomic-connected-content` needs to evaluate the connected cumulant
`K_r(q)` (`ConnectedCumulant.lean`) in closed form. For `h≥2`, `d≥1`, `r=1+d(h-1)`, and labelled
`h`-uniform hypertrees `T` on `[r]`:
```
  ∑_T ∏_{i=1}^r x_i^{deg_T(i)-1} = (r-1)!/(d!(h-1)!^d) · (x_1+⋯+x_r)^{d-1}.
```
The manuscript's own proof is bijective: root at a fixed vertex, repeatedly strip a leaf
hyperedge (its `h-1` non-root vertices form a "block", its one vertex toward the root is the
"petiole"), producing an unordered partition of the non-root vertices into `d` blocks of size
`h-1` plus an ordered word of `d-1` petiole values — with vertex `i`'s degree exactly `1 +`
its count in the word.

**What's formalized**: `HyperTreeData r h d root`, the Prüfer-recipe data itself (an *ordered*
sequence of `d` disjoint `(h-1)`-blocks, `OrderedBlocks`, together with the petiole word),
defined directly via this recipe — matching the bijection the manuscript's own proof
constructs — rather than independently via general hypergraph connectivity/acyclicity axioms
(Mathlib's `Combinatorics/Hypergraph/Basic.lean` has only bare vertex/edge-set definitions, with
no connectivity, tree, uniformity, or Prüfer-sequence support to build on; this codebase found no
existing Mathlib scaffolding for tree/hypertree enumeration of any kind, not even for ordinary
graphs). `card_orderedBlocks_mul` counts `OrderedBlocks` exactly (`(dk)! = (count)·k!^d`, proved
by peeling one block at a time and combining `Nat.choose_mul_factorial_mul_factorial` with the
inductive count for the remainder — the *ordered* count, avoiding the unordered-partition
`/d!` entirely). `hypertree_enumerator` is the full generating-function identity: the degree is
read directly off the word (`data.2 i`), and the identity follows by splitting the sum over
`HyperTreeData` (block choice × word, via `Fintype.sum_prod_type'`) and applying
`Fintype.sum_pow` for the word part's power expansion. Stated in multiplied form
(`× (h-1)!^d`) throughout to avoid natural-number division.

**Honest scope note**: what remains for `thm:atomic-connected-content` itself is relating this
identity to the actual cycle-index coefficients of `K_r(q)` — the manuscript's own separate claim
that "`K_r(q)` counts permutations whose cycle-support hypergraph on `r` prescribed blocks is
connected" — a further substantial combinatorial argument connecting permutation cycle structure
to hypergraph connectivity, not attempted here.
-/

namespace CongruenceTheory

open scoped Classical

/-- An ordered sequence of `d` pairwise-disjoint `k`-element subsets of a finite type `α`,
built recursively (peeling one block at a time from the remaining available elements),
mirroring `CycleTuple`'s technique (`CpermEqC.lean`). -/
def OrderedBlocks (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) : ℕ → Type _
  | 0 => PUnit
  | d + 1 => Σ B : {B : Finset α // B.card = k}, OrderedBlocks {x : α // x ∉ B.1} k d

noncomputable def instFintypeOrderedBlocks (k : ℕ) :
    ∀ (d : ℕ) (α : Type*) [Fintype α] [DecidableEq α], Fintype (OrderedBlocks α k d)
  | 0, α, _, _ => by unfold OrderedBlocks; infer_instance
  | d + 1, α, _, _ => by
      unfold OrderedBlocks
      haveI : ∀ B : {B : Finset α // B.card = k}, Fintype (OrderedBlocks {x : α // x ∉ B.1} k d) :=
        fun B => instFintypeOrderedBlocks k d {x : α // x ∉ B.1}
      infer_instance

noncomputable instance (α : Type*) [Fintype α] [DecidableEq α] (k d : ℕ) :
    Fintype (OrderedBlocks α k d) := instFintypeOrderedBlocks k d α

/-- **Exact count of `OrderedBlocks`**, in multiplied form: `(count) · k!^d = (dk)!`. -/
theorem card_orderedBlocks_mul (k : ℕ) : ∀ (d : ℕ) (α : Type*) [Fintype α] [DecidableEq α],
    Fintype.card α = d * k → Fintype.card (OrderedBlocks α k d) * (Nat.factorial k) ^ d =
      Nat.factorial (d * k)
  | 0, α, _, _, _ => by simp [OrderedBlocks]
  | d + 1, α, _, _, hcard => by
      unfold OrderedBlocks
      rw [Fintype.card_sigma, Finset.sum_mul]
      have hterm : ∀ B : {B : Finset α // B.card = k},
          Fintype.card (OrderedBlocks {x : α // x ∉ B.1} k d) * (Nat.factorial k) ^ (d + 1) =
            Nat.factorial (d * k) * Nat.factorial k := by
        intro B
        have hcompl : Fintype.card {x : α // x ∉ B.1} = d * k := by
          have h2 := Fintype.card_subtype_compl (fun x : α => x ∈ B.1)
          rw [h2, Fintype.card_coe, B.2, hcard]
          have : (d + 1) * k = d * k + k := by ring
          omega
        have hrec := card_orderedBlocks_mul k d {x : α // x ∉ B.1} hcompl
        rw [pow_succ, ← mul_assoc, hrec]
      rw [Finset.sum_congr rfl (fun B _ => hterm B)]
      rw [Finset.sum_const, smul_eq_mul]
      rw [show (Finset.univ : Finset {B : Finset α // B.card = k}).card =
          Fintype.card {B : Finset α // B.card = k} from rfl]
      have hchoose : Fintype.card {B : Finset α // B.card = k} = (Fintype.card α).choose k := by
        rw [Fintype.card_subtype]
        rw [show (Finset.univ.filter (fun B : Finset α => B.card = k)) =
            Finset.univ.powersetCard k from by
          ext B; simp [Finset.mem_powersetCard]]
        rw [Finset.card_powersetCard]
        simp
      rw [hchoose, hcard]
      have hnk : (d + 1) * k - k = d * k := by
        have : (d + 1) * k = d * k + k := by ring
        omega
      have hchoosefact :
          ((d + 1) * k).choose k * Nat.factorial k * Nat.factorial ((d + 1) * k - k) =
            Nat.factorial ((d + 1) * k) :=
        Nat.choose_mul_factorial_mul_factorial (by
          have : (d + 1) * k = d * k + k := by ring
          omega)
      rw [hnk] at hchoosefact
      rw [show ((d + 1) * k).choose k * (Nat.factorial (d * k) * Nat.factorial k) =
          ((d + 1) * k).choose k * Nat.factorial k * Nat.factorial (d * k) by ring]
      exact hchoosefact

variable {r h d : ℕ} (root : Fin r)

/-- The Prüfer-recipe data for a labelled `h`-uniform hypertree on `[r]` rooted at `root`:
an ordered sequence of `d` disjoint `(h-1)`-blocks partitioning the non-root points, plus a
word of `d-1` petiole values. Defined directly via this recipe (matching the bijection the
manuscript's own proof constructs) rather than independently via general hypergraph
connectivity/acyclicity axioms. -/
abbrev HyperTreeData (r h d : ℕ) (root : Fin r) :=
  OrderedBlocks {x : Fin r // x ≠ root} (h - 1) d × (Fin (d - 1) → Fin r)

theorem hyperTreeData_compl_card (hr : r = 1 + d * (h - 1)) :
    Fintype.card {x : Fin r // x ≠ root} = d * (h - 1) := by
  have h2 := Fintype.card_subtype_compl (fun x : Fin r => x = root)
  simp only [Fintype.card_fin] at h2
  have hone : Fintype.card {x : Fin r // x = root} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨root, rfl⟩, fun ⟨x, hx⟩ => Subtype.ext hx⟩
  rw [hone] at h2
  show Fintype.card {x : Fin r // ¬ x = root} = d * (h - 1)
  omega

/-- **The uniform-hypertree Prüfer enumerator** (`lem:uniform-hypertree-enumerator`): the
degree-generating-function identity for `h`-uniform hypertrees, established directly via the
Prüfer-recipe data `HyperTreeData` (existence of the bijection with actual hypertrees is the
manuscript's own content; what's proved here is the resulting generating-function identity for
the recipe data itself). Stated in multiplied form (`× (h-1)!^d`) to avoid natural-number
division. -/
theorem hypertree_enumerator {R : Type*} [CommSemiring R] (hr : r = 1 + d * (h - 1))
    (x : Fin r → R) :
    (∑ data : HyperTreeData r h d root, ∏ i : Fin (d - 1), x (data.2 i)) *
        (Nat.factorial (h - 1) : R) ^ d =
      (Nat.factorial (d * (h - 1)) : R) * (∑ v, x v) ^ (d - 1) := by
  have hblocks := card_orderedBlocks_mul (h - 1) d {x : Fin r // x ≠ root}
    (hyperTreeData_compl_card root hr)
  unfold HyperTreeData
  rw [show (∑ data : OrderedBlocks {x : Fin r // x ≠ root} (h - 1) d × (Fin (d - 1) → Fin r),
        ∏ i : Fin (d - 1), x (data.2 i)) =
      ∑ _b : OrderedBlocks {x : Fin r // x ≠ root} (h - 1) d,
        ∑ w : Fin (d - 1) → Fin r, ∏ i : Fin (d - 1), x (w i) from
    Fintype.sum_prod_type'
      (fun (_ : OrderedBlocks {x : Fin r // x ≠ root} (h - 1) d) (w : Fin (d - 1) → Fin r) =>
        ∏ i : Fin (d - 1), x (w i))]
  have hword : ∑ w : Fin (d - 1) → Fin r, ∏ i : Fin (d - 1), x (w i) = (∑ v, x v) ^ (d - 1) :=
    (Fintype.sum_pow x (d - 1)).symm
  rw [show (∑ _b : OrderedBlocks {x : Fin r // x ≠ root} (h - 1) d,
        ∑ w : Fin (d - 1) → Fin r, ∏ i : Fin (d - 1), x (w i)) =
      (Fintype.card (OrderedBlocks {x : Fin r // x ≠ root} (h - 1) d) : R) *
        (∑ v, x v) ^ (d - 1) by
    rw [Finset.sum_congr rfl (fun _ _ => hword)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
  rw [mul_right_comm]
  rw [show (Fintype.card (OrderedBlocks {x : Fin r // x ≠ root} (h - 1) d) : R) *
      (Nat.factorial (h - 1) : R) ^ d = (Nat.factorial (d * (h - 1)) : R) by
    rw [← Nat.cast_pow, ← Nat.cast_mul, hblocks]]

end CongruenceTheory
