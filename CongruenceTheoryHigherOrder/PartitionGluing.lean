import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant

/-!
**Building block for `thm:atomic-connected-content`**: a permutation-native realization of
`K_r(q)`'s defining product `∏_{B∈π} C_{|B|q}` (`ConnectedCumulant.lean`), needed as the first
step of the manuscript's own supporting claim (stated right after `K_r(q)`'s definition, not
itself a separately labeled result) that "coefficientwise, `K_r(q)` counts permutations whose
cycle-support hypergraph on `r` prescribed blocks of size `q` is connected."

Label the `rq` points as `Fin r × Fin q` (`r` macroblocks of `q` points each). For a macroblock
`B ⊆ Fin r`, `blockType B := {x : Fin r × Fin q // x.1 ∈ B}` is the merged label subtype of size
`|B|·q` (`card_blockType`, via Mathlib's `Equiv.prodSubtypeFstEquivSubtypeProd`). A `PartitionPerm
τ` (for `τ` a partition of `[r]`, i.e. `PartLat r` from `ConnectedCumulant.lean`) is a tuple of
independent permutations, one per macroblock of `τ`, each acting on its own `blockType B`; its
`ciProd := ∏_B ci(p B)` is the combined cycle-indicator monomial.

**`prod_C_eq_sum_ciProd`**: `∏_{B∈τ.parts} C(|B|q) = ∑_{p:PartitionPerm τ} p.ciProd`, purely
algebraically (`Fintype.prod_sum`, "a product of sums is a sum of products") — no gluing into an
actual single permutation of `Fin r × Fin q` is needed for this half.

**`assemble`**: glues a `PartitionPerm τ` into one actual permutation of the full label space
`Fin r × Fin q`, by extending each block's permutation to fix every point outside its own block
(`extendB`, via Mathlib's `Equiv.Perm.extendDomain`) and combining the (pairwise-disjoint, hence
commuting) results via `Finset.noncommProd`. **`ci_assemble`** is the main theorem: `ci` is
multiplicative over this gluing, `ci(assemble p) = p.ciProd` — a genuine generalization of
`CpermEqC.lean`'s `ci_sumCongr` (there, binary gluing over `m ⊕ n`; here, gluing over an arbitrary
finite partition of `Fin r`) via Mathlib's `Equiv.Perm.Disjoint.cycleType_noncommProd` and
`Equiv.Perm.cycleType_extendDomain`, plus two small helper lemmas (`multiset_sum_sum`,
`multiset_prod_map_sum`) distributing `Multiset.sum`/`.map _ |>.prod` over a `Finset`-indexed sum
of multisets.

**Honest scope note**: this connects `K_r(q)`'s definition to actual permutation combinatorics
one layer down, but does **not** yet reach the "counts connected permutations" claim itself —
that needs `assemble` shown to biject `PartitionPerm τ` with exactly the permutations respecting
`τ`'s block structure, a canonical "cycle-support connectivity partition" `π(g)` for each
permutation `g`, and a Möbius-inversion argument over `PartLat r` identifying `K_r(q)` with the
sum of `ci g` over `g` with `π(g) = ⊤`. None of that — nor any part of `thm:atomic-connected-content`
itself (the wreath-product stabilizer bounds, the incidence-graph automorphism induction, the
mod-`p` algebraic independence argument, or Lucas' theorem) — is attempted here.
-/

namespace CongruenceTheory

open scoped Classical

variable {r q : ℕ}

/-- The label subtype for a macroblock `B ⊆ Fin r`: all `(i,k) : Fin r × Fin q` with `i ∈ B`. -/
abbrev blockType (B : Finset (Fin r)) := {x : Fin r × Fin q // x.1 ∈ B}

noncomputable instance instFintypeBlockType (B : Finset (Fin r)) :
    Fintype (blockType (q := q) B) := by unfold blockType; infer_instance

/-- `blockType B ≃ ↥B × Fin q`. -/
def blockTypeEquiv (B : Finset (Fin r)) : blockType (q := q) B ≃ (↥B × Fin q) :=
  Equiv.prodSubtypeFstEquivSubtypeProd (p := fun i : Fin r => i ∈ B)

/-- `blockType B` has cardinality `|B| * q`. -/
theorem card_blockType (B : Finset (Fin r)) :
    Fintype.card (blockType (q := q) B) = B.card * q := by
  rw [Fintype.card_congr (blockTypeEquiv (q := q) B), Fintype.card_prod, Fintype.card_coe,
    Fintype.card_fin]

/-- A tuple of permutations `(p_B)_{B∈τ.parts}`, one per macroblock of `τ`, each acting on its
own merged label subtype `blockType B`. -/
def PartitionPerm (τ : PartLat r) :=
  ∀ B : τ.parts, Equiv.Perm (blockType (q := q) (B : Finset (Fin r)))

noncomputable instance (τ : PartLat r) : Fintype (PartitionPerm (q := q) τ) := by
  unfold PartitionPerm; infer_instance

/-- The combined cycle-indicator monomial `∏_B ci(p B)`. -/
noncomputable def PartitionPerm.ciProd {τ : PartLat r} (p : PartitionPerm (q := q) τ) :
    MvPolynomial ℕ ℤ :=
  ∏ B : τ.parts, ci (p B)

/-- **`∏_{B∈τ.parts} C(|B|q)` equals the sum of `ciProd` over all block-permutation tuples**,
purely algebraically (no gluing into a single permutation needed): a direct instance of
"a product of sums is a sum of products" (`Fintype.prod_sum`), combined per-block with
`Cperm_eq_sum_of_card_eq`/`Cperm_eq_C`. -/
theorem prod_C_eq_sum_ciProd (τ : PartLat r) :
    ∏ B ∈ τ.parts, C (B.card * q) = ∑ p : PartitionPerm (q := q) τ, p.ciProd := by
  have hstep : ∀ B : τ.parts, C ((B : Finset (Fin r)).card * q) =
      ∑ g : Equiv.Perm (blockType (q := q) (B : Finset (Fin r))), ci g := by
    intro B
    rw [← Cperm_eq_C]
    exact Cperm_eq_sum_of_card_eq (card_blockType (B : Finset (Fin r)))
  rw [show (∏ B ∈ τ.parts, C (B.card * q)) = ∏ B : τ.parts, C ((B : Finset (Fin r)).card * q) from
    (Finset.prod_attach τ.parts (fun B => C (B.card * q))).symm]
  rw [Finset.prod_congr rfl (fun B _ => hstep B)]
  exact Fintype.prod_sum _

/-- Extend a single block's permutation to all of `Fin r × Fin q`, fixing every point outside
that block. -/
noncomputable def extendB {τ : PartLat r} (p : PartitionPerm (q := q) τ) (B : τ.parts) :
    Equiv.Perm (Fin r × Fin q) :=
  Equiv.Perm.extendDomain (p B) (Equiv.refl (blockType (q := q) (B : Finset (Fin r))))

theorem extendB_disjoint {τ : PartLat r} (p : PartitionPerm (q := q) τ) {B1 B2 : τ.parts}
    (h : B1 ≠ B2) : Equiv.Perm.Disjoint (extendB p B1) (extendB p B2) := by
  intro x
  by_cases hx1 : x.1 ∈ (B1 : Finset (Fin r))
  · right
    have hx2 : x.1 ∉ (B2 : Finset (Fin r)) := by
      intro hx2
      exact h (Subtype.ext (τ.eq_of_mem_parts B1.2 B2.2 hx1 hx2))
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hx2
  · left
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hx1

/-- The permutation of `Fin r × Fin q` assembled by gluing the block permutations of `p`
independently on each block of `τ`, fixing nothing (every point lies in exactly one block). -/
noncomputable def assemble {τ : PartLat r} (p : PartitionPerm (q := q) τ) :
    Equiv.Perm (Fin r × Fin q) :=
  τ.parts.attach.noncommProd (fun B => extendB p B)
    (fun B1 _ B2 _ hne => (extendB_disjoint p hne).commute)

theorem cycleType_assemble {τ : PartLat r} (p : PartitionPerm (q := q) τ) :
    (assemble p).cycleType = ∑ B : τ.parts, (p B).cycleType := by
  unfold assemble
  rw [Equiv.Perm.Disjoint.cycleType_noncommProd]
  · exact Finset.sum_congr rfl (fun B _ => Equiv.Perm.cycleType_extendDomain _)
  · exact fun B1 _ B2 _ hne => extendB_disjoint p hne

theorem card_eq_sum_card_blockType (τ : PartLat r) :
    Fintype.card (Fin r × Fin q) =
      ∑ B : τ.parts, Fintype.card (blockType (q := q) (B : Finset (Fin r))) := by
  simp_rw [card_blockType]
  rw [Finset.sum_coe_sort τ.parts (fun B => B.card * q), ← Finset.sum_mul, τ.sum_card_parts]
  simp

/-- `(∑ i ∈ s, m i).sum = ∑ i ∈ s, (m i).sum`, i.e. `Multiset.sum` distributes over a
`Finset`-indexed sum of multisets. -/
theorem multiset_sum_sum {ι : Type*} (s : Finset ι) (m : ι → Multiset ℕ) :
    (∑ i ∈ s, m i).sum = ∑ i ∈ s, (m i).sum := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Multiset.sum_add, ih]

/-- `((∑ i ∈ s, m i).map f).prod = ∏ i ∈ s, ((m i).map f).prod`, i.e. mapping then taking the
product turns a `Finset`-indexed sum of multisets into a product. -/
theorem multiset_prod_map_sum {ι : Type*} (s : Finset ι) (m : ι → Multiset ℕ)
    (f : ℕ → MvPolynomial ℕ ℤ) :
    ((∑ i ∈ s, m i).map f).prod = ∏ i ∈ s, ((m i).map f).prod := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Multiset.map_add, Multiset.prod_add, Finset.prod_insert hi, ih]

/-- **`ci` is multiplicative over `assemble`**: the cycle-indicator monomial of the glued
permutation is the product of the individual blocks' monomials, matching `ci_sumCongr`'s binary
gluing lemma (`CpermEqC.lean`) generalized to an arbitrary partition. -/
theorem ci_assemble {τ : PartLat r} (p : PartitionPerm (q := q) τ) :
    ci (assemble p) = p.ciProd := by
  unfold ci PartitionPerm.ciProd
  rw [cycleType_assemble, card_eq_sum_card_blockType (q := q) τ]
  have hle : ∀ B : τ.parts,
      (p B).cycleType.sum ≤ Fintype.card (blockType (q := q) (B : Finset (Fin r))) :=
    fun B => Equiv.Perm.sum_cycleType_le (p B)
  rw [show (∑ B : τ.parts, Fintype.card (blockType (q := q) (B : Finset (Fin r)))) -
      (∑ B : τ.parts, (p B).cycleType).sum =
      ∑ B : τ.parts, (Fintype.card (blockType (q := q) (B : Finset (Fin r))) - (p B).cycleType.sum) by
    rw [multiset_sum_sum, Finset.sum_tsub_distrib _ (fun B _ => hle B)]]
  rw [← Finset.prod_pow_eq_pow_sum, multiset_prod_map_sum, ← Finset.prod_mul_distrib]
  rfl

end CongruenceTheory
