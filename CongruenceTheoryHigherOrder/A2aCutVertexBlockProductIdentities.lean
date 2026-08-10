import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexOuterFiberInduction
import CongruenceTheoryHigherOrder.A2aCutVertexAttachPartition

/-!
**Three structural identities finishing the elimination of (H-cut).** All three are genuine
equalities of finite products (not divisibility surrogates), proved directly from the underlying
`Finset`/quotient structure — no valuation, no `Nat.factorization`, anywhere in this file.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **Identity 1**: a component's island-block product equals its raw `BlockSet` product
(extracted from the inline `hPeq` argument already used in `A2aCutVertexOuterInductionSharp.lean`).
-/
theorem island_prod_eq_blockSet_prod {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (c : BlockComponent V g u) :
    ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
        Nat.factorial ((IslandV g u c i).card - 1) =
      ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1) := by
  have hcardeq : ∀ i : {k : {j : ι // j ≠ u} // Quot.mk (BlockReach V g u) k = c},
      (IslandV g u c (some i)).card = (V i.1.1).card := by
    intro i
    unfold IslandV
    rw [Finset.card_subtype]
    congr 1
    apply Finset.filter_true_of_mem
    intro x hx
    exact Or.inl ⟨i.1, i.2, hx⟩
  have herasenone : (Finset.univ.erase (none : IslandBlockIdx g u c)) =
      (Finset.univ : Finset {k : {j : ι // j ≠ u} // Quot.mk (BlockReach V g u) k = c}).image
        some := by
    apply Finset.ext
    intro x
    rcases x with _ | k
    · simp
    · simp
  rw [herasenone, Finset.prod_image (fun a _ b _ h => Option.some.inj h)]
  simp_rw [hcardeq]
  exact (Finset.prod_subtype (BlockSet g u c) (fun x => mem_blockSet g u c x)
    (fun x => Nat.factorial ((V x.1).card - 1))).symm

/-- **Identity 2**: within a single `compType`-fiber, every component shares the same attachment
count, so the product of attachment factorials over the fiber is a literal power. -/
theorem prod_ambientC0Attach_factorial_eq_pow {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (F : Finset (BlockComponent V g u)) (τ : ℕ × ℕ) (hF : ∀ c ∈ F, compType g u c = τ) :
    ∏ c ∈ F, Nat.factorial (AmbientC0Attach g u c).card = Nat.factorial τ.1 ^ F.card := by
  have hconst : ∀ c ∈ F, Nat.factorial (AmbientC0Attach g u c).card = Nat.factorial τ.1 := by
    intro c hc
    have := hF c hc
    unfold compType at this
    rw [Prod.mk.injEq] at this
    rw [this.1]
  rw [Finset.prod_congr rfl hconst, Finset.prod_const]

/-- **Identity 2, additive form**: the sum of a fiber's attachment counts is `|fiber| * a_τ`. -/
theorem sum_ambientC0Attach_eq_mul {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (F : Finset (BlockComponent V g u)) (τ : ℕ × ℕ) (hF : ∀ c ∈ F, compType g u c = τ) :
    ∑ c ∈ F, (AmbientC0Attach g u c).card = F.card * τ.1 := by
  have hconst : ∀ c ∈ F, (AmbientC0Attach g u c).card = τ.1 := by
    intro c hc
    have := hF c hc
    unfold compType at this
    rw [Prod.mk.injEq] at this
    exact this.1
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]

/-- **Identity 4**: `Finset.univ.erase c0`'s elements group exactly into `compType`-fibers, so
summing (or, via `prod_ambientC0Attach_factorial_eq_pow`, taking products) fiberwise recovers the
sum (product) over the whole erased set. -/
theorem sum_ambientC0Attach_eq_sum_fibers {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) :
    ∑ c ∈ Finset.univ.erase c0, (AmbientC0Attach g u c).card =
      ∑ τ ∈ (Finset.univ.erase c0).image (compType g u),
        ((Finset.univ.erase c0).filter (fun c => compType g u c = τ)).card * τ.1 := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ.erase c0).image (compType g u))
    (g := compType g u) (fun c hc => Finset.mem_image_of_mem _ hc)
    (fun c => (AmbientC0Attach g u c).card)]
  apply Finset.sum_congr rfl
  intro τ hτ
  exact sum_ambientC0Attach_eq_mul g u ((Finset.univ.erase c0).filter (fun c => compType g u c = τ))
    τ (fun c hc => (Finset.mem_filter.mp hc).2)

/-- **Identity 3**: the raw block product over *all* non-root blocks equals the product of `C0`'s
own island contribution together with every other component's, grouped by `compType`-fiber. Proved
via `Finset.prod_fiberwise` on the quotient map `Quot.mk (BlockReach V g u)`, which — because
`BlockComponent` *is* the quotient by that equivalence relation — assigns each non-root block to
*exactly one* component, giving a genuine equality of products over a genuine partition, not merely
a covering. -/
theorem prod_blockSet_partition {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) :
    (∏ i ∈ BlockSet g u c0, Nat.factorial ((V i.1).card - 1)) *
      ∏ c ∈ Finset.univ.erase c0, ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1) =
      ∏ i : {j : ι // j ≠ u}, Nat.factorial ((V i.1).card - 1) := by
  have hfiber : ∏ c : BlockComponent V g u, ∏ i : {k : {j : ι // j ≠ u} //
        Quot.mk (BlockReach V g u) k = c}, Nat.factorial ((V i.1.1).card - 1) =
      ∏ i : {j : ι // j ≠ u}, Nat.factorial ((V i.1).card - 1) :=
    Fintype.prod_fiberwise (Quot.mk (BlockReach V g u))
      (fun i => Nat.factorial ((V i.1).card - 1))
  have hconv : ∀ c : BlockComponent V g u,
      ∏ i : {k : {j : ι // j ≠ u} // Quot.mk (BlockReach V g u) k = c},
        Nat.factorial ((V i.1.1).card - 1) =
      ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1) := by
    intro c
    exact (Finset.prod_subtype (BlockSet g u c) (fun x => mem_blockSet g u c x)
      (fun x => Nat.factorial ((V x.1).card - 1))).symm
  simp_rw [hconv] at hfiber
  rw [← hfiber, ← Finset.mul_prod_erase Finset.univ
    (fun c => ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1)) (Finset.mem_univ c0)]
