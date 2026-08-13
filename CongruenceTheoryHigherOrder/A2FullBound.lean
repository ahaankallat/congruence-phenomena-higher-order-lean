import Mathlib
import CongruenceTheoryHigherOrder.A2MixedBlockStructure
import CongruenceTheoryHigherOrder.A2aValuationBound

/-!
**`thm:atomic-connected-content`'s (A2): the full bound (non-cut-vertex case).** Combining
`A2KernelEmbedding.lean`'s unconditional kernel bound with `A2aValuationBound.lean`'s
`card_le_root_bound_valuation` applied (via `A2MixedBlockStructure.lean`'s transfer facts) to the
range of `restrictToMixed` acting on the mixed points gives the full `(A2)` valuation bound on
`|A|` itself — *given* a root block and connectivity witness for the mixed-points structure
(the one input specific to `\widetilde H=S_q\wr S_r$'s actual structure that this generic
framework does not derive on its own; everything else — block-permutation, centralization, the
exact `|A|=|\mathrm{range}|\cdot|\ker|` factorization, and the kernel's divisibility bound — is
unconditional).
-/

namespace CongruenceTheory

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
  {V : ι → Finset Ω} {A : Subgroup (Equiv.Perm Ω)} {σ : Equiv.Perm Ω}

/-- **The range's valuation bound**, via `card_le_root_bound_valuation` transferred to the mixed
points. -/
theorem range_factorization_le (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (u : ι)
    (hblock_u : ∀ φ' ∈ MonoidHom.range (restrictToMixed hpart hne hperm hcent),
      (MixedBlock V σ u).image φ' = MixedBlock V σ u)
    (p₀ : {x // IsMixed V σ x}) (hp₀ : p₀ ∈ MixedBlock V σ u)
    (hune : (MixedBlock V σ u).Nonempty)
    (hmixed : ∀ q ∈ MixedBlock V σ u, ∃ y ∉ MixedBlock V σ u,
      (sigmaMixed hpart σ).SameCycle q y)
    {j₀ : ι} (hj₀u : j₀ ≠ u) {y₀ : {x // IsMixed V σ x}} (hy₀ : y₀ ∈ MixedBlock V σ j₀)
    (hp₀y₀ : (sigmaMixed hpart σ).SameCycle p₀ y₀)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ MixedBlock V σ i, ∃ y ∈ MixedBlock V σ j,
        (sigmaMixed hpart σ).SameCycle x y)
    {p : ℕ} (hp : p.Prime) :
    (Nat.card (MonoidHom.range (restrictToMixed hpart hne hperm hcent))).factorization p ≤
      1 + ∑ i, (Nat.factorial ((MixedBlock V σ i).card - 1)).factorization p :=
  card_le_root_bound_valuation (isPartition_MixedBlock hpart)
    (mixedBlock_hcent hpart hne hperm hcent) (mixedBlock_hperm hpart hne hperm hcent)
    u hblock_u p₀ hp₀ hune hmixed hj₀u hy₀ hp₀y₀ hconn hp

/-- **Divisibility implies factorization `≤`, at a single prime.** -/
theorem factorization_le_of_dvd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hdvd : a ∣ b) (p : ℕ) :
    a.factorization p ≤ b.factorization p :=
  Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd ha hb).mpr hdvd) p

/-- **`(A2)`'s full bound on `|A|`** (non-cut-vertex case): combining the exact
`|A|=|\mathrm{range}|\cdot|\ker|` factorization, the range's valuation bound, and the kernel's
unconditional divisibility bound. -/
theorem card_A_factorization_le (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (hMixedNe : ∀ i, ∃ x ∈ V i, IsMixed V σ x)
    (u : ι)
    (hblock_u : ∀ φ' ∈ MonoidHom.range (restrictToMixed hpart hne hperm hcent),
      (MixedBlock V σ u).image φ' = MixedBlock V σ u)
    (p₀ : {x // IsMixed V σ x}) (hp₀ : p₀ ∈ MixedBlock V σ u)
    (hune : (MixedBlock V σ u).Nonempty)
    (hmixed : ∀ q ∈ MixedBlock V σ u, ∃ y ∉ MixedBlock V σ u,
      (sigmaMixed hpart σ).SameCycle q y)
    {j₀ : ι} (hj₀u : j₀ ≠ u) {y₀ : {x // IsMixed V σ x}} (hy₀ : y₀ ∈ MixedBlock V σ j₀)
    (hp₀y₀ : (sigmaMixed hpart σ).SameCycle p₀ y₀)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ MixedBlock V σ i, ∃ y ∈ MixedBlock V σ j,
        (sigmaMixed hpart σ).SameCycle x y)
    {p : ℕ} (hp : p.Prime) :
    (Nat.card A).factorization p ≤
      1 + ∑ i, (Nat.factorial ((MixedBlock V σ i).card - 1)).factorization p +
        (∏ i, Nat.factorial (NonMixed V σ i).card).factorization p := by
  have hrange_pos : Nat.card (MonoidHom.range (restrictToMixed hpart hne hperm hcent)) ≠ 0 :=
    Nat.card_pos.ne'
  have hker_pos : Nat.card (MonoidHom.ker (restrictToMixed hpart hne hperm hcent)) ≠ 0 :=
    Nat.card_pos.ne'
  have hprod_pos : (∏ i, Nat.factorial (NonMixed V σ i).card) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)
  have hker_le : (Nat.card (MonoidHom.ker (restrictToMixed hpart hne hperm hcent))).factorization
      p ≤ (∏ i, Nat.factorial (NonMixed V σ i).card).factorization p :=
    factorization_le_of_dvd hker_pos hprod_pos
      (card_ker_dvd_prod_factorial hpart hne hperm hcent hMixedNe) p
  have hrange_le := range_factorization_le hpart hne hperm hcent u hblock_u p₀ hp₀ hune hmixed
    hj₀u hy₀ hp₀y₀ hconn hp
  rw [card_eq_card_range_mul_card_ker hpart hne hperm hcent,
    Nat.factorization_mul hrange_pos hker_pos, Finsupp.add_apply]
  omega

#print axioms range_factorization_le
#print axioms factorization_le_of_dvd
#print axioms card_A_factorization_le

end CongruenceTheory
