import Mathlib
import CongruenceTheoryHigherOrder.A2FullBound
import CongruenceTheoryHigherOrder.PochhammerValuation

/-!
**Bridging `A2FullBound.lean`'s `card_A_factorization_le` to `PochhammerValuation.lean`'s
`hCbound`.** These turn out to match almost exactly: `card_A_factorization_le`'s conclusion is
`1+\sum_i v_p((R_i-1)!) + v_p(\prod_i(\text{NonMixed}_i)!)` for `R_i:=(\text{MixedBlock}_i).card`,
while `hCbound` wants `\sum_i v_p((q-R_i)!)+1+\sum_i v_p((R_i-1)!)`. Given every block has exactly
`q` points (`\text{MixedBlock}_i.card+\text{NonMixed}_i.card=q`, since the two partition block
`i`), these are the *same* quantity — closing the numeric half of `(A2)` entirely, on top of
`A2_valuation_bound`'s own already-complete arithmetic. What remains conditional is exactly what
`card_A_factorization_le` was already conditional on: the root block and connectivity witness,
the one input specific to `\widetilde H`'s actual wreath structure this generic framework does
not derive.
-/

namespace CongruenceTheory

open Equiv
open scoped Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
  {V : ι → Finset Ω} {A : Subgroup (Equiv.Perm Ω)} {σ : Equiv.Perm Ω}

/-- **`MixedBlock` is exactly the mixed-points subtype of `V i`.** -/
theorem mixedBlock_eq_subtype (i : ι) :
    MixedBlock V σ i = (V i).subtype (IsMixedPt V σ) := by
  ext y
  simp [MixedBlock, Finset.mem_subtype]

/-- **`(\text{MixedBlock}_i).card` equals the count of mixed points inside `V i`.** -/
theorem card_mixedBlock_eq_filter (i : ι) :
    (MixedBlock V σ i).card = ((V i).filter (IsMixedPt V σ)).card := by
  rw [mixedBlock_eq_subtype, Finset.card_subtype]

/-- **Mixed and non-mixed points partition each block.** -/
theorem card_mixedBlock_add_nonMixed (i : ι) :
    (MixedBlock V σ i).card + (NonMixed V σ i).card = (V i).card := by
  rw [card_mixedBlock_eq_filter]
  exact Finset.card_filter_add_card_filter_not (s := V i) (IsMixedPt V σ)

/-- **Given every block has `q` points, the non-mixed count is `q` minus the mixed count.** -/
theorem card_nonMixed_eq_sub {q : ℕ} (i : ι) (hVi : (V i).card = q) :
    (NonMixed V σ i).card = q - (MixedBlock V σ i).card := by
  have h := card_mixedBlock_add_nonMixed (V := V) (σ := σ) i
  omega

/-- **`\prod_i(\text{NonMixed}_i)!`'s valuation is the sum of the individual valuations.** -/
theorem factorization_prod_nonMixed_factorial (p : ℕ) :
    (∏ i, Nat.factorial (NonMixed V σ i).card).factorization p =
      ∑ i, (Nat.factorial (NonMixed V σ i).card).factorization p := by
  have h := Nat.factorization_prod (S := (Finset.univ : Finset ι))
    (g := fun i => Nat.factorial (NonMixed V σ i).card)
    (fun i _ => Nat.factorial_ne_zero _)
  exact congrFun (congrArg DFunLike.coe h) p |>.trans (by
    simp [Finsupp.finset_sum_apply])

/-- **`card_A_factorization_le`'s conclusion, reshaped into `PochhammerValuation.lean`'s
`hCbound` exactly**, given every block has `q` points. -/
theorem hCbound_of_card_A (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (hMixedNe : ∀ i, ∃ x ∈ V i, IsMixedPt V σ x)
    (u : ι)
    (hblock_u : ∀ φ' ∈ MonoidHom.range (restrictToMixed hpart hne hperm hcent),
      (MixedBlock V σ u).image φ' = MixedBlock V σ u)
    (p₀ : {x // IsMixedPt V σ x}) (hp₀ : p₀ ∈ MixedBlock V σ u)
    (hune : (MixedBlock V σ u).Nonempty)
    (hmixed : ∀ q ∈ MixedBlock V σ u, ∃ y ∉ MixedBlock V σ u,
      (sigmaMixed hpart σ).SameCycle q y)
    {j₀ : ι} (hj₀u : j₀ ≠ u) {y₀ : {x // IsMixedPt V σ x}} (hy₀ : y₀ ∈ MixedBlock V σ j₀)
    (hp₀y₀ : (sigmaMixed hpart σ).SameCycle p₀ y₀)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ MixedBlock V σ i, ∃ y ∈ MixedBlock V σ j,
        (sigmaMixed hpart σ).SameCycle x y)
    {p q : ℕ} (hp : p.Prime) (hVcard : ∀ i, (V i).card = q) :
    (Nat.card A).factorization p ≤
      (∑ i, (Nat.factorial (q - (MixedBlock V σ i).card)).factorization p) + 1 +
        ∑ i, (Nat.factorial ((MixedBlock V σ i).card - 1)).factorization p := by
  have hmain := card_A_factorization_le hpart hne hperm hcent hMixedNe u hblock_u p₀ hp₀ hune
    hmixed hj₀u hy₀ hp₀y₀ hconn hp
  rw [factorization_prod_nonMixed_factorial] at hmain
  have hrw : ∀ i, (NonMixed V σ i).card = q - (MixedBlock V σ i).card :=
    fun i => card_nonMixed_eq_sub i (hVcard i)
  simp only [hrw] at hmain
  omega

/-- **`(A2)`'s complete numeric bound**: combining `hCbound_of_card_A` with
`PochhammerValuation.lean`'s `A2_valuation_bound`, closing the entire arithmetic content of
`(A2)` — `\mathrm{Fintype.card}\,\iota \cdot v_p(q) + v_p((\mathrm{Fintype.card}\,\iota-2)!) +
v_p(|A|) \le v_p(H)+1` for `H := q!^{\mathrm{Fintype.card}\,\iota}\cdot
(\mathrm{Fintype.card}\,\iota-2)!` — still conditional only on the root/connectivity witness
(the one input specific to `\widetilde H`'s actual wreath structure) and `hVcard` (every block
has `q` points, true by construction for `K_r(q)`). -/
theorem A2_numeric_bound (hpart : IsPartition V) (hne : ∀ i, (V i).Nonempty)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (hcent : ∀ φ ∈ A, Commute φ σ)
    (hMixedNe : ∀ i, ∃ x ∈ V i, IsMixedPt V σ x)
    (u : ι)
    (hblock_u : ∀ φ' ∈ MonoidHom.range (restrictToMixed hpart hne hperm hcent),
      (MixedBlock V σ u).image φ' = MixedBlock V σ u)
    (p₀ : {x // IsMixedPt V σ x}) (hp₀ : p₀ ∈ MixedBlock V σ u)
    (hune : (MixedBlock V σ u).Nonempty)
    (hmixed : ∀ q ∈ MixedBlock V σ u, ∃ y ∉ MixedBlock V σ u,
      (sigmaMixed hpart σ).SameCycle q y)
    {j₀ : ι} (hj₀u : j₀ ≠ u) {y₀ : {x // IsMixedPt V σ x}} (hy₀ : y₀ ∈ MixedBlock V σ j₀)
    (hp₀y₀ : (sigmaMixed hpart σ).SameCycle p₀ y₀)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ MixedBlock V σ i, ∃ y ∈ MixedBlock V σ j,
        (sigmaMixed hpart σ).SameCycle x y)
    {p q : ℕ} (hp : p.Prime) (hVcard : ∀ i, (V i).card = q) :
    (Fintype.card ι) * q.factorization p +
        (Nat.factorial (Fintype.card ι - 2)).factorization p + (Nat.card A).factorization p ≤
      (q.factorial ^ (Fintype.card ι) * Nat.factorial (Fintype.card ι - 2)).factorization p + 1 :=
  by
  haveI := Fact.mk hp
  have hCbound := hCbound_of_card_A hpart hne hperm hcent hMixedNe u hblock_u p₀ hp₀ hune hmixed
    hj₀u hy₀ hp₀y₀ hconn hp hVcard
  have hR1 : ∀ i ∈ (Finset.univ : Finset ι), 1 ≤ (MixedBlock V σ i).card := by
    intro i _
    obtain ⟨x, hx, hxm⟩ := hMixedNe i
    have : (⟨x, hxm⟩ : {y // IsMixedPt V σ y}) ∈ MixedBlock V σ i := by
      simp [MixedBlock, hx]
    exact Finset.card_pos.mpr ⟨_, this⟩
  have hRq : ∀ i ∈ (Finset.univ : Finset ι), (MixedBlock V σ i).card ≤ q := by
    intro i _
    rw [card_mixedBlock_eq_filter, ← hVcard i]
    exact Finset.card_filter_le _ _
  have hHval : (q.factorial ^ (Fintype.card ι) * Nat.factorial (Fintype.card ι - 2)).factorization
      p = (Fintype.card ι) * q.factorial.factorization p +
        (Nat.factorial (Fintype.card ι - 2)).factorization p := by
    rw [Nat.factorization_mul (pow_ne_zero _ (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _), Nat.factorization_pow]
    simp
  exact A2_valuation_bound (p := p) (q := q) (r := Fintype.card ι) (ι := ι)
    (s := Finset.univ) (Finset.card_univ) hR1 hRq hHval hCbound

#print axioms A2_numeric_bound

#print axioms mixedBlock_eq_subtype
#print axioms card_mixedBlock_eq_filter
#print axioms card_mixedBlock_add_nonMixed
#print axioms card_nonMixed_eq_sub
#print axioms factorization_prod_nonMixed_factorial
#print axioms hCbound_of_card_A

end CongruenceTheory
