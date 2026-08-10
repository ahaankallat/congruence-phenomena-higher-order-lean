import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexFullValuation
import CongruenceTheoryHigherOrder.A2aCutVertexMultinomialAbsorption
import CongruenceTheoryHigherOrder.A2aCutVertexAttachPartition
import CongruenceTheoryHigherOrder.A2aCutVertexBlockProductIdentities

/-!
**(A2a)'s cut-vertex case, unconditional.** Eliminates (H-cut) entirely: the manuscript's
grouping of branches by `compType` never needed to match true rooted-isomorphism type, because
(A2a) itself only ever needs an *upper* bound on `v_p(|A|)`, and the root multinomial absorption
(`multinomial_absorption`) is a pure arithmetic fact about labeled-item/repeated-group-size
multinomial coefficients, indifferent to what the grouping index denotes. This file combines it
with `factorization_card_le_cutVertex_full_bound` and the structural equalities of
`A2aCutVertexBlockProductIdentities.lean`/`A2aCutVertexAttachPartition.lean` to reach the
manuscript's own uniform display, `v_p(|A|) ≤ 1+Σ_i v_p((R_i-1)!)`, matching (A2a) exactly as
stated for the non-cut-vertex case.

**Proof discipline**: every step below is either an equality of finite products/sums (established
before any `Nat.factorization` is taken) or the *single* divisibility-to-valuation conversion at
`multinomial_absorption` itself. No other `A ≤ B ⟹ v_p(A) ≤ v_p(B)` inference occurs anywhere.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **(A2a), cut-vertex case, unconditional.** -/
theorem factorization_card_le_cutVertex_unconditional {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {j2 : ι} (hj2u : j2 ≠ u)
    (hblock_j2 : ∀ φ ∈ A, (V j2).image φ = V j2) {p₀ : Ω} (hp₀u : p₀ ∈ V u)
    (hp₀reach : Reaches g u p₀ (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩))
    (hne_attach : ∀ c : BlockComponent V g u, (AmbientC0Attach g u c).Nonempty)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    {p : ℕ} (hp : p.Prime) :
    (Nat.card A).factorization p ≤
      1 + (Nat.factorial ((V u).card - 1)).factorization p +
        ∑ i : {i : ι // i ≠ u}, (Nat.factorial ((V i.1).card - 1)).factorization p := by
  set c0 := Quot.mk (BlockReach V g u) (⟨j2, hj2u⟩ : {i : ι // i ≠ u}) with hc0def
  set a0 := (AmbientC0Attach g u c0).card with ha0def
  set T := (Finset.univ.erase c0).image (compType g u) with hTdef
  set a : ℕ × ℕ → ℕ := fun τ => τ.1 with hadef
  set m : ℕ × ℕ → ℕ := fun τ =>
      ((Finset.univ.erase c0).filter (fun c => compType g u c = τ)).card with hmdef
  have hbase : (Nat.card A).factorization p ≤
      1 + (Nat.factorial (a0 - 1)).factorization p +
        (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
            Nat.factorial ((IslandV g u c0 i).card - 1)).factorization p +
        (∏ τ ∈ T, Nat.factorial (m τ) *
            (∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
              Nat.factorial (AmbientC0Attach g u c).card) *
            (∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
              ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
                Nat.factorial ((IslandV g u c i).card - 1))).factorization p :=
    factorization_card_le_cutVertex_full_bound hpart hne hcent hperm hblock_u hj2u
      hblock_j2 hp₀u hp₀reach hne_attach hmixed hp
  -- The τ-fiber attachment product is a literal power (Identity 2).
  have hpow : ∀ τ ∈ T, ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
      Nat.factorial (AmbientC0Attach g u c).card = Nat.factorial (a τ) ^ (m τ) :=
    fun τ _ => prod_ambientC0Attach_factorial_eq_pow g u
      ((Finset.univ.erase c0).filter (fun c => compType g u c = τ)) τ
      (fun c hc => (Finset.mem_filter.mp hc).2)
  have hane : ∀ τ ∈ T, a τ ≠ 0 := by
    intro τ hτ
    rw [hTdef, Finset.mem_image] at hτ
    obtain ⟨c, -, hceq⟩ := hτ
    rw [hadef]
    show τ.1 ≠ 0
    rw [← hceq]
    exact (Finset.Nonempty.card_pos (hne_attach c)).ne'
  -- R_u = a0 + Σ_τ m_τ a_τ (Identity 4, the attach-set partition of V u regrouped by fiber).
  have hRu : a0 + ∑ τ ∈ T, m τ * a τ = (V u).card := by
    rw [card_vu_eq_sum_ambientC0Attach hpart hmixed,
      ← Finset.add_sum_erase Finset.univ (fun c => (AmbientC0Attach g u c).card)
        (Finset.mem_univ c0)]
    congr 1
    exact (sum_ambientC0Attach_eq_sum_fibers g u c0).symm
  -- The root multinomial absorption, specialized.
  have habs : Nat.factorial (a0 - 1) * ∏ τ ∈ T, Nat.factorial (a τ) ^ (m τ) * Nat.factorial (m τ)
      ∣ Nat.factorial ((V u).card - 1) := by
    have h := multinomial_absorption T a0 a m (Finset.Nonempty.card_pos (hne_attach c0)).ne' hane
    rwa [hRu] at h
  -- The only valuation-level step: factorization of the multinomial-absorption divisibility.
  have hval_abs : (Nat.factorial (a0 - 1) * ∏ τ ∈ T,
        Nat.factorial (a τ) ^ (m τ) * Nat.factorial (m τ)).factorization p ≤
      (Nat.factorial ((V u).card - 1)).factorization p := by
    have h1 : Nat.factorial (a0 - 1) *
        ∏ τ ∈ T, Nat.factorial (a τ) ^ (m τ) * Nat.factorial (m τ) ≠ 0 :=
      Nat.mul_ne_zero (Nat.factorial_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr (fun τ _ => Nat.mul_ne_zero
          (pow_ne_zero _ (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)))
    exact (Nat.factorization_le_iff_dvd h1 (Nat.factorial_ne_zero _)).mpr habs p
  -- The blocks partition, regrouped by fiber (Identities 1 and 3), a pure equality of products.
  have hblocksplit : (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
        Nat.factorial ((IslandV g u c0 i).card - 1)) *
      ∏ τ ∈ T, ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
        ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
          Nat.factorial ((IslandV g u c i).card - 1) =
      ∏ i : {j : ι // j ≠ u}, Nat.factorial ((V i.1).card - 1) := by
    rw [island_prod_eq_blockSet_prod g u c0]
    have hstep : ∏ τ ∈ T, ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
        ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
          Nat.factorial ((IslandV g u c i).card - 1) =
        ∏ c ∈ Finset.univ.erase c0, ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1) := by
      rw [← Finset.prod_fiberwise_of_maps_to (t := T) (g := compType g u)
        (fun c hc => Finset.mem_image_of_mem _ hc)
        (fun c => ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1))]
      apply Finset.prod_congr rfl
      intro τ _
      apply Finset.prod_congr rfl
      intro c hc
      exact island_prod_eq_blockSet_prod g u c
    rw [hstep]
    exact prod_blockSet_partition g u c0
  -- Rewrite hbase's fiber-attachment product via hpow (Identity 2).
  have heq1 : (∏ τ ∈ T, (Nat.factorial (m τ) *
        ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
            Nat.factorial (AmbientC0Attach g u c).card) *
          ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
            ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1)) =
      (∏ τ ∈ T, Nat.factorial (m τ) * Nat.factorial (a τ) ^ (m τ)) *
        ∏ τ ∈ T, ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
          ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
            Nat.factorial ((IslandV g u c i).card - 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro τ hτ
    rw [hpow τ hτ]
  rw [heq1] at hbase
  have hpos1 : (∏ τ ∈ T, Nat.factorial (m τ) * Nat.factorial (a τ) ^ (m τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun τ _ => Nat.mul_ne_zero (Nat.factorial_ne_zero _)
      (pow_ne_zero _ (Nat.factorial_ne_zero _)))
  have hpos2 : (∏ τ ∈ T, ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
      ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
        Nat.factorial ((IslandV g u c i).card - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun τ _ => Finset.prod_ne_zero_iff.mpr (fun c _ =>
      Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)))
  have hval1 : ((∏ τ ∈ T, Nat.factorial (m τ) * Nat.factorial (a τ) ^ (m τ)) *
        ∏ τ ∈ T, ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
          ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
            Nat.factorial ((IslandV g u c i).card - 1)).factorization p =
      (∏ τ ∈ T, Nat.factorial (m τ) * Nat.factorial (a τ) ^ (m τ)).factorization p +
        (∏ τ ∈ T, ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
          ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
            Nat.factorial ((IslandV g u c i).card - 1)).factorization p := by
    rw [Nat.factorization_mul hpos1 hpos2]
    rfl
  -- The a0/multinomial part: rearrange to match habs's order, then apply hval_abs.
  have heq2 : Nat.factorial (a0 - 1) * ∏ τ ∈ T, Nat.factorial (m τ) * Nat.factorial (a τ) ^ (m τ) =
      Nat.factorial (a0 - 1) * ∏ τ ∈ T, Nat.factorial (a τ) ^ (m τ) * Nat.factorial (m τ) := by
    congr 1
    exact Finset.prod_congr rfl (fun τ _ => mul_comm _ _)
  have hpos0 : Nat.factorial (a0 - 1) ≠ 0 := Nat.factorial_ne_zero _
  have hval2 : (Nat.factorial (a0 - 1)).factorization p +
      (∏ τ ∈ T, Nat.factorial (m τ) * Nat.factorial (a τ) ^ (m τ)).factorization p ≤
      (Nat.factorial ((V u).card - 1)).factorization p := by
    have hcomb : (Nat.factorial (a0 - 1)).factorization p +
        (∏ τ ∈ T, Nat.factorial (m τ) * Nat.factorial (a τ) ^ (m τ)).factorization p =
        (Nat.factorial (a0 - 1) *
          ∏ τ ∈ T, Nat.factorial (m τ) * Nat.factorial (a τ) ^ (m τ)).factorization p := by
      rw [Nat.factorization_mul hpos0 hpos1]
      rfl
    rw [hcomb, heq2]
    exact hval_abs
  -- The island part: an exact equality via hblocksplit, then split into the block-index sum.
  have hisl0pos : (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
      Nat.factorial ((IslandV g u c0 i).card - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)
  have hval3 : (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
        Nat.factorial ((IslandV g u c0 i).card - 1)).factorization p +
      (∏ τ ∈ T, ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
        ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
          Nat.factorial ((IslandV g u c i).card - 1)).factorization p =
      ∑ i : {i : ι // i ≠ u}, (Nat.factorial ((V i.1).card - 1)).factorization p := by
    have hcomb : (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
          Nat.factorial ((IslandV g u c0 i).card - 1)).factorization p +
        (∏ τ ∈ T, ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
          ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
            Nat.factorial ((IslandV g u c i).card - 1)).factorization p =
        ((∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
              Nat.factorial ((IslandV g u c0 i).card - 1)) *
            ∏ τ ∈ T, ∏ c ∈ (Finset.univ.erase c0).filter (fun c => compType g u c = τ),
              ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
                Nat.factorial ((IslandV g u c i).card - 1)).factorization p := by
      rw [Nat.factorization_mul hisl0pos hpos2]
      rfl
    rw [hcomb, hblocksplit,
      Nat.factorization_prod (fun i (_ : i ∈ (Finset.univ : Finset {j : ι // j ≠ u})) =>
        Nat.factorial_ne_zero ((V i.1).card - 1))]
    simp
  omega
