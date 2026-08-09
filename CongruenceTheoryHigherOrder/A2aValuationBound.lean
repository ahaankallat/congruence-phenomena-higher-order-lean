import Mathlib
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aLayerInduction
import CongruenceTheoryHigherOrder.A2aFullInduction
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.A2aLogFactorialBound

/-!
**Upgrading (A2a)'s non-cut-vertex cardinality bound to the valuation-level statement the
manuscript actually needs.** `A2aRootBound.lean` proves the literal `Nat` inequality
`|A|≤R_u∏_{i≠u}(R_i-1)!` (`card_le_root_bound`) and stops there. The manuscript's next step,
"which implies (A2a), since `v_p(R_u)≤1+v_p((R_u-1)!)`", is invalid as stated: a value inequality
does not imply a valuation inequality in general. This file closes that gap by upgrading every
layer of the underlying argument from `≤` to `∣`, which the existing group-theoretic machinery
already supports (the per-layer step factors `A` via a genuine `MonoidHom` with an exact
`|A|=|range|·|ker|` decomposition and an *injectively embedded* range, hence a subgroup whose order
*divides* the codomain's order by Lagrange, not merely bounds it), and combining with the root
orbit-stabilizer step (exact, not approximate) plus the log-factorial lemma
(`A2aLogFactorialBound.lean`) for the one genuine value-only bound (the orbit of the root incidence
has size `≤R_u`, not a divisor of `R_u`).
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **Divisibility version of the per-layer step.** Same hypotheses as
`card_le_prod_factorial_mul_card_fixBlocks`, but concluding `|A| ∣ (∏_{i∈L}(R_i-1)!)·|FixBlocks A V
L|` instead of `≤`. Proof: identical factorization `|A|=|range f|·|ker f|` (exact, via the first
isomorphism theorem), but `range f` is a genuine subgroup of `∀i:L,Perm(V i∖{q i})` (not just
cardinality-bounded by an injection), so Lagrange gives `|range f| ∣ ∏_{i∈L}(R_i-1)!` directly. -/
theorem card_dvd_prod_factorial_mul_card_fixBlocks {V : ι → Finset Ω}
    (hpart : IsPartition V) {A : Subgroup (Perm Ω)}
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) (L : Finset ι) (q : ι → Ω)
    (hq : ∀ i ∈ L, q i ∈ V i) (hfixq : ∀ i ∈ L, ∀ φ ∈ A, φ (q i) = q i) :
    Nat.card A ∣ (∏ i ∈ L, Nat.factorial ((V i).card - 1)) * Nat.card (FixBlocks A V L) := by
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
  -- The divisibility upgrade: `range f` is a genuine `Subgroup` of the codomain, so Lagrange
  -- gives divisibility of its order, not merely a cardinality bound via an injection.
  have hrangedvd : Nat.card (MonoidHom.range f) ∣ ∏ i ∈ L, Nat.factorial ((V i).card - 1) := by
    have hdvd : Nat.card (MonoidHom.range f) ∣
        Nat.card (∀ i : (L : Finset ι), Equiv.Perm ↥((V i.1).erase (q i.1))) :=
      Subgroup.card_subgroup_dvd_card (MonoidHom.range f)
    have heq : Nat.card (∀ i : (L : Finset ι), Equiv.Perm ↥((V i.1).erase (q i.1))) =
        ∏ i ∈ L, Nat.factorial ((V i).card - 1) := by
      rw [Nat.card_pi, ← Finset.prod_coe_sort L (fun i => Nat.factorial ((V i).card - 1))]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe,
        Finset.card_erase_of_mem (hq i.1 i.2)]
    rwa [heq] at hdvd
  rw [hcard, hkereq]
  exact mul_dvd_mul_right hrangedvd _

/-- **Divisibility version of `key_induction`.** Same hypotheses, concluding `|A| ∣ ∏_{i∉L}(R_i-1)!`
instead of `≤`. Proved by the identical strong induction, using
`card_dvd_prod_factorial_mul_card_fixBlocks` at each layer instead of the cardinality-only step,
and chaining divisibility (`dvd_trans`) instead of chaining inequalities. -/
theorem key_induction_dvd {V : ι → Finset Ω} (hpart : IsPartition V) {g : Perm Ω}
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y) :
    ∀ n : ℕ, ∀ L : Finset ι, (Finset.univ \ L).card ≤ n → L.Nonempty →
    ∀ A : Subgroup (Perm Ω), (∀ φ ∈ A, Commute φ g) →
    (∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) →
    (∀ i ∈ L, ∀ x ∈ V i, ∀ φ ∈ A, φ x = x) →
    Nat.card A ∣ ∏ i ∈ Lᶜ, Nat.factorial ((V i).card - 1) := by
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
    have hcard1 : Nat.card A = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1, A.one_mem⟩⟩
    rw [hcard1]
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
      have hcard1 : Nat.card A = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1, A.one_mem⟩⟩
      rw [hcard1]
    · obtain ⟨i, hiL, j, hjL, x, hx, y, hy, hxy⟩ := hconn L hLne hLuniv
      have hfixx : ∀ φ ∈ A, φ x = x := hfix i hiL x hx
      have hfixy : ∀ φ ∈ A, φ y = y := by
        intro φ hφ
        exact Perm.fixed_of_commute_of_fixed_point (hcent φ hφ) (hfixx φ hφ) hxy
      have hstep := card_dvd_prod_factorial_mul_card_fixBlocks hpart hperm ({j} : Finset ι)
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
      exact dvd_trans hstep (mul_dvd_mul_left _ hrec)

/-- **Divisibility version of `key_induction_rooted`** (`A2aRootBound.lean`). Same hypotheses,
concluding `|A| ∣ ∏_{i∈(univ∖{u})∖L}(R_i-1)!` instead of `≤`. The base case is unchanged (it already
concludes `A` is trivial, hence `|A|=1`, which divides anything); the inductive step uses the
divisibility layer step and chains via `dvd_trans` exactly as in `key_induction_dvd`. -/
theorem key_induction_rooted_dvd {V : ι → Finset Ω} (hpart : IsPartition V) {g : Perm Ω} {u : ι}
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y) :
    ∀ n : ℕ, ∀ L : Finset ι, L ⊆ Finset.univ.erase u →
      ((Finset.univ.erase u) \ L).card ≤ n → L.Nonempty →
    ∀ A : Subgroup (Perm Ω), (∀ φ ∈ A, Commute φ g) →
    (∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) →
    (∀ i ∈ L, ∀ x ∈ V i, ∀ φ ∈ A, φ x = x) →
    Nat.card A ∣ ∏ i ∈ (Finset.univ.erase u) \ L, Nat.factorial ((V i).card - 1) := by
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
    have hcard1 : Nat.card A = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1, A.one_mem⟩⟩
    rw [hcard1]
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
      have hcard1 : Nat.card A = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1, A.one_mem⟩⟩
      rw [hcard1]
    · obtain ⟨i, hiL, j, hjL, hjune, x, hx, y, hy, hxy⟩ := hconn L hLne hLuniv hLsub
      have hfixx : ∀ φ ∈ A, φ x = x := hfix i hiL x hx
      have hfixy : ∀ φ ∈ A, φ y = y := by
        intro φ hφ
        exact Perm.fixed_of_commute_of_fixed_point (hcent φ hφ) (hfixx φ hφ) hxy
      have hstep := card_dvd_prod_factorial_mul_card_fixBlocks hpart hperm ({j} : Finset ι)
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
      exact dvd_trans hstep (mul_dvd_mul_left _ hrec)

/-- **`Nat.card Apt` divides the product**, the divisibility analog of `card_le_root_bound`'s
`htotal` step. -/
theorem card_dvd_ptStab_prod {V : ι → Finset Ω} (hpart : IsPartition V) {A : Subgroup (Perm Ω)}
    {g : Perm Ω} (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j)
    (u : ι) (p₀ : Ω)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    {j₀ : ι} (hj₀u : j₀ ≠ u) {y₀ : Ω} (hy₀ : y₀ ∈ V j₀) (hp₀y₀ : g.SameCycle p₀ y₀)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y) :
    Nat.card (PtStab A p₀) ∣ ∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1) := by
  set Apt := PtStab A p₀ with hApt
  have hcent_pt : ∀ φ ∈ Apt, Commute φ g := fun φ hφ => hcent φ (mem_PtStab.mp hφ).1
  have hperm_pt : ∀ φ ∈ Apt, ∀ i, ∃ j, (V i).image φ = V j :=
    fun φ hφ => hperm φ (mem_PtStab.mp hφ).1
  have hstep0 := card_dvd_prod_factorial_mul_card_fixBlocks hpart hperm_pt ({j₀} : Finset ι)
    (fun _ => y₀)
    (by intro i0 hi0; rw [Finset.mem_singleton.mp hi0]; exact hy₀)
    (by
      intro i0 hi0 φ hφ
      obtain ⟨hφA, hφp₀⟩ := mem_PtStab.mp hφ
      exact Perm.fixed_of_commute_of_fixed_point (hcent φ hφA) hφp₀ hp₀y₀)
  simp only [Finset.prod_singleton] at hstep0
  have hj₀mem : j₀ ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hj₀u, Finset.mem_univ j₀⟩
  have hrec := key_induction_rooted_dvd hpart hmixed hconn
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
  rw [← Finset.mul_prod_erase (Finset.univ.erase u) (fun i => Nat.factorial ((V i).card - 1))
    hj₀mem]
  exact dvd_trans hstep0 (mul_dvd_mul_left _ hrec)


/-- If `p^k ≤ R` (p prime, R≥1), then `k ≤ 1+v_p((R-1)!)`. The core numeric fact, stated to take
the power bound directly as a hypothesis (so it applies to any quantity known only to be `≤ R`,
such as an orbit size, not just to `Nat.log p R` itself). -/
theorem pow_le_imp_le_one_add_factorization_factorial_pred {p : ℕ} (hp : p.Prime) (R k : ℕ)
    (hR : 1 ≤ R) (hpk : p ^ k ≤ R) : k ≤ 1 + (R - 1).factorial.factorization p := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · omega
  have hpk_eq : p ^ k = p * p ^ (k - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have h1le : 1 ≤ p ^ (k - 1) := Nat.one_le_pow _ _ hp.pos
  have hstep : p ^ (k - 1) ≤ p ^ k - 1 := by
    have h2 : 2 * p ^ (k - 1) ≤ p * p ^ (k - 1) := Nat.mul_le_mul_right _ hp.two_le
    omega
  have hRm1 : p ^ (k - 1) ≤ R - 1 := by omega
  have hpos : 0 < p ^ (k - 1) := Nat.pow_pos hp.pos
  have hdvd : p ^ (k - 1) ∣ (R - 1).factorial := Nat.dvd_factorial hpos hRm1
  have hval : (k - 1) ≤ (R - 1).factorial.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.factorial_ne_zero (R - 1))).mp hdvd
  omega

/-- **The valuation-level (A2a) statement for the "not a cut vertex" case, exactly as the
manuscript needs it, with a fully valid derivation.** Replaces the manuscript's invalid step
("`|A|≤R_u∏(R_i-1)!`, which implies (A2a) since `v_p(R_u)≤1+v_p((R_u-1)!)`") with a genuine
orbit-stabilizer valuation argument: `Nat.card A = Nat.card(orbit of p₀)·Nat.card(PtStab A p₀)`
*exactly* (orbit-stabilizer, not approximate), so `v_p(Nat.card A) = v_p(orbit) + v_p(PtStab)`. The
orbit term uses the direct power-bound form of the log-factorial lemma (valid for a value-only
bound: `p^k∣orbit∧orbit≤R_u⟹p^k≤R_u`); the `PtStab` term uses genuine divisibility
(`card_dvd_ptStab_prod`), valid since `v_p` respects `∣`. -/
theorem card_le_root_bound_valuation {V : ι → Finset Ω} (hpart : IsPartition V)
    {A : Subgroup (Perm Ω)} {g : Perm Ω} (hcent : ∀ φ ∈ A, Commute φ g)
    (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j)
    (u : ι) (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) (p₀ : Ω) (hp₀ : p₀ ∈ V u)
    (hune : (V u).Nonempty)
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    {j₀ : ι} (hj₀u : j₀ ≠ u) {y₀ : Ω} (hy₀ : y₀ ∈ V j₀) (hp₀y₀ : g.SameCycle p₀ y₀)
    (hconn : ∀ L : Finset ι, L.Nonempty → L ≠ Finset.univ.erase u → L ⊆ Finset.univ.erase u →
      ∃ i ∈ L, ∃ j, j ∉ L ∧ j ≠ u ∧ ∃ x ∈ V i, ∃ y ∈ V j, g.SameCycle x y)
    {p : ℕ} (hp : p.Prime) :
    (Nat.card A).factorization p ≤
      1 + ∑ i, (Nat.factorial ((V i).card - 1)).factorization p := by
  -- Exact orbit-stabilizer decomposition of `A` at `p₀`.
  have horbstab : Nat.card (MulAction.orbit A p₀) * Nat.card (MulAction.stabilizer A p₀) =
      Nat.card A := nat_card_orbit_mul_stabilizer p₀
  have hEquiv : MulAction.stabilizer A p₀ ≃ PtStab A p₀ :=
  { toFun := fun a => ⟨a.1.1, mem_PtStab.mpr ⟨a.1.2, a.2⟩⟩
    invFun := fun a => ⟨⟨a.1, (mem_PtStab.mp a.2).1⟩, (mem_PtStab.mp a.2).2⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }
  rw [Nat.card_congr hEquiv] at horbstab
  -- The orbit is a subset of `V u`, so its size is `≤ (V u).card`.
  have horb_le : Nat.card (MulAction.orbit A p₀) ≤ (V u).card := by
    have h := card_le_card_block_mul_card_stabilizer (G := A) V u p₀ hp₀ (fun φ => hblock_u φ.1 φ.2)
    rw [Nat.card_congr hEquiv, ← horbstab] at h
    exact Nat.le_of_mul_le_mul_right (by rwa [mul_comm] at h) Nat.card_pos
  haveI : Nonempty (MulAction.orbit A p₀) := ⟨⟨p₀, MulAction.mem_orbit_self p₀⟩⟩
  have horbpos : 0 < Nat.card (MulAction.orbit A p₀) := Nat.card_pos
  have hstabpos : 0 < Nat.card (PtStab A p₀) := Nat.card_pos
  -- `v_p(Nat.card A) = v_p(orbit) + v_p(PtStab)`.
  have hval : (Nat.card A).factorization p =
      (Nat.card (MulAction.orbit A p₀)).factorization p +
        (Nat.card (PtStab A p₀)).factorization p := by
    rw [← horbstab, Nat.factorization_mul horbpos.ne' hstabpos.ne']
    rfl
  rw [hval]
  -- Bound the orbit term.
  have hRpos : 1 ≤ (V u).card := hune.card_pos
  have hpk : p ^ ((Nat.card (MulAction.orbit A p₀)).factorization p) ≤ (V u).card := by
    have hpk' : p ^ ((Nat.card (MulAction.orbit A p₀)).factorization p) ∣
        Nat.card (MulAction.orbit A p₀) := Nat.ordProj_dvd _ p
    exact (Nat.le_of_dvd horbpos hpk').trans horb_le
  have horb_bound : (Nat.card (MulAction.orbit A p₀)).factorization p ≤
      1 + ((V u).card - 1).factorial.factorization p :=
    pow_le_imp_le_one_add_factorization_factorial_pred hp (V u).card _ hRpos hpk
  -- Bound the `PtStab` term via divisibility.
  have hptstab_dvd := card_dvd_ptStab_prod hpart hcent hperm u p₀ hmixed hj₀u hy₀ hp₀y₀ hconn
  have hprod_pos : 0 < ∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1) :=
    Finset.prod_pos (fun i _ => Nat.factorial_pos _)
  have hptstab_bound : (Nat.card (PtStab A p₀)).factorization p ≤
      ∑ i ∈ Finset.univ.erase u, (Nat.factorial ((V i).card - 1)).factorization p := by
    have h := (Nat.factorization_le_iff_dvd hstabpos.ne' hprod_pos.ne').mpr hptstab_dvd
    have hp' := h p
    have heq : (∏ i ∈ Finset.univ.erase u, Nat.factorial ((V i).card - 1)).factorization p =
        ∑ i ∈ Finset.univ.erase u, (Nat.factorial ((V i).card - 1)).factorization p := by
      rw [Nat.factorization_prod (fun i _ => Nat.factorial_ne_zero _)]
      simp
    rwa [heq] at hp'
  have hmerge : ((V u).card - 1).factorial.factorization p +
      ∑ i ∈ Finset.univ.erase u, (Nat.factorial ((V i).card - 1)).factorization p =
      ∑ i, (Nat.factorial ((V i).card - 1)).factorization p :=
    Finset.add_sum_erase _ (fun i => (Nat.factorial ((V i).card - 1)).factorization p)
      (Finset.mem_univ u)
  omega
