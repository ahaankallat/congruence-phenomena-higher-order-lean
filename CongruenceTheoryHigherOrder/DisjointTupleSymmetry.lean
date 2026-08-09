import Mathlib
import CongruenceTheoryHigherOrder.FreeActionDivides

/-!
**The `m_τ!` divisibility step of (A2a)'s cut-vertex multinomial fact**, built on
`FreeActionDivides.lean`'s general `card_dvd_of_free`. The manuscript's cut-vertex argument needs
"`(R_u-1)!/((a_0-1)!∏_τ(a_τ!)^{m_τ}m_τ!)` is an integer": having already accounted for the
`(a_0-1)!∏_τ(a_τ!)^{m_τ}` factor via `Nat.multinomial_spec` (an exact, off-the-shelf Mathlib
identity for labeled partitions), what remains is the extra `m_τ!` — the order of the symmetric
group permuting which of the `m_τ` *labeled* size-`a_τ` slots within class `τ` holds which actual
content, which does not change the underlying (unordered) partition. `DisjointTuple β m a` models
exactly this: `m` labeled pairwise-disjoint `a`-element subsets of `β`; `Equiv.Perm (Fin m)`
permutes their labels, freely (disjoint nonempty sets are never equal, so no nontrivial relabeling
fixes a given tuple) — `card_dvd_of_free` then gives `m!∣Fintype.card(DisjointTuple β m a)`
directly.

**Honest scope note**: this closes the general *principle* the cut-vertex case's `m_τ!` divisor
rests on, but assembling it into the manuscript's literal multinomial identity — combining this
with `Nat.multinomial_spec`, instantiating `β`/`m`/`a` once per rooted-isomorphism type `τ`, and
building the surrounding graph-component/rooted-isomorphism-type classification (components of the
incidence graph minus `u`, grouped by rooted isomorphism) that the manuscript's `a_0`, `a_τ`, `m_τ`
are even defined in terms of — remains a further substantial undertaking, not attempted here.
-/

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The type of `m`-tuples of pairwise-disjoint `a`-element subsets of `β`. -/
abbrev DisjointTuple (β : Type*) [Fintype β] [DecidableEq β] (m a : ℕ) :=
  {f : Fin m → Finset β // Pairwise (fun i j => Disjoint (f i) (f j)) ∧ ∀ i, (f i).card = a}

noncomputable instance (m a : ℕ) : Fintype (DisjointTuple β m a) := Fintype.ofFinite _

/-- `Equiv.Perm (Fin m)` acts on `DisjointTuple β m a` by permuting which position holds which
block. -/
noncomputable instance instMulActionDisjointTuple (m a : ℕ) :
    MulAction (Equiv.Perm (Fin m)) (DisjointTuple β m a) where
  smul σ f := ⟨fun i => f.1 (σ⁻¹ i), by
    constructor
    · intro i j hij
      have hne : σ⁻¹ i ≠ σ⁻¹ j := fun h => hij (σ⁻¹.injective h)
      exact f.2.1 hne
    · intro i
      exact f.2.2 (σ⁻¹ i)⟩
  one_smul f := by
    apply Subtype.ext
    funext i
    show f.1 ((1 : Equiv.Perm (Fin m))⁻¹ i) = f.1 i
    simp
  mul_smul σ τ f := by
    apply Subtype.ext
    funext i
    show f.1 ((σ * τ)⁻¹ i) = f.1 (τ⁻¹ (σ⁻¹ i))
    simp [mul_inv_rev]

theorem disjointTuple_smul_apply (m a : ℕ) (σ : Equiv.Perm (Fin m)) (f : DisjointTuple β m a)
    (i : Fin m) : (σ • f).1 i = f.1 (σ⁻¹ i) := rfl

/-- **Permuting labels among `m` pairwise-disjoint `a`-element blocks (`a≥1`) is a free action**,
so `m!` divides the number of such labeled tuples. This is the general principle behind the
"`m_τ!`" divisor in (A2a)'s cut-vertex multinomial-divisibility fact: labeled groups within a
single size-class `τ` can be freely relabeled, since disjoint nonempty sets are never equal. -/
theorem factorial_dvd_card_disjointTuple (m a : ℕ) (ha : 1 ≤ a) :
    Nat.factorial m ∣ Fintype.card (DisjointTuple β m a) := by
  have hcardperm : Fintype.card (Equiv.Perm (Fin m)) = Nat.factorial m := by
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [← hcardperm]
  apply card_dvd_of_free
  intro σ hσ f hf
  obtain ⟨i₀, hi₀⟩ : ∃ i, σ⁻¹ i ≠ i := by
    by_contra h
    push_neg at h
    apply hσ
    apply Equiv.ext
    intro i
    show σ i = i
    have h2 : σ (σ⁻¹ i) = σ i := congrArg σ (h i)
    simp at h2
    exact h2.symm
  have heq : f.1 (σ⁻¹ i₀) = f.1 i₀ := by
    have h1 := congrArg (fun g : DisjointTuple β m a => g.1 i₀) hf
    simpa [disjointTuple_smul_apply] using h1
  have hdisj : Disjoint (f.1 (σ⁻¹ i₀)) (f.1 i₀) := f.2.1 hi₀
  rw [heq] at hdisj
  have hbot : f.1 i₀ = ⊥ := by simpa using hdisj.eq_bot
  have hcard0 : (f.1 i₀).card = 0 := by rw [hbot]; simp
  rw [f.2.2 i₀] at hcard0
  omega
