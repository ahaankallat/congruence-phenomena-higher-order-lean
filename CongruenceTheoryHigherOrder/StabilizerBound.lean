import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount
import CongruenceTheoryHigherOrder.WreathProduct
import CongruenceTheoryHigherOrder.Semiregularity
import CongruenceTheoryHigherOrder.ConjugationInvariance

/-!
**Completes the manuscript's own stated conclusion for inequality (A1)**: "Hence the stabilizer
order divides `rq`." **`card_wreathStab_dvd`** proves exactly this — for `g` connected, the
subgroup of `Wreath r q` centralizing `g`'s image under the wreath action has order dividing `rq`.
Combined with `WreathProduct.lean` (the group and its faithful action), `Semiregularity.lean` (the
semiregularity argument), and `ConjugationInvariance.lean` (conjugation preserves connectedness),
this closes out every sentence of the manuscript's own proof of (A1) up to its final numeric
assembly step.

**Construction**: `card_dvd_of_free_action` is a general, reusable group-theory lemma — if a
finite group `H` acts on a finite type `X` freely (only the identity has any fixed point), then
`|H| ∣ |X|` — proved via Mathlib's class-equation decomposition
(`MulAction.selfEquivSigmaOrbitsQuotientStabilizer`), using that every stabilizer trivializes
under freeness (so every fiber `H⧸stabilizer` has full size `|H|`, `QuotientGroup.quotientBot`),
then summing over orbits. `wreathStab hq g` is the actual centralizer subgroup of `Wreath r q`
(`Commute (wreathToPermRotate w) g`); it inherits a `MulAction` on `Fin r × Fin q` via
`MulAction.compHom` along the restricted homomorphism. **`card_wreathStab_dvd`** applies the
general lemma to this action, whose freeness is exactly `Semiregularity.lean`'s
`wreathToPermRotate_eq_one_of_fixes` combined with the action's faithfulness
(`wreathToPermRotate_injective`).

**Honest scope note**: this is the manuscript's stated stabilizer-order conclusion, essentially
finishing (A1)'s own three sentences as formalized statements. What remains to reach the final
boxed numeric inequality `(r-1)!q^{r-1} ∣ K_r(q)` is: orbit-stabilizer on the *full* wreath group's
conjugation action (not just this centralizer subgroup) to convert "stabilizer divides `rq`" into
"orbit size is a multiple of `q^{r-1}(r-1)!`", and relating that orbit size to an actual
`MvPolynomial.coeff`-level coefficient of `K_r(q)` via `ConnectedCount.lean`'s `K_eq_Gfun_top` —
bookkeeping rather than new mathematical content, but not attempted here. Nor is any of (A2)
through (A6) or Lucas' theorem, each its own substantial undertaking.
-/

namespace CongruenceTheory

open scoped Classical

/-- If a finite group `H` acts on a finite type `X` such that only the identity has any fixed
point (a free action), then `|H|` divides `|X|`. -/
theorem card_dvd_of_free_action {H : Type*} [Group H] [Finite H] {X : Type*} [Finite X]
    [MulAction H X] (hfree : ∀ h : H, h ≠ 1 → ∀ x : X, h • x ≠ x) :
    Nat.card H ∣ Nat.card X := by
  classical
  cases nonempty_fintype H
  cases nonempty_fintype X
  simp only [Nat.card_eq_fintype_card]
  have hstab : ∀ x : X, MulAction.stabilizer H x = ⊥ := by
    intro x
    rw [Subgroup.eq_bot_iff_forall]
    intro h hh
    by_contra hne
    exact hfree h hne x hh
  let Ω := Quotient (MulAction.orbitRel H X)
  have hcard : Fintype.card X = ∑ _ω : Ω, Fintype.card H := by
    rw [← Fintype.card_sigma]
    apply Fintype.card_congr
    refine (MulAction.selfEquivSigmaOrbitsQuotientStabilizer H X).trans ?_
    apply Equiv.sigmaCongrRight
    intro ω
    rw [hstab]
    exact QuotientGroup.quotientBot.toEquiv
  rw [hcard, Finset.sum_const, smul_eq_mul]
  exact Dvd.intro_left _ rfl

variable {r q : ℕ} [NeZero r] [NeZero q] (hq : 2 ≤ q)

noncomputable instance : Finite (Wreath r q) :=
  Finite.of_equiv _ (SemidirectProduct.equivProd (φ := wreathPhi r q)).symm

/-- The centralizer, under the wreath action, of a permutation `g` — the subgroup of
`Wreath r q` whose image commutes with (equivalently, conjugation-fixes) `g`. -/
def wreathStab (g : Equiv.Perm (Fin r × Fin q)) : Subgroup (Wreath r q) where
  carrier := {w | Commute (wreathToPermRotate r q hq w) g}
  mul_mem' {a b} ha hb := by
    show Commute (wreathToPermRotate r q hq (a * b)) g
    rw [map_mul]
    exact Commute.mul_left ha hb
  one_mem' := by
    show Commute (wreathToPermRotate r q hq 1) g
    rw [map_one]; exact Commute.one_left g
  inv_mem' {a} ha := by
    show Commute (wreathToPermRotate r q hq a⁻¹) g
    rw [map_inv]
    exact ha.inv_left

noncomputable instance (g : Equiv.Perm (Fin r × Fin q)) :
    MulAction (wreathStab hq g) (Fin r × Fin q) :=
  MulAction.compHom (Fin r × Fin q)
    ((wreathToPermRotate r q hq).comp (wreathStab hq g).subtype)

omit [NeZero r] in
theorem wreathStab_smul_eq {g : Equiv.Perm (Fin r × Fin q)} (w : wreathStab hq g)
    (x : Fin r × Fin q) : w • x = wreathToPermRotate r q hq (w : Wreath r q) x := rfl

/-- **The stabilizer of a connected permutation acts freely under the wreath action**, and hence
its order divides `rq` — the manuscript's own stated conclusion ("the stabilizer order divides
`rq`") for inequality (A1). -/
theorem card_wreathStab_dvd {g : Equiv.Perm (Fin r × Fin q)} (hg : piOf g = ⊤) :
    Nat.card (wreathStab hq g) ∣ r * q := by
  have hcardX : Nat.card (Fin r × Fin q) = r * q := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [← hcardX]
  apply card_dvd_of_free_action
  intro w hw x hx
  apply hw
  have hcomm : Commute (wreathToPermRotate r q hq (w : Wreath r q)) g := w.2
  have hfix := wreathToPermRotate_eq_one_of_fixes hq hg hcomm
    (x := x) (by rwa [wreathStab_smul_eq] at hx)
  have hw1 : (w : Wreath r q) = 1 :=
    wreathToPermRotate_injective r q hq (hfix.trans (map_one _).symm)
  exact Subtype.ext hw1

end CongruenceTheory
