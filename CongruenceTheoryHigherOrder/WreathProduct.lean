import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount

/-!
**Foundational scaffolding for inequality (A1) of `thm:atomic-connected-content`'s proof**: the
manuscript's argument for the lower bound `(r-1)!q^{r-1} | K_r(q)` starts by choosing "compatible
full `q`-cycles on the `r` blocks" and considering "the group `C_q^r ⋊ S_r`" acting by conjugation
on connected permutations of a fixed cycle type. Mathlib has exactly one wreath product
(`RegularWreathProduct`), and it uses the wrong action for this purpose — `Q` acting on itself by
translation, not `S_r`'s natural action on `r` labelled blocks. This file builds the needed
wreath product **from scratch**, as a genuine subgroup of `Equiv.Perm (Fin r × Fin q)`, using
Mathlib's general external `SemidirectProduct` (which only needs an arbitrary `φ : G →* MulAut N`,
not a specific action) plus the same block-gluing style already used in `PartitionGluing.lean`.

**Construction**: `WreathN r q := Fin r → Multiplicative (ZMod q)` is `(ℤ/q)^r`; `wreathPhi`
lets `S_r = Equiv.Perm (Fin r)` act on it by permuting the `r` coordinates, giving
`Wreath r q := WreathN r q ⋊[wreathPhi r q] Equiv.Perm (Fin r)`, with order `q^r · r!` confirmed
by **`card_wreath`** (via Mathlib's `SemidirectProduct.card`). `cPowHom c hc` turns a fixed
permutation `c` with `c^q = 1` into a homomorphism from `Multiplicative (ZMod q)` (via
`ZMod.val`/`Nat.div_add_mod` to handle the periodicity directly). `blockAction` glues a family of
per-block permutations into one permutation of `Fin r × Fin q` (simpler than
`PartitionGluing.lean`'s `assemble`, since it acts on *all* of `Fin r`, no partial-subtype gluing
needed). Combining these gives `wreathFn`/`wreathFg`, whose compatibility with `wreathPhi`'s
conjugation action (`wreathFn_wreathPhi_compat`) lets Mathlib's `SemidirectProduct.lift` assemble
**`wreathToPerm`**, the actual homomorphism `Wreath r q →* Equiv.Perm (Fin r × Fin q)`.
**`wreathToPerm_injective`** shows this action is faithful whenever `c` has order exactly `q`
(not just `c^q = 1`) — proved directly from the pointwise formula `wreathToPerm_apply`, using that
a `ZMod q` value's `.val` representative is strictly below `q = orderOf c`. Finally,
**`wreathToPermRotate`** instantiates this concretely with `c = finRotate q` (Mathlib's standard
cyclic rotation), using `orderOf_finRotate` (`q ≥ 2`, via Mathlib's `IsCycle.orderOf` and
`support_finRotate_of_le`) to discharge the faithfulness hypothesis.

**Honest scope note**: this is *only* the group-and-action scaffolding for (A1) — it does not yet
touch the actual mathematical content, which needs: the conjugation action of `Wreath r q` on
*connected* permutations of a fixed cycle type (requiring conjugation-invariance of the cycle-
support connectivity partition `π(g)` from `ConnectedCount.lean`), and the semiregularity argument
itself ("a stabilizer element fixing one point is the identity on that whole block, and
connectedness propagates this to every block, so the stabilizer's image acts semiregularly on all
`rq` labels, hence has order dividing `rq`") — genuinely novel group-theoretic reasoning specific
to this manuscript's argument, with no Mathlib precedent, not attempted here. Nor is any of (A2)
through (A6) or Lucas' theorem, each its own substantial undertaking.
-/

namespace CongruenceTheory

open scoped Classical

variable {r q : ℕ} [NeZero q]

/-- The "translation" group `N = (ℤ/q)^r`, one factor per macroblock. -/
abbrev WreathN (r q : ℕ) := Fin r → Multiplicative (ZMod q)

noncomputable instance : Fintype (WreathN r q) := by unfold WreathN; infer_instance

/-- `S_r` acts on `WreathN r q` by permuting the `r` coordinates. -/
def wreathPhi (r q : ℕ) [NeZero q] : Equiv.Perm (Fin r) →* MulAut (WreathN r q) where
  toFun σ := { toFun := fun f i => f (σ⁻¹ i)
               invFun := fun f i => f (σ i)
               left_inv := fun f => by ext i; simp
               right_inv := fun f => by ext i; simp
               map_mul' := fun f g => by ext i; rfl }
  map_one' := by ext f i; simp
  map_mul' σ τ := by ext f i; simp [mul_inv_rev]

/-- The wreath product `(ℤ/q)^r ⋊ S_r`. -/
abbrev Wreath (r q : ℕ) [NeZero q] := WreathN r q ⋊[wreathPhi r q] Equiv.Perm (Fin r)

theorem card_wreathN : Nat.card (WreathN r q) = q ^ r := by
  rw [show WreathN r q = (Fin r → Multiplicative (ZMod q)) from rfl, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  exact ZMod.card q

theorem card_wreath : Nat.card (Wreath r q) = q ^ r * r.factorial := by
  rw [SemidirectProduct.card, card_wreathN,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- The homomorphism `Multiplicative (ZMod q) →* Equiv.Perm (Fin q)` sending the generator to
powers of a fixed permutation `c` with `c ^ q = 1`. -/
def cPowHom (c : Equiv.Perm (Fin q)) (hc : c ^ q = 1) :
    Multiplicative (ZMod q) →* Equiv.Perm (Fin q) where
  toFun x := c ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    show c ^ (Multiplicative.toAdd (x * y)).val = c ^ (Multiplicative.toAdd x).val *
      c ^ (Multiplicative.toAdd y).val
    rw [← pow_add, show Multiplicative.toAdd (x * y) =
      Multiplicative.toAdd x + Multiplicative.toAdd y from rfl, ZMod.val_add]
    conv_rhs => rw [← Nat.div_add_mod
      ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) q]
    rw [pow_add, pow_mul, hc, one_pow, one_mul]

/-- Glue a pointwise family of block permutations into one permutation of `Fin r × Fin q`,
acting independently and identically-indexed within each block. -/
def blockAction (g : Fin r → Equiv.Perm (Fin q)) : Equiv.Perm (Fin r × Fin q) where
  toFun p := (p.1, g p.1 p.2)
  invFun p := (p.1, (g p.1)⁻¹ p.2)
  left_inv p := by simp
  right_inv p := by simp

omit [NeZero q] in
theorem blockAction_mul (g h : Fin r → Equiv.Perm (Fin q)) :
    blockAction (g * h) = blockAction g * blockAction h := by
  ext p
  · rfl
  · simp [blockAction, Equiv.Perm.mul_apply]

/-- `fn : WreathN r q →* Equiv.Perm (Fin r × Fin q)`, acting on each block `i` via `c ^ (f i)`. -/
def wreathFn (c : Equiv.Perm (Fin q)) (hc : c ^ q = 1) :
    WreathN r q →* Equiv.Perm (Fin r × Fin q) where
  toFun f := blockAction (fun i => cPowHom c hc (f i))
  map_one' := by
    show blockAction (fun i => cPowHom c hc ((1 : WreathN r q) i)) = 1
    simp [blockAction]; rfl
  map_mul' f f' := by
    show blockAction (fun i => cPowHom c hc ((f * f') i)) =
      blockAction (fun i => cPowHom c hc (f i)) * blockAction (fun i => cPowHom c hc (f' i))
    rw [← blockAction_mul]
    congr 1
    funext i
    exact map_mul (cPowHom c hc) (f i) (f' i)

/-- `fg : Equiv.Perm (Fin r) →* Equiv.Perm (Fin r × Fin q)`, permuting the blocks. -/
def wreathFg (r q : ℕ) : Equiv.Perm (Fin r) →* Equiv.Perm (Fin r × Fin q) where
  toFun σ := σ.prodCongr (Equiv.refl (Fin q))
  map_one' := by ext p <;> simp
  map_mul' σ τ := by ext p <;> simp [Equiv.Perm.mul_apply]

theorem wreathFn_wreathPhi_compat (c : Equiv.Perm (Fin q)) (hc : c ^ q = 1)
    (σ : Equiv.Perm (Fin r)) :
    (wreathFn (r := r) c hc).comp ((wreathPhi r q σ).toMonoidHom) =
      (MulAut.conj (wreathFg r q σ)).toMonoidHom.comp (wreathFn (r := r) c hc) := by
  apply MonoidHom.ext
  intro f
  apply Equiv.ext
  intro p
  show (wreathFn c hc (wreathPhi r q σ f)) p =
    (wreathFg r q σ * wreathFn c hc f * (wreathFg r q σ)⁻¹) p
  obtain ⟨i, k⟩ := p
  show blockAction (fun j => cPowHom c hc ((wreathPhi r q σ f) j)) (i, k) =
    (wreathFg r q σ) ((wreathFn c hc f) ((wreathFg r q σ)⁻¹ (i, k)))
  simp only [blockAction, wreathFn, wreathFg, wreathPhi, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.coe_mk, Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map, Equiv.Perm.inv_def]
  simp

/-- **The wreath product `(ℤ/q)^r ⋊ S_r` acts on `Fin r × Fin q`**, via block-wise powers of a
fixed `q`-cycle `c` combined with block permutation. -/
def wreathToPerm (c : Equiv.Perm (Fin q)) (hc : c ^ q = 1) :
    Wreath r q →* Equiv.Perm (Fin r × Fin q) :=
  SemidirectProduct.lift (wreathFn c hc) (wreathFg r q) (wreathFn_wreathPhi_compat c hc)

theorem wreathToPerm_apply (c : Equiv.Perm (Fin q)) (hc : c ^ q = 1) (w : Wreath r q)
    (i : Fin r) (k : Fin q) :
    wreathToPerm (r := r) c hc w (i, k) =
      (w.right i, (c ^ (Multiplicative.toAdd (w.left (w.right i))).val) k) := by
  show (wreathFn c hc w.left * wreathFg r q w.right) (i, k) = _
  simp only [wreathFn, wreathFg, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.Perm.mul_apply,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  rfl

/-- **The wreath product's action on `Fin r × Fin q` is faithful**, given `c` has order exactly
`q` (e.g. `c = finRotate q` for `q ≥ 2`). -/
theorem wreathToPerm_injective (c : Equiv.Perm (Fin q)) (hc : c ^ q = 1)
    (horder : orderOf c = q) : Function.Injective (wreathToPerm (r := r) c hc) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  simp only [Subgroup.mem_bot]
  simp only [MonoidHom.mem_ker] at hw
  have hpt : ∀ i k, wreathToPerm (r := r) c hc w (i, k) = (i, k) := fun i k => by
    rw [hw]; rfl
  have hσ : w.right = 1 := by
    apply Equiv.ext
    intro i
    have h1 := congrArg Prod.fst (hpt i (Classical.arbitrary (Fin q)))
    rw [wreathToPerm_apply] at h1
    simpa using h1
  have hn : w.left = 1 := by
    funext i
    have hval : ∀ k, (c ^ (Multiplicative.toAdd (w.left (w.right i))).val) k = k := fun k => by
      have h2 := congrArg Prod.snd (hpt i k)
      rw [wreathToPerm_apply] at h2
      simpa using h2
    have hcpow : c ^ (Multiplicative.toAdd (w.left (w.right i))).val = 1 :=
      Equiv.ext hval
    rw [← orderOf_dvd_iff_pow_eq_one, horder] at hcpow
    have hlt : (Multiplicative.toAdd (w.left (w.right i))).val < q := ZMod.val_lt _
    have hval0 : (Multiplicative.toAdd (w.left (w.right i))).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hcpow hlt
    rw [hσ] at hval0
    show w.left i = 1
    have hzero : Multiplicative.toAdd (w.left i) = 0 := (ZMod.val_eq_zero _).mp hval0
    exact Multiplicative.toAdd.injective (by rw [hzero]; rfl)
  ext <;> simp [hσ, hn]

/-- `finRotate q` (the standard cyclic rotation of `Fin q`) has order exactly `q`, for `q ≥ 2`. -/
theorem orderOf_finRotate {q : ℕ} (hq : 2 ≤ q) : orderOf (finRotate q) = q := by
  rw [Equiv.Perm.IsCycle.orderOf (isCycle_finRotate_of_le hq), support_finRotate_of_le hq,
    Finset.card_univ, Fintype.card_fin]

theorem finRotate_pow_eq_one {q : ℕ} (hq : 2 ≤ q) : finRotate q ^ q = 1 := by
  have h := pow_orderOf_eq_one (finRotate q)
  rwa [orderOf_finRotate hq] at h

/-- **The concrete wreath product action**, via the standard rotation `c = finRotate q`. -/
noncomputable def wreathToPermRotate (r q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    Wreath r q →* Equiv.Perm (Fin r × Fin q) :=
  wreathToPerm (finRotate q) (finRotate_pow_eq_one hq)

theorem wreathToPermRotate_injective (r q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    Function.Injective (wreathToPermRotate r q hq) :=
  wreathToPerm_injective (finRotate q) (finRotate_pow_eq_one hq) (orderOf_finRotate hq)

end CongruenceTheory
