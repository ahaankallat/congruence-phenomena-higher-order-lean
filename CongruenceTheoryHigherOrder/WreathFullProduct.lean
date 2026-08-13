import Mathlib
import CongruenceTheoryHigherOrder.WreathProduct

/-!
**The *full* wreath product `S_q ≀ S_r = (\operatorname{Perm}(\operatorname{Fin} q))^r ⋊ S_r`**,
acting on `Fin r × Fin q` (`r` blocks of size `q`, with the *full* symmetric group on each
block, not just the cyclic rotations `WreathProduct.lean` builds for `(A1)`). This is the group
`thm:atomic-connected-content`'s `(A2)` argument needs (as `\widetilde H = S_q\wr S_{r-2}$, after
setting `r := $ the number of non-root blocks): `(A1)`'s `WreathProduct.lean` already supplies
every generic piece this needs — `blockAction` (gluing a family of per-block permutations,
already stated for *arbitrary* `g : \operatorname{Fin} r → \operatorname{Perm}(\operatorname{Fin}
q)$, not just rotations) and `wreathFg` (permuting the `r` blocks) — so the only new content is
swapping the "translation" group from `(\mathbb Z/q)^r` to the full `(\operatorname{Perm}
(\operatorname{Fin} q))^r$, and the embedding into `\operatorname{Perm}(\operatorname{Fin} r
\times \operatorname{Fin} q)` is in fact *simpler* here than in `(A1)`'s case: `blockAction`
itself already is the required homomorphism (no `cPowHom` detour through a single fixed cycle's
powers is needed, since every block permutation is directly available, not just rotations of a
generator), and faithfulness needs no order hypothesis at all.
-/

namespace CongruenceTheory

open scoped Classical

variable {r q : ℕ}

/-- The "translation" group `N = \operatorname{Perm}(\operatorname{Fin} q)^r`, one full
symmetric-group factor per block. -/
abbrev WreathFullN (r q : ℕ) := Fin r → Equiv.Perm (Fin q)

noncomputable instance : Fintype (WreathFullN r q) := by unfold WreathFullN; infer_instance

/-- `S_r` acts on `WreathFullN r q` by permuting the `r` coordinates. -/
def wreathFullPhi (r q : ℕ) : Equiv.Perm (Fin r) →* MulAut (WreathFullN r q) where
  toFun σ := { toFun := fun f i => f (σ⁻¹ i)
               invFun := fun f i => f (σ i)
               left_inv := fun f => by ext i; simp
               right_inv := fun f => by ext i; simp
               map_mul' := fun f g => by ext i; rfl }
  map_one' := by ext f i; simp
  map_mul' σ τ := by ext f i; simp [mul_inv_rev]

/-- **The full wreath product `S_q ≀ S_r = \operatorname{Perm}(\operatorname{Fin} q)^r ⋊ S_r`.** -/
abbrev WreathFull (r q : ℕ) := WreathFullN r q ⋊[wreathFullPhi r q] Equiv.Perm (Fin r)

theorem card_wreathFullN : Nat.card (WreathFullN r q) = (Nat.factorial q) ^ r := by
  rw [show WreathFullN r q = (Fin r → Equiv.Perm (Fin q)) from rfl, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem card_wreathFull : Nat.card (WreathFull r q) = (Nat.factorial q) ^ r * r.factorial := by
  rw [SemidirectProduct.card, card_wreathFullN,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- **`WreathFullN r q →* \operatorname{Perm}(\operatorname{Fin} r \times \operatorname{Fin} q)$,
via `blockAction` directly** (no detour through powers of a single generator, unlike `(A1)`'s
`wreathFn`). -/
def wreathFullFn (r q : ℕ) : WreathFullN r q →* Equiv.Perm (Fin r × Fin q) where
  toFun := blockAction
  map_one' := by ext p <;> simp [blockAction]
  map_mul' f f' := blockAction_mul f f'

theorem wreathFullFn_wreathFullPhi_compat (σ : Equiv.Perm (Fin r)) :
    (wreathFullFn r q).comp ((wreathFullPhi r q σ).toMonoidHom) =
      (MulAut.conj (wreathFg r q σ)).toMonoidHom.comp (wreathFullFn r q) := by
  apply MonoidHom.ext
  intro f
  apply Equiv.ext
  intro p
  show (wreathFullFn r q (wreathFullPhi r q σ f)) p =
    (wreathFg r q σ * wreathFullFn r q f * (wreathFg r q σ)⁻¹) p
  obtain ⟨i, k⟩ := p
  show blockAction (fun j => (wreathFullPhi r q σ f) j) (i, k) =
    (wreathFg r q σ) ((blockAction f) ((wreathFg r q σ)⁻¹ (i, k)))
  simp only [blockAction, wreathFg, wreathFullPhi, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.coe_mk, Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map, Equiv.Perm.inv_def]
  simp

/-- **The full wreath product `S_q ≀ S_r` acts on `\operatorname{Fin} r \times \operatorname{Fin}
q`**, block permutations acting directly on each block combined with block permutation. -/
def wreathFullToPerm (r q : ℕ) : WreathFull r q →* Equiv.Perm (Fin r × Fin q) :=
  SemidirectProduct.lift (wreathFullFn r q) (wreathFg r q) wreathFullFn_wreathFullPhi_compat

theorem wreathFullToPerm_apply (w : WreathFull r q) (i : Fin r) (k : Fin q) :
    wreathFullToPerm r q w (i, k) = (w.right i, w.left (w.right i) k) := by
  show (wreathFullFn r q w.left * wreathFg r q w.right) (i, k) = _
  simp only [wreathFullFn, wreathFg, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.Perm.mul_apply,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  rfl

/-- **`wreathFullToPerm` is injective** (given `q ≠ 0`, so `\operatorname{Fin} q` is nonempty) —
the full wreath product embeds faithfully, with no order hypothesis needed (unlike `(A1)`'s
rotation-only case). For `q = 0` the target `\operatorname{Perm}(\operatorname{Fin} r \times
\operatorname{Fin} 0)` is trivial while `\operatorname{Perm}(\operatorname{Fin} r)$ (a summand of
the domain) is not, so injectivity genuinely needs `q \ne 0`. -/
theorem wreathFullToPerm_injective (r q : ℕ) [NeZero q] :
    Function.Injective (wreathFullToPerm r q) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hpt : ∀ i k, wreathFullToPerm r q w (i, k) = (i, k) := fun i k => by rw [hw]; rfl
  have hright : w.right = 1 := by
    apply Equiv.ext
    intro i
    have h1 := congrArg Prod.fst (hpt i (Classical.arbitrary (Fin q)))
    rw [wreathFullToPerm_apply] at h1
    simpa using h1
  have hleft : w.left = 1 := by
    funext i
    apply Equiv.ext
    intro k
    have h2 := congrArg Prod.snd (hpt i k)
    rw [wreathFullToPerm_apply, hright] at h2
    simpa using h2
  exact SemidirectProduct.ext hleft hright

#print axioms card_wreathFullN
#print axioms card_wreathFull
#print axioms wreathFullFn_wreathFullPhi_compat
#print axioms wreathFullToPerm_apply
#print axioms wreathFullToPerm_injective

end CongruenceTheory
