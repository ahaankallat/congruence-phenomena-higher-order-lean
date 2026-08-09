import Mathlib

/-!
**The group-theoretic core of (A2a)'s "faithfulness" claim.**

The manuscript's proof of (A2a) forms the *bipartite incidence multigraph* of a permutation `g`
with connected block-support hypergraph (black vertices = blocks, white vertices = cycles of `g`,
decorated at each white vertex with the oriented cyclic order `g` induces there) and asserts:
"The automorphism action on this decorated incidence graph is faithful."

Unpacked, an element `φ` of the centralizer of `g` induces the *trivial* automorphism of this
decorated graph exactly when it fixes every black vertex, fixes every white vertex, and respects
the cyclic order trivially at each white vertex — and the last condition, since `φ` commutes with
`g`, means precisely that `φ` fixes some (equivalently every) point on each cycle of `g` (an
element of the centralizer that stabilizes a cycle setwise acts on it as a power of `g`
restricted to that cycle, and *not rotating* the induced cyclic order means that power is trivial
on the cycle). So the faithfulness claim reduces to a clean, self-contained, purely group-theoretic
fact about centralizers, independent of the blocks or the tree structure used elsewhere in (A2a):
an element commuting with `g` that fixes a point on every cycle of `g` is the identity. This is
what `eq_one_of_commute_of_fixed_point_on_every_cycle` proves. The literal incidence-multigraph
formalism (as a `SimpleGraph`/multigraph structure with an explicit `Aut` group) is not separately
built here, since it carries no further mathematical content beyond this fact — the same
honest-reformulation choice `Semiregularity.lean` made for the analogous claim in (A1).
-/

open Equiv

/-- The granular, reusable primitive underlying (A2a)'s faithfulness claim (and, recursively, the
tree-rooted counting bound built on top of it in `A2aOrbitBound.lean`): if `φ` commutes with `g`
and fixes a point `p`, it fixes every point on `p`'s `g`-cycle. Proof: for `q=g^i p`, commuting
gives `φ(g^i p)=g^i(φ p)=g^i p=q`. -/
theorem Perm.fixed_of_commute_of_fixed_point {α : Type*} {g φ : Perm α} (hcomm : Commute φ g)
    {p q : α} (hp : φ p = p) (hpq : g.SameCycle p q) : φ q = q := by
  obtain ⟨i, hi⟩ := hpq
  have h1 : (φ * g ^ i) p = (g ^ i * φ) p := by rw [(hcomm.zpow_right i).eq]
  simp only [Perm.mul_apply] at h1
  rw [hp, hi] at h1
  exact h1

/-- The group-theoretic heart of (A2a)'s faithfulness claim: an element of the centralizer of `g`
that fixes a point on every cycle of `g` is the identity. (Equivalently: the action of any
subgroup of the centralizer on the decorated bipartite incidence multigraph of `g` — blocks
versus cycles, with the induced cyclic order recorded at each cycle — is faithful, since an
element inducing the trivial automorphism of that decorated graph fixes a point on every cycle.) -/
theorem eq_one_of_commute_of_fixed_point_on_every_cycle {α : Type*} {g φ : Perm α}
    (hcomm : Commute φ g) (hfix : ∀ x : α, ∃ y : α, g.SameCycle x y ∧ φ y = y) :
    φ = 1 := by
  ext x
  obtain ⟨y, hxy, hfixy⟩ := hfix x
  simpa using Perm.fixed_of_commute_of_fixed_point hcomm hfixy hxy.symm
