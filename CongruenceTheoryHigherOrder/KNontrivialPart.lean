import Mathlib
import CongruenceTheory.Basic
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionRespects
import CongruenceTheoryHigherOrder.ConnectedCount

/-!
**Every permutation contributing to `K_r(q)` (`r\ge2`) has a nontrivial cycle.** The identity
permutation trivially respects every partition, so `\pi(1)=\bot` (the discrete partition); for
`r\ge2`, `\bot\ne\top`, so the identity is excluded from `K_r(q)=\sum_{\pi(g)=\top}ci(g)`'s sum,
i.e. every contributing `g` moves some point, giving `g.cycleType\ne0`. This is the building
block behind "every monomial of `K_j(p)` (`j\ge2`) has at least one nontrivial part," needed for
the witness-depth (`\delta_p`) lower bound.
-/

namespace CongruenceTheory

open scoped Classical

variable {r q : ℕ}

/-- The identity permutation trivially respects every partition. -/
theorem respects_one (τ : PartLat r) : Respects τ (1 : Equiv.Perm (Fin r × Fin q)) := by
  intro x
  show x.1 ∈ (τ.part x.1 : Finset (Fin r))
  exact τ.mem_part_self.mpr (Finset.mem_univ x.1)

/-- Consequently `\pi(g)` is `\le` every partition when `g=1`. -/
theorem piOf_one_le (τ : PartLat r) :
    piOf (1 : Equiv.Perm (Fin r × Fin q)) ≤ τ :=
  piOf_le_of_respects (respects_one τ)

/-- **`\pi(1)=\bot`**, the discrete partition. -/
theorem piOf_one_eq_bot : piOf (1 : Equiv.Perm (Fin r × Fin q)) = ⊥ :=
  le_antisymm (piOf_one_le ⊥) bot_le

/-- **`\bot\ne\top` in `PartLat r` when `r\ge2`.** -/
theorem bot_ne_top_of_two_le (hr : 2 ≤ r) : (⊥ : PartLat r) ≠ (⊤ : PartLat r) := by
  intro heq
  have hcard : (⊥ : PartLat r).parts.card = (⊤ : PartLat r).parts.card := by rw [heq]
  rw [Finpartition.card_bot] at hcard
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hsub := Finpartition.parts_top_subsingleton (Finset.univ : Finset (Fin r))
  have htop_le : (⊤ : PartLat r).parts.card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => hsub ha hb)
  omega

/-- **The identity permutation is excluded from `K_r(q)`'s connectivity sum when `r\ge2`.** -/
theorem piOf_one_ne_top (hr : 2 ≤ r) :
    piOf (1 : Equiv.Perm (Fin r × Fin q)) ≠ (⊤ : PartLat r) := by
  rw [piOf_one_eq_bot]
  exact bot_ne_top_of_two_le hr

/-- **Every permutation `g` contributing to `K_r(q)`'s connectivity sum (`\pi(g)=\top`), for
`r\ge2`, has a nontrivial cycle**: `g\ne1`, so `g.cycleType\ne0`. -/
theorem cycleType_ne_zero_of_piOf_eq_top {g : Equiv.Perm (Fin r × Fin q)} (hr : 2 ≤ r)
    (hg : piOf g = (⊤ : PartLat r)) : g.cycleType ≠ 0 := by
  intro hz
  apply piOf_one_ne_top hr
  rw [← hg]
  congr 1
  have : g = 1 := by
    rw [← Equiv.Perm.cycleType_eq_zero]
    exact hz
  rw [this]

#print axioms respects_one
#print axioms piOf_one_le
#print axioms piOf_one_eq_bot
#print axioms bot_ne_top_of_two_le
#print axioms piOf_one_ne_top
#print axioms cycleType_ne_zero_of_piOf_eq_top

end CongruenceTheory
