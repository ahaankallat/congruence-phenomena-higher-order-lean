import Mathlib

/-!
**A general free-action cardinality-divisibility fact**, extracted while investigating (A2a)'s
remaining "`u` is a cut vertex" case. That case's final step needs
"`(R_u-1)!/((a_0-1)!∏_τ(a_τ!)^{m_τ}m_τ!)` is an integer" — a "partition into groups of prescribed
sizes, with equal-size groups within each class `τ` counted as indistinguishable" count. The
`m_τ!` in the denominator is exactly the order of the group `∏_τ Equiv.Perm (Fin m_τ)` that acts
(freely, since the constituent groups are pairwise disjoint and nonempty) by permuting which
labeled slot within each size-class holds which content — so this file's `card_dvd_of_free` is
precisely the general fact needed to justify that division producing an integer. The same
principle also underlies the "there are `(r-1)!/(d!(h-1)!^d)` possible block partitions" remark in
`HypertreeEnumerator.lean`'s own manuscript source, which that file's Lean development sidesteps
entirely by staying in multiplied-out form (`× (h-1)!^d`) rather than proving the division exact.

**Honest scope note**: what's proved here is the *general* fact (a free finite group action's
order divides the cardinality of the type it acts on). Applying it to either `OrderedBlocks`
(`HypertreeEnumerator.lean`) or the cut-vertex case's mixed-size block collection requires
constructing the actual permutation action on the relevant Fintype (`OrderedBlocks` is defined
recursively, not as a flat tuple, so the natural "permute the order of the `d` blocks" action
needs an explicit intermediate equivalence to a flat-tuple representation) and verifying it is
free there — that connective work is not carried out here.
-/

open MulAction

/-- **A free action of a finite group on a finite type: the group's order divides the type's
cardinality.** Every orbit has size exactly `Nat.card G` (orbit-stabilizer, with trivial
stabilizer from freeness), and the type is partitioned into orbits
(`MulAction.selfEquivSigmaOrbits'`). -/
theorem card_dvd_of_free {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : X, g • x ≠ x) :
    Fintype.card G ∣ Fintype.card X := by
  classical
  have horbit : ∀ x : X, Nat.card (MulAction.orbit G x) = Nat.card G := by
    intro x
    have hstab : MulAction.stabilizer G x = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      by_contra hg1
      exact hfree g hg1 x (MulAction.mem_stabilizer_iff.mp hg)
    have h1 : Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) =
        Nat.card G := by
      have h2 : Nat.card (MulAction.orbit G x) = (MulAction.stabilizer G x).index := by
        rw [Subgroup.index_eq_card]
        exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)
      rw [h2]
      exact Subgroup.index_mul_card _
    rw [hstab] at h1
    simpa using h1
  have hequiv := MulAction.selfEquivSigmaOrbits' G X
  have hcard : Fintype.card X =
      ∑ ω : orbitRel.Quotient G X, Fintype.card (orbitRel.Quotient.orbit ω) :=
    (Fintype.card_congr hequiv).trans Fintype.card_sigma
  rw [hcard]
  apply Finset.dvd_sum
  intro ω _
  rw [orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
  have heq := horbit (Quotient.out ω)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at heq
  rw [heq]
