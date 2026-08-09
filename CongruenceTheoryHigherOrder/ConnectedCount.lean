import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing
import CongruenceTheoryHigherOrder.PartitionRespects

/-!
**Completes the manuscript's own supporting claim** (stated right after `K_r(q)`'s definition in
`ConnectedCumulant.lean`, not itself a separately labeled result): "coefficientwise, `K_r(q)`
counts permutations whose cycle-support hypergraph on `r` prescribed blocks of size `q` is
connected." `PartitionGluing.lean`/`PartitionRespects.lean` identified `K_r(q)`'s defining product
`∏_{B∈τ.parts}C_{|B|q}` with `∑_{g:Respects τ g}ci(g)` for every partition `τ`. This file supplies
the missing piece: a canonical **cycle-support connectivity partition** `π(g)` for every
permutation `g`, proves `Respects τ g ↔ π(g) ≤ τ`, and runs a genuine **Möbius-inversion**
argument (Mathlib's `IncidenceAlgebra.moebius_inversion_bot`) to conclude
`K_r(q) = ∑_{g : π(g)=⊤} ci(g)` (**`K_eq_Gfun_top`**) — exactly the manuscript's remark, now a
proved theorem.

**Construction of `π(g)`**: `touches g i j` holds when some point of macroblock `i` is sent by `g`
into macroblock `j`; `graphOf g := SimpleGraph.fromRel (touches g)` is the resulting connectivity
graph on `[r]`; `piOf g := Finpartition.ofSetoid (graphOf g).reachableSetoid` groups macroblocks by
graph-reachability, using Mathlib's `Finpartition.ofSetoid` (a setoid on a finite type induces a
partition by equivalence classes) applied to `SimpleGraph.reachableSetoid` (reachability is always
an equivalence relation). **`respects_iff_piOf_le`** is the key combinatorial fact:
`Respects τ g ↔ π(g) ≤ τ` — one direction chases a single reachability witness through
`Finpartition.exists_le_of_le`-style refinement reasoning directly; the other propagates
`Respects τ g`'s pointwise block-preservation along a `Relation.ReflTransGen` induction on
`SimpleGraph.reachable_iff_reflTransGen`, using that "same `τ`-block" is already an equivalence
relation.

**Möbius inversion**: with `Ffun τ := ∑_{g:Respects τ g}ci(g)` (`= ∏_{B∈τ.parts}C_{|B|q}`, via
`Ffun_eq_prod_C`) and `Gfun π := ∑_{g:π(g)=π}ci(g)`, grouping `g`'s by their own `π(g)` value gives
`Ffun τ = ∑_{π≤τ}Gfun π` (`Ffun_eq_sum_Gfun`, via Mathlib's `Finset.sum_fiberwise_of_maps_to`).
Applying Mathlib's `IncidenceAlgebra.moebius_inversion_bot` **coefficientwise** (extracting each
monomial coefficient of these `MvPolynomial ℕ ℤ`-valued sums, to stay inside `ℤ` throughout and
avoid casting `IncidenceAlgebra.mu`'s value across rings) and recombining via `MvPolynomial.ext`
gives `Gfun ⊤ = ∑_{π}μ(π,⊤)·Ffun π = K_r(q)` (`K`'s own definition, literally).

**Honest scope note**: this closes out the manuscript's supporting remark completely, but
`thm:atomic-connected-content` itself — the wreath-product stabilizer bounds (A1)/(A2), the
bipartite incidence-graph automorphism induction (A2a), the moment-cumulant expansion (A4), the
mod-`p` algebraic-independence argument (A5), the falling-factorial Vandermonde identity (A6)
combined with `HypertreeEnumerator.lean`, and Lucas' theorem — remains entirely open, and is
genuinely research-scale work beyond the scope attempted here.
-/

namespace CongruenceTheory

open scoped Classical

variable {r q : ℕ}

/-- `i` and `j` are directly connected by some cycle of `g`: some point of macroblock `i` is
sent by `g` into macroblock `j`. -/
def touches (g : Equiv.Perm (Fin r × Fin q)) (i j : Fin r) : Prop :=
  ∃ x : Fin r × Fin q, x.1 = i ∧ (g x).1 = j

noncomputable instance (g : Equiv.Perm (Fin r × Fin q)) : DecidableRel (touches (q := q) g) :=
  Classical.decRel _

/-- The cycle-support connectivity graph of `g` on the `r` macroblocks: `i` and `j` are
adjacent if some cycle of `g` visits both. -/
noncomputable def graphOf (g : Equiv.Perm (Fin r × Fin q)) : SimpleGraph (Fin r) :=
  SimpleGraph.fromRel (touches (q := q) g)

noncomputable instance (g : Equiv.Perm (Fin r × Fin q)) :
    DecidableRel (graphOf (q := q) g).Adj := by
  unfold graphOf; infer_instance

noncomputable instance (g : Equiv.Perm (Fin r × Fin q)) :
    DecidableRel (graphOf (q := q) g).Reachable := by
  classical infer_instance

/-- The canonical cycle-support connectivity partition `π(g)` of `[r]`: macroblocks are grouped
by reachability in `g`'s connectivity graph. -/
noncomputable def piOf (g : Equiv.Perm (Fin r × Fin q)) : PartLat r :=
  Finpartition.ofSetoid (graphOf (q := q) g).reachableSetoid

theorem respects_of_piOf_le {τ : PartLat r} {g : Equiv.Perm (Fin r × Fin q)} (h : piOf g ≤ τ) :
    Respects τ g := by
  intro x
  have hreach : (graphOf g).Reachable x.1 (g x).1 := by
    by_cases heq : x.1 = (g x).1
    · rw [heq]
    · exact SimpleGraph.Adj.reachable
        (SimpleGraph.fromRel_adj _ _ _ |>.mpr ⟨heq, Or.inl ⟨x, rfl, rfl⟩⟩)
  have hmem : (g x).1 ∈ (piOf g).part x.1 := by
    unfold piOf
    exact (Finpartition.mem_part_ofSetoid_iff_rel).mpr hreach
  obtain ⟨c, hc, hsub⟩ := h ((piOf g).part_mem.mpr (Finset.mem_univ x.1))
  have hxc : x.1 ∈ c := hsub ((piOf g).mem_part_self.mpr (Finset.mem_univ x.1))
  have hgxc : (g x).1 ∈ c := hsub hmem
  rwa [τ.part_eq_of_mem hc hxc]

theorem piOf_le_of_respects {τ : PartLat r} {g : Equiv.Perm (Fin r × Fin q)} (h : Respects τ g) :
    piOf g ≤ τ := by
  have hstep : ∀ b c : Fin r, (graphOf g).Adj b c → τ.part b = τ.part c := by
    intro b c hbc
    unfold graphOf at hbc
    rw [SimpleGraph.fromRel_adj (touches (q := q) g) b c] at hbc
    rcases hbc.2 with ⟨x, hx1, hx2⟩ | ⟨x, hx1, hx2⟩
    · have hmem : c ∈ (τ.part b : Finset (Fin r)) := by rw [← hx1, ← hx2]; exact h x
      exact ((τ.mem_part_iff_part_eq_part (Finset.mem_univ c) (Finset.mem_univ b)).mp hmem).symm
    · have hmem : b ∈ (τ.part c : Finset (Fin r)) := by rw [← hx1, ← hx2]; exact h x
      exact (τ.mem_part_iff_part_eq_part (Finset.mem_univ b) (Finset.mem_univ c)).mp hmem
  have hkey : ∀ i j : Fin r, (graphOf g).Reachable i j → τ.part i = τ.part j := by
    intro i j hij
    rw [SimpleGraph.reachable_iff_reflTransGen] at hij
    induction hij with
    | refl => rfl
    | tail _ hbc ih => rw [ih]; exact hstep _ _ hbc
  intro b hb
  obtain ⟨i0, hi0⟩ := (piOf g).nonempty_of_mem_parts hb
  refine ⟨τ.part i0, τ.part_mem.mpr (Finset.mem_univ i0), ?_⟩
  intro j hj
  have hbeq : (piOf g).part i0 = b := (piOf g).part_eq_of_mem hb hi0
  have hj' : j ∈ (piOf g).part i0 := hbeq ▸ hj
  unfold piOf at hj'
  have hreach : (graphOf g).Reachable i0 j := Finpartition.mem_part_ofSetoid_iff_rel.mp hj'
  rw [hkey i0 j hreach]
  exact τ.mem_part_self.mpr (Finset.mem_univ j)

/-- **`Respects τ g` iff `π(g) ≤ τ`**: `g` respects a partition exactly when its canonical
cycle-support connectivity partition refines it. -/
theorem respects_iff_piOf_le {τ : PartLat r} {g : Equiv.Perm (Fin r × Fin q)} :
    Respects τ g ↔ piOf g ≤ τ :=
  ⟨piOf_le_of_respects, respects_of_piOf_le⟩

/-- The sum of `ci` over permutations whose canonical connectivity partition is exactly `π`. -/
noncomputable def Gfun (π : PartLat r) : MvPolynomial ℕ ℤ :=
  ∑ g ∈ (Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter (fun g => piOf g = π), ci g

/-- The sum of `ci` over permutations respecting `τ` (i.e. `π(g) ≤ τ`), matching
`sum_ci_respects_eq_prod_C`. -/
noncomputable def Ffun (τ : PartLat r) : MvPolynomial ℕ ℤ :=
  ∑ g ∈ (Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter (fun g => Respects τ g), ci g

theorem Ffun_eq_sum_ci_respects (τ : PartLat r) :
    Ffun (q := q) τ = ∑ g : {g : Equiv.Perm (Fin r × Fin q) // Respects τ g}, ci g.1 := by
  unfold Ffun
  exact Finset.sum_subtype (p := Respects τ)
    ((Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter (fun g => Respects τ g))
    (fun g => by simp) ci

theorem Ffun_eq_sum_Gfun (τ : PartLat r) :
    Ffun (q := q) τ = ∑ π ∈ Finset.Iic τ, Gfun (q := q) π := by
  unfold Ffun Gfun
  have hmaps : ∀ g ∈ (Finset.univ : Finset (Equiv.Perm (Fin r × Fin q))).filter
      (fun g => Respects τ g), piOf (q := q) g ∈ Finset.Iic τ :=
    fun g hg => Finset.mem_Iic.mpr (respects_iff_piOf_le.mp (Finset.mem_filter.mp hg).2)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps ci]
  apply Finset.sum_congr rfl
  intro π hπ
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨_, hg⟩; exact hg
  · intro hg
    exact ⟨respects_iff_piOf_le.mpr (hg ▸ Finset.mem_Iic.mp hπ), hg⟩

theorem Ffun_eq_prod_C (τ : PartLat r) : Ffun (q := q) τ = ∏ B ∈ τ.parts, C (B.card * q) := by
  rw [Ffun_eq_sum_ci_respects]; exact sum_ci_respects_eq_prod_C τ

/-- **`K_r(q)` counts permutations whose cycle-support hypergraph on `r` prescribed blocks of
size `q` is connected**, matching the manuscript's own remark right after `K_r(q)`'s definition:
`K_r(q) = ∑_{g : π(g)=⊤} ci(g)`, the sum of cycle-indicator monomials over exactly those
permutations whose canonical connectivity partition is the trivial one-block partition. -/
theorem K_eq_Gfun_top (r q : ℕ) : K r q = Gfun (q := q) (⊤ : PartLat r) := by
  apply MvPolynomial.ext
  intro d
  have hcoeffFG : ∀ τ : PartLat r, MvPolynomial.coeff d (Ffun (q := q) τ) =
      ∑ π ∈ Finset.Iic τ, MvPolynomial.coeff d (Gfun (q := q) π) := by
    intro τ
    rw [Ffun_eq_sum_Gfun, MvPolynomial.coeff_sum]
  have hinv := IncidenceAlgebra.moebius_inversion_bot
    (fun π => MvPolynomial.coeff d (Gfun (q := q) π))
    (fun τ => MvPolynomial.coeff d (Ffun (q := q) τ))
    hcoeffFG (⊤ : PartLat r)
  rw [hinv]
  unfold K
  rw [MvPolynomial.coeff_sum, Finset.Iic_top]
  apply Finset.sum_congr rfl
  intro π _
  rw [show (IncidenceAlgebra.mu ℤ π ⊤ : ℤ) • (∏ B ∈ π.parts, C (B.card * q)) =
      MvPolynomial.C (IncidenceAlgebra.mu ℤ π ⊤) * ∏ B ∈ π.parts, C (B.card * q) from
    MvPolynomial.smul_eq_C_mul _ _]
  rw [MvPolynomial.coeff_C_mul, Ffun_eq_prod_C]

end CongruenceTheory
