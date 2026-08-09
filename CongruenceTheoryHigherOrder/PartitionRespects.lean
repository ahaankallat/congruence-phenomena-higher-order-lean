import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheoryHigherOrder.ConnectedCumulant
import CongruenceTheoryHigherOrder.PartitionGluing

/-!
**Second step toward the manuscript's own supporting claim** (stated right after `K_r(q)`'s
definition in `ConnectedCumulant.lean`, not itself a separately labeled result) that
"coefficientwise, `K_r(q)` counts permutations whose cycle-support hypergraph on `r` prescribed
blocks of size `q` is connected." `PartitionGluing.lean` gave a permutation-native realization of
`K_r(q)`'s defining product `∏_{B∈τ.parts}C_{|B|q}` via `assemble : PartitionPerm τ → Equiv.Perm
(Fin r×Fin q)`. This file shows `assemble` is exactly a **bijection** onto the permutations
*respecting* `τ`'s block structure (mapping every macroblock into itself, `Respects`), completing
the identification `∏_{B∈τ.parts}C_{|B|q} = ∑_{g:Respects τ g}ci(g)` (`sum_ci_respects_eq_prod_C`)
— the permutation-native form of `K_r(q)`'s own defining product, one Möbius-inversion step short
of the "counts connected permutations" claim itself.

**Key steps**: `assemble_apply` computes `assemble p` pointwise, via a general fact about
`Finset.noncommProd` of pairwise-disjoint permutations (`noncommProd_apply_of_forall_others_fix`:
if only one factor can move a point, `noncommProd` at that point reduces to that factor's action
— proved by induction on the underlying `Finset`, using a short direct argument
(`Equiv.Perm.Disjoint.apply_eq_self_of_ne`) that a permutation disjoint from `τ` fixes every point
`τ` moves to). `restrictP` is the inverse direction, restricting a `Respects τ g` permutation to
each block via Mathlib's `Equiv.Perm.subtypePerm`. `assemble_restrictP`/`restrictP_assemble` show
these are mutually inverse, packaged as the equivalence `assembleEquiv`.

**Honest scope note**: this identifies `K_r(q)`'s defining product with a sum over
`τ`-respecting permutations, but reaching `K_r(q)` itself (the Möbius-alternating sum over *all*
`τ∈PartLat r`) still needs a canonical cycle-support connectivity partition `π(g)` for each
permutation (showing `Respects τ g ↔ π(g) ≤ τ`) and the Möbius-inversion argument identifying
`K_r(q)` with `∑_{π(g)=⊤}ci(g)`. Neither is attempted here, nor is any part of
`thm:atomic-connected-content` itself (the wreath-product stabilizer bounds, the incidence-graph
automorphism induction, the mod-`p` algebraic-independence argument, Lucas' theorem).
-/

namespace CongruenceTheory

open scoped Classical

variable {r q : ℕ}

/-- If `Disjoint σ τ` and `τ` moves `x`, then `σ` fixes `τ x` — a disjoint permutation cannot
touch a point another permutation has just moved to. -/
theorem Equiv.Perm.Disjoint.apply_eq_self_of_ne {α : Type*} {σ τ : Equiv.Perm α}
    (h : Equiv.Perm.Disjoint σ τ) {x : α} (hx : τ x ≠ x) : σ (τ x) = τ x := by
  rcases h (τ x) with h1 | h2
  · exact h1
  · exact absurd (τ.injective h2) hx

/-- If `f : ι → Perm α` is pairwise disjoint over `s`, and some `i₀ ∈ s` is the only index
that can move `x`, then `noncommProd` at `x` reduces to `f i₀`'s action. -/
theorem noncommProd_apply_of_forall_others_fix {ι α : Type*} [DecidableEq ι]
    (f : ι → Equiv.Perm α) :
    ∀ (s : Finset ι) (hs : (s : Set ι).Pairwise fun i j => Equiv.Perm.Disjoint (f i) (f j))
      (i₀ : ι) (_ : i₀ ∈ s) (x : α), (∀ j ∈ s, j ≠ i₀ → f j x = x) →
      (s.noncommProd f (hs.imp (fun _ _ => Equiv.Perm.Disjoint.commute))) x = f i₀ x := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ i₀ hi₀; exact absurd hi₀ (Finset.notMem_empty i₀)
  | insert j s hj ih =>
    intro hs i₀ hi₀ x hfix
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj, Equiv.Perm.mul_apply]
    have hs' : (s : Set ι).Pairwise fun i k => Equiv.Perm.Disjoint (f i) (f k) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rcases Finset.mem_insert.mp hi₀ with rfl | hi₀'
    · have hallfix : ∀ y ∈ s, f y x = x :=
        fun y hy => hfix y (Finset.mem_insert_of_mem hy) (fun he => hj (he ▸ hy))
      have hsfix : (s.noncommProd f (hs'.imp (fun _ _ => Equiv.Perm.Disjoint.commute))) x = x :=
        Finset.noncommProd_induction s f _ (fun g => g x = x)
          (fun a b ha hb => by rw [Equiv.Perm.mul_apply, hb, ha]) rfl hallfix
      rw [hsfix]
    · have hjx : f j x = x := hfix j (Finset.mem_insert_self j s) (fun he => hj (he ▸ hi₀'))
      have hfix' : ∀ k ∈ s, k ≠ i₀ → f k x = x := fun k hk hne =>
        hfix k (Finset.mem_insert_of_mem hk) hne
      have hrec := ih hs' i₀ hi₀' x hfix'
      rw [hrec]
      by_cases hxi : f i₀ x = x
      · rw [hxi, hjx]
      · exact Equiv.Perm.Disjoint.apply_eq_self_of_ne
          (hs (Finset.mem_insert_self j s) (Finset.mem_insert_of_mem hi₀')
            (fun he => hj (he ▸ hi₀'))) hxi

/-- `g` respects `τ`'s block structure: every point stays within its own macroblock. -/
def Respects (τ : PartLat r) (g : Equiv.Perm (Fin r × Fin q)) : Prop :=
  ∀ x : Fin r × Fin q, (g x).1 ∈ (τ.part x.1 : Finset (Fin r))

theorem assemble_apply {τ : PartLat r} (p : PartitionPerm (q := q) τ) (x : Fin r × Fin q) :
    assemble p x = extendB p ⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩ x := by
  unfold assemble
  exact noncommProd_apply_of_forall_others_fix (fun B => extendB p B) τ.parts.attach
    (fun B1 _ B2 _ hne => extendB_disjoint p hne)
    ⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩ (Finset.mem_attach _ _) x
    (fun B _ hne => Equiv.Perm.extendDomain_apply_not_subtype _ _
      (fun hxB => hne (Subtype.ext (τ.part_eq_of_mem B.2 hxB).symm)))

theorem respects_assemble {τ : PartLat r} (p : PartitionPerm (q := q) τ) :
    Respects τ (assemble p) := by
  intro x
  rw [assemble_apply p x]
  unfold extendB
  set B : τ.parts := ⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩
  by_cases hxB : x.1 ∈ (B : Finset (Fin r))
  · rw [Equiv.Perm.extendDomain_apply_subtype (p B)
      (Equiv.refl (blockType (q := q) (B : Finset (Fin r)))) hxB]
    exact ((p B) ⟨x, hxB⟩).2
  · exact absurd (τ.mem_part_self.mpr (Finset.mem_univ x.1)) hxB

/-- The restriction of a `τ`-respecting permutation to a single block `B`. -/
noncomputable def restrictP {τ : PartLat r} (g : Equiv.Perm (Fin r × Fin q)) (hg : Respects τ g)
    (B : τ.parts) : Equiv.Perm (blockType (q := q) (B : Finset (Fin r))) :=
  g.subtypePerm (p := fun x : Fin r × Fin q => x.1 ∈ (B : Finset (Fin r))) (fun x => by
    constructor
    · intro hgx
      rw [τ.eq_of_mem_parts B.2 (τ.part_mem.mpr (Finset.mem_univ x.1)) hgx (hg x)]
      exact τ.mem_part_self.mpr (Finset.mem_univ x.1)
    · intro hx
      rw [← τ.part_eq_of_mem B.2 hx]
      exact hg x)

theorem assemble_restrictP {τ : PartLat r} (g : Equiv.Perm (Fin r × Fin q)) (hg : Respects τ g) :
    assemble (fun B => restrictP g hg B) = g := by
  apply Equiv.ext
  intro x
  rw [assemble_apply (fun B => restrictP g hg B) x]
  set B : τ.parts := ⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩
  have hx1B : x.1 ∈ (B : Finset (Fin r)) := τ.mem_part_self.mpr (Finset.mem_univ x.1)
  unfold extendB blockType
  rw [Equiv.Perm.extendDomain_apply_subtype (restrictP g hg B)
    (Equiv.refl (blockType (q := q) (B : Finset (Fin r)))) hx1B]
  simp only [Equiv.refl_apply, Equiv.refl_symm]
  unfold restrictP
  rw [Equiv.Perm.subtypePerm_apply]

theorem restrictP_assemble {τ : PartLat r} (p : PartitionPerm (q := q) τ) :
    (fun B => restrictP (assemble p) (respects_assemble p) B) = p := by
  funext B
  apply Equiv.ext
  intro y
  obtain ⟨x, hx⟩ := y
  unfold restrictP
  rw [Equiv.Perm.subtypePerm_apply]
  apply Subtype.ext
  show assemble p x = ((p B) ⟨x, hx⟩ : blockType (q := q) (B : Finset (Fin r))).1
  rw [assemble_apply p x]
  have hBeq : (⟨τ.part x.1, τ.part_mem.mpr (Finset.mem_univ x.1)⟩ : τ.parts) = B :=
    Subtype.ext (τ.part_eq_of_mem B.2 hx)
  rw [hBeq]
  unfold extendB blockType
  rw [Equiv.Perm.extendDomain_apply_subtype (p B)
    (Equiv.refl (blockType (q := q) (B : Finset (Fin r)))) hx]
  simp only [Equiv.refl_apply, Equiv.refl_symm]

/-- **`assemble` is a bijection** between `PartitionPerm τ` and the permutations of
`Fin r × Fin q` respecting `τ`'s block structure. -/
noncomputable def assembleEquiv (τ : PartLat r) :
    PartitionPerm (q := q) τ ≃ {g : Equiv.Perm (Fin r × Fin q) // Respects τ g} where
  toFun p := ⟨assemble p, respects_assemble p⟩
  invFun g := fun B => restrictP g.1 g.2 B
  left_inv p := restrictP_assemble p
  right_inv g := Subtype.ext (assemble_restrictP g.1 g.2)

/-- **The sum of `ci` over `τ`-respecting permutations equals `∏_{B∈τ.parts} C(|B|q)`** —
the permutation-native realization of `K_r(q)`'s own defining product. -/
theorem sum_ci_respects_eq_prod_C (τ : PartLat r) :
    (∑ g : {g : Equiv.Perm (Fin r × Fin q) // Respects τ g}, ci g.1) =
      ∏ B ∈ τ.parts, C (B.card * q) := by
  rw [prod_C_eq_sum_ciProd τ, ← Equiv.sum_comp (assembleEquiv τ) (fun g => ci g.1)]
  exact Finset.sum_congr rfl (fun p _ => ci_assemble p)

end CongruenceTheory
