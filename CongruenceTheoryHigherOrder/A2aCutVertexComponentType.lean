import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexDistinguished
import CongruenceTheoryHigherOrder.A2aCutVertexOrbitEqual

/-!
**Component "type" classifier and the type-fiberwise factorial product.** Sharpens the (A2a)
cut-vertex outer induction's crude `M.card !` accumulator down to `∏_τ (fiber_τ.card)!`, matching
the manuscript's `∏_τ m_τ!` grouping by (rooted-)isomorphism type. Two components are declared the
"same type" when they have equal attachment count and equal block-size product — exactly the two
invariants `card_ambientAttach_eq_of_moved`/`prod_blockSet_eq_of_moved` show are preserved along a
component-permuting orbit, so same-orbit components automatically have the same type.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- A component's "type": its attachment count paired with its block-size factorial product. -/
noncomputable def compType {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (c : BlockComponent V g u) : ℕ × ℕ :=
  ((AmbientC0Attach g u c).card, ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1))

/-- The (fixed, `M`-independent) set of all types occurring among components. -/
noncomputable def compTypeSet (V : ι → Finset Ω) (g : Equiv.Perm Ω) (u : ι) :
    Finset (ℕ × ℕ) :=
  (Finset.univ : Finset (BlockComponent V g u)).image (compType g u)

/-- **The type-fiberwise factorial product**, indexed over the fixed `compTypeSet` (so it
telescopes uniformly under `M.erase c1`, with empty fibers harmlessly contributing `0! = 1`). -/
noncomputable def classFactorialProd {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (M : Finset (BlockComponent V g u)) : ℕ :=
  ∏ t ∈ compTypeSet V g u, Nat.factorial ((M.filter (fun c => compType g u c = t)).card)

theorem compType_mem_compTypeSet (V : ι → Finset Ω) (g : Equiv.Perm Ω) (u : ι)
    (c : BlockComponent V g u) : compType g u c ∈ compTypeSet V g u :=
  Finset.mem_image_of_mem _ (Finset.mem_univ c)

/-- **The key telescoping identity**: erasing one component `c1` from `M` divides
`classFactorialProd` by exactly the size of `c1`'s type-fiber within `M`. -/
theorem classFactorialProd_erase {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι)
    (M : Finset (BlockComponent V g u)) {c1 : BlockComponent V g u} (hc1M : c1 ∈ M) :
    classFactorialProd g u M =
      (M.filter (fun c => compType g u c = compType g u c1)).card *
        classFactorialProd g u (M.erase c1) := by
  unfold classFactorialProd
  set τ1 := compType g u c1 with hτ1def
  set F := M.filter (fun c => compType g u c = τ1) with hFdef
  have hτ1S : τ1 ∈ compTypeSet V g u := compType_mem_compTypeSet V g u c1
  have hc1F : c1 ∈ F := by
    rw [hFdef, Finset.mem_filter]
    exact ⟨hc1M, rfl⟩
  have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨c1, hc1F⟩
  have herase_ne : ∀ t ∈ (compTypeSet V g u).erase τ1,
      (M.erase c1).filter (fun c => compType g u c = t) = M.filter (fun c => compType g u c = t) := by
    intro t ht
    have htτ1 : t ≠ τ1 := Finset.ne_of_mem_erase ht
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hxM⟩, hxt⟩
      exact ⟨hxM, hxt⟩
    · rintro ⟨hxM, hxt⟩
      refine ⟨⟨?_, hxM⟩, hxt⟩
      rintro rfl
      exact htτ1 (hτ1def.trans hxt).symm
  have herase_eq : (M.erase c1).filter (fun c => compType g u c = τ1) = F.erase c1 := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_erase, hFdef]
    tauto
  have hFerasecard : (F.erase c1).card = F.card - 1 := Finset.card_erase_of_mem hc1F
  have hsplitM :
      ∏ t ∈ compTypeSet V g u, Nat.factorial ((M.filter (fun c => compType g u c = t)).card)
      = Nat.factorial F.card *
        ∏ t ∈ (compTypeSet V g u).erase τ1,
          Nat.factorial ((M.filter (fun c => compType g u c = t)).card) := by
    rw [← Finset.mul_prod_erase (compTypeSet V g u)
      (fun t => Nat.factorial ((M.filter (fun c => compType g u c = t)).card)) hτ1S]
  have hsplitM' : ∏ t ∈ compTypeSet V g u,
      Nat.factorial (((M.erase c1).filter (fun c => compType g u c = t)).card)
      = Nat.factorial (F.card - 1) *
        ∏ t ∈ (compTypeSet V g u).erase τ1,
          Nat.factorial ((M.filter (fun c => compType g u c = t)).card) := by
    rw [← Finset.mul_prod_erase (compTypeSet V g u)
      (fun t => Nat.factorial (((M.erase c1).filter (fun c => compType g u c = t)).card)) hτ1S]
    rw [herase_eq, hFerasecard]
    congr 1
    exact Finset.prod_congr rfl (fun t ht => by rw [herase_ne t ht])
  rw [hsplitM, hsplitM']
  have hfact : Nat.factorial F.card = F.card * Nat.factorial (F.card - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, F.card = k + 1 := ⟨F.card - 1, by omega⟩
    rw [hk]
    simp [Nat.factorial_succ]
  rw [hfact]
  ring

#print axioms classFactorialProd_erase
