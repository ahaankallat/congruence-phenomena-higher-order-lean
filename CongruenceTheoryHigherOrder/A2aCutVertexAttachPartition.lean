import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexDistinguished

/-!
**`AmbientC0Attach` partitions `V u`.** Given `hmixed` (every point of `V u` reaches outside `V u`)
and `hpart` (a genuine partition of `Ω`), every point of `V u` reaches *some* component, and
`reaches_unique` already shows it reaches at most one — so the attachment sets
`AmbientC0Attach g u c`, as `c` ranges over all components, partition `V u` exactly. This is the
identity connecting the cut-vertex valuation bound's `a_0`/`a_τ` bookkeeping back to `R_u = |V u|`.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- Every point of `V u` reaches some component, given `hmixed` and `hpart`. -/
theorem exists_reaches_of_mixed {V : ι → Finset Ω} (hpart : IsPartition V) {g : Equiv.Perm Ω}
    {u : ι} (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y) {x : Ω} (hx : x ∈ V u) :
    ∃ c : BlockComponent V g u, Reaches g u x c := by
  obtain ⟨y, hyu, hxy⟩ := hmixed x hx
  obtain ⟨i, hi, -⟩ := hpart y
  have hiu : i ≠ u := by rintro rfl; exact hyu hi
  exact ⟨Quot.mk (BlockReach V g u) ⟨i, hiu⟩, ⟨i, hiu⟩, rfl, y, hi, hxy⟩

/-- `V u` is the disjoint union, over all components `c`, of `AmbientC0Attach g u c`. -/
theorem vu_eq_biUnion_ambientC0Attach {V : ι → Finset Ω} (hpart : IsPartition V) {g : Equiv.Perm Ω}
    {u : ι} (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y) :
    V u = Finset.univ.biUnion (fun c : BlockComponent V g u => AmbientC0Attach g u c) := by
  apply Finset.ext
  intro x
  rw [Finset.mem_biUnion]
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := exists_reaches_of_mixed hpart hmixed hx
    exact ⟨c, Finset.mem_univ c, (mem_ambientC0Attach g u c x).mpr ⟨hx, hc⟩⟩
  · rintro ⟨c, -, hc⟩
    exact ((mem_ambientC0Attach g u c x).mp hc).1

/-- Distinct components have disjoint attachment sets. -/
theorem ambientC0Attach_pairwiseDisjoint {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι) :
    ((Finset.univ : Finset (BlockComponent V g u)) : Set (BlockComponent V g u)).PairwiseDisjoint
      (fun c => AmbientC0Attach g u c) := by
  intro c1 _ c2 _ hne
  show Disjoint (AmbientC0Attach g u c1) (AmbientC0Attach g u c2)
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have h1 : Reaches g u x c1 := ((mem_ambientC0Attach g u c1 x).mp hx1).2
  have h2 : Reaches g u x c2 := ((mem_ambientC0Attach g u c2 x).mp hx2).2
  exact hne (reaches_unique h1 h2)

/-- **`R_u = Σ_c a_c`**: the cardinality identity underlying `Σ_τ m_τ a_τ + a_0 = R_u`. -/
theorem card_vu_eq_sum_ambientC0Attach {V : ι → Finset Ω} (hpart : IsPartition V)
    {g : Equiv.Perm Ω} {u : ι} (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y) :
    (V u).card = ∑ c : BlockComponent V g u, (AmbientC0Attach g u c).card := by
  rw [vu_eq_biUnion_ambientC0Attach hpart hmixed]
  rw [Finset.card_biUnion (ambientC0Attach_pairwiseDisjoint g u)]
