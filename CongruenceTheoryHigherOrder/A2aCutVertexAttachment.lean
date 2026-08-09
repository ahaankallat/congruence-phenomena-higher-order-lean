import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**Attachment: which component a point of `V u` reaches.** (A2a)'s cut-vertex case needs
`R_u = a_0 + Σ_τ m_τ a_τ`, i.e. that the points of `V_u` are partitioned by which component of
`ι∖{u}` their `g`-cycle reaches. `Reaches g u p c` formalizes "`p`'s cycle meets some point of some
block in component `c`"; `reaches_unique` is the well-definedness half of that partition claim —
a single point can reach at most one component, since two blocks both connected to `p`'s cycle are
directly adjacent via that shared cycle, hence already in the same component.
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- A point `p` "reaches" component `c` if `p`'s `g`-cycle meets some point of some block in `c`. -/
def Reaches {V : ι → Finset Ω} (g : Equiv.Perm Ω) (u : ι) (p : Ω) (c : BlockComponent V g u) :
    Prop :=
  ∃ x : {i : ι // i ≠ u}, Quot.mk (BlockReach V g u) x = c ∧ ∃ y ∈ V x.1, g.SameCycle p y

/-- A point can reach at most one component: if two blocks `x1,x2` both connect to `p`'s cycle,
they're directly adjacent via `p`'s own cycle, hence in the same component. -/
theorem reaches_unique {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι} {p : Ω}
    {c1 c2 : BlockComponent V g u} (h1 : Reaches g u p c1) (h2 : Reaches g u p c2) : c1 = c2 := by
  obtain ⟨x1, hx1, y1, hy1, hpy1⟩ := h1
  obtain ⟨x2, hx2, y2, hy2, hpy2⟩ := h2
  have hadj : BlockAdjSub V g u x1 x2 := ⟨y1, hy1, y2, hy2, hpy1.symm.trans hpy2⟩
  rw [← hx1, ← hx2]
  exact Quot.sound (Relation.EqvGen.rel _ _ hadj)
