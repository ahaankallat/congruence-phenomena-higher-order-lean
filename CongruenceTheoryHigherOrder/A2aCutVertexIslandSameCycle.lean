import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandG
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**`islandG`'s powers coerce to `g`'s powers, hence `SameCycle` transfers between the island and
the ambient space.** Needed to translate `hmixed`/the initial edge/`hconn` (all stated via
`g.SameCycle`) into their island-native forms for `card_le_root_bound`.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

theorem islandG_zpow_coe {V : ι → Finset Ω} (hpart : IsPartition V) (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) (n : ℤ) :
    ∀ x : {x : Ω // InComponentPlus g u c0 x}, ((islandG hpart g u c0 ^ n) x : Ω) = (g ^ n) x.1 := by
  induction n using Int.induction_on with
  | zero => intro x; simp
  | succ i ih =>
    intro x
    have hstep : (islandG hpart g u c0) ^ ((i : ℤ) + 1) =
        (islandG hpart g u c0) ^ (i : ℤ) * islandG hpart g u c0 := by
      rw [zpow_add, zpow_one]
    have hgstep : g ^ ((i : ℤ) + 1) = g ^ (i : ℤ) * g := by rw [zpow_add, zpow_one]
    rw [hstep, hgstep, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [ih (islandG hpart g u c0 x)]
    first
    | rfl
    | (congr 1; exact islandG_coe hpart g u c0 x)
  | pred i ih =>
    intro x
    have hstep : (islandG hpart g u c0) ^ (-(i : ℤ) - 1) =
        (islandG hpart g u c0) ^ (-(i : ℤ)) * (islandG hpart g u c0)⁻¹ := by
      rw [zpow_sub, zpow_one]
    have hgstep : g ^ (-(i : ℤ) - 1) = g ^ (-(i : ℤ)) * g⁻¹ := by rw [zpow_sub, zpow_one]
    rw [hstep, hgstep, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [ih ((islandG hpart g u c0)⁻¹ x)]
    first
    | rfl
    | (congr 1
       have hinv : islandG hpart g u c0 ((islandG hpart g u c0)⁻¹ x) = x := by simp
       have h2 := congrArg (fun y : {x : Ω // InComponentPlus g u c0 x} => (y : Ω)) hinv
       rw [islandG_coe] at h2
       have hg1 : g (g⁻¹ x.1) = x.1 := by simp
       exact g.injective (h2.trans hg1.symm))

theorem islandG_sameCycle_iff {V : ι → Finset Ω} (hpart : IsPartition V) (g : Equiv.Perm Ω) (u : ι)
    (c0 : BlockComponent V g u) (x y : {x : Ω // InComponentPlus g u c0 x}) :
    (islandG hpart g u c0).SameCycle x y ↔ g.SameCycle x.1 y.1 := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← islandG_zpow_coe hpart g u c0 n x, hn]⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    rw [islandG_zpow_coe hpart g u c0 n x]
    exact hn
