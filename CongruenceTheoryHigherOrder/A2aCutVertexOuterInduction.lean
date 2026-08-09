import Mathlib
import CongruenceTheoryHigherOrder.A2aOrbitBound
import CongruenceTheoryHigherOrder.A2aCutVertexComponents
import CongruenceTheoryHigherOrder.A2aCutVertexComponentAction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentHom
import CongruenceTheoryHigherOrder.A2aCutVertexAttachment
import CongruenceTheoryHigherOrder.A2aCutVertexInvariance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandInstance
import CongruenceTheoryHigherOrder.A2aCutVertexIslandHom
import CongruenceTheoryHigherOrder.A2aCutVertexDistinguished
import CongruenceTheoryHigherOrder.A2aCutVertexBranchConfinement
import CongruenceTheoryHigherOrder.A2aCutVertexBranchOrbitStab
import CongruenceTheoryHigherOrder.A2aCutVertexBranchBound
import CongruenceTheoryHigherOrder.A2aCutVertexKerAmbient
import CongruenceTheoryHigherOrder.A2aCutVertexComponentComplement
import CongruenceTheoryHigherOrder.A2aCutVertexBaseCase
import CongruenceTheoryHigherOrder.A2aCutVertexOrbitEqual
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The outer well-founded induction across (A2a)'s cut-vertex case's components**, chaining
`card_le_branch_bound` from any subgroup down to the base case, one component at a time.

**A mid-course correction, recorded honestly.** The first design attempt tried to remove a whole
`A'`-orbit of components at once per step (matching the manuscript's `m_τ` grouping exactly), using
`card_eq_orbit_mul_stabAmbient`'s orbit-size factor together with `card_ambientAttach_eq_of_moved`/
`prod_blockSet_eq_of_moved` (proved in `A2aCutVertexOrbitEqual.lean`, and still true and available)
to show every component in that orbit contributes the same factor. That ran into a genuine
obstruction: the kernel `A''` obtained from peeling `c1` (`KerAmbient` of `c1`'s restriction
homomorphism) is only *guaranteed* to fix `c1`'s own island pointwise — nothing forces it to fix
the *other* members of `c1`'s orbit pointwise too, so the accumulating "island-fixed" invariant
needed for the recursion's own base case and shrinking-measure argument cannot be carried past a
single component per step this way. Re-examining the manuscript's target
(`v_p(a_0)+Σv_p((R_i-1)!)+Σ_τ(m_τv_p(a_τ)+v_p(m_τ!))`) shows this is not a defect to route around:
the `v_p(m_τ!)` term is *supposed* to be there, and a per-component (not per-orbit) recursion that
simply accumulates one orbit-size factor per component peeled is exactly the right mechanism to
produce it — `key_induction_rooted` itself uses the analogous "one designated point/block at a
time" strategy with no attempt at within-step symmetry reduction. What is proved below is the
*unrefined* form of that accumulation (bounding every per-step orbit factor by the crude global
constant `Fintype.card (BlockComponent V g u)` rather than tracking `m_τ` explicitly) — a fully
correct, honestly weaker statement than the manuscript's exact grouped bound, recorded as such.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- If `A'` fixes the whole island of `c` pointwise, `A'` fixes `c` setwise under
`componentPermOfMem`. -/
theorem componentPermOfMem_fixed_of_island_fixed {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A' : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent' : ∀ φ ∈ A', Commute φ g) (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u) {c : BlockComponent V g u}
    (hfixc : ∀ x, InComponentPlus g u c x → ∀ φ ∈ A', φ x = x) {φ : Equiv.Perm Ω}
    (hφ : φ ∈ A') : componentPermOfMem hpart hne hcent' hperm' hφ (hblock_u' φ hφ) c = c := by
  obtain ⟨x, hxc⟩ := Quot.exists_rep c
  obtain ⟨p, hp⟩ := hne x.1
  have hpIC : InComponentPlus g u c p := Or.inl ⟨x, hxc, hp⟩
  have hfixp : φ p = p := hfixc p hpIC φ hφ
  have hblockeq : blockOfElt hpart hperm' φ hφ x.1 = x.1 := by
    have hspec := blockOfElt_spec hpart hperm' φ hφ x.1
    have hp' : φ p ∈ V (blockOfElt hpart hperm' φ hφ x.1) := hspec ▸ Finset.mem_image_of_mem φ hp
    rw [hfixp] at hp'
    obtain ⟨i0, hi0, huniq⟩ := hpart p
    exact (huniq (blockOfElt hpart hperm' φ hφ x.1) hp').trans (huniq x.1 hp).symm
  rw [← hxc, componentPermOfMem_mk]
  congr 1
  apply Subtype.ext
  rw [blockPermSub_coe]
  exact hblockeq

/-- **The outer well-founded induction across (A2a)'s cut-vertex case's components**, unrefined
form: every orbit-size factor is bounded crudely by `Fintype.card (BlockComponent V g u)`. -/
theorem key_induction_cutVertex_components {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {g : Equiv.Perm Ω} {u : ι}
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    (hreach_all : ∀ c : BlockComponent V g u, ∃ q ∈ V u, Reaches g u q c) :
    ∀ n : ℕ, ∀ M : Finset (BlockComponent V g u), M.card ≤ n →
    ∀ A' : Subgroup (Equiv.Perm Ω), ∀ (hcent' : ∀ φ ∈ A', Commute φ g),
    ∀ (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j),
    ∀ (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u),
    (∀ c, c ∉ M → ∀ x, InComponentPlus g u c x → ∀ φ ∈ A', φ x = x) →
    Nat.card A' ≤ (Fintype.card (BlockComponent V g u)) ^ M.card *
      ∏ c ∈ M, ((AmbientC0Attach g u c).card *
        ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1)) := by
  intro n
  induction n with
  | zero =>
    intro M hMcard A' hcent' hperm' hblock_u' hfixed
    have hMempty : M = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hMcard)
    subst hMempty
    simp only [Finset.card_empty, pow_zero, Finset.prod_empty, one_mul]
    apply card_le_one_of_fixes_all_blocks hcent' hmixed hpart
    intro i hiu x hx φ hφ
    have hxIC : InComponentPlus g u (Quot.mk (BlockReach V g u) (⟨i, hiu⟩ : {k : ι // k ≠ u})) x :=
      Or.inl ⟨⟨i, hiu⟩, rfl, hx⟩
    exact hfixed _ (by simp) x hxIC φ hφ
  | succ n ih =>
    intro M hMcard A' hcent' hperm' hblock_u' hfixed
    rcases M.eq_empty_or_nonempty with hMempty | hMne
    · subst hMempty
      simp only [Finset.card_empty, pow_zero, Finset.prod_empty, one_mul]
      apply card_le_one_of_fixes_all_blocks hcent' hmixed hpart
      intro i hiu x hx φ hφ
      have hxIC : InComponentPlus g u
          (Quot.mk (BlockReach V g u) (⟨i, hiu⟩ : {k : ι // k ≠ u})) x :=
        Or.inl ⟨⟨i, hiu⟩, rfl, hx⟩
      exact hfixed _ (by simp) x hxIC φ hφ
    · obtain ⟨c1, hc1M⟩ := hMne
      obtain ⟨q1, hq1u, hq1reach⟩ := hreach_all c1
      letI := componentMulAction hpart hne hcent' hperm' hblock_u'
      have hstep := card_le_branch_bound hpart hne hcent' hperm' hblock_u' c1 hq1u hq1reach
      set hcentS := fun φ (hφ : φ ∈ StabAmbient hpart hne hcent' hperm' hblock_u' c1) =>
        hcent' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ) with hcentS_def
      set hpermS := fun φ (hφ : φ ∈ StabAmbient hpart hne hcent' hperm' hblock_u' c1) =>
        hperm' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ) with hpermS_def
      set hblockS := fun φ (hφ : φ ∈ StabAmbient hpart hne hcent' hperm' hblock_u' c1) =>
        hblock_u' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ) with hblockS_def
      set A'' := KerAmbient hpart hne hcentS hpermS hblockS hq1reach with hA''def
      have hcardker : Nat.card A'' = Nat.card (MonoidHom.ker
          (islandHom hpart hne hcentS hpermS hblockS hq1reach)) :=
        card_kerAmbient hpart hne hcentS hpermS hblockS hq1reach
      have hA''leA' : A'' ≤ A' :=
        (kerAmbient_le_A hpart hne hcentS hpermS hblockS hq1reach).trans
          (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1)
      have hcent'' : ∀ φ ∈ A'', Commute φ g := fun φ hφ => hcent' φ (hA''leA' hφ)
      have hperm'' : ∀ φ ∈ A'', ∀ i, ∃ j, (V i).image φ = V j := fun φ hφ => hperm' φ (hA''leA' hφ)
      have hblock_u'' : ∀ φ ∈ A'', (V u).image φ = V u := fun φ hφ => hblock_u' φ (hA''leA' hφ)
      have hfixed'' : ∀ c, c ∉ M.erase c1 → ∀ x, InComponentPlus g u c x → ∀ φ ∈ A'', φ x = x := by
        intro c hcM x hx φ hφ
        by_cases hcc1 : c = c1
        · subst hcc1
          exact kerAmbient_fixes_island hpart hne hcentS hpermS hblockS hq1reach φ hφ hx
        · exact hfixed c (fun hcMmem => hcM (Finset.mem_erase.mpr ⟨hcc1, hcMmem⟩)) x hx φ
            (hA''leA' hφ)
      have hcardMerase : (M.erase c1).card ≤ n := by
        have := Finset.card_erase_of_mem hc1M
        omega
      have hIH := ih (M.erase c1) hcardMerase A'' hcent'' hperm'' hblock_u'' hfixed''
      have horbit_le : Nat.card (MulAction.orbit ↥A' c1) ≤ Fintype.card (BlockComponent V g u) := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_le_of_injective (fun x : (MulAction.orbit ↥A' c1) => x.1)
          Subtype.val_injective
      have hPeq : ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
          Nat.factorial ((IslandV g u c1 i).card - 1) =
          ∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1) := by
        have hcardeq : ∀ i : {k : {j : ι // j ≠ u} // Quot.mk (BlockReach V g u) k = c1},
            (IslandV g u c1 (some i)).card = (V i.1.1).card := by
          intro i
          unfold IslandV
          rw [Finset.card_subtype]
          congr 1
          apply Finset.filter_true_of_mem
          intro x hx
          exact Or.inl ⟨i.1, i.2, hx⟩
        have herasenone : (Finset.univ.erase (none : IslandBlockIdx g u c1)) =
            (Finset.univ :
              Finset {k : {j : ι // j ≠ u} // Quot.mk (BlockReach V g u) k = c1}).image some := by
          apply Finset.ext
          intro x
          rcases x with _ | k
          · simp
          · simp
        rw [herasenone, Finset.prod_image (fun a _ b _ h => Option.some.inj h)]
        simp_rw [hcardeq]
        exact (Finset.prod_subtype (BlockSet g u c1) (fun x => mem_blockSet g u c1 x)
          (fun x => Nat.factorial ((V x.1).card - 1))).symm
      have hMcard_eq : M.card = (M.erase c1).card + 1 := by
        have := Finset.card_erase_of_mem hc1M
        have hpos : 0 < M.card := Finset.card_pos.mpr ⟨c1, hc1M⟩
        omega
      calc Nat.card A' ≤ Nat.card (MulAction.orbit ↥A' c1) *
            ((AmbientC0Attach g u c1).card *
              (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
                  Nat.factorial ((IslandV g u c1 i).card - 1)) *
              Nat.card A'') := by rw [hcardker]; exact hstep
        _ = Nat.card (MulAction.orbit ↥A' c1) *
              ((AmbientC0Attach g u c1).card *
                (∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1)) *
                Nat.card A'') := by rw [hPeq]
        _ ≤ (Fintype.card (BlockComponent V g u)) *
              ((AmbientC0Attach g u c1).card *
                (∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1)) *
                Nat.card A'') := Nat.mul_le_mul_right _ horbit_le
        _ ≤ (Fintype.card (BlockComponent V g u)) *
              ((AmbientC0Attach g u c1).card *
                (∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1)) *
                ((Fintype.card (BlockComponent V g u)) ^ (M.erase c1).card *
                  ∏ c ∈ M.erase c1, ((AmbientC0Attach g u c).card *
                    ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1)))) := by
            apply Nat.mul_le_mul_left
            apply Nat.mul_le_mul_left
            exact hIH
        _ = (Fintype.card (BlockComponent V g u)) ^ M.card * ∏ c ∈ M,
              ((AmbientC0Attach g u c).card * ∏ i ∈ BlockSet g u c,
                Nat.factorial ((V i.1).card - 1)) := by
            rw [hMcard_eq, ← Finset.mul_prod_erase M _ hc1M]
            ring

/-- **A sharper form**: the orbit of `c1` under `A'` is confined to `M` itself (not just bounded
by the crude global constant `Fintype.card(BlockComponent V g u)`), since `A'` already fixes every
component outside `M` pointwise (`hfixed`) hence setwise, and an injective map can never send
`c1 ∈ M` to a fixed point outside `M`. This tightens the accumulated bound from
`Fintype.card(BlockComponent)^{M.card}` down to `M.card !` — genuinely smaller whenever
`M.card < Fintype.card(BlockComponent)`, though still short of the manuscript's exact
`∏_τ(a_τ)^{m_τ}·m_τ!` grouping by rooted-isomorphism type (which would need confining the orbit
further, to just the *same-type* remaining members of `M`). -/
theorem key_induction_cutVertex_components' {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {g : Equiv.Perm Ω} {u : ι}
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    (hreach_all : ∀ c : BlockComponent V g u, ∃ q ∈ V u, Reaches g u q c) :
    ∀ n : ℕ, ∀ M : Finset (BlockComponent V g u), M.card ≤ n →
    ∀ A' : Subgroup (Equiv.Perm Ω), ∀ (hcent' : ∀ φ ∈ A', Commute φ g),
    ∀ (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j),
    ∀ (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u),
    (∀ c, c ∉ M → ∀ x, InComponentPlus g u c x → ∀ φ ∈ A', φ x = x) →
    Nat.card A' ≤ Nat.factorial M.card *
      ∏ c ∈ M, ((AmbientC0Attach g u c).card *
        ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1)) := by
  intro n
  induction n with
  | zero =>
    intro M hMcard A' hcent' hperm' hblock_u' hfixed
    have hMempty : M = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hMcard)
    subst hMempty
    simp only [Finset.card_empty, Nat.factorial_zero, Finset.prod_empty, one_mul]
    apply card_le_one_of_fixes_all_blocks hcent' hmixed hpart
    intro i hiu x hx φ hφ
    have hxIC : InComponentPlus g u (Quot.mk (BlockReach V g u) (⟨i, hiu⟩ : {k : ι // k ≠ u})) x :=
      Or.inl ⟨⟨i, hiu⟩, rfl, hx⟩
    exact hfixed _ (by simp) x hxIC φ hφ
  | succ n ih =>
    intro M hMcard A' hcent' hperm' hblock_u' hfixed
    rcases M.eq_empty_or_nonempty with hMempty | hMne
    · subst hMempty
      simp only [Finset.card_empty, Nat.factorial_zero, Finset.prod_empty, one_mul]
      apply card_le_one_of_fixes_all_blocks hcent' hmixed hpart
      intro i hiu x hx φ hφ
      have hxIC : InComponentPlus g u
          (Quot.mk (BlockReach V g u) (⟨i, hiu⟩ : {k : ι // k ≠ u})) x :=
        Or.inl ⟨⟨i, hiu⟩, rfl, hx⟩
      exact hfixed _ (by simp) x hxIC φ hφ
    · obtain ⟨c1, hc1M⟩ := hMne
      obtain ⟨q1, hq1u, hq1reach⟩ := hreach_all c1
      letI := componentMulAction hpart hne hcent' hperm' hblock_u'
      have hstep := card_le_branch_bound hpart hne hcent' hperm' hblock_u' c1 hq1u hq1reach
      set hcentS := fun φ (hφ : φ ∈ StabAmbient hpart hne hcent' hperm' hblock_u' c1) =>
        hcent' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ) with hcentS_def
      set hpermS := fun φ (hφ : φ ∈ StabAmbient hpart hne hcent' hperm' hblock_u' c1) =>
        hperm' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ) with hpermS_def
      set hblockS := fun φ (hφ : φ ∈ StabAmbient hpart hne hcent' hperm' hblock_u' c1) =>
        hblock_u' φ (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1 hφ) with hblockS_def
      set A'' := KerAmbient hpart hne hcentS hpermS hblockS hq1reach with hA''def
      have hcardker : Nat.card A'' = Nat.card (MonoidHom.ker
          (islandHom hpart hne hcentS hpermS hblockS hq1reach)) :=
        card_kerAmbient hpart hne hcentS hpermS hblockS hq1reach
      have hA''leA' : A'' ≤ A' :=
        (kerAmbient_le_A hpart hne hcentS hpermS hblockS hq1reach).trans
          (stabAmbient_le hpart hne hcent' hperm' hblock_u' c1)
      have hcent'' : ∀ φ ∈ A'', Commute φ g := fun φ hφ => hcent' φ (hA''leA' hφ)
      have hperm'' : ∀ φ ∈ A'', ∀ i, ∃ j, (V i).image φ = V j := fun φ hφ => hperm' φ (hA''leA' hφ)
      have hblock_u'' : ∀ φ ∈ A'', (V u).image φ = V u := fun φ hφ => hblock_u' φ (hA''leA' hφ)
      have hfixed'' : ∀ c, c ∉ M.erase c1 → ∀ x, InComponentPlus g u c x → ∀ φ ∈ A'', φ x = x := by
        intro c hcM x hx φ hφ
        by_cases hcc1 : c = c1
        · subst hcc1
          exact kerAmbient_fixes_island hpart hne hcentS hpermS hblockS hq1reach φ hφ hx
        · exact hfixed c (fun hcMmem => hcM (Finset.mem_erase.mpr ⟨hcc1, hcMmem⟩)) x hx φ
            (hA''leA' hφ)
      have hcardMerase : (M.erase c1).card ≤ n := by
        have := Finset.card_erase_of_mem hc1M
        omega
      have hIH := ih (M.erase c1) hcardMerase A'' hcent'' hperm'' hblock_u'' hfixed''
      have horbit_sub : ∀ c ∈ MulAction.orbit ↥A' c1, c ∈ M := by
        intro c hc
        obtain ⟨φ, hφc⟩ := hc
        have hφc' : φ • c1 = c := hφc
        by_contra hcM
        have hfix_c : componentPermOfMem hpart hne hcent' hperm' φ.2 (hblock_u' φ.1 φ.2) c = c :=
          componentPermOfMem_fixed_of_island_fixed hpart hne hcent' hperm' hblock_u'
            (fun x hx ψ hψ => hfixed c hcM x hx ψ hψ) φ.2
        have heq2 : φ • c = c := by
          show componentHom hpart hne hcent' hperm' hblock_u' φ c = c
          rw [componentHom_apply]
          exact hfix_c
        have heq3 : φ • c1 = φ • c := by rw [hφc', heq2]
        have hc1c : c1 = c := MulAction.injective φ heq3
        exact hcM (hc1c ▸ hc1M)
      have horbit_le : Nat.card (MulAction.orbit ↥A' c1) ≤ M.card := by
        rw [Nat.card_eq_fintype_card]
        have hsubset : (MulAction.orbit ↥A' c1).toFinset ⊆ M := by
          intro c hc
          rw [Set.mem_toFinset] at hc
          exact horbit_sub c hc
        calc Fintype.card (MulAction.orbit ↥A' c1) = (MulAction.orbit ↥A' c1).toFinset.card :=
              (Set.toFinset_card _).symm
          _ ≤ M.card := Finset.card_le_card hsubset
      have hPeq : ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
          Nat.factorial ((IslandV g u c1 i).card - 1) =
          ∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1) := by
        have hcardeq : ∀ i : {k : {j : ι // j ≠ u} // Quot.mk (BlockReach V g u) k = c1},
            (IslandV g u c1 (some i)).card = (V i.1.1).card := by
          intro i
          unfold IslandV
          rw [Finset.card_subtype]
          congr 1
          apply Finset.filter_true_of_mem
          intro x hx
          exact Or.inl ⟨i.1, i.2, hx⟩
        have herasenone : (Finset.univ.erase (none : IslandBlockIdx g u c1)) =
            (Finset.univ :
              Finset {k : {j : ι // j ≠ u} // Quot.mk (BlockReach V g u) k = c1}).image some := by
          apply Finset.ext
          intro x
          rcases x with _ | k
          · simp
          · simp
        rw [herasenone, Finset.prod_image (fun a _ b _ h => Option.some.inj h)]
        simp_rw [hcardeq]
        exact (Finset.prod_subtype (BlockSet g u c1) (fun x => mem_blockSet g u c1 x)
          (fun x => Nat.factorial ((V x.1).card - 1))).symm
      have hMcard_eq : M.card = (M.erase c1).card + 1 := by
        have := Finset.card_erase_of_mem hc1M
        have hpos : 0 < M.card := Finset.card_pos.mpr ⟨c1, hc1M⟩
        omega
      calc Nat.card A' ≤ Nat.card (MulAction.orbit ↥A' c1) *
            ((AmbientC0Attach g u c1).card *
              (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
                  Nat.factorial ((IslandV g u c1 i).card - 1)) *
              Nat.card A'') := by rw [hcardker]; exact hstep
        _ = Nat.card (MulAction.orbit ↥A' c1) *
              ((AmbientC0Attach g u c1).card *
                (∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1)) *
                Nat.card A'') := by rw [hPeq]
        _ ≤ M.card *
              ((AmbientC0Attach g u c1).card *
                (∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1)) *
                Nat.card A'') := Nat.mul_le_mul_right _ horbit_le
        _ ≤ M.card *
              ((AmbientC0Attach g u c1).card *
                (∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1)) *
                (Nat.factorial (M.erase c1).card *
                  ∏ c ∈ M.erase c1, ((AmbientC0Attach g u c).card *
                    ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1)))) := by
            apply Nat.mul_le_mul_left
            apply Nat.mul_le_mul_left
            exact hIH
        _ = Nat.factorial M.card * ∏ c ∈ M,
              ((AmbientC0Attach g u c).card * ∏ i ∈ BlockSet g u c,
                Nat.factorial ((V i.1).card - 1)) := by
            rw [hMcard_eq, Nat.factorial_succ, ← Finset.mul_prod_erase M _ hc1M]
            ring
