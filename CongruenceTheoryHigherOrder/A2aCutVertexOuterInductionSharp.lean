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
import CongruenceTheoryHigherOrder.A2aCutVertexOuterInduction
import CongruenceTheoryHigherOrder.A2aCutVertexComponentType
import CongruenceTheoryHigherOrder.A2aRootBound
import CongruenceTheoryHigherOrder.CentralizerCycleFaithful

/-!
**The type-sharpened outer induction**: refines `key_induction_cutVertex_components'`'s
`M.card !` accumulator to `classFactorialProd g u M = ∏_τ (fiber_τ.card)!`, matching the
manuscript's `∏_τ m_τ!` grouping by (rooted-)isomorphism type. The only new ingredient beyond
`key_induction_cutVertex_components'` is that the peeled orbit is confined not just to `M` but to
`M`'s same-*type* fiber, via `card_ambientAttach_eq_of_moved`/`prod_blockSet_eq_of_moved` (same-orbit
components share attachment count and block-size product, hence share `compType`) together with
`classFactorialProd_erase`'s exact telescoping identity.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- **The type-sharpened outer well-founded induction.** -/
theorem key_induction_cutVertex_components'' {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {g : Equiv.Perm Ω} {u : ι}
    (hmixed : ∀ p ∈ V u, ∃ y ∉ V u, g.SameCycle p y)
    (hreach_all : ∀ c : BlockComponent V g u, ∃ q ∈ V u, Reaches g u q c) :
    ∀ n : ℕ, ∀ M : Finset (BlockComponent V g u), M.card ≤ n →
    ∀ A' : Subgroup (Equiv.Perm Ω), ∀ (hcent' : ∀ φ ∈ A', Commute φ g),
    ∀ (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j),
    ∀ (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u),
    (∀ c, c ∉ M → ∀ x, InComponentPlus g u c x → ∀ φ ∈ A', φ x = x) →
    Nat.card A' ≤ classFactorialProd g u M *
      ∏ c ∈ M, ((AmbientC0Attach g u c).card *
        ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1)) := by
  intro n
  induction n with
  | zero =>
    intro M hMcard A' hcent' hperm' hblock_u' hfixed
    have hMempty : M = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hMcard)
    subst hMempty
    have hcfp0 : classFactorialProd g u (∅ : Finset (BlockComponent V g u)) = 1 := by
      unfold classFactorialProd
      simp
    rw [hcfp0]
    simp only [Finset.prod_empty, one_mul]
    apply card_le_one_of_fixes_all_blocks hcent' hmixed hpart
    intro i hiu x hx φ hφ
    have hxIC : InComponentPlus g u (Quot.mk (BlockReach V g u) (⟨i, hiu⟩ : {k : ι // k ≠ u})) x :=
      Or.inl ⟨⟨i, hiu⟩, rfl, hx⟩
    exact hfixed _ (by simp) x hxIC φ hφ
  | succ n ih =>
    intro M hMcard A' hcent' hperm' hblock_u' hfixed
    rcases M.eq_empty_or_nonempty with hMempty | hMne
    · subst hMempty
      have hcfp0 : classFactorialProd g u (∅ : Finset (BlockComponent V g u)) = 1 := by
        unfold classFactorialProd
        simp
      rw [hcfp0]
      simp only [Finset.prod_empty, one_mul]
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
      have horbit_sub_type : ∀ c ∈ MulAction.orbit ↥A' c1,
          c ∈ M.filter (fun c => compType g u c = compType g u c1) := by
        intro c hc
        obtain ⟨φ, hφc⟩ := hc
        have hφc' : φ • c1 = c := hφc
        have hmove : componentPermOfMem hpart hne hcent' hperm' φ.2 (hblock_u' φ.1 φ.2) c1 = c :=
          hφc'
        have hcM : c ∈ M := by
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
        have htype : compType g u c1 = compType g u c := by
          have h1 : (AmbientC0Attach g u c1).card = (AmbientC0Attach g u c).card :=
            card_ambientAttach_eq_of_moved hpart hne hcent' hperm' hblock_u' φ.2 hmove
          have h2 : ∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1) =
              ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1) :=
            prod_blockSet_eq_of_moved hpart hne hcent' hperm' hblock_u' φ.2 hmove
          unfold compType
          rw [h1, h2]
        rw [Finset.mem_filter]
        exact ⟨hcM, htype.symm⟩
      have horbit_le : Nat.card (MulAction.orbit ↥A' c1) ≤
          (M.filter (fun c => compType g u c = compType g u c1)).card := by
        rw [Nat.card_eq_fintype_card]
        have hsubset : (MulAction.orbit ↥A' c1).toFinset ⊆
            M.filter (fun c => compType g u c = compType g u c1) := by
          intro c hc
          rw [Set.mem_toFinset] at hc
          exact horbit_sub_type c hc
        calc Fintype.card (MulAction.orbit ↥A' c1) = (MulAction.orbit ↥A' c1).toFinset.card :=
              (Set.toFinset_card _).symm
          _ ≤ (M.filter (fun c => compType g u c = compType g u c1)).card :=
              Finset.card_le_card hsubset
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
      have hcfp_eq := classFactorialProd_erase g u M hc1M
      calc Nat.card A' ≤ Nat.card (MulAction.orbit ↥A' c1) *
            ((AmbientC0Attach g u c1).card *
              (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c1),
                  Nat.factorial ((IslandV g u c1 i).card - 1)) *
              Nat.card A'') := by rw [hcardker]; exact hstep
        _ = Nat.card (MulAction.orbit ↥A' c1) *
              ((AmbientC0Attach g u c1).card *
                (∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1)) *
                Nat.card A'') := by rw [hPeq]
        _ ≤ (M.filter (fun c => compType g u c = compType g u c1)).card *
              ((AmbientC0Attach g u c1).card *
                (∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1)) *
                Nat.card A'') := Nat.mul_le_mul_right _ horbit_le
        _ ≤ (M.filter (fun c => compType g u c = compType g u c1)).card *
              ((AmbientC0Attach g u c1).card *
                (∏ i ∈ BlockSet g u c1, Nat.factorial ((V i.1).card - 1)) *
                (classFactorialProd g u (M.erase c1) *
                  ∏ c ∈ M.erase c1, ((AmbientC0Attach g u c).card *
                    ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1)))) := by
            apply Nat.mul_le_mul_left
            apply Nat.mul_le_mul_left
            exact hIH
        _ = classFactorialProd g u M * ∏ c ∈ M,
              ((AmbientC0Attach g u c).card * ∏ i ∈ BlockSet g u c,
                Nat.factorial ((V i.1).card - 1)) := by
            rw [hcfp_eq, ← Finset.mul_prod_erase M _ hc1M]
            ring

#print axioms key_induction_cutVertex_components''
