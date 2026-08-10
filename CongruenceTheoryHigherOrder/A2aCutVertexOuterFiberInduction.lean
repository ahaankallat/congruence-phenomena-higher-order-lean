import Mathlib
import CongruenceTheoryHigherOrder.A2aCutVertexFiberBound
import CongruenceTheoryHigherOrder.A2aCutVertexFixesC0
import CongruenceTheoryHigherOrder.A2aCutVertexKerAmbient

/-!
**The outer induction: peeling one `compType`-fiber at a time.** Chains `card_dvd_fiber_bound`
across an `A'`-invariant pool `M` of components, one full fiber per step (never one component),
so no per-step arithmetic beyond invariance, exact `range·ker` factorization, and divisibility
multiplication is ever needed — exactly the shape `card_dvd_fiber_bound` already established for a
single fiber, now assembled across all of them. The leftover at each step is `FixIslands` of the
*original* `A'` restricted to what remains, matching `key_induction_island_dvd`'s own pattern, so
the recursion bottoms out cleanly at `M = ∅`.
-/

open Equiv Classical

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- If `φ` fixes every point of `c`'s island pointwise, it fixes `c` itself as a component. -/
theorem componentPermOfMem_fixed_of_islandFixed {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {φ : Equiv.Perm Ω} (hφ : φ ∈ A)
    {c : BlockComponent V g u} {p₀ : Ω} (hp₀reach : Reaches g u p₀ c) (hfixp₀ : φ p₀ = p₀) :
    componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c = c :=
  componentPermOfMem_fixes_reached hpart hne hcent hperm hφ (hblock_u φ hφ) hfixp₀ hp₀reach

/-- If `φ` fixes a component `c0` setwise, it never sends a *different* component to `c0`. -/
theorem componentPermOfMem_ne_of_fixed {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {c0 : BlockComponent V g u} {φ : Equiv.Perm Ω}
    (hφ : φ ∈ A) (hfixc0 : componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c0 = c0)
    {c : BlockComponent V g u} (hc : c ≠ c0) :
    componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ) c ≠ c0 := by
  intro heq
  exact hc ((componentPermOfMem hpart hne hcent hperm hφ (hblock_u φ hφ)).injective
    (heq.trans hfixc0.symm))

/-- Elements of `FixIslands A g u S` fix every component of `S` setwise (not just its island
pointwise: the two are equivalent once a nonempty attach point is available). -/
theorem fixIslands_fixes_component {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) (S : Finset (BlockComponent V g u))
    (hne_attach : ∀ c ∈ S, (AmbientC0Attach g u c).Nonempty)
    {φ : Equiv.Perm Ω} (hφ : φ ∈ FixIslands A g u S) {c : BlockComponent V g u} (hc : c ∈ S) :
    componentPermOfMem hpart hne hcent hperm (mem_FixIslands.mp hφ).1
      (hblock_u φ (mem_FixIslands.mp hφ).1) c = c := by
  obtain ⟨p₀, hp₀mem⟩ := hne_attach c hc
  have hp₀reach : Reaches g u p₀ c := ((mem_ambientC0Attach g u c p₀).mp hp₀mem).2
  have hfixp₀ : φ p₀ = p₀ :=
    (mem_FixIslands.mp hφ).2 c hc p₀ (Or.inr ⟨((mem_ambientC0Attach g u c p₀).mp hp₀mem).1,
      hp₀reach⟩)
  exact componentPermOfMem_fixed_of_islandFixed hpart hne hcent hperm hblock_u
    (mem_FixIslands.mp hφ).1 hp₀reach hfixp₀

/-- **The outer induction**, peeling one `compType`-fiber of `M` at a time. -/
theorem key_induction_fiber_dvd {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {g : Equiv.Perm Ω} {u : ι} :
    ∀ n : ℕ, ∀ M : Finset (BlockComponent V g u), M.card ≤ n →
    ∀ A' : Subgroup (Equiv.Perm Ω), ∀ (hcent' : ∀ φ ∈ A', Commute φ g),
    ∀ (hperm' : ∀ φ ∈ A', ∀ i, ∃ j, (V i).image φ = V j),
    ∀ (hblock_u' : ∀ φ ∈ A', (V u).image φ = V u),
    (∀ φ : A', ∀ c ∈ M, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ M) →
    (∀ c ∈ M, (AmbientC0Attach g u c).Nonempty) →
    Nat.card A' ∣ (∏ τ ∈ M.image (compType g u),
      (Nat.factorial (M.filter (fun c => compType g u c = τ)).card *
        (∏ c ∈ M.filter (fun c => compType g u c = τ), Nat.factorial (AmbientC0Attach g u c).card) *
        (∏ c ∈ M.filter (fun c => compType g u c = τ),
          ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
            Nat.factorial ((IslandV g u c i).card - 1)))) *
      Nat.card (FixIslands A' g u M) := by
  intro n
  induction n with
  | zero =>
    intro M hMcard A' hcent' hperm' hblock_u' _ _
    have hMempty : M = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hMcard)
    subst hMempty
    rw [fixIslands_empty]
    simp
  | succ n ih =>
    intro M hMcard A' hcent' hperm' hblock_u' hMinv hne_attach
    rcases M.eq_empty_or_nonempty with hMempty | hMne
    · subst hMempty
      rw [fixIslands_empty]
      simp
    · obtain ⟨c1, hc1M⟩ := hMne
      set τ1 := compType g u c1 with hτ1def
      set S := M.filter (fun c => compType g u c = τ1) with hSdef
      have hc1S : c1 ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hc1M, rfl⟩
      have hSinv : ∀ φ : A', ∀ c ∈ S, componentHom hpart hne hcent' hperm' hblock_u' φ c ∈ S := by
        intro φ c hc
        rw [hSdef, Finset.mem_filter] at hc
        rw [hSdef, Finset.mem_filter]
        refine ⟨hMinv φ c hc.1, ?_⟩
        have hmove : componentPermOfMem hpart hne hcent' hperm' φ.2 (hblock_u' φ.1 φ.2) c =
            componentHom hpart hne hcent' hperm' hblock_u' φ c := rfl
        have h1 : (AmbientC0Attach g u c).card =
            (AmbientC0Attach g u (componentHom hpart hne hcent' hperm' hblock_u' φ c)).card :=
          card_ambientAttach_eq_of_moved hpart hne hcent' hperm' hblock_u' φ.2 hmove
        have h2 : ∏ i ∈ BlockSet g u c, Nat.factorial ((V i.1).card - 1) =
            ∏ i ∈ BlockSet g u (componentHom hpart hne hcent' hperm' hblock_u' φ c),
              Nat.factorial ((V i.1).card - 1) :=
          prod_blockSet_eq_of_moved hpart hne hcent' hperm' hblock_u' φ.2 hmove
        show compType g u (componentHom hpart hne hcent' hperm' hblock_u' φ c) = τ1
        rw [← hc.2]
        unfold compType
        rw [← h1, ← h2]
      have hne_attach_S : ∀ c ∈ S, (AmbientC0Attach g u c).Nonempty := fun c hc =>
        hne_attach c (Finset.mem_of_mem_filter c hc)
      have hfiberdvd := card_dvd_fiber_bound hpart hne hcent' hperm' hblock_u' S hSinv
        hne_attach_S
      set A'' := FixIslands (KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv) g u S
        with hA''def
      set M' := M.filter (fun c => compType g u c ≠ τ1) with hM'def
      have hcardM' : M'.card < M.card := by
        have hSM'disj : Disjoint S M' := by
          rw [Finset.disjoint_filter]
          intro c _ hcτ1 hcneτ1
          exact hcneτ1 hcτ1
        have hSM'union : S ∪ M' = M := by
          apply Finset.ext
          intro c
          simp only [hSdef, hM'def, Finset.mem_union, Finset.mem_filter]
          tauto
        have := Finset.card_union_of_disjoint hSM'disj
        rw [hSM'union] at this
        have hc1S' : c1 ∈ S := hc1S
        have : 1 ≤ S.card := Finset.card_pos.mpr ⟨c1, hc1S'⟩
        omega
      have hcardM'n : M'.card ≤ n := by omega
      have hA''leA' : A'' ≤ A' := by
        intro φ hφ
        exact kerFiberAmbient_le_A' hpart hne hcent' hperm' hblock_u' S hSinv
          (kerAttachmentAmbient_le_kerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv
            (mem_FixIslands.mp hφ).1)
      have hcent'' : ∀ φ ∈ A'', Commute φ g := fun φ hφ => hcent' φ (hA''leA' hφ)
      have hperm'' : ∀ φ ∈ A'', ∀ i, ∃ j, (V i).image φ = V j := fun φ hφ => hperm' φ (hA''leA' hφ)
      have hblock_u'' : ∀ φ ∈ A'', (V u).image φ = V u := fun φ hφ => hblock_u' φ (hA''leA' hφ)
      have hM'inv : ∀ φ : A'', ∀ c ∈ M', componentHom hpart hne hcent'' hperm'' hblock_u'' φ c ∈
          M' := by
        intro φ c hc
        rw [hM'def, Finset.mem_filter] at hc
        rw [hM'def, Finset.mem_filter]
        refine ⟨hMinv ⟨φ.1, hA''leA' φ.2⟩ c hc.1, ?_⟩
        intro hcontra
        have hmemS : componentHom hpart hne hcent'' hperm'' hblock_u'' φ c ∈ S := by
          rw [hSdef, Finset.mem_filter]
          exact ⟨hMinv ⟨φ.1, hA''leA' φ.2⟩ c hc.1, hcontra⟩
        have hφS : (φ.1 : Equiv.Perm Ω) ∈ FixIslands A' g u S :=
          mem_FixIslands.mpr ⟨hA''leA' φ.2, (mem_FixIslands.mp φ.2).2⟩
        have hfixmoved : componentPermOfMem hpart hne hcent' hperm' (hA''leA' φ.2)
            (hblock_u' φ.1 (hA''leA' φ.2))
            (componentHom hpart hne hcent'' hperm'' hblock_u'' φ c) =
            componentHom hpart hne hcent'' hperm'' hblock_u'' φ c :=
          fixIslands_fixes_component hpart hne hcent' hperm' hblock_u' S hne_attach_S hφS hmemS
        have hinj : Function.Injective (componentHom hpart hne hcent'' hperm'' hblock_u'' φ) :=
          (componentHom hpart hne hcent'' hperm'' hblock_u'' φ).injective
        have heq2 : componentHom hpart hne hcent'' hperm'' hblock_u'' φ
            (componentHom hpart hne hcent'' hperm'' hblock_u'' φ c) =
            componentHom hpart hne hcent'' hperm'' hblock_u'' φ c := hfixmoved
        have hcc : componentHom hpart hne hcent'' hperm'' hblock_u'' φ c = c := hinj heq2
        rw [hcc] at hcontra
        exact hc.2 hcontra
      have hIH := ih M' hcardM'n A'' hcent'' hperm'' hblock_u'' hM'inv
        (fun c hc => hne_attach c (Finset.mem_of_mem_filter c hc))
      have hFixEq : FixIslands A'' g u M' = FixIslands A' g u M := by
        apply le_antisymm
        · intro φ hφ
          rw [mem_FixIslands] at hφ ⊢
          refine ⟨hA''leA' hφ.1, ?_⟩
          intro c hc x hx
          by_cases hcS : compType g u c = τ1
          · have hcS' : c ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hc, hcS⟩
            exact (mem_FixIslands.mp hφ.1).2 c hcS' x hx
          · have hcM' : c ∈ M' := by rw [hM'def, Finset.mem_filter]; exact ⟨hc, hcS⟩
            exact hφ.2 c hcM' x hx
        · intro φ hφ
          rw [mem_FixIslands] at hφ
          have hφS : φ ∈ FixIslands A' g u S := by
            rw [mem_FixIslands]
            exact ⟨hφ.1, fun c hc x hx => hφ.2 c (Finset.mem_of_mem_filter c hc) x hx⟩
          have hfiberHom1 : fiberHom hpart hne hcent' hperm' hblock_u' S hSinv ⟨φ, hφ.1⟩ = 1 := by
            apply Equiv.ext
            intro ⟨c, hc⟩
            apply Subtype.ext
            show componentHom hpart hne hcent' hperm' hblock_u' ⟨φ, hφ.1⟩ c = c
            exact fixIslands_fixes_component hpart hne hcent' hperm' hblock_u' S hne_attach_S
              hφS hc
          have hφmemKFA : φ ∈ KerFiberAmbient hpart hne hcent' hperm' hblock_u' S hSinv :=
            ⟨⟨φ, hφ.1⟩, hfiberHom1, rfl⟩
          have hattachHom1 : attachmentFiberHom hpart hne hcent' hperm' hblock_u' S hSinv
              ⟨φ, hφmemKFA⟩ = 1 := by
            funext c
            apply Equiv.ext
            intro ⟨x, hx⟩
            apply Subtype.ext
            show φ x = x
            exact hφ.2 c.1 (Finset.mem_of_mem_filter c.1 c.2) x (Or.inr
              ⟨((mem_ambientC0Attach g u c.1 x).mp hx).1, ((mem_ambientC0Attach g u c.1 x).mp
                hx).2⟩)
          have hφmemKAA : φ ∈ KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv :=
            ⟨⟨φ, hφmemKFA⟩, hattachHom1, rfl⟩
          have hφA'' : φ ∈ A'' := by
            rw [hA''def, mem_FixIslands]
            exact ⟨hφmemKAA, fun c hc x hx => hφ.2 c (Finset.mem_of_mem_filter c hc) x hx⟩
          rw [mem_FixIslands]
          refine ⟨hφA'', ?_⟩
          intro c hc x hx
          rw [hM'def, Finset.mem_filter] at hc
          exact hφ.2 c hc.1 x hx
      rw [hFixEq] at hIH
      have hSprod : (∏ τ ∈ M.image (compType g u),
          (Nat.factorial (M.filter (fun c => compType g u c = τ)).card *
            (∏ c ∈ M.filter (fun c => compType g u c = τ),
              Nat.factorial (AmbientC0Attach g u c).card) *
            (∏ c ∈ M.filter (fun c => compType g u c = τ),
              ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
                Nat.factorial ((IslandV g u c i).card - 1)))) =
          (Nat.factorial S.card * (∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card) *
            (∏ c ∈ S, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1))) *
          (∏ τ ∈ M'.image (compType g u),
            (Nat.factorial (M'.filter (fun c => compType g u c = τ)).card *
              (∏ c ∈ M'.filter (fun c => compType g u c = τ),
                Nat.factorial (AmbientC0Attach g u c).card) *
              (∏ c ∈ M'.filter (fun c => compType g u c = τ),
                ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
                  Nat.factorial ((IslandV g u c i).card - 1)))) := by
        have himg : M.image (compType g u) = insert τ1 (M'.image (compType g u)) := by
          apply Finset.ext
          intro τ
          rw [Finset.mem_image, Finset.mem_insert, Finset.mem_image]
          constructor
          · intro h
            obtain ⟨c, hcM, hceq⟩ := h
            by_cases hcτ1 : compType g u c = τ1
            · left; exact hceq.symm.trans hcτ1
            · right
              refine ⟨c, ?_, hceq⟩
              rw [hM'def, Finset.mem_filter]
              exact ⟨hcM, hcτ1⟩
          · intro h
            rcases h with hτ1eq | h
            · exact ⟨c1, hc1M, hτ1eq ▸ hτ1def.symm⟩
            · obtain ⟨c, hcM', hceq⟩ := h
              rw [hM'def, Finset.mem_filter] at hcM'
              exact ⟨c, hcM'.1, hceq⟩
        have hτ1notin : τ1 ∉ M'.image (compType g u) := by
          rw [Finset.mem_image]
          rintro ⟨c, hc, hceq⟩
          rw [hM'def, Finset.mem_filter] at hc
          exact hc.2 hceq
        have hMfilterS : M.filter (fun c => compType g u c = τ1) = S := hSdef.symm
        have hMSprod_eq : ∀ τ ∈ M'.image (compType g u),
            M.filter (fun c => compType g u c = τ) = M'.filter (fun c => compType g u c = τ) := by
          intro τ hτ
          rw [Finset.mem_image] at hτ
          obtain ⟨c0', hc0'mem, hc0'eq⟩ := hτ
          rw [hM'def, Finset.mem_filter] at hc0'mem
          have hτne : τ ≠ τ1 := by rw [← hc0'eq]; exact hc0'mem.2
          apply Finset.ext
          intro c
          simp only [Finset.mem_filter, hM'def]
          constructor
          · intro hc
            refine ⟨⟨hc.1, ?_⟩, hc.2⟩
            rw [hc.2]
            exact hτne
          · intro hc
            exact ⟨hc.1.1, hc.2⟩
        rw [himg, Finset.prod_insert hτ1notin, hMfilterS]
        congr 1
        apply Finset.prod_congr rfl
        intro τ hτ
        rw [hMSprod_eq τ hτ]
      rw [hSprod]
      calc Nat.card A' ∣
          (Nat.factorial S.card * (∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card) *
            (∏ c ∈ S, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1))) *
            Nat.card (FixIslands (KerAttachmentAmbient hpart hne hcent' hperm' hblock_u' S hSinv)
              g u S) := hfiberdvd
        _ = (Nat.factorial S.card * (∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card) *
            (∏ c ∈ S, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1))) * Nat.card A'' := by rw [hA''def]
        _ ∣ (Nat.factorial S.card * (∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card) *
            (∏ c ∈ S, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1))) *
            ((∏ τ ∈ M'.image (compType g u),
                (Nat.factorial (M'.filter (fun c => compType g u c = τ)).card *
                  (∏ c ∈ M'.filter (fun c => compType g u c = τ),
                    Nat.factorial (AmbientC0Attach g u c).card) *
                  (∏ c ∈ M'.filter (fun c => compType g u c = τ),
                    ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
                      Nat.factorial ((IslandV g u c i).card - 1)))) *
              Nat.card (FixIslands A' g u M)) := mul_dvd_mul_left _ hIH
        _ = (Nat.factorial S.card * (∏ c ∈ S, Nat.factorial (AmbientC0Attach g u c).card) *
            (∏ c ∈ S, ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
              Nat.factorial ((IslandV g u c i).card - 1)) *
            (∏ τ ∈ M'.image (compType g u),
              (Nat.factorial (M'.filter (fun c => compType g u c = τ)).card *
                (∏ c ∈ M'.filter (fun c => compType g u c = τ),
                  Nat.factorial (AmbientC0Attach g u c).card) *
                (∏ c ∈ M'.filter (fun c => compType g u c = τ),
                  ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c),
                    Nat.factorial ((IslandV g u c i).card - 1))))) *
            Nat.card (FixIslands A' g u M) := by ring
