import Mathlib

/-!
**`thm:complete-prime-local`(iii)'s `(A8)`/`(A12)`: converting mod-`p` digit conditions to an
exact `\N`-decomposition.** Given `c_s\equiv\varepsilon_s\pmod p` (as natural numbers) and
`h\equiv0\pmod p`, produces the explicit witnesses `c'_s`, `h'` with `c_s=pc'_s+\varepsilon_s`
and `h=ph'` that `Dc_frobenius_factorization` (`DcFrobenius.lean`) needs.
-/

namespace CongruenceTheory

/-- **If `h\equiv0\pmod p` (as naturals), `h=p\cdot(h/p)` exactly.** -/
theorem exists_decomp_of_dvd {p h : ℕ} (hh : (h : ZMod p) = 0) :
    ∃ h' : ℕ, h = p * h' := by
  rw [ZMod.natCast_eq_zero_iff] at hh
  obtain ⟨h', hh'⟩ := hh
  exact ⟨h', hh'⟩

/-- **If `c\equiv\varepsilon\pmod p` (as naturals, `\varepsilon<p`), `c=p\cdot(c/p)+\varepsilon`
exactly.** -/
theorem exists_decomp_of_modEq {p c ε : ℕ} (hεp : ε < p)
    (hc : (c : ZMod p) = (ε : ZMod p)) :
    ∃ c' : ℕ, c = p * c' + ε := by
  have hmodeq : c % p = ε % p := (ZMod.natCast_eq_natCast_iff' c ε p).mp hc
  rw [Nat.mod_eq_of_lt hεp] at hmodeq
  refine ⟨c / p, ?_⟩
  conv_lhs => rw [← Nat.div_add_mod c p]
  rw [hmodeq]

#print axioms exists_decomp_of_dvd
#print axioms exists_decomp_of_modEq

end CongruenceTheory
