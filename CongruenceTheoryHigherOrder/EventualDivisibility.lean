import Mathlib
import CongruenceTheoryHigherOrder.OddPrimePower
import CongruenceTheoryHigherOrder.PowerOfTwoLocal

/-!
**Eventual divisibility** (main paper, Corollary `cor:eventual-divisibility`).  Let `p` be a
prime, `e ≥ 1` and `γ_p = w_1 + (p-1) w_p`.

* `eventual_divisibility_pow`: if `p ∣ γ_p`, `r ≥ e` (and `r ≥ 4` if `p = 2`), then
  `p^e ∣ A_w(n)` for every `n ≥ p^r` (indeed `p^r ∣ A_w(n)`).
* `eventual_divisibility_iff`: `A_w(n) ≡ 0 (mod p^e)` for all sufficiently large `n` iff `p ∣ γ_p`.

The proof uses `odd_prime_power_residue` (odd `p`), the `p = 2` residue `power_of_two_residue_local`
(`CongruenceTheoryHigherOrder/PowerOfTwoLocal`), and the shift congruence `Aw_shift_mod` with
`k = p^r`.
-/

namespace CongruenceTheory.Shift

/-- `A_w(0) = 1`. -/
theorem Aw_zero' (w : ℕ → ℤ) : Aw w 0 = 1 := by simp [Aw, C_zero]

/-- For every prime `p` and `r ≥ 1`, `A_w(p^r) ≡ γ_p^(p^(r-1)) (mod p^r)` when `p` is odd, and
when `p = 2` and `r ≥ 4`. -/
theorem prime_power_residue {p : ℕ} (hp : p.Prime) (w : ℕ → ℤ) (r : ℕ) (hr : 1 ≤ r)
    (h4 : p = 2 → 4 ≤ r) :
    (p : ℤ) ^ r ∣ Aw w (p ^ r) - (w 1 + ((p : ℤ) - 1) * w p) ^ (p ^ (r - 1)) := by
  by_cases h2 : p = 2
  · subst h2
    simpa using power_of_two_residue_local w r (h4 rfl)
  · exact odd_prime_power_residue hp h2 w r hr

/-- **Corollary `cor:eventual-divisibility`, first part.** -/
theorem eventual_divisibility_pow {p : ℕ} (hp : p.Prime) (w : ℕ → ℤ)
    (hγ : (p : ℤ) ∣ w 1 + ((p : ℤ) - 1) * w p) {e r : ℕ} (he : e ≤ r) (hr : 1 ≤ r)
    (h4 : p = 2 → 4 ≤ r) {n : ℕ} (hn : p ^ r ≤ n) : (p : ℤ) ^ e ∣ Aw w n := by
  have hres := prime_power_residue hp w r hr h4
  have hlt : r ≤ p ^ (r - 1) := by
    have := Nat.lt_pow_self (n := r - 1) hp.one_lt
    omega
  have hγpow : (p : ℤ) ^ r ∣ (w 1 + ((p : ℤ) - 1) * w p) ^ (p ^ (r - 1)) :=
    (pow_dvd_pow _ hlt).trans (pow_dvd_pow_of_dvd hγ _)
  have hAr : (p : ℤ) ^ r ∣ Aw w (p ^ r) := by
    have := dvd_add hres hγpow
    simpa using this
  have hk : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp.pos
  have hsh := Aw_shift_mod (p ^ r) hk w (n - p ^ r)
  rw [Nat.sub_add_cancel hn] at hsh
  push_cast at hsh
  have : (p : ℤ) ^ r ∣ Aw w n := by
    have h2 : (p : ℤ) ^ r ∣ Aw w (n - p ^ r) * Aw w (p ^ r) := hAr.mul_left _
    have := dvd_add hsh h2
    simpa using this
  exact (pow_dvd_pow _ he).trans this

/-- **Corollary `cor:eventual-divisibility`, "if" direction.** -/
theorem eventual_divisibility_of_dvd {p : ℕ} (hp : p.Prime) (w : ℕ → ℤ)
    (hγ : (p : ℤ) ∣ w 1 + ((p : ℤ) - 1) * w p) (e : ℕ) :
    ∃ N, ∀ n, N ≤ n → (p : ℤ) ^ e ∣ Aw w n := by
  refine ⟨p ^ (e + 4), fun n hn => ?_⟩
  exact eventual_divisibility_pow hp w hγ (r := e + 4) (by omega) (by omega) (fun _ => by omega) hn

/-- **Corollary `cor:eventual-divisibility`, "only if" direction.** -/
theorem dvd_of_eventually_dvd {p : ℕ} (hp : p.Prime) (w : ℕ → ℤ) (n0 : ℕ)
    (h : ∀ n, n0 ≤ n → (p : ℤ) ∣ Aw w n) : (p : ℤ) ∣ w 1 + ((p : ℤ) - 1) * w p := by
  by_contra hγ
  have hAp : ¬ (p : ℤ) ∣ Aw w p := by
    intro hd
    apply hγ
    have := Aw_prime_cong hp w
    have := dvd_sub hd this
    simpa using this
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have key : ∀ j n, n0 ≤ n + j * p → (p : ℤ) ∣ Aw w n := by
    intro j
    induction j with
    | zero => intro n hn; exact h n (by simpa using hn)
    | succ j ih =>
      intro n hn
      have h1 : (p : ℤ) ∣ Aw w (n + p) := ih (n + p) (by nlinarith)
      have h2 := Aw_shift_mod p hp.one_lt.le w n
      have h3 : (p : ℤ) ∣ Aw w n * Aw w p := by
        have := dvd_sub h1 h2
        simpa using this
      exact (hpp.dvd_or_dvd h3).resolve_right hAp
  have := key n0 0 (by have := hp.two_le; nlinarith)
  rw [Aw_zero'] at this
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

/-- **Corollary `cor:eventual-divisibility`.**  `A_w(n) ≡ 0 (mod p^e)` for all large `n` (for a
fixed `e ≥ 1`) iff `p ∣ w_1 + (p-1) w_p`. -/
theorem eventual_divisibility_iff {p : ℕ} (hp : p.Prime) (w : ℕ → ℤ) {e : ℕ} (he : 1 ≤ e) :
    (∃ N, ∀ n, N ≤ n → (p : ℤ) ^ e ∣ Aw w n) ↔ (p : ℤ) ∣ w 1 + ((p : ℤ) - 1) * w p := by
  constructor
  · rintro ⟨N, hN⟩
    exact dvd_of_eventually_dvd hp w N fun n hn =>
      (dvd_pow_self (p : ℤ) (by omega)).trans (hN n hn)
  · intro hγ
    exact eventual_divisibility_of_dvd hp w hγ e

end CongruenceTheory.Shift
