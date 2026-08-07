import Mathlib

/-!
Formalization of Lemma `lem:orbit-bound` ("Equipartition orbit bound") from
the manuscript, the sole numerical input to Theorem `thm:strong` (Strong
two-adic lifting). We give a shorter, self-contained derivation than the
manuscript's, using Mathlib's Kummer/Legendre `Nat.factorization` API
directly instead of re-deriving Lucas' theorem by hand; the final numeric
inequality proved is identical to the manuscript's `eq:factorial-bound`.
-/

namespace CongruenceTheory

open Nat

/-- The 2-adic valuation of a natural number, via `Nat.factorization`. -/
noncomputable def v2 (m : ℕ) : ℕ := m.factorization 2

lemma v2_two_prime : Nat.Prime 2 := by norm_num

/-- Auxiliary fact: for `t ≥ 1`, `v2(t) ≤ v2((t-1)!) + 1`. The single factor
`2^(v2(t)-1) ≤ t - 1` already present among `1, ..., t-1` accounts for it. -/
lemma v2_le_v2_pred_factorial_add_one (t : ℕ) (ht : 1 ≤ t) :
    v2 t ≤ v2 ((t - 1)!) + 1 := by
  rcases Nat.eq_zero_or_pos (v2 t) with hc0 | hcpos
  · omega
  · set c := v2 t with hcdef
    have htne : t ≠ 0 := by omega
    have hpow : (2:ℕ) ^ c ∣ t :=
      (Nat.Prime.pow_dvd_iff_le_factorization v2_two_prime htne).mpr le_rfl
    have ht2c : (2:ℕ) ^ c ≤ t := Nat.le_of_dvd (by omega) hpow
    have heq : (2:ℕ) ^ (c - 1) * 2 = 2 ^ c := by
      rw [← pow_succ]
      congr 1
      omega
    have hxpos : 1 ≤ (2:ℕ) ^ (c - 1) := Nat.one_le_two_pow
    have hle : (2:ℕ) ^ (c - 1) ≤ t - 1 := by omega
    have hdvd2 : (2:ℕ) ^ (c - 1) ∣ (t - 1)! :=
      Nat.dvd_factorial (by positivity) hle
    have hval : c - 1 ≤ v2 ((t - 1)!) :=
      (Nat.Prime.pow_dvd_iff_le_factorization v2_two_prime
        (Nat.factorial_ne_zero _)).mp hdvd2
    omega

/-- Factorial valuation is monotone. -/
lemma v2_factorial_mono {m n : ℕ} (h : m ≤ n) : v2 (m !) ≤ v2 (n !) :=
  Nat.factorization_le_factorization_of_dvd_right
    (Nat.factorial_dvd_factorial h) (Nat.factorial_ne_zero m) (Nat.factorial_ne_zero n)

/-- The key elementary inequality behind the orbit bound, isolated from the
prime-power structure of `n = 2^s`: for `1 ≤ a, b`,
`max(v2(a!), v2(b!)) + 1 ≥ v2(a) + v2(b)`. -/
lemma max_v2_factorial_add_one_ge (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    v2 a + v2 b ≤ max (v2 (a !)) (v2 (b !)) + 1 := by
  wlog hab : a ≤ b generalizing a b
  · have := this b a hb ha (by omega)
    rw [max_comm]
    omega
  have h1 : v2 a ≤ v2 ((a - 1)!) + 1 := v2_le_v2_pred_factorial_add_one a ha
  have h2 : v2 ((a - 1)!) ≤ v2 ((b - 1)!) := v2_factorial_mono (by omega)
  have h3 : v2 (b !) = v2 b + v2 ((b - 1)!) := by
    have heqb : b * (b - 1)! = b ! := Nat.mul_factorial_pred (by omega)
    simp only [v2, ← heqb,
      Nat.factorization_mul (show b ≠ 0 by omega) (Nat.factorial_ne_zero (b - 1)),
      Finsupp.add_apply]
  have h4 : v2 a + v2 b ≤ v2 (b !) + 1 := by omega
  have h5 : v2 (b !) ≤ max (v2 (a !)) (v2 (b !)) := le_max_right _ _
  omega

/-- The prime-power `F`-identity: for `n = 2^s` and `1 ≤ t ≤ n`,
`v2(n!) + v2(t) = s + v2(t!) + v2((n-t)!)`. This is the manuscript's
`eq:power-two-binomial` combined with the factorial factorization of the
binomial coefficient, in additive (no-truncation) form. -/
lemma val_identity (s t : ℕ) (ht0 : t ≠ 0) (htn : t ≤ 2 ^ s) :
    v2 ((2 ^ s)!) + v2 t = s + v2 (t !) + v2 ((2 ^ s - t)!) := by
  have hchoose : v2 (Nat.choose (2 ^ s) t) + v2 t = s :=
    Nat.factorization_choose_prime_pow_add_factorization v2_two_prime htn ht0
  have hprod : Nat.choose (2 ^ s) t * t ! * (2 ^ s - t)! = (2 ^ s)! :=
    Nat.choose_mul_factorial_mul_factorial htn
  have hne1 : Nat.choose (2 ^ s) t ≠ 0 := Nat.choose_ne_zero_iff.mpr htn
  have hval : v2 ((2 ^ s)!) =
      v2 (Nat.choose (2 ^ s) t) + v2 (t !) + v2 ((2 ^ s - t)!) := by
    simp only [v2, ← hprod,
      Nat.factorization_mul (Nat.mul_ne_zero hne1 (Nat.factorial_ne_zero t))
        (Nat.factorial_ne_zero (2 ^ s - t)),
      Nat.factorization_mul hne1 (Nat.factorial_ne_zero t),
      Finsupp.add_apply]
  rw [hval]
  omega

/-- **Lemma `lem:orbit-bound`** ("Equipartition orbit bound"). For `n = 2^s`,
`s ≥ 1`, and `1 ≤ a, b ≤ n`:
`2 v2(n!) - v2((n-a)!) - v2((n-b)!) - min(v2(a!), v2(b!)) ≥ 2s - 1`,
stated in addition-only form to avoid `ℕ`-truncation:
`2 v2(n!) + 1 ≥ v2((n-a)!) + v2((n-b)!) + min(v2(a!), v2(b!)) + 2 s`. -/
theorem orbit_bound (s a b : ℕ) (_hs : 1 ≤ s) (ha : 1 ≤ a) (han : a ≤ 2 ^ s)
    (hb : 1 ≤ b) (hbn : b ≤ 2 ^ s) :
    v2 ((2 ^ s - a)!) + v2 ((2 ^ s - b)!) + min (v2 (a !)) (v2 (b !)) + 2 * s ≤
      2 * v2 ((2 ^ s)!) + 1 := by
  have hA := val_identity s a (by omega) han
  have hB := val_identity s b (by omega) hbn
  have hmax := max_v2_factorial_add_one_ge a b ha hb
  have hminmax : min (v2 (a !)) (v2 (b !)) + max (v2 (a !)) (v2 (b !)) =
      v2 (a !) + v2 (b !) := min_add_max _ _
  omega

end CongruenceTheory
