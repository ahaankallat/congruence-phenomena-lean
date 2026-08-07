import Mathlib
import CongruenceTheory.Universal

/-!
Specialization of Theorem `thm:universal` to weighted-permutation sequences
`A_w`, and its easy corollaries: `cor:iterated`, the eigenvector corollary,
`cor:dynamics`.
-/

namespace CongruenceTheory

open Finset MvPolynomial

/-- `A_w(n)`, the weighted-permutation enumerator for an integral weight sequence `w`. -/
noncomputable def Aw (w : ℕ → ℤ) (n : ℕ) : ℤ := MvPolynomial.eval w (C n)

lemma cast_Aw_eq_eval_Cmod (k : ℕ) (w : ℕ → ℤ) (m : ℕ) :
    ((Aw w m : ℤ) : ZMod k) = MvPolynomial.eval (fun j => ((w j : ℤ) : ZMod k)) (Cmod k m) := by
  show (Int.castRingHom (ZMod k)) (Aw w m) = _
  rw [Aw, Cmod, MvPolynomial.eval₂_comp (Int.castRingHom (ZMod k)) w (C m),
    ← MvPolynomial.eval_map]
  rfl

/-- **Theorem `thm:universal`, specialized to `A_w`.** `A_w(n+k) ≡ A_w(n) A_w(k) (mod k)`. -/
theorem Aw_shift_mod (k : ℕ) (hk : 1 ≤ k) (w : ℕ → ℤ) (n : ℕ) :
    (k : ℤ) ∣ (Aw w (n + k) - Aw w n * Aw w k) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [cast_Aw_eq_eval_Cmod, cast_Aw_eq_eval_Cmod, cast_Aw_eq_eval_Cmod,
    universal_shift_mod k hk n, map_mul]
  ring

/-- **Corollary `cor:iterated`.** `A_w(n+qk) ≡ A_w(n) A_w(k)^q (mod k)`. -/
theorem Aw_iterated (k : ℕ) (hk : 1 ≤ k) (w : ℕ → ℤ) (n q : ℕ) :
    (k : ℤ) ∣ (Aw w (n + q * k) - Aw w n * Aw w k ^ q) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hstep := Aw_shift_mod k hk w (n + q * k)
    have heq : n + (q + 1) * k = (n + q * k) + k := by ring
    rw [heq]
    have hcomb : (k : ℤ) ∣
        (Aw w (n + q * k) - Aw w n * Aw w k ^ q) * Aw w k := Dvd.dvd.mul_right ih (Aw w k)
    have : Aw w ((n + q * k) + k) - Aw w n * Aw w k ^ (q + 1) =
        (Aw w ((n + q * k) + k) - Aw w (n + q * k) * Aw w k) +
        (Aw w (n + q * k) - Aw w n * Aw w k ^ q) * Aw w k := by ring
    rw [this]
    exact dvd_add hstep hcomb

/-- The `A_w`-eigenvector corollary: `A_w(n+k) ≡ A_w(k) A_w(n) (mod k)`, i.e. `A_w` modulo `k` is
an eigenvector of the translation operator `T_k`, with eigenvalue `A_w(k)`. -/
theorem Aw_translation_eigenvector (k : ℕ) (hk : 1 ≤ k) (w : ℕ → ℤ) (n : ℕ) :
    (k : ℤ) ∣ (Aw w (n + k) - Aw w k * Aw w n) := by
  have := Aw_shift_mod k hk w n
  have heq : Aw w (n + k) - Aw w k * Aw w n = Aw w (n + k) - Aw w n * Aw w k := by ring
  rwa [heq]

/-- **Corollary `cor:dynamics`.** Fix `k ≥ 1` and `c ≡ A_w(k) (mod k)`. For each residue
`0 ≤ r < k` and every `q ≥ 0`, `A_w(r+qk) ≡ A_w(r) c^q (mod k)`. -/
theorem Aw_dynamics (k : ℕ) (hk : 1 ≤ k) (w : ℕ → ℤ) (c : ℤ) (hc : (k : ℤ) ∣ (Aw w k - c))
    (r q : ℕ) : (k : ℤ) ∣ (Aw w (r + q * k) - Aw w r * c ^ q) := by
  have h1 := Aw_iterated k hk w r q
  have h2 : (k : ℤ) ∣ (Aw w r * Aw w k ^ q - Aw w r * c ^ q) := by
    have hpow : (k : ℤ) ∣ (Aw w k ^ q - c ^ q) := by
      have := sub_dvd_pow_sub_pow (Aw w k) c q
      exact hc.trans this
    rw [← mul_sub]
    exact Dvd.dvd.mul_left hpow (Aw w r)
  have : Aw w (r + q * k) - Aw w r * c ^ q =
      (Aw w (r + q * k) - Aw w r * Aw w k ^ q) + (Aw w r * Aw w k ^ q - Aw w r * c ^ q) := by ring
  rw [this]
  exact dvd_add h1 h2

end CongruenceTheory
