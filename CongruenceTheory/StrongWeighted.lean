import Mathlib
import CongruenceTheory.StrongTwoAdic

/-!
**Corollary `cor:weighted`** ("Weighted-permutation specialization"): specializing Theorem
`thm:strong` (`strong_two_adic`) via the evaluation ring homomorphism `X_j ↦ w_j`, for an
arbitrary integral weight sequence `w`, with no positivity assumption. This is the
permutation-native analogue of `cor:weighted`, matching the manuscript's `Cperm`/`CpermSum`
scoping already used for `thm:strong` itself (`CpermSum n` models `C_{2n}` on the domain
`Fin n ⊕ Fin n`, per `StrongTwoAdic.lean`).
-/

namespace CongruenceTheory

open MvPolynomial

/-- `A_w(n)`, the permutation-native weighted-permutation enumerator: `C_n(w_1,w_2,\dots)`
built from `Cperm` rather than the recurrence-native `C` (contrast `Aw` in
`WeightedSpecialization.lean`, which specializes `thm:universal` via `C`). -/
noncomputable def AwPerm (w : ℕ → ℤ) (n : ℕ) : ℤ := MvPolynomial.eval w (Cperm n)

/-- The `2n`-domain counterpart of `AwPerm`, matching `CpermSum`. -/
noncomputable def AwPermSum (w : ℕ → ℤ) (n : ℕ) : ℤ := MvPolynomial.eval w (CpermSum n)

/-- **Corollary `cor:weighted`**, permutation-native form: for every integral weight sequence
`w` and every `s ≥ 1`, `A_w(2^{s+1}) ≡ A_w(2^s)^2 (mod 2^{2s-1})` (with `A_w(2^{s+1})` modeled
as `AwPermSum w (2^s)`, the enumerator on the `2 \cdot 2^s`-point domain
`Fin (2^s) ⊕ Fin (2^s)`). -/
theorem AwPerm_two_adic_dynamics (s : ℕ) (hs : 1 ≤ s) (w : ℕ → ℤ) :
    (2 : ℤ) ^ (2 * s - 1) ∣ (AwPermSum w (2 ^ s) - AwPerm w (2 ^ s) * AwPerm w (2 ^ s)) := by
  obtain ⟨Q, hQ⟩ := strong_two_adic s hs
  refine ⟨MvPolynomial.eval w Q, ?_⟩
  have := congrArg (MvPolynomial.eval w) hQ
  simp only [map_sub, map_mul, map_natCast] at this
  rw [AwPermSum, AwPerm]
  push_cast at this ⊢
  linarith [this]

/-- Coefficientwise form: with a cycle-counting variable `u`, i.e. `w_j = u \cdot v_j` for a
fixed integral sequence `v`, the congruence holds identically in `\Z[u]` — the same divisibility
argument applied inside `MvPolynomial.eval₂` instead of `MvPolynomial.eval`. -/
theorem AwPerm_two_adic_dynamics_uvar (s : ℕ) (hs : 1 ≤ s) (v : ℕ → ℤ) :
    ∃ R : Polynomial ℤ,
      letI φ : ℕ → Polynomial ℤ := fun j => Polynomial.X * (Polynomial.C (v j))
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℤ)) φ (CpermSum (2 ^ s)) -
        (MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℤ)) φ (Cperm (2 ^ s))) ^ 2 =
        ((2 : Polynomial ℤ) ^ (2 * s - 1)) * R := by
  set φ : ℕ → Polynomial ℤ := fun j => Polynomial.X * (Polynomial.C (v j)) with hφ
  obtain ⟨Q, hQ⟩ := strong_two_adic s hs
  refine ⟨MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℤ)) φ Q, ?_⟩
  have h := congrArg (MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℤ)) φ) hQ
  simpa [sq, map_sub, map_mul, map_pow] using h

end CongruenceTheory
