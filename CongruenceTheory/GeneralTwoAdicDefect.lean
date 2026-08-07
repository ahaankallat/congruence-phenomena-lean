import Mathlib
import CongruenceTheory.StrongTwoAdic
import CongruenceTheory.EGFCoordinates

/-!
**Corollary `cor:general-twoadic-defect`** ("General two-adic defect formula"),
denominator-cleared form.

The manuscript states this corollary in terms of the *abstract* cycle-index polynomial `C`
(`Basic.lean`, falling-factorial recurrence): for `n = 2^s`,
`R_s = (C_{2n} - C_n^2)/2^{2s-1} ∈ ℤ[X_1,X_2,…]`, and every `A ∈ 𝓔_ℚ` satisfies
`a_{2n} - a_n^2 = 2^{2s-1} R_s(u_1,…,u_{2n})`, with the denominator-cleared conclusion
`D^{2n}(a_{2n}-a_n^2) ∈ 2^{2s-1}ℤ` for a common denominator `D` of `u_1,…,u_{2n}`.

`thm:strong` itself, however, is only proved in this codebase in its **permutation-native**
form (`StrongTwoAdic.lean`, `strong_two_adic`): `CpermSum(n) - Cperm(n)^2 = 2^{2s-1} Q` for an
explicit `Q : MvPolynomial ℕ ℤ`. The identification `Cperm_n = C_n` (the manuscript's own
`prop:cperm-eq-c`-style cycle-index bijection) is **not** re-derived anywhere in this codebase
(matching the standing "Cperm=C bridge" caveat also noted for `thm:strong` itself). So what is
proved below is the honest permutation-native analogue: a total-degree bound
`totalDegree_ci_le`/`totalDegree_Cperm_le`/`totalDegree_CpermSum_le` on the cycle-index
polynomials (a permutation of `n` points has at most `n` cycles, counting fixed points),
transferred to the witness `Q` from `strong_two_adic` exactly as `totalDegree_Qpoly_le` does
for `thm:general-defect`, and then denominator-cleared via the already-proven
`evalAt_totalDegree_denom_clear`. This gives `general_twoadic_defect_denom_clear`: for any
common positive denominator `D` of integers `z_1,…,z_{2n}`,
`D^{2n} · evalAt(z/D)(CpermSum(n) - Cperm(n)^2) ∈ 2^{2s-1}ℤ` — the denominator-cleared
conclusion, in `Cperm`/`CpermSum` coordinates rather than actual EGF coefficients `a_n`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **`deg(ci g) ≤ |α|`**: the cycle-indicator monomial of a permutation has total degree at
most the cardinality of its domain — a permutation of `n` points has at most `n` cycles,
counting fixed points as length-`1` cycles. -/
theorem totalDegree_ci_le {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    (ci g).totalDegree ≤ Fintype.card α := by
  unfold ci
  have h1 : (X 1 ^ (Fintype.card α - g.cycleType.sum) : MvPolynomial ℕ ℤ).totalDegree =
      Fintype.card α - g.cycleType.sum := MvPolynomial.totalDegree_X_pow 1 _
  have h2 : ((g.cycleType.map X).prod : MvPolynomial ℕ ℤ).totalDegree ≤ g.cycleType.card := by
    have hle :=
      MvPolynomial.totalDegree_multiset_prod (g.cycleType.map (X : ℕ → MvPolynomial ℕ ℤ))
    rw [Multiset.map_map] at hle
    have heq : (g.cycleType.map (MvPolynomial.totalDegree ∘ (X : ℕ → MvPolynomial ℕ ℤ))) =
        g.cycleType.map (fun _ => 1) := by
      apply Multiset.map_congr rfl
      intro ℓ _
      exact MvPolynomial.totalDegree_X ℓ
    rw [heq] at hle
    simpa using hle
  calc (X 1 ^ (Fintype.card α - g.cycleType.sum) * (g.cycleType.map X).prod :
        MvPolynomial ℕ ℤ).totalDegree
      ≤ (X 1 ^ (Fintype.card α - g.cycleType.sum) : MvPolynomial ℕ ℤ).totalDegree +
          ((g.cycleType.map X).prod : MvPolynomial ℕ ℤ).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ (Fintype.card α - g.cycleType.sum) + g.cycleType.card := by rw [h1]; gcongr
    _ ≤ Fintype.card α := by
        have hsum := Equiv.Perm.sum_cycleType_le g
        have hcard : g.cycleType.card ≤ g.cycleType.sum := by
          have h3 := Multiset.card_nsmul_le_sum
            (s := g.cycleType) (a := 2)
            (fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx)
          simp only [smul_eq_mul] at h3
          omega
        omega

theorem totalDegree_Cperm_le (n : ℕ) : (Cperm n).totalDegree ≤ n := by
  unfold Cperm
  apply le_trans (MvPolynomial.totalDegree_finsetSum _ _)
  apply Finset.sup_le
  intro g _
  simpa using totalDegree_ci_le g

theorem totalDegree_CpermSum_le (n : ℕ) : (CpermSum n).totalDegree ≤ 2 * n := by
  unfold CpermSum
  apply le_trans (MvPolynomial.totalDegree_finsetSum _ _)
  apply Finset.sup_le
  intro g _
  have h := totalDegree_ci_le g
  have hcard : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
    rw [Fintype.card_sum, Fintype.card_fin]; omega
  rwa [hcard] at h

theorem totalDegree_strong_two_adic_diff_le (n : ℕ) :
    (CpermSum n - Cperm n * Cperm n).totalDegree ≤ 2 * n := by
  calc (CpermSum n - Cperm n * Cperm n).totalDegree
      ≤ max (CpermSum n).totalDegree (Cperm n * Cperm n).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ max (2 * n) (2 * n) := by
        apply max_le_max
        · exact totalDegree_CpermSum_le n
        · exact le_trans (MvPolynomial.totalDegree_mul _ _) (by
            have := totalDegree_Cperm_le n; omega)
    _ = 2 * n := by omega

/-- The witness `Q` from `strong_two_adic` inherits total degree `≤ 2·2^s`, since scaling by
the nonzero integer `2^{2s-1}` doesn't change total degree. -/
theorem totalDegree_strong_two_adic_Q_le (s : ℕ) (hs : 1 ≤ s) (Q : MvPolynomial ℕ ℤ)
    (hQ : CpermSum (2 ^ s) - Cperm (2 ^ s) * Cperm (2 ^ s) =
      ((2 ^ (2 * s - 1) : ℕ) : MvPolynomial ℕ ℤ) * Q) :
    Q.totalDegree ≤ 2 * 2 ^ s := by
  have hkne : ((2 ^ (2 * s - 1) : ℕ) : ℤ) ≠ 0 := by positivity
  have hcast :
      ((2 ^ (2 * s - 1) : ℕ) : MvPolynomial ℕ ℤ) =
        MvPolynomial.C ((2 ^ (2 * s - 1) : ℕ) : ℤ) := by simp
  have heq : (MvPolynomial.C ((2 ^ (2 * s - 1) : ℕ) : ℤ) * Q).totalDegree = Q.totalDegree :=
    totalDegree_C_mul_eq hkne Q
  rw [← heq, ← hcast, ← hQ]
  exact totalDegree_strong_two_adic_diff_le (2 ^ s)

/-- **`cor:general-twoadic-defect`**, denominator-cleared form, in the permutation-native
coordinates actually proven in this codebase: if `D` is a common positive denominator for
integers `z_1,…,z_{2·2^s}`, then `D^{2·2^s}` times the evaluation of
`CpermSum(2^s) - Cperm(2^s)^2` at `u_j = z_j/D` is an integer multiple of `2^{2s-1}`. -/
theorem general_twoadic_defect_denom_clear (s : ℕ) (hs : 1 ≤ s) (D : ℕ) (hD : 0 < D)
    (z : ℕ → ℤ) :
    ∃ w : ℤ, (D : ℚ) ^ (2 * 2 ^ s) *
        evalAt (fun j => (z j : ℚ) / (D : ℚ))
          (CpermSum (2 ^ s) - Cperm (2 ^ s) * Cperm (2 ^ s)) =
      ((2 ^ (2 * s - 1) : ℕ) : ℚ) * (w : ℚ) := by
  obtain ⟨Q, hQ⟩ := strong_two_adic s hs
  have hQdeg := totalDegree_strong_two_adic_Q_le s hs Q hQ
  obtain ⟨w, hw⟩ := evalAt_totalDegree_denom_clear Q (2 * 2 ^ s) hQdeg z D hD
  refine ⟨w, ?_⟩
  rw [hQ]
  show (D : ℚ) ^ (2 * 2 ^ s) *
      evalAt _ (((2 ^ (2 * s - 1) : ℕ) : MvPolynomial ℕ ℤ) * Q) = _
  rw [map_mul]
  have hcast :
      evalAt (fun j => (z j : ℚ) / (D : ℚ)) ((2 ^ (2 * s - 1) : ℕ) : MvPolynomial ℕ ℤ) =
        ((2 ^ (2 * s - 1) : ℕ) : ℚ) := by simp [evalAt]
  rw [hcast]
  rw [show (D : ℚ) ^ (2 * 2 ^ s) *
        (((2 ^ (2 * s - 1) : ℕ) : ℚ) * evalAt (fun j => (z j : ℚ) / (D : ℚ)) Q)
      = ((2 ^ (2 * s - 1) : ℕ) : ℚ) *
        ((D : ℚ) ^ (2 * 2 ^ s) * evalAt (fun j => (z j : ℚ) / (D : ℚ)) Q) by ring,
    hw]

end CongruenceTheory
