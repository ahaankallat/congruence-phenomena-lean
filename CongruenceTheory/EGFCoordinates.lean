import Mathlib
import CongruenceTheory.PowerSeriesLog
import CongruenceTheory.Basic
import CongruenceTheory.BaseChange

/-!
**Theorem `thm:all-egf-coordinates`** (coefficient half) and **Theorem `thm:general-defect`**:
the bridge between the abstract cycle-index polynomials `C_n` (`Basic.lean`, defined by the
falling-factorial recurrence) and actual formal EGFs `F ∈ 1+xℚ[[x]]` in canonical logarithmic
coordinates (`PowerSeriesLog.lean`).

**Proof strategy**, matching the manuscript exactly: differentiate `F = exp(logOf F)`. The
log-derivative rule `D(logOf F)·F = D(F)` (`deriv_logOf_mul_self`), extracted at coefficient
`n`, gives `∑_{i=0}^n u_{i+1}·[x^{n-i}]F = (n+1)·[x^{n+1}]F`. Multiplying by `n!` and using
`n!/(n-i)! = fall(n,i)` turns this into exactly `C`'s own defining recurrence
(`C_succ`) with `X_j ↦ u_j`, so `egfCoeff F n = C_n(u_1,...,u_n)` follows by the same strong
induction that defines `C`. `thm:general-defect`'s displayed identity is then an immediate
corollary of `thm:base-change` (`base_change_mod`), specialized to `R = ℚ` and
`r = canonicalCoord · F`.
-/

namespace CongruenceTheory

open PowerSeries Finset

/-- `a_n = n! [x^n] F`, the exponential-generating-function coefficients of `F`, matching the
manuscript's `A(x) = ∑ a_n x^n/n!`. -/
noncomputable def egfCoeff (F : ℚ⟦X⟧) (n : ℕ) : ℚ := (Nat.factorial n : ℚ) * coeff n F

lemma fall_eq_descFactorial (n r : ℕ) (hr : r ≤ n) :
    fall n r = (n.descFactorial r : ℤ) := by
  rw [fall, Nat.descFactorial_eq_prod_range]
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  have hir : i < r := Finset.mem_range.mp hi
  have hin : i ≤ n := by omega
  omega

lemma factorial_eq_fall_mul (n r : ℕ) (hr : r ≤ n) :
    (Nat.factorial n : ℚ) = (fall n r : ℚ) * (Nat.factorial (n - r) : ℚ) := by
  rw [fall_eq_descFactorial n r hr]
  push_cast
  rw [← Nat.factorial_mul_descFactorial hr]
  push_cast
  ring

/-- Coefficient-level form of the log-derivative rule `D(logOf F)·F = D(F)`, extracted at
degree `n`: `∑_{i=0}^n u_{i+1}·[x^{n-i}]F = (n+1)·[x^{n+1}]F`. -/
lemma coeff_recurrence (F : ℚ⟦X⟧) (hF1 : constantCoeff F = 1) (n : ℕ) :
    ∑ i ∈ range (n + 1), canonicalCoord (i + 1) F * coeff (n - i) F =
      coeff (n + 1) F * (n + 1) := by
  have hkey := deriv_logOf_mul_self F hF1
  have hc := congrArg (coeff n) hkey
  rw [coeff_derivative, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (d⁄dX ℚ (logOf F)) * coeff j F)] at hc
  rw [← hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_derivative]
  simp only [canonicalCoord]
  push_cast
  ring

/-- The manuscript's `thm:all-egf-coordinates` recurrence, in terms of `egfCoeff` (`a_n`) and
`canonicalCoord` (`u_j`): `a_{n+1} = ∑_{r=0}^n fall(n,r) u_{r+1} a_{n-r}` — matches `C`'s own
defining recurrence (`C_succ`) exactly, with `X_j ↦ u_j`. -/
theorem egfCoeff_recurrence (F : ℚ⟦X⟧) (hF1 : constantCoeff F = 1) (n : ℕ) :
    egfCoeff F (n + 1) =
      ∑ r ∈ range (n + 1), (fall n r : ℚ) * canonicalCoord (r + 1) F * egfCoeff F (n - r) := by
  have hrec := coeff_recurrence F hF1 n
  have hmul := congrArg (fun x => (Nat.factorial n : ℚ) * x) hrec
  rw [Finset.mul_sum] at hmul
  have hlhs : (Nat.factorial n : ℚ) * (coeff (n + 1) F * (n + 1)) = egfCoeff F (n + 1) := by
    unfold egfCoeff
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hlhs] at hmul
  rw [← hmul]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r ≤ n := by
    have := Finset.mem_range.mp hr
    omega
  have hfe := factorial_eq_fall_mul n r hrn
  unfold egfCoeff
  rw [hfe]
  ring

/-- **Theorem `thm:all-egf-coordinates`**, coefficient half: `a_n = C_n(u_1,...,u_n)`, where
`a_n` is the EGF coefficient and `u_j` the canonical logarithmic coordinate. Not formalized
here: the companion multinomial/cycle-type sum formula
`a_n = ∑_{λ⊢n} (n!/z_λ) ∏_j u_j^{m_j}` — a separate combinatorial identity for `C_n` itself,
not needed for `thm:general-defect`/`thm:local-locus` below. -/
theorem egfCoeff_eq_cVal (F : ℚ⟦X⟧) (hF1 : constantCoeff F = 1) :
    ∀ n : ℕ, egfCoeff F n = cVal (fun j => canonicalCoord j F) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      unfold egfCoeff cVal evalAt
      rw [C_zero]
      simp [hF1]
    | m + 1 =>
      rw [egfCoeff_recurrence F hF1 m]
      have hev := congrArg (evalAt (fun j => canonicalCoord j F)) (C_succ m)
      simp only [map_sum, map_mul] at hev
      show _ = evalAt (fun j => canonicalCoord j F) (C (m + 1))
      rw [hev]
      apply Finset.sum_congr rfl
      intro r hr
      have hrm : r ≤ m := by
        have := Finset.mem_range.mp hr
        omega
      have hihr : egfCoeff F (m - r) = cVal (fun j => canonicalCoord j F) (m - r) :=
        ih (m - r) (by omega)
      rw [cVal] at hihr
      rw [hihr]
      have hXeval :
          evalAt (fun j => canonicalCoord j F) (MvPolynomial.X (r + 1)) =
            canonicalCoord (r + 1) F := by
        simp [evalAt]
      rw [hXeval]
      have hfeval :
          evalAt (fun j => canonicalCoord j F) ((fall m r : MvPolynomial ℕ ℤ)) =
            (fall m r : ℚ) := by
        simp [evalAt]
      rw [hfeval]
      ring

/-- **Theorem `thm:general-defect`, main identity.** For `F ∈ 𝓔_ℚ` (constant term `1`),
with EGF coefficients `a_n = egfCoeff F n` and canonical coordinates `u_j = canonicalCoord j F`,
`a_{n+k} - a_n a_k = k · Q_{n,k}(u_1,...,u_{n+k})`. An immediate corollary of `base_change_mod`
via `egfCoeff_eq_cVal`. -/
theorem general_defect_main (F : ℚ⟦X⟧) (hF1 : constantCoeff F = 1) (n k : ℕ) (hk : 1 ≤ k) :
    egfCoeff F (n + k) - egfCoeff F n * egfCoeff F k =
      (k : ℚ) * evalAt (fun j => canonicalCoord j F) (Qpoly n k hk) := by
  rw [egfCoeff_eq_cVal F hF1, egfCoeff_eq_cVal F hF1, egfCoeff_eq_cVal F hF1]
  exact base_change_mod (fun j => canonicalCoord j F) n k hk

/-- Evaluation of an integer polynomial at values that are themselves images of integers is
the image of an integer — the naturality fact behind `thm:general-defect`, part (i). -/
theorem evalAt_intCast (z : ℕ → ℤ) (P : MvPolynomial ℕ ℤ) :
    evalAt (fun j => ((z j : ℤ) : ℚ)) P = ((MvPolynomial.eval z P : ℤ) : ℚ) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evalAt]
  | add p q hp hq => rw [map_add, map_add, hp, hq]; push_cast; ring
  | mul_X p j hp =>
    rw [map_mul, map_mul, hp]
    simp [evalAt]

/-- **Theorem `thm:general-defect`, part (i).** If `F ∈ 𝓛_ℤ` (all canonical coordinates
`u_m` are integers), then `a_{n+k} ≡ a_n a_k (mod k)`: the defect is an exact integer
multiple of `k`. (Integrality of the `a_n` themselves is immediate from
`egfCoeff_eq_cVal`, since `C_n` has integer coefficients.) -/
theorem general_defect_integral (F : ℚ⟦X⟧) (hF1 : constantCoeff F = 1)
    (z : ℕ → ℤ) (hz : ∀ m, canonicalCoord m F = (z m : ℚ)) (n k : ℕ) (hk : 1 ≤ k) :
    ∃ w : ℤ, egfCoeff F (n + k) - egfCoeff F n * egfCoeff F k = (k : ℚ) * (w : ℚ) := by
  refine ⟨MvPolynomial.eval z (Qpoly n k hk), ?_⟩
  rw [general_defect_main F hF1 n k hk]
  congr 1
  rw [show (fun j => canonicalCoord j F) = (fun j => ((z j : ℤ) : ℚ)) from funext hz]
  exact evalAt_intCast z (Qpoly n k hk)

/-- **`deg C_m ≤ m`**: every monomial of the cycle-index polynomial `C_m` has total degree at
most `m` — a permutation of `m` points has at most `m` cycles. Proved by induction directly on
`C`'s own defining recurrence (`C_succ`). -/
theorem totalDegree_C_le : ∀ n : ℕ, (C n).totalDegree ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [C_zero]; simp
    | m + 1 =>
      rw [C_succ]
      apply le_trans (MvPolynomial.totalDegree_finsetSum _ _)
      apply Finset.sup_le
      intro r hr
      have hrm : r ≤ m := by
        have := Finset.mem_range.mp hr; omega
      have hcast : ((fall m r : ℤ) : MvPolynomial ℕ ℤ) = MvPolynomial.C (fall m r) := by simp
      have step1 :
          (((fall m r : ℤ) : MvPolynomial ℕ ℤ) *
              (MvPolynomial.X (r + 1) * C (m - r))).totalDegree ≤
            ((fall m r : ℤ) : MvPolynomial ℕ ℤ).totalDegree +
              (MvPolynomial.X (r + 1) * C (m - r)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      have step2 : ((fall m r : ℤ) : MvPolynomial ℕ ℤ).totalDegree = 0 := by
        rw [hcast]; exact MvPolynomial.totalDegree_C _
      have step3 :
          (MvPolynomial.X (r + 1) * C (m - r) : MvPolynomial ℕ ℤ).totalDegree ≤
            (MvPolynomial.X (r + 1) : MvPolynomial ℕ ℤ).totalDegree + (C (m - r)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      have step4 : (MvPolynomial.X (r + 1) : MvPolynomial ℕ ℤ).totalDegree ≤ 1 :=
        (MvPolynomial.totalDegree_X (r + 1)).le
      have step5 : (C (m - r)).totalDegree ≤ m - r := ih (m - r) (by omega)
      omega

theorem totalDegree_C_mul_eq {k : ℤ} (hk : k ≠ 0) (Q : MvPolynomial ℕ ℤ) :
    (MvPolynomial.C k * Q).totalDegree = Q.totalDegree := by
  rw [← MvPolynomial.smul_eq_C_mul]
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_smul_eq hk]

/-- `Q_{n,k}` inherits the same total-degree bound `n+k` as `C_{n+k}` and `C_n C_k`, since
scaling by the nonzero constant `k` doesn't change total degree (`ℤ` has no zero divisors). -/
theorem totalDegree_Qpoly_le (n k : ℕ) (hk : 1 ≤ k) : (Qpoly n k hk).totalDegree ≤ n + k := by
  have hspec := Qpoly_spec n k hk
  have hkne : (k : ℤ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have heq : (MvPolynomial.C (k : ℤ) * Qpoly n k hk).totalDegree = (Qpoly n k hk).totalDegree :=
    totalDegree_C_mul_eq hkne (Qpoly n k hk)
  rw [← heq, ← hspec]
  calc (C (n + k) - C n * C k).totalDegree
      ≤ max (C (n + k)).totalDegree (C n * C k).totalDegree := MvPolynomial.totalDegree_sub _ _
    _ ≤ max (n + k) (n + k) := by
        apply max_le_max
        · exact totalDegree_C_le (n + k)
        · exact le_trans (MvPolynomial.totalDegree_mul _ _) (by
            have := totalDegree_C_le n; have := totalDegree_C_le k; omega)
    _ = n + k := by omega

/-- Denominator-clearing: if every variable of `Q` is evaluated at a rational `z_j/D` with
common denominator `D > 0`, and `Q.totalDegree ≤ N`, then `D^N` times the evaluation is an
integer. Each monomial of degree `d ≤ N` in the support contributes
`coeff · D^{N-d} · ∏ z_i^{e_i}` after clearing, an integer since `N - d ≥ 0`. -/
theorem evalAt_totalDegree_denom_clear (Q : MvPolynomial ℕ ℤ) (N : ℕ) (hQ : Q.totalDegree ≤ N)
    (z : ℕ → ℤ) (D : ℕ) (hD : 0 < D) :
    ∃ w : ℤ, (w : ℚ) = (D : ℚ) ^ N * evalAt (fun j => (z j : ℚ) / (D : ℚ)) Q := by
  refine ⟨∑ d ∈ Q.support, Q.coeff d * (D : ℤ) ^ (N - ∑ x ∈ d.support, d x) *
    ∏ i ∈ d.support, (z i) ^ (d i), ?_⟩
  show (_ : ℚ) = (D : ℚ) ^ N *
    MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun j => (z j : ℚ) / (D : ℚ)) Q
  rw [MvPolynomial.eval₂_eq]
  push_cast
  rw [Finset.mul_sum, Finset.sum_congr rfl]
  intro d hd
  have hsum_eq : (d.sum fun _ e => e) = ∑ x ∈ d.support, d x := rfl
  have hdle : (∑ x ∈ d.support, d x) ≤ N :=
    hsum_eq ▸ le_trans (MvPolynomial.le_totalDegree hd) hQ
  have hDne : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [show (D : ℚ) ^ N = (D : ℚ) ^ (N - ∑ x ∈ d.support, d x) * (D : ℚ) ^ ∑ x ∈ d.support, d x by
    rw [← pow_add]; congr 1; omega]
  have hprodne : (D : ℚ) ^ (∑ x ∈ d.support, d x) ≠ 0 := pow_ne_zero _ hDne
  field_simp
  simp only [Int.coe_castRingHom]
  ring

/-- **Theorem `thm:general-defect`, part (ii).** If `D` is a common positive denominator of
`u_1,...,u_{n+k}` (i.e. `u_j = z_j/D` for integers `z_j`), then `D^{n+k}(a_{n+k}-a_na_k) ∈ kℤ`,
even when the coordinates themselves aren't integral. -/
theorem general_defect_denom_clear (F : ℚ⟦X⟧) (hF1 : constantCoeff F = 1)
    (n k : ℕ) (hk : 1 ≤ k) (D : ℕ) (hD : 0 < D) (z : ℕ → ℤ)
    (hz : ∀ m, canonicalCoord m F = (z m : ℚ) / (D : ℚ)) :
    ∃ w : ℤ, (D : ℚ) ^ (n + k) * (egfCoeff F (n + k) - egfCoeff F n * egfCoeff F k) =
      (k : ℚ) * (w : ℚ) := by
  obtain ⟨w, hw⟩ :=
    evalAt_totalDegree_denom_clear (Qpoly n k hk) (n + k) (totalDegree_Qpoly_le n k hk) z D hD
  refine ⟨w, ?_⟩
  rw [general_defect_main F hF1 n k hk,
    show (fun j => canonicalCoord j F) = (fun j => (z j : ℚ) / (D : ℚ)) from funext hz]
  linear_combination -(k : ℚ) * hw

end CongruenceTheory
