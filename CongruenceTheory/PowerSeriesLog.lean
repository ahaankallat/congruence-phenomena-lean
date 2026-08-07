import Mathlib

/-!
**`log(AB) = log A + log B`** for formal power series `A, B` with constant term `1`, over a
`ℚ`-algebra. This is genuinely missing from Mathlib's `PowerSeries.Log` (checked: that file
defines `log(1+X)` and `logOf`, with `logOf_one_add_X`, but no multiplicativity law), and is
needed for `thm:multiplicative-functoriality` and the manuscript's canonical-coordinates
chapter (`sec:principle`), which both rest on the classification
`(1+x\Q[[x]], \cdot) \cong (\Q^{\N}, +)` via `\log/\exp`.

**Proof strategy** (the classical one, via differentiation): the log-derivative
`D(\log A)/A` is additive under products because `D` is a derivation (Leibniz) and `D(\log A) =
A^{-1} \cdot D(A)`; two power series with equal derivative and equal (here: zero) constant term
are equal, since `n+1` is invertible in every `ℚ`-algebra.
-/

namespace CongruenceTheory

open PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Two power series over a `ℚ`-algebra with the same derivative and the same constant term
are equal. The key fact making this work in every `ℚ`-algebra (not just fields of
characteristic `0`): `n+1` is always invertible via `algebraMap ℚ A`. -/
theorem deriv_injective_of_const (f g : A⟦X⟧) (hderiv : d⁄dX A f = d⁄dX A g)
    (hconst : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  cases n with
  | zero => simpa using hconst
  | succ n =>
    have h := congrArg (coeff n) hderiv
    rw [coeff_derivative, coeff_derivative] at h
    have hcast : ((n : A) + 1) = algebraMap ℚ A ((n : ℚ) + 1) := by simp
    have hq : ((n : ℚ) + 1) ≠ 0 := by positivity
    have hinv : algebraMap ℚ A ((n : ℚ) + 1) * algebraMap ℚ A ((n : ℚ) + 1)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hq, map_one]
    have h2 := congrArg (· * algebraMap ℚ A ((n : ℚ) + 1)⁻¹) h
    simp only [hcast, mul_assoc, hinv, mul_one] at h2
    exact h2

omit [Algebra ℚ A] in
lemma coeff_one_add_X (i : ℕ) :
    coeff i (1 + X : A⟦X⟧) = if i = 0 then 1 else if i = 1 then 1 else 0 := by
  rw [map_add]
  rcases i with _ | _ | i
  · simp
  · simp
  · simp [coeff_X]

/-- The geometric series `∑(-1)ⁿXⁿ` is the inverse of `1+X`. -/
theorem geom_inv : (1 + X : A⟦X⟧) * (mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)) = 1 := by
  ext n
  rw [coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (1 + X : A⟦X⟧) * coeff j (mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)))]
  rcases n with _ | n
  · simp [coeff_one_add_X, coeff_one]
  · rw [show ∑ x ∈ Finset.range (n + 1 + 1), coeff x (1 + X : A⟦X⟧) *
          coeff (n + 1 - x) (mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)) =
        ∑ x ∈ ({0, 1} : Finset ℕ), coeff x (1 + X : A⟦X⟧) *
          coeff (n + 1 - x) (mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)) from by
      symm
      apply Finset.sum_subset
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_range]; omega
      · intro x hx hxnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
        rw [coeff_one_add_X, if_neg hxnot.1, if_neg hxnot.2]
        ring]
    rw [Finset.sum_pair (show (0 : ℕ) ≠ 1 by omega)]
    rw [coeff_one_add_X, coeff_one_add_X]
    simp only [reduceIte]
    rw [coeff_mk, coeff_mk]
    rw [show (n + 1 - 0 = n + 1) from by omega, show (n + 1 - 1 = n) from by omega]
    rw [coeff_one, if_neg (Nat.succ_ne_zero n)]
    have hsum : ((-1 : ℚ)) ^ (n + 1) + (-1 : ℚ) ^ n = 0 := by ring
    have hz : algebraMap ℚ A (((-1 : ℚ)) ^ (n + 1)) + algebraMap ℚ A ((-1 : ℚ) ^ n) = 0 := by
      rw [← map_add, hsum, map_zero]
    simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ite_self]
    linear_combination hz

theorem hasSubst_sub_one {f : A⟦X⟧} (hf : constantCoeff f = 1) : HasSubst (f - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [hf])

/-- The formal inverse of `f` (for `f` with constant term `1`), built by substituting `f-1`
into the geometric series. -/
noncomputable def geomSubst (f : A⟦X⟧) (hf : constantCoeff f = 1) : A⟦X⟧ :=
  (mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)).subst (f - 1)

theorem subst_one_eq {a : A⟦X⟧} (ha : HasSubst a) : (1 : A⟦X⟧).subst a = 1 := by
  rw [← coe_substAlgHom ha, map_one]

theorem f_mul_geomSubst (f : A⟦X⟧) (hf : constantCoeff f = 1) : f * geomSubst f hf = 1 := by
  have hsub := hasSubst_sub_one hf
  have heq : ((1 + X : A⟦X⟧) * (mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n))).subst (f - 1) =
      (1 : A⟦X⟧).subst (f - 1) := by rw [geom_inv]
  rw [subst_mul hsub, subst_add hsub, subst_one_eq hsub, subst_X hsub] at heq
  simp only [geomSubst]
  rw [show (1 : A⟦X⟧) + (f - 1) = f from by ring] at heq
  exact heq

/-- **The log-derivative rule**: `D(logOf f) · f = D(f)`, for `f` with constant term `1`. -/
theorem deriv_logOf_mul_self (f : A⟦X⟧) (hf : constantCoeff f = 1) :
    d⁄dX A (logOf f) * f = d⁄dX A f := by
  have hsub := hasSubst_sub_one hf
  rw [logOf_eq, derivative_subst A hsub]
  have hd : d⁄dX A (f - 1) = d⁄dX A f := by
    rw [Derivation.map_sub (d⁄dX A) f 1, Derivation.map_one_eq_zero (d⁄dX A), sub_zero]
  rw [hd, deriv_log]
  rw [show ((mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)).subst (f - 1)) = geomSubst f hf from rfl]
  rw [mul_assoc]
  calc geomSubst f hf * (d⁄dX A f * f) = (geomSubst f hf * f) * d⁄dX A f := by ring
    _ = (f * geomSubst f hf) * d⁄dX A f := by ring
    _ = d⁄dX A f := by rw [f_mul_geomSubst f hf]; ring

/-- **`log(AB) = log A + log B`**, for `A, B` with constant term `1` — genuinely missing from
Mathlib's `PowerSeries.Log`. -/
theorem logOf_mul (f g : A⟦X⟧) (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := by
  have hfg : constantCoeff (f * g) = 1 := by rw [map_mul, hf, hg, mul_one]
  apply deriv_injective_of_const
  · have h1 := deriv_logOf_mul_self (f * g) hfg
    have h2 := deriv_logOf_mul_self f hf
    have h3 := deriv_logOf_mul_self g hg
    have hleib0 := Derivation.leibniz (d⁄dX A) f g
    rw [smul_eq_mul, smul_eq_mul] at hleib0
    have hunit : IsUnit (f * g) := isUnit_iff_constantCoeff.mpr (by rw [hfg]; exact isUnit_one)
    apply hunit.mul_right_cancel
    rw [map_add, add_mul]
    linear_combination h1 - g * h2 - f * h3 + hleib0
  · rw [map_add, constantCoeff_logOf hfg, constantCoeff_logOf hf, constantCoeff_logOf hg, add_zero]

/-- **`thm:multiplicative-functoriality`, main clause**: the canonical logarithmic
coordinate `u_m(A) = m·[x^m]\log A` is additive under products, `u_m(AB) = u_m(A) + u_m(B)`
— an immediate corollary of `logOf_mul` (`def:canonical-coordinates`,
`thm:multiplicative-functoriality`). -/
noncomputable def canonicalCoord (m : ℕ) (f : A⟦X⟧) : A := (m : A) * coeff m (logOf f)

theorem canonicalCoord_mul (m : ℕ) (f g : A⟦X⟧) (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) :
    canonicalCoord m (f * g) = canonicalCoord m f + canonicalCoord m g := by
  simp only [canonicalCoord, logOf_mul f g hf hg, map_add]
  ring

/-- Substituting a zero-constant-term series doesn't change the constant term. -/
theorem constantCoeff_subst_of_const_zero (f g : A⟦X⟧) (hg : constantCoeff g = 0)
    (hsub : HasSubst g) : constantCoeff (f.subst g) = constantCoeff f := by
  show MvPowerSeries.constantCoeff (subst g f) = constantCoeff f
  rw [constantCoeff_subst hsub f]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    have hz : MvPowerSeries.constantCoeff (g ^ d) = 0 := by
      show constantCoeff (g ^ d) = 0
      rw [map_pow, hg]
      exact zero_pow hd
    rw [hz, smul_zero]

/-- **`log(exp g) = g`**, for `g` with zero constant term — the other half of the classical
`log/exp` inverse pair, completing (together with `logOf_mul`) enough of the
`thm:canonical-classification`/`thm:classification` machinery to identify `exp` as injective
on the zero-constant-term locus. Same technique as `logOf_mul`: `exp` is its own derivative
(`derivative_exp`), so the chain rule gives `D(exp∘g) = (exp∘g)·D(g)`; combined with the
log-derivative rule and cancelling the unit `exp∘g`, `D(log(exp∘g)) = D(g)`; both sides have
constant term `0`, so they're equal. -/
theorem logOf_exp (g : A⟦X⟧) (hg : constantCoeff g = 0) : logOf ((exp A).subst g) = g := by
  have hsub := HasSubst.of_constantCoeff_zero' hg
  have hexp1 : constantCoeff ((exp A).subst g) = 1 := by
    rw [constantCoeff_subst_of_const_zero (exp A) g hg hsub, constantCoeff_exp]
  apply deriv_injective_of_const
  · have h1 := deriv_logOf_mul_self ((exp A).subst g) hexp1
    have hchain : d⁄dX A ((exp A).subst g) = (exp A).subst g * d⁄dX A g := by
      rw [derivative_subst A hsub, derivative_exp]
    have hunit : IsUnit ((exp A).subst g) :=
      isUnit_iff_constantCoeff.mpr (by rw [hexp1]; exact isUnit_one)
    apply hunit.mul_right_cancel
    rw [hchain] at h1
    linear_combination h1
  · rw [constantCoeff_logOf hexp1, hg]

theorem constantCoeff_geomSubst (f : A⟦X⟧) (hf : constantCoeff f = 1) :
    constantCoeff (geomSubst f hf) = 1 := by
  have h := f_mul_geomSubst f hf
  have hc := congrArg constantCoeff h
  rw [map_mul, hf, map_one, one_mul] at hc
  exact hc

theorem ginv_mul_f (f : A⟦X⟧) (hf : constantCoeff f = 1) : geomSubst f hf * f = 1 := by
  rw [mul_comm]; exact f_mul_geomSubst f hf

/-- The derivative of the formal inverse, via differentiating `f · f⁻¹ = 1`. -/
theorem deriv_ginv_mul (f : A⟦X⟧) (hf : constantCoeff f = 1) :
    d⁄dX A (geomSubst f hf) * f = -(d⁄dX A f * geomSubst f hf) := by
  have hprod := f_mul_geomSubst f hf
  have hd := congrArg (d⁄dX A) hprod
  have hleib := Derivation.leibniz (d⁄dX A) f (geomSubst f hf)
  rw [smul_eq_mul, smul_eq_mul] at hleib
  rw [hleib, Derivation.map_one_eq_zero (d⁄dX A)] at hd
  linear_combination hd

/-- **`exp(log f) = f`**, for `f` with constant term `1` — completing, together with
`logOf_exp`, the full classical `log/exp` bijection between `1 + x A[[x]]` (constant term `1`)
and `x A[[x]]` (constant term `0`). Same log-derivative machinery, plus one extra step:
`k := exp(log f) · f⁻¹` has zero derivative and constant term `1` (via the quotient/product
rule and the derivative of the formal inverse `deriv_ginv_mul`), so `k = 1` by
`deriv_injective_of_const`, and cancelling the unit `f⁻¹` gives `exp(log f) = f`. -/
theorem exp_logOf (f : A⟦X⟧) (hf : constantCoeff f = 1) : (exp A).subst (logOf f) = f := by
  have hlogsub : HasSubst (logOf f) := HasSubst.of_constantCoeff_zero' (constantCoeff_logOf hf)
  set h := (exp A).subst (logOf f) with hh_def
  set ginv := geomSubst f hf with hginv_def
  have hh1 : constantCoeff h = 1 := by
    rw [hh_def, constantCoeff_subst_of_const_zero (exp A) (logOf f) (constantCoeff_logOf hf)
      hlogsub, constantCoeff_exp]
  have hDh : d⁄dX A h = h * d⁄dX A (logOf f) := by
    rw [hh_def, derivative_subst A hlogsub, derivative_exp]
  have hDlogf := deriv_logOf_mul_self f hf
  have hfginv : f * ginv = 1 := by rw [hginv_def]; exact f_mul_geomSubst f hf
  have hDginv := deriv_ginv_mul f hf
  have key : d⁄dX A (logOf f) = d⁄dX A f * ginv := by
    linear_combination ginv * hDlogf - d⁄dX A (logOf f) * hfginv
  set k := h * ginv with hk_def
  have hDk : d⁄dX A k = 0 := by
    have hleib := Derivation.leibniz (d⁄dX A) h ginv
    rw [smul_eq_mul, smul_eq_mul] at hleib
    rw [hk_def, hleib]
    linear_combination h * (ginv * hDginv - d⁄dX A (geomSubst f hf) * hfginv) +
      ginv * hDh + h * ginv * key
  have hk1 : constantCoeff k = 1 := by
    rw [hk_def, map_mul, hh1, one_mul]
    have hc := congrArg constantCoeff hfginv
    rw [map_mul, hf, one_mul] at hc
    exact hc
  have hkeq1 : k = 1 := deriv_injective_of_const k 1 (by rw [hDk]; simp) (by rw [hk1]; simp)
  have heq : h * ginv = f * ginv := by rw [← hk_def, hkeq1, ← hfginv]
  have hunit_ginv : IsUnit ginv := isUnit_iff_constantCoeff.mpr (by
    rw [hginv_def, constantCoeff_geomSubst f hf]; exact isUnit_one)
  exact hunit_ginv.mul_left_cancel (by rw [mul_comm ginv h, mul_comm ginv f]; exact heq)

theorem logOf_one : logOf (1 : A⟦X⟧) = 0 := by
  have hc1 : constantCoeff (1 : A⟦X⟧) = 1 := by simp
  have hd : d⁄dX A (logOf (1 : A⟦X⟧)) = d⁄dX A (0 : A⟦X⟧) := by
    have hh := deriv_logOf_mul_self (1 : A⟦X⟧) hc1
    simpa using hh
  exact deriv_injective_of_const _ _ (by rw [hd]) (by rw [constantCoeff_logOf hc1]; simp)

/-- **`thm:multiplicative-functoriality`, second clause**: `u_m(A^{-1}) = -u_m(A)`. -/
theorem logOf_inv (f : A⟦X⟧) (hf : constantCoeff f = 1) :
    logOf (geomSubst f hf) = -logOf f := by
  have h := logOf_mul f (geomSubst f hf) hf (constantCoeff_geomSubst f hf)
  rw [f_mul_geomSubst f hf, logOf_one] at h
  linear_combination -h

theorem canonicalCoord_inv (m : ℕ) (f : A⟦X⟧) (hf : constantCoeff f = 1) :
    canonicalCoord m (geomSubst f hf) = -canonicalCoord m f := by
  simp only [canonicalCoord, logOf_inv f hf, map_neg]
  ring

/-- **`thm:multiplicative-functoriality`, third clause**: `u_m(A^q) = q\,u_m(A)` for `q ∈ ℕ`. -/
theorem logOf_pow (f : A⟦X⟧) (hf : constantCoeff f = 1) (n : ℕ) :
    logOf (f ^ n) = (n : A⟦X⟧) * logOf f := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; exact logOf_one
  | succ n ih =>
    have hfn1 : constantCoeff (f ^ n) = 1 := by rw [map_pow, hf, one_pow]
    have hstep : logOf (f ^ (n + 1)) = logOf (f ^ n) + logOf f := by
      rw [pow_succ, logOf_mul (f ^ n) f hfn1 hf]
    rw [hstep, ih]
    push_cast
    ring

theorem canonicalCoord_pow (m : ℕ) (f : A⟦X⟧) (hf : constantCoeff f = 1) (n : ℕ) :
    canonicalCoord m (f ^ n) = (n : A) * canonicalCoord m f := by
  have hcoeff : coeff m ((n : A⟦X⟧) * logOf f) = (n : A) * coeff m (logOf f) := by
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  simp only [canonicalCoord, logOf_pow f hf n, hcoeff]
  ring

end CongruenceTheory
