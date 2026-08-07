import Mathlib
import CongruenceTheory.EulerProductTheorem

/-!
**Theorem `thm:euler-integrality`**, in full: the equivalence of (i) `A_w(x) ∈ 1+xℤ[[x]]`,
(ii) `b_n ∈ ℤ` for every `n≥1`, (iii) `∑_{d∣n}μ(n/d)w_d ≡ 0 (mod n)`.

**Clause (ii)⟺(iii)** (`euler_integrality_ii_iff_iii`): immediate from `b`'s own definition
(`b n = MTrans w n / n`), so `b n` is an integer exactly when `n ∣ MTrans w n`, which is
`thm:gauss`'s own condition (iii) (`GaussCongruence.lean`).

**Clause (ii)⟹(i)** (`euler_integrality_ii_imp_i`): `rpow_natCast`/`rpow_neg_natCast` show
`rpow F t` (the general power operation from `EulerProduct.lean`) agrees with the *ordinary*
ring operations for integer exponents. `EF n`, the integer-coefficient formal inverse of
`1-x^{n+1}` in `ℤ⟦X⟧`, is built directly via Mathlib's `PowerSeries.invOfUnit`;
`map_EF_eq_geomSubst`/`geomSubst_pow` connect it back to `ℚ⟦X⟧`'s `geomSubst` by uniqueness of
inverses. `Efactor n k : ℤ⟦X⟧` (`map_Efactor`) and `coeff_finiteProd_int` transport integrality
through the Euler factors and a finite product; combined with `euler_product` and
`coeff_tprod_eq_coeff_prod_range` (`EulerProduct.lean`), every coefficient of `AwSeries w` is
an integer.

**Clause (i)⟹(ii)** (`euler_integrality_i_imp_ii`): the manuscript's own inductive truncation
argument. `coeff_rpow_one_sub_X_pow_le`: the exact coefficients of `rpow(1-x^N)(-t)` up to
degree `N` (`1` at `0`, `t` at `N`, `0` elsewhere) — proved via the same `coeff_subst'`
finite-support technique as `coeff_logOf_one_sub_X_pow`, using that terms of degree `≥2` in the
`exp` series vanish (order `≥2N>N`, via `PowerSeries.le_order_pow`).
`coeff_AwSeries_eq_coeff_prod_range`: coefficient `N` of `A_w` only depends on the first `N`
Euler factors (a tight instance of `coeff_tprod_eq_coeff_prod_range`, using
`le_order_eulerFactor_sub_one`'s *unconditional* per-factor order bound — no existential search
needed). `prod_range_split_top` splits off the top factor (exponent `N`). `head_prod_int`:
given the exponents `1..M` are already known integral, the corresponding finite product of
Euler factors is an integer-coefficient series with constant term `1`. `coeff_N_step` combines
all of this via the convolution formula for `coeff N` of a product, using
`coeff_rpow_one_sub_X_pow_le` to isolate exactly the two nonzero terms (`i=0` and `i=N`) in the
sum: `coeff N (A_w) = coeff N (head) + b_N`. Finally, `euler_integrality_i_imp_ii` assembles
this into a strong induction on `N`: given `b_1,...,b_{N-1}` integral (IH) and `coeff N (A_w)`
integral (hypothesis (i)), `b_N = coeff N (A_w) - coeff N (head)` is a difference of integers.
-/

namespace CongruenceTheory

open PowerSeries Finset

theorem b_int_iff_dvd (w : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    (∃ z : ℤ, b w n = z) ↔ (n : ℤ) ∣ MTrans w n := by
  unfold b
  constructor
  · rintro ⟨z, hz⟩
    have : (MTrans w n : ℚ) = z * n := by
      rw [← hz]
      field_simp
    have hz2 : (MTrans w n : ℤ) = z * n := by exact_mod_cast this
    exact ⟨z, by rw [hz2, mul_comm]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc]
    push_cast
    field_simp

/-- **`thm:euler-integrality`, (ii)⟺(iii)**: `b_n ∈ ℤ` for all `n≥1` iff the Gauss-style
divisibility condition `n ∣ M_n` holds for all `n≥1`. Immediate from `b`'s own definition. -/
theorem euler_integrality_ii_iff_iii (w : ℕ → ℤ) :
    (∀ n ≥ 1, ∃ z : ℤ, b w n = z) ↔ (∀ n : ℕ, 0 < n → (n : ℤ) ∣ MTrans w n) := by
  constructor
  · intro h n hn
    exact (b_int_iff_dvd w n hn).mp (h n hn)
  · intro h n hn
    exact (b_int_iff_dvd w n hn).mpr (h n hn)

/-- `rpow F n = F^n` for a natural-number exponent: `rpow`'s transcendental (`exp/log`)
construction agrees with the ordinary ring power. -/
theorem rpow_natCast (F : ℚ⟦X⟧) (hF : constantCoeff F = 1) (n : ℕ) :
    rpow F (n : ℚ) = F ^ n := by
  have h1 : logOf (rpow F (n : ℚ)) = logOf (F ^ n) := by
    rw [logOf_rpow F hF, logOf_pow F hF n]
    congr 1
  have h2 : constantCoeff (rpow F (n : ℚ)) = 1 := constantCoeff_rpow F hF n
  have h3 : constantCoeff (F ^ n) = 1 := by rw [map_pow, hF, one_pow]
  have := exp_logOf (rpow F (n : ℚ)) h2
  rw [h1] at this
  rw [← this, exp_logOf _ h3]

/-- `rpow F (-n) = geomSubst(F^n)` for a natural-number `n`: agrees with the ordinary formal
inverse `(F^n)⁻¹`. -/
theorem rpow_neg_natCast (F : ℚ⟦X⟧) (hF : constantCoeff F = 1) (n : ℕ) :
    rpow F (-(n : ℚ)) = geomSubst (F ^ n) (by rw [map_pow, hF, one_pow]) := by
  have hFn : constantCoeff (F ^ n) = 1 := by rw [map_pow, hF, one_pow]
  have h1 : logOf (rpow F (-(n : ℚ))) = logOf (geomSubst (F ^ n) hFn) := by
    rw [logOf_rpow F hF, logOf_inv (F ^ n) hFn, logOf_pow F hF n]
    rw [show (PowerSeries.C (-(n : ℚ)) : ℚ⟦X⟧) = -(n : ℚ⟦X⟧) from by
      rw [map_neg, map_natCast]]
    ring
  have h2 : constantCoeff (rpow F (-(n : ℚ))) = 1 := constantCoeff_rpow F hF _
  have h3 : constantCoeff (geomSubst (F ^ n) hFn) = 1 := constantCoeff_geomSubst (F ^ n) hFn
  have := exp_logOf (rpow F (-(n : ℚ))) h2
  rw [h1] at this
  rw [← this, exp_logOf _ h3]

/-- The integer-coefficient formal inverse of `1-x^{n+1}` in `ℤ⟦X⟧`: well-defined since
`1-x^{n+1}` has constant term `1`, a unit in `ℤ`. -/
noncomputable def EF (n : ℕ) : ℤ⟦X⟧ := PowerSeries.invOfUnit (1 - X ^ (n + 1) : ℤ⟦X⟧) (1 : ℤˣ)

theorem EF_spec (n : ℕ) : (1 - X ^ (n + 1) : ℤ⟦X⟧) * EF n = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp

/-- Casting `EF n` to `ℚ⟦X⟧` gives exactly `geomSubst` — by uniqueness of inverses. -/
theorem map_EF_eq_geomSubst (n : ℕ) :
    (EF n).map (Int.castRingHom ℚ) = geomSubst (1 - X ^ (n + 1) : ℚ⟦X⟧) (by simp) := by
  have h1 : (1 - X ^ (n + 1) : ℚ⟦X⟧) * (EF n).map (Int.castRingHom ℚ) = 1 := by
    have := congrArg (PowerSeries.map (Int.castRingHom ℚ)) (EF_spec n)
    simp only [map_mul, map_sub, map_one, map_pow, PowerSeries.map_X] at this
    convert this using 2
  have h2 : (1 - X ^ (n + 1) : ℚ⟦X⟧) * geomSubst (1 - X ^ (n + 1) : ℚ⟦X⟧) (by simp) = 1 :=
    f_mul_geomSubst _ _
  have hunit : IsUnit (1 - X ^ (n + 1) : ℚ⟦X⟧) := isUnit_iff_constantCoeff.mpr (by simp)
  exact hunit.mul_left_cancel (h1.trans h2.symm)

/-- `(f⁻¹)^m = (f^m)⁻¹`, in the `geomSubst` formulation — by uniqueness of inverses. -/
theorem geomSubst_pow (F : ℚ⟦X⟧) (hF : constantCoeff F = 1) (m : ℕ) :
    (geomSubst F hF) ^ m = geomSubst (F ^ m) (by rw [map_pow, hF, one_pow]) := by
  have hFm : constantCoeff (F ^ m) = 1 := by rw [map_pow, hF, one_pow]
  have h1 : F ^ m * (geomSubst F hF) ^ m = 1 := by
    rw [← mul_pow, f_mul_geomSubst F hF, one_pow]
  have h2 : F ^ m * geomSubst (F ^ m) hFm = 1 := f_mul_geomSubst _ _
  have hunit : IsUnit (F ^ m) := isUnit_iff_constantCoeff.mpr (by rw [hFm]; exact isUnit_one)
  exact hunit.mul_left_cancel (h1.trans h2.symm)

/-- The integer power/inverse-power of `1-x^{n+1}` in `ℤ⟦X⟧`, matching sign of `k : ℤ`. -/
noncomputable def Efactor (n : ℕ) (k : ℤ) : ℤ⟦X⟧ :=
  if 0 ≤ k then (1 - X ^ (n + 1) : ℤ⟦X⟧) ^ k.toNat else (EF n) ^ (-k).toNat

/-- `Efactor n k` casts exactly to the `ℚ⟦X⟧` Euler factor `rpow(1-x^{n+1})(k)`. -/
theorem map_Efactor (n : ℕ) (k : ℤ) :
    (Efactor n k).map (Int.castRingHom ℚ) = rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (k : ℚ) := by
  unfold Efactor
  by_cases hk : 0 ≤ k
  · rw [if_pos hk]
    have hcast : (k.toNat : ℚ) = (k : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hk
    rw [map_pow]
    have hmap1 : (1 - X ^ (n + 1) : ℤ⟦X⟧).map (Int.castRingHom ℚ) = (1 - X ^ (n + 1) : ℚ⟦X⟧) := by
      simp
    rw [hmap1, ← hcast]
    exact (rpow_natCast (1 - X ^ (n + 1) : ℚ⟦X⟧) (by simp) k.toNat).symm
  · rw [if_neg hk]
    push Not at hk
    have hcast : ((-k).toNat : ℚ) = -(k : ℚ) := by
      have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ -k by omega)
      exact_mod_cast this
    have hcast2 : (k : ℚ) = -(((-k).toNat : ℕ) : ℚ) := by rw [hcast]; ring
    rw [map_pow, map_EF_eq_geomSubst, hcast2,
      rpow_neg_natCast (1 - X ^ (n + 1) : ℚ⟦X⟧) (by simp) (-k).toNat,
      geomSubst_pow (1 - X ^ (n + 1) : ℚ⟦X⟧) (by simp) (-k).toNat]

theorem coeff_finiteProd_int (w : ℕ → ℤ) (z : ℕ → ℤ) (hz : ∀ n, b w n = (z n : ℚ))
    (N : ℕ) (e : ℕ) :
    ∃ m : ℤ,
      coeff e (∏ n ∈ Finset.range N, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) = (m : ℚ) := by
  have heq : ∏ n ∈ Finset.range N, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) =
      (∏ n ∈ Finset.range N, Efactor n (-(z (n + 1)))).map (Int.castRingHom ℚ) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro n _
    rw [map_Efactor]
    congr 1
    rw [hz]
    push_cast
    ring
  rw [heq, coeff_map]
  exact ⟨coeff e (∏ n ∈ Finset.range N, Efactor n (-(z (n + 1)))), rfl⟩

open scoped PowerSeries.WithPiTopology in
/-- **`thm:euler-integrality`, (ii)⟹(i)**: if every Euler coordinate `b_n` is an integer, then
`A_w(x) ∈ 1+xℤ[[x]]`, i.e. every coefficient of `AwSeries w` is (the cast of) an integer. -/
theorem euler_integrality_ii_imp_i (w : ℕ → ℤ) (z : ℕ → ℤ) (hz : ∀ n, b w n = (z n : ℚ)) (e : ℕ) :
    ∃ m : ℤ, coeff e (AwSeries w) = (m : ℚ) := by
  rw [euler_product w]
  obtain ⟨N, hN⟩ := (horder_eulerFactors w) e
  have hM : Multipliable (fun n : ℕ => 1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1)) := by
    have heq : (fun n : ℕ => rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) =
        (fun n : ℕ => 1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1)) := by
      funext n; ring
    rw [← heq]; exact multipliable_eulerFactors (b w)
  have hcoeff : coeff e (∏' n, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) =
      coeff e (∏ n ∈ Finset.range N, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) := by
    have heq : (fun n : ℕ => rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) =
        (fun n : ℕ => 1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1)) := by
      funext n; ring
    rw [heq]
    exact coeff_tprod_eq_coeff_prod_range _ hM e N hN
  rw [hcoeff]
  exact coeff_finiteProd_int w z hz N e

open scoped PowerSeries.WithPiTopology in
/-- The coefficient-`N` truncation of `A_w`: coefficient `N` of `A_w` only depends on `rpow`
factors up to `n < N` — a tight instance of `coeff_tprod_eq_coeff_prod_range`, using that
`le_order_eulerFactor_sub_one` gives an *unconditional* per-factor order bound (no existential
search for a large-enough truncation is needed, unlike `coeff_finiteProd_int`'s callers). -/
theorem coeff_AwSeries_eq_coeff_prod_range (w : ℕ → ℤ) (N : ℕ) :
    coeff N (AwSeries w) =
      coeff N (∏ n ∈ Finset.range N, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) := by
  rw [euler_product w]
  have heq : (fun n : ℕ => rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) =
      (fun n : ℕ => 1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1)) := by funext n; ring
  have hM : Multipliable (fun n : ℕ => 1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1)) := by
    rw [← heq]; exact multipliable_eulerFactors (b w)
  rw [heq]
  apply coeff_tprod_eq_coeff_prod_range _ hM N N
  intro n hn
  have h1 : (N : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : N < n + 1)
  exact lt_of_lt_of_le h1 (le_order_eulerFactor_sub_one n (b w (n + 1)))

/-- Splitting off the top factor (exponent `N`) of the range-`N` product. -/
theorem prod_range_split_top (w : ℕ → ℤ) (N : ℕ) (hN : 1 ≤ N) :
    ∏ n ∈ Finset.range N, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) =
      (∏ n ∈ Finset.range (N - 1), rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) *
        rpow (1 - X ^ N : ℚ⟦X⟧) (-(b w N)) := by
  have hsplit : Finset.range N = insert (N - 1) (Finset.range (N - 1)) := by
    conv_lhs => rw [show N = (N - 1) + 1 from by omega]
    rw [Finset.range_add_one]
  rw [hsplit, Finset.prod_insert (by simp)]
  rw [show N - 1 + 1 = N from by omega]
  ring

/-- The head product (exponents `1..M`) is an integer cast with constant term `1`, given the
exponents `1..M` are already known integral. -/
theorem head_prod_int (w : ℕ → ℤ) (z : ℕ → ℤ) (M : ℕ)
    (hz : ∀ n ∈ Finset.range M, b w (n + 1) = (z (n + 1) : ℚ)) :
    ∃ H : ℤ⟦X⟧, (∏ n ∈ Finset.range M, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) =
      H.map (Int.castRingHom ℚ) ∧ constantCoeff H = 1 := by
  refine ⟨∏ n ∈ Finset.range M, Efactor n (-(z (n + 1))), ?_, ?_⟩
  · rw [map_prod]
    apply Finset.prod_congr rfl
    intro n hn
    rw [map_Efactor]
    congr 1
    rw [hz n hn]
    push_cast
    ring
  · rw [map_prod]
    apply Finset.prod_eq_one
    intro n _
    unfold Efactor
    split_ifs with hk
    · rw [map_pow]; simp
    · rw [map_pow]
      have hconst1 : constantCoeff (EF n) = 1 := by
        have h1 := EF_spec n
        have h2 := congrArg constantCoeff h1
        rw [map_mul, map_one] at h2
        have h3 : constantCoeff (1 - X ^ (n + 1) : ℤ⟦X⟧) = 1 := by simp
        rw [h3, one_mul] at h2
        exact h2
      rw [hconst1]; simp

/-- **Exact coefficients of `rpow(1-x^N)(-t)` up to degree `N`**: `1` at `e=0`, `t` at `e=N`,
`0` otherwise. Proved directly from `coeff_subst'`, restricted to `{0,1}` since the `exp`
series' degree-`≥2` terms have order `≥2N>N` (via `PowerSeries.le_order_pow`), matching the
technique used for `coeff_logOf_one_sub_X_pow`. -/
theorem coeff_rpow_one_sub_X_pow_le (N e : ℕ) (hN : N ≠ 0) (he : e ≤ N) (t : ℚ) :
    coeff e (rpow (1 - X ^ N : ℚ⟦X⟧) (-t)) = if e = 0 then 1 else if e = N then t else 0 := by
  unfold rpow
  set h : ℚ⟦X⟧ := PowerSeries.C (-t) * logOf (1 - X ^ N : ℚ⟦X⟧) with hdef
  have horder : (N : ℕ∞) ≤ h.order := by
    rw [hdef]
    calc (N : ℕ∞) ≤ (logOf (1 - X ^ N : ℚ⟦X⟧)).order := by
          have := le_order_logOf_one_sub_X_pow (N - 1)
          rwa [show N - 1 + 1 = N from by omega] at this
      _ = (0 : ℕ∞) + (logOf (1 - X ^ N : ℚ⟦X⟧)).order := by rw [zero_add]
      _ ≤ (PowerSeries.C (-t) : ℚ⟦X⟧).order + (logOf (1 - X ^ N : ℚ⟦X⟧)).order := by
          gcongr; exact zero_le
      _ ≤ _ := PowerSeries.le_order_mul _ _
  have hsubst : HasSubst h := HasSubst.of_constantCoeff_zero' (by
    have := PowerSeries.coeff_of_lt_order (φ := h) 0 (by
      apply lt_of_lt_of_le _ horder
      exact_mod_cast Nat.pos_of_ne_zero hN)
    rwa [coeff_zero_eq_constantCoeff] at this)
  rw [coeff_subst' hsubst]
  have hzero : ∀ d, 2 ≤ d → coeff d (PowerSeries.exp ℚ) • coeff e (h ^ d) = 0 := by
    intro d hd2
    have horderpow : (2 * N : ℕ∞) ≤ (h ^ d).order := by
      calc (2 * N : ℕ∞) ≤ (d : ℕ∞) * (N : ℕ∞) := by
            have hdc : (2 : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast hd2
            calc (2 * N : ℕ∞) = (2 : ℕ∞) * (N : ℕ∞) := by push_cast; ring
              _ ≤ (d : ℕ∞) * (N : ℕ∞) := by gcongr
        _ ≤ d • h.order := by rw [nsmul_eq_mul]; gcongr
        _ ≤ (h ^ d).order := PowerSeries.le_order_pow _ _
    have hlt : (e : ℕ∞) < (h ^ d).order := by
      apply lt_of_lt_of_le _ horderpow
      have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
      have : e < 2 * N := by omega
      exact_mod_cast this
    rw [PowerSeries.coeff_of_lt_order e hlt, smul_zero]
  have hsupp : Function.support (fun d => coeff d (PowerSeries.exp ℚ) • coeff e (h ^ d)) ⊆
      (({0, 1} : Finset ℕ) : Set ℕ) := by
    intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hdmem
    push Not at hdmem
    exact hd (hzero d (by omega))
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  rw [show ({0, 1} : Finset ℕ) = insert 0 {1} from rfl, Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [pow_zero, pow_one]
  have hc0 : coeff 0 (1 : ℚ⟦X⟧) = 1 := by simp
  by_cases he0 : e = 0
  · rw [he0, if_pos rfl, hc0]
    have h2 : coeff 0 h = 0 := by
      rw [hdef, coeff_C_mul]
      have hlog := coeff_logOf_one_sub_X_pow N hN 0
      rw [dif_neg (fun hc => hc.2 rfl)] at hlog
      rw [hlog]; ring
    rw [h2]; simp
  · rw [if_neg he0]
    have hc0' : coeff e (1 : ℚ⟦X⟧) = 0 := by rw [coeff_one]; simp [he0]
    rw [hc0']
    by_cases heN : e = N
    · rw [if_pos heN]
      have h2 : coeff e h = t := by
        rw [hdef, coeff_C_mul, heN]
        have hlog := coeff_logOf_one_sub_X_pow N hN N
        rw [dif_pos ⟨dvd_refl N, hN⟩] at hlog
        rw [hlog]; field_simp
      rw [h2]; simp
    · rw [if_neg heN]
      have h2 : coeff e h = 0 := by
        rw [hdef, coeff_C_mul]
        have hdvd : ¬(N ∣ e) := by
          intro hcontra
          rcases hcontra with ⟨c, hc⟩
          have hcpos : 0 < c := by
            rcases Nat.eq_zero_or_pos c with h0 | h0
            · rw [h0, mul_zero] at hc; exact absurd hc he0
            · exact h0
          have hecases : e = N := by
            rw [hc]
            have hc1 : c = 1 := by
              rcases Nat.lt_or_ge c 2 with hlt | hge
              · omega
              · exfalso
                have : N * 2 ≤ N * c := by
                  apply Nat.mul_le_mul_left
                  omega
                omega
            rw [hc1, mul_one]
          exact heN hecases
        have hlog := coeff_logOf_one_sub_X_pow N hN e
        rw [dif_neg (fun hc => hdvd hc.1)] at hlog
        rw [hlog]; ring
      rw [h2]; simp

open scoped PowerSeries.WithPiTopology in
/-- The coefficient-`N` step formula: `coeff N (A_w) = coeff N (H) + b_N`, where `H` is the
integer head product (exponents `1..N-1`). -/
theorem coeff_N_step (w : ℕ → ℤ) (z : ℕ → ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hz : ∀ n ∈ Finset.range (N - 1), b w (n + 1) = (z (n + 1) : ℚ)) :
    ∃ H : ℤ⟦X⟧, coeff N (AwSeries w) = coeff N (H.map (Int.castRingHom ℚ)) + b w N := by
  obtain ⟨H, hHeq, hHconst⟩ := head_prod_int w z (N - 1) hz
  refine ⟨H, ?_⟩
  rw [coeff_AwSeries_eq_coeff_prod_range, prod_range_split_top w N hN, hHeq]
  rw [coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (H.map (Int.castRingHom ℚ)) * coeff j (rpow (1 - X ^ N : ℚ⟦X⟧) (-(b w N))))]
  have hterm : ∀ i ∈ Finset.range (N + 1),
      coeff i (H.map (Int.castRingHom ℚ)) * coeff (N - i) (rpow (1 - X ^ N : ℚ⟦X⟧) (-(b w N))) =
        (if i = N then coeff N (H.map (Int.castRingHom ℚ)) else 0) +
          (if i = 0 then b w N else 0) := by
    intro i hi
    have hiN : i ≤ N := by have := Finset.mem_range.mp hi; omega
    rw [coeff_rpow_one_sub_X_pow_le N (N - i) (by omega : N ≠ 0) (by omega) (b w N)]
    have hHc0 : coeff 0 (H.map (Int.castRingHom ℚ)) = 1 := by
      simp [coeff_zero_eq_constantCoeff, hHconst]
    rcases eq_or_ne i 0 with hi0 | hi0
    · have hNi : N - i ≠ 0 := by omega
      have hNiN : N - i = N := by omega
      rw [if_neg hNi, if_pos hNiN, if_neg (show i ≠ N from by omega), if_pos hi0, hi0, hHc0]
      ring
    · rcases eq_or_ne i N with hiN | hiN
      · have hNi0 : N - i = 0 := by omega
        rw [hNi0, if_pos rfl, if_pos hiN, if_neg hi0]
        rw [hiN]
        ring
      · have hNi : N - i ≠ 0 := by omega
        have hNiN : N - i ≠ N := by omega
        rw [if_neg hNi, if_neg hNiN, mul_zero, if_neg hiN, if_neg hi0]
        ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' (Finset.range (N + 1)) N (fun _ => coeff N (H.map (Int.castRingHom ℚ)))]
  rw [Finset.sum_ite_eq' (Finset.range (N + 1)) 0 (fun _ => b w N)]
  simp [Finset.mem_range]

/-- **`thm:euler-integrality`, (i)⟹(ii)**: if `A_w(x) ∈ 1+xℤ[[x]]` (every coefficient of
`AwSeries w` is an integer), then every Euler coordinate `b_n` is an integer. -/
theorem euler_integrality_i_imp_ii (w : ℕ → ℤ)
    (hi : ∀ e : ℕ, ∃ m : ℤ, coeff e (AwSeries w) = (m : ℚ)) :
    ∀ N ≥ 1, ∃ z : ℤ, b w N = z := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    intro hN1
    have hz : ∀ n, ∃ zn : ℤ, (n ≥ 1 → n < N → b w n = zn) ∧ (¬(n ≥ 1 ∧ n < N) → zn = 0) := by
      intro n
      by_cases hcase : n ≥ 1 ∧ n < N
      · obtain ⟨zn, hzn⟩ := ihN n hcase.2 hcase.1
        exact ⟨zn, fun _ _ => hzn, fun hc => absurd hcase hc⟩
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hcase, fun _ => rfl⟩
    choose zfun hzfun1 hzfun2 using hz
    have hzeq : ∀ n ∈ Finset.range (N - 1), b w (n + 1) = (zfun (n + 1) : ℚ) := by
      intro n hn
      have hn' := Finset.mem_range.mp hn
      exact hzfun1 (n + 1) (by omega) (by omega)
    obtain ⟨H, hHstep⟩ := coeff_N_step w zfun N hN1 hzeq
    obtain ⟨m, hm⟩ := hi N
    have hmH : coeff N (H.map (Int.castRingHom ℚ)) = ((coeff N H : ℤ) : ℚ) := by
      rw [coeff_map]; rfl
    set mH : ℤ := coeff N H with hmHdef
    refine ⟨m - mH, ?_⟩
    rw [hm, hmH] at hHstep
    have hbN : b w N = (m : ℚ) - (mH : ℚ) := by linarith [hHstep]
    rw [hbN]
    push_cast
    ring

end CongruenceTheory
