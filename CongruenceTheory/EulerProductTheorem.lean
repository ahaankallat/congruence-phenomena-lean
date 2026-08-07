import Mathlib
import CongruenceTheory.GaussCongruence
import CongruenceTheory.EulerProduct

/-!
**Theorem `thm:euler-product`**: `A_w(x) = ∏_{n≥1}(1-x^n)^{-b_n}` in `ℚ[[x]]`, for the Euler
coordinates `b_n = (1/n)∑_{d∣n}μ(n/d)w_d`.

Assembled entirely from already-proved infrastructure:
- `b` is defined via `GaussCongruence.lean`'s `MTrans` (the Möbius transform
  `M_N=∑_{d∣N}μ(N/d)w_d`, so `b n = M_n/n`), and **`w_eq_sum_div_mul_b`** recovers the
  manuscript's `eq:w-from-b` (`w_m=∑_{d∣m}d·b_d`) directly from `GaussCongruence.lean`'s own
  `moebius_inversion`, with no new number theory needed.
- `AwSeries w := exp(∑_{m≥1}(w_m/m)x^m)` is the EGF as an element of `ℚ⟦X⟧`, in the canonical
  logarithmic-coordinates form (`PowerSeriesLog.lean`) with coordinates `u_m = w_m`; its `logOf`
  is `∑_{m≥1}(w_m/m)x^m` by construction (`logOf_exp`).
- **`euler_product`** itself: apply `logOf_tprod` (`EulerProduct.lean`) to the Euler factors
  `g n := rpow(1-x^{n+1})(-b_{n+1})`, getting
  `logOf(∏' g) = ∑' n, C(-b_{n+1})·logOf(1-x^{n+1})`. Matching this against `logOf(AwSeries w)`
  coefficient-by-coefficient (`coeff_sum_eulerFactors`) is exactly the manuscript's own
  computation: using the exact Taylor coefficients of `logOf(1-x^N)`
  (`coeff_logOf_one_sub_X_pow`), the `e`-th coefficient of the infinite sum reduces to a
  *finite* sum over divisors of `e` (reindexed via `Finset.sum_nbij'`), which is exactly
  `w_e/e` by `w_eq_sum_div_mul_b`. Both sides then have constant term `1` and the same `logOf`,
  so they're equal by the `log`/`exp` bijection (`exp_logOf`).
-/

namespace CongruenceTheory

open PowerSeries Filter Finset

/-- Euler coordinates `b_n = M_n/n`, where `M_n` is `GaussCongruence.lean`'s Möbius transform
`∑_{d∣n}μ(n/d)w_d` — matches the manuscript's `b_n=(1/n)∑_{d∣n}μ(n/d)w_d` exactly. -/
noncomputable def b (w : ℕ → ℤ) (n : ℕ) : ℚ := (MTrans w n : ℚ) / n

/-- The manuscript's `eq:w-from-b`, `w_m=∑_{d∣m}d·b_d`: Möbius inversion of `b`'s own
definition, for free from `GaussCongruence.lean`'s `moebius_inversion`. -/
theorem w_eq_sum_div_mul_b (w : ℕ → ℤ) (m : ℕ) (hm : 0 < m) :
    (w m : ℚ) = ∑ d ∈ m.divisors, (d : ℚ) * b w d := by
  have h := moebius_inversion w m hm
  have h2 : (w m : ℚ) = ∑ d ∈ m.divisors, (MTrans w d : ℚ) := by exact_mod_cast h
  rw [h2]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by
    intro hcontra
    rw [hcontra] at hd
    simp [Nat.mem_divisors] at hd
  unfold b
  field_simp

/-- `∑_{m≥1}(w_m/m)x^m`, i.e. `logOf(A_w(x))` — the canonical-coordinates generating series
with coordinates `u_m=w_m`. -/
noncomputable def Gseries (w : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk (fun m => if m = 0 then 0 else (w m : ℚ) / m)

theorem constantCoeff_Gseries (w : ℕ → ℤ) : constantCoeff (Gseries w) = 0 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [Gseries]

/-- `A_w(x) = exp(∑_{m≥1}(w_m/m)x^m) ∈ ℚ⟦X⟧`, the EGF in canonical logarithmic coordinates
with `u_m=w_m` — matches `WeightedSpecialization.lean`'s `Aw w n` (`A_w(n)`, the exponential
coefficient sequence) via `egfCoeff_eq_cVal`, though that connection isn't spelled out here. -/
noncomputable def AwSeries (w : ℕ → ℤ) : ℚ⟦X⟧ := (exp ℚ).subst (Gseries w)

theorem logOf_AwSeries (w : ℕ → ℤ) : logOf (AwSeries w) = Gseries w :=
  logOf_exp (Gseries w) (constantCoeff_Gseries w)

theorem constantCoeff_AwSeries (w : ℕ → ℤ) : constantCoeff (AwSeries w) = 1 := by
  unfold AwSeries
  rw [constantCoeff_subst_of_const_zero (exp ℚ) (Gseries w) (constantCoeff_Gseries w)
    (HasSubst.of_constantCoeff_zero' (constantCoeff_Gseries w))]
  exact constantCoeff_exp

theorem horder_eulerFactors (w : ℕ → ℤ) :
    ∀ e : ℕ, ∃ N, ∀ n ≥ N, (e : ℕ∞) < (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1).order := by
  intro e
  refine ⟨e + 1, fun n hn => ?_⟩
  have h1 : (e : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : e < n + 1)
  exact lt_of_lt_of_le h1 (le_order_eulerFactor_sub_one n (b w (n + 1)))

theorem hg1_eulerFactors (w : ℕ → ℤ) :
    ∀ n, constantCoeff (1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1) : ℚ⟦X⟧) = 1 := by
  intro n
  have : (1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1) : ℚ⟦X⟧) =
      rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) := by ring
  rw [this]
  exact constantCoeff_rpow _ (by simp) _

open scoped PowerSeries.WithPiTopology in
theorem logOf_tprod_eulerFactors (w : ℕ → ℤ) :
    logOf (∏' n, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) =
      ∑' n, PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧) := by
  have heq : (fun n : ℕ => rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) =
      (fun n : ℕ => 1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1)) := by funext n; ring
  have hM : Multipliable (fun n : ℕ => 1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1)) := by
    rw [← heq]; exact multipliable_eulerFactors (b w)
  rw [heq, logOf_tprod _ (hg1_eulerFactors w) hM (horder_eulerFactors w)]
  apply tsum_congr
  intro n
  rw [show (1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1) : ℚ⟦X⟧) =
    rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) from by ring]
  exact logOf_rpow _ (by simp) _

open scoped PowerSeries.WithPiTopology in
/-- The `e ≥ 1` coefficient of `∑' n, -b_{n+1}·logOf(1-x^{n+1})` reduces to a finite sum over
divisors of `e` (only `n+1∣e` terms are nonzero), matching `w_e/e` via `w_eq_sum_div_mul_b`. -/
theorem coeff_sum_eulerFactors (w : ℕ → ℤ) (e : ℕ) (he : e ≠ 0) :
    coeff e (∑' n, PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)) =
      (w e : ℚ) / e := by
  have hSummable :
      Summable (fun n => PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧) :
        ℕ → ℚ⟦X⟧) := by
    apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
    rw [ENat.tendsto_nhds_top_iff_natCast_lt]
    intro k
    filter_upwards [Filter.eventually_ge_atTop k] with n hn
    have h1 : (k : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : k < n + 1)
    apply lt_of_lt_of_le h1
    calc ((n + 1 : ℕ) : ℕ∞) ≤ (logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order :=
          le_order_logOf_one_sub_X_pow n
      _ ≤ (PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order := by
          calc (logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order =
                0 + (logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order := by rw [zero_add]
            _ ≤ (PowerSeries.C (-(b w (n + 1))) : ℚ⟦X⟧).order +
                  (logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order := by gcongr; exact zero_le
            _ ≤ _ := PowerSeries.le_order_mul _ _
  have hHasSum :
      HasSum (fun n => coeff e (PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)))
        (coeff e (∑' n, PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧))) :=
    (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (R := ℚ) |>.mp hSummable.hasSum) e
  have hterm : ∀ n : ℕ,
      coeff e (PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)) =
        if (n + 1) ∣ e then b w (n + 1) * (n + 1) / e else 0 := by
    intro n
    rw [coeff_C_mul, coeff_logOf_one_sub_X_pow (n + 1) (Nat.succ_ne_zero n) e]
    by_cases hdvd : (n + 1) ∣ e
    · rw [dif_pos ⟨hdvd, he⟩, if_pos hdvd]
      have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
      have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he
      have hne1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by push_cast; exact hn1
      field_simp
      push_cast
      ring
    · rw [dif_neg (fun h => hdvd h.1), if_neg hdvd, mul_zero]
  simp_rw [hterm] at hHasSum
  have hs : ∀ n ∉ (Finset.range e), (if (n + 1) ∣ e then b w (n + 1) * (n + 1) / e else 0 : ℚ) = 0 := by
    intro n hn
    rw [if_neg]
    intro hdvd
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero he) hdvd
    simp at hn
    omega
  have hval : HasSum (fun n => if (n + 1) ∣ e then b w (n + 1) * (n + 1) / e else 0 : ℕ → ℚ)
      (∑ n ∈ Finset.range e, if (n + 1) ∣ e then b w (n + 1) * (n + 1) / e else 0) :=
    hasSum_sum_of_ne_finset_zero hs
  have hHasSum' := hHasSum.unique hval
  rw [hHasSum']
  have hreindex : ∑ n ∈ Finset.range e, (if (n + 1) ∣ e then b w (n + 1) * (n + 1) / e else 0 : ℚ) =
      ∑ d ∈ e.divisors, (b w d * d / e : ℚ) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_nbij' (fun n => n + 1) (fun d => d - 1)
    case hi =>
      intro n hn
      simp only [Finset.mem_filter] at hn
      simp only [Nat.mem_divisors]
      exact ⟨hn.2, he⟩
    case hj =>
      intro d hd
      simp only [Nat.mem_divisors] at hd
      simp only [Finset.mem_filter, Finset.mem_range]
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero he)
      have hdle : d ≤ e := Nat.le_of_dvd (Nat.pos_of_ne_zero he) hd.1
      constructor
      · omega
      · rw [Nat.sub_add_cancel hd1]; exact hd.1
    case left_neg =>
      intro n hn
      simp
    case right_neg =>
      intro d hd
      simp only [Nat.mem_divisors] at hd
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero he)
      omega
    case h =>
      intro n hn
      push_cast
      ring
  rw [hreindex]
  have hwe := w_eq_sum_div_mul_b w e (Nat.pos_of_ne_zero he)
  rw [hwe, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  ring

open scoped PowerSeries.WithPiTopology in
theorem coeff_zero_sum_eulerFactors (w : ℕ → ℤ) :
    coeff 0 (∑' n, PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)) = 0 := by
  have hSummable :
      Summable (fun n => PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧) :
        ℕ → ℚ⟦X⟧) := by
    apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
    rw [ENat.tendsto_nhds_top_iff_natCast_lt]
    intro k
    filter_upwards [Filter.eventually_ge_atTop k] with n hn
    have h1 : (k : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : k < n + 1)
    apply lt_of_lt_of_le h1
    calc ((n + 1 : ℕ) : ℕ∞) ≤ (logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order :=
          le_order_logOf_one_sub_X_pow n
      _ ≤ (PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order := by
          calc (logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order =
                0 + (logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order := by rw [zero_add]
            _ ≤ (PowerSeries.C (-(b w (n + 1))) : ℚ⟦X⟧).order +
                  (logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order := by gcongr; exact zero_le
            _ ≤ _ := PowerSeries.le_order_mul _ _
  have hHasSum :
      HasSum (fun n => coeff 0 (PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)))
        (coeff 0 (∑' n, PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧))) :=
    (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (R := ℚ) |>.mp hSummable.hasSum) 0
  have hzero :
      (fun n => coeff 0 (PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧))) =
        (fun _ => (0 : ℚ)) := by
    funext n
    rw [coeff_C_mul, coeff_logOf_one_sub_X_pow (n + 1) (Nat.succ_ne_zero n) 0]
    rw [dif_neg (fun h => h.2 rfl), mul_zero]
  rw [hzero] at hHasSum
  exact (hasSum_zero.unique hHasSum).symm

open scoped PowerSeries.WithPiTopology in
theorem logOf_AwSeries_eq_sum_eulerFactors (w : ℕ → ℤ) :
    Gseries w = ∑' n, PowerSeries.C (-(b w (n + 1))) * logOf (1 - X ^ (n + 1) : ℚ⟦X⟧) := by
  apply PowerSeries.ext
  intro e
  rcases Nat.eq_zero_or_pos e with he0 | he0
  · subst he0
    rw [coeff_zero_sum_eulerFactors]
    simp [Gseries]
  · rw [coeff_sum_eulerFactors w e he0.ne']
    simp [Gseries, he0.ne']

open scoped PowerSeries.WithPiTopology in
/-- **Theorem `thm:euler-product`**: `A_w(x) = ∏_{n≥1}(1-x^n)^{-b_n}` in `ℚ[[x]]`. -/
theorem euler_product (w : ℕ → ℤ) :
    AwSeries w = ∏' n, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) := by
  have hlog1 : logOf (AwSeries w) =
      logOf (∏' n, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) := by
    rw [logOf_AwSeries, logOf_tprod_eulerFactors, ← logOf_AwSeries_eq_sum_eulerFactors]
  have hc1 : constantCoeff (AwSeries w) = 1 := constantCoeff_AwSeries w
  have hc2 :
      constantCoeff (∏' n, rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) : ℚ⟦X⟧) = 1 := by
    have heq : (fun n : ℕ => rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1)))) =
        (fun n : ℕ => 1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1)) := by funext n; ring
    have hM : Multipliable (fun n : ℕ => 1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1)) := by
      rw [← heq]; exact multipliable_eulerFactors (b w)
    obtain ⟨N, hN⟩ := (horder_eulerFactors w) 0
    have hcoeffs : coeff 0 (∏' n, (1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1))) =
        coeff 0 (∏ n ∈ Finset.range N,
          (1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b w (n + 1))) - 1))) := by
      apply coeff_tprod_eq_coeff_prod_range _ hM 0 N hN
    rw [← heq] at hcoeffs
    rw [← coeff_zero_eq_constantCoeff]
    rw [hcoeffs, coeff_zero_eq_constantCoeff]
    rw [heq]
    exact constantCoeff_prod_range _ (hg1_eulerFactors w) N
  have := exp_logOf (AwSeries w) hc1
  rw [hlog1] at this
  rw [← this, exp_logOf _ hc2]

end CongruenceTheory
