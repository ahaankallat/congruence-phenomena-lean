import Mathlib
import CongruenceTheory.PowerSeriesLog

/-!
Infrastructure toward **Theorem `thm:euler-product`** ("Euler product":
`A_w(x) = ∏_{n≥1}(1-x^n)^{-b_n}` in `ℚ[[x]]`, for the Euler coordinates
`b_n = (1/n)∑_{d∣n}μ(n/d)w_d`) and **Theorem `thm:euler-integrality`**.

**What's built here**, roughly in dependency order:
1. `coeff_logOf_one_sub_X_pow`: the *exact* coefficient formula for `logOf(1-x^N)`, matching
   the classical Taylor expansion `-log(1-y)=∑_{r≥1}yʳ/r`.
2. `rpow`: a general `Fᵗ` operation for `t` in a `ℚ`-algebra (`rpow F t := (exp A).subst
   (C t * logOf F)`), generalizing `logOf_pow`/`logOf_inv`, needed to make sense of
   `(1-x^n)^{-b_n}` for possibly non-integral rational `b_n`.
3. Order bounds (`le_order_rpow_sub_one`, `le_order_logOf_one_sub_X_pow`,
   `le_order_eulerFactor_sub_one`) via Mathlib's own `PowerSeries.le_order_subst_right'`,
   feeding into `multipliable_eulerFactors`: the infinite product of Euler factors
   `∏' n, (1-x^{n+1})^{-b_{n+1}}` is well-defined (`Multipliable`), using Mathlib's own
   `PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top`.
4. **`logOf_tprod`**: the main new result — `logOf` is additive over *infinite* products
   `∏' n, (1+g n)` (not just finite ones, which is all `logOf_mul` gives). The proof:
   `coeff_tprod_eq_coeff_prod_range` shows a coefficient of an infinite product is determined
   by any sufficiently large finite truncation (a topology/order argument: the extra factors
   beyond the truncation point are all `≡1 mod X^{e+1}`, so don't affect coefficient `e`);
   `coeff_logOf_congr` shows `logOf` of two series that agree up to degree `e` also agree at
   coefficient `e` (via `order_pow_sub_pow_gt`, showing `Aᵈ-Bᵈ` inherits the order bound on
   `A-B`); combining these with the *finite*-product case (`logOf_prod_range`, by induction
   using `logOf_mul`) and a finite-support `HasSum` argument (`hasSum_coeff_logOf`) assembles
   the full infinite statement, matched against Mathlib's own `hasSum_iff_hasSum_coeff`.

**What's still needed for `thm:euler-product` itself** (not attempted here): reindexing
`∑_{n≥1}b_n∑_{r≥1}x^{nr}/r=∑_{m≥1}(x^m/m)∑_{n∣m}nb_n=∑w_mx^m/m` (the divisor-lattice
manipulation `GaussCongruence.lean` already has related infrastructure for, via Möbius
inversion) to match `logOf A_w` against `logOf_tprod`'s conclusion specialized to
`g n := rpow(1-x^{n+1})(-b_{n+1})-1`; then **`thm:euler-integrality`**'s own two-directional
proof on top of that (⟸ is easy given the product formula; ⟹ is the manuscript's own inductive
truncation argument extracting `b_N` from `A_w(x)·∏_{n<N}(1-x^n)^{b_n} mod x^{N+1}`).
-/

namespace CongruenceTheory

open PowerSeries Filter Finset

open scoped PowerSeries.WithPiTopology

/-! ### Exact coefficients of `logOf(1-x^N)` -/

/-- `[e = k] · c` as a `ℚ⟦X⟧`-coefficient: helper for `coeff_logOf_one_sub_X_pow`. -/
private lemma coeff_neg_one_pow_mul_X_pow (d k e : ℕ) :
    coeff e (((-1 : ℚ⟦X⟧)) ^ d * X ^ k) = if e = k then (-1 : ℚ) ^ d else 0 := by
  rw [show ((-1 : ℚ⟦X⟧)) ^ d = (PowerSeries.C ((-1 : ℚ) ^ d)) from by rw [map_pow]; simp]
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs <;> ring

/-- **Exact coefficient formula for `logOf(1-x^N)`**, `N ≥ 1`: matches the classical Taylor
expansion `-log(1-y) = ∑_{r≥1} yʳ/r` substituted at `y = x^N`, so
`[x^{Nr}] logOf(1-x^N) = -1/r` for `r ≥ 1`, and `0` at every other degree. Proved directly
from `logOf`'s definition (`Mathlib`'s `log A = X - X²/2 + X³/3 - ⋯` substituted at `-X^N`)
via the substitution-coefficient formula `PowerSeries.coeff_subst'`. -/
theorem coeff_logOf_one_sub_X_pow (N : ℕ) (hN : N ≠ 0) (e : ℕ) :
    coeff e (logOf (1 - X ^ N : ℚ⟦X⟧)) =
      if h : N ∣ e ∧ e ≠ 0 then (-1 : ℚ) / (e / N) else 0 := by
  rw [logOf_eq, show (1 - X ^ N : ℚ⟦X⟧) - 1 = -X ^ N from by ring]
  have hsubst : HasSubst (-X ^ N : ℚ⟦X⟧) := by
    apply HasSubst.of_constantCoeff_zero'
    simp [hN]
  rw [coeff_subst' hsubst]
  by_cases he0 : e = 0
  · subst he0
    rw [finsum_eq_single _ 0]
    · simp
    · intro d hd
      rw [neg_pow, ← pow_mul, coeff_neg_one_pow_mul_X_pow]
      rw [if_neg]
      · simp
      · intro h
        apply hd
        have : N * d = 0 := h.symm
        rcases Nat.mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 hN
        · exact h1
  · by_cases hdvd : N ∣ e
    · rw [dif_pos ⟨hdvd, he0⟩]
      rw [finsum_eq_single _ (e / N)]
      · rw [neg_pow, ← pow_mul, coeff_neg_one_pow_mul_X_pow]
        rw [Nat.mul_div_cancel' hdvd]
        rw [if_pos rfl]
        rw [coeff_log]
        have hen0 : e / N ≠ 0 := by
          intro h
          apply he0
          have := Nat.div_mul_cancel hdvd
          rw [h, zero_mul] at this
          omega
        rw [if_neg hen0]
        simp only [smul_eq_mul, Algebra.algebraMap_self_apply, pow_succ]
        have hsq : ((-1 : ℚ)) ^ (e / N * 2) = 1 :=
          Even.neg_one_pow ⟨e / N, by ring⟩
        have hNe : ((e / N : ℕ) : ℚ) = (e : ℚ) / (N : ℚ) :=
          Nat.cast_div hdvd (by exact_mod_cast hN)
        rw [hNe]
        have hNne : (N : ℚ) ≠ 0 := by exact_mod_cast hN
        have heNne : (e : ℚ) / (N : ℚ) ≠ 0 := by
          rw [← hNe]; exact_mod_cast hen0
        field_simp
        have hsq2 : (((-1 : ℚ)) ^ (e / N)) ^ 2 = 1 := by rw [← pow_mul]; exact hsq
        rw [hsq2]
      · intro j hj
        rw [neg_pow, ← pow_mul, coeff_neg_one_pow_mul_X_pow]
        rw [if_neg]
        · simp
        · contrapose hj
          have hj' : j = e / N := by
            rw [hj, Nat.mul_div_cancel_left j (Nat.pos_of_ne_zero hN)]
          exact hj'
    · rw [dif_neg (fun h => hdvd h.1)]
      apply finsum_eq_zero_of_forall_eq_zero
      intro j
      rw [neg_pow, ← pow_mul, coeff_neg_one_pow_mul_X_pow]
      rw [if_neg]
      · simp
      · contrapose hdvd
        exact ⟨j, hdvd⟩

/-! ### `rpow`: a general power operation, and order bounds for Euler factors -/

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- `Fᵗ := exp(t · logOf F)` for `t` in a `ℚ`-algebra, generalizing `logOf_pow`/`logOf_inv`
(natural-number and `-1` powers) to arbitrary `t`. Needed to make sense of `(1-x^n)^{-b_n}`
for possibly non-integral rational `b_n`. -/
noncomputable def rpow (F : A⟦X⟧) (t : A) : A⟦X⟧ :=
  (exp A).subst (PowerSeries.C t * logOf F)

theorem constantCoeff_tlog (F : A⟦X⟧) (hF : constantCoeff F = 1) (t : A) :
    constantCoeff (PowerSeries.C t * logOf F) = 0 := by
  rw [map_mul, constantCoeff_logOf hF, mul_zero]

theorem constantCoeff_rpow (F : A⟦X⟧) (hF : constantCoeff F = 1) (t : A) :
    constantCoeff (rpow F t) = 1 := by
  unfold rpow
  rw [constantCoeff_subst_of_const_zero (exp A) (PowerSeries.C t * logOf F)
    (constantCoeff_tlog F hF t)
    (HasSubst.of_constantCoeff_zero' (constantCoeff_tlog F hF t))]
  exact constantCoeff_exp

theorem logOf_rpow (F : A⟦X⟧) (hF : constantCoeff F = 1) (t : A) :
    logOf (rpow F t) = PowerSeries.C t * logOf F := by
  unfold rpow
  exact logOf_exp (PowerSeries.C t * logOf F) (constantCoeff_tlog F hF t)

theorem le_order_rpow_sub_one (F : ℚ⟦X⟧) (hF : constantCoeff F = 1) (t : ℚ) :
    (logOf F).order ≤ (rpow F t - 1).order := by
  unfold rpow
  have hg : (PowerSeries.C t * logOf F : ℚ⟦X⟧).constantCoeff = 0 := constantCoeff_tlog F hF t
  have hexp1 : (PowerSeries.exp ℚ - 1 : ℚ⟦X⟧).constantCoeff = 0 := by
    rw [map_sub, constantCoeff_exp]; simp
  have key := PowerSeries.le_order_subst_right' hg hexp1
  have heq : ((PowerSeries.exp ℚ - 1 : ℚ⟦X⟧)).subst (PowerSeries.C t * logOf F) =
      (PowerSeries.exp ℚ).subst (PowerSeries.C t * logOf F) - 1 := by
    rw [PowerSeries.subst_sub (HasSubst.of_constantCoeff_zero' hg),
      subst_one_eq (HasSubst.of_constantCoeff_zero' hg)]
  rw [heq] at key
  refine le_trans ?_ key
  have hmul := PowerSeries.le_order_mul (PowerSeries.C t : ℚ⟦X⟧) (logOf F)
  refine le_trans ?_ hmul
  exact le_add_self

theorem le_order_logOf_one_sub_X_pow (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (logOf (1 - X ^ (n + 1) : ℚ⟦X⟧)).order := by
  rw [logOf_eq]
  have h1 : (-X ^ (n + 1) : ℚ⟦X⟧).constantCoeff = 0 := by simp
  have h2 : (PowerSeries.log ℚ).constantCoeff = 0 := PowerSeries.constantCoeff_log
  have := PowerSeries.le_order_subst_right' h1 h2
  rw [show (1 - X ^ (n + 1) : ℚ⟦X⟧) - 1 = -X ^ (n + 1) by ring] at *
  rw [show ((n + 1 : ℕ) : ℕ∞) = (-X ^ (n + 1) : ℚ⟦X⟧).order from ?_]
  · exact this
  · rw [PowerSeries.order_neg]; simp [PowerSeries.order_X_pow]

/-- The Euler factor `(1-x^{n+1})^{-b}` minus `1` has order `≥ n+1`, for any exponent `b`. -/
theorem le_order_eulerFactor_sub_one (n : ℕ) (b : ℚ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-b) - 1).order := by
  have h1 : constantCoeff (1 - X ^ (n + 1) : ℚ⟦X⟧) = 1 := by simp
  exact le_trans (le_order_logOf_one_sub_X_pow n) (le_order_rpow_sub_one _ h1 (-b))

/-- The infinite product of Euler factors `∏' n, (1-x^{n+1})^{-b_{n+1}}` is well-defined,
via Mathlib's own `multipliable_one_add_of_tendsto_order_atTop_nhds_top`. -/
theorem multipliable_eulerFactors (b : ℕ → ℚ) :
    Multipliable (fun n : ℕ => rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b (n + 1)))) := by
  have heq : (fun n : ℕ => rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b (n + 1)))) =
      (fun n : ℕ => 1 + (rpow (1 - X ^ (n + 1) : ℚ⟦X⟧) (-(b (n + 1))) - 1)) := by
    funext n; ring
  rw [heq]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  calc (n : ℕ∞) < ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_of_le hm
    _ ≤ (rpow (1 - X ^ (m + 1) : ℚ⟦X⟧) (-(b (m + 1))) - 1).order :=
        le_order_eulerFactor_sub_one m (b (m + 1))

/-! ### `logOf` is additive over infinite products -/

/-- A finite product of `(1+g i)` terms, each with `order (g i) > e`, has `order (product-1)
> e` too — closure of the "`≡1 mod X^{e+1}`" condition under finite products. -/
theorem order_prod_one_add_sub_one_gt (g : ℕ → ℚ⟦X⟧) (s : Finset ℕ) (e : ℕ)
    (hg : ∀ i ∈ s, (e : ℕ∞) < (g i).order) :
    (e : ℕ∞) < (∏ i ∈ s, (1 + g i) - 1).order := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have step : (∏ i ∈ insert a s, (1 + g i)) - 1 =
        (∏ i ∈ s, (1 + g i) - 1) + (∏ i ∈ s, (1 + g i)) * g a := by
      rw [Finset.prod_insert ha]; ring
    rw [Finset.prod_insert ha] at step
    rw [step]
    have h1 : (e : ℕ∞) < (∏ i ∈ s, (1 + g i) - 1).order :=
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have h2 : (e : ℕ∞) < ((∏ i ∈ s, (1 + g i)) * g a).order := by
      apply lt_of_lt_of_le (hg a (Finset.mem_insert_self a s))
      calc (g a).order ≤ (∏ i ∈ s, (1 + g i)).order + (g a).order := le_add_self
        _ ≤ ((∏ i ∈ s, (1 + g i)) * g a).order := PowerSeries.le_order_mul _ _
    calc (e : ℕ∞) < min ((∏ i ∈ s, (1 + g i) - 1).order) (((∏ i ∈ s, (1 + g i)) * g a).order) :=
          lt_min h1 h2
      _ ≤ _ := PowerSeries.min_order_le_order_add _ _

/-- A coefficient of an infinite product `∏' n, (1+g n)` equals that of any large enough
finite truncation, since the extra factors don't affect coefficients below their orders. -/
theorem coeff_tprod_eq_coeff_prod_range (g : ℕ → ℚ⟦X⟧)
    (hM : Multipliable (fun n => 1 + g n : ℕ → ℚ⟦X⟧)) (e N : ℕ)
    (hg : ∀ n ≥ N, (e : ℕ∞) < (g n).order) :
    coeff e (∏' n, (1 + g n)) = coeff e (∏ n ∈ Finset.range N, (1 + g n)) := by
  obtain ⟨L, hL⟩ := hM
  rw [hL.tprod_eq]
  have hcont : Tendsto (fun s : Finset ℕ => coeff e (∏ b ∈ s, (1 + g b))) Filter.atTop
      (nhds (coeff e L)) :=
    (PowerSeries.WithPiTopology.continuous_coeff (R := ℚ) e).continuousAt.tendsto.comp hL
  have hconst : Tendsto (fun s : Finset ℕ => coeff e (∏ b ∈ s, (1 + g b))) Filter.atTop
      (nhds (coeff e (∏ n ∈ Finset.range N, (1 + g n)))) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [Filter.eventually_ge_atTop (Finset.range N)] with s hs
    have hsplit : s = Finset.range N ∪ (s \ Finset.range N) :=
      (Finset.union_sdiff_of_subset hs).symm
    have hdisj : Disjoint (Finset.range N) (s \ Finset.range N) := Finset.disjoint_sdiff
    rw [hsplit, Finset.prod_union hdisj]
    have hR : (e : ℕ∞) < (∏ i ∈ s \ Finset.range N, (1 + g i) - 1).order := by
      apply order_prod_one_add_sub_one_gt
      intro i hi
      have : i ≥ N := by
        have := Finset.mem_sdiff.mp hi
        by_contra h
        push Not at h
        exact this.2 (Finset.mem_range.mpr h)
      exact hg i this
    set R := ∏ i ∈ s \ Finset.range N, (1 + g i) with hRdef
    have hReq : R = 1 + (R - 1) := by ring
    rw [hReq, mul_add, mul_one, map_add]
    have hzero : coeff e ((∏ n ∈ Finset.range N, (1 + g n)) * (R - 1)) = 0 := by
      apply PowerSeries.coeff_of_lt_order
      apply lt_of_lt_of_le hR
      calc (R - 1).order = (0 : ℕ∞) + (R - 1).order := by rw [zero_add]
        _ ≤ (∏ n ∈ Finset.range N, (1 + g n)).order + (R - 1).order := by
            gcongr; exact zero_le
        _ ≤ ((∏ n ∈ Finset.range N, (1 + g n)) * (R - 1)).order := PowerSeries.le_order_mul _ _
    rw [hzero, add_zero]
  exact tendsto_nhds_unique hcont hconst

/-- If `order(A-B) > e` then `order(Aᵈ-Bᵈ) > e` for every `d` — used to show `logOf`'s
coefficient `e` only depends on its argument's coefficients up to degree `e`. -/
theorem order_pow_sub_pow_gt (A B : ℚ⟦X⟧) (e : ℕ) (h : (e : ℕ∞) < (A - B).order) :
    ∀ d : ℕ, (e : ℕ∞) < (A ^ d - B ^ d).order := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have step : A ^ (d + 1) - B ^ (d + 1) = A * (A ^ d - B ^ d) + (A - B) * B ^ d := by ring
    rw [step]
    have h1 : (e : ℕ∞) < (A * (A ^ d - B ^ d)).order := by
      apply lt_of_lt_of_le ih
      calc (A ^ d - B ^ d).order ≤ (A).order + (A ^ d - B ^ d).order := le_add_self
        _ ≤ (A * (A ^ d - B ^ d)).order := PowerSeries.le_order_mul _ _
    have h2 : (e : ℕ∞) < ((A - B) * B ^ d).order := by
      apply lt_of_lt_of_le h
      calc (A - B).order ≤ (A - B).order + (B ^ d).order := le_self_add
        _ ≤ ((A - B) * B ^ d).order := PowerSeries.le_order_mul _ _
    calc (e : ℕ∞) < min ((A * (A ^ d - B ^ d)).order) (((A - B) * B ^ d).order) := lt_min h1 h2
      _ ≤ _ := PowerSeries.min_order_le_order_add _ _

/-- `logOf` of two series that agree up to degree `e` also agree at coefficient `e`. -/
theorem coeff_logOf_congr (F G : ℚ⟦X⟧) (hF : constantCoeff F = 1) (hG : constantCoeff G = 1)
    (e : ℕ) (h : (e : ℕ∞) < (F - G).order) :
    coeff e (logOf F) = coeff e (logOf G) := by
  have hFG1 : (F - 1) - (G - 1) = F - G := by ring
  rw [logOf_eq, logOf_eq, coeff_subst' (hasSubst_sub_one hF), coeff_subst' (hasSubst_sub_one hG)]
  apply finsum_congr
  intro d
  congr 1
  by_cases hd0 : d = 0
  · simp [hd0]
  · have hpow : (e : ℕ∞) < ((F - 1) ^ d - (G - 1) ^ d).order := by
      apply order_pow_sub_pow_gt
      rwa [hFG1]
    have := PowerSeries.coeff_of_lt_order e hpow
    rw [map_sub] at this
    linarith [sub_eq_zero.mp this]

theorem constantCoeff_prod_range (g : ℕ → ℚ⟦X⟧) (hg : ∀ n, constantCoeff (1 + g n : ℚ⟦X⟧) = 1)
    (N : ℕ) : constantCoeff (∏ n ∈ Finset.range N, (1 + g n) : ℚ⟦X⟧) = 1 := by
  rw [map_prod]
  exact Finset.prod_eq_one (fun n _ => hg n)

/-- `logOf` of a *finite* product, by induction using `logOf_mul`. -/
theorem logOf_prod_range (g : ℕ → ℚ⟦X⟧) (hg : ∀ n, constantCoeff (1 + g n : ℚ⟦X⟧) = 1)
    (N : ℕ) :
    logOf (∏ n ∈ Finset.range N, (1 + g n)) = ∑ n ∈ Finset.range N, logOf (1 + g n) := by
  induction N with
  | zero => simp [logOf_one]
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    rw [logOf_mul _ _ (constantCoeff_prod_range g hg N) (hg N), ih]

theorem le_order_logOf_of_constantCoeff_eq_one (F : ℚ⟦X⟧) (hF : constantCoeff F = 1) :
    (F - 1).order ≤ (logOf F).order := by
  rw [logOf_eq]
  exact PowerSeries.le_order_subst_right' (by simp [hF]) (by simp)

/-- Coefficient-level form of `logOf`'s additivity over the infinite product `∏' n, (1+g n)`:
`coeff e (logOf ∏') = ∑' n, coeff e (logOf (1+g n))`, established via a large-enough finite
truncation (`coeff_tprod_eq_coeff_prod_range` + `coeff_logOf_congr`) matched against
`logOf_prod_range`, with the tail of the sum vanishing since `logOf(1+g n)` inherits `g n`'s
order bound (`le_order_logOf_of_constantCoeff_eq_one`). -/
theorem hasSum_coeff_logOf (g : ℕ → ℚ⟦X⟧) (hg1 : ∀ n, constantCoeff (1 + g n : ℚ⟦X⟧) = 1)
    (hM : Multipliable (fun n => 1 + g n : ℕ → ℚ⟦X⟧))
    (horder : ∀ e : ℕ, ∃ N, ∀ n ≥ N, (e : ℕ∞) < (g n).order) (e : ℕ) :
    HasSum (fun n => coeff e (logOf (1 + g n))) (coeff e (logOf (∏' n, (1 + g n)))) := by
  obtain ⟨N, hN⟩ := horder e
  have hcoeffs :
      ∀ d ≤ e, coeff d (∏' n, (1 + g n)) = coeff d (∏ n ∈ Finset.range N, (1 + g n)) := by
    intro d hd
    apply coeff_tprod_eq_coeff_prod_range g hM d N
    intro n hn
    exact lt_of_le_of_lt (by exact_mod_cast hd) (hN n hn)
  have hstep :
      ((e + 1 : ℕ) : ℕ∞) ≤ ((∏' n, (1 + g n)) - (∏ n ∈ Finset.range N, (1 + g n))).order := by
    apply PowerSeries.nat_le_order
    intro i hi
    rw [map_sub, hcoeffs i (by omega), sub_self]
  have horderdiff :
      (e : ℕ∞) < ((∏' n, (1 + g n)) - (∏ n ∈ Finset.range N, (1 + g n))).order := by
    refine lt_of_lt_of_le ?_ hstep
    exact_mod_cast Nat.lt_succ_self e
  have hcc1 : constantCoeff (∏' n, (1 + g n) : ℚ⟦X⟧) = 1 := by
    have h0 := hcoeffs 0 (Nat.zero_le e)
    simpa [coeff_zero_eq_constantCoeff, constantCoeff_prod_range g hg1] using h0
  have key : coeff e (logOf (∏' n, (1 + g n))) =
      ∑ n ∈ Finset.range N, coeff e (logOf (1 + g n)) := by
    rw [coeff_logOf_congr _ _ hcc1 (constantCoeff_prod_range g hg1 N) e horderdiff,
      logOf_prod_range g hg1 N, map_sum]
  rw [key]
  apply hasSum_sum_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  apply PowerSeries.coeff_of_lt_order
  apply lt_of_lt_of_le (hN n (by simpa using hn))
  have := le_order_logOf_of_constantCoeff_eq_one (1 + g n) (hg1 n)
  simpa using this

/-- **`logOf` is additive over the infinite product of Euler-type factors**: extends
`logOf_mul` from finite to infinite products. This is the main new result of this file. -/
theorem logOf_tprod (g : ℕ → ℚ⟦X⟧) (hg1 : ∀ n, constantCoeff (1 + g n : ℚ⟦X⟧) = 1)
    (hM : Multipliable (fun n => 1 + g n : ℕ → ℚ⟦X⟧))
    (horder : ∀ e : ℕ, ∃ N, ∀ n ≥ N, (e : ℕ∞) < (g n).order) :
    logOf (∏' n, (1 + g n)) = ∑' n, logOf (1 + g n) := by
  have hSummable : Summable (fun n => logOf (1 + g n) : ℕ → ℚ⟦X⟧) :=
    (PowerSeries.WithPiTopology.summable_iff_summable_coeff _).mpr
      (fun e => (hasSum_coeff_logOf g hg1 hM horder e).summable)
  apply PowerSeries.ext
  intro e
  rw [(hasSum_coeff_logOf g hg1 hM horder e).tsum_eq.symm]
  exact ((PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (R := ℚ) |>.mp
    hSummable.hasSum) e).tsum_eq

end CongruenceTheory
