import Mathlib
import CongruenceTheory.EGFCoordinates

/-!
**Proposition `prop:no-all-egf-shift`** ("No universal shift law for arbitrary integral
EGFs"): there is no theorem asserting `a_{n+k}≡a_n a_k (mod k)` for *all* normalized EGFs
with integral exponential coefficients — unlike `thm:general-defect`, which needs the
*canonical logarithmic coordinates* `u_m` to be integral, not merely the coefficients `a_n`
themselves.

Witnessed exactly as in the manuscript by `A(x)=1+x²/2!`: `a_0=a_2=1` (both integers),
`a_4=0`, but `a_4-a_2·a_2=-1 ≢ 0 (mod 2)`.
-/

namespace CongruenceTheory

open PowerSeries

/-- `A(x) = 1 + x²/2!`, the manuscript's own counterexample series. -/
noncomputable def counterF : ℚ⟦X⟧ :=
  PowerSeries.mk (fun n => if n = 0 then 1 else if n = 2 then (1 / 2 : ℚ) else 0)

theorem coeff_counterF (n : ℕ) :
    coeff n counterF = if n = 0 then 1 else if n = 2 then (1 / 2 : ℚ) else 0 := by
  simp [counterF, coeff_mk]

theorem egfCoeff_counterF_0 : egfCoeff counterF 0 = 1 := by
  unfold egfCoeff; rw [coeff_counterF]; simp

theorem egfCoeff_counterF_2 : egfCoeff counterF 2 = 1 := by
  unfold egfCoeff; rw [coeff_counterF]; norm_num

theorem egfCoeff_counterF_4 : egfCoeff counterF 4 = 0 := by
  unfold egfCoeff; rw [coeff_counterF]; norm_num

/-- **`prop:no-all-egf-shift`**: `A(x)=1+x²/2!` has integer exponential coefficients
`a_0=a_2=1`, `a_4=0`, yet `a_4-a_2·a_2=-1` is not divisible by `2` — so integrality of the
ordinary EGF coefficients alone (unlike integrality of the canonical coordinates `u_m` in
`thm:general-defect`) does not force a shift congruence. -/
theorem no_universal_shift_law_for_all_integral_egf :
    egfCoeff counterF 0 = 1 ∧ egfCoeff counterF 2 = 1 ∧ egfCoeff counterF 4 = 0 ∧
      egfCoeff counterF 4 - egfCoeff counterF 2 * egfCoeff counterF 2 = -1 ∧
      ¬ ((2 : ℤ) ∣ (-1 : ℤ)) := by
  refine ⟨egfCoeff_counterF_0, egfCoeff_counterF_2, egfCoeff_counterF_4, ?_, by decide⟩
  rw [egfCoeff_counterF_2, egfCoeff_counterF_4]
  ring

end CongruenceTheory
