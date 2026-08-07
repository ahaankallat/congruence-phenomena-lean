import Mathlib
import CongruenceTheory.WeightedSpecialization

/-!
**Proposition `prop:finitewidth`**: if `w j = 0` for `j > h`, the weighted-permutation
sequence `A_w` satisfies a recurrence of width at most `h` with polynomial coefficients in
`n`. Follows directly from the falling-factorial recurrence `C_succ` used to *define* `C`
(`Basic.lean`), by discarding the terms `r ≥ h` (whose `w (r+1)` factor vanishes).
-/

namespace CongruenceTheory

open Finset

/-- **Proposition `prop:finitewidth`**: for `w j = 0` when `j > h`,
`A_w(n+1) = ∑_{r=0}^{min(n,h-1)} (n)_r · w_{r+1} · A_w(n-r)`, stated as a sum over
`Finset.range (min (n+1) h)` to avoid truncated subtraction in `h - 1`. -/
theorem Aw_finiteWidth (w : ℕ → ℤ) (h : ℕ) (hw : ∀ j, h < j → w j = 0) (n : ℕ) :
    Aw w (n + 1) =
      ∑ r ∈ Finset.range (min (n + 1) h), (fall n r : ℤ) * w (r + 1) * Aw w (n - r) := by
  have hfull : Aw w (n + 1) =
      ∑ r ∈ Finset.range (n + 1), (fall n r : ℤ) * w (r + 1) * Aw w (n - r) := by
    rw [Aw, C_succ, map_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [map_mul, map_mul, MvPolynomial.eval_X, map_intCast]
    show (fall n r : ℤ) * (w (r + 1) * Aw w (n - r)) = fall n r * w (r + 1) * Aw w (n - r)
    ring
  rw [hfull]
  symm
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro r hr hrnot
    rw [Finset.mem_range] at hr
    rw [Finset.mem_range] at hrnot
    have : w (r + 1) = 0 := hw (r + 1) (by omega)
    rw [this]
    ring

end CongruenceTheory
