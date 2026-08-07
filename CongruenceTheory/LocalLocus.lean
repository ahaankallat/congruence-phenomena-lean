import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.BaseChange
import CongruenceTheory.EGFCoordinates

/-!
**Theorem `thm:local-locus`** ("Local and modulus-local congruence principle"), plus a
finite-range strengthening of `thm:general-defect` part (ii) that it depends on.

`general_defect_denom_clear` (`EGFCoordinates.lean`) required a *single* denominator `D` common
to *every* canonical coordinate `u_1, u_2, u_3, ...`, stronger than the manuscript's actual
hypothesis (only `u_1,...,u_{n+k}` need share a denominator, since `Q_{n,k}` only involves
those finitely many variables). This file closes that gap first: `vars_C_le`/`vars_Qpoly_le`
show `Q_{n,k}` only uses variables `X_1,...,X_{n+k}` (by induction on `C`'s own recurrence,
exactly like the total-degree bound), `evalAt_congr_of_vars` shows evaluation only depends on
a sequence's values at those variables, and `general_defect_denom_clear'` combines them into
the finite-range statement matching the manuscript exactly.

`thm:local-locus` itself is then a formal consequence: define `IsKLocal m x` to mean `x = a/b`
for integers `a, b` with `b` coprime to `m` (`Z_(m)` in the manuscript's own notation,
`Z_(k) = {a/b ∈ Q : gcd(b,k)=1}`); this single definition covers *both* clause (i) (`m` a
prime `p`) and clause (ii) (`m = k`) uniformly, with no primality needed anywhere in the proof.
Given `u_1,...,u_{n+k}` all `m`-local, `common_denom_of_local` builds one common denominator
`D` (the product of the individual denominators) that is automatically coprime to `m`; feeding
this into `general_defect_denom_clear'` and dividing back by `D^{n+k}` (itself coprime to `m`)
shows the shift-defect lies in `k · Z_(m)`.
-/

namespace CongruenceTheory

open MvPolynomial Finset PowerSeries

lemma fall_pos (n r : ℕ) (hr : r ≤ n) : 0 < fall n r := by
  rw [fall]
  apply Finset.prod_pos
  intro i hi
  have : i < r := Finset.mem_range.mp hi
  omega

/-- `C_m` only uses the variables `X_1,...,X_m` — by induction directly on `C`'s own defining
recurrence, exactly as for the total-degree bound `totalDegree_C_le`. -/
theorem vars_C_le : ∀ n : ℕ, (C n).vars ⊆ Finset.Icc 1 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [C_zero]; simp
    | m + 1 =>
      rw [C_succ]
      apply Finset.Subset.trans (MvPolynomial.vars_sum_subset _ _)
      apply Finset.biUnion_subset.mpr
      intro r hr
      have hrm : r ≤ m := by
        have := Finset.mem_range.mp hr; omega
      have hcast : ((fall m r : ℤ) : MvPolynomial ℕ ℤ) = MvPolynomial.C (fall m r) := by simp
      intro i hi
      have hi' : i ∈ (((fall m r : ℤ) : MvPolynomial ℕ ℤ) *
          (MvPolynomial.X (r + 1) * C (m - r))).vars := hi
      rw [hcast] at hi'
      have hfpos : fall m r ≠ 0 := (fall_pos m r hrm).ne'
      have hveq :=
        MvPolynomial.vars_C_mul (fall m r) hfpos (MvPolynomial.X (r + 1) * C (m - r))
      rw [hveq] at hi'
      have hsub2 :
          (MvPolynomial.X (r + 1) * C (m - r) : MvPolynomial ℕ ℤ).vars ⊆
            (MvPolynomial.X (r + 1) : MvPolynomial ℕ ℤ).vars ∪ (C (m - r)).vars :=
        MvPolynomial.vars_mul _ _
      have hunion := hsub2 hi'
      simp only [Finset.mem_union, MvPolynomial.vars_X, Finset.mem_singleton] at hunion
      rcases hunion with h | h
      · simp only [Finset.mem_Icc]; omega
      · have hmr := ih (m - r) (by omega) h
        simp only [Finset.mem_Icc] at hmr
        simp only [Finset.mem_Icc]; omega

/-- `Q_{n,k}` only uses variables `X_1,...,X_{n+k}` — same argument as `totalDegree_Qpoly_le`,
using `vars_C_mul` for exact equality under the nonzero constant `k`. -/
theorem vars_Qpoly_le (n k : ℕ) (hk : 1 ≤ k) : (Qpoly n k hk).vars ⊆ Finset.Icc 1 (n + k) := by
  have hspec := Qpoly_spec n k hk
  have hkne : (k : ℤ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have heq : (MvPolynomial.C (k : ℤ) * Qpoly n k hk).vars = (Qpoly n k hk).vars :=
    MvPolynomial.vars_C_mul (k : ℤ) hkne (Qpoly n k hk)
  rw [← heq, ← hspec]
  intro x hx
  have hx1 : x ∈ (C (n + k)).vars ∪ (C n * C k).vars :=
    Finset.mem_of_subset (MvPolynomial.vars_sub_subset (p := C (n + k))) hx
  simp only [Finset.mem_union] at hx1
  rcases hx1 with h | h
  · exact vars_C_le (n + k) h
  · have h2 : x ∈ (C n).vars ∪ (C k).vars := MvPolynomial.vars_mul _ _ h
    simp only [Finset.mem_union] at h2
    rcases h2 with h3 | h3
    · have := vars_C_le n h3; simp only [Finset.mem_Icc] at this ⊢; omega
    · have := vars_C_le k h3; simp only [Finset.mem_Icc] at this ⊢; omega

/-- Evaluation only depends on a sequence's values at the polynomial's own variables. -/
theorem evalAt_congr_of_vars {R : Type*} [CommRing R] (Q : MvPolynomial ℕ ℤ)
    (z z' : ℕ → R) (h : ∀ i ∈ Q.vars, z i = z' i) :
    evalAt z Q = evalAt z' Q := by
  show MvPolynomial.eval₂ (Int.castRingHom R) z Q = MvPolynomial.eval₂ (Int.castRingHom R) z' Q
  apply MvPolynomial.eval₂_congr
  intro i c hi hcoeff
  apply h
  rw [MvPolynomial.mem_vars_iff_mem_support]
  exact ⟨c, MvPolynomial.mem_support_iff.mpr hcoeff, hi⟩

/-- Finite-range strengthening of `general_defect_denom_clear`: it suffices for `z`/`D` to
match the canonical coordinates only on `1..n+k` (the manuscript's actual hypothesis), not for
every `m`. -/
theorem general_defect_denom_clear' (F : ℚ⟦X⟧) (hF1 : constantCoeff F = 1)
    (n k : ℕ) (hk : 1 ≤ k) (D : ℕ) (hD : 0 < D) (z : ℕ → ℤ)
    (hz : ∀ m ∈ Finset.Icc 1 (n + k), canonicalCoord m F = (z m : ℚ) / (D : ℚ)) :
    ∃ w : ℤ, (D : ℚ) ^ (n + k) * (egfCoeff F (n + k) - egfCoeff F n * egfCoeff F k) =
      (k : ℚ) * (w : ℚ) := by
  obtain ⟨w, hw⟩ :=
    evalAt_totalDegree_denom_clear (Qpoly n k hk) (n + k) (totalDegree_Qpoly_le n k hk) z D hD
  refine ⟨w, ?_⟩
  rw [general_defect_main F hF1 n k hk]
  have hcongr : evalAt (fun j => canonicalCoord j F) (Qpoly n k hk) =
      evalAt (fun j => (z j : ℚ) / (D : ℚ)) (Qpoly n k hk) := by
    apply evalAt_congr_of_vars
    intro i hi
    exact hz i (Finset.mem_of_subset (vars_Qpoly_le n k hk) hi)
  rw [hcongr]
  linear_combination -(k : ℚ) * hw

/-- `x` is `m`-local (lies in `Z_(m)`): `x = a/b` for integers `a, b` with `b` coprime to `m`.
Matches the manuscript's own notation `Z_(k) = {a/b ∈ Q : gcd(b,k)=1}` — for `m` a prime `p`
this is the usual `p`-local subring `Z_(p)`. -/
def IsKLocal (m : ℕ) (x : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), 0 < b ∧ Nat.Coprime b m ∧ x = (a : ℚ) / (b : ℚ)

/-- A finite family of `m`-local rationals has a common denominator that is itself coprime to
`m` — the product of the individual (coprime-to-`m`) denominators. -/
theorem common_denom_of_local (m n k : ℕ) (u : ℕ → ℚ)
    (hu : ∀ j ∈ Finset.Icc 1 (n + k), IsKLocal m (u j)) :
    ∃ (z : ℕ → ℤ) (D : ℕ), 0 < D ∧ Nat.Coprime D m ∧
      ∀ j ∈ Finset.Icc 1 (n + k), u j = (z j : ℚ) / (D : ℚ) := by
  classical
  set a : ℕ → ℤ := fun j => if h : j ∈ Finset.Icc 1 (n + k) then (hu j h).choose else 0 with ha
  set b : ℕ → ℕ :=
    fun j => if h : j ∈ Finset.Icc 1 (n + k) then (hu j h).choose_spec.choose else 1 with hb
  have hspec : ∀ j ∈ Finset.Icc 1 (n + k), 0 < b j ∧ Nat.Coprime (b j) m ∧
      u j = (a j : ℚ) / (b j : ℚ) := by
    intro j hj
    simp only [ha, hb, dif_pos hj]
    exact (hu j hj).choose_spec.choose_spec
  set D : ℕ := ∏ j ∈ Finset.Icc 1 (n + k), b j with hDdef
  have hDpos : 0 < D := by
    apply Finset.prod_pos
    intro j hj
    exact (hspec j hj).1
  have hDcop : Nat.Coprime D m := by
    rw [hDdef]
    apply Nat.Coprime.prod_left
    intro j hj
    exact (hspec j hj).2.1
  refine ⟨fun j => a j * ((∏ i ∈ (Finset.Icc 1 (n + k)).erase j, b i : ℕ) : ℤ), D, hDpos,
    hDcop, ?_⟩
  intro j hj
  obtain ⟨hbpos, hbcop, hueq⟩ := hspec j hj
  have hDeq : D = b j * ∏ i ∈ (Finset.Icc 1 (n + k)).erase j, b i := by
    rw [hDdef, ← Finset.prod_erase_mul _ _ hj]; ring
  have hbne : (b j : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
  have hDne : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hprodne : (∏ i ∈ (Finset.Icc 1 (n + k)).erase j, (b i : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact_mod_cast (hspec i (Finset.mem_of_mem_erase hi)).1.ne'
  rw [hueq]
  push_cast [hDeq]
  field_simp

theorem isKLocal_of_int_div_coprime_pow {m N : ℕ} (hN : Nat.Coprime N m) (w : ℤ) :
    IsKLocal m ((w : ℚ) / (N : ℚ)) := by
  by_cases hN0 : N = 0
  · exact ⟨0, 1, one_pos, Nat.coprime_one_left m, by simp [hN0]⟩
  · exact ⟨w, N, Nat.pos_of_ne_zero hN0, hN, rfl⟩

/-- **Theorem `thm:local-locus`**, clauses (i) and (ii) unified: for any modulus `m` (a prime
`p` gives clause (i)'s `Z_(p)`; `m = k` gives clause (ii)'s `Z_(k)`, since the manuscript
defines `Z_(k)` by the same `gcd(b,k)=1` condition used here — no primality is needed anywhere
in the argument), if the canonical coordinates `u_1,...,u_{n+k}` are all `m`-local, the
shift-defect `a_{n+k}-a_na_k` lies in `k · Z_(m)`. -/
theorem local_locus (F : ℚ⟦X⟧) (hF1 : constantCoeff F = 1) (n k : ℕ) (hk : 1 ≤ k) (m : ℕ)
    (hu : ∀ j ∈ Finset.Icc 1 (n + k), IsKLocal m (canonicalCoord j F)) :
    ∃ y : ℚ, egfCoeff F (n + k) - egfCoeff F n * egfCoeff F k = (k : ℚ) * y ∧ IsKLocal m y := by
  obtain ⟨z, D, hDpos, hDcop, hDeq⟩ :=
    common_denom_of_local m n k (fun j => canonicalCoord j F) hu
  obtain ⟨w, hw⟩ := general_defect_denom_clear' F hF1 n k hk D hDpos z hDeq
  refine ⟨(w : ℚ) / ((D : ℤ) ^ (n + k) : ℚ), ?_, ?_⟩
  · have hDne : ((D : ℚ)) ^ (n + k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hDpos.ne')
    field_simp
    push_cast at hw ⊢
    linear_combination hw
  · have hDpow : Nat.Coprime (D ^ (n + k)) m := Nat.Coprime.pow_left _ hDcop
    have := isKLocal_of_int_div_coprime_pow (m := m) (N := D ^ (n + k)) hDpow w
    convert this using 2
    push_cast
    ring

end CongruenceTheory
