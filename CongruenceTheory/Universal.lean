import CongruenceTheory.Basic

/-!
Formalization of Theorem `thm:universal` ("Symmetric universal shift
congruence") from the manuscript: for every `n ≥ 0`, `k ≥ 1`,
`C_{n+k} ≡ C_n C_k (mod k Z[X_1,X_2,...])`.

A polynomial congruence `P ≡ Q (mod k Z[X_1,...])` means every coefficient of
`P - Q` is divisible by `k`, which is exactly the statement that `P` and `Q`
have the same image in `(Z/kZ)[X_1,X_2,...]`. We formalize it that way.
-/

open Finset MvPolynomial

namespace CongruenceTheory

/-- Reduction of `C n` modulo `k`, i.e. its image in `(ℤ/kℤ)[X_1,X_2,...]`. -/
noncomputable def Cmod (k n : ℕ) : MvPolynomial ℕ (ZMod k) :=
  MvPolynomial.map (Int.castRingHom (ZMod k)) (C n)

lemma Cmod_zero (k : ℕ) : Cmod k 0 = 1 := by
  simp [Cmod, C_zero]

lemma Cmod_succ (k n : ℕ) :
    Cmod k (n + 1) =
      ∑ r ∈ range (n + 1),
        ((fall n r : ℤ) : MvPolynomial ℕ (ZMod k)) * (MvPolynomial.X (r + 1) * Cmod k (n - r)) := by
  simp [Cmod, C_succ, map_sum]

/-- Lemma `lem:falling`, part (i): for `0 ≤ r ≤ n`,
`fall (n+k) r ≡ fall n r (mod k)`. -/
lemma fall_mod_eq (k n r : ℕ) (hr : r ≤ n) :
    ((fall (n + k) r : ℤ) : MvPolynomial ℕ (ZMod k)) = ((fall n r : ℤ) : MvPolynomial ℕ (ZMod k)) := by
  have h : ((fall (n + k) r : ℤ) : ZMod k) = ((fall n r : ℤ) : ZMod k) := by
    simp only [fall, Int.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    rw [ZMod.natCast_self]
    ring
  have hC := congrArg (MvPolynomial.C (σ := ℕ) (R := ZMod k)) h
  simpa [map_intCast] using hC

/-- Lemma `lem:falling`, part (ii): if `n < r`, then `k ∣ fall (n+k) r` — the
factor at index `i = n` in the falling-factorial product is exactly `k`. -/
lemma fall_dvd_of_lt (n r k : ℕ) (h : n < r) : (k : ℤ) ∣ fall (n + k) r := by
  have hmem : n ∈ range r := Finset.mem_range.mpr h
  have hterm : (fun i : ℕ => ((n + k : ℕ) : ℤ) - (i : ℤ)) n = (k : ℤ) := by
    show ((n + k : ℕ) : ℤ) - (n : ℤ) = (k : ℤ)
    push_cast; ring
  have hdvd : (fun i : ℕ => ((n + k : ℕ) : ℤ) - (i : ℤ)) n ∣ fall (n + k) r := by
    rw [fall]
    exact Finset.dvd_prod_of_mem (fun i : ℕ => ((n + k : ℕ) : ℤ) - (i : ℤ)) hmem
  rwa [hterm] at hdvd

/-- The mod-`k` case of Theorem `thm:universal`, proved by the manuscript's
own induction: `C_{n+k} ≡ C_k C_n (mod k)` for every `n ≥ 0`. -/
theorem universal_shift_mod (k : ℕ) (hk : 1 ≤ k) :
    ∀ n : ℕ, Cmod k (n + k) = Cmod k k * Cmod k n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [Cmod_zero]
    | m + 1 =>
      have hsplit : range (m + k + 1) = range (m + 1) ∪ Ico (m + 1) (m + k + 1) := by
        rw [range_eq_Ico, range_eq_Ico, Finset.Ico_union_Ico_eq_Ico] <;> omega
      have hdisj : Disjoint (range (m + 1)) (Ico (m + 1) (m + k + 1)) := by
        rw [range_eq_Ico]
        exact Finset.Ico_disjoint_Ico_consecutive 0 (m + 1) (m + k + 1)
      have hgoal : m + 1 + k = (m + k) + 1 := by omega
      rw [hgoal, Cmod_succ]
      rw [hsplit, Finset.sum_union hdisj]
      have hzero :
          ∑ r ∈ Ico (m + 1) (m + k + 1),
            ((fall (m + k) r : ℤ) : MvPolynomial ℕ (ZMod k)) *
              (MvPolynomial.X (r + 1) * Cmod k (m + k - r)) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        obtain ⟨hr1, _⟩ := Finset.mem_Ico.mp hr
        have hdvd : (k : ℤ) ∣ fall (m + k) r := fall_dvd_of_lt m r k (by omega)
        have hzmod : ((fall (m + k) r : ℤ) : ZMod k) = 0 := by
          rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hcast : ((fall (m + k) r : ℤ) : MvPolynomial ℕ (ZMod k)) = 0 := by
          have hC := congrArg (MvPolynomial.C (σ := ℕ) (R := ZMod k)) hzmod
          simpa [map_intCast] using hC
        rw [hcast]
        ring
      rw [hzero, add_zero]
      have hmain :
          ∑ r ∈ range (m + 1),
            ((fall (m + k) r : ℤ) : MvPolynomial ℕ (ZMod k)) *
              (MvPolynomial.X (r + 1) * Cmod k (m + k - r)) =
          Cmod k k * Cmod k (m + 1) := by
        rw [Cmod_succ, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        have hrm : r ≤ m := by
          have := Finset.mem_range.mp hr
          omega
        have hfall : ((fall (m + k) r : ℤ) : MvPolynomial ℕ (ZMod k)) =
            ((fall m r : ℤ) : MvPolynomial ℕ (ZMod k)) :=
          fall_mod_eq k m r hrm
        have hsub : m + k - r = (m - r) + k := by omega
        have hih : Cmod k ((m - r) + k) = Cmod k k * Cmod k (m - r) :=
          ih (m - r) (by omega)
        rw [hfall, hsub, hih]
        ring
      rw [hmain]

/-- Coefficientwise divisibility: `(m:ℤ)` divides every coefficient of `P`. This is the
precise meaning of `P ≡ 0 (mod m Z[X_1,X_2,...])`. -/
def DvdCoeffs (m : ℕ) (P : MvPolynomial ℕ ℤ) : Prop := ∀ d, (m : ℤ) ∣ MvPolynomial.coeff d P

/-- Coefficientwise divisibility from a vanishing `Cmod`-image. -/
lemma dvdCoeffs_of_map_eq_zero {k : ℕ} {P : MvPolynomial ℕ ℤ}
    (h : MvPolynomial.map (Int.castRingHom (ZMod k)) P = 0) : DvdCoeffs k P := by
  intro d
  have hc := congrArg (MvPolynomial.coeff d) h
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at hc
  rw [show (Int.castRingHom (ZMod k)) (MvPolynomial.coeff d P) =
      ((MvPolynomial.coeff d P : ℤ) : ZMod k) from rfl] at hc
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc

/-- Equality of `Cmod`-images is equivalent to coefficientwise divisibility of the
underlying integer-polynomial difference. -/
lemma dvdCoeffs_of_Cmod_eq {k n n' : ℕ} (h : Cmod k n = Cmod k n') :
    DvdCoeffs k (C n - C n') :=
  dvdCoeffs_of_map_eq_zero (by rw [map_sub]; exact sub_eq_zero.mpr h)

/-- **Theorem `thm:universal`, symmetric `lcm(n,k)` form.** For every `n, k ≥ 1`,
`C_{n+k} ≡ C_n C_k (mod lcm(n,k) Z[X_1,X_2,...])`. -/
theorem universal_shift_lcm (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    DvdCoeffs (Nat.lcm n k) (C (n + k) - C n * C k) := by
  have hmodk : DvdCoeffs k (C (n + k) - C k * C n) :=
    dvdCoeffs_of_map_eq_zero (by
      rw [map_sub, map_mul]; exact sub_eq_zero.mpr (universal_shift_mod k hk n))
  have hmodn : DvdCoeffs n (C (k + n) - C n * C k) :=
    dvdCoeffs_of_map_eq_zero (by
      rw [map_sub, map_mul]; exact sub_eq_zero.mpr (universal_shift_mod n hn k))
  have e1 : C (n + k) - C k * C n = C (n + k) - C n * C k := by ring
  have e2 : C (k + n) - C n * C k = C (n + k) - C n * C k := by rw [show k + n = n + k by omega]
  rw [e1] at hmodk
  rw [e2] at hmodn
  intro d
  have hk' : (k : ℤ) ∣ MvPolynomial.coeff d (C (n + k) - C n * C k) := hmodk d
  have hn' : (n : ℤ) ∣ MvPolynomial.coeff d (C (n + k) - C n * C k) := hmodn d
  set x := MvPolynomial.coeff d (C (n + k) - C n * C k) with hx
  have hkabs : k ∣ x.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hk'
    simpa using this
  have hnabs : n ∣ x.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hn'
    simpa using this
  have hlcm : Nat.lcm n k ∣ x.natAbs := Nat.lcm_dvd hnabs hkabs
  have hcast : ((Nat.lcm n k : ℕ) : ℤ) ∣ (x.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr hlcm
  exact Int.dvd_natAbs.mp hcast

end CongruenceTheory
