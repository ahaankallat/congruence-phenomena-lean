import Mathlib
import CongruenceTheory.Universal
import CongruenceTheory.StrongTwoAdic

/-!
**Theorem `thm:base-change`** ("Universal base-change theorem"): the shift-defect
identities of `thm:universal` and `thm:strong` are identities of *universal integral
polynomials*, so they transport under the unique ring homomorphism
`Z[X_1,X_2,...] → R` (`X_j ↦ r_j`) to every commutative ring `R`, with no
characteristic-zero, integrality, or Q-algebra hypothesis on `r` needed.
-/

namespace CongruenceTheory

open MvPolynomial

/-- The ring hom `Z[X_1,X_2,...] → R` sending `X_j ↦ r_j`, for any commutative ring `R`
and any sequence `r : ℕ → R`. -/
noncomputable def evalAt {R : Type*} [CommRing R] (r : ℕ → R) : MvPolynomial ℕ ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) r

@[simp] lemma evalAt_C {R : Type*} [CommRing R] (r : ℕ → R) (a : ℤ) :
    evalAt r (MvPolynomial.C a) = (a : R) := by
  simp [evalAt]

/-- `c_m(r)`, the universal cycle-index polynomial `C_m` evaluated at an arbitrary
sequence `r : ℕ → R` in any commutative ring `R`. Matches the manuscript's `c_m(r)`
in Theorem `thm:base-change`. -/
noncomputable def cVal {R : Type*} [CommRing R] (r : ℕ → R) (m : ℕ) : R := evalAt r (C m)

lemma dvdCoeffs_shift_mod (n k : ℕ) (hk : 1 ≤ k) : DvdCoeffs k (C (n + k) - C n * C k) := by
  have hmodk : DvdCoeffs k (C (n + k) - C k * C n) :=
    dvdCoeffs_of_map_eq_zero (by
      rw [map_sub, map_mul]; exact sub_eq_zero.mpr (universal_shift_mod k hk n))
  have e1 : C (n + k) - C k * C n = C (n + k) - C n * C k := by ring
  rwa [e1] at hmodk

/-- **Shift-defect polynomial `Q_{n,k}`**: the (classically chosen) integral witness to
`thm:universal`'s mod-`k` congruence, `C_{n+k} - C_n C_k = k · Q_{n,k}` — see
`Qpoly_spec`. Matches the manuscript's `Q_{n,k}(X) = (C_{n+k}(X)-C_n(X)C_k(X))/k`. -/
noncomputable def Qpoly (n k : ℕ) (hk : 1 ≤ k) : MvPolynomial ℕ ℤ :=
  Classical.choose ((MvPolynomial.C_dvd_iff_dvd_coeff (k : ℤ) (C (n + k) - C n * C k)).mpr
    (dvdCoeffs_shift_mod n k hk))

theorem Qpoly_spec (n k : ℕ) (hk : 1 ≤ k) :
    C (n + k) - C n * C k = MvPolynomial.C (k : ℤ) * Qpoly n k hk :=
  Classical.choose_spec ((MvPolynomial.C_dvd_iff_dvd_coeff (k : ℤ) (C (n + k) - C n * C k)).mpr
    (dvdCoeffs_shift_mod n k hk))

/-- **Symmetric shift-defect polynomial `H_{n,k}`**: the integral witness to
`thm:universal`'s `lcm(n,k)`-symmetric congruence (`universal_shift_lcm`). -/
noncomputable def Hpoly (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) : MvPolynomial ℕ ℤ :=
  Classical.choose ((MvPolynomial.C_dvd_iff_dvd_coeff ((Nat.lcm n k : ℕ) : ℤ)
    (C (n + k) - C n * C k)).mpr (universal_shift_lcm n k hn hk))

theorem Hpoly_spec (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    C (n + k) - C n * C k = MvPolynomial.C ((Nat.lcm n k : ℕ) : ℤ) * Hpoly n k hn hk :=
  Classical.choose_spec ((MvPolynomial.C_dvd_iff_dvd_coeff ((Nat.lcm n k : ℕ) : ℤ)
    (C (n + k) - C n * C k)).mpr (universal_shift_lcm n k hn hk))

/-- **Theorem `thm:base-change`, mod-`k` clause.** For any commutative ring `R` and any
`r : ℕ → R`, `c_{n+k}(r) - c_n(r) c_k(r) = k · Q_{n,k}(r)` in `R`; equivalently
`c_{n+k}(r) ≡ c_n(r) c_k(r) (mod kR)`. No characteristic-zero, integrality, or
`Q`-algebra hypothesis on `r` is required — the identity is inherited purely from
the ring-hom naturality of evaluation applied to the integral polynomial identity
`Qpoly_spec`. -/
theorem base_change_mod {R : Type*} [CommRing R] (r : ℕ → R) (n k : ℕ) (hk : 1 ≤ k) :
    cVal r (n + k) - cVal r n * cVal r k = (k : R) * evalAt r (Qpoly n k hk) := by
  have h := congrArg (evalAt r) (Qpoly_spec n k hk)
  simpa [cVal, map_sub, map_mul] using h

/-- **Theorem `thm:base-change`, symmetric `lcm(n,k)` clause.** For `n, k ≥ 1`,
`c_{n+k}(r) - c_n(r) c_k(r) = lcm(n,k) · H_{n,k}(r)` in `R`. -/
theorem base_change_lcm {R : Type*} [CommRing R] (r : ℕ → R) (n k : ℕ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) :
    cVal r (n + k) - cVal r n * cVal r k = (Nat.lcm n k : R) * evalAt r (Hpoly n k hn hk) := by
  have h := congrArg (evalAt r) (Hpoly_spec n k hn hk)
  simpa [cVal, map_sub, map_mul] using h

/-- `Cperm`/`CpermSum` (the permutation-native cycle-index polynomials underlying
`thm:strong`, see `Perm.lean`/`StrongTwoAdic.lean`) evaluated at an arbitrary
sequence `r : ℕ → R`. -/
noncomputable def cpermVal {R : Type*} [CommRing R] (r : ℕ → R) (n : ℕ) : R := evalAt r (Cperm n)

noncomputable def cpermSumVal {R : Type*} [CommRing R] (r : ℕ → R) (n : ℕ) : R :=
  evalAt r (CpermSum n)

/-- **Theorem `thm:base-change`, two-adic clause**, in the permutation-native form that
matches how this codebase states `thm:strong` (`strong_two_adic` in `StrongTwoAdic.lean`
works with `Cperm`/`CpermSum`, not the abstract `C`; the two families are the manuscript's
own Proposition 2.1 apart, not re-derived here — see the README's scoping note on
`prop:content-bounds`). For `s ≥ 1` and any commutative ring `R` and `r : ℕ → R`,
`c^{sum}_{2^s}(r) - c_{2^s}(r)^2` is divisible by `2^{2s-1}` in `R`. -/
theorem base_change_two_adic {R : Type*} [CommRing R] (r : ℕ → R) (s : ℕ) (hs : 1 ≤ s) :
    ∃ Qr : R, cpermSumVal r (2 ^ s) - cpermVal r (2 ^ s) * cpermVal r (2 ^ s) =
      (2 ^ (2 * s - 1) : R) * Qr := by
  obtain ⟨Q, hQ⟩ := strong_two_adic s hs
  refine ⟨evalAt r Q, ?_⟩
  have h := congrArg (evalAt r) hQ
  simp only [map_sub, map_mul, map_natCast] at h
  rw [cpermVal, cpermSumVal]
  convert h using 2
  push_cast
  ring

end CongruenceTheory
