import Mathlib
import CongruenceTheory.CpermEqC
import CongruenceTheory.OptimalDivisorLower
import CongruenceTheory.Universal

/-!
**Theorem `thm:optimal-divisor`, unified for the abstract `C`.** Until now this codebase only
had two matching *halves* of this theorem on two different-but-equal representations: the
lower bound `lcm(n,k) ∣ d_{n,k}` (`universal_shift_lcm`, `Universal.lean`, for the abstract `C`)
and the sharp prime-power bound (`optimal_divisor_lower_bound`, `OptimalDivisorLower.lean`, for
the permutation-native `Cperm`/`CpermPair`). With the `Cperm = C` bridge (`CpermEqC.lean`) now
proved, both transfer to the *same* object, and combine here into the single clean statement
the manuscript actually states: for all `n, k ≥ 1`,
`M(n,k) := nk/rad(gcd(n,k))` divides every coefficient of `C_{n+k} - C_n C_k`
(`treeM_dvd_defect`) — this is also exactly the `r = 2` base case of the tree-modulus theorem
`thm:tree-modulus`'s inductive proof (the "exact two-term content theorem" its own proof calls
for at each binary-tree node).

**Assembly**: `CpermPair_eq_Cperm` transports `optimal_divisor_lower_bound` to
`optimal_divisor_lower_bound_C` (the sharp prime-power bound, now for `C`). `treeM_factorization`
computes `M(n,k)`'s `p`-adic valuation exactly: `v_p(n)+v_p(k)-1` when `p ∣ gcd(n,k)` (matching
`optimal_divisor_lower_bound_C`'s exponent exactly) and `v_p(n)+v_p(k) = v_p(\mathrm{lcm}(n,k))`
otherwise (matching `universal_shift_lcm`'s lcm bound). `dvd_of_forall_prime_pow_dvd` packages
per-prime bounds on a single integer into one divisibility via `Nat.factorization_le_iff_dvd`.
`treeM_dvd_defect` combines all of this coefficient-by-coefficient, using
`optimal_divisor_lower_bound_C` when `p ∣ gcd(n,k)` and `universal_shift_lcm` (via
`Nat.factorization_lcm` and `Nat.ordProj_dvd`) otherwise.
-/

namespace CongruenceTheory

open MvPolynomial UniqueFactorizationMonoid

/-- `CpermPair n k` (the permutation-native cycle-index sum on `Fin n ⊕ Fin k`) equals
`Cperm (n+k)` — an immediate corollary of `Cperm_eq_sum_of_card_eq`. -/
theorem CpermPair_eq_Cperm (n k : ℕ) : CpermPair n k = Cperm (n + k) := by
  unfold CpermPair
  exact (Cperm_eq_sum_of_card_eq (β := Fin n ⊕ Fin k)
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin])).symm

/-- **`optimal_divisor_lower_bound`, transported to the abstract `C`** via `Cperm_eq_C` and
`CpermPair_eq_Cperm`: the sharp prime-power lower bound on `d_{n,k}`, now for the manuscript's
own cycle-index polynomial rather than its permutation-native stand-in. -/
theorem optimal_divisor_lower_bound_C (p n k : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ Q : MvPolynomial ℕ ℤ,
      C (n + k) - C n * C k =
        ((p ^ (padicValNat p n + padicValNat p k - 1) : ℕ) : MvPolynomial ℕ ℤ) * Q := by
  obtain ⟨Q, hQ⟩ := optimal_divisor_lower_bound p hp n k hn hk
  refine ⟨Q, ?_⟩
  simp only [← Cperm_eq_C]
  rw [← CpermPair_eq_Cperm]
  exact hQ

/-- Combine per-prime prime-power divisibility bounds on a single integer into one exact
divisor, via `Nat.factorization_le_iff_dvd`. -/
theorem dvd_of_forall_prime_pow_dvd {c : ℤ} {D : ℕ} (hD0 : D ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ^ (D.factorization p) ∣ c.natAbs) : (D : ℤ) ∣ c := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  have hc0' : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc0
  have hDvd : D ∣ c.natAbs := by
    rw [← Nat.factorization_le_iff_dvd hD0 hc0', Finsupp.le_def]
    intro p
    by_cases hp : p.Prime
    · exact (Nat.Prime.pow_dvd_iff_le_factorization hp hc0').mp (h p hp)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hcast : ((D : ℕ) : ℤ) ∣ (c.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr hDvd
  exact Int.dvd_natAbs.mp hcast

/-- The exact tree-modulus / two-term optimal-divisor modulus: `M(n,k) = nk/rad(gcd(n,k))`,
matching the manuscript's own formula in both `thm:optimal-divisor` and `thm:tree-modulus`
(`r = 2` case). -/
noncomputable def treeM (n k : ℕ) : ℕ := n * k / radical (Nat.gcd n k)

/-- `M(n,k)`'s exact `p`-adic valuation: `v_p(n)+v_p(k)-1` when `p` divides `gcd(n,k)`,
`v_p(n)+v_p(k)` otherwise — matching `optimal_divisor_lower_bound_C`'s exponent in the first
case and `v_p(\mathrm{lcm}(n,k))` in the second. -/
theorem treeM_factorization (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) (p : ℕ) (hp : p.Prime) :
    (treeM n k).factorization p =
      if p ∣ Nat.gcd n k then padicValNat p n + padicValNat p k - 1
      else padicValNat p n + padicValNat p k := by
  have hgcdne : Nat.gcd n k ≠ 0 := Nat.gcd_ne_zero_left hn
  have hraddvd : radical (Nat.gcd n k) ∣ n * k :=
    (UniqueFactorizationMonoid.radical_dvd_self).trans
      ((Nat.gcd_dvd_left n k).trans (Dvd.intro k rfl))
  unfold treeM
  rw [Nat.factorization_div hraddvd, Finsupp.coe_tsub, Pi.sub_apply,
    Nat.factorization_mul hn hk]
  simp only [Finsupp.coe_add, Pi.add_apply]
  have hradsq : Squarefree (radical (Nat.gcd n k)) := UniqueFactorizationMonoid.squarefree_radical
  have hraddviff : p ∣ radical (Nat.gcd n k) ↔ p ∣ Nat.gcd n k :=
    UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible hp.prime.irreducible hgcdne
  have hfr : (radical (Nat.gcd n k)).factorization p =
      if p ∣ Nat.gcd n k then 1 else 0 := by
    by_cases hpg : p ∣ Nat.gcd n k
    · rw [if_pos hpg]
      exact Nat.factorization_eq_one_of_squarefree hradsq hp (hraddviff.mpr hpg)
    · rw [if_neg hpg]
      exact Nat.factorization_eq_zero_of_not_dvd (fun hcontra => hpg (hraddviff.mp hcontra))
  rw [hfr]
  simp only [Nat.factorization_def n hp, Nat.factorization_def k hp]
  split_ifs <;> omega

theorem dvd_natAbs_of_int_dvd {D : ℕ} {c : ℤ} (h : (D : ℤ) ∣ c) : D ∣ c.natAbs := by
  have := Int.natAbs_dvd_natAbs.mpr h
  simpa using this

theorem treeM_ne_zero (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) : treeM n k ≠ 0 := by
  have hn0 : n ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have hgcdne : Nat.gcd n k ≠ 0 := Nat.gcd_ne_zero_left hn0
  have hraddvd : radical (Nat.gcd n k) ∣ n * k :=
    (UniqueFactorizationMonoid.radical_dvd_self).trans
      ((Nat.gcd_dvd_left n k).trans (Dvd.intro k rfl))
  have hpos : 0 < radical (Nat.gcd n k) := Nat.radical_pos (Nat.gcd n k)
  have hle : radical (Nat.gcd n k) ≤ n * k := Nat.le_of_dvd (by positivity) hraddvd
  unfold treeM
  exact Nat.div_ne_zero_iff.mpr ⟨hpos.ne', hle⟩

/-- **`thm:optimal-divisor`, unified**: `M(n,k) = nk/rad(gcd(n,k))` divides every coefficient of
`C_{n+k} - C_n C_k`, for the manuscript's own abstract cycle-index polynomial `C`. Also the
`r = 2` base case of `thm:tree-modulus`'s inductive proof. -/
theorem treeM_dvd_defect (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (d : ℕ →₀ ℕ) :
    (treeM n k : ℤ) ∣ MvPolynomial.coeff d (C (n + k) - C n * C k) := by
  have hn0 : n ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  apply dvd_of_forall_prime_pow_dvd (D := treeM n k) (treeM_ne_zero n k hn hk)
  intro p hp
  rw [treeM_factorization n k hn0 hk0 p hp]
  by_cases hpg : p ∣ Nat.gcd n k
  · rw [if_pos hpg]
    obtain ⟨Q, hQ⟩ := optimal_divisor_lower_bound_C p n k hp hn hk
    have hcoeff : MvPolynomial.coeff d (C (n + k) - C n * C k) =
        (p ^ (padicValNat p n + padicValNat p k - 1) : ℤ) * MvPolynomial.coeff d Q := by
      rw [hQ]
      have hcast : ((p ^ (padicValNat p n + padicValNat p k - 1) : ℕ) : MvPolynomial ℕ ℤ) =
          MvPolynomial.C ((p ^ (padicValNat p n + padicValNat p k - 1) : ℕ) : ℤ) := by
        simp
      rw [hcast, MvPolynomial.coeff_C_mul]
      push_cast
      ring
    apply dvd_natAbs_of_int_dvd
    rw [hcoeff]
    push_cast
    exact ⟨MvPolynomial.coeff d Q, rfl⟩
  · rw [if_neg hpg]
    have hlcm : (Nat.lcm n k : ℤ) ∣ MvPolynomial.coeff d (C (n + k) - C n * C k) :=
      universal_shift_lcm n k hn hk d
    have hlcmnat : Nat.lcm n k ∣ (MvPolynomial.coeff d (C (n + k) - C n * C k)).natAbs :=
      dvd_natAbs_of_int_dvd hlcm
    have hpg' : ¬ (p ∣ n ∧ p ∣ k) := fun h => hpg (Nat.dvd_gcd h.1 h.2)
    have hvzero : padicValNat p n = 0 ∨ padicValNat p k = 0 := by
      by_contra hcontra
      push_neg at hcontra
      apply hpg'
      constructor
      · by_contra hpn
        apply hcontra.1
        rw [← Nat.factorization_def n hp]
        exact Nat.factorization_eq_zero_of_not_dvd hpn
      · by_contra hpk
        apply hcontra.2
        rw [← Nat.factorization_def k hp]
        exact Nat.factorization_eq_zero_of_not_dvd hpk
    have hlcmfact : (Nat.lcm n k).factorization p = padicValNat p n + padicValNat p k := by
      rw [Nat.factorization_lcm hn0 hk0]
      simp only [Finsupp.sup_apply, Nat.factorization_def n hp, Nat.factorization_def k hp]
      rcases hvzero with h | h <;> omega
    have hpowdvd : p ^ (padicValNat p n + padicValNat p k) ∣ Nat.lcm n k := by
      rw [← hlcmfact]
      exact Nat.ordProj_dvd (Nat.lcm n k) p
    exact hpowdvd.trans hlcmnat

end CongruenceTheory
