import Mathlib

/-!
**Theorem `thm:gauss`** ("Prime-power Gauss criterion"): condition (iii) of
`thm:euler-integrality` — `∀N≥1, N ∣ M_N` where `M_N = ∑_{d∣N} μ(N/d) w_d` — is equivalent to
the Gauss congruence condition `w_{mp^r} ≡ w_{mp^{r-1}} (mod p^r)` for every prime `p`, `r≥1`,
and `m≥1` with `p∤m`. This is a self-contained fact about Möbius transforms of integer
sequences, independent of the power-series machinery `thm:euler-product`/`thm:euler-integrality`
need.

The crux is the **key identity**: for `p∤m`, `r≥1`,
`M_{mp^r} = ∑_{e∣m} μ(m/e)·(w_{ep^r} - w_{ep^{r-1}})`, obtained by splitting the divisors of
`m·p^r` into `e·p^i` for `e∣m`, `0≤i≤r` (using `Nat.Coprime.divisors_mul` and
`Nat.divisors_prime_pow`), then using multiplicativity of `μ` to show only `i=r` and `i=r-1`
contribute (`μ(p^j)=0` for `j≥2`).
-/

namespace CongruenceTheory

open Nat Finset ArithmeticFunction

open scoped ArithmeticFunction.Moebius

/-- **Reindexing**: divisors of `m·p^r` (for `p∤m`) correspond to pairs `(e,i)` with
`e∣m`, `0≤i≤r`, via `e·p^i`. -/
theorem sum_divisors_mul_prime_pow_reindex (m p r : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (f : ℕ → ℤ) :
    ∑ d ∈ (m * p ^ r).divisors, f d =
      ∑ e ∈ m.divisors, ∑ i ∈ Finset.range (r + 1), f (e * p ^ i) := by
  have hcop : m.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((hp.coprime_iff_not_dvd.mpr hpm).symm)
  rw [hcop.divisors_mul, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  trans (∑ x ∈ m.divisors ×ˢ (p ^ r).divisors, f (x.1 * x.2))
  · exact Finset.sum_attach (m.divisors ×ˢ (p ^ r).divisors) (fun x => f (x.1 * x.2))
  trans (∑ e ∈ m.divisors, ∑ q ∈ (p ^ r).divisors, f (e * q))
  · exact Finset.sum_product' m.divisors (p ^ r).divisors (fun a b => f (a * b))
  apply Finset.sum_congr rfl
  intro e _
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  rfl

lemma div_calc (e c p r i : ℕ) (hp : p.Prime) (hene0 : e ≠ 0) (hi : i ≤ r) :
    e * c * p ^ r / (e * p ^ i) = c * p ^ (r - i) := by
  have heq : e * c * p ^ r = (e * p ^ i) * (c * p ^ (r - i)) := by
    rw [show e * p ^ i * (c * p ^ (r - i)) = e * (c * (p ^ i * p ^ (r - i))) from by ring]
    rw [← pow_add, show i + (r - i) = r from by omega]
    ring
  rw [heq]
  exact Nat.mul_div_cancel_left _ (Nat.mul_pos (Nat.pos_of_ne_zero hene0) (pow_pos hp.pos i))

/-- **The key identity**: `M_{mp^r} = ∑_{e∣m} μ(m/e)·(w_{ep^r} - w_{ep^{r-1}})`, for `p∤m`,
`m≠0`, `r≥1`. -/
theorem key_identity (m p r : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) (hr : 1 ≤ r)
    (w : ℕ → ℤ) :
    ∑ d ∈ (m * p ^ r).divisors, (μ (m * p ^ r / d) : ℤ) * w d =
      ∑ e ∈ m.divisors,
        ((μ (m / e) : ℤ) * w (e * p ^ r) - (μ (m / e) : ℤ) * w (e * p ^ (r - 1))) := by
  rw [sum_divisors_mul_prime_pow_reindex m p r hp hpm (fun d => (μ (m * p ^ r / d) : ℤ) * w d)]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨c, hc⟩ := (Nat.mem_divisors.mp he).1
  have hene0 : e ≠ 0 := by rintro rfl; simp at hc; exact hm hc
  have hce : m / e = c := by rw [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hene0)]
  have hdiv : ∀ i ≤ r, m * p ^ r / (e * p ^ i) = c * p ^ (r - i) := by
    intro i hi
    rw [hc]; exact div_calc e c p r i hp hene0 hi
  have hcopce : c.Coprime p := by
    apply (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro hpc
    apply hpm
    rw [hc]
    exact Dvd.dvd.mul_left hpc e
  have hmul : ∀ i ≤ r, (μ (m * p ^ r / (e * p ^ i)) : ℤ) =
      (μ c : ℤ) * (μ (p ^ (r - i)) : ℤ) := by
    intro i hi
    rw [hdiv i hi]
    have := isMultiplicative_moebius.map_mul_of_coprime (hcopce.pow_right (r - i))
    exact_mod_cast this
  have hexpand : ∑ i ∈ Finset.range (r + 1), (μ (m * p ^ r / (e * p ^ i)) : ℤ) * w (e * p ^ i) =
      ∑ i ∈ Finset.range (r + 1), (μ c : ℤ) * (μ (p ^ (r - i)) : ℤ) * w (e * p ^ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hmul i (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)), mul_assoc]
  rw [hexpand, hce]
  rw [show ∑ i ∈ Finset.range (r + 1), (μ c : ℤ) * (μ (p ^ (r - i)) : ℤ) * w (e * p ^ i) =
      ∑ i ∈ ({r - 1, r} : Finset ℕ), (μ c : ℤ) * (μ (p ^ (r - i)) : ℤ) * w (e * p ^ i) from by
    symm
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_range]; omega
    · intro x hx hxnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
      rw [Finset.mem_range] at hx
      have hz : (μ (p ^ (r - x)) : ℤ) = 0 := by
        have hpp := moebius_apply_prime_pow hp (show r - x ≠ 0 by omega)
        rw [if_neg (by omega)] at hpp
        exact_mod_cast hpp
      rw [hz]; ring]
  rw [Finset.sum_pair (by omega : r - 1 ≠ r)]
  have h1 : (μ (p ^ (r - r)) : ℤ) = 1 := by simp
  have h2 : (μ (p ^ (r - (r - 1))) : ℤ) = -1 := by
    rw [show r - (r - 1) = 1 by omega, pow_one]
    exact_mod_cast moebius_apply_prime hp
  rw [h1, h2]
  ring

/-- `M_N`, the Möbius transform `∑_{d∣N} μ(N/d)·w_d`. -/
noncomputable def MTrans (w : ℕ → ℤ) (N : ℕ) : ℤ := ∑ d ∈ N.divisors, (μ (N / d) : ℤ) * w d

/-- **Möbius inversion**: `w_m = ∑_{d∣m} M_d`, for free from Mathlib's own
`ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`. -/
theorem moebius_inversion (w : ℕ → ℤ) (m : ℕ) (hm : 0 < m) :
    w m = ∑ d ∈ m.divisors, MTrans w d := by
  have hiff := @sum_eq_iff_sum_smul_moebius_eq ℤ _ (MTrans w) w
  have hrhs : ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℤ) • w x.2 = MTrans w n := by
    intro n _
    rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℤ) • w b)]
    simp only [MTrans, smul_eq_mul]
  exact ((hiff.mpr hrhs) m hm).symm

/-- **`thm:gauss`, the "`N∣M_N` for all `N` implies the Gauss congruence" direction.** -/
theorem gauss_of_dvd_forall (w : ℕ → ℤ) (hyp : ∀ N : ℕ, 0 < N → (N : ℤ) ∣ MTrans w N)
    (p m r : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (p : ℤ) ^ r ∣ (w (m * p ^ r) - w (m * p ^ (r - 1))) := by
  have hinv := moebius_inversion (fun e => w (e * p ^ r) - w (e * p ^ (r - 1))) m (by omega)
  have hG : ∀ d ∈ m.divisors, (p : ℤ) ^ r ∣
      MTrans (fun e => w (e * p ^ r) - w (e * p ^ (r - 1))) d := by
    intro d hd
    have hdm : d ∣ m := (Nat.mem_divisors.mp hd).1
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hpd : ¬ p ∣ d := fun h => hpm (h.trans hdm)
    have hkeyd := key_identity d p r hp hpd (by omega) hr w
    have hMTeq : MTrans w (d * p ^ r) =
        MTrans (fun e => w (e * p ^ r) - w (e * p ^ (r - 1))) d := by
      rw [MTrans, MTrans, hkeyd]
      exact Finset.sum_congr rfl (fun e _ => (mul_sub (μ (d / e) : ℤ) (w (e * p ^ r))
        (w (e * p ^ (r - 1)))).symm)
    have hdvd : ((d * p ^ r : ℕ) : ℤ) ∣ MTrans w (d * p ^ r) :=
      hyp (d * p ^ r) (Nat.mul_pos hd0 (pow_pos hp.pos r))
    have hdvd2 : (p : ℤ) ^ r ∣ MTrans w (d * p ^ r) := by
      refine dvd_trans ?_ hdvd
      push_cast
      exact Dvd.intro_left (d : ℤ) rfl
    rwa [hMTeq] at hdvd2
  have hdvdsum : (p : ℤ) ^ r ∣ ∑ d ∈ m.divisors,
      MTrans (fun e => w (e * p ^ r) - w (e * p ^ (r - 1))) d := Finset.dvd_sum hG
  rw [← hinv] at hdvdsum
  exact hdvdsum

/-- **`thm:gauss`, the "Gauss congruence implies `N∣M_N` for all `N`" direction.** -/
theorem dvd_forall_of_gauss (w : ℕ → ℤ)
    (hgauss : ∀ p r m : ℕ, p.Prime → 1 ≤ r → ¬ p ∣ m →
      (p : ℤ) ^ r ∣ (w (m * p ^ r) - w (m * p ^ (r - 1))))
    (N : ℕ) (hN : N ≠ 0) : (N : ℤ) ∣ MTrans w N := by
  rw [Int.ofNat_dvd_left, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; simp
  · set r := N.factorization p with hr_def
    have hrk : k ≤ r := by
      rw [hr_def]
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp hN).mp hpk
    have hr1 : 1 ≤ r := by omega
    set m := N / p ^ r with hm_def
    have hNe : N = m * p ^ r := by
      rw [hm_def, Nat.div_mul_cancel (Nat.ordProj_dvd N p)]
    have hpm : ¬ p ∣ m := not_dvd_ordCompl hp hN
    have hm1 : m ≠ 0 := by
      intro hm0
      rw [hm0, zero_mul] at hNe
      exact hN hNe
    have hkey := key_identity m p r hp hpm hm1 hr1 w
    have hprM : (p : ℤ) ^ r ∣ MTrans w N := by
      rw [MTrans, hNe, hkey]
      apply Finset.dvd_sum
      intro e he
      have hem : e ∣ m := (Nat.mem_divisors.mp he).1
      have hpe : ¬ p ∣ e := fun h => hpm (h.trans hem)
      have hdvd := hgauss p r e hp hr1 hpe
      have heq : (μ (m / e) : ℤ) * w (e * p ^ r) - (μ (m / e) : ℤ) * w (e * p ^ (r - 1)) =
          (μ (m / e) : ℤ) * (w (e * p ^ r) - w (e * p ^ (r - 1))) := by ring
      rw [heq]
      exact Dvd.dvd.mul_left hdvd _
    have hfinal : (p : ℤ) ^ k ∣ MTrans w N := (pow_dvd_pow (p : ℤ) hrk).trans hprM
    rwa [← Int.ofNat_dvd_left, Nat.cast_pow]

/-- **Theorem `thm:gauss`**: condition (iii) of `thm:euler-integrality` — `∀N≥1, N∣M_N` — is
equivalent to the Gauss congruence `w_{mp^r} ≡ w_{mp^{r-1}} (mod p^r)` for every prime `p`,
`r≥1`, `m≥1` with `p∤m`. -/
theorem gauss_iff (w : ℕ → ℤ) :
    (∀ N : ℕ, 0 < N → (N : ℤ) ∣ MTrans w N) ↔
      (∀ p r m : ℕ, p.Prime → 1 ≤ r → 1 ≤ m → ¬ p ∣ m →
        (p : ℤ) ^ r ∣ (w (m * p ^ r) - w (m * p ^ (r - 1)))) := by
  constructor
  · intro hyp p r m hp hr hm hpm
    exact gauss_of_dvd_forall w hyp p m r hp hpm hm hr
  · intro hgauss N hN
    exact dvd_forall_of_gauss w (fun p r m hp hr hpm => hgauss p r m hp hr (by
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0; simp at hpm
      · omega) hpm) N hN.ne'

end CongruenceTheory
