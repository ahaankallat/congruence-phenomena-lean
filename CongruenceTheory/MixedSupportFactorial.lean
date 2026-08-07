import Mathlib

/-!
**Lemma `lem:mixed-support-factorial`**: a pure number-theory building block for
`thm:optimal-divisor`. For a prime `p` with `p^a ∣ n` and `p^b ∣ k`, and `1 ≤ r ≤ n`,
`1 ≤ s ≤ k`,
`v_p(n! k! / ((n-r)! (k-s)!)) - min(v_p(r!), v_p(s!)) ≥ a + b - 1`.

Formalized additively (via descending factorials) to avoid truncated-subtraction and
division pitfalls: `v_p((n)_r) + v_p((k)_s) ≥ a + b - 1 + min(v_p(r!), v_p(s!))`, where
`(n)_r = n!/(n-r)! = n.descFactorial r`.
-/

namespace CongruenceTheory

open Nat

/-- `v_p((p^c)!) ≥ 2c - 1` for `c ≥ 1` (additive form avoiding subtraction:
`2c ≤ v_p((p^c)!) + 1`). The numerical engine behind the sub-lemma below. -/
theorem padicValNat_factorial_pow_ge (p : ℕ) (hp : p.Prime) :
    ∀ c : ℕ, 1 ≤ c → 2 * c ≤ padicValNat p ((p ^ c)!) + 1 := by
  haveI := Fact.mk hp
  intro c hc
  induction c with
  | zero => omega
  | succ c ih =>
    rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · subst hc0
      have h1 : padicValNat p ((p ^ 1)!) = padicValNat p (1 !) + 1 := by
        have := padicValNat_factorial_mul (p := p) 1
        simpa using this
      simp only [pow_one] at h1
      simp [h1]
    · have hstep : padicValNat p ((p ^ (c + 1))!) = padicValNat p ((p ^ c)!) + p ^ c := by
        have := padicValNat_factorial_mul (p := p) (p ^ c)
        rwa [← pow_succ'] at this
      have hpc2 : 2 ≤ p ^ c := by
        calc (2:ℕ) ≤ p ^ 1 := by simpa using hp.two_le
          _ ≤ p ^ c := Nat.pow_le_pow_right hp.one_lt.le hc0
      have := ih hc0
      omega

/-- `v_p(m!)` is monotone in `m`. -/
theorem padicValNat_factorial_mono (p : ℕ) (hp : p.Prime) {m n : ℕ} (h : m ≤ n) :
    padicValNat p (m !) ≤ padicValNat p (n !) := by
  haveI := Fact.mk hp
  obtain ⟨t, ht⟩ := factorial_dvd_factorial h
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, mul_zero] at ht; exact factorial_ne_zero n ht
  rw [ht, padicValNat.mul (factorial_ne_zero m) ht0]
  omega

/-- The crux sub-lemma (extracted from the manuscript's proof of
`lem:mixed-support-factorial`): if `v_p(r!) ≤ v_p(s!)` then `v_p(r) ≤ v_p((s-1)!) + 1`. -/
theorem padicValNat_le_padicValNat_pred_factorial_add_one (p : ℕ) (hp : p.Prime) {r s : ℕ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : padicValNat p (r !) ≤ padicValNat p (s !)) :
    padicValNat p r ≤ padicValNat p ((s - 1)!) + 1 := by
  haveI := Fact.mk hp
  by_contra hcon
  push Not at hcon
  set c := padicValNat p r with hc
  have hc2 : 2 ≤ c := by omega
  have hpcr : p ^ c ∣ r := pow_padicValNat_dvd
  have hrpc : p ^ c ≤ r := Nat.le_of_dvd hr hpcr
  have hstep2 : padicValNat p ((p ^ c)!) ≤ padicValNat p (r !) :=
    padicValNat_factorial_mono p hp hrpc
  have hstep3 := padicValNat_factorial_pow_ge p hp c (by omega)
  have hsfact : padicValNat p (s !) = padicValNat p s + padicValNat p ((s - 1)!) := by
    have hseq : s ! = s * (s - 1)! := by
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      simp [Nat.factorial_succ]
    rw [hseq, padicValNat.mul (by omega) (factorial_ne_zero _)]
  have hsm1 : padicValNat p ((s - 1)!) ≤ c - 2 := by omega
  have hsu : s - 1 < p ^ (c - 1) := by
    by_contra hge
    push Not at hge
    have hmono := padicValNat_factorial_mono p hp hge
    have hgrow := padicValNat_factorial_pow_ge p hp (c - 1) (by omega)
    omega
  have hsle : s ≤ p ^ (c - 1) := by omega
  have hps : p ^ (padicValNat p s) ∣ s := pow_padicValNat_dvd
  have hps' : p ^ (padicValNat p s) ≤ s := Nat.le_of_dvd hs hps
  have hple : p ^ (padicValNat p s) ≤ p ^ (c - 1) := hps'.trans hsle
  have hvs : padicValNat p s ≤ c - 1 :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mp hple
  omega

/-- **Lemma `lem:mixed-support-factorial`**, in descending-factorial form, under the extra
hypothesis `v_p(r!) ≤ v_p(s!)` (the general statement below removes this via symmetry). -/
theorem mixed_support_factorial_le (p : ℕ) (hp : p.Prime) {n k a b r s : ℕ}
    (hpa : p ^ a ∣ n) (hpb : p ^ b ∣ k) (hr : 1 ≤ r) (hrn : r ≤ n) (hs : 1 ≤ s) (hsk : s ≤ k)
    (hle : padicValNat p (r !) ≤ padicValNat p (s !)) :
    a + b + min (padicValNat p (r !)) (padicValNat p (s !)) ≤
      padicValNat p (n.descFactorial r) + padicValNat p (k.descFactorial s) + 1 := by
  haveI := Fact.mk hp
  rw [min_eq_left hle]
  have han : a ≤ padicValNat p n := by
    rcases eq_or_ne n 0 with rfl | hn0
    · omega
    · exact (padicValNat_dvd_iff_le hn0).mp hpa
  -- v_p(C(n,r)) ≥ v_p(n) - v_p(r), via Mathlib's Kummer-type bound
  have hchoose_n : n.factorization p ≤ (n.choose r).factorization p + r.factorization p :=
    Nat.factorization_le_factorization_choose_add hrn (by omega)
  rw [Nat.factorization_def n hp, Nat.factorization_def (n.choose r) hp,
    Nat.factorization_def r hp] at hchoose_n
  -- (n)_r = r! * C(n,r), so v_p((n)_r) = v_p(r!) + v_p(C(n,r)) ≥ v_p(r!) + v_p(n) - v_p(r) ≥ a
  have hdescn : n.descFactorial r = r ! * n.choose r :=
    Nat.descFactorial_eq_factorial_mul_choose n r
  have hvdescn : padicValNat p (n.descFactorial r) =
      padicValNat p (r !) + padicValNat p (n.choose r) := by
    rw [hdescn, padicValNat.mul (factorial_ne_zero r) (by
      rw [← Nat.pos_iff_ne_zero]; exact Nat.choose_pos hrn)]
  -- (k-1)_{s-1} = (s-1)! * C(k-1,s-1), and (k)_s = k * (k-1)_{s-1}
  have hdesck : k.descFactorial s = k * (k - 1).descFactorial (s - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simpa using Nat.succ_descFactorial_succ m t
  have hks1 : s - 1 ≤ k - 1 := by omega
  have hvdesck1 : padicValNat p ((k - 1).descFactorial (s - 1)) ≥ padicValNat p ((s - 1)!) := by
    have heq : (k - 1).descFactorial (s - 1) = (s - 1)! * (k - 1).choose (s - 1) :=
      Nat.descFactorial_eq_factorial_mul_choose (k - 1) (s - 1)
    have hposc : 0 < (k - 1).choose (s - 1) := Nat.choose_pos hks1
    rw [heq, padicValNat.mul (factorial_ne_zero _) (by omega)]
    omega
  have hvdeskpos : k ≠ 0 := by omega
  have hvdesck : padicValNat p (k.descFactorial s) =
      padicValNat p k + padicValNat p ((k - 1).descFactorial (s - 1)) := by
    rw [hdesck, padicValNat.mul hvdeskpos (by
      rw [← Nat.pos_iff_ne_zero]; exact Nat.descFactorial_pos.mpr hks1)]
  have hbk : b ≤ padicValNat p k := by
    rcases eq_or_ne k 0 with rfl | hk0
    · omega
    · exact (padicValNat_dvd_iff_le hk0).mp hpb
  have hsub := padicValNat_le_padicValNat_pred_factorial_add_one p hp hr hs hle
  omega

/-- **Lemma `lem:mixed-support-factorial`**, in descending-factorial form. For a prime `p`
with `p^a ∣ n`, `p^b ∣ k`, and `1 ≤ r ≤ n`, `1 ≤ s ≤ k`:
`v_p(n.descFactorial r) + v_p(k.descFactorial s) ≥ a + b - 1 + min(v_p(r!), v_p(s!))`
(stated as `a + b + min(...) ≤ ... + 1` to avoid truncated subtraction). -/
theorem mixed_support_factorial (p : ℕ) (hp : p.Prime) {n k a b r s : ℕ}
    (hpa : p ^ a ∣ n) (hpb : p ^ b ∣ k) (hr : 1 ≤ r) (hrn : r ≤ n) (hs : 1 ≤ s) (hsk : s ≤ k) :
    a + b + min (padicValNat p (r !)) (padicValNat p (s !)) ≤
      padicValNat p (n.descFactorial r) + padicValNat p (k.descFactorial s) + 1 := by
  rcases le_total (padicValNat p (r !)) (padicValNat p (s !)) with hle | hle
  · exact mixed_support_factorial_le p hp hpa hpb hr hrn hs hsk hle
  · have := mixed_support_factorial_le p hp hpb hpa hs hsk hr hrn hle
    rw [min_comm] at this
    omega

end CongruenceTheory
