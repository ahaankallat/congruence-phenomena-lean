import Mathlib
import CongruenceTheory.CoeffExtraction

/-!
**Proposition `prop:content-bounds`** (unconditional content bounds), upper
half: the coefficient of `X_1^{n+k-2}X_2` in `C_{n+k} - C_n C_k` is exactly
`nk`, computed for the permutation-native `Cperm`/`CpermPair`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm MvPolynomial Nat

open scoped Classical

/-- The permutation-native cycle-index sum on the disjoint-union domain `Fin n ⊕ Fin k`
(possibly unequal sizes). -/
noncomputable def CpermPair (n k : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ g : Equiv.Perm (Fin n ⊕ Fin k), ci g

/-- **Generalized `Cperm_sq`**: `Cperm n * Cperm k = ∑_{(σ,τ)} ci (sumCongr σ τ)`. -/
theorem Cperm_mul (n k : ℕ) :
    Cperm n * Cperm k =
      ∑ p : Equiv.Perm (Fin n) × Equiv.Perm (Fin k), ci (Equiv.Perm.sumCongr p.1 p.2) := by
  simp only [Cperm, Finset.sum_mul_sum, ← ci_sumCongr]
  symm
  exact Fintype.sum_prod_type
    (f := fun p : Equiv.Perm (Fin n) × Equiv.Perm (Fin k) =>
      ci (Equiv.Perm.sumCongr p.1 p.2))

/-- Additivity of `ciExp` under multiset addition. -/
lemma ciExp_add (a a' : ℕ) (m m' : Multiset ℕ) :
    ciExp a m + ciExp a' m' = ciExp (a + a') (m + m') := by
  ext j
  simp only [Finsupp.add_apply, ciExp_apply, Multiset.count_add]
  by_cases hj : j = 1 <;> simp [hj] <;> omega

/-- A multiset sum of two multisets equals a singleton iff exactly one summand is that
singleton and the other is empty. -/
lemma multiset_add_eq_singleton_iff {A B : Multiset ℕ} {x : ℕ} :
    A + B = {x} ↔ (A = {x} ∧ B = 0) ∨ (A = 0 ∧ B = {x}) := by
  constructor
  · intro h
    have hcard : Multiset.card A + Multiset.card B = 1 := by
      rw [← Multiset.card_add, h]; simp
    have hcase : Multiset.card A = 0 ∨ Multiset.card A = 1 := by omega
    rcases hcase with hA | hA
    · right
      have hA0 : A = 0 := Multiset.card_eq_zero.mp hA
      refine ⟨hA0, ?_⟩
      rw [hA0, zero_add] at h
      exact h
    · left
      obtain ⟨a, hAa⟩ := Multiset.card_eq_one.mp hA
      have hB0 : B = 0 := Multiset.card_eq_zero.mp (by omega)
      rw [hAa, hB0, add_zero] at h
      have hax : a = x := Multiset.mem_singleton.mp (h ▸ Multiset.mem_singleton_self a)
      rw [hAa, hax]
      exact ⟨rfl, hB0⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- The indicator (as a `Finset.card`) of cycle type `{2}` inside `Perm (Fin n)`, i.e.
`C(n,2)` for `n ≥ 2` and `0` otherwise. -/
noncomputable def twoCycleCount (n : ℕ) : ℤ :=
  ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.cycleType = {2})).card : ℤ)

lemma coeff_ci_sumCongr_target {n k : ℕ} (p : Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) :
    MvPolynomial.coeff (ciExp (n + k - 2) {2}) (ci (Equiv.Perm.sumCongr p.1 p.2)) =
      (if p.1.cycleType = {2} ∧ p.2.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0) +
      (if p.1.cycleType = (0 : Multiset ℕ) ∧ p.2.cycleType = {2} then (1 : ℤ) else 0) := by
  rw [ci_sumCongr, ci_eq_monomial, ci_eq_monomial, MvPolynomial.monomial_mul, one_mul,
    MvPolynomial.coeff_monomial]
  have hn : p.1.cycleType.sum ≤ n := by
    have := Equiv.Perm.sum_cycleType_le p.1; simpa using this
  have hk : p.2.cycleType.sum ≤ k := by
    have := Equiv.Perm.sum_cycleType_le p.2; simpa using this
  have hgne : ∀ x ∈ p.1.cycleType, x ≠ 1 := fun x hx => by
    have := Equiv.Perm.two_le_of_mem_cycleType hx; omega
  have hgne' : ∀ x ∈ p.2.cycleType, x ≠ 1 := fun x hx => by
    have := Equiv.Perm.two_le_of_mem_cycleType hx; omega
  have hgnesum : ∀ x ∈ p.1.cycleType + p.2.cycleType, x ≠ 1 := by
    intro x hx
    rw [Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact hgne x hx
    · exact hgne' x hx
  have h2ne : ∀ x ∈ ({2} : Multiset ℕ), x ≠ 1 := by intro x hx; simp at hx; omega
  have key : (ciExp (n - p.1.cycleType.sum) p.1.cycleType +
      ciExp (k - p.2.cycleType.sum) p.2.cycleType = ciExp (n + k - 2) ({2} : Multiset ℕ)) ↔
      (p.1.cycleType = {2} ∧ p.2.cycleType = (0 : Multiset ℕ)) ∨
        (p.1.cycleType = (0 : Multiset ℕ) ∧ p.2.cycleType = {2}) := by
    rw [ciExp_add, ciExp_eq_iff hgnesum h2ne, ← multiset_add_eq_singleton_iff]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have hsum2 : p.1.cycleType.sum + p.2.cycleType.sum = 2 := by
        have := congrArg Multiset.sum h; simpa using this
      omega
  simp only [key]
  by_cases h1 : p.1.cycleType = {2} ∧ p.2.cycleType = (0 : Multiset ℕ)
  · have h2 : ¬ (p.1.cycleType = (0 : Multiset ℕ) ∧ p.2.cycleType = {2}) := by
      rintro ⟨h2a, -⟩
      rw [h1.1] at h2a
      exact absurd h2a (by decide)
    rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]; ring
  · by_cases h2 : p.1.cycleType = (0 : Multiset ℕ) ∧ p.2.cycleType = {2}
    · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]; ring
    · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2]; ring

lemma card_cycleType_zero (N : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => σ.cycleType = (0 : Multiset ℕ))).card
      = 1 := by
  have : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => σ.cycleType = (0 : Multiset ℕ))) =
      {1} := by
    ext σ
    simp [Equiv.Perm.cycleType_eq_zero]
  rw [this]; simp

/-- The coefficient of `X_1^{n+k-2}X_2` in `Cperm n * Cperm k` is `C(n,2) + C(k,2)`. -/
theorem coeff_Cperm_mul (n k : ℕ) :
    MvPolynomial.coeff (ciExp (n + k - 2) {2}) (Cperm n * Cperm k) =
      twoCycleCount n + twoCycleCount k := by
  rw [Cperm_mul, MvPolynomial.coeff_sum]
  have hpt : ∀ p : Equiv.Perm (Fin n) × Equiv.Perm (Fin k),
      MvPolynomial.coeff (ciExp (n + k - 2) {2}) (ci (Equiv.Perm.sumCongr p.1 p.2)) =
      (if p.1.cycleType = ({2} : Multiset ℕ) then (1 : ℤ) else 0) *
        (if p.2.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0) +
      (if p.1.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0) *
        (if p.2.cycleType = ({2} : Multiset ℕ) then (1 : ℤ) else 0) := by
    intro p
    rw [coeff_ci_sumCongr_target]
    by_cases h1 : p.1.cycleType = ({2} : Multiset ℕ) <;>
      by_cases h2 : p.2.cycleType = (0 : Multiset ℕ) <;>
      by_cases h3 : p.1.cycleType = (0 : Multiset ℕ) <;>
      by_cases h4 : p.2.cycleType = ({2} : Multiset ℕ) <;>
      simp_all
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
  dsimp only
  have e1 : (∑ x : Equiv.Perm (Fin n), (if x.cycleType = ({2} : Multiset ℕ) then (1 : ℤ) else 0)) *
      (∑ y : Equiv.Perm (Fin k), (if y.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0)) =
      ∑ x : Equiv.Perm (Fin n), ∑ y : Equiv.Perm (Fin k),
        (if x.cycleType = {2} then (1 : ℤ) else 0) * (if y.cycleType = 0 then (1 : ℤ) else 0) :=
    Finset.sum_mul_sum Finset.univ Finset.univ _ _
  have e2 : (∑ x : Equiv.Perm (Fin n), (if x.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0)) *
      (∑ y : Equiv.Perm (Fin k), (if y.cycleType = ({2} : Multiset ℕ) then (1 : ℤ) else 0)) =
      ∑ x : Equiv.Perm (Fin n), ∑ y : Equiv.Perm (Fin k),
        (if x.cycleType = 0 then (1 : ℤ) else 0) * (if y.cycleType = {2} then (1 : ℤ) else 0) :=
    Finset.sum_mul_sum Finset.univ Finset.univ _ _
  rw [← e1, ← e2]
  have hz1 : (∑ x : Equiv.Perm (Fin n), (if x.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0))
      = 1 := by
    have heq : (∑ x : Equiv.Perm (Fin n), (if x.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0))
        = ((Finset.univ.filter (fun x : Equiv.Perm (Fin n) => x.cycleType = 0)).card : ℤ) := by
      rw [Finset.card_filter]; push_cast; rfl
    rw [heq, card_cycleType_zero]; norm_num
  have hz2 : (∑ y : Equiv.Perm (Fin k), (if y.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0))
      = 1 := by
    have heq : (∑ y : Equiv.Perm (Fin k), (if y.cycleType = (0 : Multiset ℕ) then (1 : ℤ) else 0))
        = ((Finset.univ.filter (fun y : Equiv.Perm (Fin k) => y.cycleType = 0)).card : ℤ) := by
      rw [Finset.card_filter]; push_cast; rfl
    rw [heq, card_cycleType_zero]; norm_num
  rw [hz1, hz2, mul_one, one_mul]
  simp only [twoCycleCount, Finset.card_filter]
  push_cast
  ring

/-- **`ci_eq_monomial`, general ambient type version.** -/
lemma ci_eq_monomial' {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    ci g = MvPolynomial.monomial (ciExp (Fintype.card α - g.cycleType.sum) g.cycleType)
      (1 : ℤ) := by
  unfold ci
  rw [pow_mul_multisetProd_eq_monomial]

/-- **Coefficient extraction, general ambient type version.** -/
theorem coeff_sum_ci_eq_card_cycleType {α : Type*} [Fintype α] [DecidableEq α]
    (m : Multiset ℕ) (hm2 : ∀ x ∈ m, 2 ≤ x) :
    MvPolynomial.coeff (ciExp (Fintype.card α - m.sum) m) (∑ g : Equiv.Perm α, ci g) =
      ((Finset.univ.filter (fun g : Equiv.Perm α => g.cycleType = m)).card : ℤ) := by
  rw [MvPolynomial.coeff_sum]
  have hcast : ((Finset.univ.filter (fun g : Equiv.Perm α => g.cycleType = m)).card : ℤ) =
      ∑ g : Equiv.Perm α, (if g.cycleType = m then (1 : ℤ) else 0) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hcast]
  apply Finset.sum_congr rfl
  intro g _
  rw [ci_eq_monomial', MvPolynomial.coeff_monomial]
  have hgne : ∀ x ∈ g.cycleType, x ≠ 1 := fun x hx => by
    have := Equiv.Perm.two_le_of_mem_cycleType hx; omega
  have hmne : ∀ x ∈ m, x ≠ 1 := fun x hx => by have := hm2 x hx; omega
  by_cases hgm : g.cycleType = m
  · simp [hgm]
  · have hne : ciExp (Fintype.card α - g.cycleType.sum) g.cycleType ≠
        ciExp (Fintype.card α - m.sum) m := by
      intro hcontra
      exact hgm ((ciExp_eq_iff hgne hmne).mp hcontra).2
    simp [hne, Ne.symm hne, hgm]

/-- The coefficient of `X_1^{n+k-2}X_2` in `CpermPair n k` is `C(n+k,2)`. -/
theorem coeff_CpermPair (n k : ℕ) :
    MvPolynomial.coeff (ciExp (n + k - 2) {2}) (CpermPair n k) =
      ((Finset.univ.filter
        (fun g : Equiv.Perm (Fin n ⊕ Fin k) => g.cycleType = ({2} : Multiset ℕ))).card : ℤ) := by
  have hcard : Fintype.card (Fin n ⊕ Fin k) = n + k := by simp
  have := coeff_sum_ci_eq_card_cycleType (α := Fin n ⊕ Fin k) ({2} : Multiset ℕ) (by
    intro x hx; simp at hx; omega)
  rw [hcard] at this
  exact this

/-- The number of `2`-cycles (transpositions) among `Perm α` equals `C(N,2)` where
`N = Fintype.card α`. -/
theorem card_twoCycle_eq_choose {α : Type*} [Fintype α] [DecidableEq α] :
    (Finset.univ.filter (fun g : Equiv.Perm α => g.cycleType = ({2} : Multiset ℕ))).card =
      (Fintype.card α).choose 2 := by
  have hcard := Equiv.Perm.card_of_cycleType α ({2} : Multiset ℕ)
  rw [show (Finset.univ.filter (fun σ : Equiv.Perm α => σ.cycleType = {2})) =
      ({g : Equiv.Perm α | g.cycleType = {2}} : Finset (Equiv.Perm α)) from rfl,
    hcard]
  by_cases hN : 2 ≤ Fintype.card α
  · rw [if_pos (by simp [hN]), Nat.choose_eq_factorial_div_factorial hN]
    simp only [Multiset.sum_singleton, Multiset.prod_singleton, Multiset.toFinset_singleton,
      Finset.prod_singleton, Multiset.count_singleton_self, Nat.factorial_one]
    have hdenom : (Fintype.card α - 2)! * 2 * 1 = (2 : ℕ)! * (Fintype.card α - 2)! := by
      norm_num [Nat.factorial]
      ring
    rw [hdenom]
  · rw [if_neg (by simp [hN]), Nat.choose_eq_zero_of_lt (by omega)]

theorem two_mul_card_twoCycle {α : Type*} [Fintype α] [DecidableEq α] :
    2 * ((Finset.univ.filter (fun g : Equiv.Perm α => g.cycleType = ({2} : Multiset ℕ))).card :
      ℤ) = (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 1) := by
  rw [card_twoCycle_eq_choose]
  have heq2 : 2 * ((Fintype.card α).choose 2) = (Fintype.card α) * (Fintype.card α - 1) := by
    rw [Nat.choose_two_right, mul_comm 2,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (Fintype.card α))]
  have hcast : (2 : ℤ) * ((Fintype.card α).choose 2 : ℤ) =
      ((Fintype.card α) * (Fintype.card α - 1) : ℕ) := by exact_mod_cast heq2
  rw [hcast]
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
  · simp [h]
  · push_cast [Nat.cast_sub h]
    ring

theorem two_mul_twoCycleCount (N : ℕ) : 2 * twoCycleCount N = (N : ℤ) * ((N : ℤ) - 1) := by
  have h := two_mul_card_twoCycle (α := Fin N)
  rw [Fintype.card_fin] at h
  rw [show twoCycleCount N = ((Finset.univ.filter
      (fun g : Equiv.Perm (Fin N) => g.cycleType = ({2} : Multiset ℕ))).card : ℤ) from rfl]
  exact h

/-- **`prop:content-bounds`, upper half.** The coefficient of `X_1^{n+k-2}X_2` in
`C_{n+k} - C_n C_k` (permutation-native) is exactly `nk`. -/
theorem coeff_defect_eq_nk (n k : ℕ) :
    MvPolynomial.coeff (ciExp (n + k - 2) {2}) (CpermPair n k - Cperm n * Cperm k) =
      (n : ℤ) * k := by
  rw [MvPolynomial.coeff_sub, coeff_CpermPair, coeff_Cperm_mul]
  have hpair := two_mul_card_twoCycle (α := Fin n ⊕ Fin k)
  simp only [Fintype.card_sum, Fintype.card_fin] at hpair
  have key : 2 * (((Finset.univ.filter
      (fun g : Equiv.Perm (Fin n ⊕ Fin k) => g.cycleType = ({2} : Multiset ℕ))).card : ℤ) -
      (twoCycleCount n + twoCycleCount k)) = 2 * ((n : ℤ) * k) := by
    rw [mul_sub, hpair, mul_add, two_mul_twoCycleCount, two_mul_twoCycleCount]
    push_cast
    ring
  have h2 : (2 : ℤ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ h2 key

end CongruenceTheory
