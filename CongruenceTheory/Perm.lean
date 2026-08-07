import Mathlib

/-!
Permutation-native cycle-index polynomials, and the algebraic gluing lemma
relating `sumCongr` to disjoint unions of cycle type, needed for
Theorem `thm:strong`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm MvPolynomial

/-- The cycle-indicator monomial of a permutation: `X_1^(fixed points) * ∏ X_ℓ` over its
(non-trivial) cycle lengths `ℓ`, matching the manuscript's `[X^λ]` convention where `λ`
includes fixed points as length-`1` cycles. -/
noncomputable def ci {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    MvPolynomial ℕ ℤ :=
  X 1 ^ (Fintype.card α - g.cycleType.sum) * (g.cycleType.map X).prod

/-- The permutation-native cycle-index polynomial on `n` labels. -/
noncomputable def Cperm (n : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ g : Equiv.Perm (Fin n), ci g

lemma ci_conj {α : Type*} [Fintype α] [DecidableEq α] (h g : Equiv.Perm α) :
    ci (h * g * h⁻¹) = ci g := by
  simp [ci, Equiv.Perm.cycleType_conj]

/-- `sumCongr σ 1` has the same cycle type as `σ`, via `extendDomain`. -/
lemma cycleType_sumCongr_one_right {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (σ : Equiv.Perm m) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm n)).cycleType = σ.cycleType := by
  set f : m ≃ Subtype (· ∈ Set.range (Sum.inl : m → m ⊕ n)) :=
    Equiv.ofInjective Sum.inl Sum.inl_injective with hf
  have hext : σ.extendDomain f = Equiv.Perm.sumCongr σ (1 : Equiv.Perm n) := by
    ext x
    cases x with
    | inl a =>
      have himg : (f a : m ⊕ n) = Sum.inl a := rfl
      rw [← himg, Equiv.Perm.extendDomain_apply_image]
      rfl
    | inr b =>
      have hnp : (Sum.inr b : m ⊕ n) ∉ Set.range (Sum.inl : m → m ⊕ n) := by
        rintro ⟨a, ha⟩; cases ha
      rw [Equiv.Perm.extendDomain_apply_not_subtype σ f hnp]
      simp
  rw [← hext, Equiv.Perm.cycleType_extendDomain]

/-- `sumCongr 1 τ` has the same cycle type as `τ`, via `extendDomain`. -/
lemma cycleType_sumCongr_one_left {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (τ : Equiv.Perm n) :
    (Equiv.Perm.sumCongr (1 : Equiv.Perm m) τ).cycleType = τ.cycleType := by
  set f : n ≃ Subtype (· ∈ Set.range (Sum.inr : n → m ⊕ n)) :=
    Equiv.ofInjective Sum.inr Sum.inr_injective with hf
  have hext : τ.extendDomain f = Equiv.Perm.sumCongr (1 : Equiv.Perm m) τ := by
    ext x
    cases x with
    | inr b =>
      have himg : (f b : m ⊕ n) = Sum.inr b := rfl
      rw [← himg, Equiv.Perm.extendDomain_apply_image]
      rfl
    | inl a =>
      have hnp : (Sum.inl a : m ⊕ n) ∉ Set.range (Sum.inr : n → m ⊕ n) := by
        rintro ⟨b, hb⟩; cases hb
      rw [Equiv.Perm.extendDomain_apply_not_subtype τ f hnp]
      simp
  rw [← hext, Equiv.Perm.cycleType_extendDomain]

/-- The two factors `sumCongr σ 1` and `sumCongr 1 τ` are disjoint permutations. -/
lemma disjoint_sumCongr_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (σ : Equiv.Perm m) (τ : Equiv.Perm n) :
    Equiv.Perm.Disjoint (Equiv.Perm.sumCongr σ (1 : Equiv.Perm n))
      (Equiv.Perm.sumCongr (1 : Equiv.Perm m) τ) := by
  intro x
  cases x with
  | inl a => right; simp
  | inr b => left; simp

/-- **Cycle-type gluing**: `cycleType (sumCongr σ τ) = cycleType σ + cycleType τ`. -/
theorem cycleType_sumCongr {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (σ : Equiv.Perm m) (τ : Equiv.Perm n) :
    (Equiv.Perm.sumCongr σ τ).cycleType = σ.cycleType + τ.cycleType := by
  have hmul : Equiv.Perm.sumCongr σ τ =
      Equiv.Perm.sumCongr σ (1 : Equiv.Perm n) * Equiv.Perm.sumCongr (1 : Equiv.Perm m) τ := by
    ext x
    cases x with
    | inl a => simp
    | inr b => simp
  rw [hmul, (disjoint_sumCongr_one σ τ).cycleType_mul, cycleType_sumCongr_one_right,
    cycleType_sumCongr_one_left]

/-- **Monomial multiplicativity**: `ci (sumCongr σ τ) = ci σ * ci τ`. -/
theorem ci_sumCongr {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (σ : Equiv.Perm m) (τ : Equiv.Perm n) :
    ci (Equiv.Perm.sumCongr σ τ) = ci σ * ci τ := by
  have hcard : Fintype.card (m ⊕ n) = Fintype.card m + Fintype.card n := Fintype.card_sum
  have hle1 : σ.cycleType.sum ≤ Fintype.card m := Equiv.Perm.sum_cycleType_le σ
  have hle2 : τ.cycleType.sum ≤ Fintype.card n := Equiv.Perm.sum_cycleType_le τ
  simp only [ci, cycleType_sumCongr, Multiset.sum_add, Multiset.map_add, Multiset.prod_add,
    hcard]
  rw [show Fintype.card m + Fintype.card n - (σ.cycleType.sum + τ.cycleType.sum) =
      (Fintype.card m - σ.cycleType.sum) + (Fintype.card n - τ.cycleType.sum) by omega,
    pow_add]
  ring

/-- The permutation-native cycle-index polynomial on a `2n`-label domain, modeled as
`Fin n ⊕ Fin n`. -/
noncomputable def CpermSum (n : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ g : Equiv.Perm (Fin n ⊕ Fin n), ci g

theorem Cperm_sq (n : ℕ) :
    Cperm n * Cperm n =
      ∑ p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n), ci (Equiv.Perm.sumCongr p.1 p.2) := by
  simp only [Cperm, Finset.sum_mul_sum, ← ci_sumCongr]
  symm
  exact Fintype.sum_prod_type
    (f := fun p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) => ci (Equiv.Perm.sumCongr p.1 p.2))

/-- The subgroup `H = Perm A × Perm B` embedded in `Perm (Fin n ⊕ Fin n)`, as a `Finset`. -/
noncomputable def HSet (n : ℕ) : Finset (Equiv.Perm (Fin n ⊕ Fin n)) :=
  Finset.univ.filter (· ∈ (Equiv.Perm.sumCongrHom (Fin n) (Fin n)).range)

theorem Cperm_sq_eq_sum_HSet (n : ℕ) :
    Cperm n * Cperm n = ∑ g ∈ HSet n, ci g := by
  rw [Cperm_sq]
  apply Finset.sum_bij (fun p _ => Equiv.Perm.sumCongrHom (Fin n) (Fin n) p)
  · intro p _
    simp only [HSet, Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_range]
    exact ⟨p, rfl⟩
  · intro p₁ _ p₂ _ h
    exact Equiv.Perm.sumCongrHom_injective h
  · intro g hg
    simp only [HSet, Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_range] at hg
    obtain ⟨p, rfl⟩ := hg
    exact ⟨p, Finset.mem_univ p, rfl⟩
  · intro p _
    rw [Equiv.Perm.sumCongrHom_apply]

theorem sum_univ_eq_sum_HSet_add_sum_compl (n : ℕ) :
    ∑ g : Equiv.Perm (Fin n ⊕ Fin n), ci g = (∑ g ∈ HSet n, ci g) + ∑ g ∈ (HSet n)ᶜ, ci g := by
  have hdisj : Disjoint (HSet n) (HSet n)ᶜ := by
    rw [Finset.disjoint_left]
    intro g hg
    simp [Finset.mem_compl, hg]
  rw [← Finset.sum_union hdisj, Finset.union_compl]

theorem CpermSum_sub_Cperm_sq (n : ℕ) :
    CpermSum n - Cperm n * Cperm n = ∑ g ∈ (HSet n)ᶜ, ci g := by
  rw [Cperm_sq_eq_sum_HSet, CpermSum, sum_univ_eq_sum_HSet_add_sum_compl]
  ring

end CongruenceTheory
