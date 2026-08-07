import Mathlib
import CongruenceTheory.Centralizer
import CongruenceTheory.OrbitSum

/-!
**Theorem `thm:strong`** ("Strong two-adic lifting"), permutation-native
form: final assembly from the orbit-bound valuation lemma, the
centralizer-in-`H` bound, and the general class-sum divisibility engine.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm Nat

open scoped Classical

/-- For every `g` outside `H`, the size of its `H`-conjugation class is
divisible by `2^(2s-1)`, where `n = 2^s`. This is the heart of the orbit
proof: combine `v2_stabilizer_le` (the centralizer bound) with
`orbit_bound` (the numerical valuation lemma) via the exact orbit-stabilizer
identity `class_card_mul_stabilizer_card`. -/
theorem class_card_dvd (s : ℕ) (hs : 1 ≤ s) (g : Equiv.Perm (Fin (2 ^ s) ⊕ Fin (2 ^ s)))
    (hg : g ∈ (HSet (2 ^ s))ᶜ) :
    (2 : ℕ) ^ (2 * s - 1) ∣ (Finset.univ.filter ((orbRel (2 ^ s)).r g)).card := by
  have hgH : g ∉ Hgrp (2 ^ s) := by
    rw [mem_Hgrp_iff]; simpa using hg
  have ha1 : 1 ≤ aCard g := one_le_aCard g hgH
  have hb1 : 1 ≤ bCard g := one_le_bCard g hgH
  have han : aCard g ≤ 2 ^ s := aCard_le g
  have hbn : bCard g ≤ 2 ^ s := bCard_le g
  have hcent := v2_stabilizer_le g
  have horbit := orbit_bound s (aCard g) (bCard g) hs ha1 han hb1 hbn
  have hprod := class_card_mul_stabilizer_card (2 ^ s) g
  have hstabne : Fintype.card ↥(MulAction.stabilizer ↥(Hgrp (2 ^ s)) g) ≠ 0 := by
    have : Nonempty ↥(MulAction.stabilizer ↥(Hgrp (2 ^ s)) g) := ⟨1, Subgroup.one_mem _⟩
    exact Fintype.card_ne_zero
  have hstab_eq : Nat.card ↥(MulAction.stabilizer ↥(Hgrp (2 ^ s)) g) =
      Fintype.card ↥(MulAction.stabilizer ↥(Hgrp (2 ^ s)) g) := Nat.card_eq_fintype_card
  rw [hstab_eq] at hcent
  have hclassne : (Finset.univ.filter ((orbRel (2 ^ s)).r g)).card ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact Nat.factorial_ne_zero _ (by
      have := hprod
      nlinarith [Nat.factorial_pos (2 ^ s)])
  have hval : v2 (Fintype.card ↥(MulAction.stabilizer ↥(Hgrp (2 ^ s)) g)) +
      v2 (Finset.univ.filter ((orbRel (2 ^ s)).r g)).card = 2 * v2 ((2 ^ s)!) := by
    have hfa := congrArg (fun x => x.factorization 2) hprod
    simp only [v2] at hcent ⊢
    rw [Nat.factorization_mul hclassne hstabne] at hfa
    rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at hfa
    simp only [Finsupp.coe_add, Pi.add_apply] at hfa
    omega
  have h2s1 : 2 * s - 1 ≤ v2 (Finset.univ.filter ((orbRel (2 ^ s)).r g)).card := by omega
  have := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hclassne).mpr h2s1
  simpa [v2] using this

lemma mem_compl_of_orbRel {n : ℕ} {g g' : Equiv.Perm (Fin n ⊕ Fin n)}
    (hg : g ∈ (HSet n)ᶜ) (hr : (orbRel n).r g' g) : g' ∈ (HSet n)ᶜ := by
  obtain ⟨h, rfl⟩ := hr
  exact compl_HSet_invariant n h g hg

lemma filter_compl_eq_filter_univ {n : ℕ} {g : Equiv.Perm (Fin n ⊕ Fin n)}
    (hg : g ∈ (HSet n)ᶜ) :
    (HSet n)ᶜ.filter ((orbRel n).r g) = Finset.univ.filter ((orbRel n).r g) := by
  ext g'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  exact fun hr => mem_compl_of_orbRel hg ((orbRel n).iseqv.symm hr)

/-- **Theorem `thm:strong`** ("Strong two-adic lifting"), permutation-native form:
`CpermSum(2^s) ≡ Cperm(2^s)^2 (mod 2^(2s-1))` for `s ≥ 1`. -/
theorem strong_two_adic (s : ℕ) (hs : 1 ≤ s) :
    ∃ Q : MvPolynomial ℕ ℤ,
      CpermSum (2 ^ s) - Cperm (2 ^ s) * Cperm (2 ^ s) =
        ((2 ^ (2 * s - 1) : ℕ) : MvPolynomial ℕ ℤ) * Q := by
  have hmain := dvd_sum_of_const_on_classes (orbRel (2 ^ s)).r
    (fun x => (orbRel (2 ^ s)).iseqv.refl x)
    (fun x y h => (orbRel (2 ^ s)).iseqv.symm h)
    (fun x y z h1 h2 => (orbRel (2 ^ s)).iseqv.trans h1 h2)
    ci (fun x y h => ci_const_on_orbit (2 ^ s) x y h) (2 ^ (2 * s - 1)) (HSet (2 ^ s))ᶜ
    (fun x hx => by
      rw [filter_compl_eq_filter_univ hx]
      exact_mod_cast class_card_dvd s hs x hx)
  obtain ⟨Q, hQ⟩ := hmain
  refine ⟨Q, ?_⟩
  rw [CpermSum_sub_Cperm_sq, hQ]

end CongruenceTheory
