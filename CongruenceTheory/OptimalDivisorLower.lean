import Mathlib
import CongruenceTheory.CentralizerPair
import CongruenceTheory.OrbitSum

/-!
**`thm:optimal-divisor`, lower bound, general `(n,k,p)`**: final assembly from
`vp_stabilizer_le_pair` (`CentralizerPair.lean`), `mixed_support_factorial`
(`MixedSupportFactorial.lean`), and the class-sum divisibility engine
(`OrbitSum.lean`) — the same three-way combination `StrongTwoAdic.lean` used
for `thm:strong`, now for arbitrary `n, k ≥ 1` and prime `p` instead of just
`n = k = 2^s`, `p = 2`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm Nat MvPolynomial

open scoped Classical

theorem Cperm_mul_eq_sum_HSetPair (n k : ℕ) :
    Cperm n * Cperm k = ∑ g ∈ HSetPair n k, ci g := by
  rw [Cperm_mul]
  apply Finset.sum_bij (fun p _ => Equiv.Perm.sumCongrHom (Fin n) (Fin k) p)
  · intro p _
    simp only [HSetPair, Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_range]
    exact ⟨p, rfl⟩
  · intro p₁ _ p₂ _ h
    exact Equiv.Perm.sumCongrHom_injective h
  · intro g hg
    simp only [HSetPair, Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_range] at hg
    obtain ⟨p, rfl⟩ := hg
    exact ⟨p, Finset.mem_univ p, rfl⟩
  · intro p _
    rw [Equiv.Perm.sumCongrHom_apply]

theorem CpermPair_sub_Cperm_mul (n k : ℕ) :
    CpermPair n k - Cperm n * Cperm k = ∑ g ∈ (HSetPair n k)ᶜ, ci g := by
  have hdisj : Disjoint (HSetPair n k) (HSetPair n k)ᶜ := by
    rw [Finset.disjoint_left]; intro g hg; simp [Finset.mem_compl, hg]
  have hsplit : CpermPair n k = (∑ g ∈ HSetPair n k, ci g) + ∑ g ∈ (HSetPair n k)ᶜ, ci g := by
    rw [CpermPair, ← Finset.sum_union hdisj, Finset.union_compl]
  rw [hsplit, Cperm_mul_eq_sum_HSetPair]
  ring

lemma mem_compl_of_orbRelPair {n k : ℕ} {g g' : Equiv.Perm (Fin n ⊕ Fin k)}
    (hg : g ∈ (HSetPair n k)ᶜ) (hr : (orbRelPair n k).r g' g) : g' ∈ (HSetPair n k)ᶜ := by
  obtain ⟨h, rfl⟩ := hr
  exact compl_HSetPair_invariant n k h g hg

lemma filter_compl_eq_filter_univ_pair {n k : ℕ} {g : Equiv.Perm (Fin n ⊕ Fin k)}
    (hg : g ∈ (HSetPair n k)ᶜ) :
    (HSetPair n k)ᶜ.filter ((orbRelPair n k).r g) = Finset.univ.filter ((orbRelPair n k).r g) := by
  ext g'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  exact fun hr => mem_compl_of_orbRelPair hg ((orbRelPair n k).iseqv.symm hr)

/-- `n.descFactorial a` times `(n-a)!` recovers `n!`, for `a ≤ n`. -/
lemma descFactorial_mul_factorial_sub (n a : ℕ) (ha : a ≤ n) :
    n.descFactorial a * (n - a)! = n ! := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  rw [show a ! * n.choose a * (n - a)! = n.choose a * a ! * (n - a)! by ring]
  exact Nat.choose_mul_factorial_mul_factorial ha

/-- **The lower-bound valuation step**, general `(n,k,p)`: for `g` outside `H`, the size of
its `H`-conjugation class is divisible by `p^(v_p(n)+v_p(k)-1)`. Combines
`vp_stabilizer_le_pair` (the centralizer bound), `mixed_support_factorial` (the
number-theoretic engine), and `class_card_mul_stabilizer_card_pair` (exact orbit-stabilizer). -/
theorem class_card_dvd_pair (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (g : Equiv.Perm (Fin n ⊕ Fin k)) (hg : g ∈ (HSetPair n k)ᶜ) :
    p ^ (padicValNat p n + padicValNat p k - 1) ∣
      (Finset.univ.filter ((orbRelPair n k).r g)).card := by
  haveI := Fact.mk hp
  have hgH : g ∉ HgrpPair n k := by rw [mem_HgrpPair_iff]; simpa using hg
  have ha1 : 1 ≤ aCardPair g := one_le_aCardPair g hgH
  have hb1 : 1 ≤ bCardPair g := one_le_bCardPair g hgH
  have han : aCardPair g ≤ n := aCardPair_le g
  have hbn : bCardPair g ≤ k := bCardPair_le g
  have hpa : p ^ (padicValNat p n) ∣ n := pow_padicValNat_dvd
  have hpb : p ^ (padicValNat p k) ∣ k := pow_padicValNat_dvd
  have hmsf := mixed_support_factorial p hp hpa hpb ha1 han hb1 hbn
  -- v_p(n.descFactorial a) + v_p((n-a)!) = v_p(n!)
  have hkeyA : padicValNat p (n.descFactorial (aCardPair g)) + padicValNat p ((n - aCardPair g)!) =
      padicValNat p (n !) := by
    have hne1 : n.descFactorial (aCardPair g) ≠ 0 := (Nat.descFactorial_pos.mpr han).ne'
    have hne2 : (n - aCardPair g)! ≠ 0 := Nat.factorial_ne_zero _
    rw [← padicValNat.mul hne1 hne2, descFactorial_mul_factorial_sub n (aCardPair g) han]
  have hkeyB : padicValNat p (k.descFactorial (bCardPair g)) + padicValNat p ((k - bCardPair g)!) =
      padicValNat p (k !) := by
    have hne1 : k.descFactorial (bCardPair g) ≠ 0 := (Nat.descFactorial_pos.mpr hbn).ne'
    have hne2 : (k - bCardPair g)! ≠ 0 := Nat.factorial_ne_zero _
    rw [← padicValNat.mul hne1 hne2, descFactorial_mul_factorial_sub k (bCardPair g) hbn]
  have hcent := vp_stabilizer_le_pair g p hp
  have hprod := class_card_mul_stabilizer_card_pair n k g
  have hstabne : Fintype.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g) ≠ 0 := by
    have : Nonempty ↥(MulAction.stabilizer ↥(HgrpPair n k) g) := ⟨1, Subgroup.one_mem _⟩
    exact Fintype.card_ne_zero
  have hstab_eq : Nat.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g) =
      Fintype.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g) := Nat.card_eq_fintype_card
  rw [hstab_eq] at hcent
  have hclassne : (Finset.univ.filter ((orbRelPair n k).r g)).card ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact Nat.factorial_ne_zero n (by nlinarith [Nat.factorial_pos k])
  have hfa := congrArg (fun x => x.factorization p) hprod
  simp only [Nat.factorization_mul hclassne hstabne,
    Nat.factorization_mul (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero k),
    Finsupp.coe_add, Pi.add_apply] at hfa
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp,
    Nat.factorization_def _ hp] at hfa
  have hfinal : padicValNat p n + padicValNat p k - 1 ≤
      padicValNat p (Finset.univ.filter ((orbRelPair n k).r g)).card := by
    omega
  exact (Nat.Prime.pow_dvd_iff_le_factorization hp hclassne).mpr
    (by rw [Nat.factorization_def _ hp]; exact hfinal)

/-- **`thm:optimal-divisor`, lower bound, general `(n,k,p)`**: for every prime `p` and every
`n, k ≥ 1`, every coefficient of `CpermPair n k - Cperm n * Cperm k` is divisible by
`p^(v_p(n)+v_p(k)-1)`. -/
theorem optimal_divisor_lower_bound (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ Q : MvPolynomial ℕ ℤ,
      CpermPair n k - Cperm n * Cperm k =
        ((p ^ (padicValNat p n + padicValNat p k - 1) : ℕ) : MvPolynomial ℕ ℤ) * Q := by
  have hmain := dvd_sum_of_const_on_classes (orbRelPair n k).r
    (fun x => (orbRelPair n k).iseqv.refl x)
    (fun x y h => (orbRelPair n k).iseqv.symm h)
    (fun x y z h1 h2 => (orbRelPair n k).iseqv.trans h1 h2)
    ci (fun x y h => ci_const_on_orbit_pair n k x y h)
    (p ^ (padicValNat p n + padicValNat p k - 1)) (HSetPair n k)ᶜ
    (fun x hx => by
      rw [filter_compl_eq_filter_univ_pair hx]
      exact_mod_cast class_card_dvd_pair p hp n k hn hk x hx)
  obtain ⟨Q, hQ⟩ := hmain
  refine ⟨Q, ?_⟩
  rw [CpermPair_sub_Cperm_mul, hQ]

end CongruenceTheory
