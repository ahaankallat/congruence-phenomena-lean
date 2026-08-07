import Mathlib

/-!
A general "sum over an equivalence relation with divisible class sizes is
divisible" lemma, proved by strong induction on `Finset.card`. This is the
combinatorial engine behind Theorem `thm:strong`'s orbit-counting argument:
if a finite set is partitioned into classes of a `d`-divisible size, and a
ring-valued function is constant on each class, then the total sum is
divisible by `d`.
-/

namespace CongruenceTheory

variable {ι : Type*} [DecidableEq ι]

theorem dvd_sum_of_const_on_classes (r : ι → ι → Prop) (hrefl : ∀ x, r x x)
    (hsymm : ∀ x y, r x y → r y x) (htrans : ∀ x y z, r x y → r y z → r x z)
    [DecidableRel r] (f : ι → MvPolynomial ℕ ℤ) (hf : ∀ x y, r x y → f x = f y)
    (d : ℕ) :
    ∀ s : Finset ι, (∀ x ∈ s, (d : ℤ) ∣ ((s.filter (r x)).card : ℤ)) →
      ∃ Q : MvPolynomial ℕ ℤ, ∑ x ∈ s, f x = (d : MvPolynomial ℕ ℤ) * Q := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hcard
    rcases s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
    · exact ⟨0, by simp⟩
    · set c := s.filter (r x0) with hcdef
      have hx0c : x0 ∈ c := by simp [hcdef, hrefl x0, hx0]
      have hcsub : c ⊆ s := Finset.filter_subset _ _
      have hsdiffssubset : s \ c ⊂ s := Finset.sdiff_ssubset hcsub ⟨x0, hx0c⟩
      have hsplit : s = c ∪ s \ c := (Finset.union_sdiff_of_subset hcsub).symm
      have hdisj : Disjoint c (s \ c) := Finset.disjoint_sdiff
      have hconst : ∀ x ∈ c, f x = f x0 := by
        intro x hx
        simp only [hcdef, Finset.mem_filter] at hx
        exact (hf x0 x hx.2).symm
      have hcsum : ∑ x ∈ c, f x = (c.card : ℤ) • f x0 := by
        rw [Finset.sum_congr rfl hconst, Finset.sum_const]
        simp [zsmul_eq_mul]
      obtain ⟨Qc, hQc⟩ : ∃ Qc, (c.card : ℤ) = (d : ℤ) * Qc := hcard x0 hx0
      have hcsum' : ∑ x ∈ c, f x = (d : MvPolynomial ℕ ℤ) * ((Qc : MvPolynomial ℕ ℤ) * f x0) := by
        rw [hcsum, hQc]
        simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
        ring
      have hrec : ∀ x ∈ s \ c, (d : ℤ) ∣ (((s \ c).filter (r x)).card : ℤ) := by
        intro x hx
        have hxs : x ∈ s := (Finset.mem_sdiff.mp hx).1
        have hxc : x ∉ c := (Finset.mem_sdiff.mp hx).2
        have heq : (s \ c).filter (r x) = s.filter (r x) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨hys, _⟩, hry⟩
            exact ⟨hys, hry⟩
          · rintro ⟨hys, hry⟩
            refine ⟨⟨hys, ?_⟩, hry⟩
            intro hyc
            simp only [hcdef, Finset.mem_filter] at hyc
            exact hxc (by
              simp only [hcdef, Finset.mem_filter]
              exact ⟨hxs, htrans x0 y x hyc.2 (hsymm x y hry)⟩)
        rw [heq]
        exact hcard x hxs
      obtain ⟨Qrest, hQrest⟩ := ih (s \ c) hsdiffssubset hrec
      refine ⟨(Qc : MvPolynomial ℕ ℤ) * f x0 + Qrest, ?_⟩
      rw [hsplit, Finset.sum_union hdisj, hcsum', hQrest]
      ring

end CongruenceTheory
