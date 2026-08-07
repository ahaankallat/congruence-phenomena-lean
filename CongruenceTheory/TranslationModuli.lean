import Mathlib
import CongruenceTheory.Universal

/-!
**Theorem `thm:translation-moduli`** ("Complete classification of universal
two-term translation moduli"): coefficientwise divisibility of a universal
polynomial identity is equivalent to divisibility after every ring
specialization. A general `MvPolynomial` fact, independent of the specific
polynomial family `C`.
-/

namespace CongruenceTheory

open MvPolynomial

/-- **Theorem `thm:translation-moduli`, (i) ⟺ (ii).** For `P : MvPolynomial ℕ ℤ` and `m : ℕ`,
coefficientwise divisibility by `m` (`DvdCoeffs m P`) is equivalent to: for every commutative
ring `R` and every specialization `φ : ℕ → R`, `m` divides the specialized value. -/
theorem dvdCoeffs_iff_forall_specialization (m : ℕ) (P : MvPolynomial ℕ ℤ) :
    DvdCoeffs m P ↔
      ∀ (R : Type) [CommRing R] (φ : ℕ → R),
        (m : R) ∣ MvPolynomial.eval₂ (Int.castRingHom R) φ P := by
  constructor
  · intro hP R _ φ
    rw [MvPolynomial.eval₂_eq]
    apply Finset.dvd_sum
    intro d _
    have hcd : (m : ℤ) ∣ MvPolynomial.coeff d P := hP d
    obtain ⟨c, hc⟩ := hcd
    refine ⟨(c : R) * d.prod fun i k => φ i ^ k, ?_⟩
    rw [hc, map_mul, mul_assoc]
    simp [map_natCast, map_intCast, Finsupp.prod]
  · intro hall
    have h := hall (MvPolynomial ℕ (ZMod m)) (fun j => MvPolynomial.X j)
    have hcast : (Int.castRingHom (MvPolynomial ℕ (ZMod m))) =
        (MvPolynomial.C).comp (Int.castRingHom (ZMod m)) := by
      apply Subsingleton.elim
    have heval : MvPolynomial.eval₂ (Int.castRingHom (MvPolynomial ℕ (ZMod m)))
        (fun j => MvPolynomial.X j) P = MvPolynomial.map (Int.castRingHom (ZMod m)) P := by
      rw [hcast]
      exact DFunLike.congr_fun
        (MvPolynomial.map_eq_eval₂Hom_C_comp (Int.castRingHom (ZMod m))).symm P
    rw [heval] at h
    obtain ⟨Q, hQ⟩ := h
    apply dvdCoeffs_of_map_eq_zero
    have hm0 : ((m : ℕ) : MvPolynomial ℕ (ZMod m)) = 0 := by
      have := ZMod.natCast_self m
      calc ((m : ℕ) : MvPolynomial ℕ (ZMod m)) = MvPolynomial.C ((m : ℕ) : ZMod m) := by
            push_cast; rfl
        _ = MvPolynomial.C 0 := by rw [this]
        _ = 0 := map_zero _
    rw [hQ, hm0, zero_mul]

end CongruenceTheory
