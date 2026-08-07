import Mathlib
import CongruenceTheory.ContentBounds

/-!
The `(n,k)`-generalized counterpart of `Conj.lean`: the conjugation action of
`H = Perm (Fin n) × Perm (Fin k)` (embedded via `sumCongrHom`) on
`Perm (Fin n ⊕ Fin k)`, for unequal `n,k` — needed for the general-`(n,k,p)`
lower bound of `thm:optimal-divisor` (`Conj.lean`'s `n = k` version stays as-is,
since `StrongTwoAdic.lean` depends on it).
-/

namespace CongruenceTheory

open Equiv Equiv.Perm Nat

variable (n k : ℕ)

/-- `H = Perm A × Perm B`, embedded in `Perm (Fin n ⊕ Fin k)` via `sumCongrHom`, as a
`Subgroup`. -/
noncomputable def HgrpPair : Subgroup (Equiv.Perm (Fin n ⊕ Fin k)) :=
  (Equiv.Perm.sumCongrHom (Fin n) (Fin k)).range

/-- The `H`-embedding, as a `Finset` (mirrors `HSet`, generalized to unequal `n,k`). -/
noncomputable def HSetPair : Finset (Equiv.Perm (Fin n ⊕ Fin k)) :=
  Finset.univ.filter (· ∈ (Equiv.Perm.sumCongrHom (Fin n) (Fin k)).range)

lemma mem_HgrpPair_iff (g : Equiv.Perm (Fin n ⊕ Fin k)) : g ∈ HgrpPair n k ↔ g ∈ HSetPair n k := by
  simp [HgrpPair, HSetPair]

noncomputable instance : Fintype ↥(HgrpPair n k) := by unfold HgrpPair; infer_instance

/-- Conjugation action of `H` on the ambient permutation group. -/
noncomputable instance : MulAction ↥(HgrpPair n k) (Equiv.Perm (Fin n ⊕ Fin k)) where
  smul h g := h.1 * g * h.1⁻¹
  one_smul g := by
    change (1 : ↥(HgrpPair n k)).1 * g * (1 : ↥(HgrpPair n k)).1⁻¹ = g
    simp
  mul_smul h1 h2 g := by
    change (h1 * h2 : ↥(HgrpPair n k)).1 * g * (h1 * h2 : ↥(HgrpPair n k)).1⁻¹ =
      h1.1 * (h2.1 * g * h2.1⁻¹) * h1.1⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

lemma smul_def_pair (h : ↥(HgrpPair n k)) (g : Equiv.Perm (Fin n ⊕ Fin k)) :
    h • g = h.1 * g * h.1⁻¹ := rfl

/-- `HSetPair n k`ᶜ is invariant under `H`-conjugation. -/
lemma compl_HSetPair_invariant (h : ↥(HgrpPair n k)) (g : Equiv.Perm (Fin n ⊕ Fin k))
    (hg : g ∈ (HSetPair n k)ᶜ) : h • g ∈ (HSetPair n k)ᶜ := by
  rw [Finset.mem_compl] at hg ⊢
  rw [smul_def_pair]
  intro hmem
  apply hg
  rw [← mem_HgrpPair_iff] at hmem ⊢
  have : g = h.1⁻¹ * (h.1 * g * h.1⁻¹) * h.1 := by group
  rw [this]
  exact (HgrpPair n k).mul_mem ((HgrpPair n k).mul_mem (Subgroup.inv_mem _ h.2) hmem) h.2

/-- The `H`-conjugation orbit relation. -/
noncomputable abbrev orbRelPair : Setoid (Equiv.Perm (Fin n ⊕ Fin k)) :=
  MulAction.orbitRel ↥(HgrpPair n k) (Equiv.Perm (Fin n ⊕ Fin k))

lemma ci_const_on_orbit_pair (g g' : Equiv.Perm (Fin n ⊕ Fin k)) (h : (orbRelPair n k).r g g') :
    ci g = ci g' := by
  obtain ⟨hh, rfl⟩ := h
  change ci (hh • g') = ci g'
  rw [smul_def_pair]
  exact ci_conj hh.1 g'

/-- `|H| = n! * k!`. -/
theorem card_HgrpPair : Fintype.card ↥(HgrpPair n k) = (n !) * (k !) := by
  have h1 : Fintype.card ↥(HgrpPair n k) = Fintype.card (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) :=
    Equiv.Perm.sumCongrHom.card_range
  rw [h1]
  simp [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]

open scoped Classical in
/-- The `H`-conjugation class of `g` (as a `Finset`) is exactly its orbit. -/
theorem filter_orbRelPair_eq_orbit_toFinset (g : Equiv.Perm (Fin n ⊕ Fin k)) :
    Finset.univ.filter ((orbRelPair n k).r g) = (MulAction.orbit ↥(HgrpPair n k) g).toFinset := by
  ext g'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
  exact MulAction.mem_orbit_symm

open scoped Classical in
/-- **Orbit-stabilizer**, specialized: the class size of `g` times the stabilizer size
equals `|H| = n! * k!`. -/
theorem class_card_mul_stabilizer_card_pair (g : Equiv.Perm (Fin n ⊕ Fin k)) :
    (Finset.univ.filter ((orbRelPair n k).r g)).card *
      Fintype.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g) = (n !) * (k !) := by
  rw [filter_orbRelPair_eq_orbit_toFinset, Set.toFinset_card]
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥(HgrpPair n k) g, card_HgrpPair]

end CongruenceTheory
