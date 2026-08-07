import Mathlib
import CongruenceTheory.Perm

/-!
The conjugation action of `H = Perm A × Perm B` (embedded via `sumCongrHom`)
on `Perm (Fin n ⊕ Fin n)`, and the orbit-equivalence-relation machinery
needed to apply `dvd_sum_of_const_on_classes` to Theorem `thm:strong`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm Nat

variable (n : ℕ)

/-- `H = Perm A × Perm B`, embedded in `Perm (Fin n ⊕ Fin n)` via `sumCongrHom`, as a
`Subgroup`. -/
noncomputable def Hgrp : Subgroup (Equiv.Perm (Fin n ⊕ Fin n)) :=
  (Equiv.Perm.sumCongrHom (Fin n) (Fin n)).range

lemma mem_Hgrp_iff (g : Equiv.Perm (Fin n ⊕ Fin n)) : g ∈ Hgrp n ↔ g ∈ HSet n := by
  simp [Hgrp, HSet]

noncomputable instance : Fintype ↥(Hgrp n) := by unfold Hgrp; infer_instance

/-- Conjugation action of `H` on the ambient permutation group. -/
noncomputable instance : MulAction ↥(Hgrp n) (Equiv.Perm (Fin n ⊕ Fin n)) where
  smul h g := h.1 * g * h.1⁻¹
  one_smul g := by
    change (1 : ↥(Hgrp n)).1 * g * (1 : ↥(Hgrp n)).1⁻¹ = g
    simp
  mul_smul h1 h2 g := by
    change (h1 * h2 : ↥(Hgrp n)).1 * g * (h1 * h2 : ↥(Hgrp n)).1⁻¹ =
      h1.1 * (h2.1 * g * h2.1⁻¹) * h1.1⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

lemma smul_def (h : ↥(Hgrp n)) (g : Equiv.Perm (Fin n ⊕ Fin n)) :
    h • g = h.1 * g * h.1⁻¹ := rfl

/-- `HSet n`ᶜ is invariant under `H`-conjugation: `H` is a subgroup, so conjugating
an element outside `H` by an element of `H` keeps it outside `H`. -/
lemma compl_HSet_invariant (h : ↥(Hgrp n)) (g : Equiv.Perm (Fin n ⊕ Fin n))
    (hg : g ∈ (HSet n)ᶜ) : h • g ∈ (HSet n)ᶜ := by
  rw [Finset.mem_compl] at hg ⊢
  rw [smul_def]
  intro hmem
  apply hg
  rw [← mem_Hgrp_iff] at hmem ⊢
  have : g = h.1⁻¹ * (h.1 * g * h.1⁻¹) * h.1 := by group
  rw [this]
  exact (Hgrp n).mul_mem ((Hgrp n).mul_mem (Subgroup.inv_mem _ h.2) hmem) h.2

/-- The `H`-conjugation orbit relation, restricted to the ambient (fintype, decidable)
`Setoid` from `MulAction.orbitRel`. -/
noncomputable abbrev orbRel : Setoid (Equiv.Perm (Fin n ⊕ Fin n)) :=
  MulAction.orbitRel ↥(Hgrp n) (Equiv.Perm (Fin n ⊕ Fin n))

lemma ci_const_on_orbit (g g' : Equiv.Perm (Fin n ⊕ Fin n)) (h : (orbRel n).r g g') :
    ci g = ci g' := by
  obtain ⟨hh, rfl⟩ := h
  change ci (hh • g') = ci g'
  rw [smul_def]
  exact ci_conj hh.1 g'

/-- `|H| = n! * n!`. -/
theorem card_Hgrp : Fintype.card ↥(Hgrp n) = (n !) * (n !) := by
  have h1 : Fintype.card ↥(Hgrp n) = Fintype.card (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :=
    Equiv.Perm.sumCongrHom.card_range
  rw [h1]
  simp [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]

open scoped Classical in
/-- The `H`-conjugation class of `g` (as a `Finset`) is exactly its orbit. -/
theorem filter_orbRel_eq_orbit_toFinset (g : Equiv.Perm (Fin n ⊕ Fin n)) :
    Finset.univ.filter ((orbRel n).r g) = (MulAction.orbit ↥(Hgrp n) g).toFinset := by
  ext g'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
  exact MulAction.mem_orbit_symm

open scoped Classical in
/-- **Orbit-stabilizer**, specialized: the class size of `g` times the stabilizer
(`= C_H(g)`, the centralizer of `g` within `H`) size equals `|H| = n! * n!`. -/
theorem class_card_mul_stabilizer_card (g : Equiv.Perm (Fin n ⊕ Fin n)) :
    (Finset.univ.filter ((orbRel n).r g)).card *
      Fintype.card ↥(MulAction.stabilizer ↥(Hgrp n) g) = (n !) * (n !) := by
  rw [filter_orbRel_eq_orbit_toFinset, Set.toFinset_card]
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥(Hgrp n) g, card_Hgrp]

end CongruenceTheory
