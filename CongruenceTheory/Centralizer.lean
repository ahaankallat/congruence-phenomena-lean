import Mathlib
import CongruenceTheory.Conj
import CongruenceTheory.OrbitBound

/-!
The centralizer-in-`H` bound: the manuscript's actual mathematical content
for Theorem `thm:strong`, via the "mixed cycles restrict faithfully"
argument.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm Nat

variable {n : ℕ} (g : Equiv.Perm (Fin n ⊕ Fin n))

open scoped Classical

/-- A point lies in a "mixed" cycle of `g` if its cycle contains both a left
(`A`) point and a right (`B`) point. -/
noncomputable def IsMixed (x : Fin n ⊕ Fin n) : Prop :=
  (∃ a : Fin n, g.SameCycle x (Sum.inl a)) ∧ (∃ b : Fin n, g.SameCycle x (Sum.inr b))

/-- The predicate cutting out the left mixed points. -/
noncomputable def MixedA (x : Fin n ⊕ Fin n) : Prop := x.isLeft ∧ IsMixed g x

/-- The predicate cutting out the right mixed points. -/
noncomputable def MixedB (x : Fin n ⊕ Fin n) : Prop := x.isRight ∧ IsMixed g x

lemma isMixed_of_sameCycle {x y : Fin n ⊕ Fin n} (h : g.SameCycle x y) :
    IsMixed g x ↔ IsMixed g y := by
  unfold IsMixed
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, h.symm.trans ha⟩, ⟨b, h.symm.trans hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, h.trans ha⟩, ⟨b, h.trans hb⟩⟩

/-- If `h` commutes with `g` and fixes `x`, it fixes every point in `x`'s `g`-cycle. -/
lemma fixed_of_commute_of_fixed {h : Equiv.Perm (Fin n ⊕ Fin n)} (hcomm : Commute h g)
    {x y : Fin n ⊕ Fin n} (hxy : g.SameCycle x y) (hx : h x = x) : h y = y := by
  obtain ⟨i, hi⟩ := hxy
  have hc : Commute h (g ^ i) := hcomm.zpow_right i
  calc h y = h ((g ^ i) x) := by rw [hi]
    _ = ((g ^ i) * h) x := by rw [← Equiv.Perm.mul_apply, ← hc]
    _ = (g ^ i) (h x) := rfl
    _ = (g ^ i) x := by rw [hx]
    _ = y := hi

/-- If `h` commutes with `g`, it maps `g`-cycles to `g`-cycles. -/
lemma sameCycle_apply_of_commute {h : Equiv.Perm (Fin n ⊕ Fin n)} (hcomm : Commute h g)
    {x y : Fin n ⊕ Fin n} (hxy : g.SameCycle x y) : g.SameCycle (h x) (h y) := by
  obtain ⟨i, hi⟩ := hxy
  refine ⟨i, ?_⟩
  have hc : h * g ^ i = g ^ i * h := hcomm.zpow_right i
  calc (g ^ i) (h x) = (g ^ i * h) x := rfl
    _ = (h * g ^ i) x := by rw [hc]
    _ = h ((g ^ i) x) := rfl
    _ = h y := by rw [hi]

/-- If `h ∈ H` commutes with `g` and `x` is mixed, so is `h x`. -/
lemma isMixed_apply_of_mem {h : Equiv.Perm (Fin n ⊕ Fin n)} (hH : h ∈ Hgrp n)
    (hcomm : Commute h g) {x : Fin n ⊕ Fin n} (hx : IsMixed g x) : IsMixed g (h x) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
  obtain ⟨p, hp⟩ := hH
  refine ⟨⟨p.1 a, ?_⟩, ⟨p.2 b, ?_⟩⟩
  · have hs := sameCycle_apply_of_commute g hcomm ha
    rwa [show h (Sum.inl a) = Sum.inl (p.1 a) by
      rw [← hp, Equiv.Perm.sumCongrHom_apply]; rfl] at hs
  · have hs := sameCycle_apply_of_commute g hcomm hb
    rwa [show h (Sum.inr b) = Sum.inr (p.2 b) by
      rw [← hp, Equiv.Perm.sumCongrHom_apply]; rfl] at hs

lemma isMixed_apply_iff {h : Equiv.Perm (Fin n ⊕ Fin n)} (hH : h ∈ Hgrp n)
    (hcomm : Commute h g) (x : Fin n ⊕ Fin n) : IsMixed g (h x) ↔ IsMixed g x := by
  refine ⟨fun hm => ?_, isMixed_apply_of_mem g hH hcomm⟩
  have hH' : h⁻¹ ∈ Hgrp n := Subgroup.inv_mem _ hH
  have hcomm' : Commute h⁻¹ g := hcomm.inv_left
  have := isMixed_apply_of_mem g hH' hcomm' hm
  simpa using this

/-- `h ∈ H` commuting with `g` maps left points to left points. -/
lemma isLeft_apply_of_mem {h : Equiv.Perm (Fin n ⊕ Fin n)} (hH : h ∈ Hgrp n)
    {x : Fin n ⊕ Fin n} (hx : x.isLeft) : (h x).isLeft := by
  obtain ⟨p, hp⟩ := hH
  obtain ⟨a, rfl⟩ := Sum.isLeft_iff.mp hx
  rw [show h (Sum.inl a) = Sum.inl (p.1 a) by
    rw [← hp, Equiv.Perm.sumCongrHom_apply]; rfl]
  exact rfl

lemma isRight_apply_of_mem {h : Equiv.Perm (Fin n ⊕ Fin n)} (hH : h ∈ Hgrp n)
    {x : Fin n ⊕ Fin n} (hx : x.isRight) : (h x).isRight := by
  obtain ⟨p, hp⟩ := hH
  obtain ⟨b, rfl⟩ := Sum.isRight_iff.mp hx
  rw [show h (Sum.inr b) = Sum.inr (p.2 b) by
    rw [← hp, Equiv.Perm.sumCongrHom_apply]; rfl]
  exact rfl

/-- **Set preservation**: `h ∈ H` commuting with `g` maps `MixedA g`-points to
`MixedA g`-points. -/
lemma mapsTo_MixedA {h : Equiv.Perm (Fin n ⊕ Fin n)} (hH : h ∈ Hgrp n) (hcomm : Commute h g)
    {x : Fin n ⊕ Fin n} (hx : MixedA g x) : MixedA g (h x) :=
  ⟨isLeft_apply_of_mem hH hx.1, isMixed_apply_of_mem g hH hcomm hx.2⟩

lemma mapsTo_MixedB {h : Equiv.Perm (Fin n ⊕ Fin n)} (hH : h ∈ Hgrp n) (hcomm : Commute h g)
    {x : Fin n ⊕ Fin n} (hx : MixedB g x) : MixedB g (h x) :=
  ⟨isRight_apply_of_mem hH hx.1, isMixed_apply_of_mem g hH hcomm hx.2⟩

lemma mapsTo_NonMixedA {h : Equiv.Perm (Fin n ⊕ Fin n)} (hH : h ∈ Hgrp n) (hcomm : Commute h g)
    {x : Fin n ⊕ Fin n} (hx : x.isLeft ∧ ¬ IsMixed g x) :
    (h x).isLeft ∧ ¬ IsMixed g (h x) :=
  ⟨isLeft_apply_of_mem hH hx.1, fun hm => hx.2 ((isMixed_apply_iff g hH hcomm x).mp hm)⟩

lemma mapsTo_NonMixedB {h : Equiv.Perm (Fin n ⊕ Fin n)} (hH : h ∈ Hgrp n) (hcomm : Commute h g)
    {x : Fin n ⊕ Fin n} (hx : x.isRight ∧ ¬ IsMixed g x) :
    (h x).isRight ∧ ¬ IsMixed g (h x) :=
  ⟨isRight_apply_of_mem hH hx.1, fun hm => hx.2 ((isMixed_apply_iff g hH hcomm x).mp hm)⟩

/-- **Faithfulness**: two elements of `C_H(g)` agreeing on the non-mixed points of `A`,
the non-mixed points of `B`, and the mixed points of `A`, are equal. This is the
manuscript's key claim: an element fixing every mixed point of `A` fixes every mixed
cycle entirely (hence also every mixed point of `B`). -/
theorem eq_of_agree {h1 h2 : Equiv.Perm (Fin n ⊕ Fin n)} (hH1 : h1 ∈ Hgrp n)
    (hH2 : h2 ∈ Hgrp n) (hcomm1 : Commute h1 g) (hcomm2 : Commute h2 g)
    (hA : ∀ x, x.isLeft → ¬ IsMixed g x → h1 x = h2 x)
    (hB : ∀ x, x.isRight → ¬ IsMixed g x → h1 x = h2 x)
    (hMa : ∀ x, MixedA g x → h1 x = h2 x) :
    h1 = h2 := by
  have hcomm : Commute (h1⁻¹ * h2) g := Commute.mul_left hcomm1.inv_left hcomm2
  ext x
  by_cases hx : IsMixed g x
  · obtain ⟨a, ha⟩ := hx.1
    have hMaa : MixedA g (Sum.inl a) := ⟨rfl, (isMixed_of_sameCycle g ha).mp hx⟩
    have hfix : (h1⁻¹ * h2) (Sum.inl a) = Sum.inl a := by
      have heq := hMa (Sum.inl a) hMaa
      show h1⁻¹ (h2 (Sum.inl a)) = Sum.inl a
      rw [← heq]
      simp
    have hfixx := fixed_of_commute_of_fixed g hcomm ha.symm hfix
    show h1 x = h2 x
    have h2x' : h1⁻¹ (h2 x) = x := hfixx
    have := congrArg h1 h2x'
    simpa using this.symm
  · cases x with
    | inl a => exact hA (Sum.inl a) rfl hx
    | inr b => exact hB (Sum.inr b) rfl hx

/-- Membership in the stabilizer of `g` (under `H`-conjugation) is exactly commuting with `g`. -/
lemma stab_iff_commute (h : ↥(Hgrp n)) :
    h ∈ MulAction.stabilizer ↥(Hgrp n) g ↔ Commute (h : Equiv.Perm (Fin n ⊕ Fin n)) g := by
  rw [MulAction.mem_stabilizer_iff, smul_def]
  constructor
  · intro he
    have h2 : (h : Equiv.Perm (Fin n ⊕ Fin n)) * g * (h : Equiv.Perm (Fin n ⊕ Fin n))⁻¹ *
        (h : Equiv.Perm (Fin n ⊕ Fin n)) = g * (h : Equiv.Perm (Fin n ⊕ Fin n)) := by rw [he]
    have h3 : (h : Equiv.Perm (Fin n ⊕ Fin n)) * g = g * (h : Equiv.Perm (Fin n ⊕ Fin n)) := by
      simpa [mul_assoc] using h2
    exact h3
  · intro hc
    show (h : Equiv.Perm (Fin n ⊕ Fin n)) * g * (h : Equiv.Perm (Fin n ⊕ Fin n))⁻¹ = g
    rw [hc]
    simp [mul_assoc]

/-- `a(g)`, the number of mixed points on the `A` side. -/
noncomputable def mixedCardA : ℕ := Nat.card {x : Fin n ⊕ Fin n // MixedA g x}

/-- `b(g)`, the number of mixed points on the `B` side. -/
noncomputable def mixedCardB : ℕ := Nat.card {x : Fin n ⊕ Fin n // MixedB g x}

variable {g} in
/-- The restriction of `f` to a `Fintype`-preserved predicate is compatible with `*`. -/
lemma subtypePermOfFintype_mul {p : Fin n ⊕ Fin n → Prop} [Finite {x // p x}]
    {f1 f2 : Equiv.Perm (Fin n ⊕ Fin n)} (h1 : ∀ x, p x → p (f1 x)) (h2 : ∀ x, p x → p (f2 x)) :
    Equiv.Perm.subtypePermOfFintype (f1 * f2) (fun x hx => h1 (f2 x) (h2 x hx)) =
      Equiv.Perm.subtypePermOfFintype f1 h1 * Equiv.Perm.subtypePermOfFintype f2 h2 := by
  ext ⟨x, hx⟩
  simp [Equiv.Perm.subtypePermOfFintype_apply, Equiv.Perm.mul_apply]

/-- The combined restriction map: `C_H(g) → Perm(A∖Ma) × Perm(B∖Mb) × Perm(Ma)`. -/
noncomputable def restrictTriple (h : ↥(MulAction.stabilizer ↥(Hgrp n) g)) :
    Equiv.Perm {x : Fin n ⊕ Fin n // x.isLeft ∧ ¬ IsMixed g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin n // x.isRight ∧ ¬ IsMixed g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin n // MixedA g x} :=
  ( Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin n))
      (fun x hx => mapsTo_NonMixedA g h.1.2 ((stab_iff_commute g h.1).mp h.2) hx),
    Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin n))
      (fun x hx => mapsTo_NonMixedB g h.1.2 ((stab_iff_commute g h.1).mp h.2) hx),
    Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin n))
      (fun x hx => mapsTo_MixedA g h.1.2 ((stab_iff_commute g h.1).mp h.2) hx) )

lemma restrictTriple_mul (h1 h2 : ↥(MulAction.stabilizer ↥(Hgrp n) g)) :
    restrictTriple g (h1 * h2) = restrictTriple g h1 * restrictTriple g h2 := by
  simp only [restrictTriple, Prod.mk_mul_mk, Prod.mk.injEq]
  exact ⟨subtypePermOfFintype_mul _ _, subtypePermOfFintype_mul _ _, subtypePermOfFintype_mul _ _⟩

/-- **The centralizer restriction homomorphism.** -/
noncomputable def restrictHom : ↥(MulAction.stabilizer ↥(Hgrp n) g) →*
    Equiv.Perm {x : Fin n ⊕ Fin n // x.isLeft ∧ ¬ IsMixed g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin n // x.isRight ∧ ¬ IsMixed g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin n // MixedA g x} :=
  MonoidHom.mk' (restrictTriple g) (restrictTriple_mul g)

theorem restrictHom_injective : Function.Injective (restrictHom (n := n) g) := by
  intro h1 h2 heq
  simp only [restrictHom, MonoidHom.mk'_apply] at heq
  apply Subtype.ext
  apply Subtype.ext
  apply eq_of_agree g h1.1.2 h2.1.2 ((stab_iff_commute g h1.1).mp h1.2)
    ((stab_iff_commute g h2.1).mp h2.2)
  · intro x hxl hxm
    have h0 := congrArg Prod.fst heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxl, hxm⟩
    simpa [restrictTriple, Equiv.Perm.subtypePermOfFintype_apply] using hx
  · intro x hxr hxm
    have h0 := congrArg (Prod.fst ∘ Prod.snd) heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxr, hxm⟩
    simpa [restrictTriple, Equiv.Perm.subtypePermOfFintype_apply] using hx
  · intro x hxm
    have h0 := congrArg (Prod.snd ∘ Prod.snd) heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxm⟩
    simpa [restrictTriple, Equiv.Perm.subtypePermOfFintype_apply] using hx

/-- The symmetric (`B`-side) version of `eq_of_agree`. -/
theorem eq_of_agree' {h1 h2 : Equiv.Perm (Fin n ⊕ Fin n)} (hcomm1 : Commute h1 g)
    (hcomm2 : Commute h2 g)
    (hA : ∀ x, x.isLeft → ¬ IsMixed g x → h1 x = h2 x)
    (hB : ∀ x, x.isRight → ¬ IsMixed g x → h1 x = h2 x)
    (hMb : ∀ x, MixedB g x → h1 x = h2 x) :
    h1 = h2 := by
  have hcomm : Commute (h1⁻¹ * h2) g := Commute.mul_left hcomm1.inv_left hcomm2
  ext x
  by_cases hx : IsMixed g x
  · obtain ⟨b, hb⟩ := hx.2
    have hMbb : MixedB g (Sum.inr b) := ⟨rfl, (isMixed_of_sameCycle g hb).mp hx⟩
    have hfix : (h1⁻¹ * h2) (Sum.inr b) = Sum.inr b := by
      have heq := hMb (Sum.inr b) hMbb
      show h1⁻¹ (h2 (Sum.inr b)) = Sum.inr b
      rw [← heq]
      simp
    have hfixx := fixed_of_commute_of_fixed g hcomm hb.symm hfix
    show h1 x = h2 x
    have h2x' : h1⁻¹ (h2 x) = x := hfixx
    have := congrArg h1 h2x'
    simpa using this.symm
  · cases x with
    | inl a => exact hA (Sum.inl a) rfl hx
    | inr b => exact hB (Sum.inr b) rfl hx

/-- The restriction map, `B`-side variant: `C_H(g) → Perm(A∖Ma) × Perm(B∖Mb) × Perm(Mb)`. -/
noncomputable def restrictTriple' (h : ↥(MulAction.stabilizer ↥(Hgrp n) g)) :
    Equiv.Perm {x : Fin n ⊕ Fin n // x.isLeft ∧ ¬ IsMixed g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin n // x.isRight ∧ ¬ IsMixed g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin n // MixedB g x} :=
  ( Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin n))
      (fun x hx => mapsTo_NonMixedA g h.1.2 ((stab_iff_commute g h.1).mp h.2) hx),
    Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin n))
      (fun x hx => mapsTo_NonMixedB g h.1.2 ((stab_iff_commute g h.1).mp h.2) hx),
    Equiv.Perm.subtypePermOfFintype (h.1 : Equiv.Perm (Fin n ⊕ Fin n))
      (fun x hx => mapsTo_MixedB g h.1.2 ((stab_iff_commute g h.1).mp h.2) hx) )

lemma restrictTriple'_mul (h1 h2 : ↥(MulAction.stabilizer ↥(Hgrp n) g)) :
    restrictTriple' g (h1 * h2) = restrictTriple' g h1 * restrictTriple' g h2 := by
  simp only [restrictTriple', Prod.mk_mul_mk, Prod.mk.injEq]
  exact ⟨subtypePermOfFintype_mul _ _, subtypePermOfFintype_mul _ _, subtypePermOfFintype_mul _ _⟩

noncomputable def restrictHom' : ↥(MulAction.stabilizer ↥(Hgrp n) g) →*
    Equiv.Perm {x : Fin n ⊕ Fin n // x.isLeft ∧ ¬ IsMixed g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin n // x.isRight ∧ ¬ IsMixed g x} ×
      Equiv.Perm {x : Fin n ⊕ Fin n // MixedB g x} :=
  MonoidHom.mk' (restrictTriple' g) (restrictTriple'_mul g)

theorem restrictHom'_injective : Function.Injective (restrictHom' (n := n) g) := by
  intro h1 h2 heq
  simp only [restrictHom', MonoidHom.mk'_apply] at heq
  apply Subtype.ext
  apply Subtype.ext
  apply eq_of_agree' g ((stab_iff_commute g h1.1).mp h1.2) ((stab_iff_commute g h2.1).mp h2.2)
  · intro x hxl hxm
    have h0 := congrArg Prod.fst heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxl, hxm⟩
    simpa [restrictTriple', Equiv.Perm.subtypePermOfFintype_apply] using hx
  · intro x hxr hxm
    have h0 := congrArg (Prod.fst ∘ Prod.snd) heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxr, hxm⟩
    simpa [restrictTriple', Equiv.Perm.subtypePermOfFintype_apply] using hx
  · intro x hxm
    have h0 := congrArg (Prod.snd ∘ Prod.snd) heq
    have hx := Equiv.ext_iff.mp h0 ⟨x, hxm⟩
    simpa [restrictTriple', Equiv.Perm.subtypePermOfFintype_apply] using hx

/-- `{x : α ⊕ β // x.isLeft ∧ P x} ≃ {a : α // P (Sum.inl a)}`. -/
def sumLeftSubtypeEquiv {α β : Type*} (P : α ⊕ β → Prop) :
    {x : α ⊕ β // x.isLeft ∧ P x} ≃ {a : α // P (Sum.inl a)} where
  toFun := fun ⟨x, hxl, hxp⟩ =>
    match x, hxl, hxp with
    | Sum.inl a, _, hxp => ⟨a, hxp⟩
  invFun := fun ⟨a, ha⟩ => ⟨Sum.inl a, rfl, ha⟩
  left_inv := fun ⟨x, hxl, hxp⟩ => by
    match x, hxl, hxp with
    | Sum.inl a, _, hxp => rfl
  right_inv := fun ⟨a, ha⟩ => rfl

/-- `{x : α ⊕ β // x.isRight ∧ P x} ≃ {b : β // P (Sum.inr b)}`. -/
def sumRightSubtypeEquiv {α β : Type*} (P : α ⊕ β → Prop) :
    {x : α ⊕ β // x.isRight ∧ P x} ≃ {b : β // P (Sum.inr b)} where
  toFun := fun ⟨x, hxr, hxp⟩ =>
    match x, hxr, hxp with
    | Sum.inr b, _, hxp => ⟨b, hxp⟩
  invFun := fun ⟨b, hb⟩ => ⟨Sum.inr b, rfl, hb⟩
  left_inv := fun ⟨x, hxr, hxp⟩ => by
    match x, hxr, hxp with
    | Sum.inr b, _, hxp => rfl
  right_inv := fun ⟨b, hb⟩ => rfl

/-- The mixed-support cardinalities, indexed by `Fin n` on each side. -/
noncomputable def aCard : ℕ := Nat.card {a : Fin n // IsMixed g (Sum.inl a)}

noncomputable def bCard : ℕ := Nat.card {b : Fin n // IsMixed g (Sum.inr b)}

lemma card_NonMixedA :
    Nat.card {x : Fin n ⊕ Fin n // x.isLeft ∧ ¬ IsMixed g x} = n - aCard g := by
  rw [Nat.card_congr (sumLeftSubtypeEquiv (fun x => ¬ IsMixed g x))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp [aCard, Nat.card_eq_fintype_card, Fintype.card_fin]

lemma card_NonMixedB :
    Nat.card {x : Fin n ⊕ Fin n // x.isRight ∧ ¬ IsMixed g x} = n - bCard g := by
  rw [Nat.card_congr (sumRightSubtypeEquiv (fun x => ¬ IsMixed g x))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp [bCard, Nat.card_eq_fintype_card, Fintype.card_fin]

lemma card_MixedA :
    Nat.card {x : Fin n ⊕ Fin n // MixedA g x} = aCard g := by
  show Nat.card {x : Fin n ⊕ Fin n // x.isLeft ∧ IsMixed g x} = aCard g
  rw [Nat.card_congr (sumLeftSubtypeEquiv (IsMixed g))]
  rfl

lemma card_MixedB :
    Nat.card {x : Fin n ⊕ Fin n // MixedB g x} = bCard g := by
  show Nat.card {x : Fin n ⊕ Fin n // x.isRight ∧ IsMixed g x} = bCard g
  rw [Nat.card_congr (sumRightSubtypeEquiv (IsMixed g))]
  rfl

theorem card_stabilizer_dvd_A :
    Nat.card ↥(MulAction.stabilizer ↥(Hgrp n) g) ∣
      (n - aCard g)! * (n - bCard g)! * (aCard g)! := by
  have hdvd := Subgroup.card_dvd_of_injective (restrictHom (n := n) g) (restrictHom_injective g)
  rw [Nat.card_prod, Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_perm,
    card_NonMixedA, card_NonMixedB, card_MixedA, ← mul_assoc] at hdvd
  exact hdvd

theorem card_stabilizer_dvd_B :
    Nat.card ↥(MulAction.stabilizer ↥(Hgrp n) g) ∣
      (n - aCard g)! * (n - bCard g)! * (bCard g)! := by
  have hdvd := Subgroup.card_dvd_of_injective (restrictHom' (n := n) g) (restrictHom'_injective g)
  rw [Nat.card_prod, Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_perm,
    card_NonMixedA, card_NonMixedB, card_MixedB, ← mul_assoc] at hdvd
  exact hdvd

theorem card_stabilizer_dvd_min :
    Nat.card ↥(MulAction.stabilizer ↥(Hgrp n) g) ∣
      (n - aCard g)! * (n - bCard g)! * min (aCard g)! (bCard g)! := by
  have hA := card_stabilizer_dvd_A g
  have hB := card_stabilizer_dvd_B g
  rcases le_total (aCard g)! (bCard g)! with hle | hle
  · rwa [min_eq_left hle]
  · rwa [min_eq_right hle]

/-- **The centralizer bound**: the manuscript's key valuation inequality
`v₂(|C_H(g)|) ≤ v₂((n-a)!) + v₂((n-b)!) + min(v₂(a!), v₂(b!))`. -/
theorem v2_stabilizer_le :
    v2 (Nat.card ↥(MulAction.stabilizer ↥(Hgrp n) g)) ≤
      v2 ((n - aCard g)!) + v2 ((n - bCard g)!) + min (v2 ((aCard g)!)) (v2 ((bCard g)!)) := by
  have hdvd := card_stabilizer_dvd_min g
  have hstabpos : Nat.card ↥(MulAction.stabilizer ↥(Hgrp n) g) ≠ 0 := Nat.card_ne_zero.mpr
    ⟨⟨1, MulAction.stabilizer ↥(Hgrp n) g |>.one_mem⟩, inferInstance⟩
  have hprodpos : (n - aCard g)! * (n - bCard g)! * min (aCard g)! (bCard g)! ≠ 0 := by positivity
  have hle : (Nat.card ↥(MulAction.stabilizer ↥(Hgrp n) g)).factorization 2 ≤
      ((n - aCard g)! * (n - bCard g)! * min (aCard g)! (bCard g)!).factorization 2 :=
    Nat.factorization_le_factorization_of_dvd_right hdvd hstabpos hprodpos
  have hval : ((n - aCard g)! * (n - bCard g)! * min (aCard g)! (bCard g)!).factorization 2 =
      v2 ((n - aCard g)!) + v2 ((n - bCard g)!) + v2 (min (aCard g)! (bCard g)!) := by
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
    simp [v2]
  have hminv2 : v2 (min (aCard g)! (bCard g)!) = min (v2 ((aCard g)!)) (v2 ((bCard g)!)) := by
    rcases le_total (aCard g) (bCard g) with hle' | hle'
    · rw [min_eq_left (Nat.factorial_le hle')]
      exact (min_eq_left (v2_factorial_mono hle')).symm
    · rw [min_eq_right (Nat.factorial_le hle')]
      exact (min_eq_right (v2_factorial_mono hle')).symm
  rw [hval, hminv2] at hle
  simpa [v2] using hle

lemma exists_mixed_pair (hg : g ∉ Hgrp n) : ∃ a b, g (Sum.inl a) = Sum.inr b := by
  by_contra hc
  push_neg at hc
  apply hg
  apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
  rintro x ⟨a, rfl⟩
  rcases hgx : g (Sum.inl a) with a' | b'
  · exact ⟨a', rfl⟩
  · exact absurd hgx (hc a b')

theorem one_le_aCard (hg : g ∉ Hgrp n) : 1 ≤ aCard g := by
  obtain ⟨a, b, hab⟩ := exists_mixed_pair g hg
  have hmixed : IsMixed g (Sum.inl a) := ⟨⟨a, SameCycle.refl g _⟩, ⟨b, ⟨1, by simpa using hab⟩⟩⟩
  haveI : Nonempty {a : Fin n // IsMixed g (Sum.inl a)} := ⟨⟨a, hmixed⟩⟩
  exact Nat.card_pos

theorem one_le_bCard (hg : g ∉ Hgrp n) : 1 ≤ bCard g := by
  obtain ⟨a, b, hab⟩ := exists_mixed_pair g hg
  have hmixed : IsMixed g (Sum.inl a) := ⟨⟨a, SameCycle.refl g _⟩, ⟨b, ⟨1, by simpa using hab⟩⟩⟩
  have hsc : g.SameCycle (Sum.inl a) (Sum.inr b) := ⟨1, by simpa using hab⟩
  have hmixed' : IsMixed g (Sum.inr b) := (isMixed_of_sameCycle g hsc).mp hmixed
  haveI : Nonempty {b : Fin n // IsMixed g (Sum.inr b)} := ⟨⟨b, hmixed'⟩⟩
  exact Nat.card_pos

theorem aCard_le (g : Equiv.Perm (Fin n ⊕ Fin n)) : aCard g ≤ n := by
  rw [aCard]
  have : Nat.card {a : Fin n // IsMixed g (Sum.inl a)} ≤ Nat.card (Fin n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  simpa using this

theorem bCard_le (g : Equiv.Perm (Fin n ⊕ Fin n)) : bCard g ≤ n := by
  rw [bCard]
  have : Nat.card {b : Fin n // IsMixed g (Sum.inr b)} ≤ Nat.card (Fin n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  simpa using this

end CongruenceTheory
