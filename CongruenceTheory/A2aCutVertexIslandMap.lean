import Mathlib
import CongruenceTheory.A2aOrbitBound
import CongruenceTheory.A2aCutVertexComponents
import CongruenceTheory.A2aCutVertexComponentAction
import CongruenceTheory.A2aCutVertexAttachment
import CongruenceTheory.A2aCutVertexInvariance
import CongruenceTheory.A2aCutVertexFixesC0
import CongruenceTheory.A2aRootBound
import CongruenceTheory.CentralizerCycleFaithful

/-!
**`PtStab A p₀` maps `p₀`'s own island into itself.** Combined with `inComponentPlus_iff`
(`g` itself is island-invariant), this is the last structural fact needed before packaging the
island restriction as a genuine `Equiv.Perm` and building the restriction homomorphism
`PtStab A p₀ → Perm(island)` — the mechanism that will let `card_le_root_bound` be applied to the
image, treating `p₀`'s component's attachment points as a virtual root, to get the per-component
factor of (A2a)'s cut-vertex bound.
-/

open Equiv

variable {Ω ι : Type*} [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- `φ` fixing `p₀`, commuting with `g`, maps the island of `p₀`'s own component into itself
(as a function, not yet packaged as a permutation). -/
theorem inComponentPlus_apply_of_fixes {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    {φ : Equiv.Perm Ω} (hφ : φ ∈ A) (hu : (V u).image φ = V u) {p₀ : Ω} (hfix : φ p₀ = p₀)
    {c0 : BlockComponent V g u} (hreach : Reaches g u p₀ c0) {x : Ω}
    (hx : InComponentPlus g u c0 x) : InComponentPlus g u c0 (φ x) := by
  have hfixc : componentPermOfMem hpart hne hcent hperm hφ hu c0 = c0 :=
    componentPermOfMem_fixes_reached hpart hne hcent hperm hφ hu hfix hreach
  rcases hx with ⟨i, hi, hxi⟩ | ⟨hxu, hxreach⟩
  · left
    refine ⟨blockPermSub hpart hne hperm hφ hu i, ?_, ?_⟩
    · have hmk := componentPermOfMem_mk hpart hne hcent hperm hφ hu i
      rw [hi, hfixc] at hmk
      exact hmk.symm
    · rw [blockPermSub_coe, ← blockOfElt_spec hpart hperm φ hφ i.1]
      exact Finset.mem_image_of_mem φ hxi
  · right
    obtain ⟨x1, hx1, y1, hy1, k, hk⟩ := hxreach
    have hu' : φ x ∈ V u := hu ▸ Finset.mem_image_of_mem φ hxu
    refine ⟨hu', blockPermSub hpart hne hperm hφ hu x1, ?_, φ y1, ?_, k, ?_⟩
    · have hmk := componentPermOfMem_mk hpart hne hcent hperm hφ hu x1
      rw [hx1, hfixc] at hmk
      exact hmk.symm
    · rw [blockPermSub_coe, ← blockOfElt_spec hpart hperm φ hφ x1.1]
      exact Finset.mem_image_of_mem φ hy1
    · have h1 : (φ * g ^ k) x = (g ^ k * φ) x := by rw [((hcent φ hφ).zpow_right k).eq]
      simp only [Equiv.Perm.mul_apply] at h1
      rw [hk] at h1
      exact h1.symm
