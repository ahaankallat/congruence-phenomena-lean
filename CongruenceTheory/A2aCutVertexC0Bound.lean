import Mathlib
import CongruenceTheory.A2aOrbitBound
import CongruenceTheory.A2aCutVertexComponents
import CongruenceTheory.A2aCutVertexAttachment
import CongruenceTheory.A2aCutVertexInvariance
import CongruenceTheory.A2aCutVertexIslandMap
import CongruenceTheory.A2aCutVertexIslandPerm
import CongruenceTheory.A2aCutVertexIslandPermMul
import CongruenceTheory.A2aCutVertexIslandInstance
import CongruenceTheory.A2aCutVertexIslandG
import CongruenceTheory.A2aCutVertexIslandHperm
import CongruenceTheory.A2aCutVertexIslandHom
import CongruenceTheory.A2aCutVertexIslandFactor
import CongruenceTheory.A2aCutVertexIslandNone
import CongruenceTheory.A2aCutVertexIslandMixed
import CongruenceTheory.A2aCutVertexIslandConn
import CongruenceTheory.A2aCutVertexIslandInitEdge
import CongruenceTheory.A2aCutVertexDistinguished
import CongruenceTheory.A2aRootBound
import CongruenceTheory.PtStabProdBound
import CongruenceTheory.IslandTightBound
import CongruenceTheory.CentralizerCycleFaithful

/-!
**(A2a)'s distinguished-component cut-vertex bound.** Combining the orbit confinement
(`card_le_ambientC0Attach_mul_card_ptStab`), the Noether/Lagrange kernel factorization
(`card_ptStab_eq_range_mul_ker`), and the tight island block-product bound
(`card_le_island_tight_bound`) gives
`Nat.card A ≤ a_0 · ∏_{i∈c0}(R_i-1)! · Nat.card(ker(islandHom))`,
exactly the `C_0`-branch's contribution to the manuscript's cut-vertex bound. `ker(islandHom)`
(elements of `A` fixing `p₀` and all of `c0`'s island pointwise) is what remains to bound for the
other rooted-isomorphism-type branches.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

theorem card_le_cutVertex_c0_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {j2 : ι} (hj2u : j2 ≠ u)
    (hblock_j2 : ∀ φ ∈ A, (V j2).image φ = V j2) {p₀ : Ω} (hp₀u : p₀ ∈ V u)
    (hp₀reach : Reaches g u p₀ (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)) :
    Nat.card A ≤
      (AmbientC0Attach g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)).card *
        (∏ i ∈ Finset.univ.erase
              (none : IslandBlockIdx g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩)),
            Nat.factorial
              ((IslandV g u (Quot.mk (BlockReach V g u) ⟨j2, hj2u⟩) i).card - 1)) *
        Nat.card (MonoidHom.ker
          (islandHom hpart hne hcent hperm hblock_u hp₀reach)) := by
  set c0 := Quot.mk (BlockReach V g u) (⟨j2, hj2u⟩ : {i : ι // i ≠ u})
  have hstep1 := card_le_ambientC0Attach_mul_card_ptStab hpart hne hcent hperm hblock_u hj2u
    hblock_j2 hp₀u hp₀reach
  have hstep2 := card_ptStab_eq_range_mul_ker hpart hne hcent hperm hblock_u hp₀reach
  have hstep3 := card_le_island_tight_bound hpart hne hcent hperm hblock_u hp₀u hp₀reach
  calc Nat.card A ≤ (AmbientC0Attach g u c0).card * Nat.card (PtStab A p₀) := hstep1
    _ = (AmbientC0Attach g u c0).card *
          (Nat.card (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hp₀reach)) *
            Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach))) := by
        rw [hstep2]
    _ ≤ (AmbientC0Attach g u c0).card *
          ((∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
              Nat.factorial ((IslandV g u c0 i).card - 1)) *
            Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach))) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_right _ hstep3
    _ = (AmbientC0Attach g u c0).card *
          (∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
              Nat.factorial ((IslandV g u c0 i).card - 1)) *
            Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hp₀reach)) := by
        rw [mul_assoc]
