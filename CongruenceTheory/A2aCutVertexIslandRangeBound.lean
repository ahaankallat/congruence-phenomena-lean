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
import CongruenceTheory.A2aCutVertexIslandNone
import CongruenceTheory.A2aCutVertexIslandMixed
import CongruenceTheory.A2aCutVertexIslandConn
import CongruenceTheory.A2aCutVertexIslandInitEdge
import CongruenceTheory.A2aRootBound
import CongruenceTheory.CentralizerCycleFaithful

/-!
**The per-component cut-vertex bound**: `card_le_root_bound` applied to the island, bounding
`Nat.card(range(islandHom))` — the "restriction image" of `PtStab A p₀` acting on `p₀`'s own
component's island — by the island's own root-bound formula. Combined with
`card_ptStab_eq_range_mul_ker`, this gives the per-component factor of (A2a)'s cut-vertex bound,
with the kernel left over to recurse into for the remaining components.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

noncomputable instance instFintypeInComponentPlus {V : ι → Finset Ω} {g : Equiv.Perm Ω} {u : ι}
    {c0 : BlockComponent V g u} : Fintype {x : Ω // InComponentPlus g u c0 x} :=
  Fintype.ofFinite _

theorem card_le_island_range_bound {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} (hp₀u : p₀ ∈ V u) {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) :
    Nat.card (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hreach)) ≤
      (IslandV g u c0 none).card *
        ∏ i ∈ Finset.univ.erase (none : IslandBlockIdx g u c0),
          Nat.factorial ((IslandV g u c0 i).card - 1) := by
  obtain ⟨j₀, hj₀ne, y₀, hy₀mem, hp₀y₀⟩ := island_init_edge hpart g u hp₀u hreach
  refine card_le_root_bound (islandV_isPartition hpart g u c0) ?_ ?_ none ?_
    ⟨p₀, Or.inr ⟨hp₀u, hreach⟩⟩ ((mem_islandV_none g u c0 _).mpr hp₀u)
    (island_hmixed hpart g u c0) hj₀ne hy₀mem hp₀y₀ (island_hconn hpart g u c0)
  · rintro φ ⟨a, rfl⟩
    exact islandPermOfPtStab_commute hpart hne hcent hperm hblock_u hreach a.1 a.2
  · rintro φ ⟨a, rfl⟩ i
    exact islandPermOfPtStab_perm hpart hne hcent hperm hblock_u hreach a.1 a.2 i
  · rintro φ ⟨a, rfl⟩
    exact islandPermOfPtStab_none hpart hne hcent hperm hblock_u hreach a.1 a.2
