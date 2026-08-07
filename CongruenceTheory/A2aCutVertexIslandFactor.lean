import Mathlib
import CongruenceTheory.A2aOrbitBound
import CongruenceTheory.A2aCutVertexComponents
import CongruenceTheory.A2aCutVertexComponentAction
import CongruenceTheory.A2aCutVertexAttachment
import CongruenceTheory.A2aCutVertexInvariance
import CongruenceTheory.A2aCutVertexFixesC0
import CongruenceTheory.A2aCutVertexIslandMap
import CongruenceTheory.A2aCutVertexIslandPermMul
import CongruenceTheory.A2aCutVertexIslandInstance
import CongruenceTheory.A2aCutVertexIslandG
import CongruenceTheory.A2aCutVertexIslandHperm
import CongruenceTheory.A2aCutVertexIslandHom
import CongruenceTheory.A2aRootBound
import CongruenceTheory.CentralizerCycleFaithful

/-!
**The Noether/Lagrange cardinality factorization for the island homomorphism**:
`Nat.card(PtStab A p₀) = Nat.card(range) * Nat.card(ker)`. `range` is a genuine subgroup of
`Equiv.Perm(island)` — to be bounded via `card_le_root_bound` (with the island's own `IsPartition`/
`hne`/`hcent`/`hperm` now all established) for (A2a)'s per-component cut-vertex factor — and `ker`
(elements of `PtStab A p₀` fixing the whole island pointwise) is the subgroup to recurse into for
the remaining, non-`c0` components.
-/

open Equiv

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- `Nat.card (PtStab A p₀)` factors as `range * ker` for the island homomorphism (Noether's
first isomorphism theorem + Lagrange). -/
theorem card_ptStab_eq_range_mul_ker {V : ι → Finset Ω} (hpart : IsPartition V)
    (hne : ∀ i, (V i).Nonempty) {A : Subgroup (Equiv.Perm Ω)} {g : Equiv.Perm Ω}
    (hcent : ∀ φ ∈ A, Commute φ g) (hperm : ∀ φ ∈ A, ∀ i, ∃ j, (V i).image φ = V j) {u : ι}
    (hblock_u : ∀ φ ∈ A, (V u).image φ = V u) {p₀ : Ω} {c0 : BlockComponent V g u}
    (hreach : Reaches g u p₀ c0) :
    Nat.card (PtStab A p₀) =
      Nat.card (MonoidHom.range (islandHom hpart hne hcent hperm hblock_u hreach)) *
        Nat.card (MonoidHom.ker (islandHom hpart hne hcent hperm hblock_u hreach)) := by
  set f := islandHom hpart hne hcent hperm hblock_u hreach
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker f),
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
