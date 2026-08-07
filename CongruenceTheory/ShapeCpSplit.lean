import Mathlib
import CongruenceTheory.Basic
import CongruenceTheory.CpermEqC
import CongruenceTheory.ConnectedCumulant
import CongruenceTheory.PartitionGluing
import CongruenceTheory.PartitionRespects
import CongruenceTheory.ConnectedCount
import CongruenceTheory.GeneralizedConnectivity
import CongruenceTheory.GeneralizedConnectivityTransport
import CongruenceTheory.GeneralizedConnectivityTop
import CongruenceTheory.GeneralizedPartitionGluing
import CongruenceTheory.GeneralizedAssembleTop
import CongruenceTheory.GeneralizedPiOfAssemble
import CongruenceTheory.GeneralizedGfunTopK
import CongruenceTheory.GeneralizedGfunProd
import CongruenceTheory.MacroMicroRelabel
import CongruenceTheory.MacroMicroReach
import CongruenceTheory.PartGraph
import CongruenceTheory.GeneralizedGfunFilter
import CongruenceTheory.MacroMicroSum
import CongruenceTheory.PartitionShape
import CongruenceTheory.MacroMicroShape
import CongruenceTheory.A3Final

/-!
**Separating out the `C_p^{m_1}` factor for singleton blocks**, matching the manuscript's own
written form `C_p^{m_1}∏_{j≥2}K_j(p)^{m_j}` verbatim rather than leaving it folded into the
undifferentiated shape-product. Uses `K_one : K 1 q = C q` to turn the "these already coincide"
observation from a README claim into an actual proof.
-/

namespace CongruenceTheory

open scoped Classical

/-- The shape-product splits off a `C p` power for every `1` in the shape multiset (using
`K_one`), leaving a product over the non-singleton block sizes. -/
theorem shape_prod_eq_Cp_pow_mul_prod (lam : Multiset ℕ) (p : ℕ) :
    (lam.map (fun j => K j p)).prod =
      (C p) ^ (lam.count 1) * ((lam.filter (· ≠ 1)).map (fun j => K j p)).prod := by
  induction lam using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih]
    by_cases ha : a = 1
    · subst ha
      simp [Multiset.count_cons, Multiset.filter_cons, Multiset.map_add, Multiset.prod_add,
        K_one, pow_succ, mul_assoc, mul_left_comm]
    · simp [Multiset.count_cons, Multiset.filter_cons, ha, Ne.symm ha, Multiset.map_add,
        Multiset.prod_add, mul_assoc, mul_left_comm]

/-- **`K_r(Qp)` in the manuscript's own written form**: a partition-shape-weighted sum with the
`C_p^{m_1}` factor for singleton microblocks made explicit, separated from the product over
non-singleton block sizes. -/
theorem K_eq_sum_shapeCount_Cp_pow_mul_prod (r Q p : ℕ) :
    K r (Q * p) = ∑ lam ∈ (connSet r Q).image GenPartLatShape,
      (shapeCount (connSet r Q) lam) •
        ((C p) ^ (lam.count 1) * ((lam.filter (· ≠ 1)).map (fun j => K j p)).prod) := by
  rw [K_eq_sum_shapeCount_prod_K]
  exact Finset.sum_congr rfl (fun lam _ => by rw [shape_prod_eq_Cp_pow_mul_prod])

end CongruenceTheory
