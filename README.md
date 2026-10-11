# Universal Shift Congruences for Weighted Permutation Sequences — Lean

A Lean 4 / Mathlib formalization of the paper *Universal Shift Congruences for
Weighted Permutation Sequences* (A. Kallat), covering the shift congruence, the
exact content of the two-term defect, the strong two-adic lift and the explicit
power-of-two residue theorem.

The second paper, *Higher-Order Defects of Cycle-Index Polynomials* (connected
cumulants and the prime-local classification of higher-order defects), is
formalized separately, together with the lifting theorem at every prime and the
Lagrange-type theorem of the main paper, in
[`congruence-phenomena-higher-order-lean`](https://github.com/ahaankallat/congruence-phenomena-higher-order-lean),
which depends on this repository as a Lake library dependency for its
foundational cycle-index and orbit-counting machinery.

## Status: both principal theorems fully verified, zero `sorry`, zero paper-specific axioms


- **Theorem `thm:universal`** ("Symmetric universal shift congruence") —
  **complete**, both the mod-`k` case (`universal_shift_mod`,
  `Universal.lean`) and the full symmetric `lcm(n,k)` strengthening
  (`universal_shift_lcm`), proved by combining the mod-`k` and mod-`n`
  cases via `DvdCoeffs`/Lagrange-free elementary `lcm`-divisibility.
- **Its easy corollaries** — `CongruenceTheory/WeightedSpecialization.lean`
  specializes the universal polynomial congruence to weighted-permutation
  sequences `A_w` (via `MvPolynomial.eval`/`eval₂_comp`), giving:
  `Aw_shift_mod` (the `A_w` form of `thm:universal`), `Aw_iterated`
  (**Corollary `cor:iterated`**), `Aw_translation_eigenvector` (the
  eigenvector corollary), and `Aw_dynamics` (**Corollary `cor:dynamics`**).
  `CongruenceTheory/FixedModulusClassification.lean` proves
  **Theorem `thm:fixed-modulus-classification`** standalone (an iff for
  *any* integer sequence with `a_0=1`, independent of the cycle-index
  machinery). Not formalized: **Theorem `thm:poly`** (the extra-variable-`t`
  polynomial refinement) — same induction, over `Polynomial ℤ` instead of
  `ℤ`, genuinely low marginal value over what's already proved, skipped for
  now.
- **Theorem `thm:power-of-two`** ("Explicit power-of-two residue") and its corollary
  (`cor:power-of-two-01`) — **complete**, `CongruenceTheory/PowerOfTwoResidue.lean`, zero `sorry`,
  `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`. With
  `α = w₁ + w₂`, `β = w₂ + w₄`: `power_of_two_r1/r2/r3` give `A_w(2) ≡ α (2)`,
  `A_w(4) ≡ α² + 2β (4)`, `A_w(8) ≡ α⁴ + 4α²β + 4β² (8)`; `power_of_two_residue` gives
  `A_w(2^r) ≡ α^(2^(r-1)) (mod 2^r)` for every `r ≥ 4`; `power_of_two_zero_one` shows the residue
  is `1` or `0` according to the parity of `α`. The proof needs only `Aw_two_adic` (the strong
  lift stated for the recurrence-native `A_w`, derived from `strong_two_adic` via `Cperm_eq_C`)
  and the explicit values of `A_w(2)` and `A_w(4)`.
- **Theorem `thm:strong`** ("Strong two-adic lifting") —
  `CongruenceTheory.strong_two_adic`, in `CongruenceTheory/StrongTwoAdic.lean`:
  `∃ Q, CpermSum(2^s) − Cperm(2^s)·Cperm(2^s) = 2^(2s−1) · Q` for every `s ≥ 1`,
  where `Cperm`/`CpermSum` are the permutation-native cycle-index
  polynomials (`CongruenceTheory/Perm.lean`). `#print axioms` reports only
  `[propext, Classical.choice, Quot.sound]` — Lean/Mathlib's standard
  foundational axioms, nothing paper-specific.

  This is the manuscript's actual hard theorem, proved by formalizing its
  full orbit-counting argument end to end:
  1. **Lemma `lem:orbit-bound`** (`OrbitBound.lean`) — the numerical core,
     via Mathlib's Legendre/Kummer `Nat.factorization` API. Shorter than
     the manuscript's own proof (skips its digit-sum monotonicity lemma).
  2. **Cycle-index algebra** (`Perm.lean`) — `Cperm`/`CpermSum`, the
     cycle-type gluing theorem for `sumCongr` (via `extendDomain` +
     `Disjoint.cycleType_mul`), and the identities `Cperm(n)² = ∑_{h∈H} ci h`
     and `CpermSum(n) − Cperm(n)² = ∑_{g∉H} ci g` (`H = Perm A × Perm B`,
     embedded via `sumCongrHom`).
  3. **The class-sum divisibility engine** (`OrbitSum.lean`) — a
     from-scratch, group-theory-free lemma: summing a class-invariant
     function over a finite set partitioned into `d`-divisible classes is
     divisible by `d` (strong induction on `Finset.card`).
  4. **`H`-conjugation and orbit-stabilizer** (`Conj.lean`) — the
     conjugation `MulAction`, invariance of `Hᶜ`, and
     `class_card_mul_stabilizer_card`: `(orbit size)·|C_H(g)| = n!·n!`,
     exactly.
  5. **The centralizer bound** (`Centralizer.lean`) — the manuscript's
     actual mathematical content: the "mixed cycles restrict faithfully"
     argument. Defines the mixed-cycle support via `Equiv.Perm.SameCycle`;
     proves that an element of `C_H(g)` fixing every mixed point of `A`
     fixes the whole mixed structure (`eq_of_agree`, via "commutes with
     `g` and fixes one point of a cycle ⇒ fixes the whole cycle"); builds
     two injective group homomorphisms `C_H(g) → Perm(A∖M_A) × Perm(B∖M_B)
     × Perm(M_A)` (and the `M_B` mirror) via `Equiv.Perm.subtypePermOfFintype`;
     gets **exact** divisibility `|C_H(g)| ∣ (n−a)!(n−b)!·a!` (and the
     `b!` mirror) from Lagrange (`Subgroup.card_dvd_of_injective`) — sharper
     than a mere inequality, which is what makes the final valuation
     comparison work; combines to
     `v₂(|C_H(g)|) ≤ v₂((n-a)!) + v₂((n-b)!) + min(v₂(a!), v₂(b!))`.
  6. **Final assembly** (`StrongTwoAdic.lean`) — combines 1–5: for
     `n = 2^s`, every `g ∉ H` has `2^(2s-1) ∣ |orbit(g)|`; feeding this into
     the class-sum engine closes the theorem.

  Mathlib's `Equiv.Perm.nat_card_centralizer`/`card_of_cycleType`
  (`Mathlib.GroupTheory.Perm.Centralizer`) compute centralizers/conjugacy
  classes in the *full* symmetric group — not directly usable here, since
  the theorem needs the centralizer *within the subgroup* `H`, which is
  smaller and required the from-scratch faithfulness argument above.

No error, gap, or false claim was found anywhere in this process — every
formalized result confirms the manuscript exactly (the orbit-bound lemma
even improves on the manuscript's own proof).


## File-by-file breakdown

- **`CongruenceTheory/Basic.lean`** — falling factorial, cycle-index
  polynomial `C` via the manuscript's recurrence.
- **`CongruenceTheory/Universal.lean`** — Theorem `thm:universal`, mod-`k`.
- **`CongruenceTheory/OrbitBound.lean`** — Lemma `lem:orbit-bound`.
- **`CongruenceTheory/Perm.lean`** — `Cperm`/`CpermSum`, cycle-type gluing,
  `H`-embedding sum identity.
- **`CongruenceTheory/OrbitSum.lean`** — the class-sum divisibility engine.
- **`CongruenceTheory/Conj.lean`** — `H`-conjugation action,
  orbit-stabilizer specialized.
- **`CongruenceTheory/Centralizer.lean`** — the centralizer-in-`H` bound
  (the manuscript's hard theorem).
- **`CongruenceTheory/StrongTwoAdic.lean`** — final assembly:
  `strong_two_adic`, Theorem `thm:strong`.
- **`CongruenceTheory/WeightedSpecialization.lean`** — `A_w` specialization
  of `thm:universal` and its easy corollaries (`cor:iterated`, eigenvector,
  `cor:dynamics`).
- **`CongruenceTheory/FixedModulusClassification.lean`** — Theorem
  `thm:fixed-modulus-classification`, standalone.
- **`CongruenceTheory/TranslationModuli.lean`** — Theorem
  `thm:translation-moduli` (i)⟺(ii): coefficientwise divisibility of a
  universal `MvPolynomial` identity is equivalent to divisibility of the
  value after every ring specialization. A general fact, independent of `C`.

- **`CongruenceTheory/CoeffExtraction.lean`** — the coefficient-extraction
  bridge: `ciExp` (the exponent-vector encoding of a cycle type), `ci g =
  monomial (ciExp ...) 1`, and `coeff_Cperm_eq_card_cycleType`: the
  coefficient of the monomial for cycle type `m` in `Cperm N` is exactly
  `#{g | cycleType g = m}`.
- **`CongruenceTheory/StrongWeighted.lean`** — **`cor:weighted`**
  ("Weighted-permutation specialization"), permutation-native form:
  `AwPerm_two_adic_dynamics` specializes `thm:strong` itself
  (`strong_two_adic`, not just `thm:universal`) via `MvPolynomial.eval`,
  giving `A_w(2^{s+1}) ≡ A_w(2^s)^2 (mod 2^{2s-1})` for *every* integral
  weight sequence `w` — no positivity assumption, matching the manuscript.
  `AwPerm_two_adic_dynamics_uvar` is the coefficientwise `ℤ[u]` form (a
  cycle-counting variable `u`), via `MvPolynomial.eval₂` into
  `Polynomial ℤ`. This is genuinely new content: `thm:strong`'s own proof
  never needed to specialize the polynomial identity, only sum whole
  `H`-orbits, so this bridge didn't exist before. (The paper's concrete
  named instances — `OEIS{A000085}` involutions, `OEIS{A000166}`
  derangements, `OEIS{A028342}`, etc. — are direct substitutions of `w`
  into the one general theorem above; not separately formalized here, matching
  how the manuscript itself treats them as immediate substitutions with no
  separate proof.)
- **`CongruenceTheory/ContentBounds.lean`** — **`prop:content-bounds`,
  upper half, complete**: `coeff_defect_eq_nk` proves
  `[X_1^{n+k-2}X_2](CpermPair n k - Cperm n · Cperm k) = nk` exactly
  (permutation-native). Built via `Cperm_mul` (generalizing `Cperm_sq` to
  unequal `n,k`), `ciExp_add`/`multiset_add_eq_singleton_iff` (characterizing
  which permutation pairs contribute to that monomial), and
  `card_twoCycle_eq_choose`/`two_mul_card_twoCycle` (computed directly from
  Mathlib's `Equiv.Perm.card_of_cycleType`, avoiding division by working
  with everything doubled).

- **`CongruenceTheory/MixedSupportFactorial.lean`** — **`lem:mixed-support-factorial`**,
  fully general in the prime `p` and in `(n,k)` (not just the `n=k=2^s`,
  `p=2` case used for `thm:strong`): for `p^a ∣ n`, `p^b ∣ k`, `1≤r≤n`,
  `1≤s≤k`, `a+b+min(v_p(r!),v_p(s!)) ≤ v_p(n.descFactorial r) +
  v_p(k.descFactorial s) + 1` (`descFactorial` form of the manuscript's
  `v_p(n!k!/((n-r)!(k-s)!)) - min(v_p(r!),v_p(s!)) ≥ a+b-1`, restated with
  the `min` moved to the same side as `a+b` to avoid truncated-subtraction
  pitfalls). The manuscript's own proof of the crux step (`v_p(r!)≤v_p(s!)
  ⟹ v_p(r) ≤ v_p((s-1)!)+1`) was reworked into a cleaner growth-rate
  argument built on Mathlib's `padicValNat_factorial_mul`
  (`v_p((p·n)!) = v_p(n!) + n`): `padicValNat_factorial_pow_ge` shows
  `v_p((p^c)!) ≥ 2c-1` by induction, which both bounds `r` from below
  (`r ≥ p^{v_p(r)}`) and, via a contradiction argument, bounds `v_p(s)`
  above by `c-1`, closing the inequality without the manuscript's own
  digit-counting case split. The Kummer-type half (`v_p(C(n,r)) ≥ v_p(n) -
  v_p(r)`) came directly from Mathlib's
  `Nat.factorization_le_factorization_choose_add`, needing no new proof at
  all. (An earlier draft of this lemma had the `min` on the wrong side —
  a strictly weaker statement — which wasn't caught until wiring it into
  the theorem below forced `omega` to fail; fixed by re-deriving the
  correct inequality direction from the same proof, confirmed by hand
  first this time.)
- **`CongruenceTheory/ConjPair.lean`** / **`CongruenceTheory/CentralizerPair.lean`** —
  the `(n,k)`-and-general-`p` counterparts of `Conj.lean`/`Centralizer.lean`:
  same conjugation action, "mixed cycles restrict faithfully" argument, and
  centralizer bound (`vp_stabilizer_le_pair`), just re-typed on
  `Fin n ⊕ Fin k` instead of `Fin n ⊕ Fin n` and for a general prime `p`
  instead of `p=2` (`Centralizer.lean`/`Conj.lean` themselves are
  untouched, since `StrongTwoAdic.lean` still depends on them). Purely
  mechanical generalization — same proofs, different types — and compiled
  almost immediately once the one real bug (a dropped explicit `g`
  argument at several call sites, an artifact of the mechanical rewrite)
  was fixed.
- **`CongruenceTheory/OptimalDivisorLower.lean`** — **`thm:optimal-divisor`,
  lower bound, complete and fully general**: `optimal_divisor_lower_bound`
  proves that for *every* prime `p` and *every* `n,k ≥ 1`, every
  coefficient of `CpermPair n k - Cperm n · Cperm k` is divisible by
  `p^(v_p(n)+v_p(k)-1)` — combining `vp_stabilizer_le_pair`,
  `mixed_support_factorial`, and the class-sum divisibility engine
  (`OrbitSum.lean`) exactly as `StrongTwoAdic.lean` combined `orbit_bound`,
  `v2_stabilizer_le`, and the same engine for `thm:strong`. This is the
  "it remains to prove the lower bound at a common prime `p`" half of the
  manuscript's own proof of `thm:optimal-divisor`.
- **`CongruenceTheory/SupportTheorem.lean`** — **`prop:support`**,
  permutation-native form: `AwPerm_eq_zero_of_not_mem_Gamma` proves that if
  `n` isn't in the numerical semigroup `Γ(w)` generated by `supp(w)`
  (`Gamma`, defined here — fixed points count as length-`1` parts, so
  `1` is a generator only when `w 1 ≠ 0`, matching the manuscript's own
  definition exactly), then `AwPerm w n = 0`. Proved by evaluating `eval w
  (ci g)` for every permutation `g` directly as `w 1 ^ (fixed points) *
  ∏_{ℓ ∈ cycleType g} w ℓ` (`eval_ci`, via applying `eval w` to
  `pow_mul_multisetProd_eq_monomial` from `CoeffExtraction.lean`) and
  showing any nonzero term would witness `n ∈ Γ(w)`.
  `AwPerm_eq_zero_below_min_support` derives the manuscript's first "in
  particular" clause (`AwPerm w n = 0` for `1 ≤ n < d` where `d` is the
  least index with `w d ≠ 0`) as a corollary. (The second clause, the exact
  value `AwPerm w d = (d-1)! · w d`, needs an additional argument — that
  only the single-`d`-cycle permutations survive — not formalized here;
  the vanishing statements are the substantive content.)
- **`CongruenceTheory/FiniteWidth.lean`** — **`prop:finitewidth`**,
  complete: `Aw_finiteWidth` proves that if `w j = 0` for `j > h`, then
  `A_w(n+1) = ∑_{r∈range(min(n+1,h))} (n)_r · w_{r+1} · A_w(n-r)` (the
  `min(n+1,h)` bound avoids the truncated-subtraction pitfall of the
  manuscript's own `min(n,h-1)` when `h = 0`). Falls directly out of
  `C_succ`, the falling-factorial recurrence already used to *define* `C`
  in `Basic.lean`: apply `eval w`, then `Finset.sum_subset` to discard the
  terms `r ≥ h` whose `w (r+1)` factor vanishes. The most direct
  formalization this session — no new machinery needed, uses only what
  `Basic.lean`/`WeightedSpecialization.lean` already provide.
- **`CongruenceTheory/GaussCongruence.lean`** — **`thm:gauss`, complete,
  both directions of the iff**: `gauss_iff` proves `(∀N≥1, N∣M_N) ↔
  (∀p,r≥1,m≥1 with p∤m, w_{mp^r} ≡ w_{mp^{r-1}} (mod p^r))`, where
  `M_N = ∑_{d∣N} μ(N/d)·w_d` is the Möbius transform of `w`. This is the
  theorem that was **attempted and abandoned twice earlier this session**
  on exactly this kind of divisor-lattice reindexing; the third attempt
  succeeded by validating every sub-lemma standalone in isolation before
  assembling them (the same discipline that made `PrimeValue.lean` land),
  rather than writing the whole proof at once. The crux (`key_identity`,
  used by both directions): for `p∤m`, `r≥1`, `M_{mp^r} = ∑_{e∣m}
  μ(m/e)·(w_{ep^r} - w_{ep^{r-1}})`, via `sum_divisors_mul_prime_pow_reindex`
  (splitting divisors of `m·p^r` into `e·p^i` pairs, using
  `Nat.Coprime.divisors_mul` and `Nat.divisors_prime_pow` — the exact
  reindexing that broke both earlier attempts) combined with
  multiplicativity of `μ` collapsing the `i`-sum to just `i=r,r-1`
  (`μ(p^j)=0` for `j≥2`). `gauss_of_dvd_forall` (`⟸`) uses `key_identity`
  plus Möbius inversion, free from Mathlib's own
  `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq` exactly as
  anticipated. `dvd_forall_of_gauss` (`⟹`) uses `key_identity` plus
  Mathlib's `Nat.dvd_iff_prime_pow_dvd_dvd` (`d∣n ↔ ∀p k, p^k∣d → p^k∣n`)
  to avoid the induction-over-prime-factors combination step that looked
  like the hard part in earlier planning — reducing to `N = m·p^{v_p(N)}`
  via `Nat.ordProj_dvd`/`not_dvd_ordCompl` made both directions the same
  shape, once `key_identity` was in hand.
- **`CongruenceTheory/PowerSeriesLog.lean`** — **`log(AB) = log A + log B`
  for formal power series**, genuinely new infrastructure Mathlib itself
  doesn't have (checked directly: `PowerSeries.Log` defines `log(1+X)` and
  `logOf`, with `logOf_one_add_X`, but no multiplicativity law — this was
  the fact blocking `thm:multiplicative-functoriality` and the entire
  canonical-coordinates chapter). Proved via the classical route:
  `d⁄dX A` is a `Derivation` (Leibniz for free), the log-derivative
  `D(logOf f)·f = D(f)` (`deriv_logOf_mul_self`, via Mathlib's own
  `derivative_subst` chain rule composed with the geometric series
  `(1+X)·∑(-1)ⁿXⁿ = 1`, itself proved by hand — `geom_inv` — since a
  Mathlib search for it timed out), then two power series over a `ℚ`-algebra
  with equal derivative and equal constant term are equal
  (`deriv_injective_of_const`, using that `n+1` is always invertible via
  `algebraMap ℚ A`, working in *every* `ℚ`-algebra, not just fields).
  Combining the log-derivative rule for `f`, `g`, and `fg` via Leibniz and
  cancelling the unit `fg` gives `logOf_mul`. `canonicalCoord_mul` derives
  `thm:multiplicative-functoriality`'s main clause (`u_m(AB)=u_m(A)+u_m(B)`
  for the canonical logarithmic coordinate `u_m(A)=m·[x^m]\log A`) as an
  immediate corollary. **All three clauses of `thm:multiplicative-functoriality`
  are now complete**: `logOf_inv`/`canonicalCoord_inv` give `u_m(A^{-1})=-u_m(A)`
  (via `logOf_one : log 1 = 0`, applying `logOf_mul` to `f·f⁻¹=1`, itself
  built from `geomSubst`, the formal inverse via substituting the geometric
  series), and `logOf_pow`/`canonicalCoord_pow` give `u_m(A^q)=q\,u_m(A)` for
  `q∈ℕ` (by induction on `q` via `logOf_mul` applied to `f^q·f=f^{q+1}`,
  with `coeff m ((q:A⟦X⟧)·g) = q·coeff m g` handled via the `ℕ`-scalar-action
  detour `↑q * g = q • g` rather than an unneeded second induction). Also
  proved, **both halves of the full classical `log`/`exp` bijection**:
  `logOf_exp` (`log(exp g) = g` for `g` with zero constant term — same
  technique, `exp`'s own derivative gives the chain rule directly) and
  `exp_logOf` (`exp(log f) = f` for `f` with constant term `1` — the harder
  direction, needing one extra step: `k := exp(log f)·f⁻¹` has zero
  derivative and constant term `1`, via the quotient rule and the
  derivative of the formal inverse `deriv_ginv_mul`, so `k=1` by
  `deriv_injective_of_const`, and cancelling the unit `f⁻¹` finishes it).
  Together with `logOf_mul`, this gives a complete, mutually-inverse
  correspondence between `1+xA[[x]]` and `xA[[x]]` (constant term `1` vs.
  `0`) over any `ℚ`-algebra `A` — everything `thm:canonical-classification`'s
  bijection itself asserts.
- **`CongruenceTheory/BaseChange.lean`** — **Theorem `thm:base-change`**
  ("Universal base-change theorem"), all three clauses. The insight: the
  shift-defect identities of `thm:universal`/`thm:strong` are identities of
  *universal integral polynomials* in `Z[X_1,X_2,...]`, so they transport
  under the unique ring hom `Z[X_1,X_2,...]→R` (`X_j↦r_j`) to *every*
  commutative ring `R`, with no characteristic-zero, `Q`-algebra, or
  integrality hypothesis on `r` needed — the whole theorem is naturality of
  evaluation applied to an already-proved identity. Concretely: `Qpoly`/
  `Hpoly` are the manuscript's `Q_{n,k}`/`H_{n,k}` shift-defect polynomials,
  extracted as literal `MvPolynomial ℕ ℤ` witnesses via Mathlib's
  `MvPolynomial.C_dvd_iff_dvd_coeff` applied to `universal_shift_mod`/
  `universal_shift_lcm`'s coefficientwise-divisibility conclusions (so no
  new combinatorics — this is packaging already-proved facts as an actual
  polynomial identity, exactly as the manuscript's own one-line proof
  does). `base_change_mod`/`base_change_lcm` then apply `evalAt r`
  (`eval₂Hom (Int.castRingHom R) r`) to `Qpoly_spec`/`Hpoly_spec`. The
  two-adic clause (`base_change_two_adic`) similarly transports
  `strong_two_adic`, in the permutation-native `Cperm`/`CpermSum` form that
  `thm:strong` is actually stated in here (not the abstract `C` — the two
  families are the manuscript's own Prop 2.1 apart, not re-derived, per the
  existing `prop:content-bounds` scoping note above).
- **`CongruenceTheory/EGFCoordinates.lean`** — the bridge between the
  abstract `C_n` (falling-factorial recurrence, `Basic.lean`) and actual
  power series in canonical coordinates (`PowerSeriesLog.lean`), plus
  **Theorem `thm:general-defect`**. Differentiating `F=exp(logOf F)` and
  extracting the log-derivative rule at coefficient `n` gives
  `∑_{i=0}^n u_{i+1}[x^{n-i}]F=(n+1)[x^{n+1}]F`; multiplying by `n!` and
  using `n!/(n-i)!=\mathrm{fall}(n,i)` (via Mathlib's
  `Nat.factorial_mul_descFactorial`) turns this into *exactly* `C`'s own
  defining recurrence (`C_succ`) with `X_j↦u_j` — so `egfCoeff F n =
  C_n(u_1,...,u_n)` (`egfCoeff_eq_cVal`, **`thm:all-egf-coordinates`**'s
  coefficient half) follows by the same strong induction that defines `C`
  in the first place. `thm:general-defect`'s displayed identity
  (`general_defect_main`) is then an immediate corollary of
  `base_change_mod`, and part (i) (`general_defect_integral`: integral
  canonical coordinates force an exact integer-multiple-of-`k` defect) via
  a short naturality lemma (`evalAt_intCast`) for evaluation at
  integer-image points. **`thm:general-defect` part (ii)** (the
  denominator-clearing statement for non-integral coordinates,
  `general_defect_denom_clear`) is now also done: `totalDegree_C_le`
  proves `deg C_m ≤ m` by induction directly on `C`'s own recurrence (a
  permutation of `m` points has at most `m` cycles), `totalDegree_Qpoly_le`
  transports this to `Q_{n,k}` (via `totalDegree_C_mul_eq`, using that
  `ℤ` has no zero divisors so multiplying by the nonzero constant `k`
  doesn't change total degree — Mathlib's `MvPolynomial.support_smul_eq`),
  and `evalAt_totalDegree_denom_clear` is the general fact that `D^N` times
  an evaluation at `z_j/D` is an integer whenever the polynomial's total
  degree is `≤N` (each monomial of degree `d≤N` in the support contributes
  an integer `coeff·D^{N-d}·∏z_i^{e_i}` after clearing).
- **`CongruenceTheory/LocalLocus.lean`** — **Theorem `thm:local-locus`**,
  clauses (i) and (ii) unified. First closes a real gap:
  `general_defect_denom_clear` needed a *single* denominator for *every*
  canonical coordinate, stronger than the manuscript's actual finite-range
  hypothesis. `vars_C_le`/`vars_Qpoly_le` show `Q_{n,k}` only involves
  `X_1,...,X_{n+k}` (by induction on `C`'s recurrence, using Mathlib's
  `MvPolynomial.vars` API — same shape of argument as the total-degree
  bound), `evalAt_congr_of_vars` shows evaluation only depends on a
  sequence's values at those variables, and `general_defect_denom_clear'`
  combines them into the manuscript's actual (finite-range) part (ii).
  `thm:local-locus` itself: `IsKLocal m x` (`x=a/b`, `b` coprime to `m`,
  matching the manuscript's own `Z_(k)={a/b∈Q:gcd(b,k)=1}` notation
  literally) covers *both* clause (i) (`m` prime) and clause (ii) (`m=k`)
  with one definition — no primality is needed anywhere in the proof.
  `common_denom_of_local` builds one common denominator (the product of
  the individual coprime-to-`m` denominators, itself coprime to `m`); fed
  into `general_defect_denom_clear'` and divided back out (a power of a
  coprime-to-`m` number is still coprime to `m`), this shows the
  shift-defect lies in `k·Z_(m)`. Not formalized: `cor:general-twoadic-defect`
  (the manuscript states this for the abstract `C`, but this codebase's
  `thm:strong` is only proved for the permutation-native `Cperm`/`CpermSum`
  — see the `prop:content-bounds` scoping note — so reaching it here would
  need either the `Cperm=C` bridge or a separate `Cperm`/`CpermSum`
  total-degree/vars bound, neither built) and the exact-locus restatement
  `thm:local-locus` part (iii) (definitional given the above).
- **`CongruenceTheory/EulerProduct.lean`** — substantial infrastructure
  toward **`thm:euler-product`**, now including the hard analytic step.
  `coeff_logOf_one_sub_X_pow`: the *exact* coefficient formula for
  `logOf(1-x^N)` (`[x^{Nr}]=-1/r`, `0` elsewhere), matching the classical
  Taylor expansion `-log(1-y)=∑_{r≥1}yʳ/r`, proved directly from `logOf`'s
  own definition via `PowerSeries.coeff_subst'` — genuinely new (not in
  Mathlib). `rpow F t := exp(C t · logOf F)`: a general power operation
  for `t` in a `ℚ`-algebra, generalizing `logOf_pow`/`logOf_inv`, needed
  since Euler coordinates `b_n` need not be integral. Order bounds (via
  Mathlib's own `PowerSeries.le_order_subst_right'`, applied twice)
  combine into `multipliable_eulerFactors`: the infinite product
  `∏' n,(1-x^{n+1})^{-b_{n+1}}` is well-defined, using Mathlib's own
  `multipliable_one_add_of_tendsto_order_atTop_nhds_top` — confirming
  Mathlib's `PiTopology`/`Multipliable`/`tprod` machinery for formal power
  series was indeed sufficient, resolving what looked like the main
  uncertainty going in. **`logOf_tprod`** (the main new result): `logOf`
  is additive over *infinite* products, extending `logOf_mul` (finite
  only) — proved via a genuine truncation argument
  (`coeff_tprod_eq_coeff_prod_range`: a coefficient of an infinite
  product is determined by any large-enough finite truncation, since the
  remaining factors are `≡1 mod X^{e+1}`; `coeff_logOf_congr`: `logOf`'s
  coefficient `e` only depends on its argument's coefficients up to
  degree `e`, via `order_pow_sub_pow_gt`) combined with the finite case
  (`logOf_prod_range`, induction on `logOf_mul`) through a finite-support
  `HasSum` argument matched against Mathlib's `hasSum_iff_hasSum_coeff`.
- **`CongruenceTheory/EulerProductTheorem.lean`** — **Theorem
  `thm:euler-product`** itself, complete: `AwSeries w = exp(∑_{m≥1}
  (w_m/m)x^m)` is `A_w(x)`, in canonical logarithmic coordinates with
  `u_m=w_m`. `b n := MTrans w n / n` are the Euler coordinates (`MTrans`
  is `GaussCongruence.lean`'s own Möbius transform `∑_{d∣n}μ(n/d)w_d`),
  and `w_eq_sum_div_mul_b` recovers the manuscript's `eq:w-from-b`
  (`w_m=∑_{d∣m}d·b_d`) directly from `GaussCongruence.lean`'s own
  `moebius_inversion` — no new number theory needed. `euler_product`
  itself: apply `logOf_tprod` to the Euler factors `rpow(1-x^{n+1})
  (-b_{n+1})`, then match `logOf(∏' factors) = ∑' n, C(-b_{n+1})·
  logOf(1-x^{n+1})` against `logOf(A_w) = ∑(w_m/m)x^m` coefficient by
  coefficient (`coeff_sum_eulerFactors`): using the exact Taylor
  coefficients of `logOf(1-x^N)`, the `e`-th coefficient of the infinite
  sum collapses to a *finite* sum over divisors of `e` (reindexed via
  `Finset.sum_nbij'`), matching `w_e/e` exactly via `w_eq_sum_div_mul_b`.
  Both sides then have constant term `1` and equal `logOf`, so are equal
  by the `log`/`exp` bijection (`exp_logOf`).
- **`CongruenceTheory/EulerIntegrality.lean`** — **`thm:euler-integrality`
  in full** — all three clauses now done, completing the entire
  Euler/Gauss chapter. `euler_integrality_ii_iff_iii`: clauses (ii)
  (`b_n∈ℤ`) and (iii) (`n∣M_n`, `thm:gauss`'s own condition) are
  equivalent, immediate from `b`'s definition. **(ii)⟹(i)**
  (`euler_integrality_ii_imp_i`): built via `EF n`, the
  integer-coefficient formal inverse of `1-x^{n+1}` in `ℤ⟦X⟧` (Mathlib's
  `PowerSeries.invOfUnit`); `map_EF_eq_geomSubst`/`geomSubst_pow`
  connecting it back to `ℚ⟦X⟧`'s `geomSubst` by uniqueness of inverses;
  `Efactor n k`/`map_Efactor`/`coeff_finiteProd_int` transporting
  integrality through the Euler factors and a finite product, combined
  with `euler_product` and `coeff_tprod_eq_coeff_prod_range`.
  **(i)⟹(ii)** (`euler_integrality_i_imp_ii`), the manuscript's own
  harder inductive truncation argument, is now also complete:
  `coeff_rpow_one_sub_X_pow_le` gives the exact coefficients of
  `rpow(1-x^N)(-t)` up to degree `N` (`1` at `0`, `t` at `N`, `0`
  otherwise — via the same `coeff_subst'` finite-support technique as
  `coeff_logOf_one_sub_X_pow`, using `PowerSeries.le_order_pow` to kill
  the `exp` series' degree-`≥2` terms); `coeff_AwSeries_eq_coeff_prod_range`
  shows coefficient `N` of `A_w` depends only on the first `N` Euler
  factors, via an *unconditional* per-factor order bound
  (`le_order_eulerFactor_sub_one`) rather than an existential search;
  `prod_range_split_top`/`head_prod_int` split off the top factor and
  package the (by induction) already-integral head as an integer series;
  `coeff_N_step` combines these via the convolution formula for `coeff N`
  of a product, isolating the two nonzero terms to get
  `coeff N(A_w)=coeff N(head)+b_N`; the final strong induction
  (`euler_integrality_i_imp_ii`) reads off `b_N` as a difference of two
  known integers.
- **`CongruenceTheory/NoAllEgfShift.lean`** — **`prop:no-all-egf-shift`**:
  the manuscript's own counterexample `A(x)=1+x²/2!` showing integrality of
  the ordinary EGF coefficients alone (`a_0=a_2=1`, `a_4=0`) does *not*
  force a shift congruence — `a_4-a_2·a_2=-1` is not divisible by `2`,
  unlike `thm:general-defect`'s hypothesis on the canonical logarithmic
  coordinates `u_m` themselves.
- **`CongruenceTheory/GeneralTwoAdicDefect.lean`** —
  **`cor:general-twoadic-defect`**, denominator-cleared form, honestly
  adapted to the permutation-native `Cperm`/`CpermSum` that `thm:strong`
  actually proves in this codebase (not the abstract `C` the manuscript
  states it for — see the standing "Cperm=C bridge" caveat below).
  `totalDegree_ci_le`: the cycle-indicator monomial of a permutation on `α`
  has total degree `≤ |α|` (at most `|α|` cycles, counting fixed points),
  via `Multiset.card_nsmul_le_sum` against
  `Equiv.Perm.two_le_of_mem_cycleType` to bound cycle count by cycle-length
  sum. This gives `totalDegree_Cperm_le n ≤ n` and
  `totalDegree_CpermSum_le n ≤ 2n`, hence a degree bound on
  `strong_two_adic`'s witness `Q` (`totalDegree_strong_two_adic_Q_le`, by
  the same nonzero-constant-scaling argument as `totalDegree_Qpoly_le`),
  and finally `general_twoadic_defect_denom_clear`: for a common positive
  denominator `D` of `z_1,…,z_{2·2^s}`,
  `D^{2·2^s}·eval(z/D)(CpermSum(2^s)-Cperm(2^s)^2) ∈ 2^{2s-1}ℤ`, reusing
  `evalAt_totalDegree_denom_clear` from `EGFCoordinates.lean`.

- **`CongruenceTheory/CpermEqC.lean`** — **the `Cperm = C` bridge, in full**
  (the manuscript's own Prop 2.1-style cycle-index identification), proved
  here for the first time in this codebase: `Cperm n = C n` for every `n`,
  i.e. the permutation-native cycle-index sum (`Perm.lean`) and the abstract
  falling-factorial cycle-index polynomial (`Basic.lean`) are the *same*
  object. Proof: show `Cperm` satisfies `C`'s own recurrence (`C_succ`) via
  a genuine combinatorial bijection — the manuscript's own "expose the cycle
  containing a distinguished point" decomposition, formalized directly on
  permutations: `Equiv.Perm (Fin (m+1)) ≃ Σ r ≤ m, (ordered r-tuple of
  points ≠ 0) × Equiv.Perm (remaining m-r points)`, via
  `g ↦ (r, the cycle of 0 in g as an ordered tuple, g restricted to the
  complement)`. Built from `List.formPerm`/`Equiv.Perm.toList`/
  `Equiv.Perm.formPerm_toList` (Mathlib's list-cycle correspondence) and
  `Equiv.Perm.ofSubtype`/`subtypePerm` for the disjoint complement gluing:
  `CycleTuple m r`/`CycleCompl m r t` (the tuple and complement types),
  `gAssemble` (the assembled permutation), `ci_gAssemble` (its
  cycle-indicator monomial is exactly `X_{r+1} * ci h`), and
  `exists_decomp_zero`/`exists_decomp_pos` +
  `gAssemble_injective_zero`/`_pos` (existence and uniqueness of the
  decomposition) combine via `Finset.sum_bij`/`Fintype.sum_sigma` into
  `Cperm_succ_alt` — exactly `C_succ`'s recursive form — and `Cperm_eq_C`
  follows by the same strong induction that defines `C`. This is a
  standalone bridge lemma; the earlier `Cperm`/`CpermSum`-native files
  `ContentBounds.lean`, `StrongTwoAdic.lean`, `GeneralTwoAdicDefect.lean`
  have not been retrofitted to restate their conclusions for the abstract
  `C` — that unification is now possible but not yet done for those three;
  it *is* done for `OptimalDivisorLower.lean`, below.
- **`CongruenceTheory/OptimalDivisorC.lean`** — **`thm:optimal-divisor`,
  unified for the abstract `C`.** Previously two matching *halves* on two
  different representations (the lcm lower bound `universal_shift_lcm`, for
  `C`; the sharp prime-power bound `optimal_divisor_lower_bound`, for
  `Cperm`/`CpermPair`) — now, via the `Cperm=C` bridge, combined into the
  single statement the manuscript actually states: for all `n,k≥1`,
  `M(n,k):=nk/rad(gcd(n,k))` divides every coefficient of `C_{n+k}-C_nC_k`
  (`treeM_dvd_defect`). `CpermPair_eq_Cperm` transports
  `optimal_divisor_lower_bound` to `optimal_divisor_lower_bound_C`;
  `treeM_factorization` computes `M(n,k)`'s exact `p`-adic valuation
  (`v_p(n)+v_p(k)-1` when `p∣gcd(n,k)`, matching the prime-power bound;
  `v_p(n)+v_p(k)=v_p(\mathrm{lcm}(n,k))` otherwise, matching the lcm bound)
  via `Nat.factorization_div`/`UniqueFactorizationMonoid.squarefree_radical`;
  `dvd_of_forall_prime_pow_dvd` packages per-prime bounds on one integer
  into one divisibility via `Nat.factorization_le_iff_dvd`; `treeM_dvd_defect`
  combines all of this coefficient-by-coefficient. This is also exactly the
  `r=2` base case of `thm:tree-modulus`'s own inductive proof (the "exact
  two-term content theorem" its induction calls for at each binary-tree
  node), used directly below.

## Build

```bash
lake build
```

`.lake/packages` includes a full Mathlib build; no re-fetch is needed if you
have network access for the initial `lake update`, or reuse an existing
`.lake` directory pinned to the same toolchain (`v4.31.0`) and Mathlib
revision.

## Scope

This repository covers the main paper and the framework behind it: the
universal shift congruence, the strong two-adic lift, canonical logarithmic
coordinates, base change, localization, finite determinacy, multiplicative
functoriality, and the exact content of the two-term multiplicative defect.
It does not include the higher-order connected-cumulant classification;
see `congruence-phenomena-higher-order-lean` for that (and for its markedly
less complete verification status).
- **`CongruenceTheory/PrimeWitness.lean`** — **`prop:prime-witness`,
  complete**: the matching sharp *upper* bound. Generalizes
  `ContentBounds.lean`'s single-`2`-cycle coefficient-extraction argument
  to a single-`2p`-cycle (`coeff_defect_singleCycle`), reduces it via
  Mathlib's `Nat.add_choose_eq` (Vandermonde's identity) to the
  central-binomial sum `∑_{i=1}^{2p-1} C(n,i)C(k,2p-i)` the manuscript
  itself uses, then proves this sum's `p`-adic valuation is exactly
  `v_p(n)+v_p(k)-2` via **ultrametric dominance**
  (`padicValNat_sum_eq_of_unique_min`, a new general-purpose lemma: one
  term with strictly minimal valuation forces the whole sum's valuation).
  The manuscript's own proof splits on `p` odd vs. `p=2` to bound the
  central term's Kummer-carry count; this formalization avoids that split
  entirely, via a cleaner argument: among the `p` consecutive integers
  `n,…,n-p+1`, exactly one (`n` itself) is divisible by `p`, giving
  `v_p(C(n,p))+1=v_p(n)` exactly (`padicValNat_choose_prime_self_add_one`),
  while every non-central term is shown to have strictly larger valuation
  via the *same* `Nat.factorization_le_factorization_choose_add` bound
  `MixedSupportFactorial.lean` already used. **This completes
  `thm:optimal-divisor` in full**: combined with
  `optimal_divisor_lower_bound`, every coefficient of `CpermPair n k -
  Cperm n · Cperm k` is divisible by `p^(v_p(n)+v_p(k)-1)` for every prime
  `p`, and this is sharp — the `2p`-cycle coefficient witnesses equality
  exactly, for every common prime `p ∣ gcd(n,k)`.
- **`CongruenceTheory/PrimeValue.lean`** — **`prop:prime`**, complete:
  `AwPerm_prime_cong` proves `A_w(p) ≡ w_1 - w_p (mod p)` for every prime
  `p`. A *different* orbit argument from `thm:strong`'s — this is
  conjugation by the *full* symmetric group `S_p` on itself (not the
  `H`-subgroup case `Conj.lean`/`Centralizer.lean` were built for), so it
  goes straight to Mathlib's own `Equiv.Perm.card_isConj_mul_eq` (exact
  class-size formula, `|class(g)| · z_λ = p!`) instead of custom
  machinery. The real content is `not_dvd_centralizer_size`:
  `z_λ = (p-|λ|)!·∏λ·∏(multiplicity!)` is `p`-free for every cycle type
  other than the identity's and the single-`p`-cycle's, since a cycle type
  summing to exactly the prime `p` with every part `<p` forces every
  factor of `z_λ` to be a factorial/product of numbers `<p`. Combined with
  `dvd_sum_of_const_on_classes` (`OrbitSum.lean`, reused unchanged) this
  gives `Cperm p = X_1^p + (p-1)!·X_p + p·Q`; Fermat (`ZMod.pow_card`) and
  Wilson (`ZMod.wilsons_lemma`) finish it off. Took the most iteration of
  anything this round (working around several `omega`-can't-see-`hp.pos`
  and cast-ambiguity traps), but every piece was validated standalone
  before assembly, and nothing was left broken.
