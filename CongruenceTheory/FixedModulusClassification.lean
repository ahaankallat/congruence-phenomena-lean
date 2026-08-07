import Mathlib

/-!
**Theorem `thm:fixed-modulus-classification`** ("Exact fixed-modulus
classification"): a standalone fact about *any* integer sequence with
`a_0 = 1`, independent of the cycle-index machinery. Self-contained.
-/

namespace CongruenceTheory

/-- **Theorem `thm:fixed-modulus-classification`.** For any integer sequence `a` with
`a 0 = 1` and any `k ≥ 1`: `a_{n+k} ≡ a_n a_k (mod k)` for every `n ≥ 0` (condition (i))
iff `a_{r+qk} ≡ a_r a_k^q (mod k)` for every `0 ≤ r < k` and `q ≥ 0` (condition (ii)),
i.e. modulo `k` each residue-class subsequence is a geometric progression with common
multiplier `a_k`. -/
theorem fixed_modulus_classification (a : ℕ → ℤ) (k : ℕ) (hk : 1 ≤ k) :
    (∀ n, (k : ℤ) ∣ (a (n + k) - a n * a k)) ↔
      (∀ r q, r < k → (k : ℤ) ∣ (a (r + q * k) - a r * a k ^ q)) := by
  constructor
  · intro hi r q _
    induction q with
    | zero => simp
    | succ q ih =>
      have hstep := hi (r + q * k)
      have heq : r + (q + 1) * k = (r + q * k) + k := by ring
      rw [heq]
      have hsplit : a ((r + q * k) + k) - a r * a k ^ (q + 1) =
          (a ((r + q * k) + k) - a (r + q * k) * a k) +
            (a (r + q * k) - a r * a k ^ q) * a k := by ring
      rw [hsplit]
      exact dvd_add hstep (Dvd.dvd.mul_right ih (a k))
  · intro hii n
    set r := n % k with hr
    set q := n / k with hq
    have hrk : r < k := Nat.mod_lt n hk
    have hn : n = r + q * k := by
      rw [hr, hq, mul_comm]
      exact (Nat.mod_add_div n k).symm
    have h1 := hii r q hrk
    rw [← hn] at h1
    have h2 := hii r (q + 1) hrk
    have heq2 : r + (q + 1) * k = n + k := by rw [hn]; ring
    rw [heq2] at h2
    have hcomb : a (n + k) - a n * a k =
        (a (n + k) - a r * a k ^ (q + 1)) - (a n - a r * a k ^ q) * a k := by ring
    rw [hcomb]
    exact dvd_sub h2 (Dvd.dvd.mul_right h1 (a k))

end CongruenceTheory
