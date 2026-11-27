import Theorems.BinomialTheorem.A

/-! # Binomial theorem: proof (Euler)

By induction on `n`, using Pascal's rule `Nat.choose_succ_succ`; no use of `add_pow`. -/

universe u

namespace TuriMath.BinomialTheorem

open Finset

theorem main : A.Statement.{u} := by
  intro R _ x y n
  induction n with
  | zero => simp
  | succ n ih =>
    -- T = ∑ k<n+1, C(n,k) x^(n-k) y^k
    have h1 : x * ∑ k ∈ range (n + 1), (n.choose k : R) * x ^ (n - k) * y ^ k
        = ∑ k ∈ range (n + 2), (n.choose k : R) * x ^ (n + 1 - k) * y ^ k := by
      rw [sum_range_succ _ (n + 1), Nat.choose_succ_self, mul_sum]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      refine sum_congr rfl fun k hk => ?_
      have : n + 1 - k = (n - k) + 1 := by
        have := mem_range.mp hk; omega
      rw [this, pow_succ]; ring
    have h2 : y * ∑ k ∈ range (n + 1), (n.choose k : R) * x ^ (n - k) * y ^ k
        = ∑ k ∈ range (n + 1), (n.choose k : R) * x ^ (n - k) * y ^ (k + 1) := by
      rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    have h3 : ∑ k ∈ range (n + 1 + 1), ((n + 1).choose k : R) * x ^ (n + 1 - k) * y ^ k
        = ∑ k ∈ range (n + 1), (n.choose k : R) * x ^ (n - k) * y ^ (k + 1)
          + ∑ k ∈ range (n + 2), (n.choose k : R) * x ^ (n + 1 - k) * y ^ k := by
      rw [sum_range_succ' _ (n + 1), sum_range_succ' (fun k => (n.choose k : R) * x ^ (n + 1 - k) * y ^ k) (n + 1)]
      simp only [Nat.choose_succ_succ, Nat.cast_add, Nat.choose_zero_right, Nat.cast_one,
        add_mul, sum_add_distrib, Nat.succ_sub_succ]
      ring
    rw [pow_succ, ih, mul_comm _ (x + y), add_mul, h1, h2, h3, add_comm]
