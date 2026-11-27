import Theorems.BinomialTheorem.A
import Theorems.BinomialTheorem.B

/-! # Binomial theorem: A ↔ B (Euler)

The two statements differ only in how the sum is indexed (`range (n+1)` vs `Fin (n+1)`).
Each direction uses the other statement as hypothesis and rewrites the sum. -/

universe u

namespace TuriMath.BinomialTheorem

open Finset

private lemma sum_eq (R : Type u) [CommRing R] (x y : R) (n : ℕ) :
    ∑ k : Fin (n + 1), ((Nat.choose n k : ℕ) : R) * x ^ (n - (k : ℕ)) * y ^ (k : ℕ)
      = ∑ k ∈ range (n + 1), (n.choose k : R) * x ^ (n - k) * y ^ k :=
  Fin.sum_univ_eq_sum_range (fun k => ((Nat.choose n k : ℕ) : R) * x ^ (n - k) * y ^ k) (n + 1)

theorem equiv : A.Statement.{u} ↔ B.Statement.{u} := by
  constructor
  · intro h R _ x y n
    rw [sum_eq]
    exact h R x y n
  · intro h R _ x y n
    rw [← sum_eq]
    exact h R x y n

end TuriMath.BinomialTheorem
