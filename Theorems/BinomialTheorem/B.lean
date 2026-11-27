import Mathlib

/-!
# Binomial theorem — statement B (Gauss, blind formalization)

Source (TuriMath/binomial-theorem#1, Wikipedia "Binomial theorem", §Statement; Freek 100 #44):
> the expansion of any nonnegative integer power n of the binomial x + y is a sum of the form
> (x + y)^n = ∑_{k=0}^{n} C(n, k) x^(n−k) y^k

Mapping, source → Lean:
* "x, y" (ring elements, per issue notes) → `x y : R` for an arbitrary `R : Type u` with `[CommRing R]`
* "any nonnegative integer power n"       → `n : ℕ`, universally quantified
* "(x + y)^n"                              → `(x + y) ^ n`
* "∑_{k=0}^{n}"                            → `∑ k : Fin (n + 1), …`, i.e. k runs over 0, 1, …, n
                                             (`(k : ℕ)` is the value of `k`)
* "C(n, k)" (a natural number in the ring) → `((Nat.choose n k : ℕ) : R)`
* "x^(n−k)"                                → `x ^ (n - (k : ℕ))`; truncated ℕ-subtraction is exact
                                             here since `k ≤ n`
* "y^k"                                    → `y ^ (k : ℕ)`
* the term order C · x^(n−k) · y^k is kept as written (product is commutative anyway).
-/

universe u

namespace TuriMath.BinomialTheorem.B

open BigOperators

/-- The binomial theorem over an arbitrary commutative ring, indexing the sum by `Fin (n + 1)`. -/
def Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (x y : R) (n : ℕ),
    (x + y) ^ n = ∑ k : Fin (n + 1), ((Nat.choose n k : ℕ) : R) * x ^ (n - (k : ℕ)) * y ^ (k : ℕ)

/-! ## Sanity section

The statement has no hypotheses beyond `R` being a commutative ring and `n : ℕ`; we check
that such data exist (so the statement is not vacuous): a nontrivial ring (ℤ)
and a finite one of positive characteristic (`ZMod 5`). -/

example : ∃ (R : Type) (_ : CommRing R) (_ : Nontrivial R), True :=
  ⟨ℤ, inferInstance, inferInstance, trivial⟩

example : ∃ (_ : CommRing (ZMod 5)), True := ⟨inferInstance, trivial⟩

/-! ## Concrete checks of the right-hand side

These evaluate the exact expression used in `Statement` on small cases (they do not prove it). -/

/-- n = 2, x = 3, y = 5 in ℤ: 8² = 64 = 1·9 + 2·3·5 + 1·25. -/
example : ((3 : ℤ) + 5) ^ 2 =
    ∑ k : Fin (2 + 1), ((Nat.choose 2 k : ℕ) : ℤ) * (3 : ℤ) ^ (2 - (k : ℕ)) * (5 : ℤ) ^ (k : ℕ) := by
  decide

/-- n = 3, x = 2, y = -1 in ℤ: 1³ = 1 = 8 − 12 + 6 − 1. Exercises a negative entry. -/
example : ((2 : ℤ) + (-1)) ^ 3 =
    ∑ k : Fin (3 + 1), ((Nat.choose 3 k : ℕ) : ℤ) * (2 : ℤ) ^ (3 - (k : ℕ)) * (-1 : ℤ) ^ (k : ℕ) := by
  decide

/-- n = 5, x = y = 1 in ZMod 5: 2⁵ = 32 ≡ 2, and the sum is 1 + 5 + 10 + 10 + 5 + 1 = 32 ≡ 2.
Checks the casts of `C(n, k)` into a ring of positive characteristic. -/
example : ((1 : ZMod 5) + 1) ^ 5 =
    ∑ k : Fin (5 + 1), ((Nat.choose 5 k : ℕ) : ZMod 5) * (1 : ZMod 5) ^ (5 - (k : ℕ)) *
      (1 : ZMod 5) ^ (k : ℕ) := by
  decide

/-- n = 0: (x + y)^0 = 1 and the sum has the single term C(0,0)·x^0·y^0 = 1. -/
example : ((7 : ℤ) + 4) ^ 0 =
    ∑ k : Fin (0 + 1), ((Nat.choose 0 k : ℕ) : ℤ) * (7 : ℤ) ^ (0 - (k : ℕ)) * (4 : ℤ) ^ (k : ℕ) := by
  decide

end TuriMath.BinomialTheorem.B
