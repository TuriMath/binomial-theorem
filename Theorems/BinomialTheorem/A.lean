import Mathlib

/-!
# Binomial theorem — statement A (Noether)

Source (issue TuriMath/binomial-theorem#1, Wikipedia "Binomial theorem", §Statement):
> the expansion of any nonnegative integer power n of the binomial x + y is a sum of the form
> (x + y)^n = ∑_{k=0}^{n} C(n, k) x^(n−k) y^k
-/

universe u

namespace TuriMath.BinomialTheorem.A

open Finset

/-- The binomial theorem.

Mapping from the source to Lean, one line each:
* "x + y" with x, y in an arbitrary commutative ring → `R : Type u`, `[CommRing R]`, `x y : R`
  (universe-polymorphic; not a semiring, not a specific ring, per the issue notes).
* "any nonnegative integer power n" → `n : ℕ` (ℕ is exactly the nonnegative integers).
* "(x + y)^n" → `(x + y) ^ n` (monoid power in `R`).
* "∑_{k=0}^{n}" → `∑ k ∈ range (n + 1)`; `range (n + 1) = {0, 1, …, n}`.
* "C(n, k)" → `(n.choose k : R)`: Mathlib's `Nat.choose`, a natural number cast into `R`.
* "x^(n−k)" → `x ^ (n - k)`; truncated ℕ-subtraction is exact here since `k ≤ n` on the range.
* "y^k" → `y ^ k`.
* Juxtaposition "C(n, k) x^(n−k) y^k" → `(n.choose k : R) * x ^ (n - k) * y ^ k`, in the source order. -/
def Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (x y : R) (n : ℕ),
    (x + y) ^ n = ∑ k ∈ range (n + 1), (n.choose k : R) * x ^ (n - k) * y ^ k

/-! ## Sanity section

The statement has no hypotheses beyond the structure assumption `[CommRing R]`, so there is
nothing that could be jointly unsatisfiable. For completeness we check that the structure
assumption is inhabited in every universe `u` (so the `∀ R` is not vacuous), and that the
right-hand side is the familiar one in a small case. -/

/-- A commutative ring exists in every universe `u` (e.g. `ULift ℤ`). -/
example : Nonempty (CommRing (ULift.{u} ℤ)) := ⟨inferInstance⟩

/-- The right-hand side for `n = 2` over `ℤ` is `x^2 + 2xy + y^2`, as expected. -/
example (x y : ℤ) :
    ∑ k ∈ range (2 + 1), ((Nat.choose 2 k : ℕ) : ℤ) * x ^ (2 - k) * y ^ k
      = x ^ 2 + 2 * x * y + y ^ 2 := by
  simp [sum_range_succ, Nat.choose]

end TuriMath.BinomialTheorem.A
