module

/-!
# The even bases with exactly one four-digit Kaprekar cycle

Fix a base `B ≥ 2`. The four-digit Kaprekar map `K_B` acts on the integers `0 ≤ x < B^4`, each
written with exactly four base-`B` digits, leading zeros allowed: arrange the four digits in
decreasing order and in increasing order, read both arrangements as base-`B` numbers, and subtract
the second from the first. In base ten this is Kaprekar's routine, for example
`7641 - 1467 = 6174`.

An input whose four digits are all equal goes to the fixed point `0`, which is excluded. A *cycle*
is a periodic orbit of `K_B` through an input whose digits are not all equal. Orbits are counted up to cyclic shift.
A fixed point is a cycle with least period one.

This file imports nothing beyond Lean's core library. It states two theorems.

* `unique_cycle_iff`: an even base `B ≥ 2` has exactly one cycle if and only if
  `B = 3·2^(2k+1)` or `B = 5·2^(2k+1)` for some `k ≥ 0`, or `B = 7·2^n` with `n ≥ 1` and `3 ∤ n`.
* `unique_cycle_length`: in these three families the unique cycle has length `6(k+1)`, `1` and
  `3`, respectively.

Together they are Corollary 2 of R. Galyavin, *Cycles of the four-digit Kaprekar map in even
bases* (2026), doi:10.5281/zenodo.24358739. Chen, Ono, Schwartz and Thakur recorded this pattern
from numerical evidence (*Four-digit Kaprekar dynamics in odd bases*, J. Integer Seq. 29 (2026),
Article 26.4.7, Remark 28). Base ten is `5·2^1`; its unique cycle is the fixed point `6174`.

The paper's Theorem 1, the classification of all cycles in every even base, is also proved in the
accompanying Lean development. It is *not* stated in this file; see the README.

## Definitions

Each definition is the plain textbook notion. None of them encodes the proof.

* `digits4 B x` lists the four base-`B` digits of `x`, most significant first. The digit of
  `B^3` is `x / B / B / B % B`, which equals `x / B^3 % B`.
* `ofDigits B ds` reads a list of digits, most significant first, as a base-`B` number
  (Horner's rule).
* `sortDesc` is insertion sort into decreasing order. Its reverse is the increasing order.
* `kaprekar B x` is the descending arrangement minus the ascending arrangement. The subtraction is
  in `Nat`, but it never truncates, because the descending arrangement is the larger number.
* `iterate f n` is the `n`-fold composite of `f`.

Only inputs `x < B^4` are ever quantified over. For such `x`, `kaprekar B x < B^4` again.
-/

@[expose] public section

namespace PalomarKaprekar

/-- The four base-`B` digits of `x`, most significant first, leading zeros allowed. For
`x < B^4` they are the unique `d₀, d₁, d₂, d₃ < B` with `x = d₀ B³ + d₁ B² + d₂ B + d₃`. -/
def digits4 (B x : Nat) : List Nat :=
  [x / B / B / B % B, x / B / B % B, x / B % B, x % B]

/-- Read a list of digits, most significant first, as a base-`B` number (Horner's rule):
`ofDigits B [d₀, d₁, d₂, d₃] = ((d₀ B + d₁) B + d₂) B + d₃`. -/
def ofDigits (B : Nat) (ds : List Nat) : Nat :=
  ds.foldl (fun acc d => acc * B + d) 0

/-- Insert `a` into a list sorted in decreasing order, keeping it sorted. -/
def insertDesc (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if b ≤ a then a :: b :: l else b :: insertDesc a l

/-- Insertion sort into decreasing order. -/
def sortDesc : List Nat → List Nat
  | [] => []
  | a :: l => insertDesc a (sortDesc l)

/-- The four-digit Kaprekar map in base `B`: the digits of `x` arranged in decreasing order,
minus the same digits arranged in increasing order, both read as base-`B` numbers. -/
def kaprekar (B x : Nat) : Nat :=
  ofDigits B (sortDesc (digits4 B x)) - ofDigits B (sortDesc (digits4 B x)).reverse

/-- In base ten, the Kaprekar map fixes `6174`. -/
theorem kaprekar_ten_6174 : kaprekar 10 6174 = 6174 := by decide

/-- `iterate f n x` applies `f` to `x` exactly `n` times. -/
def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => f (iterate f n x)

/-- The four base-`B` digits of `x` are all equal. -/
def IsRepdigit (B x : Nat) : Prop :=
  x / B / B / B % B = x / B / B % B ∧ x / B / B % B = x / B % B ∧ x / B % B = x % B

/-- `x` is a periodic point of `K_B`: some positive number of steps returns to `x`. -/
def IsPeriodic (B x : Nat) : Prop :=
  ∃ k, 0 < k ∧ iterate (kaprekar B) k x = x

/-- `x` has least period `L` under `K_B`, so its cycle has length `L`. -/
def HasPeriod (B x L : Nat) : Prop :=
  0 < L ∧ iterate (kaprekar B) L x = x ∧
    ∀ i, 0 < i → i < L → iterate (kaprekar B) i x ≠ x

/-- `K_B` has exactly one cycle up to cyclic shift, and its least period is `L`. There is an input `x < B^4`
whose digits are not all equal and which has least period `L`, and the forward orbit of `x`
(which is its cycle) contains every periodic input `y < B^4` whose digits are not all equal. -/
def HasUniqueCycleOfLength (B L : Nat) : Prop :=
  ∃ x, x < B ^ 4 ∧ ¬ IsRepdigit B x ∧ HasPeriod B x L ∧
    ∀ y, y < B ^ 4 → ¬ IsRepdigit B y → IsPeriodic B y →
      ∃ j, iterate (kaprekar B) j x = y

/-- **Corollary 2, classification.** An even base `B ≥ 2` has exactly one four-digit Kaprekar
cycle if and only if `B = 3·2^(2k+1)` or `B = 5·2^(2k+1)` for some `k`, or `B = 7·2^n` with
`n ≥ 1` and `n` not divisible by `3`. -/
theorem unique_cycle_iff (B : Nat) (hB : 2 ≤ B) (heven : B % 2 = 0) :
    (∃ L, HasUniqueCycleOfLength B L) ↔
      (∃ k, B = 3 * 2 ^ (2 * k + 1)) ∨ (∃ k, B = 5 * 2 ^ (2 * k + 1)) ∨
        (∃ n, 1 ≤ n ∧ ¬ 3 ∣ n ∧ B = 7 * 2 ^ n) := by
  sorry

/-- **Corollary 2, lengths.** The unique cycle has length `6(k+1)` in base `3·2^(2k+1)`,
length `1` in base `5·2^(2k+1)`, and length `3` in base `7·2^n` when `n ≥ 1` and
`3 ∤ n`. -/
theorem unique_cycle_length (k n : Nat) :
    HasUniqueCycleOfLength (3 * 2 ^ (2 * k + 1)) (6 * (k + 1)) ∧
      HasUniqueCycleOfLength (5 * 2 ^ (2 * k + 1)) 1 ∧
      (1 ≤ n → ¬ 3 ∣ n → HasUniqueCycleOfLength (7 * 2 ^ n) 3) := by
  sorry

end PalomarKaprekar
