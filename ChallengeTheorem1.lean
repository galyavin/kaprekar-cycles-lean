module

/-!
# All four-digit Kaprekar cycles in even bases

Theorem 1 of Rustem Galyavin, *Cycles of the four-digit Kaprekar map in even bases*
(2026), doi:10.5281/zenodo.24358739.

In base `B ≥ 2`, write each natural number below `B^4` with four digits, allowing leading
zeros. Sort the digits in decreasing and increasing order, read both arrangements as
base-`B` numbers, and subtract the increasing arrangement from the decreasing one.
A cycle is an orbit of periodic points with nonconstant digits, counted up to cyclic
shift. Its length is the least positive return time.

Write `B = m * 2^n` with `m` odd and `n ≥ 1`.

* (a) For `m ≥ 5`, lift each cycle of the folded permutation on `T_m` by scaling its
  differences by `2^n`. Each lift has its original length. There is one additional orbit
  of length `n+1` if `2^n ≡ 1 (mod m)`, or one of length `2(n+1)` if `m = 5` and
  `n ≡ 2 (mod 4)`. The conditions are mutually exclusive and the list is exhaustive.
* (b) For `m = 3`, there is one cycle of length `3(n+1)` when `n` is odd. When `n`
  is even there are two cycles, of lengths `n+1` and `2(n+1)`.
* (c) For `m = 1`, base two has two fixed points. For odd `n ≥ 3` there are
  `(n-1)/2` cycles of each length `n` and `n+2`. For even `n ≥ 2` there are
  `(n-2)/2` cycles of each length `n` and `n+2`, one of length `n/2`, and one of
  length `n/2+1`.

The representatives for the two optional cycles in (a), for (b), and for the power
families in (c) use difference pairs from the paper. The number produced by subtraction
from a pair lies on the corresponding orbit. Any pair on a core cycle yields a
representative of the same lifted orbit.
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

/-- The forward orbit of `x` contains `y`. For a periodic `x`, this is cycle membership. -/
def OnOrbit (B x y : Nat) : Prop := ∃ i, iterate (kaprekar B) i x = y

/-- A representative is a valid, nonconstant four-digit number of least period `L`. -/
def IsCycleOfLength (B x L : Nat) : Prop :=
  x < B ^ 4 ∧ ¬ IsRepdigit B x ∧ HasPeriod B x L

/-- The paper's `T_m`: the odd pairs `m > u > v > 0`. -/
def InOddCore (m : Int) (p : Int × Int) : Prop :=
  p.2 > 0 ∧ p.1 > p.2 ∧ m > p.1 ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 1

/-- The folded permutation on `T_m`: sort the absolute values of `2u-m` and `2v-m`. -/
def coreStep (m : Int) (p : Int × Int) : Int × Int :=
  let abs (x : Int) := if x < 0 then -x else x
  let u := abs (2 * p.1 - m)
  let v := abs (2 * p.2 - m)
  if u ≥ v then (u, v) else (v, u)

/-- The `i`th iterate of the folded permutation. -/
def coreIterate (m : Int) : Nat → (Int × Int) → (Int × Int)
  | 0, p => p
  | i + 1, p => coreStep m (coreIterate m i p)

/-- Read the post-subtraction digits for the difference pair `(u,v)`.
The arguments used below satisfy `0 ≤ v ≤ u < B` and `0 < u`, so all four digits
in the selected row are nonnegative and less than `B`. -/
def wordOfDifferences (B : Nat) (p : Int × Int) : Nat :=
  let base : Int := B
  let read (a b c d : Int) := (((a * base + b) * base + c) * base + d).toNat
  if p.2 = 0 then read (p.1 - 1) (base - 1) (base - 1) (base - p.1)
  else read p.1 (p.2 - 1) (base - 1 - p.2) (base - p.1)

/-- A representative of the lift of an odd-core pair `p`. -/
def liftRepresentative (B n : Nat) (p : Int × Int) : Nat :=
  wordOfDifferences B ((2 : Int) ^ n * p.1, (2 : Int) ^ n * p.2)

/-- The boundary representative with pair `(a * 2^n, 0)`. -/
def boundaryRepresentative (B n : Nat) (a : Int) : Nat :=
  wordOfDifferences B (a * 2 ^ n, 0)

/-- Theorem 1(a). The lift-orbit equivalence puts odd-core cycles in bijection with
the lifted cycles. The return-time equivalence gives equality of their least periods. -/
structure LargeOddCoreCycles (B m n : Nat) : Prop where
  exhaustive : ∀ x, x < B ^ 4 → ¬ IsRepdigit B x →
    (IsPeriodic B x ↔
      (∃ p, InOddCore m p ∧ OnOrbit B (liftRepresentative B n p) x) ∨
      ((m : Int) ∣ (2 : Int) ^ n - 1) ∧ OnOrbit B (boundaryRepresentative B n 1) x ∨
      m = 5 ∧ n % 4 = 2 ∧ OnOrbit B (boundaryRepresentative B n 2) x)
  lift_periodic : ∀ p, InOddCore m p →
    let x := liftRepresentative B n p
    x < B ^ 4 ∧ ¬ IsRepdigit B x ∧ IsPeriodic B x
  lift_orbits : ∀ p q, InOddCore m p → InOddCore m q →
    (OnOrbit B (liftRepresentative B n p) (liftRepresentative B n q) ↔
      ∃ i, coreIterate m i p = q)
  lift_returns : ∀ p, InOddCore m p → ∀ i,
    (iterate (kaprekar B) i (liftRepresentative B n p) = liftRepresentative B n p ↔
      coreIterate m i p = p)
  residue_one : ((m : Int) ∣ (2 : Int) ^ n - 1) →
    IsCycleOfLength B (boundaryRepresentative B n 1) (n + 1)
  exceptional_five : m = 5 → n % 4 = 2 →
    IsCycleOfLength B (boundaryRepresentative B n 2) (2 * (n + 1))
  separate : ∀ p, InOddCore m p →
    ¬ OnOrbit B (liftRepresentative B n p) (boundaryRepresentative B n 1) ∧
    ¬ OnOrbit B (liftRepresentative B n p) (boundaryRepresentative B n 2)
  exclusive : ¬ (((m : Int) ∣ (2 : Int) ^ n - 1) ∧ m = 5 ∧ n % 4 = 2)

/-- Theorem 1(b). `S` has pair `(2^n,0)` and `E` has pair `(2^(n+1),0)`. -/
structure ThreeCoreCycles (B n : Nat) : Prop where
  exhaustive : ∀ x, x < B ^ 4 → ¬ IsRepdigit B x →
    (IsPeriodic B x ↔ OnOrbit B (boundaryRepresentative B n 1) x ∨
      n % 2 = 0 ∧ OnOrbit B (boundaryRepresentative B n 2) x)
  periods : if n % 2 = 0 then
      IsCycleOfLength B (boundaryRepresentative B n 1) (n + 1) ∧
      IsCycleOfLength B (boundaryRepresentative B n 2) (2 * (n + 1))
    else IsCycleOfLength B (boundaryRepresentative B n 1) (3 * (n + 1))
  separate : n % 2 = 0 →
    ¬ OnOrbit B (boundaryRepresentative B n 1) (boundaryRepresentative B n 2)

/-- The `i`th zero-boundary representative in base `2^n`. -/
def powerZero (n i : Nat) : Nat := wordOfDifferences (2 ^ n) (2 ^ (i + 1), 0)

/-- The `i`th anti-diagonal representative in base `2^n`. -/
def powerAnti (n i : Nat) : Nat :=
  wordOfDifferences (2 ^ n) (2 ^ (n - 1) + 2 ^ i, 2 ^ (n - 1) - 2 ^ i)

/-- Select the zero-boundary or anti-diagonal representative, respectively. -/
def powerRepresentative (n i : Nat) (antiDiagonal : Bool) : Nat :=
  if antiDiagonal then powerAnti n i else powerZero n i

/-- Theorem 1(c) for `n ≥ 2`. Each family has `n / 2` pairwise distinct cycles.
The first `(n-1)/2` indices in each family have full period. When `n` is even
the one remaining index in each family has half period. -/
structure HigherPowerCycles (n : Nat) : Prop where
  exhaustive : ∀ x, x < (2 ^ n : Nat) ^ 4 → ¬ IsRepdigit (2 ^ n) x →
    (IsPeriodic (2 ^ n) x ↔ ∃ (i : Fin (n / 2)) (antiDiagonal : Bool),
      OnOrbit (2 ^ n) (powerRepresentative n i.val antiDiagonal) x)
  disjoint : ∀ (i j : Fin (n / 2)) (b c : Bool),
    (OnOrbit (2 ^ n) (powerRepresentative n i.val b) (powerRepresentative n j.val c) ↔
      i = j ∧ b = c)
  periods : ∀ i : Fin (n / 2),
    IsCycleOfLength (2 ^ n) (powerZero n i.val)
        (if i.val < (n - 1) / 2 then n + 2 else n / 2 + 1) ∧
      IsCycleOfLength (2 ^ n) (powerAnti n i.val)
        (if i.val < (n - 1) / 2 then n else n / 2)
  odd_count : n % 2 = 1 → n / 2 = (n - 1) / 2
  even_count : n % 2 = 0 → (n - 1) / 2 = (n - 2) / 2 ∧ n / 2 = (n - 2) / 2 + 1

/-- **Theorem 1(a)**: all cycles and their lengths for odd part at least five. -/
theorem cycles_odd_core (m n : Nat) (hodd : m % 2 = 1) (hm : 5 ≤ m) (hn : 1 ≤ n) :
    LargeOddCoreCycles (2 ^ n * m) m n := by
  sorry

/-- **Theorem 1(b)**: all cycles and their lengths for odd part three. -/
theorem cycles_core_three (n : Nat) (hn : 1 ≤ n) : ThreeCoreCycles (2 ^ n * 3) n := by
  sorry

/-- **Theorem 1(c), base two**: the only cycles are the fixed points `0111` and `1001`
(decimal 7 and 9). -/
theorem cycles_base_two :
    (∀ x, x < 2 ^ 4 → ¬ IsRepdigit 2 x → (IsPeriodic 2 x ↔ x = 7 ∨ x = 9)) ∧
      IsCycleOfLength 2 7 1 ∧ IsCycleOfLength 2 9 1 := by
  sorry

/-- **Theorem 1(c), higher powers of two**: the complete count and least-period
table in base `2^n` for `n ≥ 2`. -/
theorem cycles_higher_powers_two (n : Nat) (hn : 2 ≤ n) : HigherPowerCycles n := by
  sorry

end PalomarKaprekar
