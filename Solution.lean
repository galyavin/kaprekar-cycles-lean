module

import TheoremC

/-!
# Solution: the even bases with exactly one four-digit Kaprekar cycle

This file proves the two statements of `Challenge.lean`. Its definitions are copied verbatim from
`Challenge.lean`; Comparator checks that they are identical.

The proofs transport the uniqueness and least-period fields of `KaprekarBoundary.every_even_base`
from `TheoremC.lean` to the Challenge's map.
The development works with four-slot words `Digits` (integer entries `a, b, c, d`), a sorting
network `sort4`, and a step map `step B`, which it proves equal to descending minus ascending
arrangement (`step_value`). The bridge to the Challenge's map on natural numbers has four parts.

1. `word B x` is the development's word of the four base-`B` digits of `x`. By `value_word` and
   `value_nat`, `word B` and `Digits.value B` are inverse bijections between `[0, B^4)` and the
   valid words.
2. `sortDesc_four` evaluates insertion sort on four entries, and `sort4_four` evaluates the
   network `sort4`. Both give the same max/min expressions (`sort_four`).
3. By `kaprekar_value`, `K_B x` equals the value of `step B (word B x)`. Hence `word_kaprekar` and
   `word_iterate`: `word B` conjugates `K_B` to `step B`.
4. `dev_of_unique` and `unique_of_dev` translate "exactly one cycle, of length `L`" into the
   development's `uniqueDigitCycle` and `digitPeriod`.
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


/-! ## Bridge to the development -/

open KaprekarBoundary

private theorem pow_four (B : Nat) : B ^ 4 = B * B * B * B := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

/-- Reading the four digits of `x < B^4` back gives `x`. -/
private theorem nat_value_digits (B x : Nat) (hB : 0 < B) (hx : x < B ^ 4) :
    ((x / B / B / B % B * B + x / B / B % B) * B + x / B % B) * B + x % B = x := by
  have h3 : x / B / B / B < B := by
    rw [Nat.div_lt_iff_lt_mul hB, Nat.div_lt_iff_lt_mul hB, Nat.div_lt_iff_lt_mul hB, ← pow_four]
    exact hx
  rw [Nat.mod_eq_of_lt h3, Nat.div_add_mod' (x / B / B) B, Nat.div_add_mod' (x / B) B,
    Nat.div_add_mod' x B]

/-- The digits of the number with digits `a, b, c, d < B` are `a, b, c, d`. -/
private theorem nat_digits_value (B a b c d : Nat) (hB : 0 < B)
    (ha : a < B) (hb : b < B) (hc : c < B) (hd : d < B) :
    (((a * B + b) * B + c) * B + d) / B / B / B = a ∧
    (((a * B + b) * B + c) * B + d) / B / B / B % B = a ∧
    (((a * B + b) * B + c) * B + d) / B / B % B = b ∧
    (((a * B + b) * B + c) * B + d) / B % B = c ∧
    (((a * B + b) * B + c) * B + d) % B = d := by
  have div_step : ∀ y r : Nat, r < B → (y * B + r) / B = y := by
    intro y r hr
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hr, Nat.zero_add]
  have mod_step : ∀ y r : Nat, r < B → (y * B + r) % B = r := by
    intro y r hr
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  rw [div_step _ _ hd, div_step _ _ hc, div_step _ _ hb]
  exact ⟨rfl, Nat.mod_eq_of_lt ha, mod_step _ _ hb, mod_step _ _ hc, mod_step _ _ hd⟩

/-- The development's four-slot word of the four base-`B` digits of `x`. -/
private def word (B x : Nat) : Digits :=
  ⟨((x / B / B / B % B : Nat) : Int), ((x / B / B % B : Nat) : Int),
    ((x / B % B : Nat) : Int), ((x % B : Nat) : Int)⟩

private theorem word_valid (B x : Nat) (hB : 0 < B) : (word B x).valid (B : Int) := by
  have h1 := Nat.mod_lt (x / B / B / B) hB
  have h2 := Nat.mod_lt (x / B / B) hB
  have h3 := Nat.mod_lt (x / B) hB
  have h4 := Nat.mod_lt x hB
  simp only [word, Digits.valid]
  omega

private theorem value_word (B x : Nat) (hB : 0 < B) (hx : x < B ^ 4) :
    (word B x).value (B : Int) = (x : Int) := by
  have h := nat_value_digits B x hB hx
  simp only [word, Digits.value]
  exact_mod_cast h

/-- Every valid word is the word of exactly one number below `B^4`, namely its value. -/
private theorem value_nat (B : Nat) (hB : 0 < B) (q : Digits) (hq : q.valid (B : Int)) :
    ∃ N : Nat, (N : Int) = q.value (B : Int) ∧ N < B ^ 4 ∧ word B N = q := by
  obtain ⟨a, b, c, d⟩ := q
  simp only [Digits.valid] at hq
  obtain ⟨⟨ha0, ha⟩, ⟨hb0, hb⟩, ⟨hc0, hc⟩, ⟨hd0, hd⟩⟩ := hq
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
  obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le hc0
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hd0
  have ha' : a < B := by omega
  have hb' : b < B := by omega
  have hc' : c < B := by omega
  have hd' : d < B := by omega
  obtain ⟨e3, h1, h2, h3, h4⟩ := nat_digits_value B a b c d hB ha' hb' hc' hd'
  refine ⟨((a * B + b) * B + c) * B + d, ?_, ?_, ?_⟩
  · simp only [Digits.value]
    norm_cast
  · have h : (((a * B + b) * B + c) * B + d) / B / B / B < B := by rw [e3]; exact ha'
    rw [Nat.div_lt_iff_lt_mul hB, Nat.div_lt_iff_lt_mul hB, Nat.div_lt_iff_lt_mul hB,
      ← pow_four] at h
    exact h
  · unfold word
    rw [h1, h2, h3, h4]

private theorem nonconstant_word (B x : Nat) : ¬ IsRepdigit B x ↔ (word B x).nonconstant := by
  simp only [IsRepdigit, Digits.nonconstant, word]
  constructor
  · intro h h'
    exact h ⟨by omega, by omega, by omega⟩
  · intro h h'
    exact h ⟨by omega, by omega, by omega⟩

/-! ## Insertion sort and the sorting network agree -/

private theorem sortPair_cast (x y : Nat) :
    sortPair (x : Int) (y : Int) = (((max x y : Nat) : Int), ((min x y : Nat) : Int)) := by
  by_cases h : y ≤ x
  · have hz : (y : Int) ≤ x := by omega
    simp [sortPair, hz, Nat.max_eq_left h, Nat.min_eq_right h]
  · have hz : ¬ (y : Int) ≤ x := by omega
    have hxy : x ≤ y := by omega
    simp [sortPair, hz, Nat.max_eq_right hxy, Nat.min_eq_left hxy]

private theorem sort4_four (a b c d : Nat) :
    sort4 ⟨(a : Int), (b : Int), (c : Int), (d : Int)⟩ =
      ⟨((max (max a b) (max c d) : Nat) : Int),
        ((max (min (max a b) (max c d)) (max (min a b) (min c d)) : Nat) : Int),
        ((min (min (max a b) (max c d)) (max (min a b) (min c d)) : Nat) : Int),
        ((min (min a b) (min c d) : Nat) : Int)⟩ := by
  simp only [sort4, sortPair_cast]

private theorem sortDesc_four (a b c d : Nat) :
    sortDesc [a, b, c, d] =
      [max (max a b) (max c d),
        max (min (max a b) (max c d)) (max (min a b) (min c d)),
        min (min (max a b) (max c d)) (max (min a b) (min c d)),
        min (min a b) (min c d)] := by
  simp only [sortDesc, insertDesc]
  repeat' (first | split | simp only [insertDesc])
  all_goals (simp only [List.cons.injEq, and_true] <;> omega)

private theorem sort_four (a b c d : Nat) : ∃ p q r t : Nat,
    sortDesc [a, b, c, d] = [p, q, r, t] ∧
      sort4 ⟨(a : Int), (b : Int), (c : Int), (d : Int)⟩ =
        ⟨(p : Int), (q : Int), (r : Int), (t : Int)⟩ :=
  ⟨_, _, _, _, sortDesc_four a b c d, sort4_four a b c d⟩

/-! ## `word` conjugates `K_B` to the development's `step` -/

private theorem kaprekar_value (B x : Nat) (hB : 2 ≤ B) :
    (kaprekar B x : Int) = (step (B : Int) (word B x)).value (B : Int) := by
  obtain ⟨M, hM, -, -⟩ := value_nat B (by omega) _
    (step_valid (B : Int) (by omega) (word B x) (word_valid B x (by omega)))
  have hv := step_value (B : Int) (word B x)
  rw [← hM] at hv ⊢
  obtain ⟨p, q, r, t, hs, h4⟩ :=
    sort_four (x / B / B / B % B) (x / B / B % B) (x / B % B) (x % B)
  have hw : sort4 (word B x) = ⟨(p : Int), (q : Int), (r : Int), (t : Int)⟩ := h4
  rw [hw] at hv
  have hk : kaprekar B x =
      ofDigits B (sortDesc [x / B / B / B % B, x / B / B % B, x / B % B, x % B]) -
        ofDigits B (sortDesc [x / B / B / B % B, x / B / B % B, x / B % B, x % B]).reverse :=
    rfl
  rw [hk, hs]
  simp only [ofDigits, Digits.value, Digits.rev, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil, Nat.zero_mul,
    Nat.zero_add] at hv ⊢
  have eD : ((((p * B + q) * B + r) * B + t : Nat) : Int) =
      (((p : Int) * B + q) * B + r) * B + t := by norm_cast
  have eA : ((((t * B + r) * B + q) * B + p : Nat) : Int) =
      (((t : Int) * B + r) * B + q) * B + p := by norm_cast
  rw [← eD, ← eA] at hv
  generalize ((p * B + q) * B + r) * B + t = D at hv ⊢
  generalize ((t * B + r) * B + q) * B + p = A at hv ⊢
  omega

private theorem word_kaprekar (B x : Nat) (hB : 2 ≤ B) :
    word B (kaprekar B x) = step (B : Int) (word B x) := by
  obtain ⟨M, hM, -, hw⟩ := value_nat B (by omega) _
    (step_valid (B : Int) (by omega) (word B x) (word_valid B x (by omega)))
  have h := kaprekar_value B x hB
  have hkM : kaprekar B x = M := by omega
  rw [hkM, hw]

private theorem kaprekar_lt (B x : Nat) (hB : 2 ≤ B) : kaprekar B x < B ^ 4 := by
  obtain ⟨M, hM, hMlt, -⟩ := value_nat B (by omega) _
    (step_valid (B : Int) (by omega) (word B x) (word_valid B x (by omega)))
  have h := kaprekar_value B x hB
  have hkM : kaprekar B x = M := by omega
  rw [hkM]
  exact hMlt

private theorem word_iterate (B x i : Nat) (hB : 2 ≤ B) :
    word B (iterate (kaprekar B) i x) = iter (step (B : Int)) i (word B x) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show word B (kaprekar B (iterate (kaprekar B) i x)) =
      step (B : Int) (iter (step (B : Int)) i (word B x))
    rw [word_kaprekar B _ hB, ih]

private theorem iterate_lt (B x i : Nat) (hB : 2 ≤ B) (hx : x < B ^ 4) :
    iterate (kaprekar B) i x < B ^ 4 := by
  induction i with
  | zero => exact hx
  | succ i _ =>
    show kaprekar B (iterate (kaprekar B) i x) < B ^ 4
    exact kaprekar_lt B _ hB

private theorem iterate_eq_iff (B x y i : Nat) (hB : 2 ≤ B) (hx : x < B ^ 4) (hy : y < B ^ 4) :
    iterate (kaprekar B) i x = y ↔ iter (step (B : Int)) i (word B x) = word B y := by
  rw [← word_iterate B x i hB]
  constructor
  · intro h
    rw [h]
  · intro h
    have h1 := value_word B _ (by omega) (iterate_lt B x i hB hx)
    have h2 := value_word B y (by omega) hy
    rw [h] at h1
    have h3 := h1.symm.trans h2
    exact_mod_cast h3

/-! ## Translating the unique-cycle property -/

private theorem dev_of_unique (B L : Nat) (hB : 2 ≤ B) (h : HasUniqueCycleOfLength B L) :
    uniqueDigitCycle (B : Int) := by
  obtain ⟨x, hx, hrep, ⟨hL, hret, -⟩, hall⟩ := h
  refine ⟨word B x, word_valid B x (by omega), (nonconstant_word B x).mp hrep, ⟨L - 1, ?_⟩, ?_⟩
  · rw [show L - 1 + 1 = L by omega]
    exact (iterate_eq_iff B x x L hB hx hx).mp hret
  · intro z hz hzn hzp
    obtain ⟨N, -, hNlt, hwN⟩ := value_nat B (by omega) z hz
    subst hwN
    have hNrep : ¬ IsRepdigit B N := (nonconstant_word B N).mpr hzn
    have hNper : IsPeriodic B N := by
      obtain ⟨k, hk⟩ := hzp
      exact ⟨k + 1, by omega, (iterate_eq_iff B N N (k + 1) hB hNlt hNlt).mpr hk⟩
    obtain ⟨j, hj⟩ := hall N hNlt hNrep hNper
    exact ⟨j, (iterate_eq_iff B x N j hB hx hNlt).mp hj⟩

private theorem unique_of_dev (B : Nat) (hB : 2 ≤ B) (p : Pair) (hp : validPair (B : Int) p) (L : Nat)
    (hu : uniqueDigitCycle (B : Int)) (hL : digitPeriod (B : Int) p L) :
    HasUniqueCycleOfLength B L := by
  obtain ⟨q0, -, -, hq0p, hall⟩ := hu
  have hwv : (fromPair (B : Int) p).valid (B : Int) := fromPair_valid _ p hp
  have hwn : (fromPair (B : Int) p).nonconstant := by
    apply (nonconstant_iff _).mpr
    rw [pair_of_subtraction _ _ hp]
    have := (pairMap_valid _ _ hp).1
    omega
  obtain ⟨hL0, hLret, hLmin⟩ := hL
  have hwp : periodic (step (B : Int)) (fromPair (B : Int) p) :=
    ⟨L - 1, by rw [show L - 1 + 1 = L by omega]; exact hLret⟩
  obtain ⟨N, -, hNlt, hNw⟩ := value_nat B (by omega) _ hwv
  have hreach : ∀ z : Digits, z.valid (B : Int) → z.nonconstant →
      periodic (step (B : Int)) z → reaches (step (B : Int)) (fromPair (B : Int) p) z := by
    intro z hz hzn hzp
    have back := (periodic_reachable _ _ _ hq0p (hall _ hwv hwn hwp)).2
    exact reaches_trans _ _ _ _ back (hall z hz hzn hzp)
  refine ⟨N, hNlt, (nonconstant_word B N).mpr (by rw [hNw]; exact hwn), ⟨hL0, ?_, ?_⟩, ?_⟩
  · exact (iterate_eq_iff B N N L hB hNlt hNlt).mpr (by rw [hNw]; exact hLret)
  · intro i hi0 hiL h
    exact hLmin i hi0 hiL (by rw [← hNw]; exact (iterate_eq_iff B N N i hB hNlt hNlt).mp h)
  · intro y hy hyrep hyper
    obtain ⟨k, hk0, hk⟩ := hyper
    have hyp : periodic (step (B : Int)) (word B y) :=
      ⟨k - 1, by
        rw [show k - 1 + 1 = k by omega]
        exact (iterate_eq_iff B y y k hB hy hy).mp hk⟩
    obtain ⟨j, hj⟩ :=
      hreach (word B y) (word_valid B y (by omega)) ((nonconstant_word B y).mp hyrep) hyp
    exact ⟨j, (iterate_eq_iff B N y j hB hNlt hy).mpr (by rw [hNw]; exact hj)⟩

private theorem odd_factorization_unique {m r : Int} {n s : Nat}
    (hm : m % 2 = 1) (hr : r % 2 = 1) (h : (2 : Int)^n * m = 2^s * r) :
    m = r ∧ n = s := by
  induction n generalizing s with
  | zero =>
    cases s with
    | zero => exact ⟨by simpa using h, rfl⟩
    | succ s =>
      rw [Int.pow_zero, Int.one_mul, Int.pow_succ', Int.mul_assoc] at h
      omega
  | succ n ih =>
    cases s with
    | zero =>
      rw [Int.pow_zero, Int.one_mul, Int.pow_succ', Int.mul_assoc] at h
      omega
    | succ s =>
      simp only [Int.pow_succ', Int.mul_assoc] at h
      obtain ⟨hmr, hns⟩ := ih (by omega : (2 : Int)^n * m = 2^s * r)
      exact ⟨hmr, congrArg Nat.succ hns⟩

/-- Specialize `every_even_base` to a supplied positive odd core and exponent. -/
private theorem known_factorization (m : Int) (n : Nat) (hm : 0 < m) (hodd : m % 2 = 1)
    (hn : 0 < n) : TheoremCStatement m n := by
  have hs : (2 : Int) ≤ 2^n := by
    have h := Int.pow_lt_pow_of_lt (by decide : (1 : Int) < 2) hn
    simp only [Int.pow_zero] at h
    omega
  have hB : 2 ≤ (2 : Int)^n * m := by
    have h := Int.mul_le_mul_of_nonneg_left (show 1 ≤ m by omega) (show 0 ≤ (2 : Int)^n by omega)
    simp only [Int.mul_one] at h
    omega
  have heven : ((2 : Int)^n * m) % 2 = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [Int.pow_succ', Int.mul_assoc]
    omega
  obtain ⟨r, s, -, hro, -, heq, hC⟩ := every_even_base _ hB heven
  obtain ⟨rfl, rfl⟩ := odd_factorization_unique hodd hro heq
  exact hC

/-! ## The two Challenge theorems -/

theorem unique_cycle_length (k n : Nat) :
    HasUniqueCycleOfLength (3 * 2 ^ (2 * k + 1)) (6 * (k + 1)) ∧
      HasUniqueCycleOfLength (5 * 2 ^ (2 * k + 1)) 1 ∧
      (1 ≤ n → ¬ 3 ∣ n → HasUniqueCycleOfLength (7 * 2 ^ n) 3) := by
  have hs : (0 : Int) < 2 ^ (2 * k + 1) := Int.pow_pos (by decide)
  have hs' := Nat.two_pow_pos (2 * k + 1)
  refine ⟨?_, ?_, ?_⟩
  · have hBz : ((3 * 2 ^ (2 * k + 1) : Nat) : Int) = 2 ^ (2 * k + 1) * 3 := by
      rw [Int.mul_comm]; norm_cast
    have hC := known_factorization 3 (2 * k + 1) (by decide) (by decide) (by omega)
    have hu := hC.uniqueness.mpr (Or.inl ⟨rfl, by omega⟩)
    have hL := hC.unique_lengths.1 rfl (by omega)
    rw [show (2 * k + 1) / 2 = k by omega] at hL
    rw [← hBz] at hu
    have hp : validPair ((3 * 2 ^ (2 * k + 1) : Nat) : Int) (2 ^ (2 * k + 1), 0) := by
      rw [hBz]; simp only [validPair]; omega
    exact unique_of_dev _ (by omega) _ hp _ hu (hBz ▸ hL)
  · have hBz : ((5 * 2 ^ (2 * k + 1) : Nat) : Int) = 2 ^ (2 * k + 1) * 5 := by
      rw [Int.mul_comm]; norm_cast
    have hC := known_factorization 5 (2 * k + 1) (by decide) (by decide) (by omega)
    have hu := hC.uniqueness.mpr (Or.inr (Or.inl ⟨rfl, by omega⟩))
    have hL := hC.unique_lengths.2.1 rfl (by omega)
    rw [← hBz] at hu
    have hp : validPair ((5 * 2 ^ (2 * k + 1) : Nat) : Int)
        (scale (2 ^ (2 * k + 1)) (3, 1)) := by
      rw [hBz]; simp only [validPair, scale]; omega
    exact unique_of_dev _ (by omega) _ hp _ hu (hBz ▸ hL)
  · intro hn h3
    have hn3 : n % 3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using h3
    have hs7 : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
    have hs7' := Nat.two_pow_pos n
    have hBz : ((7 * 2 ^ n : Nat) : Int) = 2 ^ n * 7 := by
      rw [Int.mul_comm]; norm_cast
    have hC := known_factorization 7 n (by decide) (by decide) (by omega)
    have hu := hC.uniqueness.mpr (Or.inr (Or.inr ⟨rfl, hn3⟩))
    have hL := hC.unique_lengths.2.2 rfl hn3
    rw [← hBz] at hu
    have hp : validPair ((7 * 2 ^ n : Nat) : Int) (scale (2 ^ n) (3, 1)) := by
      rw [hBz]; simp only [validPair, scale]; omega
    exact unique_of_dev _ (by omega) _ hp _ hu (hBz ▸ hL)

theorem unique_cycle_iff (B : Nat) (hB : 2 ≤ B) (heven : B % 2 = 0) :
    (∃ L, HasUniqueCycleOfLength B L) ↔
      (∃ k, B = 3 * 2 ^ (2 * k + 1)) ∨ (∃ k, B = 5 * 2 ^ (2 * k + 1)) ∨
        (∃ n, 1 ≤ n ∧ ¬ 3 ∣ n ∧ B = 7 * 2 ^ n) := by
  constructor
  · rintro ⟨L, h⟩
    have hu := dev_of_unique B L hB h
    obtain ⟨m, n, -, -, hnpos, he, hC⟩ := every_even_base (B : Int) (by omega) (by omega)
    rw [he] at hu
    rcases hC.uniqueness.mp hu with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
    · refine Or.inl ⟨n / 2, ?_⟩
      rw [show 2 * (n / 2) + 1 = n by omega]
      have h3 : (B : Int) = 3 * 2 ^ n := by rw [he]; exact Int.mul_comm _ _
      exact_mod_cast h3
    · refine Or.inr (Or.inl ⟨n / 2, ?_⟩)
      rw [show 2 * (n / 2) + 1 = n by omega]
      have h5 : (B : Int) = 5 * 2 ^ n := by rw [he]; exact Int.mul_comm _ _
      exact_mod_cast h5
    · refine Or.inr (Or.inr ⟨n, hnpos, (by simpa only [Nat.dvd_iff_mod_eq_zero] using hn), ?_⟩)
      have h7 : (B : Int) = 7 * 2 ^ n := by rw [he]; exact Int.mul_comm _ _
      exact_mod_cast h7
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨n, hnpos, hn, rfl⟩)
    · exact ⟨_, (unique_cycle_length k 0).1⟩
    · exact ⟨_, (unique_cycle_length k 0).2.1⟩
    · exact ⟨_, (unique_cycle_length 0 n).2.2 hnpos hn⟩

#print axioms unique_cycle_iff
#print axioms unique_cycle_length

end PalomarKaprekar
