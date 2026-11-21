module

public import Solution
import all Solution
import TheoremC

/-!
# Solution for the even-base cycle classification

The original Solution supplies the digit-sorting definitions and the conjugacy
between natural numbers below `B^4` and the development's four-slot words.
The new definitions through `HigherPowerCycles` are identical to the Challenge.
The proofs below transport the cases of `KaprekarBoundary.theoremC` to natural
numbers, using the development's scaled-pair dynamics to identify the lifted
orbits. Comparator checks all four declarations against the standalone Challenge.
-/

@[expose] public section

namespace PalomarKaprekar

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

open KaprekarBoundary

private theorem periodic_iff (B x : Nat) (hB : 2 ≤ B) (hx : x < B ^ 4) :
    IsPeriodic B x ↔ periodic (step (B : Int)) (word B x) := by
  constructor
  · rintro ⟨k, hk, eq⟩
    exact ⟨k - 1, by
      rw [show k - 1 + 1 = k by omega]
      exact (iterate_eq_iff B x x k hB hx hx).mp eq⟩
  · rintro ⟨k, eq⟩
    exact ⟨k + 1, by omega, (iterate_eq_iff B x x (k + 1) hB hx hx).mpr eq⟩

private theorem representative_data (B : Nat) (hB : 2 ≤ B) (p : Pair)
    (hp : validPair (B : Int) p) :
    let x := wordOfDifferences B p
    x < B ^ 4 ∧ ¬ IsRepdigit B x ∧ word B x = fromPair (B : Int) p := by
  obtain ⟨x, hvalue, hx, hword⟩ := value_nat B (by omega) _ (fromPair_valid _ _ hp)
  have rep : wordOfDifferences B p = x := by
    have h : wordOfDifferences B p = ((fromPair (B : Int) p).value B).toNat := by
      by_cases hzero : p.2 = 0 <;> simp [wordOfDifferences, fromPair, Digits.value, hzero]
    rw [h, ← hvalue]
    simp
  rw [rep]
  refine ⟨hx, (nonconstant_word B x).mpr ?_, hword⟩
  rw [hword, nonconstant_iff, pair_of_subtraction _ _ hp]
  have hpos := (pairMap_valid _ _ hp).1
  omega

private theorem represented_iterate_iff (B : Nat) (hB : 2 ≤ B) (p : Pair)
    (hp : validPair (B : Int) p) (x i : Nat) (hx : x < B ^ 4) :
    iterate (kaprekar B) i (wordOfDifferences B p) = x ↔
      iter (step (B : Int)) i (fromPair (B : Int) p) = word B x := by
  obtain ⟨hrep, -, hword⟩ := representative_data B hB p hp
  rw [iterate_eq_iff B _ x i hB hrep hx, hword]

private theorem represented_orbit_iff (B : Nat) (hB : 2 ≤ B) (p : Pair)
    (hp : validPair (B : Int) p) (x : Nat) (hx : x < B ^ 4) :
    OnOrbit B (wordOfDifferences B p) x ↔
      reaches (step (B : Int)) (fromPair (B : Int) p) (word B x) :=
  exists_congr (fun i => represented_iterate_iff B hB p hp x i hx)

private theorem represented_period (B : Nat) (hB : 2 ≤ B) (p : Pair)
    (hp : validPair (B : Int) p) (L : Nat) (hL : digitPeriod (B : Int) p L) :
    IsCycleOfLength B (wordOfDifferences B p) L := by
  obtain ⟨hx, hrep, hword⟩ := representative_data B hB p hp
  refine ⟨hx, hrep, hL.1, ?_, ?_⟩
  · exact (represented_iterate_iff B hB p hp _ L hx).mpr (hword ▸ hL.2.1)
  · intro i hi hiL hiRet
    have eq := (represented_iterate_iff B hB p hp _ i hx).mp hiRet
    rw [hword] at eq
    exact hL.2.2 i hi hiL eq

private theorem valid_boundary_reps (B : Nat) (m : Int) (n : Nat)
    (hcast : (B : Int) = 2 ^ n * m) (hm : 3 ≤ m) :
    validPair (B : Int) (2 ^ n, 0) ∧ validPair (B : Int) (2 * 2 ^ n, 0) := by
  have hs : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  have h1 := Int.mul_lt_mul_of_pos_left (show (1 : Int) < m by omega) hs
  have h2 := Int.mul_lt_mul_of_pos_left (show (2 : Int) < m by omega) hs
  simp only [Int.mul_one] at h1
  rw [Int.mul_comm _ 2] at h2
  simp only [validPair, hcast]
  exact ⟨⟨by omega, h1, by omega, by omega⟩, ⟨by omega, h2, by omega, by omega⟩⟩

private theorem boundary_rep_one (B n : Nat) :
    boundaryRepresentative B n 1 = wordOfDifferences B (2 ^ n, 0) := by
  simp [boundaryRepresentative]

private theorem in_odd_core_iff (m : Int) (p : Pair) :
    InOddCore m p ↔ oddCore m p := by
  grind [InOddCore, oddCore, validPair]

private theorem core_iterate_eq (m : Int) (hm : m % 2 = 1) (p : Pair) (hp : oddCore m p)
    (i : Nat) : coreIterate m i p = iter (pairMap m) i p := by
  rw [generic_actual_iter m p (fun k => oddCore_away m hm _ (oddCore_orbit m hm p hp k))]
  induction i with
  | zero => rfl
  | succ i ih =>
    change genericMap m (coreIterate m i p) = genericMap m (iter (genericMap m) i p)
    rw [ih]

/-- **Theorem 1(a)**: all cycles and their lengths for odd part at least five. -/
theorem cycles_odd_core (m n : Nat) (hodd : m % 2 = 1) (hm : 5 ≤ m) (hn : 1 ≤ n) :
    LargeOddCoreCycles (2 ^ n * m) m n := by
  let B : Nat := 2 ^ n * m
  let s : Int := 2 ^ n
  have hs : 0 < s := Int.pow_pos (by decide)
  have hB : 2 ≤ B := by
    have h := Nat.le_mul_of_pos_left m (Nat.pow_pos (n := n) (by decide : 0 < (2 : Nat)))
    omega
  have hcast : (B : Int) = 2 ^ n * (m : Int) := by simp [B]
  have hodd' : (m : Int) % 2 = 1 := by exact_mod_cast hodd
  have dev := (theoremC (m : Int) n (by omega) hodd' (by omega)).odd_core (by omega)
  obtain ⟨hS, hE⟩ := valid_boundary_reps B (m : Int) n hcast (by omega)
  have hLift (p : Pair) (hp : oddCore (m : Int) p) : validPair (B : Int) (scale s p) := by
    rw [hcast]
    exact scaled_core_valid _ s hs p hp
  have hWord (x : Nat) (hx : x < B ^ 4) (hrep : ¬ IsRepdigit B x) :=
    dev.words (word B x) (hcast ▸ word_valid B x (by omega)) ((nonconstant_word B x).mp hrep)
  have cancel_scale (p q : Pair) : scale s p = scale s q ↔ p = q := by
    constructor
    · intro h
      exact Prod.ext
        ((Int.mul_eq_mul_left_iff (Int.ne_of_gt hs)).mp (congrArg Prod.fst h))
        ((Int.mul_eq_mul_left_iff (Int.ne_of_gt hs)).mp (congrArg Prod.snd h))
    · exact congrArg (scale s)
  change LargeOddCoreCycles B m n
  constructor
  · intro x hx hrep
    rw [periodic_iff B x hB hx, boundary_rep_one]
    change periodic (step (B : Int)) (word B x) ↔
      (∃ p, InOddCore m p ∧ OnOrbit B (wordOfDifferences B (scale s p)) x) ∨
      ((m : Int) ∣ s - 1) ∧ OnOrbit B (wordOfDifferences B (s, 0)) x ∨
      m = 5 ∧ n % 4 = 2 ∧ OnOrbit B (wordOfDifferences B (2 * s, 0)) x
    rw [represented_orbit_iff B hB _ hS x hx, represented_orbit_iff B hB _ hE x hx]
    have hpairs :
        (∃ p, InOddCore m p ∧ OnOrbit B (wordOfDifferences B (scale s p)) x) ↔
        ∃ p, oddCore (m : Int) p ∧ periodic (pairMap (m : Int)) p ∧
          word B x = fromPair (B : Int) (scale s p) := by
      constructor
      · rintro ⟨p, hp, hit⟩
        have hp' := (in_odd_core_iff _ _).mp hp
        obtain ⟨i, hi⟩ := (represented_orbit_iff B hB _ (hLift p hp') x hx).mp hit
        have hi' := iter_fromPair (B : Int) (scale s p) (hLift p hp') i
        rw [hi', hcast, iter_scaled_core _ hodd' n p hp' i] at hi
        let q := iter (pairMap (m : Int)) i p
        have hq : oddCore (m : Int) q := by
          dsimp [q]
          rw [generic_actual_iter _ _ (fun k =>
            oddCore_away _ hodd' _ (oddCore_orbit _ hodd' _ hp' k))]
          exact oddCore_orbit _ hodd' _ hp' i
        have result := hi.symm
        rw [← hcast] at result
        exact ⟨q, hq, oddCore_periodic _ hodd' q hq, result⟩
      · rintro ⟨p, hp, -, eq⟩
        exact ⟨p, (in_odd_core_iff _ _).mpr hp,
          (represented_orbit_iff B hB _ (hLift _ hp) x hx).mpr ⟨0, eq.symm⟩⟩
    rw [hpairs, hcast]
    have h5 : ((m : Int) = 5) ↔ m = 5 := by omega
    simpa only [s, h5] using hWord x hx hrep
  · intro p hp
    have hp' := (in_odd_core_iff _ _).mp hp
    have v := hLift p hp'
    obtain ⟨hx, hrep, hword⟩ := representative_data B hB (scale s p) v
    refine ⟨hx, hrep, (periodic_iff B _ hB hx).mpr ?_⟩
    obtain ⟨k, hk⟩ := oddCore_periodic _ hodd' p hp'
    have ret := (dev.lift_clock p hp' (k + 1)).mpr hk
    rw [hword, hcast]
    exact ⟨k, ret⟩
  · intro p q hp hq
    have hp' := (in_odd_core_iff _ _).mp hp
    have hq' := (in_odd_core_iff _ _).mp hq
    obtain ⟨hqB, -, hqWord⟩ := representative_data B hB _ (hLift q hq')
    change OnOrbit B (wordOfDifferences B (scale s p)) (wordOfDifferences B (scale s q)) ↔ _
    rw [represented_orbit_iff B hB _ (hLift p hp') _ hqB, hqWord,
      word_reach_iff _ _ _ (hLift p hp') (hLift q hq'), reaches]
    apply exists_congr
    intro i
    rw [hcast, iter_scaled_core _ hodd' n p hp', cancel_scale, core_iterate_eq _ hodd' p hp']
  · intro p hp i
    have hp' := (in_odd_core_iff _ _).mp hp
    obtain ⟨hx, -, hword⟩ := representative_data B hB _ (hLift p hp')
    change iterate (kaprekar B) i (wordOfDifferences B (scale s p)) =
      wordOfDifferences B (scale s p) ↔ _
    rw [represented_iterate_iff B hB _ (hLift p hp') _ i hx, hword, hcast,
      dev.lift_clock p hp' i, core_iterate_eq _ hodd' p hp']
  · intro h
    rw [boundary_rep_one]
    exact represented_period B hB _ hS _ (hcast.symm ▸ dev.residue_one h)
  · intro h5 h4
    exact represented_period B hB _ hE _ (hcast.symm ▸ dev.exceptional_five (by exact_mod_cast h5) h4)
  · intro p hp
    have hp' := (in_odd_core_iff _ _).mp hp
    rw [boundary_rep_one]
    change ¬ OnOrbit B (wordOfDifferences B (scale s p)) (wordOfDifferences B (s, 0)) ∧
      ¬ OnOrbit B (wordOfDifferences B (scale s p)) (wordOfDifferences B (2 * s, 0))
    have separated (q : Pair) (hq : validPair (B : Int) q) (hz : q.2 = 0) :
        ¬ OnOrbit B (wordOfDifferences B (scale s p)) (wordOfDifferences B q) := by
      obtain ⟨hx, -, hword⟩ := representative_data B hB q hq
      rw [represented_orbit_iff B hB _ (hLift p hp') _ hx, hword, hcast]
      exact dev.separate p hp' q (hcast ▸ hq) (Or.inl hz)
    exact ⟨separated _ hS rfl, separated _ hE rfl⟩
  · rintro ⟨hres, h5, h4⟩
    exact dev.exclusive ⟨hres, by exact_mod_cast h5, h4⟩

/-- **Theorem 1(b)**: all cycles and their lengths for odd part three. -/
theorem cycles_core_three (n : Nat) (hn : 1 ≤ n) : ThreeCoreCycles (2 ^ n * 3) n := by
  let B : Nat := 2 ^ n * 3
  let s : Int := 2 ^ n
  have hB : 2 ≤ B := by
    have h := Nat.le_mul_of_pos_left 3 (Nat.pow_pos (n := n) (by decide : 0 < (2 : Nat)))
    omega
  have hcast : (B : Int) = 2 ^ n * 3 := by simp [B]
  have dev := (theoremC 3 n (by decide) (by decide) (by omega)).core_three rfl
  obtain ⟨hS, hE⟩ := valid_boundary_reps B 3 n hcast (by decide)
  change ThreeCoreCycles B n
  constructor
  · intro x hx hrep
    rw [periodic_iff B x hB hx, boundary_rep_one]
    change periodic (step (B : Int)) (word B x) ↔
      OnOrbit B (wordOfDifferences B (s, 0)) x ∨
      n % 2 = 0 ∧ OnOrbit B (wordOfDifferences B (2 * s, 0)) x
    rw [represented_orbit_iff B hB _ hS x hx, represented_orbit_iff B hB _ hE x hx, hcast]
    exact dev.words _ (hcast ▸ word_valid B x (by omega)) ((nonconstant_word B x).mp hrep)
  · rw [boundary_rep_one]
    have periods := dev.periods
    split
    · rename_i he
      rw [ite_eq_left he] at periods
      exact ⟨represented_period B hB _ hS _ (hcast.symm ▸ periods.1),
        represented_period B hB _ hE _ (hcast.symm ▸ periods.2)⟩
    · rename_i he
      rw [ite_eq_right he] at periods
      exact represented_period B hB _ hS _ (hcast.symm ▸ periods)
  · intro he hit
    have periods := dev.periods
    rw [ite_eq_left he] at periods
    rw [boundary_rep_one] at hit
    obtain ⟨hx, -, hword⟩ := representative_data B hB _ hE
    obtain ⟨i, hi⟩ := (represented_orbit_iff B hB _ hS _ hx).mp hit
    rw [hword, hcast] at hi
    exact periods.2.2.2 (n + 1) (by omega) (by omega)
      (by rw [← hi, iter_commute, periods.1.2.1])

/-- **Theorem 1(c), base two**: the only cycles are the fixed points `0111` and `1001`
(decimal 7 and 9). -/
theorem cycles_base_two :
    (∀ x, x < 2 ^ 4 → ¬ IsRepdigit 2 x → (IsPeriodic 2 x ↔ x = 7 ∨ x = 9)) ∧
      IsCycleOfLength 2 7 1 ∧ IsCycleOfLength 2 9 1 := by
  have dev := (theoremC 1 1 (by decide) (by decide) (by decide)).binary rfl rfl
  have hTwo : 2 ≤ (2 : Nat) := by decide
  have w7 : word 2 7 = ⟨0, 1, 1, 1⟩ := by decide
  have w9 : word 2 9 = ⟨1, 0, 0, 1⟩ := by decide
  have hw (x y : Nat) (hx : x < 2 ^ 4) (hy : y < 2 ^ 4) : word 2 x = word 2 y ↔ x = y :=
    (iterate_eq_iff 2 x y 0 hTwo hx hy).symm
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hrep
    rw [periodic_iff 2 x hTwo hx]
    change periodic (step (2 : Int)) (word 2 x) ↔ _
    rw [dev _ (word_valid 2 x (by decide)) ((nonconstant_word 2 x).mp hrep),
      ← w7, ← w9, hw x 7 hx (by decide), hw x 9 hx (by decide)]
  · exact ⟨by decide, by simp [IsRepdigit], by decide, by decide, by omega⟩
  · exact ⟨by decide, by simp [IsRepdigit], by decide, by decide, by omega⟩

private theorem power_rep (n i : Nat) (b : Bool) :
    powerRepresentative n i b = wordOfDifferences (2 ^ n) (powerRep n i b) := by
  cases b <;> rfl

/-- **Theorem 1(c), higher powers of two**: the complete count and least-period
table in base `2^n` for `n ≥ 2`. -/
theorem cycles_higher_powers_two (n : Nat) (hn : 2 ≤ n) : HigherPowerCycles n := by
  let B : Nat := 2 ^ n
  have hB : 2 ≤ B := by
    have h := Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) (show 0 < n by omega)
    omega
  have hcast : (B : Int) = 2 ^ n := by simp [B]
  have dev := (theoremC 1 n (by decide) (by decide) (by omega)).pure_power rfl hn
  have hp (i : Fin (n / 2)) : validPair (B : Int) (powZ i.val) ∧ validPair (B : Int) (powA n i.val) := by
    have hi := i.isLt
    have h := pow_valid i.val (n - i.val - 2)
    dsimp only at h
    rw [show i.val + (n - i.val - 2) + 2 = n by omega] at h
    rw [hcast]
    exact h
  have hv (i : Fin (n / 2)) (b : Bool) : validPair (B : Int) (powerRep n i.val b) := by
    cases b
    · exact (hp i).1
    · exact (hp i).2
  have reach (i : Fin (n / 2)) (b : Bool) (x : Nat) (hx : x < B ^ 4) :
      OnOrbit B (powerRepresentative n i.val b) x ↔
        reaches (step (B : Int)) (fromPair (B : Int) (powerRep n i.val b)) (word B x) := by
    rw [power_rep]
    exact represented_orbit_iff B hB _ (hv i b) x hx
  constructor
  · intro x hx hrep
    change IsPeriodic B x ↔ ∃ (i : Fin (n / 2)) (b : Bool),
      OnOrbit B (powerRepresentative n i.val b) x
    rw [periodic_iff B x hB hx]
    refine (dev.words _ (hcast ▸ word_valid B x (by omega))
      ((nonconstant_word B x).mp hrep)).trans ?_
    rw [← hcast]
    exact exists_congr (fun i => exists_congr (fun b => (reach i b x hx).symm))
  · intro i j b c
    have hx := representative_data B hB _ (hv j c)
    have eq : powerRepresentative n j.val c < B ^ 4 := by rw [power_rep]; exact hx.1
    rw [reach i b _ eq, power_rep, hx.2.2, hcast]
    exact dev.disjoint i j b c
  · intro i
    obtain ⟨hz, ha⟩ := dev.periods i
    exact ⟨represented_period B hB _ (hp i).1 _ (hcast.symm ▸ hz),
      represented_period B hB _ (hp i).2 _ (hcast.symm ▸ ha)⟩
  · exact dev.odd_counts
  · exact dev.even_counts

#print axioms cycles_odd_core
#print axioms cycles_core_three
#print axioms cycles_base_two
#print axioms cycles_higher_powers_two

end PalomarKaprekar
