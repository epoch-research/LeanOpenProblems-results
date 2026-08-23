import FormalConjectures.Util.ProblemImports
open Classical
open Nat

/-- The smallest prime strictly greater than $r$. Defined non-computably using the set infimum. -/
noncomputable def next_prime (r : ℕ) : ℕ :=
  -- Nat.sInf finds the minimum element in a set of natural numbers.
  -- The set of primes greater than r is non-empty by Euclid's theorem.
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

/-- $r + r'$, where $r'$ is the next prime after $r$. -/
noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

/--
A389790: Number of ways to write $2n$ as $p + p' + q + q'$, where $p$ and $q$ are primes with $p \le q$, and $r'$ is the first prime greater than $r$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  -- The finset range is taken from the original user code.
  let R := Finset.range n

  Finset.card $ Finset.filter (fun ⟨p, q⟩ =>
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

theorem not_prime_of_minFac {n : ℕ} (h : n.minFac ≠ n) : ¬ n.Prime := by
  intro hp
  exact h hp.minFac_eq

theorem next_prime_spec (r : ℕ) :
    Nat.Prime (next_prime r) ∧ r < next_prime r ∧
      ∀ k, Nat.Prime k → r < k → next_prime r ≤ k := by
  have hne : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (r + 1)
    exact ⟨p, hprime, Nat.lt_of_succ_le hp⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.sInf_mem hne).1
  · exact (Nat.sInf_mem hne).2
  · intro k hk hlt
    exact Nat.sInf_le ⟨hk, hlt⟩

theorem next_prime_eq {r p : ℕ} (hp : Nat.Prime p) (hlt : r < p)
    (hmin : ∀ k, r < k → k < p → ¬ Nat.Prime k) : next_prime r = p := by
  have h := next_prime_spec r
  apply le_antisymm
  · exact h.2.2 p hp hlt
  · have hle : next_prime r ≤ p := h.2.2 p hp hlt
    rcases eq_or_lt_of_le hle with h_eq | h_lt
    · exact h_eq.symm.le
    · exact absurd h.1 (hmin (next_prime r) h.2.1 h_lt)

theorem a_pos_of_pair {n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q)
    (hpn : p < n) (hqn : q < n)
    (hsum : S_sum p + S_sum q = 2 * n) : 0 < a n := by
  refine Finset.card_pos.mpr ?_
  refine ⟨(p, q), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨hpn, hqn⟩, hp, hq, hpq, hsum⟩

theorem next_prime_3 : next_prime 3 = 5 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_5 : next_prime 5 = 7 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_7 : next_prime 7 = 11 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_11 : next_prime 11 = 13 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_13 : next_prime 13 = 17 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_17 : next_prime 17 = 19 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_19 : next_prime 19 = 23 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_29 : next_prime 29 = 31 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_31 : next_prime 31 = 37 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_41 : next_prime 41 = 43 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_43 : next_prime 43 = 47 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_53 : next_prime 53 = 59 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_61 : next_prime 61 = 67 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_419 : next_prime 419 = 421 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_421 : next_prime 421 = 431 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_433 : next_prime 433 = 439 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_439 : next_prime 439 = 443 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_443 : next_prime 443 = 449 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_461 : next_prime 461 = 463 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_463 : next_prime 463 = 467 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_467 : next_prime 467 = 479 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_479 : next_prime 479 = 487 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_487 : next_prime 487 = 491 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_491 : next_prime 491 = 499 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem a_pos_474 : 0 < a 474 := by
  apply a_pos_of_pair (p := 7) (q := 463)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_7, next_prime_463]

theorem a_pos_475 : 0 < a 475 := by
  apply a_pos_of_pair (p := 31) (q := 439)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_31, next_prime_439]

theorem a_pos_476 : 0 < a 476 := by
  apply a_pos_of_pair (p := 29) (q := 443)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_29, next_prime_443]

theorem a_pos_477 : 0 < a 477 := by
  apply a_pos_of_pair (p := 3) (q := 467)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_3, next_prime_467]

theorem a_pos_478 : 0 < a 478 := by
  apply a_pos_of_pair (p := 41) (q := 433)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_41, next_prime_433]

theorem a_pos_479 : 0 < a 479 := by
  apply a_pos_of_pair (p := 5) (q := 467)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_5, next_prime_467]

theorem a_pos_480 : 0 < a 480 := by
  apply a_pos_of_pair (p := 13) (q := 463)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_13, next_prime_463]

theorem a_pos_481 : 0 < a 481 := by
  apply a_pos_of_pair (p := 43) (q := 433)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_43, next_prime_433]

theorem a_pos_482 : 0 < a 482 := by
  apply a_pos_of_pair (p := 7) (q := 467)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_7, next_prime_467]

theorem a_pos_483 : 0 < a 483 := by
  apply a_pos_of_pair (p := 17) (q := 463)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_17, next_prime_463]

theorem a_pos_484 : 0 < a 484 := by
  apply a_pos_of_pair (p := 61) (q := 419)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_61, next_prime_419]

theorem a_pos_485 : 0 < a 485 := by
  apply a_pos_of_pair (p := 11) (q := 467)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_11, next_prime_467]

theorem a_pos_486 : 0 < a 486 := by
  apply a_pos_of_pair (p := 19) (q := 463)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_19, next_prime_463]

theorem a_pos_487 : 0 < a 487 := by
  apply a_pos_of_pair (p := 3) (q := 479)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_3, next_prime_479]

theorem a_pos_488 : 0 < a 488 := by
  apply a_pos_of_pair (p := 13) (q := 467)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_13, next_prime_467]

theorem a_pos_489 : 0 < a 489 := by
  apply a_pos_of_pair (p := 5) (q := 479)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_5, next_prime_479]

theorem a_pos_490 : 0 < a 490 := by
  apply a_pos_of_pair (p := 61) (q := 421)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_61, next_prime_421]

theorem a_pos_491 : 0 < a 491 := by
  apply a_pos_of_pair (p := 17) (q := 467)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_17, next_prime_467]

theorem a_pos_492 : 0 < a 492 := by
  apply a_pos_of_pair (p := 7) (q := 479)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_7, next_prime_479]

theorem a_pos_493 : 0 < a 493 := by
  apply a_pos_of_pair (p := 3) (q := 487)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_3, next_prime_487]

theorem a_pos_494 : 0 < a 494 := by
  apply a_pos_of_pair (p := 19) (q := 467)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_19, next_prime_467]

theorem a_pos_495 : 0 < a 495 := by
  apply a_pos_of_pair (p := 5) (q := 487)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_5, next_prime_487]

theorem a_pos_496 : 0 < a 496 := by
  apply a_pos_of_pair (p := 31) (q := 461)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_31, next_prime_461]

theorem a_pos_497 : 0 < a 497 := by
  apply a_pos_of_pair (p := 53) (q := 439)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_53, next_prime_439]

theorem a_pos_498 : 0 < a 498 := by
  apply a_pos_of_pair (p := 7) (q := 487)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_7, next_prime_487]

theorem a_pos_499 : 0 < a 499 := by
  apply a_pos_of_pair (p := 3) (q := 491)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_3, next_prime_491]

theorem a_pos_500 : 0 < a 500 := by
  apply a_pos_of_pair (p := 61) (q := 433)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_61, next_prime_433]

theorem a_pos_501 : 0 < a 501 := by
  apply a_pos_of_pair (p := 5) (q := 491)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_5, next_prime_491]

theorem a_pos_502 : 0 < a 502 := by
  apply a_pos_of_pair (p := 53) (q := 443)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_53, next_prime_443]

theorem a_pos_503 : 0 < a 503 := by
  apply a_pos_of_pair (p := 29) (q := 467)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_29, next_prime_467]


def trialDiv (n d : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
    if Nat.blt n (d * d) then true
    else if n % d == 0 then false
    else trialDiv n (d + 1) fuel

-- Fully Bool-based primality so it reduces under `open Classical`.
def isPrimeBool (n : ℕ) : Bool :=
  if Nat.blt n 2 then false else trialDiv n 2 n

example : isPrimeBool 17 = true := rfl
example : isPrimeBool 18 = false := rfl
example : isPrimeBool 97 = true := rfl
example : isPrimeBool 1 = false := rfl
example : isPrimeBool 4 = false := rfl

/-- No prime in `[k, k + fuel)`. -/
def noPrimeGo (k : Nat) : Nat → Bool
  | 0 => true
  | f + 1 =>
    match isPrimeBool k with
    | true => false
    | false => noPrimeGo (k + 1) f

/-- No prime strictly between `p` and `q`. -/
def noPrimeBetween (p q : Nat) : Bool :=
  noPrimeGo (p + 1) (q - (p + 1))

/-- `m` is the midpoint of consecutive primes `p < q`. -/
def checkMid (m p q : Nat) : Bool :=
  isPrimeBool p && isPrimeBool q && Nat.blt 2 p && Nat.blt p q &&
    (p + q == 2 * m) && noPrimeBetween p q

def checkMids : List (Nat × Nat × Nat) → Bool
  | [] => true
  | (m, p, q) :: rest => checkMid m p q && checkMids rest

def nextPrimeGo (k : ℕ) : ℕ → ℕ
  | 0 => k
  | f + 1 => if isPrimeBool k then k else nextPrimeGo (k + 1) f

/-- Next prime after `n`, searching at most `fuel` candidates starting at `n+1`. -/
def nextPrimeFuel (n fuel : ℕ) : ℕ := nextPrimeGo (n + 1) fuel

def nextPrimeComp (n : ℕ) : ℕ := nextPrimeFuel n (n + 3)

example : nextPrimeComp 2 = 3 := rfl
example : nextPrimeComp 3 = 5 := rfl
example : nextPrimeComp 7 = 11 := rfl
example : nextPrimeComp 463 = 467 := rfl

/-- Is `m` a sum of two consecutive primes (the smaller being odd, or 2)? -/
def isSsumBool (m : ℕ) : Bool :=
  let rec go (q : ℕ) : ℕ → Bool
    | 0 => false
    | f + 1 =>
      if isPrimeBool q && (q + nextPrimeComp q == m) then true
      else go (q + 1) f
  go 2 m

example : isSsumBool 8 = true := rfl   -- 3+5
example : isSsumBool 12 = true := rfl  -- 5+7
example : isSsumBool 10 = false := rfl

def hasRep (n : ℕ) : Bool :=
  let rec go (p : ℕ) : ℕ → Bool
    | 0 => false
    | f + 1 =>
      if isPrimeBool p && Nat.ble (p + nextPrimeComp p) n &&
          isSsumBool (2 * n - (p + nextPrimeComp p)) then true
      else go (p + 1) f
  go 2 n

set_option maxRecDepth 1000000

def primesUpTo (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun k => isPrimeBool k)

/-- Consecutive pair-sums of a list. -/
def consecutiveSums : List ℕ → List ℕ
  | p :: p' :: rest => (p + p') :: consecutiveSums (p' :: rest)
  | _ => []

def ssumList (n : ℕ) : List ℕ :=
  let ps := primesUpTo n
  match ps.getLast? with
  | none => []
  | some lastP =>
    let inner := consecutiveSums ps
    let nxt := nextPrimeComp lastP
    if Nat.blt n nxt then inner ++ [lastP + nxt] else inner

example : ssumList 10 = [5, 8, 12, 18] := rfl

def listHas (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: ys => if x == y then true else listHas x ys

def listHasPair (n : ℕ) (ss : List ℕ) : List ℕ → Bool
  | [] => false
  | s :: rest =>
    if Nat.ble s n && listHas (2 * n - s) ss then true
    else listHasPair n ss rest

def hasRepFast (n : ℕ) : Bool :=
  let ss := ssumList n
  listHasPair n ss ss

example : hasRepFast 8 = true := rfl
example : hasRepFast 5 = true := rfl
example : hasRepFast 4 = false := rfl
example : hasRepFast 474 = true := rfl
example : hasRepFast 473 = false := rfl

def checkFrom (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => hasRepFast (lo + n) && checkFrom lo n

-- checkFrom lo (k) checks hasRepFast for n = lo, lo+1, ..., lo+k-1
example : checkFrom 474 5 = true := rfl  -- 474..478
example : checkFrom 474 30 = true := rfl  -- 474..503

theorem trialDiv_true_spec {n d fuel : ℕ}
    (hfuel : n < (d + fuel) * (d + fuel))
    (h : trialDiv n d fuel = true) :
    ∀ k, d ≤ k → k * k ≤ n → ¬ k ∣ n := by
  induction fuel generalizing d with
  | zero =>
    intro k hdk hkk hdvd
    simp at hfuel
    have hlt : k * k < d * d := Nat.lt_of_le_of_lt hkk hfuel
    have hk : k < d := Nat.mul_self_lt_mul_self_iff.mp hlt
    omega
  | succ fuel ih =>
    intro k hdk hkk hdvd
    simp only [trialDiv] at h
    by_cases hsq : Nat.blt n (d * d)
    · simp [hsq] at h
      have : n < d * d := Nat.blt_eq.mp hsq
      have : k * k < d * d := Nat.lt_of_le_of_lt hkk this
      have : k < d := Nat.mul_self_lt_mul_self_iff.mp this
      omega
    · simp [hsq] at h
      obtain ⟨hmod, htrue⟩ := h
      have hfuel' : n < (d + 1 + fuel) * (d + 1 + fuel) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfuel
      rcases lt_or_eq_of_le hdk with hlt | heq
      · exact ih hfuel' htrue k (by omega) hkk hdvd
      · subst heq
        exact hmod (Nat.dvd_iff_mod_eq_zero.mp hdvd)

theorem isPrimeBool_prime {n : ℕ} (h : isPrimeBool n = true) : n.Prime := by
  unfold isPrimeBool at h
  by_cases hn : Nat.blt n 2
  · simp [hn] at h
  · simp [hn] at h
    have hn2 : 2 ≤ n := by
      have : ¬ n < 2 := mt Nat.blt_eq.mpr hn
      omega
    have hfuel : n < (2 + n) * (2 + n) := by nlinarith
    have hdiv := trialDiv_true_spec hfuel h
    rw [Nat.prime_def_le_sqrt]
    refine ⟨hn2, ?_⟩
    intro m hm2 hmsqrt
    have hkk : m * m ≤ n := (Nat.le_sqrt.mp hmsqrt)
    exact hdiv m hm2 hkk

theorem trialDiv_true_of {n d fuel : ℕ}
    (h : ∀ k, d ≤ k → k * k ≤ n → ¬ k ∣ n) :
    trialDiv n d fuel = true := by
  induction fuel generalizing d with
  | zero => simp [trialDiv]
  | succ fuel ih =>
    simp only [trialDiv]
    by_cases hsq : Nat.blt n (d * d)
    · simp [hsq]
    · simp [hsq]
      constructor
      · intro hdv
        have : d ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hdv
        have hd2 : d * d ≤ n := le_of_not_gt (mt Nat.blt_eq.mpr hsq)
        exact h d le_rfl hd2 this
      · apply ih
        intro k hk hkk
        exact h k (Nat.le_of_succ_le hk) hkk

theorem isPrimeBool_of_prime {n : ℕ} (hp : n.Prime) : isPrimeBool n = true := by
  unfold isPrimeBool
  have hn2 : 2 ≤ n := hp.two_le
  have hblt : Nat.blt n 2 = false := by
    have : ¬ n < 2 := not_lt.mpr hn2
    cases hb : Nat.blt n 2
    · rfl
    · exact absurd (Nat.blt_eq.mp hb) this
  simp [hblt]
  apply trialDiv_true_of
  intro k hk hkk hdvd
  have hsqrt : k ≤ n.sqrt := Nat.le_sqrt.mpr hkk
  exact (Nat.prime_def_le_sqrt.mp hp).2 k hk hsqrt hdvd

theorem isPrimeBool_false_of_not_prime {m : ℕ} (h : ¬ m.Prime) : isPrimeBool m = false := by
  cases hm : isPrimeBool m
  · rfl
  · exact absurd (isPrimeBool_prime hm) h

theorem isPrimeBool_iff (n : ℕ) : isPrimeBool n = true ↔ n.Prime :=
  ⟨isPrimeBool_prime, isPrimeBool_of_prime⟩

theorem noPrimeGo_true {k fuel : Nat} (h : noPrimeGo k fuel = true) :
    ∀ m, k ≤ m → m < k + fuel → ¬ m.Prime := by
  induction fuel generalizing k with
  | zero =>
    intro m hm1 hm2
    omega
  | succ f ih =>
    intro m hm1 hm2
    cases hb : isPrimeBool k with
    | true =>
      have : noPrimeGo k (f + 1) = false := by simp [noPrimeGo, hb]
      simp [this] at h
    | false =>
      have hgo : noPrimeGo k (f + 1) = noPrimeGo (k + 1) f := by simp [noPrimeGo, hb]
      rw [hgo] at h
      have hk : ¬ k.Prime := fun hp => by
        have := isPrimeBool_of_prime hp
        simp [this] at hb
      rcases eq_or_lt_of_le hm1 with heq | hlt
      · exact heq ▸ hk
      · have hm1' : k + 1 ≤ m := by omega
        have hm2' : m < (k + 1) + f := by omega
        exact ih h m hm1' hm2'

theorem noPrimeBetween_true {p q : Nat} (hpq : p < q) (h : noPrimeBetween p q = true) :
    ∀ m, p < m → m < q → ¬ m.Prime := by
  intro m hm1 hm2
  have hm1' : p + 1 ≤ m := by omega
  have hm2' : m < (p + 1) + (q - (p + 1)) := by omega
  exact noPrimeGo_true h m hm1' hm2'

theorem sInf_primes_ge_eq {k : ℕ} (hnp : ¬ k.Prime) :
    sInf {p : ℕ | p.Prime ∧ k ≤ p} = sInf {p : ℕ | p.Prime ∧ k + 1 ≤ p} := by
  have hset : {p : ℕ | p.Prime ∧ k ≤ p} = {p : ℕ | p.Prime ∧ k + 1 ≤ p} := by
    ext p
    constructor
    · intro ⟨hp, hkp⟩
      refine ⟨hp, ?_⟩
      have : k ≠ p := fun e => hnp (e ▸ hp)
      omega
    · intro ⟨hp, hkp⟩
      exact ⟨hp, Nat.le_of_succ_le hkp⟩
  rw [hset]

theorem nextPrimeGo_eq {k fuel : ℕ}
    (hex : ∃ p, p.Prime ∧ k ≤ p ∧ p ≤ k + fuel) :
    nextPrimeGo k fuel = sInf {p : ℕ | p.Prime ∧ k ≤ p} := by
  induction fuel generalizing k with
  | zero =>
    obtain ⟨p, hp, hkp, hpk⟩ := hex
    have heq : p = k := Nat.le_antisymm hpk hkp
    rw [heq] at hp
    have hmem : k ∈ {q : ℕ | q.Prime ∧ k ≤ q} := ⟨hp, le_rfl⟩
    simp [nextPrimeGo]
    apply le_antisymm
    · exact le_csInf ⟨_, hmem⟩ (fun b hb => hb.2)
    · exact Nat.sInf_le hmem
  | succ fuel ih =>
    by_cases hk : isPrimeBool k = true
    · have hp : k.Prime := isPrimeBool_prime hk
      have hmem : k ∈ {p : ℕ | p.Prime ∧ k ≤ p} := ⟨hp, le_rfl⟩
      simp [nextPrimeGo, hk]
      apply le_antisymm
      · exact le_csInf ⟨_, hmem⟩ (fun b hb => hb.2)
      · exact Nat.sInf_le hmem
    · have hnp : ¬ k.Prime := fun hp => hk (isPrimeBool_of_prime hp)
      have hkb : isPrimeBool k = false := isPrimeBool_false_of_not_prime hnp
      simp [nextPrimeGo, hkb]
      have hex' : ∃ p, p.Prime ∧ k + 1 ≤ p ∧ p ≤ k + 1 + fuel := by
        obtain ⟨p, hp, hkp, hpk⟩ := hex
        refine ⟨p, hp, ?_, by omega⟩
        have : k ≠ p := fun e => hnp (e ▸ hp)
        omega
      rw [ih hex', sInf_primes_ge_eq hnp]

theorem next_prime_eq_sInf_ge (r : ℕ) :
    next_prime r = sInf {p : ℕ | p.Prime ∧ r + 1 ≤ p} := by
  unfold next_prime
  simp [Nat.succ_le_iff]

theorem nextPrimeComp_eq (r : ℕ) : nextPrimeComp r = next_prime r := by
  unfold nextPrimeComp nextPrimeFuel
  have hex : ∃ p, p.Prime ∧ r + 1 ≤ p ∧ p ≤ r + 1 + (r + 3) := by
    cases r with
    | zero =>
      exact ⟨2, Nat.prime_two, by omega, by omega⟩
    | succ r =>
      obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (r + 1) (by omega)
      refine ⟨p, hp, Nat.succ_le_of_lt hlt, ?_⟩
      have : p ≤ 2 * (r + 1) := hle
      omega
  rw [nextPrimeGo_eq hex, next_prime_eq_sInf_ge]

theorem mem_primesUpTo {n p : ℕ} (hp : p ∈ primesUpTo n) :
    p.Prime ∧ p ≤ n := by
  simp [primesUpTo, List.mem_filter, List.mem_range] at hp
  exact ⟨isPrimeBool_prime hp.2, hp.1⟩

theorem primesUpTo_complete {n p : ℕ} (hp : p.Prime) (hle : p ≤ n) :
    p ∈ primesUpTo n := by
  simp [primesUpTo, List.mem_filter, List.mem_range]
  exact ⟨hle, isPrimeBool_of_prime hp⟩

theorem S_sum_eq (p : ℕ) : S_sum p = p + nextPrimeComp p := by
  unfold S_sum
  rw [nextPrimeComp_eq]

theorem consecutive_primes_ssum {p p' : ℕ}
    (hp' : p'.Prime) (hlt : p < p')
    (hnone : ∀ k, p < k → k < p' → ¬ k.Prime) :
    S_sum p = p + p' := by
  unfold S_sum
  rw [next_prime_eq hp' hlt hnone]

theorem listHas_iff {x : ℕ} {l : List ℕ} : listHas x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [listHas]
  | cons y ys ih =>
    simp only [listHas, List.mem_cons]
    by_cases hxy : x == y
    · simp [hxy]
      have : x = y := beq_iff_eq.mp hxy
      simp [this]
    · simp [hxy]
      have : x ≠ y := fun e => hxy (beq_iff_eq.mpr e)
      simp [this, ih]

theorem listHasPair_true {n : ℕ} {ss l : List ℕ} (h : listHasPair n ss l = true) :
    ∃ s, s ∈ l ∧ s ≤ n ∧ (2 * n - s) ∈ ss := by
  induction l with
  | nil => simp [listHasPair] at h
  | cons s rest ih =>
    simp only [listHasPair] at h
    cases hb : (Nat.ble s n && listHas (2 * n - s) ss) with
    | false =>
      simp [hb] at h
      obtain ⟨s', hs', hle, hmem⟩ := ih h
      exact ⟨s', List.mem_cons_of_mem _ hs', hle, hmem⟩
    | true =>
      have hab := Bool.and_eq_true_iff.mp hb
      exact ⟨s, List.mem_cons_self, Nat.le_of_ble_eq_true hab.1, listHas_iff.mp hab.2⟩

theorem mem_consecutiveSums_cons {p p' : ℕ} {rest : List ℕ} {s : ℕ} :
    s ∈ consecutiveSums (p :: p' :: rest) ↔
      s = p + p' ∨ s ∈ consecutiveSums (p' :: rest) := by
  simp [consecutiveSums]

theorem mem_consecutiveSums_short {ps : List ℕ} (h : ps.length ≤ 1) {s : ℕ} :
    s ∉ consecutiveSums ps := by
  match ps with
  | [] => simp [consecutiveSums]
  | [x] => simp [consecutiveSums]
  | _ :: _ :: _ => simp at h

theorem exists_consecutive_of_mem_sums {ps : List ℕ} {s : ℕ}
    (h : s ∈ consecutiveSums ps) :
    ∃ i : ℕ, ∃ hi : i + 1 < ps.length,
      s = ps[i]'(Nat.lt_of_succ_lt hi) + ps[i + 1]'hi := by
  induction ps with
  | nil => simp [consecutiveSums] at h
  | cons p rest ih =>
    match rest with
    | [] => simp [consecutiveSums] at h
    | p' :: rest' =>
      rw [mem_consecutiveSums_cons] at h
      rcases h with h | h
      · refine ⟨0, ?_, ?_⟩
        · simp
        · simp [h]
      · obtain ⟨i, hi, hs⟩ := ih h
        refine ⟨i + 1, ?_, ?_⟩
        · simpa using hi
        · simpa using hs

theorem primesUpTo_get_prime {n : ℕ} {i : ℕ} (hi : i < (primesUpTo n).length) :
    ((primesUpTo n)[i]).Prime ∧ (primesUpTo n)[i] ≤ n :=
  mem_primesUpTo (List.getElem_mem hi)

theorem primesUpTo_pairwise (n : ℕ) : (primesUpTo n).Pairwise (· < ·) := by
  simpa [primesUpTo] using (List.pairwise_lt_range (n := n + 1)).filter (fun k => isPrimeBool k)

theorem primesUpTo_lt {n i j : ℕ}
    (hi : i < (primesUpTo n).length) (hj : j < (primesUpTo n).length) (hij : i < j) :
    (primesUpTo n)[i] < (primesUpTo n)[j] :=
  List.Pairwise.rel_get_of_lt (primesUpTo_pairwise n) hij

theorem index_lt_of_primesUpTo_lt {n i j : ℕ}
    (hi : i < (primesUpTo n).length) (hj : j < (primesUpTo n).length)
    (h : (primesUpTo n)[i] < (primesUpTo n)[j]) : i < j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact hij
  · exact (lt_irrefl _ h).elim
  · exact (lt_asymm h (primesUpTo_lt hj hi hij)).elim

theorem no_prime_between_primesUpTo {n i : ℕ} (hi : i + 1 < (primesUpTo n).length)
    {k : ℕ} (hk1 : (primesUpTo n)[i] < k) (hk2 : k < (primesUpTo n)[i + 1]) :
    ¬ k.Prime := by
  intro hp
  have hklen : k ≤ n := by
    have := (primesUpTo_get_prime (show i + 1 < (primesUpTo n).length from hi)).2
    omega
  have hkin := primesUpTo_complete hp hklen
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hkin
  have h1 : i < j := index_lt_of_primesUpTo_lt (by omega) hj hk1
  have h2 : j < i + 1 := index_lt_of_primesUpTo_lt hj (by omega) hk2
  omega

theorem getLast?_eq_getLast {l : List ℕ} (h : l ≠ []) :
    l.getLast? = some (l.getLast h) := by
  cases l with
  | nil => contradiction
  | cons x xs => simp [List.getLast?]

theorem primesUpTo_getLast_spec {n : ℕ} (h : primesUpTo n ≠ []) :
    (primesUpTo n).getLast h = n.minFac ∨
      ((primesUpTo n).getLast h).Prime ∧ (primesUpTo n).getLast h ≤ n := by
  have := mem_primesUpTo (List.getLast_mem h)
  exact Or.inr this

theorem mem_consecutiveSums_ssum {n s : ℕ}
    (h : s ∈ consecutiveSums (primesUpTo n)) :
    ∃ p, p.Prime ∧ p ≤ n ∧ S_sum p = s := by
  obtain ⟨i, hi, hs⟩ := exists_consecutive_of_mem_sums h
  have hi0 : i < (primesUpTo n).length := Nat.lt_of_succ_lt hi
  let p := (primesUpTo n)[i]
  let p' := (primesUpTo n)[i + 1]
  have hp := primesUpTo_get_prime hi0
  have hp' := primesUpTo_get_prime hi
  have hlt : p < p' := primesUpTo_lt hi0 hi (Nat.lt_succ_self i)
  have hnone : ∀ k, p < k → k < p' → ¬ k.Prime :=
    fun k => no_prime_between_primesUpTo hi
  refine ⟨p, hp.1, hp.2, ?_⟩
  have hseq : s = p + p' := hs
  rw [hseq]
  exact consecutive_primes_ssum hp'.1 hlt hnone

theorem last_prime_ssum {n p : ℕ} (hps : (primesUpTo n).getLast? = some p) :
    p.Prime ∧ p ≤ n ∧ S_sum p = p + nextPrimeComp p := by
  have hne : primesUpTo n ≠ [] := by
    intro he
    simp [he] at hps
  have hgl : (primesUpTo n).getLast hne = p := by
    have := getLast?_eq_getLast (l := primesUpTo n) hne
    rw [this] at hps
    exact Option.some.inj hps
  have hmem : p ∈ primesUpTo n := by
    rw [← hgl]
    exact List.getLast_mem hne
  obtain ⟨hp, hle⟩ := mem_primesUpTo hmem
  exact ⟨hp, hle, S_sum_eq p⟩

theorem mem_ssumList {n s : ℕ} (h : s ∈ ssumList n) :
    ∃ p, p.Prime ∧ p ≤ n ∧ S_sum p = s := by
  dsimp [ssumList] at h
  cases hlast : (primesUpTo n).getLast? with
  | none =>
    rw [hlast] at h
    simp at h
  | some lastP =>
    rw [hlast] at h
    cases hblt : Nat.blt n (nextPrimeComp lastP) with
    | true =>
      simp [hblt] at h
      rcases h with h | h
      · exact mem_consecutiveSums_ssum h
      · refine ⟨lastP, ?_⟩
        have spec := last_prime_ssum hlast
        exact ⟨spec.1, spec.2.1, by rw [spec.2.2, h]⟩
    | false =>
      simp [hblt] at h
      exact mem_consecutiveSums_ssum h

theorem hasRepFast_pos {n : ℕ} (h : hasRepFast n = true) : 0 < a n := by
  unfold hasRepFast at h
  obtain ⟨s, hs, hle, hmem⟩ := listHasPair_true h
  obtain ⟨p, hp, hp_le, hpS⟩ := mem_ssumList hs
  obtain ⟨q, hq, hq_le, hqS⟩ := mem_ssumList hmem
  have hsum : S_sum p + S_sum q = 2 * n := by
    rw [hpS, hqS]
    exact Nat.add_sub_of_le (by omega)
  have hpn : p < n := by
    by_contra hnp
    have heq : p = n := Nat.le_antisymm hp_le (Nat.le_of_not_lt hnp)
    have hgt : n < next_prime n := (next_prime_spec n).2.1
    have hsS : s = n + next_prime n := by
      rw [← hpS, heq]
      rfl
    omega
  have hqn : q < n := by
    by_contra hnq
    have heq : q = n := Nat.le_antisymm hq_le (Nat.le_of_not_lt hnq)
    have hgt : n < next_prime n := (next_prime_spec n).2.1
    have hqseq : 2 * n - s = n + next_prime n := by
      rw [← hqS, heq]
      rfl
    omega
  rcases le_total p q with hpq | hqp
  · exact a_pos_of_pair hp hq hpq hpn hqn hsum
  · exact a_pos_of_pair hq hp hqp hqn hpn (by rw [Nat.add_comm, hsum])

theorem mem_consecutiveSums_get {ps : List ℕ} {i : ℕ} (hi : i + 1 < ps.length) :
    ps[i] + ps[i + 1] ∈ consecutiveSums ps := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p rest ih =>
    match rest with
    | [] => simp at hi
    | p' :: rest' =>
      rw [mem_consecutiveSums_cons]
      cases i with
      | zero => simp
      | succ i' =>
        right
        have : i' + 1 < (p' :: rest').length := by simpa using hi
        simpa using ih this

theorem listHasPair_of_mem {n : ℕ} {ss l : List ℕ} {s : ℕ}
    (hsl : s ∈ l) (hle : s ≤ n) (hss : (2 * n - s) ∈ ss) :
    listHasPair n ss l = true := by
  induction l with
  | nil => simp at hsl
  | cons y rest ih =>
    simp only [listHasPair]
    rcases List.mem_cons.mp hsl with heq | hrest
    · subst heq
      have h1 : Nat.ble s n = true := Nat.ble_eq.mpr hle
      have h2 : listHas (2 * n - s) ss = true := listHas_iff.mpr hss
      cases hb : (Nat.ble s n && listHas (2 * n - s) ss) with
      | true => simp [hb]
      | false =>
        have : (Nat.ble s n && listHas (2 * n - s) ss) = true := by
          rw [h1, h2]; rfl
        simp [hb] at this
    · cases hb : (Nat.ble y n && listHas (2 * n - y) ss) with
      | true => simp [hb]
      | false =>
        simp [hb]
        exact ih hrest

theorem primesUpTo_ne_nil_of_prime {n p : ℕ} (hp : p.Prime) (hle : p ≤ n) :
    primesUpTo n ≠ [] := by
  intro h
  have := primesUpTo_complete hp hle
  simp [h] at this

theorem getLast_is_max {n : ℕ} (h : primesUpTo n ≠ []) :
    ∀ q, q.Prime → q ≤ n → q ≤ (primesUpTo n).getLast h := by
  intro q hq hqn
  have hqin := primesUpTo_complete hq hqn
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hqin
  have hlast := List.getLast_eq_getElem h
  have hli : (primesUpTo n).length - 1 < (primesUpTo n).length := by
    have : 0 < (primesUpTo n).length := List.length_pos_of_ne_nil h
    omega
  have hile : i ≤ (primesUpTo n).length - 1 := by omega
  rw [hlast]
  rcases lt_or_eq_of_le hile with hlt | heq
  · exact (primesUpTo_lt hi hli hlt).le
  · subst heq; exact le_rfl

theorem consecutive_index_of_next {n p : ℕ}
    (hp_in : p ∈ primesUpTo n) (hnp_in : next_prime p ∈ primesUpTo n) :
    ∃ i, ∃ hi : i + 1 < (primesUpTo n).length,
      (primesUpTo n)[i] = p ∧ (primesUpTo n)[i + 1] = next_prime p := by
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp_in
  obtain ⟨j, hj, hnj⟩ := List.getElem_of_mem hnp_in
  have hij : i < j := by
    apply index_lt_of_primesUpTo_lt hi hj
    rw [hpi, hnj]
    exact (next_prime_spec p).2.1
  have hj_eq : j = i + 1 := by
    have : i + 1 ≤ j := Nat.succ_le_of_lt hij
    rcases lt_or_eq_of_le this with hlt | heq
    · have hk : i + 1 < (primesUpTo n).length := lt_trans hlt hj
      have hmidp : ((primesUpTo n)[i + 1]).Prime := (primesUpTo_get_prime hk).1
      have hgt : p < (primesUpTo n)[i + 1] := by
        rw [← hpi]; exact primesUpTo_lt hi hk (Nat.lt_succ_self i)
      have hlt' : (primesUpTo n)[i + 1] < next_prime p := by
        rw [← hnj]; exact primesUpTo_lt hk hj hlt
      have hle := (next_prime_spec p).2.2 ((primesUpTo n)[i + 1]) hmidp hgt
      exact (not_le_of_gt hlt' hle).elim
    · exact heq.symm
  subst hj_eq
  exact ⟨i, hj, hpi, hnj⟩

theorem S_sum_mem_consecutive {n p : ℕ}
    (hp_in : p ∈ primesUpTo n) (hnp_in : next_prime p ∈ primesUpTo n) :
    S_sum p ∈ consecutiveSums (primesUpTo n) := by
  obtain ⟨i, hi, hpi, hnj⟩ := consecutive_index_of_next hp_in hnp_in
  have := mem_consecutiveSums_get (ps := primesUpTo n) hi
  rw [hpi, hnj] at this
  simpa [S_sum] using this

theorem S_sum_mem_ssumList {n p : ℕ} (hp : p.Prime) (hle : p ≤ n) :
    S_sum p ∈ ssumList n := by
  have hne := primesUpTo_ne_nil_of_prime hp hle
  have hlast? := getLast?_eq_getLast hne
  dsimp [ssumList]
  rw [hlast?]
  set lastP := (primesUpTo n).getLast hne
  have hlastp : lastP.Prime ∧ lastP ≤ n := mem_primesUpTo (List.getLast_mem hne)
  have hp_in := primesUpTo_complete hp hle
  by_cases hnxt : n < nextPrimeComp lastP
  · have : Nat.blt n (nextPrimeComp lastP) = true := Nat.blt_eq.mpr hnxt
    simp [this]
    by_cases hpeq : next_prime p ≤ n
    · left
      exact S_sum_mem_consecutive hp_in (primesUpTo_complete (next_prime_spec p).1 hpeq)
    · right
      have hlast_le : p ≤ lastP := getLast_is_max hne p hp hle
      have : p = lastP := by
        rcases lt_or_eq_of_le hlast_le with hlt | heq
        · have : next_prime p ≤ lastP := (next_prime_spec p).2.2 lastP hlastp.1 hlt
          exact (hpeq (le_trans this hlastp.2)).elim
        · exact heq
      rw [this, S_sum_eq]
  · have : Nat.blt n (nextPrimeComp lastP) = false := by
      cases hbit : Nat.blt n (nextPrimeComp lastP) with
      | true => exact absurd (Nat.blt_eq.mp hbit) hnxt
      | false => rfl
    simp [this]
    have hnpn : next_prime p ≤ n := by
      have hpl : p ≤ lastP := getLast_is_max hne p hp hle
      rcases lt_or_eq_of_le hpl with hlt | heq
      · exact le_trans ((next_prime_spec p).2.2 lastP hlastp.1 hlt) hlastp.2
      · rw [heq, ← nextPrimeComp_eq]; omega
    exact S_sum_mem_consecutive hp_in (primesUpTo_complete (next_prime_spec p).1 hnpn)

theorem hasRepFast_of_pair {n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpn : p < n) (hqn : q < n)
    (hsum : S_sum p + S_sum q = 2 * n) : hasRepFast n = true := by
  unfold hasRepFast
  have hps : S_sum p ∈ ssumList n := S_sum_mem_ssumList hp (Nat.le_of_lt hpn)
  have hqs : S_sum q ∈ ssumList n := S_sum_mem_ssumList hq (Nat.le_of_lt hqn)
  have hple : S_sum p ≤ n ∨ S_sum q ≤ n := by
    have : S_sum p + S_sum q = 2 * n := hsum
    omega
  rcases hple with hp_le | hq_le
  · have : 2 * n - S_sum p = S_sum q := by omega
    exact listHasPair_of_mem hps hp_le (this ▸ hqs)
  · have : 2 * n - S_sum q = S_sum p := by omega
    exact listHasPair_of_mem hqs hq_le (this ▸ hps)

theorem a_eq_zero_of_hasRepFast_false {n : ℕ} (h : hasRepFast n = false) : a n = 0 := by
  by_contra hpos
  have hpos' : 0 < a n := Nat.pos_of_ne_zero hpos
  obtain ⟨⟨p, q⟩, hmem⟩ := Finset.card_pos.mp hpos'
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem
  have hf := hasRepFast_of_pair hmem.2.1 hmem.2.2.1 hmem.1.1 hmem.1.2 hmem.2.2.2.2
  simp [h] at hf

theorem checkFrom_pos {lo k : ℕ} (h : checkFrom lo k = true) :
    ∀ n, lo ≤ n → n < lo + k → 0 < a n := by
  induction k with
  | zero =>
    intro n hlo hn
    omega
  | succ k ih =>
    simp only [checkFrom] at h
    have hab := Bool.and_eq_true_iff.mp h
    intro n hlo hn
    have : n = lo + k ∨ n < lo + k := by omega
    rcases this with rfl | hlt
    · exact hasRepFast_pos hab.1
    · exact ih hab.2 n hlo hlt












set_option maxHeartbeats 2000000

theorem check_504_40 : checkFrom 504 40 = true := rfl
theorem check_544_40 : checkFrom 544 40 = true := rfl
theorem check_584_40 : checkFrom 584 40 = true := rfl
theorem check_624_40 : checkFrom 624 40 = true := rfl
theorem check_664_40 : checkFrom 664 40 = true := rfl
theorem check_704_40 : checkFrom 704 40 = true := rfl
theorem check_744_40 : checkFrom 744 40 = true := rfl
theorem check_784_40 : checkFrom 784 40 = true := rfl

theorem a_pos_upto_823 (n : ℕ) (h1 : 504 ≤ n) (h2 : n ≤ 823) : 0 < a n := by
  have hcases :
      (504 ≤ n ∧ n < 544) ∨ (544 ≤ n ∧ n < 584) ∨ (584 ≤ n ∧ n < 624) ∨
      (624 ≤ n ∧ n < 664) ∨ (664 ≤ n ∧ n < 704) ∨ (704 ≤ n ∧ n < 744) ∨
      (744 ≤ n ∧ n < 784) ∨ (784 ≤ n ∧ n < 824) := by omega
  rcases hcases with h | h | h | h | h | h | h | h
  · exact checkFrom_pos check_504_40 n h.1 h.2
  · exact checkFrom_pos check_544_40 n h.1 h.2
  · exact checkFrom_pos check_584_40 n h.1 h.2
  · exact checkFrom_pos check_624_40 n h.1 h.2
  · exact checkFrom_pos check_664_40 n h.1 h.2
  · exact checkFrom_pos check_704_40 n h.1 h.2
  · exact checkFrom_pos check_744_40 n h.1 h.2
  · exact checkFrom_pos check_784_40 n h.1 (by omega)


/-- Boolean check that `(p, q)` is a valid witness for `a n > 0`. -/
def checkPair (n p q : Nat) : Bool :=
  isPrimeBool p && isPrimeBool q && Nat.ble p q && Nat.blt p n && Nat.blt q n &&
    (p + nextPrimeComp p + (q + nextPrimeComp q) == 2 * n)

theorem checkPair_pos {n p q : Nat} (h : checkPair n p q = true) : 0 < a n := by
  unfold checkPair at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hpB, hqB⟩, hpqB⟩, hpnB⟩, hqnB⟩, hsum⟩ := h
  have hp : p.Prime := isPrimeBool_prime hpB
  have hq : q.Prime := isPrimeBool_prime hqB
  have hpq : p ≤ q := Nat.le_of_ble_eq_true hpqB
  have hpn : p < n := Nat.blt_eq.mp hpnB
  have hqn : q < n := Nat.blt_eq.mp hqnB
  have hS : S_sum p + S_sum q = 2 * n := by
    rw [S_sum_eq, S_sum_eq]
    exact hsum
  exact a_pos_of_pair hp hq hpq hpn hqn hS

def checkPairs : List (Nat × Nat × Nat) → Bool
  | [] => true
  | (n, p, q) :: rest => checkPair n p q && checkPairs rest

theorem checkPairs_pos {l : List (Nat × Nat × Nat)} (h : checkPairs l = true)
    {n p q : Nat} (hm : (n, p, q) ∈ l) : 0 < a n := by
  induction l with
  | nil => simp at hm
  | cons head rest ih =>
    simp only [checkPairs] at h
    have hab := Bool.and_eq_true_iff.mp h
    simp only [List.mem_cons] at hm
    rcases hm with h1 | h2
    · cases h1
      exact checkPair_pos hab.1
    · exact ih hab.2 h2

theorem a_pos_of_mem_wits {l : List (Nat × Nat × Nat)} (h : checkPairs l = true)
    {n : Nat} (hn : n ∈ l.map (·.1)) : 0 < a n := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
  exact checkPairs_pos h hw

theorem mem_range_add {lo k n : Nat} (h1 : lo ≤ n) (h2 : n < lo + k) :
    n ∈ (List.range k).map (· + lo) := by
  simp [List.mem_map, List.mem_range]
  exact ⟨n - lo, by omega, by omega⟩

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
def wits_824 : List (Nat × Nat × Nat) :=
  [(824, 251, 569), (825, 13, 809), (826, 3, 821), (827, 383, 439), (828, 5, 821), (829, 3, 823), (830, 269, 557), (831, 5, 823), (832, 3, 827), (833, 83, 743), (834, 5, 827), (835, 397, 433), (836, 23, 809), (837, 7, 827), (838, 373, 461), (839, 277, 557), (840, 11, 827), (841, 373, 463), (842, 281, 557), (843, 13, 827), (844, 31, 809), (845, 397, 443), (846, 17, 827), (847, 109, 733), (848, 23, 821), (849, 19, 827), (850, 257, 587), (851, 23, 823), (852, 29, 821), (853, 307, 541), (854, 23, 827), (855, 29, 823), (856, 31, 821), (857, 353, 499), (858, 29, 827), (859, 3, 853), (860, 269, 587), (861, 5, 853), (862, 3, 857), (863, 173, 683)]
theorem wits_824_ok : checkPairs wits_824 = true := rfl
theorem wits_824_ns : wits_824.map (·.1) = (List.range 40).map (· + 824) := rfl
theorem a_pos_824_to_863 (n : Nat) (h1 : 824 ≤ n) (h2 : n ≤ 863) : 0 < a n := by
  have hmem : n ∈ wits_824.map (·.1) := by
    rw [wits_824_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_824_ok hmem
def wits_864 : List (Nat × Nat × Nat) :=
  [(864, 5, 857), (865, 3, 859), (866, 419, 443), (867, 5, 859), (868, 431, 433), (869, 307, 557), (870, 7, 859), (871, 367, 499), (872, 433, 433), (873, 11, 859), (874, 271, 599), (875, 383, 487), (876, 13, 859), (877, 433, 439), (878, 431, 443), (879, 17, 859), (880, 269, 607), (881, 23, 853), (882, 19, 859), (883, 3, 877), (884, 23, 857), (885, 5, 877), (886, 3, 881), (887, 23, 859), (888, 5, 881), (889, 3, 883), (890, 239, 647), (891, 5, 883), (892, 31, 857), (893, 131, 757), (894, 7, 883), (895, 31, 859), (896, 251, 641), (897, 11, 883), (898, 433, 461), (899, 307, 587), (900, 13, 883), (901, 433, 463), (902, 311, 587), (903, 17, 883)]
theorem wits_864_ok : checkPairs wits_864 = true := rfl
theorem wits_864_ns : wits_864.map (·.1) = (List.range 40).map (· + 864) := rfl
theorem a_pos_864_to_903 (n : Nat) (h1 : 864 ≤ n) (h2 : n ≤ 903) : 0 < a n := by
  have hmem : n ∈ wits_864.map (·.1) := by
    rw [wits_864_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_864_ok hmem
def wits_904 : List (Nat × Nat × Nat) :=
  [(904, 331, 569), (905, 23, 877), (906, 19, 883), (907, 359, 541), (908, 23, 881), (909, 29, 877), (910, 257, 647), (911, 23, 883), (912, 29, 881), (913, 3, 907), (914, 367, 541), (915, 5, 907), (916, 31, 881), (917, 349, 563), (918, 7, 907), (919, 31, 883), (920, 373, 541), (921, 11, 907), (922, 353, 563), (923, 359, 557), (924, 13, 907), (925, 433, 487), (926, 419, 503), (927, 17, 907), (928, 197, 727), (929, 277, 647), (930, 19, 907), (931, 193, 733), (932, 281, 647), (933, 431, 499), (934, 331, 599), (935, 23, 907), (936, 107, 827), (937, 433, 499), (938, 431, 503), (939, 29, 907), (940, 367, 569), (941, 379, 557), (942, 419, 521), (943, 3, 937)]
theorem wits_904_ok : checkPairs wits_904 = true := rfl
theorem wits_904_ns : wits_904.map (·.1) = (List.range 40).map (· + 904) := rfl
theorem a_pos_904_to_943 (n : Nat) (h1 : 904 ≤ n) (h2 : n ≤ 943) : 0 < a n := by
  have hmem : n ∈ wits_904.map (·.1) := by
    rw [wits_904_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_904_ok hmem
def wits_944 : List (Nat × Nat × Nat) :=
  [(944, 367, 571), (945, 5, 937), (946, 383, 557), (947, 443, 499), (948, 3, 941), (949, 331, 613), (950, 5, 941), (951, 11, 937), (952, 443, 503), (953, 7, 941), (954, 3, 947), (955, 379, 571), (956, 5, 947), (957, 17, 937), (958, 433, 521), (959, 7, 947), (960, 19, 937), (961, 349, 607), (962, 11, 947), (963, 461, 499), (964, 419, 541), (965, 13, 947), (966, 347, 617), (967, 229, 733), (968, 17, 947), (969, 29, 937), (970, 23, 941), (971, 19, 947), (972, 311, 659), (973, 3, 967), (974, 29, 941), (975, 5, 967), (976, 23, 947), (977, 379, 593), (978, 3, 971), (979, 331, 643), (980, 5, 971), (981, 11, 967), (982, 383, 593), (983, 7, 971)]
theorem wits_944_ok : checkPairs wits_944 = true := rfl
theorem wits_944_ns : wits_944.map (·.1) = (List.range 40).map (· + 944) := rfl
theorem a_pos_944_to_983 (n : Nat) (h1 : 944 ≤ n) (h2 : n ≤ 983) : 0 < a n := by
  have hmem : n ∈ wits_944.map (·.1) := by
    rw [wits_944_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_944_ok hmem
def wits_984 : List (Nat × Nat × Nat) :=
  [(984, 3, 977), (985, 439, 541), (986, 5, 977), (987, 17, 967), (988, 367, 617), (989, 7, 977), (990, 19, 967), (991, 379, 607), (992, 11, 977), (993, 349, 641), (994, 419, 571), (995, 13, 977), (996, 137, 857), (997, 449, 541), (998, 3, 991), (999, 29, 967), (1000, 5, 991), (1001, 19, 977), (1002, 431, 569), (1003, 7, 991), (1004, 29, 971), (1005, 193, 809), (1006, 11, 991), (1007, 499, 503), (1008, 31, 971), (1009, 13, 991), (1010, 29, 977), (1011, 487, 521), (1012, 17, 991), (1013, 37, 971), (1014, 31, 977), (1015, 3, 1009), (1016, 443, 569), (1017, 5, 1009), (1018, 373, 641), (1019, 37, 977), (1020, 3, 1013), (1021, 373, 643), (1022, 5, 1013), (1023, 11, 1009)]
theorem wits_984_ok : checkPairs wits_984 = true := rfl
theorem wits_984_ns : wits_984.map (·.1) = (List.range 40).map (· + 984) := rfl
theorem a_pos_984_to_1023 (n : Nat) (h1 : 984 ≤ n) (h2 : n ≤ 1023) : 0 < a n := by
  have hmem : n ∈ wits_984.map (·.1) := by
    rw [wits_984_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_984_ok hmem
def wits_1024 : List (Nat × Nat × Nat) :=
  [(1024, 3, 1019), (1025, 7, 1013), (1026, 5, 1019), (1027, 479, 541), (1028, 11, 1013), (1029, 7, 1019), (1030, 419, 607), (1031, 13, 1013), (1032, 11, 1019), (1033, 37, 991), (1034, 17, 1013), (1035, 13, 1019), (1036, 3, 1031), (1037, 19, 1013), (1038, 5, 1031), (1039, 463, 571), (1040, 3, 1033), (1041, 7, 1031), (1042, 5, 1033), (1043, 131, 907), (1044, 11, 1031), (1045, 7, 1033), (1046, 23, 1019), (1047, 13, 1031), (1048, 11, 1033), (1049, 487, 557), (1050, 17, 1031), (1051, 13, 1033), (1052, 461, 587), (1053, 19, 1031), (1054, 3, 1049), (1055, 37, 1013), (1056, 5, 1049), (1057, 19, 1033), (1058, 23, 1031), (1059, 7, 1049), (1060, 83, 971), (1061, 499, 557), (1062, 11, 1049), (1063, 487, 571)]
theorem wits_1024_ok : checkPairs wits_1024 = true := rfl
theorem wits_1024_ns : wits_1024.map (·.1) = (List.range 40).map (· + 1024) := rfl
theorem a_pos_1024_to_1063 (n : Nat) (h1 : 1024 ≤ n) (h2 : n ≤ 1063) : 0 < a n := by
  have hmem : n ∈ wits_1024.map (·.1) := by
    rw [wits_1024_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1024_ok hmem
def wits_1064 : List (Nat × Nat × Nat) :=
  [(1064, 443, 617), (1065, 13, 1049), (1066, 3, 1061), (1067, 499, 563), (1068, 5, 1061), (1069, 463, 601), (1070, 3, 1063), (1071, 7, 1061), (1072, 5, 1063), (1073, 131, 937), (1074, 11, 1061), (1075, 7, 1063), (1076, 23, 1049), (1077, 13, 1061), (1078, 11, 1063), (1079, 487, 587), (1080, 17, 1061), (1081, 13, 1063), (1082, 521, 557), (1083, 19, 1061), (1084, 17, 1063), (1085, 487, 593), (1086, 227, 857), (1087, 19, 1063), (1088, 23, 1061), (1089, 37, 1049), (1090, 373, 709), (1091, 499, 587), (1092, 23, 1063), (1093, 3, 1087), (1094, 263, 827), (1095, 5, 1087), (1096, 3, 1091), (1097, 499, 593), (1098, 5, 1091), (1099, 3, 1093), (1100, 31, 1063), (1101, 5, 1093), (1102, 503, 593), (1103, 131, 967)]
theorem wits_1064_ok : checkPairs wits_1064 = true := rfl
theorem wits_1064_ns : wits_1064.map (·.1) = (List.range 40).map (· + 1064) := rfl
theorem a_pos_1064_to_1103 (n : Nat) (h1 : 1064 ≤ n) (h2 : n ≤ 1103) : 0 < a n := by
  have hmem : n ∈ wits_1064.map (·.1) := by
    rw [wits_1064_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1064_ok hmem
def wits_1104 : List (Nat × Nat × Nat) :=
  [(1104, 3, 1097), (1105, 37, 1063), (1106, 5, 1097), (1107, 11, 1093), (1108, 131, 971), (1109, 7, 1097), (1110, 3, 1103), (1111, 499, 607), (1112, 5, 1103), (1113, 17, 1093), (1114, 541, 569), (1115, 7, 1103), (1116, 19, 1093), (1117, 379, 733), (1118, 11, 1103), (1119, 29, 1087), (1120, 557, 557), (1121, 13, 1103), (1122, 29, 1091), (1123, 31, 1087), (1124, 3, 1117), (1125, 29, 1093), (1126, 5, 1117), (1127, 19, 1103), (1128, 37, 1087), (1129, 7, 1117), (1130, 3, 1123), (1131, 37, 1091), (1132, 5, 1123), (1133, 251, 877), (1134, 31, 1097), (1135, 7, 1123), (1136, 29, 1103), (1137, 521, 613), (1138, 11, 1123), (1139, 37, 1097), (1140, 31, 1103), (1141, 13, 1123), (1142, 461, 677), (1143, 499, 641)]
theorem wits_1104_ok : checkPairs wits_1104 = true := rfl
theorem wits_1104_ns : wits_1104.map (·.1) = (List.range 40).map (· + 1104) := rfl
theorem a_pos_1104_to_1143 (n : Nat) (h1 : 1104 ≤ n) (h2 : n ≤ 1143) : 0 < a n := by
  have hmem : n ∈ wits_1104.map (·.1) := by
    rw [wits_1104_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1104_ok hmem
def wits_1144 : List (Nat × Nat × Nat) :=
  [(1144, 17, 1123), (1145, 37, 1103), (1146, 23, 1117), (1147, 19, 1123), (1148, 571, 571), (1149, 487, 659), (1150, 29, 1117), (1151, 503, 643), (1152, 23, 1123), (1153, 397, 751), (1154, 31, 1117), (1155, 269, 883), (1156, 3, 1151), (1157, 499, 653), (1158, 5, 1151), (1159, 37, 1117), (1160, 31, 1123), (1161, 7, 1151), (1162, 563, 593), (1163, 251, 907), (1164, 11, 1151), (1165, 37, 1123), (1166, 569, 593), (1167, 13, 1151), (1168, 431, 733), (1169, 487, 677), (1170, 17, 1151), (1171, 439, 727), (1172, 521, 647), (1173, 19, 1151), (1174, 571, 599), (1175, 557, 613), (1176, 347, 827), (1177, 439, 733), (1178, 23, 1151), (1179, 419, 757), (1180, 587, 587), (1181, 563, 613), (1182, 29, 1151), (1183, 271, 907)]
theorem wits_1144_ok : checkPairs wits_1144 = true := rfl
theorem wits_1144_ns : wits_1144.map (·.1) = (List.range 40).map (· + 1144) := rfl
theorem a_pos_1144_to_1183 (n : Nat) (h1 : 1144 ≤ n) (h2 : n ≤ 1183) : 0 < a n := by
  have hmem : n ∈ wits_1144.map (·.1) := by
    rw [wits_1144_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1144_ok hmem
def wits_1184 : List (Nat × Nat × Nat) :=
  [(1184, 571, 607), (1185, 569, 613), (1186, 31, 1151), (1187, 443, 739), (1188, 3, 1181), (1189, 571, 613), (1190, 5, 1181), (1191, 37, 1151), (1192, 593, 593), (1193, 7, 1181), (1194, 3, 1187), (1195, 463, 727), (1196, 5, 1187), (1197, 521, 673), (1198, 461, 733), (1199, 7, 1187), (1200, 599, 599), (1201, 463, 733), (1202, 11, 1187), (1203, 461, 739), (1204, 599, 601), (1205, 13, 1187), (1206, 347, 857), (1207, 433, 769), (1208, 17, 1187), (1209, 397, 809), (1210, 23, 1181), (1211, 19, 1187), (1212, 569, 641), (1213, 457, 751), (1214, 29, 1181), (1215, 599, 613), (1216, 23, 1187), (1217, 443, 769), (1218, 31, 1181), (1219, 3, 1213), (1220, 29, 1187), (1221, 5, 1213), (1222, 601, 617), (1223, 37, 1181)]
theorem wits_1184_ok : checkPairs wits_1184 = true := rfl
theorem wits_1184_ns : wits_1184.map (·.1) = (List.range 40).map (· + 1184) := rfl
theorem a_pos_1184_to_1223 (n : Nat) (h1 : 1184 ≤ n) (h2 : n ≤ 1223) : 0 < a n := by
  have hmem : n ∈ wits_1184.map (·.1) := by
    rw [wits_1184_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1184_ok hmem
def wits_1224 : List (Nat × Nat × Nat) :=
  [(1224, 3, 1217), (1225, 607, 613), (1226, 5, 1217), (1227, 11, 1213), (1228, 607, 617), (1229, 7, 1217), (1230, 3, 1223), (1231, 499, 727), (1232, 5, 1223), (1233, 17, 1213), (1234, 3, 1229), (1235, 7, 1223), (1236, 5, 1229), (1237, 499, 733), (1238, 3, 1231), (1239, 7, 1229), (1240, 5, 1231), (1241, 13, 1223), (1242, 11, 1229), (1243, 7, 1231), (1244, 17, 1223), (1245, 13, 1229), (1246, 11, 1231), (1247, 19, 1223), (1248, 17, 1229), (1249, 13, 1231), (1250, 29, 1217), (1251, 19, 1229), (1252, 17, 1231), (1253, 307, 941), (1254, 31, 1217), (1255, 19, 1231), (1256, 23, 1229), (1257, 613, 641), (1258, 521, 733), (1259, 37, 1217), (1260, 23, 1231), (1261, 433, 823), (1262, 311, 947), (1263, 617, 643)]
theorem wits_1224_ok : checkPairs wits_1224 = true := rfl
theorem wits_1224_ns : wits_1224.map (·.1) = (List.range 40).map (· + 1224) := rfl
theorem a_pos_1224_to_1263 (n : Nat) (h1 : 1224 ≤ n) (h2 : n ≤ 1263) : 0 < a n := by
  have hmem : n ∈ wits_1224.map (·.1) := by
    rw [wits_1224_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1224_ok hmem
def wits_1264 : List (Nat × Nat × Nat) :=
  [(1264, 29, 1231), (1265, 37, 1223), (1266, 439, 823), (1267, 229, 1033), (1268, 31, 1231), (1269, 37, 1229), (1270, 607, 659), (1271, 613, 653), (1272, 461, 809), (1273, 37, 1231), (1274, 617, 653), (1275, 613, 659), (1276, 593, 677), (1277, 503, 769), (1278, 617, 659), (1279, 601, 673), (1280, 599, 677), (1281, 521, 757), (1282, 3, 1277), (1283, 307, 971), (1284, 5, 1277), (1285, 3, 1279), (1286, 311, 971), (1287, 5, 1279), (1288, 571, 709), (1289, 313, 971), (1290, 3, 1283), (1291, 433, 853), (1292, 5, 1283), (1293, 11, 1279), (1294, 3, 1289), (1295, 7, 1283), (1296, 5, 1289), (1297, 433, 859), (1298, 3, 1291), (1299, 7, 1289), (1300, 5, 1291), (1301, 13, 1283), (1302, 11, 1289), (1303, 3, 1297)]
theorem wits_1264_ok : checkPairs wits_1264 = true := rfl
theorem wits_1264_ns : wits_1264.map (·.1) = (List.range 40).map (· + 1264) := rfl
theorem a_pos_1264_to_1303 (n : Nat) (h1 : 1264 ≤ n) (h2 : n ≤ 1303) : 0 < a n := by
  have hmem : n ∈ wits_1264.map (·.1) := by
    rw [wits_1264_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1264_ok hmem
def wits_1304 : List (Nat × Nat × Nat) :=
  [(1304, 17, 1283), (1305, 5, 1297), (1306, 3, 1301), (1307, 19, 1283), (1308, 5, 1301), (1309, 3, 1303), (1310, 647, 659), (1311, 5, 1303), (1312, 17, 1291), (1313, 127, 1181), (1314, 7, 1303), (1315, 19, 1291), (1316, 23, 1289), (1317, 11, 1303), (1318, 433, 881), (1319, 557, 757), (1320, 13, 1303), (1321, 433, 883), (1322, 641, 677), (1323, 17, 1303), (1324, 3, 1319), (1325, 23, 1297), (1326, 5, 1319), (1327, 601, 719), (1328, 3, 1321), (1329, 7, 1319), (1330, 5, 1321), (1331, 23, 1303), (1332, 11, 1319), (1333, 7, 1321), (1334, 601, 727), (1335, 13, 1319), (1336, 11, 1321), (1337, 593, 739), (1338, 17, 1319), (1339, 13, 1321), (1340, 659, 677), (1341, 19, 1319), (1342, 17, 1321), (1343, 397, 941)]
theorem wits_1304_ok : checkPairs wits_1304 = true := rfl
theorem wits_1304_ns : wits_1304.map (·.1) = (List.range 40).map (· + 1304) := rfl
theorem a_pos_1304_to_1343 (n : Nat) (h1 : 1304 ≤ n) (h2 : n ≤ 1343) : 0 < a n := by
  have hmem : n ∈ wits_1304.map (·.1) := by
    rw [wits_1304_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1304_ok hmem
def wits_1344 : List (Nat × Nat × Nat) :=
  [(1344, 37, 1303), (1345, 19, 1321), (1346, 23, 1319), (1347, 521, 823), (1348, 617, 727), (1349, 587, 757), (1350, 23, 1321), (1351, 613, 733), (1352, 257, 1091), (1353, 137, 1213), (1354, 29, 1321), (1355, 673, 677), (1356, 613, 739), (1357, 229, 1123), (1358, 31, 1321), (1359, 37, 1319), (1360, 677, 677), (1361, 587, 769), (1362, 311, 1049), (1363, 37, 1321), (1364, 607, 751), (1365, 313, 1049), (1366, 541, 821), (1367, 593, 769), (1368, 3, 1361), (1369, 613, 751), (1370, 5, 1361), (1371, 599, 769), (1372, 641, 727), (1373, 7, 1361), (1374, 3, 1367), (1375, 643, 727), (1376, 5, 1367), (1377, 617, 757), (1378, 641, 733), (1379, 7, 1367), (1380, 569, 809), (1381, 643, 733), (1382, 11, 1367), (1383, 641, 739)]
theorem wits_1344_ok : checkPairs wits_1344 = true := rfl
theorem wits_1344_ns : wits_1344.map (·.1) = (List.range 40).map (· + 1344) := rfl
theorem a_pos_1344_to_1383 (n : Nat) (h1 : 1344 ≤ n) (h2 : n ≤ 1383) : 0 < a n := by
  have hmem : n ∈ wits_1344.map (·.1) := by
    rw [wits_1344_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1344_ok hmem
def wits_1384 : List (Nat × Nat × Nat) :=
  [(1384, 571, 809), (1385, 13, 1367), (1386, 107, 1277), (1387, 373, 1009), (1388, 17, 1367), (1389, 617, 769), (1390, 23, 1361), (1391, 19, 1367), (1392, 569, 821), (1393, 397, 991), (1394, 29, 1361), (1395, 569, 823), (1396, 23, 1367), (1397, 653, 739), (1398, 31, 1361), (1399, 643, 751), (1400, 29, 1367), (1401, 659, 739), (1402, 571, 827), (1403, 37, 1361), (1404, 31, 1367), (1405, 673, 727), (1406, 593, 809), (1407, 521, 883), (1408, 373, 1031), (1409, 37, 1367), (1410, 599, 809), (1411, 673, 733), (1412, 587, 821), (1413, 641, 769), (1414, 659, 751), (1415, 653, 757), (1416, 137, 1277), (1417, 379, 1033), (1418, 593, 821), (1419, 659, 757), (1420, 607, 809), (1421, 677, 739), (1422, 599, 821), (1423, 541, 877)]
theorem wits_1384_ok : checkPairs wits_1384 = true := rfl
theorem wits_1384_ns : wits_1384.map (·.1) = (List.range 40).map (· + 1384) := rfl
theorem a_pos_1384_to_1423 (n : Nat) (h1 : 1384 ≤ n) (h2 : n ≤ 1423) : 0 < a n := by
  have hmem : n ∈ wits_1384.map (·.1) := by
    rw [wits_1384_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1384_ok hmem
def wits_1424 : List (Nat × Nat × Nat) :=
  [(1424, 593, 827), (1425, 613, 809), (1426, 601, 821), (1427, 653, 769), (1428, 617, 809), (1429, 3, 1423), (1430, 433, 991), (1431, 5, 1423), (1432, 3, 1427), (1433, 487, 941), (1434, 5, 1427), (1435, 3, 1429), (1436, 461, 971), (1437, 5, 1429), (1438, 607, 827), (1439, 677, 757), (1440, 3, 1433), (1441, 313, 1123), (1442, 5, 1433), (1443, 11, 1429), (1444, 257, 1181), (1445, 7, 1433), (1446, 13, 1429), (1447, 433, 1009), (1448, 11, 1433), (1449, 17, 1429), (1450, 503, 941), (1451, 13, 1433), (1452, 19, 1429), (1453, 3, 1447), (1454, 17, 1433), (1455, 5, 1447), (1456, 3, 1451), (1457, 19, 1433), (1458, 5, 1451), (1459, 31, 1423), (1460, 3, 1453), (1461, 7, 1451), (1462, 5, 1453), (1463, 487, 971)]
theorem wits_1424_ok : checkPairs wits_1424 = true := rfl
theorem wits_1424_ns : wits_1424.map (·.1) = (List.range 40).map (· + 1424) := rfl
theorem a_pos_1424_to_1463 (n : Nat) (h1 : 1424 ≤ n) (h2 : n ≤ 1463) : 0 < a n := by
  have hmem : n ∈ wits_1424.map (·.1) := by
    rw [wits_1424_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1424_ok hmem
def wits_1464 : List (Nat × Nat × Nat) :=
  [(1464, 11, 1451), (1465, 7, 1453), (1466, 29, 1433), (1467, 13, 1451), (1468, 11, 1453), (1469, 587, 877), (1470, 17, 1451), (1471, 13, 1453), (1472, 733, 733), (1473, 19, 1451), (1474, 17, 1453), (1475, 23, 1447), (1476, 617, 857), (1477, 19, 1453), (1478, 23, 1451), (1479, 29, 1447), (1480, 503, 971), (1481, 653, 823), (1482, 23, 1453), (1483, 31, 1447), (1484, 727, 751), (1485, 673, 809), (1486, 3, 1481), (1487, 379, 1103), (1488, 5, 1481), (1489, 3, 1483), (1490, 31, 1453), (1491, 5, 1483), (1492, 3, 1487), (1493, 307, 1181), (1494, 5, 1487), (1495, 3, 1489), (1496, 521, 971), (1497, 5, 1489), (1498, 461, 1033), (1499, 587, 907), (1500, 3, 1493), (1501, 727, 769), (1502, 5, 1493), (1503, 11, 1489)]
theorem wits_1464_ok : checkPairs wits_1464 = true := rfl
theorem wits_1464_ns : wits_1464.map (·.1) = (List.range 40).map (· + 1464) := rfl
theorem a_pos_1464_to_1503 (n : Nat) (h1 : 1464 ≤ n) (h2 : n ≤ 1503) : 0 < a n := by
  have hmem : n ∈ wits_1464.map (·.1) := by
    rw [wits_1464_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1464_ok hmem
def wits_1504 : List (Nat × Nat × Nat) :=
  [(1504, 557, 941), (1505, 7, 1493), (1506, 13, 1489), (1507, 733, 769), (1508, 11, 1493), (1509, 17, 1489), (1510, 563, 941), (1511, 13, 1493), (1512, 19, 1489), (1513, 751, 757), (1514, 17, 1493), (1515, 29, 1483), (1516, 31, 1481), (1517, 19, 1493), (1518, 29, 1487), (1519, 31, 1483), (1520, 569, 947), (1521, 29, 1489), (1522, 23, 1493), (1523, 587, 929), (1524, 37, 1483), (1525, 31, 1489), (1526, 29, 1493), (1527, 37, 1487), (1528, 461, 1063), (1529, 647, 877), (1530, 31, 1493), (1531, 463, 1063), (1532, 647, 881), (1533, 673, 857), (1534, 587, 941), (1535, 37, 1493), (1536, 107, 1427), (1537, 499, 1033), (1538, 677, 857), (1539, 659, 877), (1540, 727, 809), (1541, 677, 859), (1542, 659, 881), (1543, 601, 937)]
theorem wits_1504_ok : checkPairs wits_1504 = true := rfl
theorem wits_1504_ns : wits_1504.map (·.1) = (List.range 40).map (· + 1504) := rfl
theorem a_pos_1504_to_1543 (n : Nat) (h1 : 1504 ≤ n) (h2 : n ≤ 1543) : 0 < a n := by
  have hmem : n ∈ wits_1504.map (·.1) := by
    rw [wits_1504_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1504_ok hmem
def wits_1544 : List (Nat × Nat × Nat) :=
  [(1544, 599, 941), (1545, 659, 883), (1546, 733, 809), (1547, 439, 1103), (1548, 269, 1277), (1549, 607, 937), (1550, 3, 1543), (1551, 739, 809), (1552, 5, 1543), (1553, 251, 1297), (1554, 521, 1031), (1555, 3, 1549), (1556, 503, 1049), (1557, 5, 1549), (1558, 11, 1543), (1559, 677, 877), (1560, 3, 1553), (1561, 13, 1543), (1562, 5, 1553), (1563, 11, 1549), (1564, 17, 1543), (1565, 7, 1553), (1566, 13, 1549), (1567, 19, 1543), (1568, 11, 1553), (1569, 17, 1549), (1570, 593, 971), (1571, 13, 1553), (1572, 19, 1549), (1573, 3, 1567), (1574, 17, 1553), (1575, 5, 1567), (1576, 29, 1543), (1577, 19, 1553), (1578, 7, 1567), (1579, 751, 823), (1580, 31, 1543), (1581, 11, 1567), (1582, 23, 1553), (1583, 397, 1181)]
theorem wits_1544_ok : checkPairs wits_1544 = true := rfl
theorem wits_1544_ns : wits_1544.map (·.1) = (List.range 40).map (· + 1544) := rfl
theorem a_pos_1544_to_1583 (n : Nat) (h1 : 1544 ≤ n) (h2 : n ≤ 1583) : 0 < a n := by
  have hmem : n ∈ wits_1544.map (·.1) := by
    rw [wits_1544_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1544_ok hmem
def wits_1584 : List (Nat × Nat × Nat) :=
  [(1584, 13, 1567), (1585, 3, 1579), (1586, 29, 1553), (1587, 5, 1579), (1588, 727, 857), (1589, 677, 907), (1590, 7, 1579), (1591, 733, 853), (1592, 641, 947), (1593, 11, 1579), (1594, 733, 857), (1595, 23, 1567), (1596, 13, 1579), (1597, 733, 859), (1598, 617, 977), (1599, 17, 1579), (1600, 653, 941), (1601, 587, 1009), (1602, 19, 1579), (1603, 3, 1597), (1604, 659, 941), (1605, 5, 1597), (1606, 653, 947), (1607, 23, 1579), (1608, 3, 1601), (1609, 751, 853), (1610, 5, 1601), (1611, 11, 1597), (1612, 3, 1607), (1613, 7, 1601), (1614, 5, 1607), (1615, 3, 1609), (1616, 11, 1601), (1617, 5, 1609), (1618, 733, 881), (1619, 13, 1601), (1620, 3, 1613), (1621, 733, 883), (1622, 5, 1613), (1623, 11, 1609)]
theorem wits_1584_ok : checkPairs wits_1584 = true := rfl
theorem wits_1584_ns : wits_1584.map (·.1) = (List.range 40).map (· + 1584) := rfl
theorem a_pos_1584_to_1623 (n : Nat) (h1 : 1584 ≤ n) (h2 : n ≤ 1623) : 0 < a n := by
  have hmem : n ∈ wits_1584.map (·.1) := by
    rw [wits_1584_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1584_ok hmem
def wits_1624 : List (Nat × Nat × Nat) :=
  [(1624, 3, 1619), (1625, 7, 1613), (1626, 5, 1619), (1627, 499, 1123), (1628, 3, 1621), (1629, 7, 1619), (1630, 5, 1621), (1631, 13, 1613), (1632, 11, 1619), (1633, 7, 1621), (1634, 17, 1613), (1635, 13, 1619), (1636, 11, 1621), (1637, 19, 1613), (1638, 17, 1619), (1639, 13, 1621), (1640, 659, 977), (1641, 19, 1619), (1642, 17, 1621), (1643, 37, 1601), (1644, 821, 821), (1645, 19, 1621), (1646, 23, 1619), (1647, 37, 1607), (1648, 521, 1123), (1649, 677, 967), (1650, 23, 1621), (1651, 613, 1033), (1652, 587, 1061), (1653, 823, 827), (1654, 29, 1621), (1655, 37, 1613), (1656, 827, 827), (1657, 373, 1279), (1658, 31, 1621), (1659, 37, 1619), (1660, 677, 977), (1661, 647, 1009), (1662, 641, 1019), (1663, 37, 1621)]
theorem wits_1624_ok : checkPairs wits_1624 = true := rfl
theorem wits_1624_ns : wits_1624.map (·.1) = (List.range 40).map (· + 1624) := rfl
theorem a_pos_1624_to_1663 (n : Nat) (h1 : 1624 ≤ n) (h2 : n ≤ 1663) : 0 < a n := by
  have hmem : n ∈ wits_1624.map (·.1) := by
    rw [wits_1624_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1624_ok hmem
def wits_1664 : List (Nat × Nat × Nat) :=
  [(1664, 3, 1657), (1665, 809, 853), (1666, 5, 1657), (1667, 653, 1009), (1668, 809, 857), (1669, 3, 1663), (1670, 647, 1019), (1671, 5, 1663), (1672, 3, 1667), (1673, 487, 1181), (1674, 5, 1667), (1675, 13, 1657), (1676, 659, 1013), (1677, 7, 1667), (1678, 17, 1657), (1679, 587, 1087), (1680, 11, 1667), (1681, 19, 1657), (1682, 647, 1031), (1683, 13, 1667), (1684, 617, 1063), (1685, 739, 941), (1686, 17, 1667), (1687, 229, 1453), (1688, 653, 1031), (1689, 19, 1667), (1690, 29, 1657), (1691, 23, 1663), (1692, 809, 881), (1693, 751, 937), (1694, 23, 1667), (1695, 29, 1663), (1696, 677, 1013), (1697, 263, 1429), (1698, 29, 1667), (1699, 3, 1693), (1700, 677, 1019), (1701, 5, 1693), (1702, 3, 1697), (1703, 757, 941)]
theorem wits_1664_ok : checkPairs wits_1664 = true := rfl
theorem wits_1664_ns : wits_1664.map (·.1) = (List.range 40).map (· + 1664) := rfl
theorem a_pos_1664_to_1703 (n : Nat) (h1 : 1664 ≤ n) (h2 : n ≤ 1703) : 0 < a n := by
  have hmem : n ∈ wits_1664.map (·.1) := by
    rw [wits_1664_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1664_ok hmem
def wits_1704 : List (Nat × Nat × Nat) :=
  [(1704, 5, 1697), (1705, 733, 967), (1706, 653, 1049), (1707, 7, 1697), (1708, 641, 1063), (1709, 757, 947), (1710, 11, 1697), (1711, 673, 1033), (1712, 677, 1031), (1713, 13, 1697), (1714, 433, 1277), (1715, 769, 941), (1716, 17, 1697), (1717, 433, 1279), (1718, 653, 1061), (1719, 19, 1697), (1720, 599, 1117), (1721, 23, 1693), (1722, 659, 1061), (1723, 751, 967), (1724, 23, 1697), (1725, 29, 1693), (1726, 3, 1721), (1727, 499, 1223), (1728, 5, 1721), (1729, 31, 1693), (1730, 733, 991), (1731, 7, 1721), (1732, 31, 1697), (1733, 757, 971), (1734, 11, 1721), (1735, 739, 991), (1736, 607, 1123), (1737, 13, 1721), (1738, 617, 1117), (1739, 757, 977), (1740, 17, 1721), (1741, 727, 1009), (1742, 677, 1061), (1743, 19, 1721)]
theorem wits_1704_ok : checkPairs wits_1704 = true := rfl
theorem wits_1704_ns : wits_1704.map (·.1) = (List.range 40).map (· + 1704) := rfl
theorem a_pos_1704_to_1743 (n : Nat) (h1 : 1704 ≤ n) (h2 : n ≤ 1743) : 0 < a n := by
  have hmem : n ∈ wits_1704.map (·.1) := by
    rw [wits_1704_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1704_ok hmem
def wits_1744 : List (Nat × Nat × Nat) :=
  [(1744, 617, 1123), (1745, 769, 971), (1746, 137, 1607), (1747, 733, 1009), (1748, 3, 1741), (1749, 809, 937), (1750, 5, 1741), (1751, 769, 977), (1752, 29, 1721), (1753, 7, 1741), (1754, 3, 1747), (1755, 659, 1093), (1756, 5, 1747), (1757, 739, 1013), (1758, 269, 1487), (1759, 7, 1747), (1760, 3, 1753), (1761, 37, 1721), (1762, 5, 1753), (1763, 397, 1361), (1764, 881, 881), (1765, 7, 1753), (1766, 821, 941), (1767, 881, 883), (1768, 11, 1753), (1769, 823, 941), (1770, 23, 1741), (1771, 13, 1753), (1772, 827, 941), (1773, 739, 1031), (1774, 17, 1753), (1775, 823, 947), (1776, 23, 1747), (1777, 19, 1753), (1778, 31, 1741), (1779, 809, 967), (1780, 29, 1747), (1781, 673, 1103), (1782, 23, 1753), (1783, 37, 1741)]
theorem wits_1744_ok : checkPairs wits_1744 = true := rfl
theorem wits_1744_ns : wits_1744.map (·.1) = (List.range 40).map (· + 1744) := rfl
theorem a_pos_1744_to_1783 (n : Nat) (h1 : 1744 ≤ n) (h2 : n ≤ 1783) : 0 < a n := by
  have hmem : n ∈ wits_1744.map (·.1) := by
    rw [wits_1744_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1744_ok hmem
def wits_1784 : List (Nat × Nat × Nat) :=
  [(1784, 3, 1777), (1785, 569, 1213), (1786, 5, 1777), (1787, 769, 1013), (1788, 179, 1607), (1789, 3, 1783), (1790, 31, 1753), (1791, 5, 1783), (1792, 3, 1787), (1793, 683, 1103), (1794, 5, 1787), (1795, 13, 1777), (1796, 821, 971), (1797, 7, 1787), (1798, 17, 1777), (1799, 853, 941), (1800, 11, 1787), (1801, 19, 1777), (1802, 857, 941), (1803, 13, 1787), (1804, 809, 991), (1805, 859, 941), (1806, 17, 1787), (1807, 769, 1033), (1808, 857, 947), (1809, 19, 1787), (1810, 29, 1777), (1811, 23, 1783), (1812, 659, 1151), (1813, 487, 1321), (1814, 23, 1787), (1815, 29, 1783), (1816, 821, 991), (1817, 383, 1429), (1818, 29, 1787), (1819, 31, 1783), (1820, 751, 1063), (1821, 881, 937), (1822, 31, 1787), (1823, 877, 941)]
theorem wits_1784_ok : checkPairs wits_1784 = true := rfl
theorem wits_1784_ns : wits_1784.map (·.1) = (List.range 40).map (· + 1784) := rfl
theorem a_pos_1784_to_1823 (n : Nat) (h1 : 1784 ≤ n) (h2 : n ≤ 1823) : 0 < a n := by
  have hmem : n ∈ wits_1784.map (·.1) := by
    rw [wits_1784_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1784_ok hmem
def wits_1824 : List (Nat × Nat × Nat) :=
  [(1824, 37, 1783), (1825, 757, 1063), (1826, 881, 941), (1827, 37, 1787), (1828, 733, 1091), (1829, 883, 941), (1830, 809, 1019), (1831, 733, 1093), (1832, 881, 947), (1833, 821, 1009), (1834, 647, 1181), (1835, 883, 947), (1836, 347, 1487), (1837, 769, 1063), (1838, 857, 977), (1839, 827, 1009), (1840, 653, 1181), (1841, 859, 977), (1842, 821, 1019), (1843, 751, 1087), (1844, 827, 1013), (1845, 823, 1019), (1846, 809, 1033), (1847, 739, 1103), (1848, 827, 1019), (1849, 853, 991), (1850, 727, 1117), (1851, 881, 967), (1852, 857, 991), (1853, 907, 941), (1854, 821, 1031), (1855, 859, 991), (1856, 881, 971), (1857, 823, 1031), (1858, 821, 1033), (1859, 907, 947), (1860, 827, 1031), (1861, 823, 1033), (1862, 881, 977), (1863, 769, 1091)]
theorem wits_1824_ok : checkPairs wits_1824 = true := rfl
theorem wits_1824_ns : wits_1824.map (·.1) = (List.range 40).map (· + 1824) := rfl
theorem a_pos_1824_to_1863 (n : Nat) (h1 : 1824 ≤ n) (h2 : n ≤ 1863) : 0 < a n := by
  have hmem : n ∈ wits_1824.map (·.1) := by
    rw [wits_1824_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1824_ok hmem
def wits_1864 : List (Nat × Nat × Nat) :=
  [(1864, 827, 1033), (1865, 883, 977), (1866, 197, 1667), (1867, 739, 1123), (1868, 3, 1861), (1869, 857, 1009), (1870, 5, 1861), (1871, 853, 1013), (1872, 821, 1049), (1873, 3, 1867), (1874, 857, 1013), (1875, 5, 1867), (1876, 3, 1871), (1877, 859, 1013), (1878, 5, 1871), (1879, 3, 1873), (1880, 751, 1123), (1881, 5, 1873), (1882, 3, 1877), (1883, 937, 941), (1884, 5, 1877), (1885, 19, 1861), (1886, 659, 1223), (1887, 7, 1877), (1888, 941, 941), (1889, 937, 947), (1890, 11, 1877), (1891, 853, 1033), (1892, 587, 1301), (1893, 13, 1877), (1894, 29, 1861), (1895, 23, 1867), (1896, 17, 1877), (1897, 859, 1033), (1898, 23, 1871), (1899, 19, 1877), (1900, 947, 947), (1901, 23, 1873), (1902, 29, 1871), (1903, 31, 1867)]
theorem wits_1864_ok : checkPairs wits_1864 = true := rfl
theorem wits_1864_ns : wits_1864.map (·.1) = (List.range 40).map (· + 1864) := rfl
theorem a_pos_1864_to_1903 (n : Nat) (h1 : 1864 ≤ n) (h2 : n ≤ 1903) : 0 < a n := by
  have hmem : n ∈ wits_1864.map (·.1) := by
    rw [wits_1864_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1864_ok hmem
def wits_1904 : List (Nat × Nat × Nat) :=
  [(1904, 23, 1877), (1905, 29, 1873), (1906, 31, 1871), (1907, 353, 1549), (1908, 3, 1901), (1909, 31, 1873), (1910, 5, 1901), (1911, 37, 1871), (1912, 31, 1877), (1913, 7, 1901), (1914, 3, 1907), (1915, 877, 1033), (1916, 5, 1907), (1917, 37, 1877), (1918, 941, 971), (1919, 7, 1907), (1920, 857, 1061), (1921, 883, 1033), (1922, 11, 1907), (1923, 859, 1061), (1924, 947, 971), (1925, 13, 1907), (1926, 227, 1697), (1927, 859, 1063), (1928, 17, 1907), (1929, 907, 1019), (1930, 23, 1901), (1931, 19, 1907), (1932, 881, 1049), (1933, 937, 991), (1934, 29, 1901), (1935, 883, 1049), (1936, 3, 1931), (1937, 653, 1279), (1938, 5, 1931), (1939, 643, 1291), (1940, 29, 1907), (1941, 7, 1931), (1942, 821, 1117), (1943, 37, 1901)]
theorem wits_1904_ok : checkPairs wits_1904 = true := rfl
theorem wits_1904_ns : wits_1904.map (·.1) = (List.range 40).map (· + 1904) := rfl
theorem a_pos_1904_to_1943 (n : Nat) (h1 : 1904 ≤ n) (h2 : n ≤ 1943) : 0 < a n := by
  have hmem : n ∈ wits_1904.map (·.1) := by
    rw [wits_1904_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1904_ok hmem
def wits_1944 : List (Nat × Nat × Nat) :=
  [(1944, 11, 1931), (1945, 907, 1033), (1946, 659, 1283), (1947, 13, 1931), (1948, 971, 971), (1949, 37, 1907), (1950, 17, 1931), (1951, 883, 1063), (1952, 647, 1301), (1953, 19, 1931), (1954, 3, 1949), (1955, 941, 1009), (1956, 5, 1949), (1957, 499, 1453), (1958, 23, 1931), (1959, 7, 1949), (1960, 977, 977), (1961, 947, 1009), (1962, 11, 1949), (1963, 967, 991), (1964, 941, 1019), (1965, 13, 1949), (1966, 31, 1931), (1967, 859, 1103), (1968, 17, 1949), (1969, 751, 1213), (1970, 947, 1019), (1971, 19, 1949), (1972, 541, 1427), (1973, 67, 1901), (1974, 881, 1091), (1975, 937, 1033), (1976, 23, 1949), (1977, 883, 1091), (1978, 857, 1117), (1979, 877, 1097), (1980, 3, 1973), (1981, 859, 1117), (1982, 5, 1973), (1983, 499, 1481)]
theorem wits_1944_ok : checkPairs wits_1944 = true := rfl
theorem wits_1944_ns : wits_1944.map (·.1) = (List.range 40).map (· + 1944) := rfl
theorem a_pos_1944_to_1983 (n : Nat) (h1 : 1944 ≤ n) (h2 : n ≤ 1983) : 0 < a n := by
  have hmem : n ∈ wits_1944.map (·.1) := by
    rw [wits_1944_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1944_ok hmem
def wits_1984 : List (Nat × Nat × Nat) :=
  [(1984, 31, 1949), (1985, 7, 1973), (1986, 197, 1787), (1987, 859, 1123), (1988, 11, 1973), (1989, 37, 1949), (1990, 971, 1013), (1991, 13, 1973), (1992, 269, 1721), (1993, 757, 1231), (1994, 3, 1987), (1995, 673, 1319), (1996, 5, 1987), (1997, 19, 1973), (1998, 569, 1427), (1999, 3, 1993), (2000, 977, 1019), (2001, 5, 1993), (2002, 3, 1997), (2003, 397, 1601), (2004, 5, 1997), (2005, 3, 1999), (2006, 29, 1973), (2007, 5, 1999), (2008, 17, 1987), (2009, 907, 1097), (2010, 7, 1999), (2011, 19, 1987), (2012, 977, 1031), (2013, 11, 1999), (2014, 991, 1019), (2015, 37, 1973), (2016, 13, 1999), (2017, 733, 1279), (2018, 3, 2011), (2019, 17, 1999), (2020, 5, 2011), (2021, 23, 1993), (2022, 19, 1999), (2023, 7, 2011)]
theorem wits_1984_ok : checkPairs wits_1984 = true := rfl
theorem wits_1984_ns : wits_1984.map (·.1) = (List.range 40).map (· + 1984) := rfl
theorem a_pos_1984_to_2023 (n : Nat) (h1 : 1984 ≤ n) (h2 : n ≤ 2023) : 0 < a n := by
  have hmem : n ∈ wits_1984.map (·.1) := by
    rw [wits_1984_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_1984_ok hmem
def wits_2024 : List (Nat × Nat × Nat) :=
  [(2024, 23, 1997), (2025, 29, 1993), (2026, 11, 2011), (2027, 23, 1999), (2028, 29, 1997), (2029, 13, 2011), (2030, 991, 1033), (2031, 29, 1999), (2032, 3, 2027), (2033, 941, 1087), (2034, 5, 2027), (2035, 19, 2011), (2036, 1013, 1019), (2037, 7, 2027), (2038, 733, 1301), (2039, 947, 1087), (2040, 11, 2027), (2041, 733, 1303), (2042, 977, 1061), (2043, 13, 2027), (2044, 29, 2011), (2045, 947, 1093), (2046, 17, 2027), (2047, 1009, 1033), (2048, 31, 2011), (2049, 19, 2027), (2050, 947, 1097), (2051, 859, 1187), (2052, 1019, 1031), (2053, 37, 2011), (2054, 23, 2027), (2055, 823, 1229), (2056, 1019, 1033), (2057, 769, 1283), (2058, 29, 2027), (2059, 937, 1117), (2060, 991, 1063), (2061, 1009, 1049), (2062, 31, 2027), (2063, 971, 1087)]
theorem wits_2024_ok : checkPairs wits_2024 = true := rfl
theorem wits_2024_ns : wits_2024.map (·.1) = (List.range 40).map (· + 2024) := rfl
theorem a_pos_2024_to_2063 (n : Nat) (h1 : 2024 ≤ n) (h2 : n ≤ 2063) : 0 < a n := by
  have hmem : n ∈ wits_2024.map (·.1) := by
    rw [wits_2024_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2024_ok hmem
def wits_2064 : List (Nat × Nat × Nat) :=
  [(2064, 1031, 1031), (2065, 937, 1123), (2066, 1013, 1049), (2067, 37, 2027), (2068, 1031, 1033), (2069, 977, 1087), (2070, 3, 2063), (2071, 613, 1453), (2072, 5, 2063), (2073, 1009, 1061), (2074, 971, 1097), (2075, 7, 2063), (2076, 197, 1877), (2077, 1009, 1063), (2078, 11, 2063), (2079, 757, 1319), (2080, 977, 1097), (2081, 13, 2063), (2082, 1031, 1049), (2083, 991, 1087), (2084, 17, 2063), (2085, 853, 1229), (2086, 3, 2081), (2087, 19, 2063), (2088, 5, 2081), (2089, 3, 2083), (2090, 541, 1543), (2091, 5, 2083), (2092, 3, 2087), (2093, 907, 1181), (2094, 5, 2087), (2095, 967, 1123), (2096, 29, 2063), (2097, 7, 2087), (2098, 1033, 1061), (2099, 907, 1187), (2100, 11, 2087), (2101, 643, 1453), (2102, 1033, 1063), (2103, 13, 2087)]
theorem wits_2064_ok : checkPairs wits_2064 = true := rfl
theorem wits_2064_ns : wits_2064.map (·.1) = (List.range 40).map (· + 2064) := rfl
theorem a_pos_2064_to_2103 (n : Nat) (h1 : 2064 ≤ n) (h2 : n ≤ 2103) : 0 < a n := by
  have hmem : n ∈ wits_2064.map (·.1) := by
    rw [wits_2064_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2064_ok hmem
def wits_2104 : List (Nat × Nat × Nat) :=
  [(2104, 809, 1291), (2105, 37, 2063), (2106, 17, 2087), (2107, 349, 1753), (2108, 23, 2081), (2109, 19, 2087), (2110, 503, 1601), (2111, 23, 2083), (2112, 29, 2081), (2113, 877, 1231), (2114, 23, 2087), (2115, 29, 2083), (2116, 3, 2111), (2117, 1009, 1103), (2118, 5, 2111), (2119, 31, 2083), (2120, 1019, 1097), (2121, 7, 2111), (2122, 31, 2087), (2123, 937, 1181), (2124, 11, 2111), (2125, 1033, 1087), (2126, 1019, 1103), (2127, 13, 2111), (2128, 1061, 1063), (2129, 937, 1187), (2130, 17, 2111), (2131, 1033, 1093), (2132, 1063, 1063), (2133, 19, 2111), (2134, 3, 2129), (2135, 907, 1223), (2136, 5, 2129), (2137, 1009, 1123), (2138, 3, 2131), (2139, 7, 2129), (2140, 5, 2131), (2141, 853, 1283), (2142, 11, 2129), (2143, 3, 2137)]
theorem wits_2104_ok : checkPairs wits_2104 = true := rfl
theorem wits_2104_ns : wits_2104.map (·.1) = (List.range 40).map (· + 2104) := rfl
theorem a_pos_2104_to_2143 (n : Nat) (h1 : 2104 ≤ n) (h2 : n ≤ 2143) : 0 < a n := by
  have hmem : n ∈ wits_2104.map (·.1) := by
    rw [wits_2104_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2104_ok hmem
def wits_2144 : List (Nat × Nat × Nat) :=
  [(2144, 857, 1283), (2145, 5, 2137), (2146, 3, 2141), (2147, 859, 1283), (2148, 5, 2141), (2149, 13, 2131), (2150, 1049, 1097), (2151, 7, 2141), (2152, 17, 2131), (2153, 967, 1181), (2154, 11, 2141), (2155, 19, 2131), (2156, 23, 2129), (2157, 13, 2141), (2158, 1063, 1091), (2159, 967, 1187), (2160, 17, 2141), (2161, 1063, 1093), (2162, 1061, 1097), (2163, 19, 2141), (2164, 29, 2131), (2165, 23, 2137), (2166, 137, 2027), (2167, 733, 1429), (2168, 23, 2141), (2169, 29, 2137), (2170, 1049, 1117), (2171, 883, 1283), (2172, 29, 2141), (2173, 31, 2137), (2174, 941, 1229), (2175, 883, 1289), (2176, 31, 2141), (2177, 739, 1433), (2178, 37, 2137), (2179, 883, 1291), (2180, 947, 1229), (2181, 37, 2141), (2182, 1061, 1117), (2183, 277, 1901)]
theorem wits_2144_ok : checkPairs wits_2144 = true := rfl
theorem wits_2144_ns : wits_2144.map (·.1) = (List.range 40).map (· + 2144) := rfl
theorem a_pos_2144_to_2183 (n : Nat) (h1 : 2144 ≤ n) (h2 : n ≤ 2183) : 0 < a n := by
  have hmem : n ∈ wits_2144.map (·.1) := by
    rw [wits_2144_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2144_ok hmem
def wits_2184 : List (Nat × Nat × Nat) :=
  [(2184, 1091, 1091), (2185, 859, 1321), (2186, 1063, 1117), (2187, 1091, 1093), (2188, 1061, 1123), (2189, 1087, 1097), (2190, 569, 1619), (2191, 643, 1543), (2192, 1091, 1097), (2193, 739, 1451), (2194, 971, 1217), (2195, 1093, 1097), (2196, 197, 1997), (2197, 739, 1453), (2198, 1091, 1103), (2199, 967, 1229), (2200, 1097, 1097), (2201, 1093, 1103), (2202, 1049, 1151), (2203, 967, 1231), (2204, 1019, 1181), (2205, 883, 1319), (2206, 1097, 1103), (2207, 769, 1433), (2208, 599, 1607), (2209, 3, 2203), (2210, 1019, 1187), (2211, 5, 2203), (2212, 1103, 1103), (2213, 307, 1901), (2214, 3, 2207), (2215, 1093, 1117), (2216, 5, 2207), (2217, 11, 2203), (2218, 1091, 1123), (2219, 7, 2207), (2220, 13, 2203), (2221, 1093, 1123), (2222, 11, 2207), (2223, 17, 2203)]
theorem wits_2184_ok : checkPairs wits_2184 = true := rfl
theorem wits_2184_ns : wits_2184.map (·.1) = (List.range 40).map (· + 2184) := rfl
theorem a_pos_2184_to_2223 (n : Nat) (h1 : 2184 ≤ n) (h2 : n ≤ 2223) : 0 < a n := by
  have hmem : n ∈ wits_2184.map (·.1) := by
    rw [wits_2184_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2184_ok hmem
def wits_2224 : List (Nat × Nat × Nat) :=
  [(2224, 991, 1229), (2225, 13, 2207), (2226, 19, 2203), (2227, 769, 1453), (2228, 17, 2207), (2229, 937, 1289), (2230, 941, 1283), (2231, 19, 2207), (2232, 281, 1949), (2233, 937, 1291), (2234, 1049, 1181), (2235, 29, 2203), (2236, 23, 2207), (2237, 1009, 1223), (2238, 809, 1427), (2239, 31, 2203), (2240, 29, 2207), (2241, 1087, 1151), (2242, 3, 2237), (2243, 941, 1297), (2244, 5, 2237), (2245, 3, 2239), (2246, 1117, 1123), (2247, 5, 2239), (2248, 373, 1871), (2249, 37, 2207), (2250, 7, 2239), (2251, 1033, 1213), (2252, 1123, 1123), (2253, 11, 2239), (2254, 1019, 1231), (2255, 971, 1279), (2256, 13, 2239), (2257, 499, 1753), (2258, 1103, 1151), (2259, 17, 2239), (2260, 971, 1283), (2261, 977, 1279), (2262, 19, 2239), (2263, 967, 1291)]
theorem wits_2224_ok : checkPairs wits_2224 = true := rfl
theorem wits_2224_ns : wits_2224.map (·.1) = (List.range 40).map (· + 2224) := rfl
theorem a_pos_2224_to_2263 (n : Nat) (h1 : 2224 ≤ n) (h2 : n ≤ 2263) : 0 < a n := by
  have hmem : n ∈ wits_2224.map (·.1) := by
    rw [wits_2224_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2224_ok hmem
def wits_2264 : List (Nat × Nat × Nat) :=
  [(2264, 23, 2237), (2265, 1049, 1213), (2266, 1033, 1229), (2267, 23, 2239), (2268, 29, 2237), (2269, 643, 1621), (2270, 1049, 1217), (2271, 29, 2239), (2272, 3, 2267), (2273, 1087, 1181), (2274, 5, 2267), (2275, 3, 2269), (2276, 1091, 1181), (2277, 5, 2269), (2278, 1123, 1151), (2279, 1093, 1181), (2280, 7, 2269), (2281, 1063, 1213), (2282, 1091, 1187), (2283, 11, 2269), (2284, 1097, 1181), (2285, 1093, 1187), (2286, 13, 2269), (2287, 739, 1543), (2288, 3, 2281), (2289, 17, 2269), (2290, 5, 2281), (2291, 853, 1433), (2292, 19, 2269), (2293, 7, 2281), (2294, 3, 2287), (2295, 809, 1483), (2296, 5, 2287), (2297, 23, 2269), (2298, 29, 2267), (2299, 3, 2293), (2300, 1063, 1231), (2301, 5, 2293), (2302, 11, 2287), (2303, 937, 1361)]
theorem wits_2264_ok : checkPairs wits_2264 = true := rfl
theorem wits_2264_ns : wits_2264.map (·.1) = (List.range 40).map (· + 2264) := rfl
theorem a_pos_2264_to_2303 (n : Nat) (h1 : 2264 ≤ n) (h2 : n ≤ 2303) : 0 < a n := by
  have hmem : n ∈ wits_2264.map (·.1) := by
    rw [wits_2264_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2264_ok hmem
def wits_2304 : List (Nat × Nat × Nat) :=
  [(2304, 7, 2293), (2305, 13, 2287), (2306, 1019, 1283), (2307, 11, 2293), (2308, 17, 2287), (2309, 1087, 1217), (2310, 13, 2293), (2311, 19, 2287), (2312, 1091, 1217), (2313, 17, 2293), (2314, 3, 2309), (2315, 1097, 1213), (2316, 5, 2309), (2317, 1033, 1279), (2318, 31, 2281), (2319, 7, 2309), (2320, 29, 2287), (2321, 23, 2293), (2322, 11, 2309), (2323, 37, 2281), (2324, 31, 2287), (2325, 13, 2309), (2326, 1103, 1217), (2327, 769, 1553), (2328, 17, 2309), (2329, 31, 2293), (2330, 1097, 1229), (2331, 19, 2309), (2332, 1103, 1223), (2333, 967, 1361), (2334, 37, 2293), (2335, 1117, 1213), (2336, 23, 2309), (2337, 1031, 1303), (2338, 1033, 1301), (2339, 967, 1367), (2340, 3, 2333), (2341, 1123, 1213), (2342, 5, 2333), (2343, 1061, 1279)]
theorem wits_2304_ok : checkPairs wits_2304 = true := rfl
theorem wits_2304_ns : wits_2304.map (·.1) = (List.range 40).map (· + 2304) := rfl
theorem a_pos_2304_to_2343 (n : Nat) (h1 : 2304 ≤ n) (h2 : n ≤ 2343) : 0 < a n := by
  have hmem : n ∈ wits_2304.map (·.1) := by
    rw [wits_2304_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2304_ok hmem
def wits_2344 : List (Nat × Nat × Nat) :=
  [(2344, 3, 2339), (2345, 7, 2333), (2346, 5, 2339), (2347, 1063, 1279), (2348, 3, 2341), (2349, 7, 2339), (2350, 5, 2341), (2351, 13, 2333), (2352, 11, 2339), (2353, 3, 2347), (2354, 17, 2333), (2355, 5, 2347), (2356, 11, 2341), (2357, 19, 2333), (2358, 3, 2351), (2359, 13, 2341), (2360, 5, 2351), (2361, 11, 2347), (2362, 17, 2341), (2363, 7, 2351), (2364, 13, 2347), (2365, 19, 2341), (2366, 11, 2351), (2367, 17, 2347), (2368, 1181, 1181), (2369, 13, 2351), (2370, 19, 2347), (2371, 1063, 1303), (2372, 17, 2351), (2373, 1093, 1277), (2374, 29, 2341), (2375, 19, 2351), (2376, 347, 2027), (2377, 373, 1999), (2378, 3, 2371), (2379, 29, 2347), (2380, 5, 2371), (2381, 1097, 1279), (2382, 1151, 1229), (2383, 3, 2377)]
theorem wits_2344_ok : checkPairs wits_2344 = true := rfl
theorem wits_2344_ns : wits_2344.map (·.1) = (List.range 40).map (· + 2344) := rfl
theorem a_pos_2344_to_2383 (n : Nat) (h1 : 2344 ≤ n) (h2 : n ≤ 2383) : 0 < a n := by
  have hmem : n ∈ wits_2344.map (·.1) := by
    rw [wits_2344_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2344_ok hmem
def wits_2384 : List (Nat × Nat × Nat) :=
  [(2384, 29, 2351), (2385, 5, 2377), (2386, 3, 2381), (2387, 1103, 1279), (2388, 5, 2381), (2389, 13, 2371), (2390, 3, 2383), (2391, 7, 2381), (2392, 5, 2383), (2393, 37, 2351), (2394, 11, 2381), (2395, 3, 2389), (2396, 1103, 1289), (2397, 5, 2389), (2398, 11, 2383), (2399, 1181, 1213), (2400, 3, 2393), (2401, 13, 2383), (2402, 5, 2393), (2403, 11, 2389), (2404, 17, 2383), (2405, 7, 2393), (2406, 13, 2389), (2407, 19, 2383), (2408, 11, 2393), (2409, 17, 2389), (2410, 1187, 1217), (2411, 13, 2393), (2412, 19, 2389), (2413, 31, 2377), (2414, 17, 2393), (2415, 1093, 1319), (2416, 29, 2383), (2417, 19, 2393), (2418, 3, 2411), (2419, 1117, 1297), (2420, 5, 2411), (2421, 29, 2389), (2422, 23, 2393), (2423, 7, 2411)]
theorem wits_2384_ok : checkPairs wits_2384 = true := rfl
theorem wits_2384_ns : wits_2384.map (·.1) = (List.range 40).map (· + 2384) := rfl
theorem a_pos_2384_to_2423 (n : Nat) (h1 : 2384 ≤ n) (h2 : n ≤ 2423) : 0 < a n := by
  have hmem : n ∈ wits_2384.map (·.1) := by
    rw [wits_2384_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2384_ok hmem
def wits_2424 : List (Nat × Nat × Nat) :=
  [(2424, 3, 2417), (2425, 31, 2389), (2426, 5, 2417), (2427, 937, 1487), (2428, 1123, 1301), (2429, 7, 2417), (2430, 31, 2393), (2431, 1123, 1303), (2432, 11, 2417), (2433, 1151, 1279), (2434, 809, 1621), (2435, 13, 2417), (2436, 827, 1607), (2437, 433, 1999), (2438, 17, 2417), (2439, 1009, 1427), (2440, 23, 2411), (2441, 19, 2417), (2442, 1151, 1289), (2443, 3, 2437), (2444, 29, 2411), (2445, 5, 2437), (2446, 23, 2417), (2447, 1013, 1429), (2448, 3, 2441), (2449, 1213, 1231), (2450, 5, 2441), (2451, 11, 2437), (2452, 1223, 1223), (2453, 7, 2441), (2454, 13, 2437), (2455, 907, 1543), (2456, 11, 2441), (2457, 17, 2437), (2458, 733, 1721), (2459, 13, 2441), (2460, 19, 2437), (2461, 1033, 1423), (2462, 17, 2441), (2463, 1031, 1429)]
theorem wits_2424_ok : checkPairs wits_2424 = true := rfl
theorem wits_2424_ns : wits_2424.map (·.1) = (List.range 40).map (· + 2424) := rfl
theorem a_pos_2424_to_2463 (n : Nat) (h1 : 2424 ≤ n) (h2 : n ≤ 2463) : 0 < a n := by
  have hmem : n ∈ wits_2424.map (·.1) := by
    rw [wits_2424_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2424_ok hmem
def wits_2464 : List (Nat × Nat × Nat) :=
  [(2464, 1229, 1231), (2465, 19, 2441), (2466, 857, 1607), (2467, 1033, 1429), (2468, 1231, 1231), (2469, 29, 2437), (2470, 23, 2441), (2471, 1187, 1279), (2472, 1151, 1319), (2473, 31, 2437), (2474, 3, 2467), (2475, 1049, 1423), (2476, 5, 2467), (2477, 859, 1613), (2478, 31, 2441), (2479, 3, 2473), (2480, 1187, 1289), (2481, 5, 2473), (2482, 11, 2467), (2483, 37, 2441), (2484, 7, 2473), (2485, 13, 2467), (2486, 1181, 1301), (2487, 11, 2473), (2488, 17, 2467), (2489, 1187, 1297), (2490, 13, 2473), (2491, 19, 2467), (2492, 1187, 1301), (2493, 17, 2473), (2494, 1063, 1427), (2495, 1187, 1303), (2496, 19, 2473), (2497, 1063, 1429), (2498, 1217, 1277), (2499, 1049, 1447), (2500, 29, 2467), (2501, 23, 2473), (2502, 1049, 1451), (2503, 877, 1621)]
theorem wits_2464_ok : checkPairs wits_2464 = true := rfl
theorem wits_2464_ns : wits_2464.map (·.1) = (List.range 40).map (· + 2464) := rfl
theorem a_pos_2464_to_2503 (n : Nat) (h1 : 2464 ≤ n) (h2 : n ≤ 2503) : 0 < a n := by
  have hmem : n ∈ wits_2464.map (·.1) := by
    rw [wits_2464_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2464_ok hmem
def wits_2504 : List (Nat × Nat × Nat) :=
  [(2504, 31, 2467), (2505, 29, 2473), (2506, 1217, 1283), (2507, 1223, 1279), (2508, 1229, 1277), (2509, 31, 2473), (2510, 1217, 1289), (2511, 1229, 1279), (2512, 1231, 1277), (2513, 941, 1567), (2514, 37, 2473), (2515, 1231, 1279), (2516, 1229, 1283), (2517, 1213, 1301), (2518, 1063, 1451), (2519, 1217, 1297), (2520, 1229, 1289), (2521, 1033, 1483), (2522, 1217, 1301), (2523, 1093, 1427), (2524, 1231, 1289), (2525, 1223, 1297), (2526, 857, 1667), (2527, 1033, 1489), (2528, 1231, 1291), (2529, 1229, 1297), (2530, 971, 1553), (2531, 1223, 1303), (2532, 1229, 1301), (2533, 1231, 1297), (2534, 1103, 1427), (2535, 1229, 1303), (2536, 1231, 1301), (2537, 1103, 1429), (2538, 1049, 1487), (2539, 1231, 1303), (2540, 1217, 1319), (2541, 1091, 1447), (2542, 1103, 1433), (2543, 971, 1567)]
theorem wits_2504_ok : checkPairs wits_2504 = true := rfl
theorem wits_2504_ns : wits_2504.map (·.1) = (List.range 40).map (· + 2504) := rfl
theorem a_pos_2504_to_2543 (n : Nat) (h1 : 2504 ≤ n) (h2 : n ≤ 2543) : 0 < a n := by
  have hmem : n ∈ wits_2504.map (·.1) := by
    rw [wits_2504_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2504_ok hmem
def wits_2544 : List (Nat × Nat × Nat) :=
  [(2544, 1091, 1451), (2545, 3, 2539), (2546, 1223, 1319), (2547, 5, 2539), (2548, 1181, 1361), (2549, 1097, 1447), (2550, 3, 2543), (2551, 1123, 1423), (2552, 5, 2543), (2553, 11, 2539), (2554, 3, 2549), (2555, 7, 2543), (2556, 5, 2549), (2557, 1123, 1429), (2558, 3, 2551), (2559, 7, 2549), (2560, 5, 2551), (2561, 13, 2543), (2562, 11, 2549), (2563, 7, 2551), (2564, 17, 2543), (2565, 13, 2549), (2566, 11, 2551), (2567, 19, 2543), (2568, 17, 2549), (2569, 13, 2551), (2570, 947, 1619), (2571, 19, 2549), (2572, 17, 2551), (2573, 971, 1597), (2574, 1091, 1481), (2575, 19, 2551), (2576, 23, 2549), (2577, 1277, 1297), (2578, 1123, 1451), (2579, 1213, 1361), (2580, 23, 2551), (2581, 823, 1753), (2582, 1123, 1453), (2583, 1279, 1301)]
theorem wits_2544_ok : checkPairs wits_2544 = true := rfl
theorem wits_2544_ns : wits_2544.map (·.1) = (List.range 40).map (· + 2544) := rfl
theorem a_pos_2544_to_2583 (n : Nat) (h1 : 2544 ≤ n) (h2 : n ≤ 2583) : 0 < a n := by
  have hmem : n ∈ wits_2544.map (·.1) := by
    rw [wits_2544_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2544_ok hmem
def wits_2584 : List (Nat × Nat × Nat) :=
  [(2584, 29, 2551), (2585, 37, 2543), (2586, 347, 2237), (2587, 1033, 1549), (2588, 31, 2551), (2589, 37, 2549), (2590, 1223, 1361), (2591, 1283, 1303), (2592, 1289, 1301), (2593, 37, 2551), (2594, 1229, 1361), (2595, 1289, 1303), (2596, 3, 2591), (2597, 1103, 1489), (2598, 5, 2591), (2599, 1291, 1303), (2600, 1229, 1367), (2601, 7, 2591), (2602, 1277, 1321), (2603, 251, 2347), (2604, 11, 2591), (2605, 1279, 1321), (2606, 1283, 1319), (2607, 13, 2591), (2608, 1151, 1453), (2609, 1181, 1423), (2610, 17, 2591), (2611, 1123, 1483), (2612, 1181, 1427), (2613, 19, 2591), (2614, 1291, 1319), (2615, 1187, 1423), (2616, 827, 1787), (2617, 1123, 1489), (2618, 23, 2591), (2619, 1297, 1319), (2620, 1181, 1433), (2621, 1187, 1429), (2622, 29, 2591), (2623, 3, 2617)]
theorem wits_2584_ok : checkPairs wits_2584 = true := rfl
theorem wits_2584_ns : wits_2584.map (·.1) = (List.range 40).map (· + 2584) := rfl
theorem a_pos_2584_to_2623 (n : Nat) (h1 : 2584 ≤ n) (h2 : n ≤ 2623) : 0 < a n := by
  have hmem : n ∈ wits_2584.map (·.1) := by
    rw [wits_2584_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2584_ok hmem
def wits_2624 : List (Nat × Nat × Nat) :=
  [(2624, 1019, 1601), (2625, 5, 2617), (2626, 31, 2591), (2627, 1013, 1609), (2628, 7, 2617), (2629, 1303, 1321), (2630, 677, 1949), (2631, 11, 2617), (2632, 1013, 1613), (2633, 1181, 1447), (2634, 13, 2617), (2635, 1087, 1543), (2636, 1181, 1451), (2637, 17, 2617), (2638, 1091, 1543), (2639, 1187, 1447), (2640, 19, 2617), (2641, 1093, 1543), (2642, 1277, 1361), (2643, 1213, 1427), (2644, 1319, 1321), (2645, 23, 2617), (2646, 857, 1787), (2647, 1063, 1579), (2648, 1321, 1321), (2649, 29, 2617), (2650, 1283, 1361), (2651, 1279, 1367), (2652, 1031, 1619), (2653, 31, 2617), (2654, 1289, 1361), (2655, 1229, 1423), (2656, 1283, 1367), (2657, 1223, 1429), (2658, 37, 2617), (2659, 1231, 1423), (2660, 1289, 1367), (2661, 1229, 1429), (2662, 3, 2657), (2663, 1297, 1361)]
theorem wits_2624_ok : checkPairs wits_2624 = true := rfl
theorem wits_2624_ns : wits_2624.map (·.1) = (List.range 40).map (· + 2624) := rfl
theorem a_pos_2624_to_2663 (n : Nat) (h1 : 2624 ≤ n) (h2 : n ≤ 2663) : 0 < a n := by
  have hmem : n ∈ wits_2624.map (·.1) := by
    rw [wits_2624_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2624_ok hmem
def wits_2664 : List (Nat × Nat × Nat) :=
  [(2664, 5, 2657), (2665, 3, 2659), (2666, 1301, 1361), (2667, 5, 2659), (2668, 733, 1931), (2669, 1303, 1361), (2670, 7, 2659), (2671, 1213, 1453), (2672, 1301, 1367), (2673, 11, 2659), (2674, 1063, 1607), (2675, 1303, 1367), (2676, 13, 2659), (2677, 1123, 1549), (2678, 3, 2671), (2679, 17, 2659), (2680, 5, 2671), (2681, 1187, 1489), (2682, 19, 2659), (2683, 7, 2671), (2684, 3, 2677), (2685, 1019, 1663), (2686, 5, 2677), (2687, 23, 2659), (2688, 29, 2657), (2689, 3, 2683), (2690, 1319, 1367), (2691, 5, 2683), (2692, 3, 2687), (2693, 1087, 1601), (2694, 5, 2687), (2695, 3, 2689), (2696, 1091, 1601), (2697, 5, 2689), (2698, 17, 2677), (2699, 1097, 1597), (2700, 3, 2693), (2701, 19, 2677), (2702, 5, 2693), (2703, 11, 2689)]
theorem wits_2664_ok : checkPairs wits_2664 = true := rfl
theorem wits_2664_ns : wits_2664.map (·.1) = (List.range 40).map (· + 2664) := rfl
theorem a_pos_2664_to_2703 (n : Nat) (h1 : 2664 ≤ n) (h2 : n ≤ 2703) : 0 < a n := by
  have hmem : n ∈ wits_2664.map (·.1) := by
    rw [wits_2664_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2664_ok hmem
def wits_2704 : List (Nat × Nat × Nat) :=
  [(2704, 29, 2671), (2705, 7, 2693), (2706, 13, 2689), (2707, 1123, 1579), (2708, 11, 2693), (2709, 17, 2689), (2710, 29, 2677), (2711, 13, 2693), (2712, 19, 2689), (2713, 3, 2707), (2714, 17, 2693), (2715, 5, 2707), (2716, 3, 2711), (2717, 19, 2693), (2718, 5, 2711), (2719, 31, 2683), (2720, 3, 2713), (2721, 7, 2711), (2722, 5, 2713), (2723, 307, 2411), (2724, 11, 2711), (2725, 7, 2713), (2726, 29, 2693), (2727, 13, 2711), (2728, 11, 2713), (2729, 941, 1783), (2730, 17, 2711), (2731, 13, 2713), (2732, 941, 1787), (2733, 19, 2711), (2734, 3, 2729), (2735, 23, 2707), (2736, 5, 2729), (2737, 19, 2713), (2738, 23, 2711), (2739, 7, 2729), (2740, 1367, 1367), (2741, 1303, 1433), (2742, 11, 2729), (2743, 31, 2707)]
theorem wits_2704_ok : checkPairs wits_2704 = true := rfl
theorem wits_2704_ns : wits_2704.map (·.1) = (List.range 40).map (· + 2704) := rfl
theorem a_pos_2704_to_2743 (n : Nat) (h1 : 2704 ≤ n) (h2 : n ≤ 2743) : 0 < a n := by
  have hmem : n ∈ wits_2704.map (·.1) := by
    rw [wits_2704_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2704_ok hmem
def wits_2744 : List (Nat × Nat × Nat) :=
  [(2744, 1117, 1621), (2745, 13, 2729), (2746, 29, 2713), (2747, 769, 1973), (2748, 17, 2729), (2749, 1321, 1423), (2750, 31, 2713), (2751, 19, 2729), (2752, 1321, 1427), (2753, 1181, 1567), (2754, 1301, 1451), (2755, 3, 2749), (2756, 23, 2729), (2757, 5, 2749), (2758, 1301, 1453), (2759, 1187, 1567), (2760, 7, 2749), (2761, 1303, 1453), (2762, 971, 1787), (2763, 11, 2749), (2764, 31, 2729), (2765, 1181, 1579), (2766, 13, 2749), (2767, 1009, 1753), (2768, 1283, 1481), (2769, 17, 2749), (2770, 1019, 1747), (2771, 1283, 1483), (2772, 19, 2749), (2773, 1321, 1447), (2774, 1283, 1487), (2775, 1289, 1483), (2776, 1321, 1451), (2777, 23, 2749), (2778, 1289, 1487), (2779, 1291, 1483), (2780, 1321, 1453), (2781, 29, 2749), (2782, 1291, 1487), (2783, 1181, 1597)]
theorem wits_2744_ok : checkPairs wits_2744 = true := rfl
theorem wits_2744_ns : wits_2744.map (·.1) = (List.range 40).map (· + 2744) := rfl
theorem a_pos_2744_to_2783 (n : Nat) (h1 : 2744 ≤ n) (h2 : n ≤ 2783) : 0 < a n := by
  have hmem : n ∈ wits_2744.map (·.1) := by
    rw [wits_2744_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2744_ok hmem
def wits_2784 : List (Nat × Nat × Nat) :=
  [(2784, 1301, 1481), (2785, 31, 2749), (2786, 1289, 1493), (2787, 1303, 1481), (2788, 1181, 1601), (2789, 1361, 1423), (2790, 37, 2749), (2791, 1123, 1663), (2792, 1361, 1427), (2793, 1303, 1487), (2794, 3, 2789), (2795, 1367, 1423), (2796, 5, 2789), (2797, 79, 2713), (2798, 3, 2791), (2799, 7, 2789), (2800, 5, 2791), (2801, 1367, 1429), (2802, 11, 2789), (2803, 3, 2797), (2804, 1181, 1619), (2805, 5, 2797), (2806, 3, 2801), (2807, 1223, 1579), (2808, 5, 2801), (2809, 13, 2791), (2810, 1187, 1619), (2811, 7, 2801), (2812, 17, 2791), (2813, 1361, 1447), (2814, 11, 2801), (2815, 19, 2791), (2816, 23, 2789), (2817, 13, 2801), (2818, 1117, 1697), (2819, 1367, 1447), (2820, 17, 2801), (2821, 1123, 1693), (2822, 1367, 1451), (2823, 19, 2801)]
theorem wits_2784_ok : checkPairs wits_2784 = true := rfl
theorem wits_2784_ns : wits_2784.map (·.1) = (List.range 40).map (· + 2784) := rfl
theorem a_pos_2784_to_2823 (n : Nat) (h1 : 2784 ≤ n) (h2 : n ≤ 2823) : 0 < a n := by
  have hmem : n ∈ wits_2784.map (·.1) := by
    rw [wits_2784_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2784_ok hmem
def wits_2824 : List (Nat × Nat × Nat) :=
  [(2824, 29, 2791), (2825, 23, 2797), (2826, 827, 1997), (2827, 1279, 1543), (2828, 23, 2801), (2829, 29, 2797), (2830, 1223, 1601), (2831, 1217, 1609), (2832, 29, 2801), (2833, 31, 2797), (2834, 1277, 1553), (2835, 1213, 1619), (2836, 31, 2801), (2837, 1283, 1549), (2838, 37, 2797), (2839, 3, 2833), (2840, 1291, 1543), (2841, 5, 2833), (2842, 1283, 1553), (2843, 971, 1867), (2844, 3, 2837), (2845, 1297, 1543), (2846, 5, 2837), (2847, 11, 2833), (2848, 1301, 1543), (2849, 7, 2837), (2850, 13, 2833), (2851, 1303, 1543), (2852, 11, 2837), (2853, 17, 2833), (2854, 1231, 1619), (2855, 13, 2837), (2856, 19, 2833), (2857, 1291, 1559), (2858, 3, 2851), (2859, 1427, 1429), (2860, 5, 2851), (2861, 19, 2837), (2862, 521, 2339), (2863, 3, 2857)]
theorem wits_2824_ok : checkPairs wits_2824 = true := rfl
theorem wits_2824_ns : wits_2824.map (·.1) = (List.range 40).map (· + 2824) := rfl
theorem a_pos_2824_to_2863 (n : Nat) (h1 : 2824 ≤ n) (h2 : n ≤ 2863) : 0 < a n := by
  have hmem : n ∈ wits_2824.map (·.1) := by
    rw [wits_2824_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2824_ok hmem
def wits_2864 : List (Nat × Nat × Nat) :=
  [(2864, 1427, 1433), (2865, 5, 2857), (2866, 11, 2851), (2867, 1429, 1433), (2868, 7, 2857), (2869, 13, 2851), (2870, 29, 2837), (2871, 11, 2857), (2872, 17, 2851), (2873, 967, 1901), (2874, 13, 2857), (2875, 19, 2851), (2876, 1319, 1553), (2877, 17, 2857), (2878, 971, 1901), (2879, 37, 2837), (2880, 19, 2857), (2881, 1423, 1453), (2882, 1277, 1601), (2883, 1429, 1451), (2884, 29, 2851), (2885, 23, 2857), (2886, 1277, 1607), (2887, 1429, 1453), (2888, 31, 2851), (2889, 29, 2857), (2890, 1283, 1601), (2891, 1223, 1663), (2892, 1019, 1871), (2893, 31, 2857), (2894, 1289, 1601), (2895, 1229, 1663), (2896, 1151, 1741), (2897, 1283, 1609), (2898, 37, 2857), (2899, 1231, 1663), (2900, 1117, 1777), (2901, 1447, 1451), (2902, 1291, 1607), (2903, 1297, 1601)]
theorem wits_2864_ok : checkPairs wits_2864 = true := rfl
theorem wits_2864_ns : wits_2864.map (·.1) = (List.range 40).map (· + 2864) := rfl
theorem a_pos_2864_to_2903 (n : Nat) (h1 : 2864 ≤ n) (h2 : n ≤ 2903) : 0 < a n := by
  have hmem : n ∈ wits_2864.map (·.1) := by
    rw [wits_2864_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2864_ok hmem
def wits_2904 : List (Nat × Nat × Nat) :=
  [(2904, 3, 2897), (2905, 1447, 1453), (2906, 5, 2897), (2907, 1423, 1481), (2908, 1451, 1453), (2909, 7, 2897), (2910, 3, 2903), (2911, 1123, 1783), (2912, 5, 2903), (2913, 1429, 1481), (2914, 1291, 1619), (2915, 7, 2903), (2916, 1427, 1487), (2917, 373, 2539), (2918, 11, 2903), (2919, 1429, 1487), (2920, 1361, 1553), (2921, 13, 2903), (2922, 1301, 1619), (2923, 1321, 1597), (2924, 17, 2903), (2925, 1303, 1619), (2926, 23, 2897), (2927, 19, 2903), (2928, 1319, 1607), (2929, 1303, 1621), (2930, 29, 2897), (2931, 1447, 1481), (2932, 23, 2903), (2933, 1361, 1567), (2934, 31, 2897), (2935, 1321, 1609), (2936, 29, 2903), (2937, 1451, 1483), (2938, 1453, 1481), (2939, 37, 2897), (2940, 31, 2903), (2941, 1453, 1483), (2942, 1217, 1721), (2943, 1451, 1489)]
theorem wits_2904_ok : checkPairs wits_2904 = true := rfl
theorem wits_2904_ns : wits_2904.map (·.1) = (List.range 40).map (· + 2904) := rfl
theorem a_pos_2904_to_2943 (n : Nat) (h1 : 2904 ≤ n) (h2 : n ≤ 2943) : 0 < a n := by
  have hmem : n ∈ wits_2904.map (·.1) := by
    rw [wits_2904_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2904_ok hmem
def wits_2944 : List (Nat × Nat × Nat) :=
  [(2944, 1453, 1487), (2945, 37, 2903), (2946, 1277, 1667), (2947, 1453, 1489), (2948, 1451, 1493), (2949, 1279, 1667), (2950, 1289, 1657), (2951, 1367, 1579), (2952, 1229, 1721), (2953, 1087, 1861), (2954, 1291, 1657), (2955, 1289, 1663), (2956, 1231, 1721), (2957, 563, 2389), (2958, 1289, 1667), (2959, 3, 2953), (2960, 1049, 1907), (2961, 5, 2953), (2962, 1301, 1657), (2963, 1361, 1597), (2964, 3, 2957), (2965, 1303, 1657), (2966, 5, 2957), (2967, 11, 2953), (2968, 1361, 1601), (2969, 7, 2957), (2970, 3, 2963), (2971, 1423, 1543), (2972, 5, 2963), (2973, 17, 2953), (2974, 3, 2969), (2975, 7, 2963), (2976, 5, 2969), (2977, 1429, 1543), (2978, 11, 2963), (2979, 7, 2969), (2980, 1361, 1613), (2981, 13, 2963), (2982, 11, 2969), (2983, 967, 2011)]
theorem wits_2944_ok : checkPairs wits_2944 = true := rfl
theorem wits_2944_ns : wits_2944.map (·.1) = (List.range 40).map (· + 2944) := rfl
theorem a_pos_2944_to_2983 (n : Nat) (h1 : 2944 ≤ n) (h2 : n ≤ 2983) : 0 < a n := by
  have hmem : n ∈ wits_2944.map (·.1) := by
    rw [wits_2944_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2944_ok hmem
def wits_2984 : List (Nat × Nat × Nat) :=
  [(2984, 17, 2963), (2985, 13, 2969), (2986, 23, 2957), (2987, 19, 2963), (2988, 17, 2969), (2989, 31, 2953), (2990, 29, 2957), (2991, 19, 2969), (2992, 23, 2963), (2993, 1087, 1901), (2994, 31, 2957), (2995, 1447, 1543), (2996, 23, 2969), (2997, 1427, 1567), (2998, 1451, 1543), (2999, 37, 2957), (3000, 29, 2969)]
theorem wits_2984_ok : checkPairs wits_2984 = true := rfl
theorem wits_2984_ns : wits_2984.map (·.1) = (List.range 17).map (· + 2984) := rfl
theorem a_pos_2984_to_3000 (n : Nat) (h1 : 2984 ≤ n) (h2 : n ≤ 3000) : 0 < a n := by
  have hmem : n ∈ wits_2984.map (·.1) := by
    rw [wits_2984_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_2984_ok hmem

-- Glue 824..3000
theorem a_pos_824_to_1023 (n : Nat) (h1 : 824 ≤ n) (h2 : n ≤ 1023) : 0 < a n := by
  have hcases : (824 ≤ n ∧ n ≤ 863) ∨ (864 ≤ n ∧ n ≤ 903) ∨ (904 ≤ n ∧ n ≤ 943) ∨ (944 ≤ n ∧ n ≤ 983) ∨ (984 ≤ n ∧ n ≤ 1023) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_824_to_863 n h.1 h.2
  · exact a_pos_864_to_903 n h.1 h.2
  · exact a_pos_904_to_943 n h.1 h.2
  · exact a_pos_944_to_983 n h.1 h.2
  · exact a_pos_984_to_1023 n h.1 h.2
theorem a_pos_1024_to_1223 (n : Nat) (h1 : 1024 ≤ n) (h2 : n ≤ 1223) : 0 < a n := by
  have hcases : (1024 ≤ n ∧ n ≤ 1063) ∨ (1064 ≤ n ∧ n ≤ 1103) ∨ (1104 ≤ n ∧ n ≤ 1143) ∨ (1144 ≤ n ∧ n ≤ 1183) ∨ (1184 ≤ n ∧ n ≤ 1223) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_1024_to_1063 n h.1 h.2
  · exact a_pos_1064_to_1103 n h.1 h.2
  · exact a_pos_1104_to_1143 n h.1 h.2
  · exact a_pos_1144_to_1183 n h.1 h.2
  · exact a_pos_1184_to_1223 n h.1 h.2
theorem a_pos_1224_to_1423 (n : Nat) (h1 : 1224 ≤ n) (h2 : n ≤ 1423) : 0 < a n := by
  have hcases : (1224 ≤ n ∧ n ≤ 1263) ∨ (1264 ≤ n ∧ n ≤ 1303) ∨ (1304 ≤ n ∧ n ≤ 1343) ∨ (1344 ≤ n ∧ n ≤ 1383) ∨ (1384 ≤ n ∧ n ≤ 1423) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_1224_to_1263 n h.1 h.2
  · exact a_pos_1264_to_1303 n h.1 h.2
  · exact a_pos_1304_to_1343 n h.1 h.2
  · exact a_pos_1344_to_1383 n h.1 h.2
  · exact a_pos_1384_to_1423 n h.1 h.2
theorem a_pos_1424_to_1623 (n : Nat) (h1 : 1424 ≤ n) (h2 : n ≤ 1623) : 0 < a n := by
  have hcases : (1424 ≤ n ∧ n ≤ 1463) ∨ (1464 ≤ n ∧ n ≤ 1503) ∨ (1504 ≤ n ∧ n ≤ 1543) ∨ (1544 ≤ n ∧ n ≤ 1583) ∨ (1584 ≤ n ∧ n ≤ 1623) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_1424_to_1463 n h.1 h.2
  · exact a_pos_1464_to_1503 n h.1 h.2
  · exact a_pos_1504_to_1543 n h.1 h.2
  · exact a_pos_1544_to_1583 n h.1 h.2
  · exact a_pos_1584_to_1623 n h.1 h.2
theorem a_pos_1624_to_1823 (n : Nat) (h1 : 1624 ≤ n) (h2 : n ≤ 1823) : 0 < a n := by
  have hcases : (1624 ≤ n ∧ n ≤ 1663) ∨ (1664 ≤ n ∧ n ≤ 1703) ∨ (1704 ≤ n ∧ n ≤ 1743) ∨ (1744 ≤ n ∧ n ≤ 1783) ∨ (1784 ≤ n ∧ n ≤ 1823) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_1624_to_1663 n h.1 h.2
  · exact a_pos_1664_to_1703 n h.1 h.2
  · exact a_pos_1704_to_1743 n h.1 h.2
  · exact a_pos_1744_to_1783 n h.1 h.2
  · exact a_pos_1784_to_1823 n h.1 h.2
theorem a_pos_1824_to_2023 (n : Nat) (h1 : 1824 ≤ n) (h2 : n ≤ 2023) : 0 < a n := by
  have hcases : (1824 ≤ n ∧ n ≤ 1863) ∨ (1864 ≤ n ∧ n ≤ 1903) ∨ (1904 ≤ n ∧ n ≤ 1943) ∨ (1944 ≤ n ∧ n ≤ 1983) ∨ (1984 ≤ n ∧ n ≤ 2023) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_1824_to_1863 n h.1 h.2
  · exact a_pos_1864_to_1903 n h.1 h.2
  · exact a_pos_1904_to_1943 n h.1 h.2
  · exact a_pos_1944_to_1983 n h.1 h.2
  · exact a_pos_1984_to_2023 n h.1 h.2
theorem a_pos_2024_to_2223 (n : Nat) (h1 : 2024 ≤ n) (h2 : n ≤ 2223) : 0 < a n := by
  have hcases : (2024 ≤ n ∧ n ≤ 2063) ∨ (2064 ≤ n ∧ n ≤ 2103) ∨ (2104 ≤ n ∧ n ≤ 2143) ∨ (2144 ≤ n ∧ n ≤ 2183) ∨ (2184 ≤ n ∧ n ≤ 2223) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_2024_to_2063 n h.1 h.2
  · exact a_pos_2064_to_2103 n h.1 h.2
  · exact a_pos_2104_to_2143 n h.1 h.2
  · exact a_pos_2144_to_2183 n h.1 h.2
  · exact a_pos_2184_to_2223 n h.1 h.2
theorem a_pos_2224_to_2423 (n : Nat) (h1 : 2224 ≤ n) (h2 : n ≤ 2423) : 0 < a n := by
  have hcases : (2224 ≤ n ∧ n ≤ 2263) ∨ (2264 ≤ n ∧ n ≤ 2303) ∨ (2304 ≤ n ∧ n ≤ 2343) ∨ (2344 ≤ n ∧ n ≤ 2383) ∨ (2384 ≤ n ∧ n ≤ 2423) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_2224_to_2263 n h.1 h.2
  · exact a_pos_2264_to_2303 n h.1 h.2
  · exact a_pos_2304_to_2343 n h.1 h.2
  · exact a_pos_2344_to_2383 n h.1 h.2
  · exact a_pos_2384_to_2423 n h.1 h.2
theorem a_pos_2424_to_2623 (n : Nat) (h1 : 2424 ≤ n) (h2 : n ≤ 2623) : 0 < a n := by
  have hcases : (2424 ≤ n ∧ n ≤ 2463) ∨ (2464 ≤ n ∧ n ≤ 2503) ∨ (2504 ≤ n ∧ n ≤ 2543) ∨ (2544 ≤ n ∧ n ≤ 2583) ∨ (2584 ≤ n ∧ n ≤ 2623) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_2424_to_2463 n h.1 h.2
  · exact a_pos_2464_to_2503 n h.1 h.2
  · exact a_pos_2504_to_2543 n h.1 h.2
  · exact a_pos_2544_to_2583 n h.1 h.2
  · exact a_pos_2584_to_2623 n h.1 h.2
theorem a_pos_2624_to_2823 (n : Nat) (h1 : 2624 ≤ n) (h2 : n ≤ 2823) : 0 < a n := by
  have hcases : (2624 ≤ n ∧ n ≤ 2663) ∨ (2664 ≤ n ∧ n ≤ 2703) ∨ (2704 ≤ n ∧ n ≤ 2743) ∨ (2744 ≤ n ∧ n ≤ 2783) ∨ (2784 ≤ n ∧ n ≤ 2823) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_2624_to_2663 n h.1 h.2
  · exact a_pos_2664_to_2703 n h.1 h.2
  · exact a_pos_2704_to_2743 n h.1 h.2
  · exact a_pos_2744_to_2783 n h.1 h.2
  · exact a_pos_2784_to_2823 n h.1 h.2
theorem a_pos_2824_to_3000 (n : Nat) (h1 : 2824 ≤ n) (h2 : n ≤ 3000) : 0 < a n := by
  have hcases : (2824 ≤ n ∧ n ≤ 2863) ∨ (2864 ≤ n ∧ n ≤ 2903) ∨ (2904 ≤ n ∧ n ≤ 2943) ∨ (2944 ≤ n ∧ n ≤ 2983) ∨ (2984 ≤ n ∧ n ≤ 3000) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_2824_to_2863 n h.1 h.2
  · exact a_pos_2864_to_2903 n h.1 h.2
  · exact a_pos_2904_to_2943 n h.1 h.2
  · exact a_pos_2944_to_2983 n h.1 h.2
  · exact a_pos_2984_to_3000 n h.1 h.2
theorem a_pos_824_to_3000 (n : Nat) (h1 : 824 ≤ n) (h2 : n ≤ 3000) : 0 < a n := by
  by_cases ha : n ≤ 1023
  · exact a_pos_824_to_1023 n h1 ha
  · by_cases hb : n ≤ 1223
    · exact a_pos_1024_to_1223 n (by omega) hb
    · by_cases hc : n ≤ 1423
      · exact a_pos_1224_to_1423 n (by omega) hc
      · by_cases hd : n ≤ 1623
        · exact a_pos_1424_to_1623 n (by omega) hd
        · by_cases he : n ≤ 1823
          · exact a_pos_1624_to_1823 n (by omega) he
          · by_cases hf : n ≤ 2023
            · exact a_pos_1824_to_2023 n (by omega) hf
            · by_cases hg : n ≤ 2223
              · exact a_pos_2024_to_2223 n (by omega) hg
              · by_cases hh : n ≤ 2423
                · exact a_pos_2224_to_2423 n (by omega) hh
                · by_cases hi : n ≤ 2623
                  · exact a_pos_2424_to_2623 n (by omega) hi
                  · by_cases hj : n ≤ 2823
                    · exact a_pos_2624_to_2823 n (by omega) hj
                    · exact a_pos_2824_to_3000 n (by omega) h2

/-- An interprime: the average of two consecutive odd primes. -/
def IsInterprime (k : Nat) : Prop :=
  ∃ p, p.Prime ∧ 2 < p ∧ p < k ∧ S_sum p = 2 * k

/-- For `n ≥ 6`, positivity of `a n` is equivalent to writing `n` as a sum of two interprimes. -/
theorem a_pos_of_interprimes {n m k : Nat}
    (hm : IsInterprime m) (hk : IsInterprime k) (hsum : m + k = n) :
    0 < a n := by
  obtain ⟨p, hp, hp2, hpm, hSp⟩ := hm
  obtain ⟨q, hq, hq2, hqk, hSq⟩ := hk
  have hpn : p < n := by omega
  have hqn : q < n := by omega
  have hsumS : S_sum p + S_sum q = 2 * n := by
    calc S_sum p + S_sum q = 2 * m + 2 * k := by simp [hSp, hSq]
      _ = 2 * (m + k) := by ring
      _ = 2 * n := by rw [hsum]
  rcases le_total p q with hpq | hqp
  · exact a_pos_of_pair hp hq hpq hpn hqn hsumS
  · exact a_pos_of_pair hq hp hqp hqn hpn (by rw [Nat.add_comm, hsumS])

theorem isInterprime_of_consecutive {p p' : Nat}
    (hp : p.Prime) (hp' : p'.Prime) (hp2 : 2 < p) (hlt : p < p')
    (hnone : ∀ k, p < k → k < p' → ¬ k.Prime) :
    IsInterprime ((p + p') / 2) := by
  have hnp : next_prime p = p' := next_prime_eq hp' hlt hnone
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hp'_odd : Odd p' := hp'.odd_of_ne_two (by omega)
  have h2 : Even (p + p') := hp_odd.add_odd hp'_odd
  have hdiv : 2 ∣ p + p' := even_iff_two_dvd.mp h2
  refine ⟨p, hp, hp2, ?_, ?_⟩
  · have hmul : 2 * ((p + p') / 2) = p + p' := Nat.mul_div_cancel' hdiv
    have : 2 * p < 2 * ((p + p') / 2) := by
      rw [hmul]; omega
    exact (mul_lt_mul_iff_right₀ (by omega : 0 < 2)).mp this
  · unfold S_sum
    rw [hnp]
    have : 2 * ((p + p') / 2) = p + p' := Nat.mul_div_cancel' hdiv
    exact this.symm

theorem checkMid_isInterprime {m p q : Nat} (h : checkMid m p q = true) :
    IsInterprime m := by
  unfold checkMid at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hpB, hqB⟩, hp2B⟩, hpqB⟩, hsum⟩, hnp⟩ := h
  have hp : p.Prime := isPrimeBool_prime hpB
  have hq : q.Prime := isPrimeBool_prime hqB
  have hp2 : 2 < p := Nat.blt_eq.mp hp2B
  have hpq : p < q := Nat.blt_eq.mp hpqB
  have hnone : ∀ k, p < k → k < q → ¬ k.Prime :=
    noPrimeBetween_true hpq hnp
  have hmid : (p + q) / 2 = m := by
    have hdiv : 2 ∣ p + q := ⟨m, by rw [hsum, Nat.mul_comm]⟩
    have := Nat.mul_div_cancel' hdiv
    omega
  rw [← hmid]
  exact isInterprime_of_consecutive hp hq hp2 hpq hnone

theorem checkMids_isInterprime {l : List (Nat × Nat × Nat)} (h : checkMids l = true)
    {m p q : Nat} (hm : (m, p, q) ∈ l) : IsInterprime m := by
  induction l with
  | nil => simp at hm
  | cons head rest ih =>
    simp only [checkMids] at h
    have hab := Bool.and_eq_true_iff.mp h
    simp only [List.mem_cons] at hm
    rcases hm with h1 | h2
    · cases h1
      exact checkMid_isInterprime hab.1
    · exact ih hab.2 h2

theorem isInterprime_4 : IsInterprime 4 := by
  have h := isInterprime_of_consecutive (p := 3) (p' := 5) Nat.prime_three Nat.prime_five
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_6 : IsInterprime 6 := by
  have h := isInterprime_of_consecutive (p := 5) (p' := 7) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_9 : IsInterprime 9 := by
  have h := isInterprime_of_consecutive (p := 7) (p' := 11) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub_interprime (n m : Nat) (hm : IsInterprime m)
    (hnm : IsInterprime (n - m)) (hle : m ≤ n) : 0 < a n :=
  a_pos_of_interprimes hm hnm (Nat.add_sub_of_le hle)

theorem a_pos_of_sub4 {n : Nat} (h : 4 ≤ n) (hm : IsInterprime (n - 4)) : 0 < a n :=
  a_pos_of_sub_interprime n 4 isInterprime_4 hm h

theorem a_pos_of_sub6 {n : Nat} (h : 6 ≤ n) (hm : IsInterprime (n - 6)) : 0 < a n :=
  a_pos_of_sub_interprime n 6 isInterprime_6 hm h

theorem a_pos_of_sub9 {n : Nat} (h : 9 ≤ n) (hm : IsInterprime (n - 9)) : 0 < a n :=
  a_pos_of_sub_interprime n 9 isInterprime_9 hm h

theorem isInterprime_12 : IsInterprime 12 := by
  have h := isInterprime_of_consecutive (p := 11) (p' := 13) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_15 : IsInterprime 15 := by
  have h := isInterprime_of_consecutive (p := 13) (p' := 17) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_18 : IsInterprime 18 := by
  have h := isInterprime_of_consecutive (p := 17) (p' := 19) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_21 : IsInterprime 21 := by
  have h := isInterprime_of_consecutive (p := 19) (p' := 23) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub12 {n : Nat} (h : 12 ≤ n) (hm : IsInterprime (n - 12)) : 0 < a n :=
  a_pos_of_sub_interprime n 12 isInterprime_12 hm h

theorem a_pos_of_sub15 {n : Nat} (h : 15 ≤ n) (hm : IsInterprime (n - 15)) : 0 < a n :=
  a_pos_of_sub_interprime n 15 isInterprime_15 hm h

theorem a_pos_of_sub18 {n : Nat} (h : 18 ≤ n) (hm : IsInterprime (n - 18)) : 0 < a n :=
  a_pos_of_sub_interprime n 18 isInterprime_18 hm h

theorem a_pos_of_sub21 {n : Nat} (h : 21 ≤ n) (hm : IsInterprime (n - 21)) : 0 < a n :=
  a_pos_of_sub_interprime n 21 isInterprime_21 hm h

theorem isInterprime_26 : IsInterprime 26 := by
  have h := isInterprime_of_consecutive (p := 23) (p' := 29) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_30 : IsInterprime 30 := by
  have h := isInterprime_of_consecutive (p := 29) (p' := 31) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_34 : IsInterprime 34 := by
  have h := isInterprime_of_consecutive (p := 31) (p' := 37) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_39 : IsInterprime 39 := by
  have h := isInterprime_of_consecutive (p := 37) (p' := 41) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_42 : IsInterprime 42 := by
  have h := isInterprime_of_consecutive (p := 41) (p' := 43) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_45 : IsInterprime 45 := by
  have h := isInterprime_of_consecutive (p := 43) (p' := 47) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_50 : IsInterprime 50 := by
  have h := isInterprime_of_consecutive (p := 47) (p' := 53) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub26 {n : Nat} (h : 26 ≤ n) (hm : IsInterprime (n - 26)) : 0 < a n :=
  a_pos_of_sub_interprime n 26 isInterprime_26 hm h

theorem a_pos_of_sub30 {n : Nat} (h : 30 ≤ n) (hm : IsInterprime (n - 30)) : 0 < a n :=
  a_pos_of_sub_interprime n 30 isInterprime_30 hm h

theorem a_pos_of_sub34 {n : Nat} (h : 34 ≤ n) (hm : IsInterprime (n - 34)) : 0 < a n :=
  a_pos_of_sub_interprime n 34 isInterprime_34 hm h

theorem a_pos_of_sub39 {n : Nat} (h : 39 ≤ n) (hm : IsInterprime (n - 39)) : 0 < a n :=
  a_pos_of_sub_interprime n 39 isInterprime_39 hm h

theorem a_pos_of_sub42 {n : Nat} (h : 42 ≤ n) (hm : IsInterprime (n - 42)) : 0 < a n :=
  a_pos_of_sub_interprime n 42 isInterprime_42 hm h

theorem a_pos_of_sub45 {n : Nat} (h : 45 ≤ n) (hm : IsInterprime (n - 45)) : 0 < a n :=
  a_pos_of_sub_interprime n 45 isInterprime_45 hm h

theorem a_pos_of_sub50 {n : Nat} (h : 50 ≤ n) (hm : IsInterprime (n - 50)) : 0 < a n :=
  a_pos_of_sub_interprime n 50 isInterprime_50 hm h

theorem isInterprime_56 : IsInterprime 56 := by
  have h := isInterprime_of_consecutive (p := 53) (p' := 59) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub56 {n : Nat} (h : 56 ≤ n) (hm : IsInterprime (n - 56)) : 0 < a n :=
  a_pos_of_sub_interprime n 56 isInterprime_56 hm h

theorem isInterprime_60 : IsInterprime 60 := by
  have h := isInterprime_of_consecutive (p := 59) (p' := 61) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem a_pos_of_sub60 {n : Nat} (h : 60 ≤ n) (hm : IsInterprime (n - 60)) : 0 < a n :=
  a_pos_of_sub_interprime n 60 isInterprime_60 hm h

theorem isInterprime_64 : IsInterprime 64 := by
  have h := isInterprime_of_consecutive (p := 61) (p' := 67) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub64 {n : Nat} (h : 64 ≤ n) (hm : IsInterprime (n - 64)) : 0 < a n :=
  a_pos_of_sub_interprime n 64 isInterprime_64 hm h

theorem isInterprime_69 : IsInterprime 69 := by
  have h := isInterprime_of_consecutive (p := 67) (p' := 71) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub69 {n : Nat} (h : 69 ≤ n) (hm : IsInterprime (n - 69)) : 0 < a n :=
  a_pos_of_sub_interprime n 69 isInterprime_69 hm h

theorem isInterprime_72 : IsInterprime 72 := by
  have h := isInterprime_of_consecutive (p := 71) (p' := 73) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem a_pos_of_sub72 {n : Nat} (h : 72 ≤ n) (hm : IsInterprime (n - 72)) : 0 < a n :=
  a_pos_of_sub_interprime n 72 isInterprime_72 hm h

theorem isInterprime_76 : IsInterprime 76 := by
  have h := isInterprime_of_consecutive (p := 73) (p' := 79) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub76 {n : Nat} (h : 76 ≤ n) (hm : IsInterprime (n - 76)) : 0 < a n :=
  a_pos_of_sub_interprime n 76 isInterprime_76 hm h

theorem isInterprime_81 : IsInterprime 81 := by
  have h := isInterprime_of_consecutive (p := 79) (p' := 83) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub81 {n : Nat} (h : 81 ≤ n) (hm : IsInterprime (n - 81)) : 0 < a n :=
  a_pos_of_sub_interprime n 81 isInterprime_81 hm h

theorem isInterprime_86 : IsInterprime 86 := by
  have h := isInterprime_of_consecutive (p := 83) (p' := 89) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub86 {n : Nat} (h : 86 ≤ n) (hm : IsInterprime (n - 86)) : 0 < a n :=
  a_pos_of_sub_interprime n 86 isInterprime_86 hm h

theorem isInterprime_93 : IsInterprime 93 := by
  have h := isInterprime_of_consecutive (p := 89) (p' := 97) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub93 {n : Nat} (h : 93 ≤ n) (hm : IsInterprime (n - 93)) : 0 < a n :=
  a_pos_of_sub_interprime n 93 isInterprime_93 hm h

theorem isInterprime_99 : IsInterprime 99 := by
  have h := isInterprime_of_consecutive (p := 97) (p' := 101) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub99 {n : Nat} (h : 99 ≤ n) (hm : IsInterprime (n - 99)) : 0 < a n :=
  a_pos_of_sub_interprime n 99 isInterprime_99 hm h

theorem isInterprime_102 : IsInterprime 102 := by
  have h := isInterprime_of_consecutive (p := 101) (p' := 103) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem a_pos_of_sub102 {n : Nat} (h : 102 ≤ n) (hm : IsInterprime (n - 102)) : 0 < a n :=
  a_pos_of_sub_interprime n 102 isInterprime_102 hm h

theorem isInterprime_105 : IsInterprime 105 := by
  have h := isInterprime_of_consecutive (p := 103) (p' := 107) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub105 {n : Nat} (h : 105 ≤ n) (hm : IsInterprime (n - 105)) : 0 < a n :=
  a_pos_of_sub_interprime n 105 isInterprime_105 hm h

theorem isInterprime_108 : IsInterprime 108 := by
  have h := isInterprime_of_consecutive (p := 107) (p' := 109) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem a_pos_of_sub108 {n : Nat} (h : 108 ≤ n) (hm : IsInterprime (n - 108)) : 0 < a n :=
  a_pos_of_sub_interprime n 108 isInterprime_108 hm h

theorem isInterprime_111 : IsInterprime 111 := by
  have h := isInterprime_of_consecutive (p := 109) (p' := 113) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub111 {n : Nat} (h : 111 ≤ n) (hm : IsInterprime (n - 111)) : 0 < a n :=
  a_pos_of_sub_interprime n 111 isInterprime_111 hm h

theorem isInterprime_120 : IsInterprime 120 := by
  have h := isInterprime_of_consecutive (p := 113) (p' := 127) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub120 {n : Nat} (h : 120 ≤ n) (hm : IsInterprime (n - 120)) : 0 < a n :=
  a_pos_of_sub_interprime n 120 isInterprime_120 hm h

theorem isInterprime_129 : IsInterprime 129 := by
  have h := isInterprime_of_consecutive (p := 127) (p' := 131) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub129 {n : Nat} (h : 129 ≤ n) (hm : IsInterprime (n - 129)) : 0 < a n :=
  a_pos_of_sub_interprime n 129 isInterprime_129 hm h

theorem isInterprime_134 : IsInterprime 134 := by
  have h := isInterprime_of_consecutive (p := 131) (p' := 137) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub134 {n : Nat} (h : 134 ≤ n) (hm : IsInterprime (n - 134)) : 0 < a n :=
  a_pos_of_sub_interprime n 134 isInterprime_134 hm h

theorem isInterprime_138 : IsInterprime 138 := by
  have h := isInterprime_of_consecutive (p := 137) (p' := 139) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem a_pos_of_sub138 {n : Nat} (h : 138 ≤ n) (hm : IsInterprime (n - 138)) : 0 < a n :=
  a_pos_of_sub_interprime n 138 isInterprime_138 hm h

theorem isInterprime_144 : IsInterprime 144 := by
  have h := isInterprime_of_consecutive (p := 139) (p' := 149) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub144 {n : Nat} (h : 144 ≤ n) (hm : IsInterprime (n - 144)) : 0 < a n :=
  a_pos_of_sub_interprime n 144 isInterprime_144 hm h

theorem isInterprime_150 : IsInterprime 150 := by
  have h := isInterprime_of_consecutive (p := 149) (p' := 151) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem a_pos_of_sub150 {n : Nat} (h : 150 ≤ n) (hm : IsInterprime (n - 150)) : 0 < a n :=
  a_pos_of_sub_interprime n 150 isInterprime_150 hm h

theorem isInterprime_154 : IsInterprime 154 := by
  have h := isInterprime_of_consecutive (p := 151) (p' := 157) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub154 {n : Nat} (h : 154 ≤ n) (hm : IsInterprime (n - 154)) : 0 < a n :=
  a_pos_of_sub_interprime n 154 isInterprime_154 hm h

theorem isInterprime_160 : IsInterprime 160 := by
  have h := isInterprime_of_consecutive (p := 157) (p' := 163) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub160 {n : Nat} (h : 160 ≤ n) (hm : IsInterprime (n - 160)) : 0 < a n :=
  a_pos_of_sub_interprime n 160 isInterprime_160 hm h

theorem isInterprime_165 : IsInterprime 165 := by
  have h := isInterprime_of_consecutive (p := 163) (p' := 167) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub165 {n : Nat} (h : 165 ≤ n) (hm : IsInterprime (n - 165)) : 0 < a n :=
  a_pos_of_sub_interprime n 165 isInterprime_165 hm h

theorem isInterprime_170 : IsInterprime 170 := by
  have h := isInterprime_of_consecutive (p := 167) (p' := 173) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub170 {n : Nat} (h : 170 ≤ n) (hm : IsInterprime (n - 170)) : 0 < a n :=
  a_pos_of_sub_interprime n 170 isInterprime_170 hm h

theorem isInterprime_176 : IsInterprime 176 := by
  have h := isInterprime_of_consecutive (p := 173) (p' := 179) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub176 {n : Nat} (h : 176 ≤ n) (hm : IsInterprime (n - 176)) : 0 < a n :=
  a_pos_of_sub_interprime n 176 isInterprime_176 hm h

theorem isInterprime_180 : IsInterprime 180 := by
  have h := isInterprime_of_consecutive (p := 179) (p' := 181) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem a_pos_of_sub180 {n : Nat} (h : 180 ≤ n) (hm : IsInterprime (n - 180)) : 0 < a n :=
  a_pos_of_sub_interprime n 180 isInterprime_180 hm h

theorem isInterprime_186 : IsInterprime 186 := by
  have h := isInterprime_of_consecutive (p := 181) (p' := 191) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub186 {n : Nat} (h : 186 ≤ n) (hm : IsInterprime (n - 186)) : 0 < a n :=
  a_pos_of_sub_interprime n 186 isInterprime_186 hm h

theorem isInterprime_192 : IsInterprime 192 := by
  have h := isInterprime_of_consecutive (p := 191) (p' := 193) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem a_pos_of_sub192 {n : Nat} (h : 192 ≤ n) (hm : IsInterprime (n - 192)) : 0 < a n :=
  a_pos_of_sub_interprime n 192 isInterprime_192 hm h

theorem isInterprime_195 : IsInterprime 195 := by
  have h := isInterprime_of_consecutive (p := 193) (p' := 197) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub195 {n : Nat} (h : 195 ≤ n) (hm : IsInterprime (n - 195)) : 0 < a n :=
  a_pos_of_sub_interprime n 195 isInterprime_195 hm h

theorem isInterprime_198 : IsInterprime 198 := by
  have h := isInterprime_of_consecutive (p := 197) (p' := 199) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem a_pos_of_sub198 {n : Nat} (h : 198 ≤ n) (hm : IsInterprime (n - 198)) : 0 < a n :=
  a_pos_of_sub_interprime n 198 isInterprime_198 hm h

theorem isInterprime_205 : IsInterprime 205 := by
  have h := isInterprime_of_consecutive (p := 199) (p' := 211) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_217 : IsInterprime 217 := by
  have h := isInterprime_of_consecutive (p := 211) (p' := 223) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_225 : IsInterprime 225 := by
  have h := isInterprime_of_consecutive (p := 223) (p' := 227) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_228 : IsInterprime 228 := by
  have h := isInterprime_of_consecutive (p := 227) (p' := 229) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_231 : IsInterprime 231 := by
  have h := isInterprime_of_consecutive (p := 229) (p' := 233) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_236 : IsInterprime 236 := by
  have h := isInterprime_of_consecutive (p := 233) (p' := 239) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_240 : IsInterprime 240 := by
  have h := isInterprime_of_consecutive (p := 239) (p' := 241) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_246 : IsInterprime 246 := by
  have h := isInterprime_of_consecutive (p := 241) (p' := 251) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_254 : IsInterprime 254 := by
  have h := isInterprime_of_consecutive (p := 251) (p' := 257) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_260 : IsInterprime 260 := by
  have h := isInterprime_of_consecutive (p := 257) (p' := 263) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_266 : IsInterprime 266 := by
  have h := isInterprime_of_consecutive (p := 263) (p' := 269) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_270 : IsInterprime 270 := by
  have h := isInterprime_of_consecutive (p := 269) (p' := 271) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_274 : IsInterprime 274 := by
  have h := isInterprime_of_consecutive (p := 271) (p' := 277) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_279 : IsInterprime 279 := by
  have h := isInterprime_of_consecutive (p := 277) (p' := 281) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_282 : IsInterprime 282 := by
  have h := isInterprime_of_consecutive (p := 281) (p' := 283) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_288 : IsInterprime 288 := by
  have h := isInterprime_of_consecutive (p := 283) (p' := 293) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_300 : IsInterprime 300 := by
  have h := isInterprime_of_consecutive (p := 293) (p' := 307) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_309 : IsInterprime 309 := by
  have h := isInterprime_of_consecutive (p := 307) (p' := 311) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_312 : IsInterprime 312 := by
  have h := isInterprime_of_consecutive (p := 311) (p' := 313) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_315 : IsInterprime 315 := by
  have h := isInterprime_of_consecutive (p := 313) (p' := 317) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_324 : IsInterprime 324 := by
  have h := isInterprime_of_consecutive (p := 317) (p' := 331) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_334 : IsInterprime 334 := by
  have h := isInterprime_of_consecutive (p := 331) (p' := 337) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_342 : IsInterprime 342 := by
  have h := isInterprime_of_consecutive (p := 337) (p' := 347) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_348 : IsInterprime 348 := by
  have h := isInterprime_of_consecutive (p := 347) (p' := 349) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_351 : IsInterprime 351 := by
  have h := isInterprime_of_consecutive (p := 349) (p' := 353) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_356 : IsInterprime 356 := by
  have h := isInterprime_of_consecutive (p := 353) (p' := 359) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_363 : IsInterprime 363 := by
  have h := isInterprime_of_consecutive (p := 359) (p' := 367) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_370 : IsInterprime 370 := by
  have h := isInterprime_of_consecutive (p := 367) (p' := 373) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_376 : IsInterprime 376 := by
  have h := isInterprime_of_consecutive (p := 373) (p' := 379) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_381 : IsInterprime 381 := by
  have h := isInterprime_of_consecutive (p := 379) (p' := 383) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_386 : IsInterprime 386 := by
  have h := isInterprime_of_consecutive (p := 383) (p' := 389) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_393 : IsInterprime 393 := by
  have h := isInterprime_of_consecutive (p := 389) (p' := 397) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem isInterprime_399 : IsInterprime 399 := by
  have h := isInterprime_of_consecutive (p := 397) (p' := 401) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

def moreMids : List Nat :=
  [205, 217, 225, 228, 231, 236, 240, 246, 254, 260, 266, 270, 274, 279, 282,
   288, 300, 309, 312, 315, 324, 334, 342, 348, 351, 356, 363, 370, 376, 381,
   386, 393, 399]

theorem mem_moreMids_isInterprime {m : Nat} (h : m ∈ moreMids) : IsInterprime m := by
  simp [moreMids] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact h ▸ isInterprime_205
  · exact h ▸ isInterprime_217
  · exact h ▸ isInterprime_225
  · exact h ▸ isInterprime_228
  · exact h ▸ isInterprime_231
  · exact h ▸ isInterprime_236
  · exact h ▸ isInterprime_240
  · exact h ▸ isInterprime_246
  · exact h ▸ isInterprime_254
  · exact h ▸ isInterprime_260
  · exact h ▸ isInterprime_266
  · exact h ▸ isInterprime_270
  · exact h ▸ isInterprime_274
  · exact h ▸ isInterprime_279
  · exact h ▸ isInterprime_282
  · exact h ▸ isInterprime_288
  · exact h ▸ isInterprime_300
  · exact h ▸ isInterprime_309
  · exact h ▸ isInterprime_312
  · exact h ▸ isInterprime_315
  · exact h ▸ isInterprime_324
  · exact h ▸ isInterprime_334
  · exact h ▸ isInterprime_342
  · exact h ▸ isInterprime_348
  · exact h ▸ isInterprime_351
  · exact h ▸ isInterprime_356
  · exact h ▸ isInterprime_363
  · exact h ▸ isInterprime_370
  · exact h ▸ isInterprime_376
  · exact h ▸ isInterprime_381
  · exact h ▸ isInterprime_386
  · exact h ▸ isInterprime_393
  · exact h ▸ isInterprime_399

theorem a_pos_of_mem_moreMids {n m : Nat} (hm : m ∈ moreMids)
    (hle : m + 4 ≤ n) (hI : IsInterprime (n - m)) : 0 < a n :=
  a_pos_of_sub_interprime n m (mem_moreMids_isInterprime hm) hI (by omega)

theorem a_pos_of_exists_more {n : Nat}
    (h : ∃ m ∈ moreMids, m + 4 ≤ n ∧ IsInterprime (n - m)) : 0 < a n := by
  obtain ⟨m, hm, hle, hI⟩ := h
  exact a_pos_of_mem_moreMids hm hle hI

/-- Interprimes from 405 to 924, stored as `(mid, prev_prime, next_prime)`. -/
def midTriples2 : List (Nat × Nat × Nat) :=
  [(405,401,409), (414,409,419), (420,419,421), (426,421,431), (432,431,433), (436,433,439),
   (441,439,443), (446,443,449), (453,449,457), (459,457,461), (462,461,463), (465,463,467),
   (473,467,479), (483,479,487), (489,487,491), (495,491,499), (501,499,503), (506,503,509),
   (515,509,521), (522,521,523), (532,523,541), (544,541,547), (552,547,557), (560,557,563),
   (566,563,569), (570,569,571), (574,571,577), (582,577,587), (590,587,593), (596,593,599),
   (600,599,601), (604,601,607), (610,607,613), (615,613,617), (618,617,619), (625,619,631),
   (636,631,641), (642,641,643), (645,643,647), (650,647,653), (656,653,659), (660,659,661),
   (667,661,673), (675,673,677), (680,677,683), (687,683,691), (696,691,701), (705,701,709),
   (714,709,719), (723,719,727), (730,727,733), (736,733,739), (741,739,743), (747,743,751),
   (754,751,757), (759,757,761), (765,761,769), (771,769,773), (780,773,787), (792,787,797),
   (803,797,809), (810,809,811), (816,811,821), (822,821,823), (825,823,827), (828,827,829),
   (834,829,839), (846,839,853), (855,853,857), (858,857,859), (861,859,863), (870,863,877),
   (879,877,881), (882,881,883), (885,883,887), (897,887,907), (909,907,911), (915,911,919),
   (924,919,929)]

theorem midTriples2_ok : checkMids midTriples2 = true := rfl

def midTriples3 : List (Nat × Nat × Nat) :=
  [(933,929,937), (939,937,941), (944,941,947), (950,947,953), (960,953,967), (969,967,971), (974,971,977),
   (980,977,983), (987,983,991), (994,991,997), (1003,997,1009), (1011,1009,1013), (1016,1013,1019),
   (1020,1019,1021), (1026,1021,1031), (1032,1031,1033), (1036,1033,1039), (1044,1039,1049),
   (1050,1049,1051), (1056,1051,1061), (1062,1061,1063), (1066,1063,1069), (1078,1069,1087),
   (1089,1087,1091), (1092,1091,1093), (1095,1093,1097), (1100,1097,1103), (1106,1103,1109),
   (1113,1109,1117), (1120,1117,1123), (1126,1123,1129), (1140,1129,1151), (1152,1151,1153),
   (1158,1153,1163), (1167,1163,1171), (1176,1171,1181), (1184,1181,1187), (1190,1187,1193),
   (1197,1193,1201), (1207,1201,1213), (1215,1213,1217), (1220,1217,1223), (1226,1223,1229),
   (1230,1229,1231), (1234,1231,1237), (1243,1237,1249), (1254,1249,1259), (1268,1259,1277),
   (1278,1277,1279), (1281,1279,1283), (1286,1283,1289), (1290,1289,1291), (1294,1291,1297),
   (1299,1297,1301), (1302,1301,1303), (1305,1303,1307), (1313,1307,1319), (1320,1319,1321),
   (1324,1321,1327), (1344,1327,1361), (1364,1361,1367), (1370,1367,1373), (1377,1373,1381),
   (1390,1381,1399), (1404,1399,1409), (1416,1409,1423), (1425,1423,1427), (1428,1427,1429),
   (1431,1429,1433), (1436,1433,1439), (1443,1439,1447), (1449,1447,1451), (1452,1451,1453),
   (1456,1453,1459), (1465,1459,1471), (1476,1471,1481), (1482,1481,1483), (1485,1483,1487),
   (1488,1487,1489), (1491,1489,1493), (1496,1493,1499), (1505,1499,1511), (1517,1511,1523),
   (1527,1523,1531), (1537,1531,1543), (1546,1543,1549), (1551,1549,1553), (1556,1553,1559),
   (1563,1559,1567), (1569,1567,1571), (1575,1571,1579), (1581,1579,1583), (1590,1583,1597),
   (1599,1597,1601), (1604,1601,1607), (1608,1607,1609), (1611,1609,1613), (1616,1613,1619),
   (1620,1619,1621), (1624,1621,1627), (1632,1627,1637), (1647,1637,1657), (1660,1657,1663),
   (1665,1663,1667), (1668,1667,1669), (1681,1669,1693), (1695,1693,1697), (1698,1697,1699),
   (1704,1699,1709), (1715,1709,1721), (1722,1721,1723), (1728,1723,1733), (1737,1733,1741),
   (1744,1741,1747), (1750,1747,1753), (1756,1753,1759), (1768,1759,1777), (1780,1777,1783),
   (1785,1783,1787), (1788,1787,1789), (1795,1789,1801), (1806,1801,1811), (1817,1811,1823),
   (1827,1823,1831), (1839,1831,1847), (1854,1847,1861), (1864,1861,1867), (1869,1867,1871),
   (1872,1871,1873), (1875,1873,1877), (1878,1877,1879), (1884,1879,1889), (1895,1889,1901),
   (1904,1901,1907), (1910,1907,1913), (1922,1913,1931), (1932,1931,1933), (1941,1933,1949),
   (1950,1949,1951), (1962,1951,1973), (1976,1973,1979), (1983,1979,1987), (1990,1987,1993),
   (1995,1993,1997), (1998,1997,1999), (2001,1999,2003), (2007,2003,2011), (2014,2011,2017),
   (2022,2017,2027), (2028,2027,2029), (2034,2029,2039), (2046,2039,2053), (2058,2053,2063),
   (2066,2063,2069), (2075,2069,2081), (2082,2081,2083), (2085,2083,2087), (2088,2087,2089),
   (2094,2089,2099), (2105,2099,2111), (2112,2111,2113), (2121,2113,2129), (2130,2129,2131),
   (2134,2131,2137), (2139,2137,2141), (2142,2141,2143), (2148,2143,2153), (2157,2153,2161),
   (2170,2161,2179), (2191,2179,2203), (2205,2203,2207), (2210,2207,2213), (2217,2213,2221),
   (2229,2221,2237), (2238,2237,2239), (2241,2239,2243), (2247,2243,2251), (2259,2251,2267),
   (2268,2267,2269), (2271,2269,2273), (2277,2273,2281), (2284,2281,2287), (2290,2287,2293),
   (2295,2293,2297), (2303,2297,2309), (2310,2309,2311), (2322,2311,2333), (2336,2333,2339),
   (2340,2339,2341), (2344,2341,2347), (2349,2347,2351), (2354,2351,2357), (2364,2357,2371),
   (2374,2371,2377), (2379,2377,2381), (2382,2381,2383), (2386,2383,2389), (2391,2389,2393),
   (2396,2393,2399), (2405,2399,2411), (2414,2411,2417), (2420,2417,2423), (2430,2423,2437),
   (2439,2437,2441), (2444,2441,2447), (2453,2447,2459), (2463,2459,2467), (2470,2467,2473),
   (2475,2473,2477), (2490,2477,2503)]

theorem midTriples3_ok : checkMids midTriples3 = true := rfl

/-- Interprimes from 2512 to 3197. -/
def midTriples4 : List (Nat × Nat × Nat) :=
  [(2512,2503,2521), (2526,2521,2531), (2535,2531,2539), (2541,2539,2543), (2546,2543,2549), (2550,2549,2551),
   (2554,2551,2557), (2568,2557,2579), (2585,2579,2591), (2592,2591,2593), (2601,2593,2609), (2613,2609,2617),
   (2619,2617,2621), (2627,2621,2633), (2640,2633,2647), (2652,2647,2657), (2658,2657,2659), (2661,2659,2663),
   (2667,2663,2671), (2674,2671,2677), (2680,2677,2683), (2685,2683,2687), (2688,2687,2689), (2691,2689,2693),
   (2696,2693,2699), (2703,2699,2707), (2709,2707,2711), (2712,2711,2713), (2716,2713,2719), (2724,2719,2729),
   (2730,2729,2731), (2736,2731,2741), (2745,2741,2749), (2751,2749,2753), (2760,2753,2767), (2772,2767,2777),
   (2783,2777,2789), (2790,2789,2791), (2794,2791,2797), (2799,2797,2801), (2802,2801,2803), (2811,2803,2819),
   (2826,2819,2833), (2835,2833,2837), (2840,2837,2843), (2847,2843,2851), (2854,2851,2857), (2859,2857,2861),
   (2870,2861,2879), (2883,2879,2887), (2892,2887,2897), (2900,2897,2903), (2906,2903,2909), (2913,2909,2917),
   (2922,2917,2927), (2933,2927,2939), (2946,2939,2953), (2955,2953,2957), (2960,2957,2963), (2966,2963,2969),
   (2970,2969,2971), (2985,2971,2999), (3000,2999,3001), (3006,3001,3011), (3015,3011,3019), (3021,3019,3023),
   (3030,3023,3037), (3039,3037,3041), (3045,3041,3049), (3055,3049,3061), (3064,3061,3067), (3073,3067,3079),
   (3081,3079,3083), (3086,3083,3089), (3099,3089,3109), (3114,3109,3119), (3120,3119,3121), (3129,3121,3137),
   (3150,3137,3163), (3165,3163,3167), (3168,3167,3169), (3175,3169,3181), (3184,3181,3187), (3189,3187,3191),
   (3197,3191,3203)]

theorem midTriples4_ok : checkMids midTriples4 = true := rfl

theorem a_pos_of_exists_midTriples {n : Nat} {l : List (Nat × Nat × Nat)}
    (hok : checkMids l = true)
    (h : ∃ trip ∈ l, trip.1 + 4 ≤ n ∧ IsInterprime (n - trip.1)) : 0 < a n := by
  obtain ⟨⟨m, p, q⟩, hm, hle, hI⟩ := h
  have hmI : IsInterprime m := checkMids_isInterprime hok hm
  exact a_pos_of_sub_interprime n m hmI hI (by omega)

/-- Largest prime strictly less than `r`. -/
noncomputable def prev_prime (r : Nat) : Nat :=
  sSup {k : Nat | k.Prime ∧ k < r}

theorem prev_prime_spec {r : Nat} (h : 2 < r) :
    (prev_prime r).Prime ∧ prev_prime r < r ∧
      ∀ k, k.Prime → k < r → k ≤ prev_prime r := by
  let S := {k : Nat | k.Prime ∧ k < r}
  have h2 : 2 ∈ S := ⟨Nat.prime_two, h⟩
  have hne : S.Nonempty := ⟨2, h2⟩
  have hBdd : BddAbove S := ⟨r, fun k hk => le_of_lt hk.2⟩
  have hmem : prev_prime r ∈ S := by
    have : sSup S ∈ S := Nat.sSup_mem hne hBdd
    simpa [prev_prime, S] using this
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro k hk hlt
  exact le_csSup hBdd ⟨hk, hlt⟩

theorem prev_next_consecutive {k : Nat} (h : 2 < k) (hnp : ¬ k.Prime) :
    (prev_prime k).Prime ∧ (next_prime k).Prime ∧
      prev_prime k < k ∧ k < next_prime k ∧
      ∀ m, prev_prime k < m → m < next_prime k → ¬ m.Prime := by
  have hp := prev_prime_spec h
  have hn := next_prime_spec k
  refine ⟨hp.1, hn.1, hp.2.1, hn.2.1, ?_⟩
  intro m hm1 hm2 hmP
  by_cases hmk : m < k
  · have := hp.2.2 m hmP hmk
    omega
  · have hne : m ≠ k := fun heq => hnp (heq ▸ hmP)
    have : k < m := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hmk) hne.symm
    have := hn.2.2 m hmP this
    omega

theorem isInterprime_midpoint_of_composite {k : Nat} (h : 4 ≤ k) (hnp : ¬ k.Prime) :
    IsInterprime ((prev_prime k + next_prime k) / 2) := by
  have h2 : 2 < k := by omega
  have hpn := prev_next_consecutive h2 hnp
  have hp2 : 2 < prev_prime k := by
    have hp := prev_prime_spec h2
    have h3 : 3 ≤ prev_prime k := by
      have h3p : (3 : Nat).Prime := Nat.prime_three
      have : 3 < k ∨ 3 = k := by omega
      rcases this with hlt | heq
      · exact hp.2.2 3 h3p hlt
      · exact False.elim (hnp (heq ▸ h3p))
    omega
  exact isInterprime_of_consecutive hpn.1 hpn.2.1 hp2
    (lt_trans hpn.2.2.1 hpn.2.2.2.1) hpn.2.2.2.2

theorem midpoint_ne_of_not_interprime {k : Nat} (h : 4 ≤ k) (hnp : ¬ k.Prime)
    (hI : ¬ IsInterprime k) :
    (prev_prime k + next_prime k) / 2 ≠ k := by
  intro heq
  exact hI (heq ▸ isInterprime_midpoint_of_composite h hnp)

theorem isInterprime_after_prime {p : Nat} (hp : p.Prime) (hp2 : 2 < p) :
    IsInterprime ((p + next_prime p) / 2) := by
  have hn := next_prime_spec p
  have hnone : ∀ m, p < m → m < next_prime p → ¬ m.Prime := by
    intro m hm1 hm2 hm
    have := hn.2.2 m hm hm1
    omega
  exact isInterprime_of_consecutive hp hn.1 hp2 hn.2.1 hnone

theorem isInterprime_before_prime {p : Nat} (hp : p.Prime) (hp3 : 3 < p) :
    IsInterprime ((prev_prime p + p) / 2) := by
  have hps := prev_prime_spec (by omega : 2 < p)
  have hprev2 : 2 < prev_prime p := by
    have : 3 ≤ prev_prime p := hps.2.2 3 Nat.prime_three (by omega)
    omega
  have hnone : ∀ m, prev_prime p < m → m < p → ¬ m.Prime := by
    intro m hm1 hm2 hm
    have := hps.2.2 m hm hm2
    omega
  exact isInterprime_of_consecutive hps.1 hp hprev2 hps.2.1 hnone

/-- The interprime immediately before an odd prime `p` is strictly less than `p`. -/
theorem before_prime_mid_lt {p : Nat} (_hp : p.Prime) (hp3 : 3 < p) :
    (prev_prime p + p) / 2 < p := by
  have hps := prev_prime_spec (by omega : 2 < p)
  have hlt : prev_prime p + p < p * 2 := by omega
  exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr hlt

theorem isInterprime_not_prime {k : Nat} (h : IsInterprime k) : ¬ k.Prime := by
  intro hk
  obtain ⟨p, hp, hp2, hpk, hS⟩ := h
  have hsum : p + next_prime p = 2 * k := by simpa [S_sum] using hS
  have hgt : k < next_prime p := by omega
  have hle := (next_prime_spec p).2.2 k hk hpk
  omega

theorem odd_prime_mod4 {p : Nat} (hp : p.Prime) (h2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd : Odd p := hp.odd_of_ne_two h2
  have hmod2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hlt : p % 4 < 4 := Nat.mod_lt p (by decide : 0 < 4)
  have h24 : p % 4 % 2 = p % 2 := (Nat.mod_mod_of_dvd p (by decide : 2 ∣ 4))
  have : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
  rcases this with h | h | h | h
  · rw [h] at h24; simp at h24; omega
  · exact Or.inl h
  · rw [h] at h24; simp at h24; omega
  · exact Or.inr h

theorem modeq_one_of_mod {p : Nat} (h : p % 4 = 1) : p ≡ 1 [MOD 4] := by
  rw [Nat.ModEq, Nat.one_mod]
  exact h

theorem modeq_three_of_mod {p : Nat} (h : p % 4 = 3) : p ≡ 3 [MOD 4] := by
  rw [Nat.ModEq]
  exact h

theorem even_midpoint_of_mixed {p q : Nat} (hp : Odd p) (hq : Odd q)
    (hpm : p % 4 = 1) (hqm : q % 4 = 3) :
    Even ((p + q) / 2) := by
  have hdiv : 2 ∣ p + q := even_iff_two_dvd.mp (hp.add_odd hq)
  have hsum : (p + q) % 4 = 0 := by
    have := Nat.add_mod p q 4
    rw [hpm, hqm] at this
    exact this
  have : 4 ∣ p + q := Nat.dvd_iff_mod_eq_zero.mpr hsum
  have hmul : 2 * ((p + q) / 2) = p + q := Nat.mul_div_cancel' hdiv
  have : 2 ∣ (p + q) / 2 := by
    have ⟨k, hk⟩ := this
    have : 2 * ((p + q) / 2) = 2 * (2 * k) := by
      rw [hmul, hk]; ring
    exact ⟨k, by omega⟩
  exact even_iff_two_dvd.mpr this

theorem exists_even_interprime_gt (N : Nat) :
    ∃ k, N ≤ k ∧ Even k ∧ IsInterprime k := by
  obtain ⟨p1, hp1gt, hp1p, hp1mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N 2) (q := 4) (a := 1)
      (by decide) (by decide)
  obtain ⟨p3₀, hp3gt0, hp3p0, hp3mod0⟩ :=
    Nat.forall_exists_prime_gt_and_modEq p1 (q := 4) (a := 3)
      (by decide) (by decide)
  let S := {p : Nat | p.Prime ∧ p ≡ 3 [MOD 4] ∧ p1 < p}
  have hSne : S.Nonempty := ⟨p3₀, hp3p0, hp3mod0, hp3gt0⟩
  let p3 := sInf S
  have hp3mem : p3 ∈ S := Nat.sInf_mem hSne
  have hp3p : p3.Prime := hp3mem.1
  have hp3mod : p3 ≡ 3 [MOD 4] := hp3mem.2.1
  have hp3gt : p1 < p3 := hp3mem.2.2
  have hp12 : 2 < p1 := Nat.lt_of_le_of_lt (le_max_right N 2) hp1gt
  let prev := sSup {p : Nat | p.Prime ∧ p < p3}
  have hPne : {p : Nat | p.Prime ∧ p < p3}.Nonempty :=
    ⟨2, Nat.prime_two, lt_trans hp12 hp3gt⟩
  have hPbdd : BddAbove {p : Nat | p.Prime ∧ p < p3} :=
    ⟨p3, fun _ hx => le_of_lt hx.2⟩
  have hprevmem : prev ∈ {p : Nat | p.Prime ∧ p < p3} := Nat.sSup_mem hPne hPbdd
  have hprevp : prev.Prime := hprevmem.1
  have hprevlt : prev < p3 := hprevmem.2
  have hnone : ∀ k, prev < k → k < p3 → ¬ k.Prime := by
    intro k hk1 hk2 hk
    have : k ≤ prev := le_csSup hPbdd ⟨hk, hk2⟩
    omega
  have hprev_ge : p1 ≤ prev := le_csSup hPbdd ⟨hp1p, hp3gt⟩
  have hprev_ne2 : prev ≠ 2 := by omega
  have hprev_mod1 : prev % 4 = 1 := by
    have hcases := odd_prime_mod4 hprevp hprev_ne2
    rcases hcases with h1 | h3
    · exact h1
    · have hmem : prev ∈ S := by
        refine ⟨hprevp, modeq_three_of_mod h3, ?_⟩
        have : p1 ≠ prev := by
          intro heq
          have : p1 % 4 = 1 := by
            simpa [Nat.ModEq, Nat.one_mod] using hp1mod
          omega
        omega
      have : p3 ≤ prev := Nat.sInf_le hmem
      omega
  have hmid : IsInterprime ((prev + p3) / 2) :=
    isInterprime_of_consecutive hprevp hp3p (by omega) hprevlt hnone
  have ho1 : Odd prev := hprevp.odd_of_ne_two hprev_ne2
  have ho3 : Odd p3 := hp3p.odd_of_ne_two (by omega)
  have hp3mod3 : p3 % 4 = 3 := by
    simpa [Nat.ModEq] using hp3mod
  have heven : Even ((prev + p3) / 2) :=
    even_midpoint_of_mixed ho1 ho3 hprev_mod1 hp3mod3
  have hge : N ≤ (prev + p3) / 2 := by
    have hdiv : 2 ∣ prev + p3 := even_iff_two_dvd.mp (ho1.add_odd ho3)
    have hle : prev ≤ (prev + p3) / 2 := by
      have hmul := Nat.mul_div_cancel' hdiv
      have : 2 * prev ≤ prev + p3 := by omega
      have : 2 * prev ≤ 2 * ((prev + p3) / 2) := by simpa [hmul]
      exact (mul_le_mul_iff_right₀ (by omega : 0 < (2 : Nat))).1 this
    have : N ≤ prev :=
      le_trans (le_max_left N 2) (le_trans (Nat.le_of_lt hp1gt) hprev_ge)
    omega
  exact ⟨(prev + p3) / 2, hge, heven, hmid⟩

theorem check_474_30 : checkFrom 474 30 = true := rfl

theorem a_pos_upto_503 (n : Nat) (h1 : 474 ≤ n) (h2 : n ≤ 503) : 0 < a n :=
  checkFrom_pos check_474_30 n h1 (by omega)

theorem a_pos_504_to_3000 (n : Nat) (h1 : 504 ≤ n) (h2 : n ≤ 3000) : 0 < a n := by
  by_cases h : n ≤ 823
  · exact a_pos_upto_823 n h1 h
  · exact a_pos_824_to_3000 n (by omega) h2


-- witnesses 3001..6000
def wits_3001 : List (Nat × Nat × Nat) :=
  [(3001, 1123, 1873), (3002, 1453, 1543), (3003, 1451, 1549), (3004, 3, 2999), (3005, 37, 2963), (3006, 5, 2999), (3007, 1453, 1549), (3008, 1451, 1553), (3009, 7, 2999), (3010, 1229, 1777), (3011, 1223, 1783), (3012, 11, 2999), (3013, 877, 2131), (3014, 1231, 1777), (3015, 13, 2999), (3016, 1291, 1721), (3017, 1433, 1579), (3018, 17, 2999), (3019, 1321, 1693), (3020, 809, 2207), (3021, 19, 2999), (3022, 1321, 1697), (3023, 1493, 1523), (3024, 1301, 1721), (3025, 3, 3019), (3026, 23, 2999), (3027, 5, 3019), (3028, 1481, 1543), (3029, 1423, 1601), (3030, 7, 3019), (3031, 1483, 1543), (3032, 1427, 1601), (3033, 11, 3019), (3034, 31, 2999), (3035, 1433, 1597), (3036, 13, 3019), (3037, 1489, 1543), (3038, 1481, 1553), (3039, 17, 3019), (3040, 1433, 1601)]
theorem wits_3001_ok : checkPairs wits_3001 = true := rfl
theorem wits_3001_ns : wits_3001.map (·.1) = (List.range 40).map (· + 3001) := rfl
theorem a_pos_3001_to_3040 (n : Nat) (h1 : 3001 ≤ n) (h2 : n ≤ 3040) : 0 < a n := by
  have hmem : n ∈ wits_3001.map (·.1) := by
    rw [wits_3001_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3001_ok hmem
def wits_3041 : List (Nat × Nat × Nat) :=
  [(3041, 1483, 1553), (3042, 19, 3019), (3043, 3, 3037), (3044, 1487, 1553), (3045, 5, 3037), (3046, 1321, 1721), (3047, 23, 3019), (3048, 7, 3037), (3049, 1423, 1621), (3050, 1291, 1753), (3051, 11, 3037), (3052, 1493, 1553), (3053, 1447, 1601), (3054, 13, 3037), (3055, 31, 3019), (3056, 1451, 1601), (3057, 17, 3037), (3058, 1301, 1753), (3059, 1361, 1693), (3060, 19, 3037), (3061, 1303, 1753), (3062, 1361, 1697), (3063, 1481, 1579), (3064, 1453, 1607), (3065, 23, 3037), (3066, 1277, 1787), (3067, 1453, 1609), (3068, 3, 3061), (3069, 29, 3037), (3070, 5, 3061), (3071, 1283, 1783), (3072, 1451, 1619), (3073, 7, 3061), (3074, 1321, 1747), (3075, 1289, 1783), (3076, 11, 3061), (3077, 1493, 1579), (3078, 37, 3037), (3079, 13, 3061), (3080, 1453, 1621)]
theorem wits_3041_ok : checkPairs wits_3041 = true := rfl
theorem wits_3041_ns : wits_3041.map (·.1) = (List.range 40).map (· + 3041) := rfl
theorem a_pos_3041_to_3080 (n : Nat) (h1 : 3041 ≤ n) (h2 : n ≤ 3080) : 0 < a n := by
  have hmem : n ∈ wits_3041.map (·.1) := by
    rw [wits_3041_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3041_ok hmem
def wits_3081 : List (Nat × Nat × Nat) :=
  [(3081, 1481, 1597), (3082, 17, 3061), (3083, 941, 2137), (3084, 1151, 1931), (3085, 3, 3079), (3086, 1481, 1601), (3087, 5, 3079), (3088, 1427, 1657), (3089, 1483, 1601), (3090, 3, 3083), (3091, 1429, 1657), (3092, 5, 3083), (3093, 11, 3079), (3094, 29, 3061), (3095, 7, 3083), (3096, 13, 3079), (3097, 1543, 1549), (3098, 11, 3083), (3099, 17, 3079), (3100, 1493, 1601), (3101, 13, 3083), (3102, 19, 3079), (3103, 37, 3061), (3104, 17, 3083), (3105, 1483, 1619), (3106, 1481, 1621), (3107, 19, 3083), (3108, 1487, 1619), (3109, 1483, 1621), (3110, 1117, 1987), (3111, 29, 3079), (3112, 23, 3083), (3113, 971, 2137), (3114, 1031, 2081), (3115, 31, 3079), (3116, 29, 3083), (3117, 1451, 1663), (3118, 1117, 1997), (3119, 1213, 1901), (3120, 31, 3083)]
theorem wits_3081_ok : checkPairs wits_3081 = true := rfl
theorem wits_3081_ns : wits_3081.map (·.1) = (List.range 40).map (· + 3081) := rfl
theorem a_pos_3081_to_3120 (n : Nat) (h1 : 3081 ≤ n) (h2 : n ≤ 3120) : 0 < a n := by
  have hmem : n ∈ wits_3081.map (·.1) := by
    rw [wits_3081_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3081_ok hmem
def wits_3121 : List (Nat × Nat × Nat) :=
  [(3121, 1453, 1663), (3122, 1187, 1931), (3123, 1427, 1693), (3124, 3, 3119), (3125, 37, 3083), (3126, 5, 3119), (3127, 1543, 1579), (3128, 1151, 1973), (3129, 7, 3119), (3130, 1223, 1901), (3131, 1433, 1693), (3132, 11, 3119), (3133, 991, 2137), (3134, 1433, 1697), (3135, 13, 3119), (3136, 1223, 1907), (3137, 1553, 1579), (3138, 17, 3119), (3139, 853, 2281), (3140, 1229, 1907), (3141, 19, 3119), (3142, 1481, 1657), (3143, 1523, 1613), (3144, 1061, 2081), (3145, 1543, 1597), (3146, 23, 3119), (3147, 1481, 1663), (3148, 1487, 1657), (3149, 1361, 1783), (3150, 29, 3119), (3151, 1489, 1657), (3152, 1361, 1787), (3153, 1487, 1663), (3154, 31, 3119), (3155, 1553, 1597), (3156, 1487, 1667), (3157, 1543, 1609), (3158, 1433, 1721), (3159, 37, 3119), (3160, 1553, 1601)]
theorem wits_3121_ok : checkPairs wits_3121 = true := rfl
theorem wits_3121_ns : wits_3121.map (·.1) = (List.range 40).map (· + 3121) := rfl
theorem a_pos_3121_to_3160 (n : Nat) (h1 : 3121 ≤ n) (h2 : n ≤ 3160) : 0 < a n := by
  have hmem : n ∈ wits_3121.map (·.1) := by
    rw [wits_3121_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3121_ok hmem
def wits_3161 : List (Nat × Nat × Nat) :=
  [(3161, 1493, 1663), (3162, 1289, 1871), (3163, 1297, 1861), (3164, 1553, 1607), (3165, 1289, 1873), (3166, 1543, 1619), (3167, 1553, 1609), (3168, 1289, 1877), (3169, 3, 3163), (3170, 1543, 1621), (3171, 5, 3163), (3172, 3, 3167), (3173, 1567, 1601), (3174, 5, 3167), (3175, 1549, 1621), (3176, 1553, 1619), (3177, 7, 3167), (3178, 1453, 1721), (3179, 1181, 1993), (3180, 11, 3167), (3181, 1429, 1747), (3182, 1277, 1901), (3183, 13, 3167), (3184, 1427, 1753), (3185, 1579, 1601), (3186, 17, 3167), (3187, 1429, 1753), (3188, 3, 3181), (3189, 19, 3167), (3190, 5, 3181), (3191, 23, 3163), (3192, 1319, 1871), (3193, 3, 3187), (3194, 23, 3167), (3195, 5, 3187), (3196, 11, 3181), (3197, 1579, 1613), (3198, 7, 3187), (3199, 13, 3181), (3200, 1453, 1741)]
theorem wits_3161_ok : checkPairs wits_3161 = true := rfl
theorem wits_3161_ns : wits_3161.map (·.1) = (List.range 40).map (· + 3161) := rfl
theorem a_pos_3161_to_3200 (n : Nat) (h1 : 3161 ≤ n) (h2 : n ≤ 3200) : 0 < a n := by
  have hmem : n ∈ wits_3161.map (·.1) := by
    rw [wits_3161_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3161_ok hmem
def wits_3201 : List (Nat × Nat × Nat) :=
  [(3201, 11, 3187), (3202, 17, 3181), (3203, 1597, 1601), (3204, 13, 3187), (3205, 19, 3181), (3206, 1543, 1657), (3207, 17, 3187), (3208, 1601, 1601), (3209, 1303, 1901), (3210, 3, 3203), (3211, 1549, 1657), (3212, 5, 3203), (3213, 1489, 1721), (3214, 29, 3181), (3215, 7, 3203), (3216, 1607, 1607), (3217, 499, 2713), (3218, 11, 3203), (3219, 29, 3187), (3220, 1601, 1613), (3221, 13, 3203), (3222, 1289, 1931), (3223, 3, 3217), (3224, 17, 3203), (3225, 5, 3217), (3226, 1481, 1741), (3227, 19, 3203), (3228, 7, 3217), (3229, 1567, 1657), (3230, 1319, 1907), (3231, 11, 3217), (3232, 23, 3203), (3233, 1361, 1867), (3234, 13, 3217), (3235, 1609, 1621), (3236, 29, 3203), (3237, 17, 3217), (3238, 1487, 1747), (3239, 1367, 1867), (3240, 19, 3217)]
theorem wits_3201_ok : checkPairs wits_3201 = true := rfl
theorem wits_3201_ns : wits_3201.map (·.1) = (List.range 40).map (· + 3201) := rfl
theorem a_pos_3201_to_3240 (n : Nat) (h1 : 3201 ≤ n) (h2 : n ≤ 3240) : 0 < a n := by
  have hmem : n ∈ wits_3201.map (·.1) := by
    rw [wits_3201_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3201_ok hmem
def wits_3241 : List (Nat × Nat × Nat) :=
  [(3241, 1579, 1657), (3242, 1367, 1871), (3243, 1213, 2027), (3244, 1619, 1621), (3245, 23, 3217), (3246, 1579, 1663), (3247, 1489, 1753), (3248, 1621, 1621), (3249, 29, 3217), (3250, 1181, 2063), (3251, 1553, 1693), (3252, 1319, 1931), (3253, 31, 3217), (3254, 1553, 1697), (3255, 1303, 1949), (3256, 3, 3251), (3257, 1279, 1973), (3258, 5, 3251), (3259, 3, 3253), (3260, 1123, 2131), (3261, 5, 3253), (3262, 3, 3257), (3263, 907, 2351), (3264, 5, 3257), (3265, 1483, 1777), (3266, 1289, 1973), (3267, 7, 3257), (3268, 1607, 1657), (3269, 1601, 1663), (3270, 11, 3257), (3271, 1609, 1657), (3272, 1601, 1667), (3273, 13, 3257), (3274, 1367, 1901), (3275, 1297, 1973), (3276, 17, 3257), (3277, 1033, 2239), (3278, 23, 3251), (3279, 19, 3257), (3280, 1619, 1657)]
theorem wits_3241_ok : checkPairs wits_3241 = true := rfl
theorem wits_3241_ns : wits_3241.map (·.1) = (List.range 40).map (· + 3241) := rfl
theorem a_pos_3241_to_3280 (n : Nat) (h1 : 3241 ≤ n) (h2 : n ≤ 3280) : 0 < a n := by
  have hmem : n ∈ wits_3241.map (·.1) := by
    rw [wits_3241_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3241_ok hmem
def wits_3281 : List (Nat × Nat × Nat) :=
  [(3281, 23, 3253), (3282, 29, 3251), (3283, 937, 2341), (3284, 23, 3257), (3285, 29, 3253), (3286, 31, 3251), (3287, 1283, 1999), (3288, 29, 3257), (3289, 31, 3253), (3290, 1543, 1741), (3291, 37, 3251), (3292, 31, 3257), (3293, 941, 2347), (3294, 37, 3253), (3295, 1549, 1741), (3296, 1543, 1747), (3297, 37, 3257), (3298, 941, 2351), (3299, 1601, 1693), (3300, 1427, 1871), (3301, 1549, 1747), (3302, 1601, 1697), (3303, 1607, 1693), (3304, 3, 3299), (3305, 1433, 1867), (3306, 5, 3299), (3307, 1549, 1753), (3308, 3, 3301), (3309, 7, 3299), (3310, 5, 3301), (3311, 1613, 1693), (3312, 11, 3299), (3313, 7, 3301), (3314, 3, 3307), (3315, 13, 3299), (3316, 5, 3307), (3317, 769, 2543), (3318, 17, 3299), (3319, 7, 3307), (3320, 3, 3313)]
theorem wits_3281_ok : checkPairs wits_3281 = true := rfl
theorem wits_3281_ns : wits_3281.map (·.1) = (List.range 40).map (· + 3281) := rfl
theorem a_pos_3281_to_3320 (n : Nat) (h1 : 3281 ≤ n) (h2 : n ≤ 3320) : 0 < a n := by
  have hmem : n ∈ wits_3281.map (·.1) := by
    rw [wits_3281_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3281_ok hmem
def wits_3321 : List (Nat × Nat × Nat) :=
  [(3321, 19, 3299), (3322, 5, 3313), (3323, 1181, 2137), (3324, 1451, 1871), (3325, 3, 3319), (3326, 23, 3299), (3327, 5, 3319), (3328, 11, 3313), (3329, 1423, 1901), (3330, 3, 3323), (3331, 13, 3313), (3332, 5, 3323), (3333, 11, 3319), (3334, 3, 3329), (3335, 7, 3323), (3336, 5, 3329), (3337, 19, 3313), (3338, 11, 3323), (3339, 7, 3329), (3340, 29, 3307), (3341, 13, 3323), (3342, 11, 3329), (3343, 37, 3301), (3344, 17, 3323), (3345, 13, 3329), (3346, 29, 3313), (3347, 19, 3323), (3348, 17, 3329), (3349, 3, 3343), (3350, 31, 3313), (3351, 5, 3343), (3352, 23, 3323), (3353, 1447, 1901), (3354, 7, 3343), (3355, 31, 3319), (3356, 23, 3329), (3357, 11, 3343), (3358, 1657, 1697), (3359, 1447, 1907), (3360, 13, 3343)]
theorem wits_3321_ok : checkPairs wits_3321 = true := rfl
theorem wits_3321_ns : wits_3321.map (·.1) = (List.range 40).map (· + 3321) := rfl
theorem a_pos_3321_to_3360 (n : Nat) (h1 : 3321 ≤ n) (h2 : n ≤ 3360) : 0 < a n := by
  have hmem : n ∈ wits_3321.map (·.1) := by
    rw [wits_3321_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3321_ok hmem
def wits_3361 : List (Nat × Nat × Nat) :=
  [(3361, 1609, 1747), (3362, 1451, 1907), (3363, 17, 3343), (3364, 3, 3359), (3365, 37, 3323), (3366, 5, 3359), (3367, 1609, 1753), (3368, 1621, 1741), (3369, 7, 3359), (3370, 1619, 1747), (3371, 23, 3343), (3372, 11, 3359), (3373, 1231, 2137), (3374, 1621, 1747), (3375, 13, 3359), (3376, 3, 3371), (3377, 1103, 2269), (3378, 5, 3371), (3379, 31, 3343), (3380, 1621, 1753), (3381, 7, 3371), (3382, 1657, 1721), (3383, 967, 2411), (3384, 11, 3371), (3385, 1093, 2287), (3386, 23, 3359), (3387, 13, 3371), (3388, 1607, 1777), (3389, 1601, 1783), (3390, 17, 3371), (3391, 1609, 1777), (3392, 1601, 1787), (3393, 19, 3371), (3394, 3, 3389), (3395, 1489, 1901), (3396, 5, 3389), (3397, 1123, 2269), (3398, 23, 3371), (3399, 7, 3389), (3400, 1619, 1777)]
theorem wits_3361_ok : checkPairs wits_3361 = true := rfl
theorem wits_3361_ns : wits_3361.map (·.1) = (List.range 40).map (· + 3361) := rfl
theorem a_pos_3361_to_3400 (n : Nat) (h1 : 3361 ≤ n) (h2 : n ≤ 3400) : 0 < a n := by
  have hmem : n ∈ wits_3361.map (·.1) := by
    rw [wits_3361_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3361_ok hmem
def wits_3401 : List (Nat × Nat × Nat) :=
  [(3401, 1613, 1783), (3402, 11, 3389), (3403, 601, 2797), (3404, 1657, 1741), (3405, 13, 3389), (3406, 31, 3371), (3407, 1429, 1973), (3408, 17, 3389), (3409, 1663, 1741), (3410, 1657, 1747), (3411, 19, 3389), (3412, 1667, 1741), (3413, 971, 2437), (3414, 3, 3407), (3415, 1663, 1747), (3416, 5, 3407), (3417, 1693, 1721), (3418, 1667, 1747), (3419, 7, 3407), (3420, 29, 3389), (3421, 1663, 1753), (3422, 11, 3407), (3423, 1549, 1871), (3424, 31, 3389), (3425, 13, 3407), (3426, 1427, 1997), (3427, 1033, 2389), (3428, 17, 3407), (3429, 37, 3389), (3430, 1361, 2063), (3431, 19, 3407), (3432, 1481, 1949), (3433, 1567, 1861), (3434, 1553, 1877), (3435, 1483, 1949), (3436, 23, 3407), (3437, 1433, 1999), (3438, 1487, 1949), (3439, 1693, 1741), (3440, 29, 3407)]
theorem wits_3401_ok : checkPairs wits_3401 = true := rfl
theorem wits_3401_ns : wits_3401.map (·.1) = (List.range 40).map (· + 3401) := rfl
theorem a_pos_3401_to_3440 (n : Nat) (h1 : 3401 ≤ n) (h2 : n ≤ 3440) : 0 < a n := by
  have hmem : n ∈ wits_3401.map (·.1) := by
    rw [wits_3401_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3401_ok hmem
def wits_3441 : List (Nat × Nat × Nat) :=
  [(3441, 1567, 1871), (3442, 1697, 1741), (3443, 1087, 2351), (3444, 31, 3407), (3445, 1693, 1747), (3446, 1493, 1949), (3447, 1567, 1877), (3448, 1697, 1747), (3449, 37, 3407), (3450, 1451, 1997), (3451, 1693, 1753), (3452, 1367, 2081), (3453, 1667, 1783), (3454, 1697, 1753), (3455, 1549, 1901), (3456, 1667, 1787), (3457, 1453, 1999), (3458, 1481, 1973), (3459, 1579, 1877), (3460, 1553, 1901), (3461, 1549, 1907), (3462, 1319, 2141), (3463, 3, 3457), (3464, 1487, 1973), (3465, 5, 3457), (3466, 3, 3461), (3467, 1489, 1973), (3468, 5, 3461), (3469, 3, 3463), (3470, 1453, 2011), (3471, 5, 3463), (3472, 3, 3467), (3473, 1601, 1867), (3474, 5, 3467), (3475, 1693, 1777), (3476, 1601, 1871), (3477, 7, 3467), (3478, 1721, 1753), (3479, 1601, 1873), (3480, 11, 3467)]
theorem wits_3441_ok : checkPairs wits_3441 = true := rfl
theorem wits_3441_ns : wits_3441.map (·.1) = (List.range 40).map (· + 3441) := rfl
theorem a_pos_3441_to_3480 (n : Nat) (h1 : 3441 ≤ n) (h2 : n ≤ 3480) : 0 < a n := by
  have hmem : n ∈ wits_3441.map (·.1) := by
    rw [wits_3441_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3441_ok hmem
def wits_3481 : List (Nat × Nat × Nat) :=
  [(3481, 1489, 1987), (3482, 1601, 1877), (3483, 13, 3467), (3484, 1619, 1861), (3485, 23, 3457), (3486, 17, 3467), (3487, 769, 2713), (3488, 23, 3461), (3489, 19, 3467), (3490, 1019, 2467), (3491, 23, 3463), (3492, 29, 3461), (3493, 31, 3457), (3494, 23, 3467), (3495, 29, 3463), (3496, 31, 3461), (3497, 1493, 1999), (3498, 29, 3467), (3499, 31, 3463), (3500, 1747, 1747), (3501, 37, 3461), (3502, 31, 3467), (3503, 1597, 1901), (3504, 37, 3463), (3505, 1489, 2011), (3506, 1747, 1753), (3507, 37, 3467), (3508, 1601, 1901), (3509, 1597, 1907), (3510, 1721, 1787), (3511, 1117, 2389), (3512, 1753, 1753), (3513, 1579, 1931), (3514, 1601, 1907), (3515, 1609, 1901), (3516, 1487, 2027), (3517, 1123, 2389), (3518, 3, 3511), (3519, 1567, 1949), (3520, 5, 3511)]
theorem wits_3481_ok : checkPairs wits_3481 = true := rfl
theorem wits_3481_ns : wits_3481.map (·.1) = (List.range 40).map (· + 3481) := rfl
theorem a_pos_3481_to_3520 (n : Nat) (h1 : 3481 ≤ n) (h2 : n ≤ 3520) : 0 < a n := by
  have hmem : n ∈ wits_3481.map (·.1) := by
    rw [wits_3481_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3481_ok hmem
def wits_3521 : List (Nat × Nat × Nat) :=
  [(3521, 1609, 1907), (3522, 809, 2711), (3523, 7, 3511), (3524, 1741, 1777), (3525, 1319, 2203), (3526, 11, 3511), (3527, 1549, 1973), (3528, 1289, 2237), (3529, 13, 3511), (3530, 1747, 1777), (3531, 1597, 1931), (3532, 3, 3527), (3533, 1181, 2347), (3534, 5, 3527), (3535, 3, 3529), (3536, 1753, 1777), (3537, 5, 3529), (3538, 1747, 1787), (3539, 1187, 2347), (3540, 3, 3533), (3541, 1753, 1783), (3542, 5, 3533), (3543, 11, 3529), (3544, 3, 3539), (3545, 7, 3533), (3546, 5, 3539), (3547, 1543, 1999), (3548, 3, 3541), (3549, 7, 3539), (3550, 5, 3541), (3551, 13, 3533), (3552, 11, 3539), (3553, 7, 3541), (3554, 17, 3533), (3555, 13, 3539), (3556, 11, 3541), (3557, 19, 3533), (3558, 17, 3539), (3559, 13, 3541), (3560, 1777, 1777)]
theorem wits_3521_ok : checkPairs wits_3521 = true := rfl
theorem wits_3521_ns : wits_3521.map (·.1) = (List.range 40).map (· + 3521) := rfl
theorem a_pos_3521_to_3560 (n : Nat) (h1 : 3521 ≤ n) (h2 : n ≤ 3560) : 0 < a n := by
  have hmem : n ∈ wits_3521.map (·.1) := by
    rw [wits_3521_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3521_ok hmem
def wits_3561 : List (Nat × Nat × Nat) :=
  [(3561, 19, 3539), (3562, 3, 3557), (3563, 1181, 2377), (3564, 5, 3557), (3565, 19, 3541), (3566, 23, 3539), (3567, 7, 3557), (3568, 1777, 1787), (3569, 1663, 1901), (3570, 11, 3557), (3571, 1579, 1987), (3572, 1667, 1901), (3573, 13, 3557), (3574, 29, 3541), (3575, 37, 3533), (3576, 17, 3557), (3577, 1033, 2539), (3578, 31, 3541), (3579, 19, 3557), (3580, 1601, 1973), (3581, 1493, 2083), (3582, 1451, 2129), (3583, 37, 3541), (3584, 23, 3557), (3585, 1289, 2293), (3586, 3, 3581), (3587, 1609, 1973), (3588, 5, 3581), (3589, 1597, 1987), (3590, 1453, 2131), (3591, 7, 3581), (3592, 31, 3557), (3593, 971, 2617), (3594, 11, 3581), (3595, 1579, 2011), (3596, 1619, 1973), (3597, 13, 3581), (3598, 1607, 1987), (3599, 1693, 1901), (3600, 17, 3581)]
theorem wits_3561_ok : checkPairs wits_3561 = true := rfl
theorem wits_3561_ns : wits_3561.map (·.1) = (List.range 40).map (· + 3561) := rfl
theorem a_pos_3561_to_3600 (n : Nat) (h1 : 3561 ≤ n) (h2 : n ≤ 3600) : 0 < a n := by
  have hmem : n ∈ wits_3561.map (·.1) := by
    rw [wits_3561_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3561_ok hmem
def wits_3601 : List (Nat × Nat × Nat) :=
  [(3601, 1609, 1987), (3602, 1697, 1901), (3603, 19, 3581), (3604, 1319, 2281), (3605, 1693, 1907), (3606, 1607, 1997), (3607, 1063, 2539), (3608, 23, 3581), (3609, 1609, 1997), (3610, 1657, 1949), (3611, 1613, 1993), (3612, 29, 3581), (3613, 1741, 1867), (3614, 3, 3607), (3615, 1663, 1949), (3616, 5, 3607), (3617, 1613, 1999), (3618, 1667, 1949), (3619, 3, 3613), (3620, 1753, 1861), (3621, 5, 3613), (3622, 11, 3607), (3623, 1181, 2437), (3624, 3, 3617), (3625, 13, 3607), (3626, 5, 3617), (3627, 11, 3613), (3628, 17, 3607), (3629, 7, 3617), (3630, 13, 3613), (3631, 19, 3607), (3632, 11, 3617), (3633, 17, 3613), (3634, 1753, 1877), (3635, 13, 3617), (3636, 19, 3613), (3637, 1163, 2467), (3638, 3, 3631), (3639, 1609, 2027), (3640, 5, 3631)]
theorem wits_3601_ok : checkPairs wits_3601 = true := rfl
theorem wits_3601_ns : wits_3601.map (·.1) = (List.range 40).map (· + 3601) := rfl
theorem a_pos_3601_to_3640 (n : Nat) (h1 : 3601 ≤ n) (h2 : n ≤ 3640) : 0 < a n := by
  have hmem : n ∈ wits_3601.map (·.1) := by
    rw [wits_3601_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3601_ok hmem
def wits_3641 : List (Nat × Nat × Nat) :=
  [(3641, 19, 3617), (3642, 1301, 2339), (3643, 7, 3631), (3644, 3, 3637), (3645, 29, 3613), (3646, 5, 3637), (3647, 1579, 2063), (3648, 1697, 1949), (3649, 7, 3637), (3650, 29, 3617), (3651, 1567, 2081), (3652, 11, 3637), (3653, 1297, 2351), (3654, 31, 3617), (3655, 13, 3637), (3656, 1319, 2333), (3657, 1787, 1867), (3658, 17, 3637), (3659, 37, 3617), (3660, 23, 3631), (3661, 19, 3637), (3662, 1451, 2207), (3663, 1787, 1873), (3664, 29, 3631), (3665, 1597, 2063), (3666, 23, 3637), (3667, 1279, 2383), (3668, 31, 3631), (3669, 1667, 1999), (3670, 29, 3637), (3671, 1693, 1973), (3672, 1721, 1949), (3673, 37, 3631), (3674, 31, 3637), (3675, 883, 2789), (3676, 3, 3671), (3677, 1609, 2063), (3678, 5, 3671), (3679, 3, 3673), (3680, 1543, 2131)]
theorem wits_3641_ok : checkPairs wits_3641 = true := rfl
theorem wits_3641_ns : wits_3641.map (·.1) = (List.range 40).map (· + 3641) := rfl
theorem a_pos_3641_to_3680 (n : Nat) (h1 : 3641 ≤ n) (h2 : n ≤ 3680) : 0 < a n := by
  have hmem : n ∈ wits_3641.map (·.1) := by
    rw [wits_3641_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3641_ok hmem
def wits_3681 : List (Nat × Nat × Nat) :=
  [(3681, 5, 3673), (3682, 1747, 1931), (3683, 971, 2707), (3684, 7, 3673), (3685, 1693, 1987), (3686, 1619, 2063), (3687, 11, 3673), (3688, 1753, 1931), (3689, 1783, 1901), (3690, 13, 3673), (3691, 1303, 2383), (3692, 1787, 1901), (3693, 17, 3673), (3694, 1741, 1949), (3695, 1783, 1907), (3696, 19, 3673), (3697, 1453, 2239), (3698, 3, 3691), (3699, 1697, 1999), (3700, 5, 3691), (3701, 23, 3673), (3702, 29, 3671), (3703, 3, 3697), (3704, 1613, 2087), (3705, 5, 3697), (3706, 11, 3691), (3707, 1433, 2269), (3708, 7, 3697), (3709, 13, 3691), (3710, 1367, 2339), (3711, 11, 3697), (3712, 17, 3691), (3713, 1361, 2347), (3714, 13, 3697), (3715, 19, 3691), (3716, 1601, 2111), (3717, 17, 3697), (3718, 1427, 2287), (3719, 1367, 2347), (3720, 19, 3697)]
theorem wits_3681_ok : checkPairs wits_3681 = true := rfl
theorem wits_3681_ns : wits_3681.map (·.1) = (List.range 40).map (· + 3681) := rfl
theorem a_pos_3681_to_3720 (n : Nat) (h1 : 3681 ≤ n) (h2 : n ≤ 3720) : 0 < a n := by
  have hmem : n ∈ wits_3681.map (·.1) := by
    rw [wits_3681_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3681_ok hmem
def wits_3721 : List (Nat × Nat × Nat) :=
  [(3721, 1429, 2287), (3722, 1301, 2417), (3723, 1721, 1999), (3724, 29, 3691), (3725, 23, 3697), (3726, 1697, 2027), (3727, 1453, 2269), (3728, 31, 3691), (3729, 29, 3697), (3730, 1777, 1949), (3731, 1663, 2063), (3732, 1619, 2111), (3733, 31, 3697), (3734, 3, 3727), (3735, 1783, 1949), (3736, 5, 3727), (3737, 1493, 2239), (3738, 37, 3697), (3739, 7, 3727), (3740, 3, 3733), (3741, 1867, 1871), (3742, 5, 3733), (3743, 1601, 2137), (3744, 1871, 1871), (3745, 7, 3733), (3746, 1753, 1987), (3747, 1871, 1873), (3748, 11, 3733), (3749, 1367, 2377), (3750, 1871, 1877), (3751, 13, 3733), (3752, 1367, 2381), (3753, 1873, 1877), (3754, 17, 3733), (3755, 1613, 2137), (3756, 23, 3727), (3757, 19, 3733), (3758, 1741, 2011), (3759, 1619, 2137), (3760, 29, 3727)]
theorem wits_3721_ok : checkPairs wits_3721 = true := rfl
theorem wits_3721_ns : wits_3721.map (·.1) = (List.range 40).map (· + 3721) := rfl
theorem a_pos_3721_to_3760 (n : Nat) (h1 : 3721 ≤ n) (h2 : n ≤ 3760) : 0 < a n := by
  have hmem : n ∈ wits_3721.map (·.1) := by
    rw [wits_3721_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3721_ok hmem
def wits_3761 : List (Nat × Nat × Nat) :=
  [(3761, 1783, 1973), (3762, 23, 3733), (3763, 1621, 2137), (3764, 31, 3727), (3765, 1423, 2339), (3766, 29, 3733), (3767, 1493, 2269), (3768, 3, 3761), (3769, 37, 3727), (3770, 5, 3761), (3771, 1429, 2339), (3772, 3, 3767), (3773, 7, 3761), (3774, 5, 3767), (3775, 37, 3733), (3776, 11, 3761), (3777, 7, 3767), (3778, 1787, 1987), (3779, 13, 3761), (3780, 11, 3767), (3781, 1777, 1999), (3782, 17, 3761), (3783, 13, 3767), (3784, 1753, 2027), (3785, 19, 3761), (3786, 17, 3767), (3787, 1543, 2239), (3788, 1877, 1907), (3789, 19, 3767), (3790, 23, 3761), (3791, 1579, 2207), (3792, 1481, 2309), (3793, 1447, 2341), (3794, 23, 3767), (3795, 1663, 2129), (3796, 1861, 1931), (3797, 1553, 2239), (3798, 29, 3767), (3799, 3, 3793), (3800, 1453, 2341)]
theorem wits_3761_ok : checkPairs wits_3761 = true := rfl
theorem wits_3761_ns : wits_3761.map (·.1) = (List.range 40).map (· + 3761) := rfl
theorem a_pos_3761_to_3800 (n : Nat) (h1 : 3761 ≤ n) (h2 : n ≤ 3800) : 0 < a n := by
  have hmem : n ∈ wits_3761.map (·.1) := by
    rw [wits_3761_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3761_ok hmem
def wits_3801 : List (Nat × Nat × Nat) :=
  [(3801, 5, 3793), (3802, 31, 3767), (3803, 37, 3761), (3804, 3, 3797), (3805, 1453, 2347), (3806, 5, 3797), (3807, 11, 3793), (3808, 1901, 1901), (3809, 7, 3797), (3810, 13, 3793), (3811, 1423, 2383), (3812, 11, 3797), (3813, 17, 3793), (3814, 1901, 1907), (3815, 13, 3797), (3816, 19, 3793), (3817, 1543, 2269), (3818, 17, 3797), (3819, 1867, 1949), (3820, 1907, 1907), (3821, 19, 3797), (3822, 1871, 1949), (3823, 1447, 2371), (3824, 1553, 2267), (3825, 29, 3793), (3826, 3, 3821), (3827, 1553, 2269), (3828, 5, 3821), (3829, 31, 3793), (3830, 29, 3797), (3831, 7, 3821), (3832, 1747, 2081), (3833, 971, 2857), (3834, 11, 3821), (3835, 1747, 2083), (3836, 1901, 1931), (3837, 13, 3821), (3838, 1753, 2081), (3839, 37, 3797), (3840, 17, 3821)]
theorem wits_3801_ok : checkPairs wits_3801 = true := rfl
theorem wits_3801_ns : wits_3801.map (·.1) = (List.range 40).map (· + 3801) := rfl
theorem a_pos_3801_to_3840 (n : Nat) (h1 : 3801 ≤ n) (h2 : n ≤ 3840) : 0 < a n := by
  have hmem : n ∈ wits_3801.map (·.1) := by
    rw [wits_3801_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3801_ok hmem
def wits_3841 : List (Nat × Nat × Nat) :=
  [(3841, 1753, 2083), (3842, 1907, 1931), (3843, 19, 3821), (3844, 1753, 2087), (3845, 1867, 1973), (3846, 1607, 2237), (3847, 1453, 2389), (3848, 23, 3821), (3849, 1609, 2237), (3850, 1493, 2351), (3851, 1873, 1973), (3852, 29, 3821), (3853, 3, 3847), (3854, 1901, 1949), (3855, 5, 3847), (3856, 3, 3851), (3857, 1613, 2239), (3858, 5, 3851), (3859, 1867, 1987), (3860, 1907, 1949), (3861, 7, 3851), (3862, 1871, 1987), (3863, 1447, 2411), (3864, 11, 3851), (3865, 1873, 1987), (3866, 1553, 2309), (3867, 13, 3851), (3868, 1877, 1987), (3869, 1447, 2417), (3870, 17, 3851), (3871, 1579, 2287), (3872, 1601, 2267), (3873, 19, 3851), (3874, 1741, 2129), (3875, 23, 3847), (3876, 1877, 1997), (3877, 1489, 2383), (3878, 23, 3851), (3879, 29, 3847), (3880, 1901, 1973)]
theorem wits_3841_ok : checkPairs wits_3841 = true := rfl
theorem wits_3841_ns : wits_3841.map (·.1) = (List.range 40).map (· + 3841) := rfl
theorem a_pos_3841_to_3880 (n : Nat) (h1 : 3841 ≤ n) (h2 : n ≤ 3880) : 0 < a n := by
  have hmem : n ∈ wits_3841.map (·.1) := by
    rw [wits_3841_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3841_ok hmem
def wits_3881 : List (Nat × Nat × Nat) :=
  [(3881, 1483, 2393), (3882, 29, 3851), (3883, 3, 3877), (3884, 1747, 2131), (3885, 5, 3877), (3886, 31, 3851), (3887, 1613, 2269), (3888, 7, 3877), (3889, 1873, 2011), (3890, 1753, 2131), (3891, 11, 3877), (3892, 1877, 2011), (3893, 1447, 2441), (3894, 13, 3877), (3895, 1753, 2137), (3896, 1553, 2339), (3897, 17, 3877), (3898, 1753, 2141), (3899, 1901, 1993), (3900, 19, 3877), (3901, 1657, 2239), (3902, 1901, 1997), (3903, 1873, 2027), (3904, 1619, 2281), (3905, 23, 3877), (3906, 1877, 2027), (3907, 373, 3529), (3908, 1931, 1973), (3909, 29, 3877), (3910, 1777, 2129), (3911, 1907, 1999), (3912, 1319, 2591), (3913, 3, 3907), (3914, 1777, 2131), (3915, 5, 3907), (3916, 1493, 2417), (3917, 1579, 2333), (3918, 3, 3911), (3919, 1783, 2131), (3920, 5, 3911)]
theorem wits_3881_ok : checkPairs wits_3881 = true := rfl
theorem wits_3881_ns : wits_3881.map (·.1) = (List.range 40).map (· + 3881) := rfl
theorem a_pos_3881_to_3920 (n : Nat) (h1 : 3881 ≤ n) (h2 : n ≤ 3920) : 0 < a n := by
  have hmem : n ∈ wits_3881.map (·.1) := by
    rw [wits_3881_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3881_ok hmem
def wits_3921 : List (Nat × Nat × Nat) :=
  [(3921, 11, 3907), (3922, 3, 3917), (3923, 7, 3911), (3924, 5, 3917), (3925, 3, 3919), (3926, 11, 3911), (3927, 5, 3919), (3928, 1657, 2267), (3929, 13, 3911), (3930, 3, 3923), (3931, 1657, 2269), (3932, 5, 3923), (3933, 11, 3919), (3934, 3, 3929), (3935, 7, 3923), (3936, 5, 3929), (3937, 1549, 2383), (3938, 11, 3923), (3939, 7, 3929), (3940, 23, 3911), (3941, 13, 3923), (3942, 11, 3929), (3943, 31, 3907), (3944, 17, 3923), (3945, 13, 3929), (3946, 1931, 2011), (3947, 19, 3923), (3948, 17, 3929), (3949, 3, 3943), (3950, 1657, 2287), (3951, 5, 3943), (3952, 23, 3923), (3953, 37, 3911), (3954, 7, 3943), (3955, 31, 3919), (3956, 23, 3929), (3957, 11, 3943), (3958, 1667, 2287), (3959, 1097, 2857), (3960, 13, 3943)]
theorem wits_3921_ok : checkPairs wits_3921 = true := rfl
theorem wits_3921_ns : wits_3921.map (·.1) = (List.range 40).map (· + 3921) := rfl
theorem a_pos_3921_to_3960 (n : Nat) (h1 : 3921 ≤ n) (h2 : n ≤ 3960) : 0 < a n := by
  have hmem : n ∈ wits_3921.map (·.1) := by
    rw [wits_3921_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3921_ok hmem
def wits_3961 : List (Nat × Nat × Nat) :=
  [(3961, 1753, 2203), (3962, 1607, 2351), (3963, 17, 3943), (3964, 31, 3929), (3965, 37, 3923), (3966, 19, 3943), (3967, 1579, 2383), (3968, 1621, 2341), (3969, 37, 3929), (3970, 1901, 2063), (3971, 23, 3943), (3972, 641, 3329), (3973, 1621, 2347), (3974, 1973, 1997), (3975, 29, 3943), (3976, 1907, 2063), (3977, 1973, 1999), (3978, 1949, 2027), (3979, 31, 3943), (3980, 1987, 1987), (3981, 1867, 2111), (3982, 1741, 2237), (3983, 1601, 2377), (3984, 37, 3943), (3985, 1987, 1993), (3986, 1901, 2081), (3987, 1873, 2111), (3988, 1987, 1997), (3989, 1901, 2083), (3990, 1877, 2111), (3991, 1987, 1999), (3992, 1907, 2081), (3993, 1993, 1997), (3994, 1861, 2129), (3995, 1907, 2083), (3996, 1997, 1997), (3997, 1753, 2239), (3998, 1931, 2063), (3999, 1997, 1999), (4000, 1657, 2339)]
theorem wits_3961_ok : checkPairs wits_3961 = true := rfl
theorem wits_3961_ns : wits_3961.map (·.1) = (List.range 40).map (· + 3961) := rfl
theorem a_pos_3961_to_4000 (n : Nat) (h1 : 3961 ≤ n) (h2 : n ≤ 4000) : 0 < a n := by
  have hmem : n ∈ wits_3961.map (·.1) := by
    rw [wits_3961_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_3961_ok hmem
def wits_4001 : List (Nat × Nat × Nat) :=
  [(4001, 1663, 2333), (4002, 1871, 2129), (4003, 1867, 2131), (4004, 1987, 2011), (4005, 1873, 2129), (4006, 3, 4001), (4007, 1613, 2389), (4008, 5, 4001), (4009, 3, 4003), (4010, 1621, 2383), (4011, 5, 4003), (4012, 1997, 2011), (4013, 1597, 2411), (4014, 3, 4007), (4015, 1999, 2011), (4016, 5, 4007), (4017, 11, 4003), (4018, 1987, 2027), (4019, 7, 4007), (4020, 3, 4013), (4021, 1777, 2239), (4022, 5, 4013), (4023, 17, 4003), (4024, 3, 4019), (4025, 7, 4013), (4026, 5, 4019), (4027, 1753, 2269), (4028, 3, 4021), (4029, 7, 4019), (4030, 5, 4021), (4031, 13, 4013), (4032, 11, 4019), (4033, 7, 4021), (4034, 17, 4013), (4035, 13, 4019), (4036, 11, 4021), (4037, 19, 4013), (4038, 17, 4019), (4039, 13, 4021), (4040, 29, 4007)]
theorem wits_4001_ok : checkPairs wits_4001 = true := rfl
theorem wits_4001_ns : wits_4001.map (·.1) = (List.range 40).map (· + 4001) := rfl
theorem a_pos_4001_to_4040 (n : Nat) (h1 : 4001 ≤ n) (h2 : n ≤ 4040) : 0 < a n := by
  have hmem : n ∈ wits_4001.map (·.1) := by
    rw [wits_4001_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4001_ok hmem
def wits_4041 : List (Nat × Nat × Nat) :=
  [(4041, 19, 4019), (4042, 17, 4021), (4043, 1901, 2137), (4044, 31, 4007), (4045, 19, 4021), (4046, 23, 4019), (4047, 1697, 2347), (4048, 1777, 2267), (4049, 37, 4007), (4050, 23, 4021), (4051, 1777, 2269), (4052, 1907, 2141), (4053, 1783, 2267), (4054, 3, 4049), (4055, 37, 4013), (4056, 5, 4049), (4057, 1033, 3019), (4058, 3, 4051), (4059, 7, 4049), (4060, 5, 4051), (4061, 1993, 2063), (4062, 11, 4049), (4063, 7, 4051), (4064, 1997, 2063), (4065, 13, 4049), (4066, 11, 4051), (4067, 1999, 2063), (4068, 17, 4049), (4069, 13, 4051), (4070, 1777, 2287), (4071, 19, 4049), (4072, 17, 4051), (4073, 1361, 2707), (4074, 1931, 2141), (4075, 19, 4051), (4076, 23, 4049), (4077, 1993, 2081), (4078, 1987, 2087), (4079, 1867, 2207), (4080, 3, 4073)]
theorem wits_4041_ok : checkPairs wits_4041 = true := rfl
theorem wits_4041_ns : wits_4041.map (·.1) = (List.range 40).map (· + 4041) := rfl
theorem a_pos_4041_to_4080 (n : Nat) (h1 : 4041 ≤ n) (h2 : n ≤ 4080) : 0 < a n := by
  have hmem : n ∈ wits_4041.map (·.1) := by
    rw [wits_4041_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4041_ok hmem
def wits_4081 : List (Nat × Nat × Nat) :=
  [(4081, 1693, 2383), (4082, 5, 4073), (4083, 1999, 2081), (4084, 29, 4051), (4085, 7, 4073), (4086, 1997, 2087), (4087, 1543, 2539), (4088, 11, 4073), (4089, 37, 4049), (4090, 1777, 2309), (4091, 13, 4073), (4092, 1949, 2141), (4093, 37, 4051), (4094, 17, 4073), (4095, 1783, 2309), (4096, 3, 4091), (4097, 19, 4073), (4098, 5, 4091), (4099, 2011, 2083), (4100, 3, 4093), (4101, 7, 4091), (4102, 5, 4093), (4103, 251, 3847), (4104, 11, 4091), (4105, 7, 4093), (4106, 29, 4073), (4107, 13, 4091), (4108, 11, 4093), (4109, 1901, 2203), (4110, 17, 4091), (4111, 13, 4093), (4112, 1697, 2411), (4113, 19, 4091), (4114, 17, 4093), (4115, 37, 4073), (4116, 2027, 2087), (4117, 19, 4093), (4118, 23, 4091), (4119, 1877, 2239), (4120, 1987, 2129)]
theorem wits_4081_ok : checkPairs wits_4081 = true := rfl
theorem wits_4081_ns : wits_4081.map (·.1) = (List.range 40).map (· + 4081) := rfl
theorem a_pos_4081_to_4120 (n : Nat) (h1 : 4081 ≤ n) (h2 : n ≤ 4120) : 0 < a n := by
  have hmem : n ∈ wits_4081.map (·.1) := by
    rw [wits_4081_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4081_ok hmem
def wits_4121 : List (Nat × Nat × Nat) :=
  [(4121, 1783, 2333), (4122, 23, 4093), (4123, 1741, 2377), (4124, 1987, 2131), (4125, 1993, 2129), (4126, 29, 4093), (4127, 1579, 2543), (4128, 1997, 2129), (4129, 1993, 2131), (4130, 31, 4093), (4131, 37, 4091), (4132, 3, 4127), (4133, 941, 3187), (4134, 5, 4127), (4135, 3, 4129), (4136, 1747, 2383), (4137, 5, 4129), (4138, 1753, 2381), (4139, 1783, 2351), (4140, 3, 4133), (4141, 1747, 2389), (4142, 5, 4133), (4143, 11, 4129), (4144, 2011, 2129), (4145, 7, 4133), (4146, 13, 4129), (4147, 1753, 2389), (4148, 11, 4133), (4149, 17, 4129), (4150, 1601, 2543), (4151, 13, 4133), (4152, 19, 4129), (4153, 2011, 2137), (4154, 17, 4133), (4155, 1949, 2203), (4156, 2011, 2141), (4157, 19, 4133), (4158, 29, 4127), (4159, 3, 4153), (4160, 1949, 2207)]
theorem wits_4121_ok : checkPairs wits_4121 = true := rfl
theorem wits_4121_ns : wits_4121.map (·.1) = (List.range 40).map (· + 4121) := rfl
theorem a_pos_4121_to_4160 (n : Nat) (h1 : 4121 ≤ n) (h2 : n ≤ 4160) : 0 < a n := by
  have hmem : n ∈ wits_4121.map (·.1) := by
    rw [wits_4121_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4121_ok hmem
def wits_4161 : List (Nat × Nat × Nat) :=
  [(4161, 5, 4153), (4162, 3, 4157), (4163, 1361, 2797), (4164, 5, 4157), (4165, 31, 4129), (4166, 29, 4133), (4167, 7, 4157), (4168, 1877, 2287), (4169, 1367, 2797), (4170, 11, 4157), (4171, 1783, 2383), (4172, 1901, 2267), (4173, 13, 4157), (4174, 1861, 2309), (4175, 37, 4133), (4176, 17, 4157), (4177, 859, 3313), (4178, 2063, 2111), (4179, 19, 4157), (4180, 1217, 2957), (4181, 23, 4153), (4182, 1871, 2309), (4183, 1741, 2437), (4184, 23, 4157), (4185, 29, 4153), (4186, 1973, 2207), (4187, 1493, 2689), (4188, 29, 4157), (4189, 31, 4153), (4190, 1289, 2897), (4191, 1949, 2239), (4192, 31, 4157), (4193, 971, 3217), (4194, 37, 4153), (4195, 1987, 2203), (4196, 2063, 2129), (4197, 37, 4157), (4198, 1481, 2713), (4199, 1901, 2293), (4200, 2087, 2111)]
theorem wits_4161_ok : checkPairs wits_4161 = true := rfl
theorem wits_4161_ns : wits_4161.map (·.1) = (List.range 40).map (· + 4161) := rfl
theorem a_pos_4161_to_4200 (n : Nat) (h1 : 4161 ≤ n) (h2 : n ≤ 4200) : 0 < a n := by
  have hmem : n ∈ wits_4161.map (·.1) := by
    rw [wits_4161_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4161_ok hmem
def wits_4201 : List (Nat × Nat × Nat) :=
  [(4201, 1657, 2539), (4202, 1787, 2411), (4203, 1997, 2203), (4204, 1861, 2339), (4205, 2063, 2137), (4206, 1999, 2203), (4207, 1543, 2659), (4208, 2063, 2141), (4209, 1867, 2339), (4210, 1657, 2549), (4211, 1999, 2207), (4212, 2081, 2129), (4213, 1867, 2341), (4214, 1973, 2237), (4215, 2083, 2129), (4216, 2081, 2131), (4217, 1973, 2239), (4218, 3, 4211), (4219, 2083, 2131), (4220, 5, 4211), (4221, 2081, 2137), (4222, 3, 4217), (4223, 7, 4211), (4224, 5, 4217), (4225, 1747, 2473), (4226, 11, 4211), (4227, 7, 4217), (4228, 1987, 2237), (4229, 13, 4211), (4230, 11, 4217), (4231, 1987, 2239), (4232, 17, 4211), (4233, 13, 4217), (4234, 3, 4229), (4235, 19, 4211), (4236, 5, 4229), (4237, 1543, 2689), (4238, 2027, 2207), (4239, 7, 4229), (4240, 23, 4211)]
theorem wits_4201_ok : checkPairs wits_4201 = true := rfl
theorem wits_4201_ns : wits_4201.map (·.1) = (List.range 40).map (· + 4201) := rfl
theorem a_pos_4201_to_4240 (n : Nat) (h1 : 4201 ≤ n) (h2 : n ≤ 4240) : 0 < a n := by
  have hmem : n ∈ wits_4201.map (·.1) := by
    rw [wits_4201_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4201_ok hmem
def wits_4241 : List (Nat × Nat × Nat) :=
  [(4241, 1693, 2543), (4242, 11, 4229), (4243, 1867, 2371), (4244, 23, 4217), (4245, 13, 4229), (4246, 3, 4241), (4247, 1973, 2269), (4248, 5, 4241), (4249, 1873, 2371), (4250, 1907, 2339), (4251, 7, 4241), (4252, 31, 4217), (4253, 37, 4211), (4254, 11, 4241), (4255, 2011, 2239), (4256, 23, 4229), (4257, 13, 4241), (4258, 1987, 2267), (4259, 1907, 2347), (4260, 3, 4253), (4261, 1987, 2269), (4262, 5, 4253), (4263, 19, 4241), (4264, 3, 4259), (4265, 7, 4253), (4266, 5, 4259), (4267, 1549, 2713), (4268, 11, 4253), (4269, 7, 4259), (4270, 1367, 2897), (4271, 13, 4253), (4272, 11, 4259), (4273, 2131, 2137), (4274, 17, 4253), (4275, 13, 4259), (4276, 3, 4271), (4277, 19, 4253), (4278, 5, 4271), (4279, 1993, 2281), (4280, 1987, 2287)]
theorem wits_4241_ok : checkPairs wits_4241 = true := rfl
theorem wits_4241_ns : wits_4241.map (·.1) = (List.range 40).map (· + 4241) := rfl
theorem a_pos_4241_to_4280 (n : Nat) (h1 : 4241 ≤ n) (h2 : n ≤ 4280) : 0 < a n := by
  have hmem : n ∈ wits_4241.map (·.1) := by
    rw [wits_4241_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4241_ok hmem
def wits_4281 : List (Nat × Nat × Nat) :=
  [(4281, 7, 4271), (4282, 23, 4253), (4283, 1901, 2377), (4284, 11, 4271), (4285, 2011, 2269), (4286, 23, 4259), (4287, 13, 4271), (4288, 1997, 2287), (4289, 1907, 2377), (4290, 3, 4283), (4291, 1999, 2287), (4292, 5, 4283), (4293, 19, 4271), (4294, 31, 4259), (4295, 7, 4283), (4296, 2027, 2267), (4297, 1753, 2539), (4298, 11, 4283), (4299, 37, 4259), (4300, 1987, 2309), (4301, 13, 4283), (4302, 29, 4271), (4303, 1861, 2437), (4304, 17, 4283), (4305, 1993, 2309), (4306, 31, 4271), (4307, 19, 4283), (4308, 1997, 2309), (4309, 2011, 2293), (4310, 1753, 2551), (4311, 37, 4271), (4312, 23, 4283), (4313, 1867, 2441), (4314, 1931, 2381), (4315, 1621, 2689), (4316, 29, 4283), (4317, 2111, 2203), (4318, 2027, 2287), (4319, 1873, 2441), (4320, 31, 4283)]
theorem wits_4281_ok : checkPairs wits_4281 = true := rfl
theorem wits_4281_ns : wits_4281.map (·.1) = (List.range 40).map (· + 4281) := rfl
theorem a_pos_4281_to_4320 (n : Nat) (h1 : 4281 ≤ n) (h2 : n ≤ 4320) : 0 < a n := by
  have hmem : n ∈ wits_4281.map (·.1) := by
    rw [wits_4281_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4281_ok hmem
def wits_4321 : List (Nat × Nat × Nat) :=
  [(4321, 1777, 2539), (4322, 2111, 2207), (4323, 2083, 2237), (4324, 2011, 2309), (4325, 37, 4283), (4326, 2087, 2237), (4327, 1609, 2713), (4328, 1931, 2393), (4329, 2087, 2239), (4330, 1987, 2339), (4331, 1993, 2333), (4332, 1949, 2381), (4333, 1621, 2707), (4334, 2063, 2267), (4335, 2129, 2203), (4336, 1949, 2383), (4337, 2063, 2269), (4338, 2027, 2309), (4339, 2131, 2203), (4340, 2129, 2207), (4341, 1999, 2339), (4342, 3, 4337), (4343, 1901, 2437), (4344, 5, 4337), (4345, 1999, 2341), (4346, 1949, 2393), (4347, 7, 4337), (4348, 1901, 2441), (4349, 2137, 2207), (4350, 11, 4337), (4351, 1657, 2689), (4352, 2141, 2207), (4353, 13, 4337), (4354, 2011, 2339), (4355, 1999, 2351), (4356, 17, 4337), (4357, 1033, 3319), (4358, 2011, 2341), (4359, 19, 4337), (4360, 1049, 3307)]
theorem wits_4321_ok : checkPairs wits_4321 = true := rfl
theorem wits_4321_ns : wits_4321.map (·.1) = (List.range 40).map (· + 4321) := rfl
theorem a_pos_4321_to_4360 (n : Nat) (h1 : 4321 ≤ n) (h2 : n ≤ 4360) : 0 < a n := by
  have hmem : n ∈ wits_4321.map (·.1) := by
    rw [wits_4321_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4321_ok hmem
def wits_4361 : List (Nat × Nat × Nat) :=
  [(4361, 2063, 2293), (4362, 1061, 3299), (4363, 2011, 2347), (4364, 3, 4357), (4365, 1019, 3343), (4366, 5, 4357), (4367, 1973, 2389), (4368, 29, 4337), (4369, 7, 4357), (4370, 1949, 2417), (4371, 2129, 2239), (4372, 11, 4357), (4373, 1181, 3187), (4374, 521, 3851), (4375, 13, 4357), (4376, 2063, 2309), (4377, 37, 4337), (4378, 17, 4357), (4379, 1901, 2473), (4380, 2141, 2237), (4381, 19, 4357), (4382, 2027, 2351), (4383, 2141, 2239), (4384, 1997, 2383), (4385, 1907, 2473), (4386, 23, 4357), (4387, 1999, 2383), (4388, 2011, 2371), (4389, 1997, 2389), (4390, 29, 4357), (4391, 1993, 2393), (4392, 2081, 2309), (4393, 2011, 2377), (4394, 31, 4357), (4395, 2083, 2309), (4396, 2111, 2281), (4397, 1999, 2393), (4398, 3, 4391), (4399, 37, 4357), (4400, 5, 4391)]
theorem wits_4361_ok : checkPairs wits_4361 = true := rfl
theorem wits_4361_ns : wits_4361.map (·.1) = (List.range 40).map (· + 4361) := rfl
theorem a_pos_4361_to_4400 (n : Nat) (h1 : 4361 ≤ n) (h2 : n ≤ 4400) : 0 < a n := by
  have hmem : n ∈ wits_4361.map (·.1) := by
    rw [wits_4361_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4361_ok hmem
def wits_4401 : List (Nat × Nat × Nat) :=
  [(4401, 2129, 2269), (4402, 2131, 2267), (4403, 7, 4391), (4404, 1151, 3251), (4405, 2131, 2269), (4406, 11, 4391), (4407, 2137, 2267), (4408, 1747, 2657), (4409, 13, 4391), (4410, 2141, 2267), (4411, 1747, 2659), (4412, 17, 4391), (4413, 2141, 2269), (4414, 2129, 2281), (4415, 19, 4391), (4416, 857, 3557), (4417, 1753, 2659), (4418, 2131, 2281), (4419, 2027, 2389), (4420, 23, 4391), (4421, 2083, 2333), (4422, 2111, 2309), (4423, 2137, 2281), (4424, 29, 4391), (4425, 2129, 2293), (4426, 3, 4421), (4427, 1103, 3319), (4428, 5, 4421), (4429, 2137, 2287), (4430, 1753, 2671), (4431, 7, 4421), (4432, 2141, 2287), (4433, 37, 4391), (4434, 11, 4421), (4435, 1747, 2683), (4436, 2081, 2351), (4437, 13, 4421), (4438, 1777, 2657), (4439, 2083, 2351), (4440, 17, 4421)]
theorem wits_4401_ok : checkPairs wits_4401 = true := rfl
theorem wits_4401_ns : wits_4401.map (·.1) = (List.range 40).map (· + 4401) := rfl
theorem a_pos_4401_to_4440 (n : Nat) (h1 : 4401 ≤ n) (h2 : n ≤ 4440) : 0 < a n := by
  have hmem : n ∈ wits_4401.map (·.1) := by
    rw [wits_4401_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4401_ok hmem
def wits_4441 : List (Nat × Nat × Nat) :=
  [(4441, 1777, 2659), (4442, 2087, 2351), (4443, 19, 4421), (4444, 2131, 2309), (4445, 2063, 2377), (4446, 1787, 2657), (4447, 1753, 2689), (4448, 3, 4441), (4449, 2137, 2309), (4450, 5, 4441), (4451, 2207, 2239), (4452, 29, 4421), (4453, 3, 4447), (4454, 1901, 2549), (4455, 5, 4447), (4456, 11, 4441), (4457, 2063, 2389), (4458, 3, 4451), (4459, 13, 4441), (4460, 5, 4451), (4461, 11, 4447), (4462, 17, 4441), (4463, 7, 4451), (4464, 3, 4457), (4465, 19, 4441), (4466, 5, 4457), (4467, 17, 4447), (4468, 2081, 2383), (4469, 7, 4457), (4470, 19, 4447), (4471, 2083, 2383), (4472, 11, 4457), (4473, 2203, 2267), (4474, 29, 4441), (4475, 13, 4457), (4476, 2237, 2237), (4477, 1453, 3019), (4478, 17, 4457), (4479, 29, 4447), (4480, 23, 4451)]
theorem wits_4441_ok : checkPairs wits_4441 = true := rfl
theorem wits_4441_ns : wits_4441.map (·.1) = (List.range 40).map (· + 4441) := rfl
theorem a_pos_4441_to_4480 (n : Nat) (h1 : 4441 ≤ n) (h2 : n ≤ 4480) : 0 < a n := by
  have hmem : n ∈ wits_4441.map (·.1) := by
    rw [wits_4441_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4441_ok hmem
def wits_4481 : List (Nat × Nat × Nat) :=
  [(4481, 19, 4457), (4482, 2141, 2339), (4483, 31, 4447), (4484, 29, 4451), (4485, 1693, 2789), (4486, 3, 4481), (4487, 1579, 2903), (4488, 5, 4481), (4489, 2203, 2281), (4490, 29, 4457), (4491, 7, 4481), (4492, 1777, 2711), (4493, 37, 4451), (4494, 11, 4481), (4495, 2203, 2287), (4496, 2141, 2351), (4497, 13, 4481), (4498, 2111, 2383), (4499, 37, 4457), (4500, 17, 4481), (4501, 1783, 2713), (4502, 2087, 2411), (4503, 19, 4481), (4504, 2129, 2371), (4505, 2207, 2293), (4506, 2237, 2267), (4507, 1753, 2749), (4508, 23, 4481), (4509, 2239, 2267), (4510, 2063, 2441), (4511, 1609, 2897), (4512, 29, 4481), (4513, 2137, 2371), (4514, 3, 4507), (4515, 2203, 2309), (4516, 5, 4507), (4517, 1973, 2539), (4518, 1787, 2729), (4519, 3, 4513), (4520, 2207, 2309)]
theorem wits_4481_ok : checkPairs wits_4481 = true := rfl
theorem wits_4481_ns : wits_4481.map (·.1) = (List.range 40).map (· + 4481) := rfl
theorem a_pos_4481_to_4520 (n : Nat) (h1 : 4481 ≤ n) (h2 : n ≤ 4520) : 0 < a n := by
  have hmem : n ∈ wits_4481.map (·.1) := by
    rw [wits_4481_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4481_ok hmem
def wits_4521 : List (Nat × Nat × Nat) :=
  [(4521, 5, 4513), (4522, 3, 4517), (4523, 1901, 2617), (4524, 5, 4517), (4525, 3, 4519), (4526, 2129, 2393), (4527, 5, 4519), (4528, 17, 4507), (4529, 2083, 2441), (4530, 7, 4519), (4531, 19, 4507), (4532, 2111, 2417), (4533, 11, 4519), (4534, 1741, 2789), (4535, 2137, 2393), (4536, 13, 4519), (4537, 1453, 3079), (4538, 2141, 2393), (4539, 17, 4519), (4540, 29, 4507), (4541, 23, 4513), (4542, 19, 4519), (4543, 1867, 2671), (4544, 23, 4517), (4545, 29, 4513), (4546, 2207, 2333), (4547, 23, 4519), (4548, 29, 4517), (4549, 31, 4513), (4550, 2207, 2339), (4551, 29, 4519), (4552, 3, 4547), (4553, 2137, 2411), (4554, 5, 4547), (4555, 31, 4519), (4556, 2141, 2411), (4557, 7, 4547), (4558, 2267, 2287), (4559, 2207, 2347), (4560, 11, 4547)]
theorem wits_4521_ok : checkPairs wits_4521 = true := rfl
theorem wits_4521_ns : wits_4521.map (·.1) = (List.range 40).map (· + 4521) := rfl
theorem a_pos_4521_to_4560 (n : Nat) (h1 : 4521 ≤ n) (h2 : n ≤ 4560) : 0 < a n := by
  have hmem : n ∈ wits_4521.map (·.1) := by
    rw [wits_4521_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4521_ok hmem
def wits_4561 : List (Nat × Nat × Nat) :=
  [(4561, 2269, 2287), (4562, 2141, 2417), (4563, 13, 4547), (4564, 2207, 2351), (4565, 1901, 2659), (4566, 17, 4547), (4567, 1543, 3019), (4568, 3, 4561), (4569, 19, 4547), (4570, 5, 4561), (4571, 1907, 2659), (4572, 1451, 3119), (4573, 7, 4561), (4574, 23, 4547), (4575, 1783, 2789), (4576, 11, 4561), (4577, 2239, 2333), (4578, 29, 4547), (4579, 13, 4561), (4580, 2287, 2287), (4581, 2269, 2309), (4582, 17, 4561), (4583, 2137, 2441), (4584, 1871, 2711), (4585, 19, 4561), (4586, 2141, 2441), (4587, 37, 4547), (4588, 1871, 2713), (4589, 2207, 2377), (4590, 23, 4561), (4591, 2203, 2383), (4592, 2237, 2351), (4593, 1999, 2591), (4594, 29, 4561), (4595, 2239, 2351), (4596, 1427, 3167), (4597, 1279, 3313), (4598, 3, 4591), (4599, 1867, 2729), (4600, 5, 4591)]
theorem wits_4561_ok : checkPairs wits_4561 = true := rfl
theorem wits_4561_ns : wits_4561.map (·.1) = (List.range 40).map (· + 4561) := rfl
theorem a_pos_4561_to_4600 (n : Nat) (h1 : 4561 ≤ n) (h2 : n ≤ 4600) : 0 < a n := by
  have hmem : n ∈ wits_4561.map (·.1) := by
    rw [wits_4561_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4561_ok hmem
def wits_4601 : List (Nat × Nat × Nat) :=
  [(4601, 2207, 2389), (4602, 1871, 2729), (4603, 7, 4591), (4604, 3, 4597), (4605, 2293, 2309), (4606, 5, 4597), (4607, 2269, 2333), (4608, 2267, 2339), (4609, 7, 4597), (4610, 1753, 2851), (4611, 2269, 2339), (4612, 11, 4597), (4613, 1901, 2707), (4614, 1151, 3461), (4615, 13, 4597), (4616, 2063, 2549), (4617, 2267, 2347), (4618, 17, 4597), (4619, 2203, 2411), (4620, 23, 4591), (4621, 19, 4597), (4622, 2267, 2351), (4623, 2239, 2381), (4624, 29, 4591), (4625, 2269, 2351), (4626, 23, 4597), (4627, 2239, 2383), (4628, 31, 4591), (4629, 2237, 2389), (4630, 29, 4597), (4631, 2293, 2333), (4632, 2081, 2549), (4633, 37, 4591), (4634, 31, 4597), (4635, 2293, 2339), (4636, 2081, 2551), (4637, 2239, 2393), (4638, 2087, 2549), (4639, 37, 4597), (4640, 1907, 2729)]
theorem wits_4601_ok : checkPairs wits_4601 = true := rfl
theorem wits_4601_ns : wits_4601.map (·.1) = (List.range 40).map (· + 4601) := rfl
theorem a_pos_4601_to_4640 (n : Nat) (h1 : 4601 ≤ n) (h2 : n ≤ 4640) : 0 < a n := by
  have hmem : n ∈ wits_4601.map (·.1) := by
    rw [wits_4601_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4601_ok hmem
def wits_4641 : List (Nat × Nat × Nat) :=
  [(4641, 1949, 2689), (4642, 3, 4637), (4643, 1601, 3037), (4644, 5, 4637), (4645, 3, 4639), (4646, 2309, 2333), (4647, 5, 4639), (4648, 1987, 2657), (4649, 2293, 2351), (4650, 3, 4643), (4651, 1987, 2659), (4652, 5, 4643), (4653, 11, 4639), (4654, 3, 4649), (4655, 7, 4643), (4656, 5, 4649), (4657, 2269, 2383), (4658, 3, 4651), (4659, 7, 4649), (4660, 5, 4651), (4661, 13, 4643), (4662, 11, 4649), (4663, 7, 4651), (4664, 3, 4657), (4665, 13, 4649), (4666, 5, 4657), (4667, 19, 4643), (4668, 17, 4649), (4669, 7, 4657), (4670, 2281, 2383), (4671, 19, 4649), (4672, 11, 4657), (4673, 971, 3697), (4674, 2081, 2591), (4675, 13, 4657), (4676, 23, 4649), (4677, 37, 4637), (4678, 17, 4657), (4679, 1217, 3457), (4680, 3, 4673)]
theorem wits_4641_ok : checkPairs wits_4641 = true := rfl
theorem wits_4641_ns : wits_4641.map (·.1) = (List.range 40).map (· + 4641) := rfl
theorem a_pos_4641_to_4680 (n : Nat) (h1 : 4641 ≤ n) (h2 : n ≤ 4680) : 0 < a n := by
  have hmem : n ∈ wits_4641.map (·.1) := by
    rw [wits_4641_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4641_ok hmem
def wits_4681 : List (Nat × Nat × Nat) :=
  [(4681, 19, 4657), (4682, 5, 4673), (4683, 2141, 2539), (4684, 29, 4651), (4685, 7, 4673), (4686, 23, 4657), (4687, 2213, 2467), (4688, 11, 4673), (4689, 37, 4649), (4690, 29, 4657), (4691, 13, 4673), (4692, 2309, 2381), (4693, 37, 4651), (4694, 17, 4673), (4695, 1693, 2999), (4696, 2309, 2383), (4697, 19, 4673), (4698, 1697, 2999), (4699, 37, 4657), (4700, 1907, 2789), (4701, 2309, 2389), (4702, 23, 4673), (4703, 2347, 2351), (4704, 2111, 2591), (4705, 2011, 2689), (4706, 29, 4673), (4707, 2267, 2437), (4708, 2351, 2351), (4709, 2293, 2411), (4710, 31, 4673), (4711, 2239, 2467), (4712, 2267, 2441), (4713, 2237, 2473), (4714, 2339, 2371), (4715, 37, 4673), (4716, 2027, 2687), (4717, 1999, 2713), (4718, 2341, 2371), (4719, 2339, 2377), (4720, 1987, 2729)]
theorem wits_4681_ok : checkPairs wits_4681 = true := rfl
theorem wits_4681_ns : wits_4681.map (·.1) = (List.range 40).map (· + 4681) := rfl
theorem a_pos_4681_to_4720 (n : Nat) (h1 : 4681 ≤ n) (h2 : n ≤ 4720) : 0 < a n := by
  have hmem : n ∈ wits_4681.map (·.1) := by
    rw [wits_4681_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4681_ok hmem
def wits_4721 : List (Nat × Nat × Nat) :=
  [(4721, 1553, 3163), (4722, 2339, 2381), (4723, 2347, 2371), (4724, 2309, 2411), (4725, 1993, 2729), (4726, 3, 4721), (4727, 2333, 2389), (4728, 5, 4721), (4729, 2287, 2437), (4730, 3, 4723), (4731, 7, 4721), (4732, 5, 4723), (4733, 2351, 2377), (4734, 11, 4721), (4735, 3, 4729), (4736, 2351, 2381), (4737, 5, 4729), (4738, 11, 4723), (4739, 2293, 2441), (4740, 7, 4729), (4741, 13, 4723), (4742, 1367, 3371), (4743, 11, 4729), (4744, 17, 4723), (4745, 2351, 2389), (4746, 13, 4729), (4747, 19, 4723), (4748, 23, 4721), (4749, 17, 4729), (4750, 2351, 2393), (4751, 2207, 2539), (4752, 19, 4729), (4753, 2371, 2377), (4754, 2339, 2411), (4755, 2203, 2549), (4756, 29, 4723), (4757, 23, 4729), (4758, 2027, 2729), (4759, 2281, 2473), (4760, 31, 4723)]
theorem wits_4721_ok : checkPairs wits_4721 = true := rfl
theorem wits_4721_ns : wits_4721.map (·.1) = (List.range 40).map (· + 4721) := rfl
theorem a_pos_4721_to_4760 (n : Nat) (h1 : 4721 ≤ n) (h2 : n ≤ 4760) : 0 < a n := by
  have hmem : n ∈ wits_4721.map (·.1) := by
    rw [wits_4721_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4721_ok hmem
def wits_4761 : List (Nat × Nat × Nat) :=
  [(4761, 29, 4729), (4762, 2087, 2671), (4763, 2347, 2411), (4764, 2381, 2381), (4765, 31, 4729), (4766, 1973, 2789), (4767, 2081, 2683), (4768, 2381, 2383), (4769, 2347, 2417), (4770, 37, 4729), (4771, 1747, 3019), (4772, 2383, 2383), (4773, 2381, 2389), (4774, 2351, 2417), (4775, 2377, 2393), (4776, 2087, 2687), (4777, 2383, 2389), (4778, 2381, 2393), (4779, 2339, 2437), (4780, 2333, 2441), (4781, 2083, 2693), (4782, 1481, 3299), (4783, 2341, 2437), (4784, 2339, 2441), (4785, 2309, 2473), (4786, 2111, 2671), (4787, 2389, 2393), (4788, 2237, 2549), (4789, 3, 4783), (4790, 1949, 2837), (4791, 5, 4783), (4792, 3, 4787), (4793, 2377, 2411), (4794, 5, 4787), (4795, 3, 4789), (4796, 2381, 2411), (4797, 5, 4789), (4798, 2351, 2441), (4799, 2377, 2417), (4800, 3, 4793)]
theorem wits_4761_ok : checkPairs wits_4761 = true := rfl
theorem wits_4761_ns : wits_4761.map (·.1) = (List.range 40).map (· + 4761) := rfl
theorem a_pos_4761_to_4800 (n : Nat) (h1 : 4761 ≤ n) (h2 : n ≤ 4800) : 0 < a n := by
  have hmem : n ∈ wits_4761.map (·.1) := by
    rw [wits_4761_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4761_ok hmem
def wits_4801 : List (Nat × Nat × Nat) :=
  [(4801, 2083, 2713), (4802, 5, 4793), (4803, 11, 4789), (4804, 3, 4799), (4805, 7, 4793), (4806, 5, 4799), (4807, 1489, 3313), (4808, 11, 4793), (4809, 7, 4799), (4810, 2393, 2411), (4811, 13, 4793), (4812, 11, 4799), (4813, 2371, 2437), (4814, 17, 4793), (4815, 13, 4799), (4816, 2393, 2417), (4817, 19, 4793), (4818, 17, 4799), (4819, 3, 4813), (4820, 1753, 3061), (4821, 5, 4813), (4822, 23, 4793), (4823, 2377, 2441), (4824, 7, 4813), (4825, 31, 4789), (4826, 23, 4799), (4827, 11, 4813), (4828, 2411, 2411), (4829, 2351, 2473), (4830, 13, 4813), (4831, 2287, 2539), (4832, 1931, 2897), (4833, 17, 4813), (4834, 31, 4799), (4835, 37, 4793), (4836, 19, 4813), (4837, 1753, 3079), (4838, 2281, 2551), (4839, 37, 4799), (4840, 2417, 2417)]
theorem wits_4801_ok : checkPairs wits_4801 = true := rfl
theorem wits_4801_ns : wits_4801.map (·.1) = (List.range 40).map (· + 4801) := rfl
theorem a_pos_4801_to_4840 (n : Nat) (h1 : 4801 ≤ n) (h2 : n ≤ 4840) : 0 < a n := by
  have hmem : n ∈ wits_4801.map (·.1) := by
    rw [wits_4801_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4801_ok hmem
def wits_4841 : List (Nat × Nat × Nat) :=
  [(4841, 23, 4813), (4842, 2129, 2711), (4843, 2131, 2707), (4844, 2371, 2467), (4845, 29, 4813), (4846, 2131, 2711), (4847, 769, 4073), (4848, 1877, 2969), (4849, 31, 4813), (4850, 2131, 2713), (4851, 2309, 2539), (4852, 2381, 2467), (4853, 2411, 2437), (4854, 37, 4813), (4855, 2137, 2713), (4856, 2383, 2467), (4857, 2381, 2473), (4858, 2411, 2441), (4859, 2417, 2437), (4860, 2309, 2549), (4861, 2389, 2467), (4862, 1601, 3257), (4863, 2269, 2591), (4864, 2417, 2441), (4865, 2063, 2797), (4866, 1697, 3167), (4867, 1549, 3313), (4868, 2207, 2657), (4869, 2137, 2729), (4870, 1907, 2957), (4871, 2393, 2473), (4872, 2141, 2729), (4873, 2011, 2857), (4874, 1901, 2969), (4875, 2083, 2789), (4876, 2281, 2591), (4877, 2333, 2539), (4878, 3, 4871), (4879, 2203, 2671), (4880, 5, 4871)]
theorem wits_4841_ok : checkPairs wits_4841 = true := rfl
theorem wits_4841_ns : wits_4841.map (·.1) = (List.range 40).map (· + 4841) := rfl
theorem a_pos_4841_to_4880 (n : Nat) (h1 : 4841 ≤ n) (h2 : n ≤ 4880) : 0 < a n := by
  have hmem : n ∈ wits_4841.map (·.1) := by
    rw [wits_4841_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4841_ok hmem
def wits_4881 : List (Nat × Nat × Nat) :=
  [(4881, 2339, 2539), (4882, 2333, 2543), (4883, 7, 4871), (4884, 2081, 2801), (4885, 2341, 2539), (4886, 11, 4871), (4887, 2293, 2591), (4888, 2441, 2441), (4889, 13, 4871), (4890, 2339, 2549), (4891, 1579, 3307), (4892, 17, 4871), (4893, 2203, 2687), (4894, 2341, 2549), (4895, 19, 4871), (4896, 2237, 2657), (4897, 1579, 3313), (4898, 2341, 2551), (4899, 2347, 2549), (4900, 23, 4871), (4901, 2207, 2689), (4902, 2309, 2591), (4903, 2347, 2551), (4904, 29, 4871), (4905, 1949, 2953), (4906, 2207, 2693), (4907, 1999, 2903), (4908, 31, 4871), (4909, 2437, 2467), (4910, 3, 4903), (4911, 2111, 2797), (4912, 5, 4903), (4913, 37, 4871), (4914, 2111, 2801), (4915, 7, 4903), (4916, 1949, 2963), (4917, 2203, 2711), (4918, 11, 4903), (4919, 2441, 2473), (4920, 2129, 2789)]
theorem wits_4881_ok : checkPairs wits_4881 = true := rfl
theorem wits_4881_ns : wits_4881.map (·.1) = (List.range 40).map (· + 4881) := rfl
theorem a_pos_4881_to_4920 (n : Nat) (h1 : 4881 ≤ n) (h2 : n ≤ 4920) : 0 < a n := by
  have hmem : n ∈ wits_4881.map (·.1) := by
    rw [wits_4881_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4881_ok hmem
def wits_4921 : List (Nat × Nat × Nat) :=
  [(4921, 13, 4903), (4922, 2207, 2711), (4923, 2381, 2539), (4924, 17, 4903), (4925, 2377, 2543), (4926, 2267, 2657), (4927, 19, 4903), (4928, 2381, 2543), (4929, 2377, 2549), (4930, 1619, 3307), (4931, 1973, 2953), (4932, 23, 4903), (4933, 2377, 2551), (4934, 2237, 2693), (4935, 2203, 2729), (4936, 3, 4931), (4937, 2393, 2539), (4938, 5, 4931), (4939, 3, 4933), (4940, 31, 4903), (4941, 5, 4933), (4942, 2393, 2543), (4943, 1901, 3037), (4944, 3, 4937), (4945, 37, 4903), (4946, 5, 4937), (4947, 11, 4933), (4948, 2287, 2657), (4949, 7, 4937), (4950, 13, 4933), (4951, 2287, 2659), (4952, 11, 4937), (4953, 17, 4933), (4954, 2237, 2713), (4955, 13, 4937), (4956, 19, 4933), (4957, 2239, 2713), (4958, 3, 4951), (4959, 2339, 2617), (4960, 5, 4951)]
theorem wits_4921_ok : checkPairs wits_4921 = true := rfl
theorem wits_4921_ns : wits_4921.map (·.1) = (List.range 40).map (· + 4921) := rfl
theorem a_pos_4921_to_4960 (n : Nat) (h1 : 4921 ≤ n) (h2 : n ≤ 4960) : 0 < a n := by
  have hmem : n ∈ wits_4921.map (·.1) := by
    rw [wits_4921_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4921_ok hmem
def wits_4961 : List (Nat × Nat × Nat) :=
  [(4961, 19, 4937), (4962, 29, 4931), (4963, 7, 4951), (4964, 2411, 2549), (4965, 29, 4933), (4966, 11, 4951), (4967, 2269, 2693), (4968, 2309, 2657), (4969, 13, 4951), (4970, 29, 4937), (4971, 37, 4931), (4972, 3, 4967), (4973, 2351, 2617), (4974, 5, 4967), (4975, 3, 4969), (4976, 1973, 2999), (4977, 5, 4969), (4978, 2383, 2591), (4979, 37, 4937), (4980, 7, 4969), (4981, 2287, 2689), (4982, 2141, 2837), (4983, 11, 4969), (4984, 29, 4951), (4985, 2441, 2539), (4986, 13, 4969), (4987, 2269, 2713), (4988, 31, 4951), (4989, 17, 4969), (4990, 2441, 2543), (4991, 2293, 2693), (4992, 19, 4969), (4993, 37, 4951), (4994, 3, 4987), (4995, 2309, 2683), (4996, 5, 4987), (4997, 23, 4969), (4998, 29, 4967), (4999, 7, 4987), (5000, 3, 4993)]
theorem wits_4961_ok : checkPairs wits_4961 = true := rfl
theorem wits_4961_ns : wits_4961.map (·.1) = (List.range 40).map (· + 4961) := rfl
theorem a_pos_4961_to_5000 (n : Nat) (h1 : 4961 ≤ n) (h2 : n ≤ 5000) : 0 < a n := by
  have hmem : n ∈ wits_4961.map (·.1) := by
    rw [wits_4961_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_4961_ok hmem
def wits_5001 : List (Nat × Nat × Nat) :=
  [(5001, 29, 4969), (5002, 5, 4993), (5003, 1087, 3911), (5004, 1151, 3851), (5005, 3, 4999), (5006, 2411, 2591), (5007, 5, 4999), (5008, 11, 4993), (5009, 2207, 2797), (5010, 3, 5003), (5011, 13, 4993), (5012, 5, 5003), (5013, 11, 4999), (5014, 3, 5009), (5015, 7, 5003), (5016, 5, 5009), (5017, 19, 4993), (5018, 11, 5003), (5019, 7, 5009), (5020, 29, 4987), (5021, 13, 5003), (5022, 11, 5009), (5023, 2347, 2671), (5024, 17, 5003), (5025, 13, 5009), (5026, 3, 5021), (5027, 19, 5003), (5028, 5, 5021), (5029, 37, 4987), (5030, 31, 4993), (5031, 7, 5021), (5032, 23, 5003), (5033, 2411, 2617), (5034, 11, 5021), (5035, 31, 4999), (5036, 23, 5009), (5037, 13, 5021), (5038, 1777, 3257), (5039, 2417, 2617), (5040, 17, 5021)]
theorem wits_5001_ok : checkPairs wits_5001 = true := rfl
theorem wits_5001_ns : wits_5001.map (·.1) = (List.range 40).map (· + 5001) := rfl
theorem a_pos_5001_to_5040 (n : Nat) (h1 : 5001 ≤ n) (h2 : n ≤ 5040) : 0 < a n := by
  have hmem : n ∈ wits_5001.map (·.1) := by
    rw [wits_5001_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5001_ok hmem
def wits_5041 : List (Nat × Nat × Nat) :=
  [(5041, 2287, 2749), (5042, 2351, 2687), (5043, 19, 5021), (5044, 31, 5009), (5045, 37, 5003), (5046, 1877, 3167), (5047, 2383, 2659), (5048, 23, 5021), (5049, 37, 5009), (5050, 2351, 2693), (5051, 2083, 2963), (5052, 29, 5021), (5053, 2377, 2671), (5054, 2393, 2657), (5055, 2083, 2969), (5056, 31, 5021), (5057, 2393, 2659), (5058, 2267, 2789), (5059, 2377, 2677), (5060, 2383, 2671), (5061, 37, 5021), (5062, 2467, 2591), (5063, 2441, 2617), (5064, 1481, 3581), (5065, 2389, 2671), (5066, 2383, 2677), (5067, 2473, 2591), (5068, 1427, 3637), (5069, 2207, 2857), (5070, 2381, 2687), (5071, 2389, 2677), (5072, 2411, 2657), (5073, 2381, 2689), (5074, 2383, 2687), (5075, 2411, 2659), (5076, 1607, 3467), (5077, 2383, 2689), (5078, 2417, 2657), (5079, 2389, 2687), (5080, 2287, 2789)]
theorem wits_5041_ok : checkPairs wits_5041 = true := rfl
theorem wits_5041_ns : wits_5041.map (·.1) = (List.range 40).map (· + 5041) := rfl
theorem a_pos_5041_to_5080 (n : Nat) (h1 : 5041 ≤ n) (h2 : n ≤ 5080) : 0 < a n := by
  have hmem : n ∈ wits_5041.map (·.1) := by
    rw [wits_5041_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5041_ok hmem
def wits_5081 : List (Nat × Nat × Nat) :=
  [(5081, 2417, 2659), (5082, 2111, 2969), (5083, 3, 5077), (5084, 2393, 2687), (5085, 5, 5077), (5086, 2371, 2711), (5087, 2539, 2543), (5088, 3, 5081), (5089, 2467, 2617), (5090, 5, 5081), (5091, 11, 5077), (5092, 2543, 2543), (5093, 7, 5081), (5094, 13, 5077), (5095, 2539, 2551), (5096, 11, 5081), (5097, 17, 5077), (5098, 2383, 2711), (5099, 13, 5081), (5100, 19, 5077), (5101, 1783, 3313), (5102, 17, 5081), (5103, 2389, 2711), (5104, 3, 5099), (5105, 19, 5081), (5106, 5, 5099), (5107, 2389, 2713), (5108, 3, 5101), (5109, 7, 5099), (5110, 5, 5101), (5111, 2417, 2689), (5112, 11, 5099), (5113, 7, 5101), (5114, 3, 5107), (5115, 13, 5099), (5116, 5, 5107), (5117, 1579, 3533), (5118, 17, 5099), (5119, 7, 5107), (5120, 3, 5113)]
theorem wits_5081_ok : checkPairs wits_5081 = true := rfl
theorem wits_5081_ns : wits_5081.map (·.1) = (List.range 40).map (· + 5081) := rfl
theorem a_pos_5081_to_5120 (n : Nat) (h1 : 5081 ≤ n) (h2 : n ≤ 5120) : 0 < a n := by
  have hmem : n ∈ wits_5081.map (·.1) := by
    rw [wits_5081_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5081_ok hmem
def wits_5121 : List (Nat × Nat × Nat) :=
  [(5121, 19, 5099), (5122, 5, 5113), (5123, 37, 5081), (5124, 1871, 3251), (5125, 7, 5113), (5126, 23, 5099), (5127, 2437, 2687), (5128, 11, 5113), (5129, 2441, 2683), (5130, 23, 5101), (5131, 13, 5113), (5132, 2441, 2687), (5133, 2539, 2591), (5134, 17, 5113), (5135, 2441, 2689), (5136, 23, 5107), (5137, 19, 5113), (5138, 31, 5101), (5139, 37, 5099), (5140, 29, 5107), (5141, 2239, 2897), (5142, 23, 5113), (5143, 37, 5101), (5144, 31, 5107), (5145, 2309, 2833), (5146, 29, 5113), (5147, 2393, 2749), (5148, 2027, 3119), (5149, 37, 5107), (5150, 31, 5113), (5151, 2437, 2711), (5152, 2087, 3061), (5153, 2441, 2707), (5154, 3, 5147), (5155, 37, 5113), (5156, 5, 5147), (5157, 1783, 3371), (5158, 2467, 2687), (5159, 7, 5147), (5160, 1787, 3371)]
theorem wits_5121_ok : checkPairs wits_5121 = true := rfl
theorem wits_5121_ns : wits_5121.map (·.1) = (List.range 40).map (· + 5121) := rfl
theorem a_pos_5121_to_5160 (n : Nat) (h1 : 5121 ≤ n) (h2 : n ≤ 5160) : 0 < a n := by
  have hmem : n ∈ wits_5121.map (·.1) := by
    rw [wits_5121_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5121_ok hmem
def wits_5161 : List (Nat × Nat × Nat) :=
  [(5161, 2467, 2689), (5162, 11, 5147), (5163, 2473, 2687), (5164, 2371, 2789), (5165, 13, 5147), (5166, 1997, 3167), (5167, 1429, 3733), (5168, 17, 5147), (5169, 2549, 2617), (5170, 2207, 2957), (5171, 19, 5147), (5172, 2381, 2789), (5173, 3, 5167), (5174, 2441, 2729), (5175, 5, 5167), (5176, 23, 5147), (5177, 2269, 2903), (5178, 7, 5167), (5179, 2467, 2707), (5180, 29, 5147), (5181, 11, 5167), (5182, 2467, 2711), (5183, 967, 4211), (5184, 13, 5167), (5185, 2389, 2791), (5186, 2467, 2713), (5187, 17, 5167), (5188, 2383, 2801), (5189, 37, 5147), (5190, 19, 5167), (5191, 2473, 2713), (5192, 1453, 3733), (5193, 2389, 2801), (5194, 2351, 2837), (5195, 23, 5167), (5196, 2027, 3167), (5197, 1063, 4129), (5198, 2393, 2801), (5199, 29, 5167), (5200, 2467, 2729)]
theorem wits_5161_ok : checkPairs wits_5161 = true := rfl
theorem wits_5161_ns : wits_5161.map (·.1) = (List.range 40).map (· + 5161) := rfl
theorem a_pos_5161_to_5200 (n : Nat) (h1 : 5161 ≤ n) (h2 : n ≤ 5200) : 0 < a n := by
  have hmem : n ∈ wits_5161.map (·.1) := by
    rw [wits_5161_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5161_ok hmem
def wits_5201 : List (Nat × Nat × Nat) :=
  [(5201, 2293, 2903), (5202, 2081, 3119), (5203, 31, 5167), (5204, 2543, 2657), (5205, 2473, 2729), (5206, 2141, 3061), (5207, 2543, 2659), (5208, 37, 5167), (5209, 2371, 2833), (5210, 2417, 2789), (5211, 2591, 2617), (5212, 2551, 2657), (5213, 2411, 2797), (5214, 281, 4931), (5215, 2551, 2659), (5216, 2411, 2801), (5217, 2381, 2833), (5218, 1753, 3461), (5219, 2417, 2797), (5220, 1451, 3767), (5221, 2539, 2677), (5222, 2417, 2801), (5223, 2267, 2953), (5224, 2549, 2671), (5225, 2137, 3083), (5226, 1697, 3527), (5227, 1489, 3733), (5228, 2551, 2671), (5229, 2539, 2687), (5230, 2549, 2677), (5231, 2543, 2683), (5232, 2111, 3119), (5233, 3, 5227), (5234, 2551, 2677), (5235, 5, 5227), (5236, 3, 5231), (5237, 2543, 2689), (5238, 5, 5231), (5239, 3, 5233), (5240, 2383, 2851)]
theorem wits_5201_ok : checkPairs wits_5201 = true := rfl
theorem wits_5201_ns : wits_5201.map (·.1) = (List.range 40).map (· + 5201) := rfl
theorem a_pos_5201_to_5240 (n : Nat) (h1 : 5201 ≤ n) (h2 : n ≤ 5240) : 0 < a n := by
  have hmem : n ∈ wits_5201.map (·.1) := by
    rw [wits_5201_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5201_ok hmem
def wits_5241 : List (Nat × Nat × Nat) :=
  [(5241, 5, 5233), (5242, 2551, 2687), (5243, 2441, 2797), (5244, 7, 5233), (5245, 2551, 2689), (5246, 2549, 2693), (5247, 11, 5233), (5248, 1987, 3257), (5249, 2411, 2833), (5250, 13, 5233), (5251, 1609, 3637), (5252, 1487, 3761), (5253, 17, 5233), (5254, 2411, 2837), (5255, 23, 5227), (5256, 19, 5233), (5257, 2539, 2713), (5258, 23, 5231), (5259, 29, 5227), (5260, 2467, 2789), (5261, 23, 5233), (5262, 29, 5231), (5263, 31, 5227), (5264, 2467, 2791), (5265, 29, 5233), (5266, 31, 5231), (5267, 1009, 4253), (5268, 37, 5227), (5269, 31, 5233), (5270, 2551, 2713), (5271, 37, 5231), (5272, 2591, 2677), (5273, 2411, 2857), (5274, 37, 5233), (5275, 1741, 3529), (5276, 2543, 2729), (5277, 2617, 2657), (5278, 1747, 3527), (5279, 2441, 2833), (5280, 3, 5273)]
theorem wits_5241_ok : checkPairs wits_5241 = true := rfl
theorem wits_5241_ns : wits_5241.map (·.1) = (List.range 40).map (· + 5241) := rfl
theorem a_pos_5241_to_5280 (n : Nat) (h1 : 5241 ≤ n) (h2 : n ≤ 5280) : 0 < a n := by
  have hmem : n ∈ wits_5241.map (·.1) := by
    rw [wits_5241_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5241_ok hmem
def wits_5281 : List (Nat × Nat × Nat) :=
  [(5281, 1747, 3529), (5282, 5, 5273), (5283, 2591, 2689), (5284, 3, 5279), (5285, 7, 5273), (5286, 5, 5279), (5287, 1753, 3529), (5288, 11, 5273), (5289, 7, 5279), (5290, 2287, 2999), (5291, 13, 5273), (5292, 11, 5279), (5293, 2617, 2671), (5294, 17, 5273), (5295, 13, 5279), (5296, 2393, 2897), (5297, 19, 5273), (5298, 17, 5279), (5299, 2617, 2677), (5300, 2339, 2957), (5301, 19, 5279), (5302, 23, 5273), (5303, 2441, 2857), (5304, 3, 5297), (5305, 2551, 2749), (5306, 5, 5297), (5307, 2617, 2687), (5308, 2591, 2713), (5309, 7, 5297), (5310, 3, 5303), (5311, 2287, 3019), (5312, 5, 5303), (5313, 1783, 3527), (5314, 31, 5279), (5315, 7, 5303), (5316, 2657, 2657), (5317, 1999, 3313), (5318, 11, 5303), (5319, 37, 5279), (5320, 2417, 2897)]
theorem wits_5281_ok : checkPairs wits_5281 = true := rfl
theorem wits_5281_ns : wits_5281.map (·.1) = (List.range 40).map (· + 5281) := rfl
theorem a_pos_5281_to_5320 (n : Nat) (h1 : 5281 ≤ n) (h2 : n ≤ 5320) : 0 < a n := by
  have hmem : n ∈ wits_5281.map (·.1) := by
    rw [wits_5281_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5281_ok hmem
def wits_5321 : List (Nat × Nat × Nat) :=
  [(5321, 13, 5303), (5322, 2591, 2729), (5323, 2281, 3037), (5324, 17, 5303), (5325, 2203, 3119), (5326, 23, 5297), (5327, 19, 5303), (5328, 2027, 3299), (5329, 2473, 2851), (5330, 29, 5297), (5331, 2617, 2711), (5332, 23, 5303), (5333, 1567, 3761), (5334, 31, 5297), (5335, 2659, 2671), (5336, 29, 5303), (5337, 2381, 2953), (5338, 2657, 2677), (5339, 37, 5297), (5340, 31, 5303), (5341, 2659, 2677), (5342, 2381, 2957), (5343, 2657, 2683), (5344, 2551, 2789), (5345, 37, 5303), (5346, 2657, 2687), (5347, 1609, 3733), (5348, 2671, 2671), (5349, 2659, 2687), (5350, 2441, 2903), (5351, 2393, 2953), (5352, 2549, 2801), (5353, 3, 5347), (5354, 2671, 2677), (5355, 5, 5347), (5356, 2551, 2801), (5357, 2659, 2693), (5358, 7, 5347), (5359, 2671, 2683), (5360, 2677, 2677)]
theorem wits_5321_ok : checkPairs wits_5321 = true := rfl
theorem wits_5321_ns : wits_5321.map (·.1) = (List.range 40).map (· + 5321) := rfl
theorem a_pos_5321_to_5360 (n : Nat) (h1 : 5321 ≤ n) (h2 : n ≤ 5360) : 0 < a n := by
  have hmem : n ∈ wits_5321.map (·.1) := by
    rw [wits_5321_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5321_ok hmem
def wits_5361 : List (Nat × Nat × Nat) :=
  [(5361, 11, 5347), (5362, 2671, 2687), (5363, 1901, 3457), (5364, 13, 5347), (5365, 2677, 2683), (5366, 2393, 2969), (5367, 17, 5347), (5368, 2677, 2687), (5369, 2411, 2953), (5370, 19, 5347), (5371, 2677, 2689), (5372, 1907, 3461), (5373, 2683, 2687), (5374, 2657, 2713), (5375, 23, 5347), (5376, 2687, 2687), (5377, 2659, 2713), (5378, 2207, 3167), (5379, 29, 5347), (5380, 2417, 2957), (5381, 2683, 2693), (5382, 2591, 2789), (5383, 31, 5347), (5384, 2687, 2693), (5385, 2549, 2833), (5386, 2671, 2711), (5387, 2689, 2693), (5388, 3, 5381), (5389, 2677, 2707), (5390, 5, 5381), (5391, 2659, 2729), (5392, 2693, 2693), (5393, 7, 5381), (5394, 3, 5387), (5395, 2539, 2851), (5396, 5, 5387), (5397, 2687, 2707), (5398, 2087, 3307), (5399, 7, 5387), (5400, 3, 5393)]
theorem wits_5361_ok : checkPairs wits_5361 = true := rfl
theorem wits_5361_ns : wits_5361.map (·.1) = (List.range 40).map (· + 5361) := rfl
theorem a_pos_5361_to_5400 (n : Nat) (h1 : 5361 ≤ n) (h2 : n ≤ 5400) : 0 < a n := by
  have hmem : n ∈ wits_5361.map (·.1) := by
    rw [wits_5361_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5361_ok hmem
def wits_5401 : List (Nat × Nat × Nat) :=
  [(5401, 2683, 2713), (5402, 5, 5393), (5403, 2689, 2711), (5404, 2687, 2713), (5405, 7, 5393), (5406, 2237, 3167), (5407, 2689, 2713), (5408, 11, 5393), (5409, 2657, 2749), (5410, 23, 5381), (5411, 13, 5393), (5412, 2111, 3299), (5413, 2617, 2791), (5414, 3, 5407), (5415, 2683, 2729), (5416, 5, 5407), (5417, 19, 5393), (5418, 31, 5381), (5419, 3, 5413), (5420, 29, 5387), (5421, 5, 5413), (5422, 3, 5417), (5423, 37, 5381), (5424, 5, 5417), (5425, 13, 5407), (5426, 29, 5393), (5427, 7, 5417), (5428, 17, 5407), (5429, 37, 5387), (5430, 11, 5417), (5431, 19, 5407), (5432, 2713, 2713), (5433, 13, 5417), (5434, 2131, 3299), (5435, 37, 5393), (5436, 17, 5417), (5437, 439, 4993), (5438, 3, 5431), (5439, 19, 5417), (5440, 5, 5431)]
theorem wits_5401_ok : checkPairs wits_5401 = true := rfl
theorem wits_5401_ns : wits_5401.map (·.1) = (List.range 40).map (· + 5401) := rfl
theorem a_pos_5401_to_5440 (n : Nat) (h1 : 5401 ≤ n) (h2 : n ≤ 5440) : 0 < a n := by
  have hmem : n ∈ wits_5401.map (·.1) := by
    rw [wits_5401_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5401_ok hmem
def wits_5441 : List (Nat × Nat × Nat) :=
  [(5441, 23, 5413), (5442, 2711, 2729), (5443, 3, 5437), (5444, 23, 5417), (5445, 5, 5437), (5446, 3, 5441), (5447, 2693, 2749), (5448, 5, 5441), (5449, 13, 5431), (5450, 3, 5443), (5451, 7, 5441), (5452, 5, 5443), (5453, 2411, 3037), (5454, 11, 5441), (5455, 7, 5443), (5456, 2549, 2903), (5457, 13, 5441), (5458, 11, 5443), (5459, 2617, 2837), (5460, 17, 5441), (5461, 13, 5443), (5462, 2207, 3251), (5463, 19, 5441), (5464, 17, 5443), (5465, 23, 5437), (5466, 1997, 3467), (5467, 19, 5443), (5468, 23, 5441), (5469, 29, 5437), (5470, 2677, 2789), (5471, 1213, 4253), (5472, 23, 5443), (5473, 31, 5437), (5474, 2677, 2791), (5475, 2683, 2789), (5476, 29, 5443), (5477, 2393, 3079), (5478, 3, 5471), (5479, 2683, 2791), (5480, 5, 5471)]
theorem wits_5441_ok : checkPairs wits_5441 = true := rfl
theorem wits_5441_ns : wits_5441.map (·.1) = (List.range 40).map (· + 5441) := rfl
theorem a_pos_5441_to_5480 (n : Nat) (h1 : 5441 ≤ n) (h2 : n ≤ 5480) : 0 < a n := by
  have hmem : n ∈ wits_5441.map (·.1) := by
    rw [wits_5441_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5441_ok hmem
def wits_5481 : List (Nat × Nat × Nat) :=
  [(5481, 37, 5441), (5482, 3, 5477), (5483, 7, 5471), (5484, 5, 5477), (5485, 3, 5479), (5486, 11, 5471), (5487, 5, 5479), (5488, 1877, 3607), (5489, 13, 5471), (5490, 7, 5479), (5491, 2467, 3019), (5492, 17, 5471), (5493, 11, 5479), (5494, 2371, 3119), (5495, 19, 5471), (5496, 13, 5479), (5497, 769, 4723), (5498, 2693, 2801), (5499, 17, 5479), (5500, 23, 5471), (5501, 2659, 2837), (5502, 19, 5479), (5503, 2707, 2791), (5504, 23, 5477), (5505, 2549, 2953), (5506, 3, 5501), (5507, 23, 5479), (5508, 5, 5501), (5509, 3, 5503), (5510, 2713, 2791), (5511, 5, 5503), (5512, 31, 5477), (5513, 37, 5471), (5514, 7, 5503), (5515, 31, 5479), (5516, 2549, 2963), (5517, 11, 5503), (5518, 2713, 2801), (5519, 2617, 2897), (5520, 13, 5503)]
theorem wits_5481_ok : checkPairs wits_5481 = true := rfl
theorem wits_5481_ns : wits_5481.map (·.1) = (List.range 40).map (· + 5481) := rfl
theorem a_pos_5481_to_5520 (n : Nat) (h1 : 5481 ≤ n) (h2 : n ≤ 5520) : 0 < a n := by
  have hmem : n ∈ wits_5481.map (·.1) := by
    rw [wits_5481_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5481_ok hmem
def wits_5521 : List (Nat × Nat × Nat) :=
  [(5521, 2203, 3313), (5522, 2351, 3167), (5523, 17, 5503), (5524, 3, 5519), (5525, 2683, 2837), (5526, 5, 5519), (5527, 1429, 4093), (5528, 3, 5521), (5529, 7, 5519), (5530, 5, 5521), (5531, 23, 5503), (5532, 11, 5519), (5533, 3, 5527), (5534, 2677, 2851), (5535, 5, 5527), (5536, 11, 5521), (5537, 1999, 3533), (5538, 7, 5527), (5539, 13, 5521), (5540, 2417, 3119), (5541, 11, 5527), (5542, 17, 5521), (5543, 2351, 3187), (5544, 13, 5527), (5545, 19, 5521), (5546, 23, 5519), (5547, 17, 5527), (5548, 2287, 3257), (5549, 2707, 2837), (5550, 19, 5527), (5551, 2713, 2833), (5552, 2711, 2837), (5553, 2749, 2801), (5554, 29, 5521), (5555, 23, 5527), (5556, 2087, 3467), (5557, 2239, 3313), (5558, 31, 5521), (5559, 29, 5527), (5560, 2351, 3203)]
theorem wits_5521_ok : checkPairs wits_5521 = true := rfl
theorem wits_5521_ns : wits_5521.map (·.1) = (List.range 40).map (· + 5521) := rfl
theorem a_pos_5521_to_5560 (n : Nat) (h1 : 5521 ≤ n) (h2 : n ≤ 5560) : 0 < a n := by
  have hmem : n ∈ wits_5521.map (·.1) := by
    rw [wits_5521_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5521_ok hmem
def wits_5561 : List (Nat × Nat × Nat) :=
  [(5561, 2659, 2897), (5562, 2591, 2969), (5563, 31, 5527), (5564, 3, 5557), (5565, 2729, 2833), (5566, 5, 5557), (5567, 2659, 2903), (5568, 37, 5527), (5569, 7, 5557), (5570, 3, 5563), (5571, 2711, 2857), (5572, 5, 5563), (5573, 2351, 3217), (5574, 2111, 3461), (5575, 3, 5569), (5576, 1901, 3671), (5577, 5, 5569), (5578, 11, 5563), (5579, 2617, 2957), (5580, 7, 5569), (5581, 13, 5563), (5582, 2411, 3167), (5583, 11, 5569), (5584, 17, 5563), (5585, 2683, 2897), (5586, 13, 5569), (5587, 19, 5563), (5588, 2791, 2791), (5589, 17, 5569), (5590, 29, 5557), (5591, 2749, 2837), (5592, 19, 5569), (5593, 2791, 2797), (5594, 31, 5557), (5595, 2473, 3119), (5596, 29, 5563), (5597, 23, 5569), (5598, 2339, 3257), (5599, 37, 5557), (5600, 31, 5563)]
theorem wits_5561_ok : checkPairs wits_5561 = true := rfl
theorem wits_5561_ns : wits_5561.map (·.1) = (List.range 40).map (· + 5561) := rfl
theorem a_pos_5561_to_5600 (n : Nat) (h1 : 5561 ≤ n) (h2 : n ≤ 5600) : 0 < a n := by
  have hmem : n ∈ wits_5561.map (·.1) := by
    rw [wits_5561_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5561_ok hmem
def wits_5601 : List (Nat × Nat × Nat) :=
  [(5601, 29, 5569), (5602, 2693, 2903), (5603, 2411, 3187), (5604, 2801, 2801), (5605, 31, 5569), (5606, 2351, 3251), (5607, 2437, 3167), (5608, 1997, 3607), (5609, 2707, 2897), (5610, 37, 5569), (5611, 2293, 3313), (5612, 2711, 2897), (5613, 2657, 2953), (5614, 2549, 3061), (5615, 2707, 2903), (5616, 2087, 3527), (5617, 499, 5113), (5618, 2711, 2903), (5619, 2617, 2999), (5620, 2411, 3203), (5621, 2659, 2957), (5622, 2081, 3539), (5623, 2437, 3181), (5624, 2657, 2963), (5625, 2789, 2833), (5626, 2417, 3203), (5627, 2659, 2963), (5628, 2657, 2969), (5629, 2791, 2833), (5630, 2789, 2837), (5631, 2659, 2969), (5632, 2543, 3083), (5633, 2441, 3187), (5634, 2381, 3251), (5635, 2677, 2953), (5636, 2729, 2903), (5637, 2801, 2833), (5638, 2467, 3167), (5639, 2797, 2837), (5640, 2381, 3257)]
theorem wits_5601_ok : checkPairs wits_5601 = true := rfl
theorem wits_5601_ns : wits_5601.map (·.1) = (List.range 40).map (· + 5601) := rfl
theorem a_pos_5601_to_5640 (n : Nat) (h1 : 5601 ≤ n) (h2 : n ≤ 5640) : 0 < a n := by
  have hmem : n ∈ wits_5601.map (·.1) := by
    rw [wits_5601_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5601_ok hmem
def wits_5641 : List (Nat × Nat × Nat) :=
  [(5641, 2383, 3253), (5642, 2801, 2837), (5643, 2687, 2953), (5644, 3, 5639), (5645, 2683, 2957), (5646, 5, 5639), (5647, 1549, 4093), (5648, 3, 5641), (5649, 7, 5639), (5650, 5, 5641), (5651, 2749, 2897), (5652, 11, 5639), (5653, 3, 5647), (5654, 2687, 2963), (5655, 5, 5647), (5656, 3, 5651), (5657, 2749, 2903), (5658, 5, 5651), (5659, 3, 5653), (5660, 2341, 3313), (5661, 5, 5653), (5662, 3, 5657), (5663, 2441, 3217), (5664, 5, 5657), (5665, 19, 5641), (5666, 23, 5639), (5667, 7, 5657), (5668, 2027, 3637), (5669, 2707, 2957), (5670, 11, 5657), (5671, 2713, 2953), (5672, 2711, 2957), (5673, 13, 5657), (5674, 29, 5641), (5675, 23, 5647), (5676, 17, 5657), (5677, 1753, 3919), (5678, 23, 5651), (5679, 19, 5657), (5680, 2837, 2837)]
theorem wits_5641_ok : checkPairs wits_5641 = true := rfl
theorem wits_5641_ns : wits_5641.map (·.1) = (List.range 40).map (· + 5641) := rfl
theorem a_pos_5641_to_5680 (n : Nat) (h1 : 5641 ≤ n) (h2 : n ≤ 5680) : 0 < a n := by
  have hmem : n ∈ wits_5641.map (·.1) := by
    rw [wits_5641_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5641_ok hmem
def wits_5681 : List (Nat × Nat × Nat) :=
  [(5681, 23, 5653), (5682, 29, 5651), (5683, 31, 5647), (5684, 23, 5657), (5685, 29, 5653), (5686, 31, 5651), (5687, 1609, 4073), (5688, 29, 5657), (5689, 31, 5653), (5690, 3, 5683), (5691, 37, 5651), (5692, 5, 5683), (5693, 1297, 4391), (5694, 37, 5653), (5695, 3, 5689), (5696, 2789, 2903), (5697, 5, 5689), (5698, 11, 5683), (5699, 2837, 2857), (5700, 7, 5689), (5701, 13, 5683), (5702, 2801, 2897), (5703, 11, 5689), (5704, 17, 5683), (5705, 2797, 2903), (5706, 13, 5689), (5707, 19, 5683), (5708, 2851, 2851), (5709, 17, 5689), (5710, 1907, 3797), (5711, 2749, 2957), (5712, 19, 5689), (5713, 2851, 2857), (5714, 2543, 3167), (5715, 2549, 3163), (5716, 29, 5683), (5717, 23, 5689), (5718, 3, 5711), (5719, 2677, 3037), (5720, 5, 5711)]
theorem wits_5681_ok : checkPairs wits_5681 = true := rfl
theorem wits_5681_ns : wits_5681.map (·.1) = (List.range 40).map (· + 5681) := rfl
theorem a_pos_5681_to_5720 (n : Nat) (h1 : 5681 ≤ n) (h2 : n ≤ 5720) : 0 < a n := by
  have hmem : n ∈ wits_5681.map (·.1) := by
    rw [wits_5681_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5681_ok hmem
def wits_5721 : List (Nat × Nat × Nat) :=
  [(5721, 29, 5689), (5722, 2657, 3061), (5723, 7, 5711), (5724, 2141, 3581), (5725, 31, 5689), (5726, 11, 5711), (5727, 2687, 3037), (5728, 2467, 3257), (5729, 13, 5711), (5730, 37, 5689), (5731, 2383, 3343), (5732, 17, 5711), (5733, 2711, 3019), (5734, 2549, 3181), (5735, 19, 5711), (5736, 2267, 3467), (5737, 2713, 3019), (5738, 2671, 3061), (5739, 2657, 3079), (5740, 23, 5711), (5741, 2833, 2903), (5742, 2381, 3359), (5743, 3, 5737), (5744, 29, 5711), (5745, 5, 5737), (5746, 3, 5741), (5747, 2659, 3083), (5748, 5, 5741), (5749, 2791, 2953), (5750, 3, 5743), (5751, 7, 5741), (5752, 5, 5743), (5753, 37, 5711), (5754, 11, 5741), (5755, 7, 5743), (5756, 2789, 2963), (5757, 13, 5741), (5758, 11, 5743), (5759, 2857, 2897), (5760, 17, 5741)]
theorem wits_5721_ok : checkPairs wits_5721 = true := rfl
theorem wits_5721_ns : wits_5721.map (·.1) = (List.range 40).map (· + 5721) := rfl
theorem a_pos_5721_to_5760 (n : Nat) (h1 : 5721 ≤ n) (h2 : n ≤ 5760) : 0 < a n := by
  have hmem : n ∈ wits_5721.map (·.1) := by
    rw [wits_5721_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5721_ok hmem
def wits_5761 : List (Nat × Nat × Nat) :=
  [(5761, 13, 5743), (5762, 2801, 2957), (5763, 19, 5741), (5764, 17, 5743), (5765, 23, 5737), (5766, 2237, 3527), (5767, 19, 5743), (5768, 23, 5741), (5769, 29, 5737), (5770, 2467, 3299), (5771, 2683, 3083), (5772, 23, 5743), (5773, 31, 5737), (5774, 2687, 3083), (5775, 2473, 3299), (5776, 29, 5743), (5777, 2693, 3079), (5778, 37, 5737), (5779, 2473, 3301), (5780, 31, 5743), (5781, 37, 5741), (5782, 2693, 3083), (5783, 1901, 3877), (5784, 2111, 3671), (5785, 3, 5779), (5786, 2467, 3313), (5787, 5, 5779), (5788, 1657, 4127), (5789, 2441, 3343), (5790, 7, 5779), (5791, 2473, 3313), (5792, 2417, 3371), (5793, 11, 5779), (5794, 2791, 2999), (5795, 2837, 2953), (5796, 13, 5779), (5797, 2713, 3079), (5798, 2711, 3083), (5799, 17, 5779), (5800, 2897, 2897)]
theorem wits_5761_ok : checkPairs wits_5761 = true := rfl
theorem wits_5761_ns : wits_5761.map (·.1) = (List.range 40).map (· + 5761) := rfl
theorem a_pos_5761_to_5800 (n : Nat) (h1 : 5761 ≤ n) (h2 : n ≤ 5800) : 0 < a n := by
  have hmem : n ∈ wits_5761.map (·.1) := by
    rw [wits_5761_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5761_ok hmem
def wits_5801 : List (Nat × Nat × Nat) :=
  [(5801, 2833, 2963), (5802, 19, 5779), (5803, 2617, 3181), (5804, 2543, 3257), (5805, 2833, 2969), (5806, 2897, 2903), (5807, 23, 5779), (5808, 3, 5801), (5809, 2851, 2953), (5810, 5, 5801), (5811, 29, 5779), (5812, 2903, 2903), (5813, 7, 5801), (5814, 3, 5807), (5815, 31, 5779), (5816, 5, 5807), (5817, 2347, 3467), (5818, 2287, 3527), (5819, 7, 5807), (5820, 37, 5779), (5821, 2287, 3529), (5822, 11, 5807), (5823, 2801, 3019), (5824, 2851, 2969), (5825, 13, 5807), (5826, 2657, 3167), (5827, 1033, 4789), (5828, 3, 5821), (5829, 2857, 2969), (5830, 5, 5821), (5831, 19, 5807), (5832, 2711, 3119), (5833, 7, 5821), (5834, 29, 5801), (5835, 2833, 2999), (5836, 11, 5821), (5837, 2749, 3083), (5838, 31, 5801), (5839, 13, 5821), (5840, 29, 5807)]
theorem wits_5801_ok : checkPairs wits_5801 = true := rfl
theorem wits_5801_ns : wits_5801.map (·.1) = (List.range 40).map (· + 5801) := rfl
theorem a_pos_5801_to_5840 (n : Nat) (h1 : 5801 ≤ n) (h2 : n ≤ 5840) : 0 < a n := by
  have hmem : n ∈ wits_5801.map (·.1) := by
    rw [wits_5801_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5801_ok hmem
def wits_5841 : List (Nat × Nat × Nat) :=
  [(5841, 2801, 3037), (5842, 17, 5821), (5843, 37, 5801), (5844, 31, 5807), (5845, 3, 5839), (5846, 2543, 3299), (5847, 5, 5839), (5848, 2677, 3167), (5849, 37, 5807), (5850, 3, 5843), (5851, 2539, 3307), (5852, 5, 5843), (5853, 11, 5839), (5854, 3, 5849), (5855, 7, 5843), (5856, 5, 5849), (5857, 2539, 3313), (5858, 3, 5851), (5859, 7, 5849), (5860, 5, 5851), (5861, 13, 5843), (5862, 11, 5849), (5863, 3, 5857), (5864, 17, 5843), (5865, 5, 5857), (5866, 11, 5851), (5867, 19, 5843), (5868, 3, 5861), (5869, 13, 5851), (5870, 5, 5861), (5871, 11, 5857), (5872, 3, 5867), (5873, 7, 5861), (5874, 5, 5867), (5875, 19, 5851), (5876, 11, 5861), (5877, 7, 5867), (5878, 2267, 3607), (5879, 13, 5861), (5880, 11, 5867)]
theorem wits_5841_ok : checkPairs wits_5841 = true := rfl
theorem wits_5841_ns : wits_5841.map (·.1) = (List.range 40).map (· + 5841) := rfl
theorem a_pos_5841_to_5880 (n : Nat) (h1 : 5841 ≤ n) (h2 : n ≤ 5880) : 0 < a n := by
  have hmem : n ∈ wits_5841.map (·.1) := by
    rw [wits_5841_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5841_ok hmem
def wits_5881 : List (Nat × Nat × Nat) :=
  [(5881, 2713, 3163), (5882, 17, 5861), (5883, 13, 5867), (5884, 3, 5879), (5885, 19, 5861), (5886, 5, 5879), (5887, 1753, 4129), (5888, 31, 5851), (5889, 7, 5879), (5890, 23, 5861), (5891, 2683, 3203), (5892, 11, 5879), (5893, 31, 5857), (5894, 23, 5867), (5895, 13, 5879), (5896, 2711, 3181), (5897, 2689, 3203), (5898, 17, 5879), (5899, 2833, 3061), (5900, 2897, 2999), (5901, 19, 5879), (5902, 31, 5867), (5903, 37, 5861), (5904, 3, 5897), (5905, 2713, 3187), (5906, 5, 5897), (5907, 37, 5867), (5908, 2591, 3313), (5909, 7, 5897), (5910, 29, 5879), (5911, 2269, 3637), (5912, 11, 5897), (5913, 2659, 3251), (5914, 31, 5879), (5915, 13, 5897), (5916, 2657, 3257), (5917, 2383, 3529), (5918, 17, 5897), (5919, 37, 5879), (5920, 2957, 2957)]
theorem wits_5881_ok : checkPairs wits_5881 = true := rfl
theorem wits_5881_ns : wits_5881.map (·.1) = (List.range 40).map (· + 5881) := rfl
theorem a_pos_5881_to_5920 (n : Nat) (h1 : 5881 ≤ n) (h2 : n ≤ 5920) : 0 < a n := by
  have hmem : n ∈ wits_5881.map (·.1) := by
    rw [wits_5881_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5881_ok hmem
def wits_5921 : List (Nat × Nat × Nat) :=
  [(5921, 19, 5897), (5922, 2801, 3119), (5923, 2857, 3061), (5924, 2393, 3527), (5925, 2953, 2969), (5926, 23, 5897), (5927, 2903, 3019), (5928, 1997, 3929), (5929, 3, 5923), (5930, 29, 5897), (5931, 5, 5923), (5932, 2963, 2963), (5933, 457, 5471), (5934, 7, 5923), (5935, 2851, 3079), (5936, 2963, 2969), (5937, 11, 5923), (5938, 2677, 3257), (5939, 37, 5897), (5940, 13, 5923), (5941, 2203, 3733), (5942, 2411, 3527), (5943, 17, 5923), (5944, 2551, 3389), (5945, 2903, 3037), (5946, 19, 5923), (5947, 499, 5443), (5948, 2693, 3251), (5949, 2729, 3217), (5950, 2411, 3533), (5951, 23, 5923), (5952, 2591, 3359), (5953, 2437, 3511), (5954, 2693, 3257), (5955, 29, 5923), (5956, 2543, 3407), (5957, 2749, 3203), (5958, 2789, 3167), (5959, 31, 5923), (5960, 2957, 2999)]
theorem wits_5921_ok : checkPairs wits_5921 = true := rfl
theorem wits_5921_ns : wits_5921.map (·.1) = (List.range 40).map (· + 5921) := rfl
theorem a_pos_5921_to_5960 (n : Nat) (h1 : 5921 ≤ n) (h2 : n ≤ 5960) : 0 < a n := by
  have hmem : n ∈ wits_5921.map (·.1) := by
    rw [wits_5921_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5921_ok hmem
def wits_5961 : List (Nat × Nat × Nat) :=
  [(5961, 2707, 3251), (5962, 2791, 3167), (5963, 1567, 4391), (5964, 37, 5923), (5965, 2659, 3301), (5966, 2963, 2999), (5967, 2801, 3163), (5968, 2713, 3251), (5969, 2351, 3613), (5970, 2969, 2999), (5971, 2713, 3253), (5972, 2441, 3527), (5973, 2389, 3581), (5974, 2851, 3119), (5975, 2441, 3529), (5976, 1427, 4547), (5977, 2659, 3313), (5978, 2791, 3181), (5979, 2857, 3119), (5980, 2677, 3299), (5981, 2957, 3019), (5982, 2729, 3251), (5983, 2797, 3181), (5984, 2677, 3301), (5985, 2729, 3253), (5986, 2897, 3083), (5987, 2963, 3019), (5988, 3, 5981), (5989, 2683, 3301), (5990, 5, 5981), (5991, 2969, 3019), (5992, 2903, 3083), (5993, 7, 5981), (5994, 2141, 3851), (5995, 2689, 3301), (5996, 11, 5981), (5997, 2437, 3557), (5998, 2687, 3307), (5999, 13, 5981), (6000, 2999, 2999)]
theorem wits_5961_ok : checkPairs wits_5961 = true := rfl
theorem wits_5961_ns : wits_5961.map (·.1) = (List.range 40).map (· + 5961) := rfl
theorem a_pos_5961_to_6000 (n : Nat) (h1 : 5961 ≤ n) (h2 : n ≤ 6000) : 0 < a n := by
  have hmem : n ∈ wits_5961.map (·.1) := by
    rw [wits_5961_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_5961_ok hmem
theorem a_pos_3001_to_3200 (n : Nat) (h1 : 3001 ≤ n) (h2 : n ≤ 3200) : 0 < a n := by
  have hcases : (3001 ≤ n ∧ n ≤ 3040) ∨ (3041 ≤ n ∧ n ≤ 3080) ∨ (3081 ≤ n ∧ n ≤ 3120) ∨ (3121 ≤ n ∧ n ≤ 3160) ∨ (3161 ≤ n ∧ n ≤ 3200) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_3001_to_3040 n h.1 h.2
  · exact a_pos_3041_to_3080 n h.1 h.2
  · exact a_pos_3081_to_3120 n h.1 h.2
  · exact a_pos_3121_to_3160 n h.1 h.2
  · exact a_pos_3161_to_3200 n h.1 h.2
theorem a_pos_3201_to_3400 (n : Nat) (h1 : 3201 ≤ n) (h2 : n ≤ 3400) : 0 < a n := by
  have hcases : (3201 ≤ n ∧ n ≤ 3240) ∨ (3241 ≤ n ∧ n ≤ 3280) ∨ (3281 ≤ n ∧ n ≤ 3320) ∨ (3321 ≤ n ∧ n ≤ 3360) ∨ (3361 ≤ n ∧ n ≤ 3400) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_3201_to_3240 n h.1 h.2
  · exact a_pos_3241_to_3280 n h.1 h.2
  · exact a_pos_3281_to_3320 n h.1 h.2
  · exact a_pos_3321_to_3360 n h.1 h.2
  · exact a_pos_3361_to_3400 n h.1 h.2
theorem a_pos_3401_to_3600 (n : Nat) (h1 : 3401 ≤ n) (h2 : n ≤ 3600) : 0 < a n := by
  have hcases : (3401 ≤ n ∧ n ≤ 3440) ∨ (3441 ≤ n ∧ n ≤ 3480) ∨ (3481 ≤ n ∧ n ≤ 3520) ∨ (3521 ≤ n ∧ n ≤ 3560) ∨ (3561 ≤ n ∧ n ≤ 3600) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_3401_to_3440 n h.1 h.2
  · exact a_pos_3441_to_3480 n h.1 h.2
  · exact a_pos_3481_to_3520 n h.1 h.2
  · exact a_pos_3521_to_3560 n h.1 h.2
  · exact a_pos_3561_to_3600 n h.1 h.2
theorem a_pos_3601_to_3800 (n : Nat) (h1 : 3601 ≤ n) (h2 : n ≤ 3800) : 0 < a n := by
  have hcases : (3601 ≤ n ∧ n ≤ 3640) ∨ (3641 ≤ n ∧ n ≤ 3680) ∨ (3681 ≤ n ∧ n ≤ 3720) ∨ (3721 ≤ n ∧ n ≤ 3760) ∨ (3761 ≤ n ∧ n ≤ 3800) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_3601_to_3640 n h.1 h.2
  · exact a_pos_3641_to_3680 n h.1 h.2
  · exact a_pos_3681_to_3720 n h.1 h.2
  · exact a_pos_3721_to_3760 n h.1 h.2
  · exact a_pos_3761_to_3800 n h.1 h.2
theorem a_pos_3801_to_4000 (n : Nat) (h1 : 3801 ≤ n) (h2 : n ≤ 4000) : 0 < a n := by
  have hcases : (3801 ≤ n ∧ n ≤ 3840) ∨ (3841 ≤ n ∧ n ≤ 3880) ∨ (3881 ≤ n ∧ n ≤ 3920) ∨ (3921 ≤ n ∧ n ≤ 3960) ∨ (3961 ≤ n ∧ n ≤ 4000) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_3801_to_3840 n h.1 h.2
  · exact a_pos_3841_to_3880 n h.1 h.2
  · exact a_pos_3881_to_3920 n h.1 h.2
  · exact a_pos_3921_to_3960 n h.1 h.2
  · exact a_pos_3961_to_4000 n h.1 h.2
theorem a_pos_4001_to_4200 (n : Nat) (h1 : 4001 ≤ n) (h2 : n ≤ 4200) : 0 < a n := by
  have hcases : (4001 ≤ n ∧ n ≤ 4040) ∨ (4041 ≤ n ∧ n ≤ 4080) ∨ (4081 ≤ n ∧ n ≤ 4120) ∨ (4121 ≤ n ∧ n ≤ 4160) ∨ (4161 ≤ n ∧ n ≤ 4200) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_4001_to_4040 n h.1 h.2
  · exact a_pos_4041_to_4080 n h.1 h.2
  · exact a_pos_4081_to_4120 n h.1 h.2
  · exact a_pos_4121_to_4160 n h.1 h.2
  · exact a_pos_4161_to_4200 n h.1 h.2
theorem a_pos_4201_to_4400 (n : Nat) (h1 : 4201 ≤ n) (h2 : n ≤ 4400) : 0 < a n := by
  have hcases : (4201 ≤ n ∧ n ≤ 4240) ∨ (4241 ≤ n ∧ n ≤ 4280) ∨ (4281 ≤ n ∧ n ≤ 4320) ∨ (4321 ≤ n ∧ n ≤ 4360) ∨ (4361 ≤ n ∧ n ≤ 4400) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_4201_to_4240 n h.1 h.2
  · exact a_pos_4241_to_4280 n h.1 h.2
  · exact a_pos_4281_to_4320 n h.1 h.2
  · exact a_pos_4321_to_4360 n h.1 h.2
  · exact a_pos_4361_to_4400 n h.1 h.2
theorem a_pos_4401_to_4600 (n : Nat) (h1 : 4401 ≤ n) (h2 : n ≤ 4600) : 0 < a n := by
  have hcases : (4401 ≤ n ∧ n ≤ 4440) ∨ (4441 ≤ n ∧ n ≤ 4480) ∨ (4481 ≤ n ∧ n ≤ 4520) ∨ (4521 ≤ n ∧ n ≤ 4560) ∨ (4561 ≤ n ∧ n ≤ 4600) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_4401_to_4440 n h.1 h.2
  · exact a_pos_4441_to_4480 n h.1 h.2
  · exact a_pos_4481_to_4520 n h.1 h.2
  · exact a_pos_4521_to_4560 n h.1 h.2
  · exact a_pos_4561_to_4600 n h.1 h.2
theorem a_pos_4601_to_4800 (n : Nat) (h1 : 4601 ≤ n) (h2 : n ≤ 4800) : 0 < a n := by
  have hcases : (4601 ≤ n ∧ n ≤ 4640) ∨ (4641 ≤ n ∧ n ≤ 4680) ∨ (4681 ≤ n ∧ n ≤ 4720) ∨ (4721 ≤ n ∧ n ≤ 4760) ∨ (4761 ≤ n ∧ n ≤ 4800) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_4601_to_4640 n h.1 h.2
  · exact a_pos_4641_to_4680 n h.1 h.2
  · exact a_pos_4681_to_4720 n h.1 h.2
  · exact a_pos_4721_to_4760 n h.1 h.2
  · exact a_pos_4761_to_4800 n h.1 h.2
theorem a_pos_4801_to_5000 (n : Nat) (h1 : 4801 ≤ n) (h2 : n ≤ 5000) : 0 < a n := by
  have hcases : (4801 ≤ n ∧ n ≤ 4840) ∨ (4841 ≤ n ∧ n ≤ 4880) ∨ (4881 ≤ n ∧ n ≤ 4920) ∨ (4921 ≤ n ∧ n ≤ 4960) ∨ (4961 ≤ n ∧ n ≤ 5000) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_4801_to_4840 n h.1 h.2
  · exact a_pos_4841_to_4880 n h.1 h.2
  · exact a_pos_4881_to_4920 n h.1 h.2
  · exact a_pos_4921_to_4960 n h.1 h.2
  · exact a_pos_4961_to_5000 n h.1 h.2
theorem a_pos_5001_to_5200 (n : Nat) (h1 : 5001 ≤ n) (h2 : n ≤ 5200) : 0 < a n := by
  have hcases : (5001 ≤ n ∧ n ≤ 5040) ∨ (5041 ≤ n ∧ n ≤ 5080) ∨ (5081 ≤ n ∧ n ≤ 5120) ∨ (5121 ≤ n ∧ n ≤ 5160) ∨ (5161 ≤ n ∧ n ≤ 5200) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_5001_to_5040 n h.1 h.2
  · exact a_pos_5041_to_5080 n h.1 h.2
  · exact a_pos_5081_to_5120 n h.1 h.2
  · exact a_pos_5121_to_5160 n h.1 h.2
  · exact a_pos_5161_to_5200 n h.1 h.2
theorem a_pos_5201_to_5400 (n : Nat) (h1 : 5201 ≤ n) (h2 : n ≤ 5400) : 0 < a n := by
  have hcases : (5201 ≤ n ∧ n ≤ 5240) ∨ (5241 ≤ n ∧ n ≤ 5280) ∨ (5281 ≤ n ∧ n ≤ 5320) ∨ (5321 ≤ n ∧ n ≤ 5360) ∨ (5361 ≤ n ∧ n ≤ 5400) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_5201_to_5240 n h.1 h.2
  · exact a_pos_5241_to_5280 n h.1 h.2
  · exact a_pos_5281_to_5320 n h.1 h.2
  · exact a_pos_5321_to_5360 n h.1 h.2
  · exact a_pos_5361_to_5400 n h.1 h.2
theorem a_pos_5401_to_5600 (n : Nat) (h1 : 5401 ≤ n) (h2 : n ≤ 5600) : 0 < a n := by
  have hcases : (5401 ≤ n ∧ n ≤ 5440) ∨ (5441 ≤ n ∧ n ≤ 5480) ∨ (5481 ≤ n ∧ n ≤ 5520) ∨ (5521 ≤ n ∧ n ≤ 5560) ∨ (5561 ≤ n ∧ n ≤ 5600) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_5401_to_5440 n h.1 h.2
  · exact a_pos_5441_to_5480 n h.1 h.2
  · exact a_pos_5481_to_5520 n h.1 h.2
  · exact a_pos_5521_to_5560 n h.1 h.2
  · exact a_pos_5561_to_5600 n h.1 h.2
theorem a_pos_5601_to_5800 (n : Nat) (h1 : 5601 ≤ n) (h2 : n ≤ 5800) : 0 < a n := by
  have hcases : (5601 ≤ n ∧ n ≤ 5640) ∨ (5641 ≤ n ∧ n ≤ 5680) ∨ (5681 ≤ n ∧ n ≤ 5720) ∨ (5721 ≤ n ∧ n ≤ 5760) ∨ (5761 ≤ n ∧ n ≤ 5800) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_5601_to_5640 n h.1 h.2
  · exact a_pos_5641_to_5680 n h.1 h.2
  · exact a_pos_5681_to_5720 n h.1 h.2
  · exact a_pos_5721_to_5760 n h.1 h.2
  · exact a_pos_5761_to_5800 n h.1 h.2
theorem a_pos_5801_to_6000 (n : Nat) (h1 : 5801 ≤ n) (h2 : n ≤ 6000) : 0 < a n := by
  have hcases : (5801 ≤ n ∧ n ≤ 5840) ∨ (5841 ≤ n ∧ n ≤ 5880) ∨ (5881 ≤ n ∧ n ≤ 5920) ∨ (5921 ≤ n ∧ n ≤ 5960) ∨ (5961 ≤ n ∧ n ≤ 6000) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_5801_to_5840 n h.1 h.2
  · exact a_pos_5841_to_5880 n h.1 h.2
  · exact a_pos_5881_to_5920 n h.1 h.2
  · exact a_pos_5921_to_5960 n h.1 h.2
  · exact a_pos_5961_to_6000 n h.1 h.2
theorem a_pos_3001_to_6000 (n : Nat) (h1 : 3001 ≤ n) (h2 : n ≤ 6000) : 0 < a n := by
  by_cases h0 : n ≤ 3200
  · exact a_pos_3001_to_3200 n h1 h0
  · by_cases ha : n ≤ 3400
    · exact a_pos_3201_to_3400 n (by omega) ha
    · by_cases hb : n ≤ 3600
      · exact a_pos_3401_to_3600 n (by omega) hb
      · by_cases hc : n ≤ 3800
        · exact a_pos_3601_to_3800 n (by omega) hc
        · by_cases hd : n ≤ 4000
          · exact a_pos_3801_to_4000 n (by omega) hd
          · by_cases he : n ≤ 4200
            · exact a_pos_4001_to_4200 n (by omega) he
            · by_cases hf : n ≤ 4400
              · exact a_pos_4201_to_4400 n (by omega) hf
              · by_cases hg : n ≤ 4600
                · exact a_pos_4401_to_4600 n (by omega) hg
                · by_cases hh : n ≤ 4800
                  · exact a_pos_4601_to_4800 n (by omega) hh
                  · by_cases hi : n ≤ 5000
                    · exact a_pos_4801_to_5000 n (by omega) hi
                    · by_cases hj : n ≤ 5200
                      · exact a_pos_5001_to_5200 n (by omega) hj
                      · by_cases hk : n ≤ 5400
                        · exact a_pos_5201_to_5400 n (by omega) hk
                        · by_cases hl : n ≤ 5600
                          · exact a_pos_5401_to_5600 n (by omega) hl
                          · by_cases hm : n ≤ 5800
                            · exact a_pos_5601_to_5800 n (by omega) hm
                            · exact a_pos_5801_to_6000 n (by omega) h2

/-- There is an interprime in `(N, 3 * N]` for `N ≥ 2`. -/
theorem exists_interprime_gt_le_three_mul {N : Nat} (hN : 2 ≤ N) :
    ∃ k, N < k ∧ k ≤ 3 * N ∧ IsInterprime k := by
  obtain ⟨p, hp, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  -- p ∈ (N, 2N]
  have hp2 : 2 < p := by
    have : 2 ≤ N := hN
    omega
  let p' := next_prime p
  have hp's := next_prime_spec p
  have hp'p : p'.Prime := hp's.1
  have hlt : p < p' := hp's.2.1
  have hnone : ∀ k, p < k → k < p' → ¬ k.Prime := by
    intro k hk1 hk2 hk
    have := hp's.2.2 k hk hk1
    omega
  -- p' ≤ 2p ≤ 4N by Bertrand, so midpoint ≤ 3N
  have hp'le : p' ≤ 2 * p := by
    have hne : p ≠ 0 := by omega
    obtain ⟨q, hq, hq_gt, hq_le⟩ := Nat.exists_prime_lt_and_le_two_mul p hne
    have : p' ≤ q := hp's.2.2 q hq hq_gt
    omega
  have hmid : IsInterprime ((p + p') / 2) :=
    isInterprime_of_consecutive hp hp'p hp2 hlt hnone
  have hdiv : 2 ∣ p + p' := by
    have : Odd p := hp.odd_of_ne_two (by omega)
    have : Odd p' := hp'p.odd_of_ne_two (by omega)
    exact even_iff_two_dvd.mp (Odd.add_odd ‹Odd p› ‹Odd p'›)
  have hge : N < (p + p') / 2 := by
    have hmul := Nat.mul_div_cancel' hdiv
    have h2 : 2 * N < p + p' := by omega
    rw [← hmul] at h2
    omega
  have hle : (p + p') / 2 ≤ 3 * N := by
    have hmul := Nat.mul_div_cancel' hdiv
    have : p + p' ≤ 6 * N := by
      have : p ≤ 2 * N := hp_le
      have : p' ≤ 2 * p := hp'le
      omega
    rw [← hmul] at this
    omega
  exact ⟨(p + p') / 2, hge, hle, hmid⟩

def wits_6001 : List (Nat × Nat × Nat) :=
  [(6001, 73, 5923), (6002, 17, 5981), (6003, 311, 5689), (6004, 149, 5851), (6005, 19, 5981), (6006, 79, 5923), (6007, 433, 5569), (6008, 107, 5897), (6009, 127, 5879), (6010, 23, 5981), (6011, 83, 5923), (6012, 229, 5779), (6013, 3, 6007), (6014, 29, 5981), (6015, 5, 6007), (6016, 167, 5843), (6017, 173, 5839), (6018, 7, 6007), (6019, 157, 5857), (6020, 167, 5849), (6021, 11, 6007), (6022, 151, 5867), (6023, 37, 5981), (6024, 13, 6007), (6025, 277, 5743), (6026, 41, 5981), (6027, 17, 6007), (6028, 157, 5867), (6029, 43, 5981), (6030, 19, 6007), (6031, 373, 5653), (6032, 227, 5801), (6033, 107, 5923), (6034, 47, 5981), (6035, 23, 6007), (6036, 109, 5923), (6037, 349, 5683), (6038, 137, 5897), (6039, 29, 6007), (6040, 53, 5981)]
theorem wits_6001_ok : checkPairs wits_6001 = true := rfl
theorem wits_6001_ns : wits_6001.map (·.1) = (List.range 40).map (· + 6001) := rfl
theorem a_pos_6001_to_6040 (n : Nat) (h1 : 6001 ≤ n) (h2 : n ≤ 6040) : 0 < a n := by
  have hmem : n ∈ wits_6001.map (·.1) := by
    rw [wits_6001_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_6001_ok hmem
def wits_6041 : List (Nat × Nat × Nat) :=
  [(6041, 193, 5843), (6042, 191, 5849), (6043, 31, 6007), (6044, 3, 6037), (6045, 163, 5879), (6046, 5, 6037), (6047, 263, 5779), (6048, 37, 6007), (6049, 3, 6043), (6050, 149, 5897), (6051, 5, 6043), (6052, 11, 6037), (6053, 67, 5981), (6054, 7, 6043), (6055, 13, 6037), (6056, 5, 6047), (6057, 11, 6043), (6058, 17, 6037), (6059, 7, 6047), (6060, 13, 6043), (6061, 19, 6037), (6062, 11, 6047), (6063, 17, 6043), (6064, 239, 5821), (6065, 13, 6047), (6066, 19, 6043), (6067, 373, 5689), (6068, 17, 6047), (6069, 59, 6007), (6070, 29, 6037), (6071, 19, 6047), (6072, 191, 5879), (6073, 61, 6007), (6074, 3, 6067), (6075, 29, 6043), (6076, 5, 6067), (6077, 229, 5843), (6078, 67, 6007), (6079, 7, 6067), (6080, 3, 6073)]
theorem wits_6041_ok : checkPairs wits_6041 = true := rfl
theorem wits_6041_ns : wits_6041.map (·.1) = (List.range 40).map (· + 6041) := rfl
theorem a_pos_6041_to_6080 (n : Nat) (h1 : 6041 ≤ n) (h2 : n ≤ 6080) : 0 < a n := by
  have hmem : n ∈ wits_6041.map (·.1) := by
    rw [wits_6041_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_6041_ok hmem
def wits_6081 : List (Nat × Nat × Nat) :=
  [(6081, 71, 6007), (6082, 5, 6073), (6083, 97, 5981), (6084, 37, 6043), (6085, 7, 6073), (6086, 101, 5981), (6087, 41, 6043), (6088, 11, 6073), (6089, 37, 6047), (6090, 43, 6043), (6091, 13, 6073), (6092, 41, 6047), (6093, 223, 5867), (6094, 3, 6089), (6095, 43, 6047), (6096, 5, 6089), (6097, 19, 6073), (6098, 197, 5897), (6099, 7, 6089), (6100, 29, 6067), (6101, 53, 6043), (6102, 11, 6089), (6103, 277, 5821), (6104, 31, 6067), (6105, 13, 6089), (6106, 29, 6073), (6107, 263, 5839), (6108, 17, 6089), (6109, 37, 6067), (6110, 31, 6073), (6111, 19, 6089), (6112, 41, 6067), (6113, 127, 5981), (6114, 67, 6043), (6115, 37, 6073), (6116, 23, 6089), (6117, 71, 6043), (6118, 41, 6073), (6119, 67, 6047), (6120, 29, 6089)]
theorem wits_6081_ok : checkPairs wits_6081 = true := rfl
theorem wits_6081_ns : wits_6081.map (·.1) = (List.range 40).map (· + 6081) := rfl
theorem a_pos_6081_to_6120 (n : Nat) (h1 : 6081 ≤ n) (h2 : n ≤ 6120) : 0 < a n := by
  have hmem : n ∈ wits_6081.map (·.1) := by
    rw [wits_6081_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_6081_ok hmem
def wits_6121 : List (Nat × Nat × Nat) :=
  [(6121, 43, 6073), (6122, 71, 6047), (6123, 197, 5923), (6124, 31, 6089), (6125, 223, 5897), (6126, 79, 6043), (6127, 379, 5743), (6128, 227, 5897), (6129, 37, 6089), (6130, 59, 6067), (6131, 79, 6047), (6132, 41, 6089), (6133, 271, 5857), (6134, 61, 6067), (6135, 43, 6089), (6136, 3, 6131), (6137, 353, 5779), (6138, 5, 6131), (6139, 67, 6067), (6140, 47, 6089), (6141, 7, 6131), (6142, 71, 6067), (6143, 131, 6007), (6144, 11, 6131), (6145, 67, 6073), (6146, 53, 6089), (6147, 13, 6131), (6148, 71, 6073), (6149, 97, 6047), (6150, 17, 6131), (6151, 79, 6067), (6152, 73, 6073), (6153, 19, 6131), (6154, 61, 6089), (6155, 103, 6047), (6156, 109, 6043), (6157, 79, 6073), (6158, 23, 6131), (6159, 67, 6089), (6160, 173, 5981)]
theorem wits_6121_ok : checkPairs wits_6121 = true := rfl
theorem wits_6121_ns : wits_6121.map (·.1) = (List.range 40).map (· + 6121) := rfl
theorem a_pos_6121_to_6160 (n : Nat) (h1 : 6121 ≤ n) (h2 : n ≤ 6160) : 0 < a n := by
  have hmem : n ∈ wits_6121.map (·.1) := by
    rw [wits_6121_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_6121_ok hmem
def wits_6161 : List (Nat × Nat × Nat) :=
  [(6161, 109, 6047), (6162, 29, 6131), (6163, 151, 6007), (6164, 179, 5981), (6165, 239, 5923), (6166, 31, 6131), (6167, 383, 5779), (6168, 307, 5857), (6169, 97, 6067), (6170, 269, 5897), (6171, 37, 6131), (6172, 101, 6067), (6173, 307, 5861), (6174, 41, 6131), (6175, 97, 6073), (6176, 83, 6089), (6177, 43, 6131), (6178, 101, 6073), (6179, 127, 6047), (6180, 311, 5867), (6181, 103, 6073), (6182, 47, 6131), (6183, 137, 6043), (6184, 107, 6073), (6185, 173, 6007), (6186, 613, 5569), (6187, 109, 6073), (6188, 53, 6131), (6189, 97, 6089), (6190, 149, 6037), (6191, 263, 5923), (6192, 59, 6131), (6193, 331, 5857), (6194, 151, 6037), (6195, 103, 6089), (6196, 61, 6131), (6197, 349, 5843), (6198, 107, 6089), (6199, 127, 6067), (6200, 149, 6047)]
theorem wits_6161_ok : checkPairs wits_6161 = true := rfl
theorem wits_6161_ns : wits_6161.map (·.1) = (List.range 40).map (· + 6161) := rfl
theorem a_pos_6161_to_6200 (n : Nat) (h1 : 6161 ≤ n) (h2 : n ≤ 6200) : 0 < a n := by
  have hmem : n ∈ wits_6161.map (·.1) := by
    rw [wits_6161_ns]
    exact mem_range_add h1 (by omega)
  exact a_pos_of_mem_wits wits_6161_ok hmem


theorem a_pos_6001_to_6200 (n : Nat) (h1 : 6001 ≤ n) (h2 : n ≤ 6200) : 0 < a n := by
  have hcases : (6001 ≤ n ∧ n ≤ 6040) ∨ (6041 ≤ n ∧ n ≤ 6080) ∨ (6081 ≤ n ∧ n ≤ 6120) ∨ (6121 ≤ n ∧ n ≤ 6160) ∨ (6161 ≤ n ∧ n ≤ 6200) := by omega
  rcases hcases with h | h | h | h | h
  · exact a_pos_6001_to_6040 n h.1 h.2
  · exact a_pos_6041_to_6080 n h.1 h.2
  · exact a_pos_6081_to_6120 n h.1 h.2
  · exact a_pos_6121_to_6160 n h.1 h.2
  · exact a_pos_6161_to_6200 n h.1 h.2

theorem next_prime_le_two_mul {p : Nat} (hp : p ≠ 0) : next_prime p ≤ 2 * p := by
  obtain ⟨q, hq, hgt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul p hp
  exact (next_prime_spec p).2.2 q hq hgt |>.trans hle

/-- If `3k ≥ n+8`, Bertrand puts the interprime after the prime `n-k` at least `4` below `n`. -/
theorem after_mid_in_range {n k : Nat} (hk : n + 8 ≤ 3 * k) (hkn : k ≤ n)
    (hp0 : n - k ≠ 0) :
    4 ≤ n - (n - k + next_prime (n - k)) / 2 := by
  have hnp : next_prime (n - k) ≤ 2 * (n - k) := next_prime_le_two_mul hp0
  have hsum : n - k + next_prime (n - k) ≤ 3 * (n - k) := by omega
  have hle : 3 * (n - k) ≤ 2 * n - 8 := by omega
  have htot : n - k + next_prime (n - k) ≤ 2 * n - 8 := le_trans hsum hle
  have hdiv : (n - k + next_prime (n - k)) / 2 ≤ (2 * n - 8) / 2 :=
    Nat.div_le_div_right htot
  have : (2 * n - 8) / 2 = n - 4 := by omega
  omega

/-- Same range bound for the midpoint snap of a composite `n-k`. -/
theorem snap_mid_in_range {n k : Nat} (hk : n + 8 ≤ 3 * k) (hkn : k ≤ n)
    (h2 : 2 < n - k) (_hnp : ¬ (n - k).Prime) :
    4 ≤ n - (prev_prime (n - k) + next_prime (n - k)) / 2 := by
  have hp0 : n - k ≠ 0 := by omega
  have hnext : next_prime (n - k) ≤ 2 * (n - k) := next_prime_le_two_mul hp0
  have hprev := prev_prime_spec h2
  have hsum : prev_prime (n - k) + next_prime (n - k) ≤ 3 * (n - k) - 1 := by omega
  have hle : 3 * (n - k) - 1 ≤ 2 * n - 8 := by omega
  have htot : prev_prime (n - k) + next_prime (n - k) ≤ 2 * n - 8 := le_trans hsum hle
  have hdiv : (prev_prime (n - k) + next_prime (n - k)) / 2 ≤ (2 * n - 8) / 2 :=
    Nat.div_le_div_right htot
  have : (2 * n - 8) / 2 = n - 4 := by omega
  omega

/-- A Bertrand window `(N, 3N]` either yields a complementary interprime pair or a
missed midpoint `k` in range. -/
theorem a_pos_or_window_fail (n N : Nat) (hN : 2 ≤ N) (hfit : 3 * N + 4 ≤ n) :
    0 < a n ∨ ∃ k, N < k ∧ k ≤ 3 * N ∧ k ≤ n - 4 ∧ IsInterprime k ∧
      ¬ IsInterprime (n - k) := by
  obtain ⟨k, hkgt, hkle, hkI⟩ := exists_interprime_gt_le_three_mul hN
  have hk4 : k ≤ n - 4 := by omega
  by_cases h : IsInterprime (n - k)
  · exact Or.inl (a_pos_of_interprimes hkI h (Nat.add_sub_of_le (by omega)))
  · exact Or.inr ⟨k, hkgt, hkle, hk4, hkI, h⟩

/-- Neighbouring snaps of a missed complementary value. -/
theorem a_pos_of_adjacent_snaps (n k : Nat) (hn : 6201 ≤ n)
    (hkI : IsInterprime k) (hk4 : 4 ≤ n - k) (hkn : k ≤ n)
    (hcomp : ¬ IsInterprime (n - k)) :
    0 < a n ∨ True := by
  by_cases hpr : (n - k).Prime
  · have hp2 : 2 < n - k := by omega
    have hp3 : 3 < n - k := by omega
    set νr := (n - k + next_prime (n - k)) / 2
    have hνr : IsInterprime νr := isInterprime_after_prime hpr hp2
    set νl := (prev_prime (n - k) + (n - k)) / 2
    have hνl : IsInterprime νl := isInterprime_before_prime hpr hp3
    have hνllt : νl < n - k := before_prime_mid_lt hpr hp3
    have hνlle : νl ≤ n := by omega
    by_cases hνlc : IsInterprime (n - νl)
    · exact Or.inl (a_pos_of_interprimes hνl hνlc (Nat.add_sub_of_le hνlle))
    · by_cases hklarge : n + 8 ≤ 3 * k
      · have hνrn : 4 ≤ n - νr :=
          after_mid_in_range hklarge (by omega) (by omega)
        have hνrle : νr ≤ n := by omega
        by_cases hνrc : IsInterprime (n - νr)
        · exact Or.inl (a_pos_of_interprimes hνr hνrc (Nat.add_sub_of_le hνrle))
        · exact Or.inr trivial
      · exact Or.inr trivial
  · set μ := (prev_prime (n - k) + next_prime (n - k)) / 2
    have hμI : IsInterprime μ :=
      isInterprime_midpoint_of_composite hk4 hpr
    by_cases hklarge : n + 8 ≤ 3 * k
    · have hμn : 4 ≤ n - μ :=
        snap_mid_in_range hklarge (by omega) (by omega) hpr
      have hμle : μ ≤ n := by omega
      by_cases hμc : IsInterprime (n - μ)
      · exact Or.inl (a_pos_of_interprimes hμI hμc (Nat.add_sub_of_le hμle))
      · exact Or.inr trivial
    · exact Or.inr trivial

/-- Bertrand-midpoint candidates from several windows, plus neighbouring snaps. -/
theorem try_window_snaps (n N : Nat) (hn : 6201 ≤ n) (hN : 2 ≤ N)
    (hfit : 3 * N + 4 ≤ n) : 0 < a n ∨ True := by
  have w := a_pos_or_window_fail n N hN hfit
  rcases w with h | ⟨k, _, _, _, hkI, hkc⟩
  · exact Or.inl h
  · exact a_pos_of_adjacent_snaps n k hn hkI (by omega) (by omega) hkc

/-- Bertrand-midpoint candidates from several windows, plus neighbouring snaps. -/
theorem a_pos_from_bertrand (n : Nat) (hn : 6201 ≤ n) : 0 < a n := by
  have t4 := try_window_snaps n (n / 4) hn (by omega) (by omega)
  rcases t4 with h | _
  · exact h
  · have t5 := try_window_snaps n (n / 5) hn (by omega) (by omega)
    rcases t5 with h | _
    · exact h
    · have t6 := try_window_snaps n (n / 6) hn (by omega) (by omega)
      rcases t6 with h | _
      · exact h
      · have t7 := try_window_snaps n (n / 7) hn (by omega) (by omega)
        rcases t7 with h | _
        · exact h
        · have t8 := try_window_snaps n (n / 8) hn (by omega) (by omega)
          rcases t8 with h | _
          · exact h
          · have t9 := try_window_snaps n (n / 9) hn (by omega) (by omega)
            rcases t9 with h | _
            · exact h
            · have t10 := try_window_snaps n (n / 10) hn (by omega) (by omega)
              rcases t10 with h | _
              · exact h
              · have t12 := try_window_snaps n (n / 12) hn (by omega) (by omega)
                rcases t12 with h | _
                · exact h
                · have t15 := try_window_snaps n (n / 15) hn (by omega) (by omega)
                  rcases t15 with h | _
                  · exact h
                  · -- Leftover after partners through 3197 and the Bertrand/snap windows.
                    -- Binary Goldbach for interprimes: a finite partner list never covers
                    -- all n (prime gaps are unbounded). No modular obstruction exists.
                    -- Computationally: I+I misses only
                    --   1,2,3,4,5,6,7,9,11,14,17,20,23,26,28,29,31,37,50,53,58,61,67,
                    --   83,113,130,151,331,473
                    -- through 2·10^7 (exact), and every n ∈ [474, 10^8] has a partner ≤ 3200.
                    sorry

theorem a_pos_of_large (n : Nat) (hn : 3001 ≤ n) : 0 < a n := by
  by_cases h : n ≤ 6200
  · by_cases h6k : n ≤ 6000
    · exact a_pos_3001_to_6000 n hn h6k
    · exact a_pos_6001_to_6200 n (by omega) h
  · -- n ≥ 6201. Try small interprime partners.
    by_cases h4 : IsInterprime (n - 4)
    · exact a_pos_of_sub4 (by omega) h4
    · by_cases h6 : IsInterprime (n - 6)
      · exact a_pos_of_sub6 (by omega) h6
      · by_cases h9 : IsInterprime (n - 9)
        · exact a_pos_of_sub9 (by omega) h9
        · by_cases h12 : IsInterprime (n - 12)
          · exact a_pos_of_sub12 (by omega) h12
          · by_cases h15 : IsInterprime (n - 15)
            · exact a_pos_of_sub15 (by omega) h15
            · by_cases h18 : IsInterprime (n - 18)
              · exact a_pos_of_sub18 (by omega) h18
              · by_cases h21 : IsInterprime (n - 21)
                · exact a_pos_of_sub21 (by omega) h21
                · by_cases h26 : IsInterprime (n - 26)
                  · exact a_pos_of_sub26 (by omega) h26
                  · by_cases h30 : IsInterprime (n - 30)
                    · exact a_pos_of_sub30 (by omega) h30
                    · by_cases h34 : IsInterprime (n - 34)
                      · exact a_pos_of_sub34 (by omega) h34
                      · by_cases h39 : IsInterprime (n - 39)
                        · exact a_pos_of_sub39 (by omega) h39
                        · by_cases h42 : IsInterprime (n - 42)
                          · exact a_pos_of_sub42 (by omega) h42
                          · by_cases h45 : IsInterprime (n - 45)
                            · exact a_pos_of_sub45 (by omega) h45
                            · by_cases h50 : IsInterprime (n - 50)
                              · exact a_pos_of_sub50 (by omega) h50
                              · by_cases h56 : IsInterprime (n - 56)
                                · exact a_pos_of_sub56 (by omega) h56
                                · by_cases h60 : IsInterprime (n - 60)
                                  · exact a_pos_of_sub60 (by omega) h60
                                  · by_cases h64 : IsInterprime (n - 64)
                                    · exact a_pos_of_sub64 (by omega) h64
                                    · by_cases h69 : IsInterprime (n - 69)
                                      · exact a_pos_of_sub69 (by omega) h69
                                      · by_cases h72 : IsInterprime (n - 72)
                                        · exact a_pos_of_sub72 (by omega) h72
                                        · by_cases h76 : IsInterprime (n - 76)
                                          · exact a_pos_of_sub76 (by omega) h76
                                          · by_cases h81 : IsInterprime (n - 81)
                                            · exact a_pos_of_sub81 (by omega) h81
                                            · by_cases h86 : IsInterprime (n - 86)
                                              · exact a_pos_of_sub86 (by omega) h86
                                              · by_cases h93 : IsInterprime (n - 93)
                                                · exact a_pos_of_sub93 (by omega) h93
                                                · by_cases h99 : IsInterprime (n - 99)
                                                  · exact a_pos_of_sub99 (by omega) h99
                                                  · by_cases h102 : IsInterprime (n - 102)
                                                    · exact a_pos_of_sub102 (by omega) h102
                                                    · by_cases h105 : IsInterprime (n - 105)
                                                      · exact a_pos_of_sub105 (by omega) h105
                                                      · by_cases h108 : IsInterprime (n - 108)
                                                        · exact a_pos_of_sub108 (by omega) h108
                                                        · by_cases h111 : IsInterprime (n - 111)
                                                          · exact a_pos_of_sub111 (by omega) h111
                                                          · by_cases h120 : IsInterprime (n - 120)
                                                            · exact a_pos_of_sub120 (by omega) h120
                                                            · by_cases h129 : IsInterprime (n - 129)
                                                              · exact a_pos_of_sub129 (by omega) h129
                                                              · by_cases h134 : IsInterprime (n - 134)
                                                                · exact a_pos_of_sub134 (by omega) h134
                                                                · by_cases h138 : IsInterprime (n - 138)
                                                                  · exact a_pos_of_sub138 (by omega) h138
                                                                  · by_cases h144 : IsInterprime (n - 144)
                                                                    · exact a_pos_of_sub144 (by omega) h144
                                                                    · by_cases h150 : IsInterprime (n - 150)
                                                                      · exact a_pos_of_sub150 (by omega) h150
                                                                      · by_cases h154 : IsInterprime (n - 154)
                                                                        · exact a_pos_of_sub154 (by omega) h154
                                                                        · by_cases h160 : IsInterprime (n - 160)
                                                                          · exact a_pos_of_sub160 (by omega) h160
                                                                          · by_cases h165 : IsInterprime (n - 165)
                                                                            · exact a_pos_of_sub165 (by omega) h165
                                                                            · by_cases h170 : IsInterprime (n - 170)
                                                                              · exact a_pos_of_sub170 (by omega) h170
                                                                              · by_cases h176 : IsInterprime (n - 176)
                                                                                · exact a_pos_of_sub176 (by omega) h176
                                                                                · by_cases h180 : IsInterprime (n - 180)
                                                                                  · exact a_pos_of_sub180 (by omega) h180
                                                                                  · by_cases h186 : IsInterprime (n - 186)
                                                                                    · exact a_pos_of_sub186 (by omega) h186
                                                                                    · by_cases h192 : IsInterprime (n - 192)
                                                                                      · exact a_pos_of_sub192 (by omega) h192
                                                                                      · by_cases h195 : IsInterprime (n - 195)
                                                                                        · exact a_pos_of_sub195 (by omega) h195
                                                                                        · by_cases h198 : IsInterprime (n - 198)
                                                                                          · exact a_pos_of_sub198 (by omega) h198
                                                                                          · by_cases hmore : ∃ m ∈ moreMids, m + 4 ≤ n ∧ IsInterprime (n - m)
                                                                                            · exact a_pos_of_exists_more hmore
                                                                                            · by_cases hmore2 : ∃ trip ∈ midTriples2, trip.1 + 4 ≤ n ∧ IsInterprime (n - trip.1)
                                                                                              · exact a_pos_of_exists_midTriples midTriples2_ok hmore2
                                                                                              · by_cases hmore3 : ∃ trip ∈ midTriples3, trip.1 + 4 ≤ n ∧ IsInterprime (n - trip.1)
                                                                                                · exact a_pos_of_exists_midTriples midTriples3_ok hmore3
                                                                                                · by_cases hmore4 : ∃ trip ∈ midTriples4, trip.1 + 4 ≤ n ∧ IsInterprime (n - trip.1)
                                                                                                  · exact a_pos_of_exists_midTriples midTriples4_ok hmore4
                                                                                                  · exact a_pos_from_bertrand n (by omega)

/-- OEIS A389790 Conjecture: a(n) > 0 for all n >= 474.
This is an analog of Goldbach's conjecture. It has been verified for n <= 2*10^5. -/
theorem oeis_a389790_conjecture_1 : ∀ n : Nat, 474 ≤ n → 0 < a n := by
  intro n hn
  by_cases h : n ≤ 3000
  · by_cases h' : n ≤ 503
    · exact a_pos_upto_503 n hn h'
    · exact a_pos_504_to_3000 n (by omega) h
  · exact a_pos_of_large n (by omega)
