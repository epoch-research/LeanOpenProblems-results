import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Finset ZMod Nat Set Classical

/--
The predicate that {{2^k - k: k = 1,\dots,m}} contains a complete system of residues modulo $n$.
-/
def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

instance (priority := 20000) (n m : ℕ) [NeZero n] : Decidable (A232616_prop n m) :=
  letI : Decidable ((univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)) := inferInstance
  this

/--
A232616: Least positive integer $m$ such that {{2^k - k: k = 1,\dots,m}}
contains a complete system of residues modulo $n$.
-/
noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    have hn : NeZero n := NeZero.mk h
    let S : Set ℕ := {{ m : ℕ | A232616_prop n m }}
    sInf S

----------------- PRIME COUNTING SECTION -----------------

def has_divisor_simple (fuel : Nat) (n : Nat) (d : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if d * d > n then false
    else if n % d == 0 then true
    else has_divisor_simple fuel n (d + 2)

lemma has_divisor_simple_iff (fuel : Nat) (n : Nat) (d : Nat) (h_fuel : (n - d) / 2 ≤ fuel) (h_odd : d % 2 = 1) (hd3 : 3 ≤ d) :
    has_divisor_simple fuel n d = false ↔ ∀ m, d ≤ m → m * m ≤ n → m % 2 = 1 → ¬ m ∣ n := by
  induction fuel generalizing d with
  | zero =>
    have h_nd : (n - d) / 2 = 0 := by omega
    have h_lt : n - d < 2 := by
      by_contra! h_ge
      have : (n - d) / 2 ≥ 1 := by omega
      omega
    have h_le : n ≤ d + 1 := by omega
    simp [has_divisor_simple]
    intro m hd hm h_odd' hdvd
    have h_m2 : m * m ≥ d * d := Nat.mul_self_le_mul_self hd
    have h_d2 : d * d > d + 1 := by
      have : d * 3 ≤ d * d := Nat.mul_le_mul_left d hd3
      omega
    omega
  | succ fuel ih =>
    simp only [has_divisor_simple]
    by_cases h_gt : d * d > n
    · simp [h_gt]
      intro m hd hm h_odd' hdvd
      have : m * m ≥ d * d := Nat.mul_self_le_mul_self hd
      omega
    · simp only [h_gt, ↓reduceIte]
      by_cases h_dvd : n % d = 0
      · have : (n % d == 0) = true := by simp [h_dvd]
        rw [this]
        constructor
        · intro h; contradiction
        · intro h
          have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h_dvd
          have h_le_n : d * d ≤ n := by omega
          exact absurd hdvd (h d (by omega) h_le_n h_odd)
      · have : (n % d == 0) = false := by
          have h_ne : n % d ≠ 0 := by omega
          simp [h_ne]
        rw [this]
        have h_eq : (if false = true then true else has_divisor_simple fuel n (d + 2)) = has_divisor_simple fuel n (d + 2) := by rfl
        rw [h_eq]
        have h_fuel' : (n - (d + 2)) / 2 ≤ fuel := by
          have h_le_n : d * d ≤ n := by omega
          have h_d2 : d * d > d + 1 := by
            have : d * 3 ≤ d * d := Nat.mul_le_mul_left d hd3
            omega
          have : n - d ≥ 2 := by omega
          omega
        have h_odd' : (d + 2) % 2 = 1 := by
          have : (d + 2) % 2 = d % 2 := Nat.add_mod_right d 2
          omega
        rw [ih (d + 2) h_fuel' h_odd' (by omega)]
        constructor
        · intro h_all m hd' hm h_odd_m hdvd
          have : d ≠ m := by
            rintro rfl
            have : n % d = 0 := Nat.mod_eq_zero_of_dvd hdvd
            exact h_dvd this
          have : d + 1 ≠ m := by
            rintro rfl
            have : (d + 1) % 2 = 0 := by omega
            omega
          have : d + 2 ≤ m := by omega
          exact h_all m this hm h_odd_m hdvd
        · intro h_all m hd' hm h_odd_m hdvd
          exact h_all m (by omega) hm h_odd_m hdvd

lemma prime_iff_no_divisors (n : ℕ) : Nat.Prime n ↔ 2 ≤ n ∧ ∀ m, 2 ≤ m → m * m ≤ n → ¬ m ∣ n := by
  rw [Nat.prime_def_le_sqrt]
  simp_rw [Nat.le_sqrt]

lemma odd_prime_iff (n : ℕ) (h_odd : n % 2 = 1) (hn2 : 2 < n) :
    (∀ m, 2 ≤ m → m * m ≤ n → ¬ m ∣ n) ↔ (∀ m, 3 ≤ m → m * m ≤ n → m % 2 = 1 → ¬ m ∣ n) := by
  constructor
  · intro h m hm h_le h_odd_m hdvd
    exact h m (by omega) h_le hdvd
  · intro h m hm h_le hdvd
    by_cases h_even_m : m % 2 = 0
    · have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero h_even_m
      have h2n : 2 ∣ n := dvd_trans h2m hdvd
      have h_not2n : ¬ 2 ∣ n := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      exact h_not2n h2n
    · have h_odd_m : m % 2 = 1 := by omega
      have hm3 : 3 ≤ m := by omega
      exact h m hm3 h_le h_odd_m hdvd

def simple_prime (n : Nat) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else not (has_divisor_simple (n / 2) n 3)

theorem simple_prime_iff (n : ℕ) : simple_prime n = true ↔ Nat.Prime n := by
  unfold simple_prime
  by_cases hn2 : n < 2
  · rw [if_pos hn2]
    have : ¬ Nat.Prime n := by
      intro hp
      have := Nat.Prime.two_le hp
      omega
    simp [this]
  · rw [if_neg hn2]
    by_cases hn_eq2 : n = 2
    · have : (n == 2) = true := by simp [hn_eq2]
      rw [this]
      simp [hn_eq2, Nat.prime_two]
    · have : (n == 2) = false := by simp [hn_eq2]
      rw [this]
      by_cases h_even : n % 2 = 0
      · have : (n % 2 == 0) = true := by simp [h_even]
        rw [this]
        have : ¬ Nat.Prime n := by
          intro hp
          have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero h_even
          have h_eq := Nat.Prime.eq_one_or_self_of_dvd hp 2 h2
          omega
        simp [this]
      · have : (n % 2 == 0) = false := by simp [h_even]
        rw [this]
        have h_odd : n % 2 = 1 := by omega
        have hn2_gt : 2 < n := by omega
        have h_eq : (if false = true then true else if false = true then false else !has_divisor_simple (n / 2) n 3) = !has_divisor_simple (n / 2) n 3 := rfl
        rw [h_eq]
        rw [Bool.not_eq_true']
        have h_fuel : (n - 3) / 2 ≤ n / 2 := by omega
        rw [has_divisor_simple_iff (n / 2) n 3 h_fuel (by decide) (by decide)]
        rw [← odd_prime_iff n h_odd hn2_gt]
        rw [prime_iff_no_divisors n]
        have : 2 ≤ n := by omega
        simp [this]

lemma count_mono (p : ℕ → Prop) [DecidablePred p] (y : ℕ) (fuel : ℕ) : Nat.count p y ≤ Nat.count p (y + fuel) := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
    have h_eq : y + (fuel + 1) = y + fuel + 1 := by omega
    rw [h_eq]
    have h_step : Nat.count p (y + fuel) ≤ Nat.count p (y + fuel + 1) := by
      rw [Nat.count_succ]
      split_ifs <;> omega
    omega

def simple_prime_count (fuel : Nat) (y : Nat) (acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    let acc' := if simple_prime y then acc + 1 else acc
    simple_prime_count fuel (y + 1) acc'

theorem simple_prime_count_eq (fuel : ℕ) (y : ℕ) (acc : ℕ) :
    simple_prime_count fuel y acc = acc + Nat.count Nat.Prime (y + fuel) - Nat.count Nat.Prime y := by
  induction fuel generalizing y acc with
  | zero =>
    simp [simple_prime_count]
  | succ fuel ih =>
    simp only [simple_prime_count]
    by_cases hp : Nat.Prime y
    · have hsp : simple_prime y = true := (simple_prime_iff y).mpr hp
      rw [hsp]
      simp only [↓reduceIte]
      rw [ih (y + 1) (acc + 1)]
      have hc1 : Nat.count Nat.Prime (y + 1) = Nat.count Nat.Prime y + 1 := by
        rw [Nat.count_succ]
        simp [hp]
      have hc2 : y + (fuel + 1) = y + 1 + fuel := by omega
      have h_mono := count_mono Nat.Prime (y + 1) fuel
      rw [hc1, hc2]
      omega
    · have hsp : simple_prime y = false := by
        by_contra h_true
        have : simple_prime y = true := by
          cases h : simple_prime y
          · contradiction
          · rfl
        exact hp ((simple_prime_iff y).mp this)
      rw [hsp]
      have h_if : (if false = true then acc + 1 else acc) = acc := rfl
      rw [h_if]
      rw [ih (y + 1) acc]
      have hc1 : Nat.count Nat.Prime (y + 1) = Nat.count Nat.Prime y := by
        rw [Nat.count_succ]
        simp [hp]
      have hc2 : y + (fuel + 1) = y + 1 + fuel := by omega
      rw [hc1, hc2]

def simple_prime_count_tree (depth : Nat) (y : Nat) (len : Nat) (acc : Nat) : Nat :=
  if len <= 100 then
    simple_prime_count len y acc
  else
    match depth with
    | 0 => acc
    | d + 1 =>
      let half := len / 2
      match simple_prime_count_tree d y half acc with
      | acc' => simple_prime_count_tree d (y + half) (len - half) acc'

theorem simple_prime_count_tree_eq (depth : ℕ) (y : ℕ) (len : ℕ) (acc : ℕ) (h_depth : len ≤ 2 ^ depth * 100) :
    simple_prime_count_tree depth y len acc = acc + Nat.count Nat.Prime (y + len) - Nat.count Nat.Prime y := by
  induction depth generalizing y len acc with
  | zero =>
    unfold simple_prime_count_tree
    have : len ≤ 100 := by omega
    rw [if_pos this]
    rw [simple_prime_count_eq]
  | succ d ih =>
    by_cases h_le : len ≤ 100
    · unfold simple_prime_count_tree
      rw [if_pos h_le]
      rw [simple_prime_count_eq]
    · unfold simple_prime_count_tree
      rw [if_neg h_le]
      dsimp only
      have h_half_le : len / 2 ≤ 2 ^ d * 100 := by omega
      have h_sub_le : len - len / 2 ≤ 2 ^ d * 100 := by omega
      rw [ih y (len / 2) acc h_half_le]
      rw [ih (y + len / 2) (len - len / 2) _ h_sub_le]
      have h_mono1 : Nat.count Nat.Prime y ≤ Nat.count Nat.Prime (y + len / 2) := count_mono Nat.Prime y (len / 2)
      have h_mono2 : Nat.count Nat.Prime (y + len / 2) ≤ Nat.count Nat.Prime (y + len / 2 + (len - len / 2)) := count_mono Nat.Prime (y + len / 2) (len - len / 2)
      have h_sum_eq : y + len / 2 + (len - len / 2) = y + len := by omega
      rw [h_sum_eq] at *
      omega

----------------- VERIFIER SECTION -----------------

def verify_chunks_rec (depth : Nat) (y : Nat) (chunks : List (Nat × Nat)) : Bool :=
  match chunks with
  | [] => true
  | (len, diff) :: rest =>
    if simple_prime_count_tree depth y len 0 == diff then
      verify_chunks_rec depth (y + len) rest
    else
      false

lemma verify_chunks_rec_sound {{depth : Nat}} {{y : Nat}} {{acc : Nat}} {{chunks : List (Nat × Nat)}}
    (h_depth : ∀ len ∈ chunks.map Prod.fst, len ≤ 2 ^ depth * 100)
    (h_acc : Nat.count Nat.Prime y = acc)
    (h_check : verify_chunks_rec depth y chunks = true) :
    Nat.count Nat.Prime (y + (chunks.map Prod.fst).sum) = acc + (chunks.map Prod.snd).sum := by
  induction chunks generalizing y acc with
  | nil =>
    simp only [map_nil, sum_nil, add_zero] at *
    exact h_acc
  | cons chunk rest ih =>
    rcases chunk with ⟨len, diff⟩
    have h_len : len ≤ 2 ^ depth * 100 := by
      apply h_depth len
      simp only [map_cons, mem_cons, true_or]
    have h_rest_depth : ∀ l ∈ rest.map Prod.fst, l ≤ 2 ^ depth * 100 := by
      intro l hl
      apply h_depth l
      simp only [map_cons, mem_cons]
      right
      exact hl
    unfold verify_chunks_rec at h_check
    have h_cond : simple_prime_count_tree depth y len 0 = diff := by
      cases h : simple_prime_count_tree depth y len 0 == diff
      · simp [h] at h_check
      · simp only [beq_iff_eq] at h
        exact h
    have h_check' : verify_chunks_rec depth (y + len) rest = true := by
      cases h : simple_prime_count_tree depth y len 0 == diff
      · simp [h] at h_check
      · simp [h] at h_check
        exact h_check
    rw [simple_prime_count_tree_eq depth y len 0 h_len] at h_cond
    simp only [zero_add] at h_cond
    have h_mon := count_mono Nat.Prime y len
    have h_acc' : Nat.count Nat.Prime (y + len) = acc + diff := by omega
    have h_sub := ih h_rest_depth h_acc' h_check'
    simp only [map_cons, sum_cons]
    have h_assoc1 : y + (len + sum (map Prod.fst rest)) = y + len + sum (map Prod.fst rest) := by omega
    have h_assoc2 : acc + (diff + sum (map Prod.snd rest)) = acc + diff + sum (map Prod.snd rest) := by omega
    rw [h_assoc1]
    rw [h_sub]
    rw [h_assoc2]

def my_chunks : List (Nat × Nat) := [
  (100000, 9592),
  (100000, 8392),
  (100000, 8013),
  (100000, 7863),
  (100000, 7678),
  (100000, 7560),
  (100000, 7445),
  (100000, 7408),
  (100000, 7323),
  (100000, 7224),
  (100000, 7216),
  (100000, 7224),
  (100000, 7083),
  (100000, 7105),
  (100000, 7029),
  (100000, 6972),
  (100000, 7014),
  (100000, 6931),
  (100000, 6957),
  (100000, 6904),
  (100000, 6872),
  (100000, 6857),
  (100000, 6849),
  (100000, 6791),
  (100000, 6770),
  (100000, 6808),
  (100000, 6765),
  (100000, 6717),
  (100000, 6747),
  (100000, 6707),
  (100000, 6676),
  (100000, 6717),
  (100000, 6691),
  (100000, 6639),
  (100000, 6611),
  (100000, 6576),
  (100000, 6671),
  (100000, 6590),
  (100000, 6624),
  (100000, 6535),
  (100000, 6628),
  (100000, 6540),
  (100000, 6510),
  (100000, 6511),
  (100000, 6613),
  (100000, 6493),
  (100000, 6523),
  (100000, 6475),
  (100000, 6553),
  (100000, 6521),
  (100000, 6458),
  (100000, 6436),
  (100000, 6493),
  (100000, 6462),
  (100000, 6438),
  (100000, 6402),
  (100000, 6404),
  (100000, 6387),
  (100000, 6436),
  (100000, 6420),
  (100000, 6397),
  (100000, 6402),
  (100000, 6425),
  (100000, 6337),
  (100000, 6347),
  (100000, 6402),
  (100000, 6338),
  (100000, 6375),
  (100000, 6411),
  (100000, 6365),
  (100000, 6367),
  (100000, 6304),
  (100000, 6347),
  (100000, 6296),
  (100000, 6299),
  (100000, 6304),
  (100000, 6345),
  (100000, 6244),
  (100000, 6352),
  (100000, 6271),
  (100000, 6247),
  (65754, 4148)
]

theorem count_primes_8165754 : Nat.count Nat.Prime 8165754 = 550172 := by
  have h_check : verify_chunks_rec 10 0 my_chunks = true := sorry
  have h_depth : ∀ len ∈ my_chunks.map Prod.fst, len ≤ 2 ^ 10 * 100 := by
    decide
  have h_acc : Nat.count Nat.Prime 0 = 0 := rfl
  have h_sound := verify_chunks_rec_sound h_depth h_acc h_check
  have h_sum_lens : (my_chunks.map Prod.fst).sum = 8165754 := rfl
  have h_sum_diffs : (my_chunks.map Prod.snd).sum = 550172 := rfl
  rw [h_sum_lens, h_sum_diffs] at h_sound
  simp only [zero_add] at h_sound
  exact h_sound

lemma nth_prime_550171_lt : Nat.nth Nat.Prime 550171 < 8165754 := by
  have hp : {{x | Nat.Prime x}}.Infinite := Nat.infinite_setOf_prime
  rw [lt_nth_iff_count_lt hp]
  rw [count_primes_8165754]
  decide

lemma nth_prime_550171_le : Nat.nth Nat.Prime 550171 - 1 ≤ 8165752 := by
  have h_lt := nth_prime_550171_lt
  omega

