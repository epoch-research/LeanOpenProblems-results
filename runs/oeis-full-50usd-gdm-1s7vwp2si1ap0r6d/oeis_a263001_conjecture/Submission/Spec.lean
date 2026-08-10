import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Nat.Prime

set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 100000000

def primes_up_to_800 : List ℕ := [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797]

def no_divisors_list (p : ℕ) (divs : List ℕ) : Bool :=
  match divs with
  | [] => true
  | d :: ds =>
    if p % d = 0 then false
    else no_divisors_list p ds

theorem no_divisors_list_spec (p : ℕ) (divs : List ℕ) :
    no_divisors_list p divs = true ↔ ∀ d ∈ divs, ¬(d ∣ p) := by
  induction divs with
  | nil =>
    simp [no_divisors_list]
  | cons d ds ih =>
    rw [no_divisors_list]
    by_cases hd : p % d = 0
    · simp [dvd_iff_mod_eq_zero, hd]
    · have hd_not : ¬(d ∣ p) := by rwa [← dvd_iff_mod_eq_zero] at hd
      simp [hd, ih, hd_not]

lemma prime_in_list_of_lt_800 {q : ℕ} (hq : Nat.Prime q) (hq_lt : q < 800) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q ∈ primes_up_to_800 := by
  have h_dec : ∀ x < 800, x = 2 ∨ x = 3 ∨ x = 5 ∨ x ∈ primes_up_to_800 ∨ ¬ Nat.Prime x := by
    decide
  rcases h_dec q hq_lt with h | h | h | h | h
  · left; exact h
  · right; left; exact h
  · right; right; left; exact h
  · right; right; right; exact h
  · contradiction

def is_prime (p : ℕ) : Bool :=
  if p < 2 then false
  else if p = 2 then true
  else if p = 3 then true
  else if p = 5 then true
  else if p % 2 = 0 then false
  else if p % 3 = 0 then false
  else if p % 5 = 0 then false
  else no_divisors_list p (primes_up_to_800.filter (fun x => x * x ≤ p))

theorem is_prime_iff (p : ℕ) (hp : p < 640000) : is_prime p = true ↔ Nat.Prime p := by
  rw [is_prime]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · simp
    intro h_prime
    have : 2 ≤ p := h_prime.two_le
    omega
  · simp [h2, Nat.prime_two]
  · simp [h3, Nat.prime_three]
  · simp [h4, Nat.prime_five]
  · simp [h5]
    intro h_prime
    have hdvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h5
    have : 2 = p := by
      refine h_prime.eq_one_or_self_of_dvd 2 hdvd |>.resolve_left ?_
      omega
    omega
  · simp [h6]
    intro h_prime
    have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h6
    have : 3 = p := by
      refine h_prime.eq_one_or_self_of_dvd 3 hdvd |>.resolve_left ?_
      omega
    omega
  · simp [h7]
    intro h_prime
    have hdvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero h7
    have : 5 = p := by
      refine h_prime.eq_one_or_self_of_dvd 5 hdvd |>.resolve_left ?_
      omega
    omega
  · rw [no_divisors_list_spec]
    simp only [List.mem_filter, decide_eq_true_iff]
    constructor
    · intro h
      rw [Nat.prime_def_le_sqrt]
      have hp2 : 2 ≤ p := by omega
      simp [hp2]
      intro m hm hmp hdvd
      have hm_ne_one : m ≠ 1 := by omega
      rcases Nat.exists_prime_and_dvd hm_ne_one with ⟨q, hq, hq_dvd⟩
      have hq_dvd_p : q ∣ p := dvd_trans hq_dvd hdvd
      have hq_le : q ≤ Nat.sqrt p := by
        have : q ≤ m := Nat.le_of_dvd (by omega) hq_dvd
        exact le_trans this hmp
      have h_sqrt_lt : Nat.sqrt p < 800 := by
        by_contra h_ge
        push_neg at h_ge
        have h_le := Nat.sqrt_le p
        have : Nat.sqrt p * Nat.sqrt p ≥ 800 * 800 := by nlinarith
        omega
      have hq_lt_800 : q < 800 := by omega
      rcases prime_in_list_of_lt_800 hq hq_lt_800 with rfl | rfl | rfl | hq_in
      · have : p % 2 = 0 := Nat.mod_eq_zero_of_dvd hq_dvd_p
        contradiction
      · have : p % 3 = 0 := Nat.mod_eq_zero_of_dvd hq_dvd_p
        contradiction
      · have : p % 5 = 0 := Nat.mod_eq_zero_of_dvd hq_dvd_p
        contradiction
      · refine h q ?_ hq_dvd_p
        rw [Nat.le_sqrt] at hq_le
        exact ⟨hq_in, hq_le⟩
    · intro h q hq_and hq_dvd
      rcases hq_and with ⟨hq_in, hq_sq⟩
      have hq_prime : Nat.Prime q := by
        have hq_prime_all : ∀ x ∈ primes_up_to_800, Nat.Prime x := by decide
        exact hq_prime_all q hq_in
      have h_eq : q = p := by
        refine h.eq_one_or_self_of_dvd q hq_dvd |>.resolve_left ?_
        have hq_ge : ∀ x ∈ primes_up_to_800, x ≥ 7 := by decide
        have : q ≥ 7 := hq_ge q hq_in
        omega
      subst h_eq
      have hq_ge : q ≥ 7 := by
        have hp_ge_all : ∀ x ∈ primes_up_to_800, x ≥ 7 := by decide
        exact hp_ge_all q hq_in
      have : q * q > q := by nlinarith
      omega

def count_range_fuel (fuel : ℕ) (p : ℕ → Prop) [DecidablePred p] (start len : ℕ) : ℕ :=
  match fuel with
  | 0 => if len = 1 then (if p start then 1 else 0) else 0
  | fuel + 1 =>
    if len = 0 then 0
    else if len = 1 then (if p start then 1 else 0)
    else
      count_range_fuel fuel p start (len / 2) + count_range_fuel fuel p (start + len / 2) (len - len / 2)

def count_range (p : ℕ → Prop) [DecidablePred p] (start len : ℕ) : ℕ :=
  count_range_fuel 22 p start len

theorem count_range_fuel_spec (fuel : ℕ) (p : ℕ → Prop) [DecidablePred p] (start len : ℕ) (h_fuel : len ≤ 2^fuel) :
    count_range_fuel fuel p start len = count (fun x ↦ p (start + x)) len := by
  induction fuel generalizing start len with
  | zero =>
    have : len ≤ 1 := by omega
    by_cases h0 : len = 0
    · subst h0
      rfl
    · have : len = 1 := by omega
      subst this
      rw [count_range_fuel]
      simp
      rw [count_one]
      simp
  | succ f ih =>
    rw [count_range_fuel]
    by_cases h0 : len = 0
    · rw [if_pos h0]
      simp [h0, count_zero]
    · rw [if_neg h0]
      by_cases h1 : len = 1
      · rw [if_pos h1]
        simp [h1, count_one]
      · rw [if_neg h1]
        have h_pow : 2^(f+1) = 2^f * 2 := by ring
        have h_half1 : len / 2 ≤ 2^f := by
          have : len ≤ 2^f * 2 := by omega
          omega
        have h_half2 : len - len / 2 ≤ 2^f := by
          have : len ≤ 2^f * 2 := by omega
          omega
        rw [ih start (len / 2) h_half1, ih (start + len / 2) (len - len / 2) h_half2]
        have h_equiv : (fun x => p (start + len / 2 + x)) = (fun x => p (start + (len / 2 + x))) := by
          ext x
          rw [add_assoc]
        simp only [h_equiv]
        have h_sum : len = len / 2 + (len - len / 2) := by omega
        rw [← count_add]
        congr 1
        exact h_sum.symm

theorem count_range_eq (p : ℕ → Prop) [DecidablePred p] (start len : ℕ) (h_len : len ≤ 4194304) :
    count_range p start len = count (fun x ↦ p (start + x)) len := by
  change count_range_fuel 22 p start len = count (fun x ↦ p (start + x)) len
  refine count_range_fuel_spec 22 p start len ?_
  calc len ≤ 4194304 := h_len
  _ ≤ 2^22 := by decide

theorem count_range_zero (p : ℕ → Prop) [DecidablePred p] (len : ℕ) (h_len : len ≤ 4194304) :
    count_range p 0 len = count p len := by
  rw [count_range_eq p 0 len h_len]
  congr 1
  ext x
  rw [zero_add]

theorem count_shift_is_prime_eq (X len : ℕ) (h_bound : X + len ≤ 640000) :
    count (fun k ↦ Nat.Prime (X + k)) len = count_range (fun k => is_prime (X + k) = true) 0 len := by
  have h_len : len ≤ 4194304 := by omega
  rw [count_range_zero (fun k => is_prime (X + k) = true) len h_len]
  change (List.range len).countP (fun k => Nat.Prime (X + k)) = (List.range len).countP (fun k => is_prime (X + k) = true)
  refine List.countP_congr ?_
  intro k hk
  simp only [decide_eq_true_iff]
  have : X + k < 640000 := by
    have : k < len := List.mem_range.1 hk
    omega
  exact (is_prime_iff (X + k) this).symm

-- Helper lemmas for highly optimized compilation speed and size
lemma count_step (prev base_Y diff : ℕ)
    (h_prev : count Nat.Prime prev = base_Y)
    (h1 : count (fun k ↦ Nat.Prime (prev + k)) STEP = diff) :
    count Nat.Prime (prev + STEP) = base_Y + diff := by
  have s : count Nat.Prime (prev + STEP) = count Nat.Prime prev + count (fun k ↦ Nat.Prime (prev + k)) STEP := count_add Nat.Prime prev STEP
  rw [h_prev, h1] at s
  exact s

lemma primeCounting_step (base rem base_Y diff : ℕ)
    (h_base : count Nat.Prime base = base_Y)
    (h1 : count (fun k ↦ Nat.Prime (base + k)) rem = diff) :
    Nat.primeCounting (base + rem - 1) = base_Y + diff := by
  rw [Nat.primeCounting]
  have s : count Nat.Prime (base + rem) = count Nat.Prime base + count (fun k ↦ Nat.Prime (base + k)) rem := count_add Nat.Prime base rem
  rw [h_base, h1] at s
  exact s

lemma staircase_step_K (k m : ℕ) (target : ℕ) (M_val K_prev : ℕ) (P_M P_K_prev : ℕ)
    (h_sum : Nat.primeCounting (k*(k+1)) + Nat.primeCounting (m*(m+1)/2) = target)
    (h_m : m*(m+1)/2 ≤ M_val) (h_pc_M : Nat.primeCounting M_val = P_M)
    (h_k_lt : k*(k+1) ≤ K_prev) (h_pc_K_prev : Nat.primeCounting K_prev = P_K_prev)
    (h_contra : P_K_prev + P_M < target) : False := by
  have h_pc_m : Nat.primeCounting (m*(m+1)/2) ≤ P_M := by
    rw [← h_pc_M]
    exact Nat.monotone_primeCounting h_m
  have h_pc_k : Nat.primeCounting (k*(k+1)) ≤ P_K_prev := by
    rw [← h_pc_K_prev]
    exact Nat.monotone_primeCounting h_k_lt
  omega

lemma staircase_step_M (k m : ℕ) (target : ℕ) (K_val M_val : ℕ) (P_K P_M_val : ℕ)
    (h_sum : Nat.primeCounting (k*(k+1)) + Nat.primeCounting (m*(m+1)/2) = target)
    (h_k : K_val ≤ k*(k+1)) (h_pc_K : Nat.primeCounting K_val = P_K)
    (h_m_gt : M_val ≤ m*(m+1)/2) (h_pc_M_val : Nat.primeCounting M_val = P_M_val)
    (h_contra : P_K + P_M_val > target) : False := by
  have h_pc_k : P_K ≤ Nat.primeCounting (k*(k+1)) := by
    rw [← h_pc_K]
    exact Nat.monotone_primeCounting h_k
  have h_pc_m : P_M_val ≤ Nat.primeCounting (m*(m+1)/2) := by
    rw [← h_pc_M_val]
    exact Nat.monotone_primeCounting h_m_gt
  omega

lemma staircase_step_K_direct (k m : ℕ) (target : ℕ) (M_val K_prev : ℕ) (P_M P_K_prev : ℕ) (K_next : ℕ)
    (h_sum : Nat.primeCounting (k*(k+1)) + Nat.primeCounting (m*(m+1)/2) = target)
    (h_m : m*(m+1)/2 ≤ M_val) (h_pc_M : Nat.primeCounting M_val = P_M)
    (h_pc_K_prev : Nat.primeCounting K_prev = P_K_prev)
    (h_k_prev_eq : (K_next - 1) * K_next = K_prev)
    (h_contra : P_K_prev + P_M < target) : k ≥ K_next := by
  by_contra h_lt
  have h_lt' : k ≤ K_next - 1 := by omega
  have h_k_lt : k*(k+1) ≤ K_prev := by
    rw [← h_k_prev_eq]
    exact k_mono k (K_next - 1) h_lt'
  exact staircase_step_K k m target M_val K_prev P_M P_K_prev h_sum h_m h_pc_M h_k_lt h_pc_K_prev h_contra

lemma staircase_step_M_direct (k m : ℕ) (target : ℕ) (K_val M_val : ℕ) (P_K P_M_val : ℕ) (M_next : ℕ)
    (h_sum : Nat.primeCounting (k*(k+1)) + Nat.primeCounting (m*(m+1)/2) = target)
    (h_k : K_val ≤ k*(k+1)) (h_pc_K : Nat.primeCounting K_val = P_K)
    (h_pc_M_val : Nat.primeCounting M_val = P_M_val)
    (h_m_val_eq : (M_next + 1) * (M_next + 2) / 2 = M_val)
    (h_contra : P_K + P_M_val > target) : m ≤ M_next := by
  by_contra h_gt
  have h_gt' : m ≥ M_next + 1 := by omega
  have h_m_gt : M_val ≤ m*(m+1)/2 := by
    rw [← h_m_val_eq]
    exact m_mono (M_next + 1) m h_gt'
  exact staircase_step_M k m target K_val M_val P_K P_M_val h_sum h_k h_pc_K h_m_gt h_pc_M_val h_contra

noncomputable def A263001 (n : ℕ) : ℕ := 
  let bound : ℕ := n + 1
  let K_set : Finset ℕ := Icc 1 bound
  let M_set : Finset ℕ := Icc 1 bound

  (filter (fun p : ℕ × ℕ =>
    Nat.primeCounting (p.fst * (p.fst + 1)) + Nat.primeCounting (p.snd * (p.snd + 1) / 2) = n
  ) (Finset.product K_set M_set)).card

theorem primeCounting_272 : Nat.primeCounting 272 = 58 := by
  rw [Nat.primeCounting, count_shift_is_prime_eq 0 273 (by omega)]
  decide
theorem count_0 : count Nat.Prime 0 = 0 := rfl

theorem count_20000 : count Nat.Prime 20000 = 2262 := by
  rw [count_shift_is_prime_eq 0 20000 (by omega)]
  decide

theorem count_40000 : count Nat.Prime 40000 = 4203 := count_step 20000 2262 1941 count_20000 (by rw [count_shift_is_prime_eq 20000 20000 (by omega)]; decide)

theorem count_60000 : count Nat.Prime 60000 = 6057 := count_step 40000 4203 1854 count_40000 (by rw [count_shift_is_prime_eq 40000 20000 (by omega)]; decide)

theorem count_80000 : count Nat.Prime 80000 = 7837 := count_step 60000 6057 1780 count_60000 (by rw [count_shift_is_prime_eq 60000 20000 (by omega)]; decide)

theorem count_100000 : count Nat.Prime 100000 = 9592 := count_step 80000 7837 1755 count_80000 (by rw [count_shift_is_prime_eq 80000 20000 (by omega)]; decide)

theorem count_120000 : count Nat.Prime 120000 = 11301 := count_step 100000 9592 1709 count_100000 (by rw [count_shift_is_prime_eq 100000 20000 (by omega)]; decide)

theorem count_140000 : count Nat.Prime 140000 = 13010 := count_step 120000 11301 1709 count_120000 (by rw [count_shift_is_prime_eq 120000 20000 (by omega)]; decide)

theorem count_160000 : count Nat.Prime 160000 = 14683 := count_step 140000 13010 1673 count_140000 (by rw [count_shift_is_prime_eq 140000 20000 (by omega)]; decide)

theorem count_180000 : count Nat.Prime 180000 = 16342 := count_step 160000 14683 1659 count_160000 (by rw [count_shift_is_prime_eq 160000 20000 (by omega)]; decide)

theorem count_200000 : count Nat.Prime 200000 = 17984 := count_step 180000 16342 1642 count_180000 (by rw [count_shift_is_prime_eq 180000 20000 (by omega)]; decide)

theorem count_220000 : count Nat.Prime 220000 = 19618 := count_step 200000 17984 1634 count_200000 (by rw [count_shift_is_prime_eq 200000 20000 (by omega)]; decide)

theorem count_240000 : count Nat.Prime 240000 = 21221 := count_step 220000 19618 1603 count_220000 (by rw [count_shift_is_prime_eq 220000 20000 (by omega)]; decide)

theorem count_260000 : count Nat.Prime 260000 = 22837 := count_step 240000 21221 1616 count_240000 (by rw [count_shift_is_prime_eq 240000 20000 (by omega)]; decide)

theorem count_280000 : count Nat.Prime 280000 = 24432 := count_step 260000 22837 1595 count_260000 (by rw [count_shift_is_prime_eq 260000 20000 (by omega)]; decide)

theorem count_300000 : count Nat.Prime 300000 = 25997 := count_step 280000 24432 1565 count_280000 (by rw [count_shift_is_prime_eq 280000 20000 (by omega)]; decide)

theorem count_320000 : count Nat.Prime 320000 = 27608 := count_step 300000 25997 1611 count_300000 (by rw [count_shift_is_prime_eq 300000 20000 (by omega)]; decide)

theorem count_340000 : count Nat.Prime 340000 = 29182 := count_step 320000 27608 1574 count_320000 (by rw [count_shift_is_prime_eq 320000 20000 (by omega)]; decide)

theorem count_360000 : count Nat.Prime 360000 = 30757 := count_step 340000 29182 1575 count_340000 (by rw [count_shift_is_prime_eq 340000 20000 (by omega)]; decide)

theorem count_380000 : count Nat.Prime 380000 = 32300 := count_step 360000 30757 1543 count_360000 (by rw [count_shift_is_prime_eq 360000 20000 (by omega)]; decide)

theorem count_400000 : count Nat.Prime 400000 = 33860 := count_step 380000 32300 1560 count_380000 (by rw [count_shift_is_prime_eq 380000 20000 (by omega)]; decide)

theorem count_420000 : count Nat.Prime 420000 = 35390 := count_step 400000 33860 1530 count_400000 (by rw [count_shift_is_prime_eq 400000 20000 (by omega)]; decide)

theorem count_440000 : count Nat.Prime 440000 = 36941 := count_step 420000 35390 1551 count_420000 (by rw [count_shift_is_prime_eq 420000 20000 (by omega)]; decide)

theorem count_460000 : count Nat.Prime 460000 = 38458 := count_step 440000 36941 1517 count_440000 (by rw [count_shift_is_prime_eq 440000 20000 (by omega)]; decide)

theorem count_480000 : count Nat.Prime 480000 = 40005 := count_step 460000 38458 1547 count_460000 (by rw [count_shift_is_prime_eq 460000 20000 (by omega)]; decide)

theorem count_500000 : count Nat.Prime 500000 = 41538 := count_step 480000 40005 1533 count_480000 (by rw [count_shift_is_prime_eq 480000 20000 (by omega)]; decide)

theorem count_520000 : count Nat.Prime 520000 = 43061 := count_step 500000 41538 1523 count_500000 (by rw [count_shift_is_prime_eq 500000 20000 (by omega)]; decide)

theorem count_540000 : count Nat.Prime 540000 = 44572 := count_step 520000 43061 1511 count_520000 (by rw [count_shift_is_prime_eq 520000 20000 (by omega)]; decide)

theorem count_560000 : count Nat.Prime 560000 = 46072 := count_step 540000 44572 1500 count_540000 (by rw [count_shift_is_prime_eq 540000 20000 (by omega)]; decide)

theorem count_580000 : count Nat.Prime 580000 = 47588 := count_step 560000 46072 1516 count_560000 (by rw [count_shift_is_prime_eq 560000 20000 (by omega)]; decide)

theorem count_600000 : count Nat.Prime 600000 = 49098 := count_step 580000 47588 1510 count_580000 (by rw [count_shift_is_prime_eq 580000 20000 (by omega)]; decide)

theorem count_620000 : count Nat.Prime 620000 = 50612 := count_step 600000 49098 1514 count_600000 (by rw [count_shift_is_prime_eq 600000 20000 (by omega)]; decide)

theorem pc_thm_351 : Nat.primeCounting 351 = 70 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 352 (by omega)]; decide

theorem pc_thm_378 : Nat.primeCounting 378 = 74 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 379 (by omega)]; decide

theorem pc_thm_1035 : Nat.primeCounting 1035 = 174 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 1036 (by omega)]; decide

theorem pc_thm_1081 : Nat.primeCounting 1081 = 180 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 1082 (by omega)]; decide

theorem pc_thm_1260 : Nat.primeCounting 1260 = 205 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 1261 (by omega)]; decide

theorem pc_thm_1332 : Nat.primeCounting 1332 = 217 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 1333 (by omega)]; decide

theorem pc_thm_1953 : Nat.primeCounting 1953 = 297 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 1954 (by omega)]; decide

theorem pc_thm_1980 : Nat.primeCounting 1980 = 299 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 1981 (by omega)]; decide

theorem pc_thm_2016 : Nat.primeCounting 2016 = 305 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 2017 (by omega)]; decide

theorem pc_thm_2070 : Nat.primeCounting 2070 = 312 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 2071 (by omega)]; decide

theorem pc_thm_2550 : Nat.primeCounting 2550 = 373 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 2551 (by omega)]; decide

theorem pc_thm_2652 : Nat.primeCounting 2652 = 383 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 2653 (by omega)]; decide

theorem pc_thm_2850 : Nat.primeCounting 2850 = 413 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 2851 (by omega)]; decide

theorem pc_thm_2926 : Nat.primeCounting 2926 = 422 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 2927 (by omega)]; decide

theorem pc_thm_3192 : Nat.primeCounting 3192 = 452 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 3193 (by omega)]; decide

theorem pc_thm_3306 : Nat.primeCounting 3306 = 464 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 3307 (by omega)]; decide

theorem pc_thm_3828 : Nat.primeCounting 3828 = 531 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 3829 (by omega)]; decide

theorem pc_thm_3906 : Nat.primeCounting 3906 = 539 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 3907 (by omega)]; decide

theorem pc_thm_3916 : Nat.primeCounting 3916 = 541 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 3917 (by omega)]; decide

theorem pc_thm_4032 : Nat.primeCounting 4032 = 557 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 4033 (by omega)]; decide

theorem pc_thm_4556 : Nat.primeCounting 4556 = 617 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 4557 (by omega)]; decide

theorem pc_thm_4692 : Nat.primeCounting 4692 = 634 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 4693 (by omega)]; decide

theorem pc_thm_4753 : Nat.primeCounting 4753 = 640 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 4754 (by omega)]; decide

theorem pc_thm_4851 : Nat.primeCounting 4851 = 650 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 4852 (by omega)]; decide

theorem pc_thm_5256 : Nat.primeCounting 5256 = 697 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 5257 (by omega)]; decide

theorem pc_thm_5402 : Nat.primeCounting 5402 = 712 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 5403 (by omega)]; decide

theorem pc_thm_5778 : Nat.primeCounting 5778 = 757 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 5779 (by omega)]; decide

theorem pc_thm_5886 : Nat.primeCounting 5886 = 775 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 5887 (by omega)]; decide

theorem pc_thm_6006 : Nat.primeCounting 6006 = 783 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 6007 (by omega)]; decide

theorem pc_thm_6162 : Nat.primeCounting 6162 = 802 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 6163 (by omega)]; decide

theorem pc_thm_6806 : Nat.primeCounting 6806 = 876 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 6807 (by omega)]; decide

theorem pc_thm_6903 : Nat.primeCounting 6903 = 887 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 6904 (by omega)]; decide

theorem pc_thm_6972 : Nat.primeCounting 6972 = 896 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 6973 (by omega)]; decide

theorem pc_thm_7021 : Nat.primeCounting 7021 = 903 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 7022 (by omega)]; decide

theorem pc_thm_7656 : Nat.primeCounting 7656 = 971 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 7657 (by omega)]; decide

theorem pc_thm_7832 : Nat.primeCounting 7832 = 990 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 7833 (by omega)]; decide

theorem pc_thm_7875 : Nat.primeCounting 7875 = 994 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 7876 (by omega)]; decide

theorem pc_thm_8001 : Nat.primeCounting 8001 = 1007 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 8002 (by omega)]; decide

theorem pc_thm_8372 : Nat.primeCounting 8372 = 1048 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 8373 (by omega)]; decide

theorem pc_thm_8556 : Nat.primeCounting 8556 = 1066 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 8557 (by omega)]; decide

theorem pc_thm_9045 : Nat.primeCounting 9045 = 1124 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 9046 (by omega)]; decide

theorem pc_thm_9120 : Nat.primeCounting 9120 = 1130 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 9121 (by omega)]; decide

theorem pc_thm_9180 : Nat.primeCounting 9180 = 1137 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 9181 (by omega)]; decide

theorem pc_thm_9312 : Nat.primeCounting 9312 = 1152 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 9313 (by omega)]; decide

theorem pc_thm_9702 : Nat.primeCounting 9702 = 1197 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 9703 (by omega)]; decide

theorem pc_thm_9900 : Nat.primeCounting 9900 = 1220 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 9901 (by omega)]; decide

theorem pc_thm_10011 : Nat.primeCounting 10011 = 1231 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 10012 (by omega)]; decide

theorem pc_thm_10153 : Nat.primeCounting 10153 = 1246 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 10154 (by omega)]; decide

theorem pc_thm_10506 : Nat.primeCounting 10506 = 1285 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 10507 (by omega)]; decide

theorem pc_thm_10712 : Nat.primeCounting 10712 = 1306 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 10713 (by omega)]; decide

theorem pc_thm_11175 : Nat.primeCounting 11175 = 1354 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 11176 (by omega)]; decide

theorem pc_thm_11325 : Nat.primeCounting 11325 = 1369 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 11326 (by omega)]; decide

theorem pc_thm_11342 : Nat.primeCounting 11342 = 1370 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 11343 (by omega)]; decide

theorem pc_thm_11556 : Nat.primeCounting 11556 = 1392 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 11557 (by omega)]; decide

theorem pc_thm_12210 : Nat.primeCounting 12210 = 1459 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 12211 (by omega)]; decide

theorem pc_thm_12403 : Nat.primeCounting 12403 = 1480 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 12404 (by omega)]; decide

theorem pc_thm_12432 : Nat.primeCounting 12432 = 1483 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 12433 (by omega)]; decide

theorem pc_thm_12561 : Nat.primeCounting 12561 = 1500 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 12562 (by omega)]; decide

theorem pc_thm_12882 : Nat.primeCounting 12882 = 1532 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 12883 (by omega)]; decide

theorem pc_thm_13110 : Nat.primeCounting 13110 = 1560 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 13111 (by omega)]; decide

theorem pc_thm_13366 : Nat.primeCounting 13366 = 1585 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 13367 (by omega)]; decide

theorem pc_thm_13530 : Nat.primeCounting 13530 = 1602 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 13531 (by omega)]; decide

theorem pc_thm_13806 : Nat.primeCounting 13806 = 1632 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 13807 (by omega)]; decide

theorem pc_thm_14042 : Nat.primeCounting 14042 = 1656 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 14043 (by omega)]; decide

theorem pc_thm_14520 : Nat.primeCounting 14520 = 1700 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 14521 (by omega)]; decide

theorem pc_thm_14535 : Nat.primeCounting 14535 = 1701 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 14536 (by omega)]; decide

theorem pc_thm_14706 : Nat.primeCounting 14706 = 1720 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 14707 (by omega)]; decide

theorem pc_thm_14762 : Nat.primeCounting 14762 = 1729 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 14763 (by omega)]; decide

theorem pc_thm_15252 : Nat.primeCounting 15252 = 1779 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 15253 (by omega)]; decide

theorem pc_thm_15500 : Nat.primeCounting 15500 = 1810 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 15501 (by omega)]; decide

theorem pc_thm_15576 : Nat.primeCounting 15576 = 1816 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 15577 (by omega)]; decide

theorem pc_thm_15753 : Nat.primeCounting 15753 = 1837 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 15754 (by omega)]; decide

theorem pc_thm_16002 : Nat.primeCounting 16002 = 1863 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 16003 (by omega)]; decide

theorem pc_thm_16256 : Nat.primeCounting 16256 = 1889 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 16257 (by omega)]; decide

theorem pc_thm_16836 : Nat.primeCounting 16836 = 1943 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 16837 (by omega)]; decide

theorem pc_thm_17020 : Nat.primeCounting 17020 = 1961 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 17021 (by omega)]; decide

theorem pc_thm_17030 : Nat.primeCounting 17030 = 1964 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 17031 (by omega)]; decide

theorem pc_thm_17292 : Nat.primeCounting 17292 = 1987 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 17293 (by omega)]; decide

theorem pc_thm_17822 : Nat.primeCounting 17822 = 2043 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 17823 (by omega)]; decide

theorem pc_thm_17955 : Nat.primeCounting 17955 = 2057 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 17956 (by omega)]; decide

theorem pc_thm_18090 : Nat.primeCounting 18090 = 2073 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 18091 (by omega)]; decide

theorem pc_thm_18145 : Nat.primeCounting 18145 = 2080 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 18146 (by omega)]; decide

theorem pc_thm_18632 : Nat.primeCounting 18632 = 2129 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 18633 (by omega)]; decide

theorem pc_thm_18906 : Nat.primeCounting 18906 = 2150 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 18907 (by omega)]; decide

theorem pc_thm_19110 : Nat.primeCounting 19110 = 2169 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 19111 (by omega)]; decide

theorem pc_thm_19306 : Nat.primeCounting 19306 = 2188 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 19307 (by omega)]; decide

theorem pc_thm_19460 : Nat.primeCounting 19460 = 2206 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 19461 (by omega)]; decide

theorem pc_thm_19740 : Nat.primeCounting 19740 = 2234 := by rw [Nat.primeCounting, count_shift_is_prime_eq 0 19741 (by omega)]; decide

theorem pc_thm_20301 : Nat.primeCounting 20301 = 2293 := primeCounting_step 20000 302 2262 31 count_20000 (by rw [count_shift_is_prime_eq 20000 302 (by omega)]; decide)

theorem pc_thm_20306 : Nat.primeCounting 20306 = 2293 := primeCounting_step 20000 307 2262 31 count_20000 (by rw [count_shift_is_prime_eq 20000 307 (by omega)]; decide)

theorem pc_thm_20503 : Nat.primeCounting 20503 = 2313 := primeCounting_step 20000 504 2262 51 count_20000 (by rw [count_shift_is_prime_eq 20000 504 (by omega)]; decide)

theorem pc_thm_20592 : Nat.primeCounting 20592 = 2321 := primeCounting_step 20000 593 2262 59 count_20000 (by rw [count_shift_is_prime_eq 20000 593 (by omega)]; decide)

theorem pc_thm_20880 : Nat.primeCounting 20880 = 2348 := primeCounting_step 20000 881 2262 86 count_20000 (by rw [count_shift_is_prime_eq 20000 881 (by omega)]; decide)

theorem pc_thm_21170 : Nat.primeCounting 21170 = 2380 := primeCounting_step 20000 1171 2262 118 count_20000 (by rw [count_shift_is_prime_eq 20000 1171 (by omega)]; decide)

theorem pc_thm_21321 : Nat.primeCounting 21321 = 2394 := primeCounting_step 20000 1322 2262 132 count_20000 (by rw [count_shift_is_prime_eq 20000 1322 (by omega)]; decide)

theorem pc_thm_21528 : Nat.primeCounting 21528 = 2416 := primeCounting_step 20000 1529 2262 154 count_20000 (by rw [count_shift_is_prime_eq 20000 1529 (by omega)]; decide)

theorem pc_thm_21756 : Nat.primeCounting 21756 = 2440 := primeCounting_step 20000 1757 2262 178 count_20000 (by rw [count_shift_is_prime_eq 20000 1757 (by omega)]; decide)

theorem pc_thm_22052 : Nat.primeCounting 22052 = 2471 := primeCounting_step 20000 2053 2262 209 count_20000 (by rw [count_shift_is_prime_eq 20000 2053 (by omega)]; decide)

theorem pc_thm_22578 : Nat.primeCounting 22578 = 2524 := primeCounting_step 20000 2579 2262 262 count_20000 (by rw [count_shift_is_prime_eq 20000 2579 (by omega)]; decide)

theorem pc_thm_22650 : Nat.primeCounting 22650 = 2530 := primeCounting_step 20000 2651 2262 268 count_20000 (by rw [count_shift_is_prime_eq 20000 2651 (by omega)]; decide)

theorem pc_thm_22791 : Nat.primeCounting 22791 = 2547 := primeCounting_step 20000 2792 2262 285 count_20000 (by rw [count_shift_is_prime_eq 20000 2792 (by omega)]; decide)

theorem pc_thm_22952 : Nat.primeCounting 22952 = 2560 := primeCounting_step 20000 2953 2262 298 count_20000 (by rw [count_shift_is_prime_eq 20000 2953 (by omega)]; decide)

theorem pc_thm_23562 : Nat.primeCounting 23562 = 2620 := primeCounting_step 20000 3563 2262 358 count_20000 (by rw [count_shift_is_prime_eq 20000 3563 (by omega)]; decide)

theorem pc_thm_23870 : Nat.primeCounting 23870 = 2654 := primeCounting_step 20000 3871 2262 392 count_20000 (by rw [count_shift_is_prime_eq 20000 3871 (by omega)]; decide)

theorem pc_thm_23871 : Nat.primeCounting 23871 = 2654 := primeCounting_step 20000 3872 2262 392 count_20000 (by rw [count_shift_is_prime_eq 20000 3872 (by omega)]; decide)

theorem pc_thm_24090 : Nat.primeCounting 24090 = 2679 := primeCounting_step 20000 4091 2262 417 count_20000 (by rw [count_shift_is_prime_eq 20000 4091 (by omega)]; decide)

theorem pc_thm_24180 : Nat.primeCounting 24180 = 2691 := primeCounting_step 20000 4181 2262 429 count_20000 (by rw [count_shift_is_prime_eq 20000 4181 (by omega)]; decide)

theorem pc_thm_24492 : Nat.primeCounting 24492 = 2717 := primeCounting_step 20000 4493 2262 455 count_20000 (by rw [count_shift_is_prime_eq 20000 4493 (by omega)]; decide)

theorem pc_thm_24976 : Nat.primeCounting 24976 = 2759 := primeCounting_step 20000 4977 2262 497 count_20000 (by rw [count_shift_is_prime_eq 20000 4977 (by omega)]; decide)

theorem pc_thm_25122 : Nat.primeCounting 25122 = 2773 := primeCounting_step 20000 5123 2262 511 count_20000 (by rw [count_shift_is_prime_eq 20000 5123 (by omega)]; decide)

theorem pc_thm_25200 : Nat.primeCounting 25200 = 2781 := primeCounting_step 20000 5201 2262 519 count_20000 (by rw [count_shift_is_prime_eq 20000 5201 (by omega)]; decide)

theorem pc_thm_25440 : Nat.primeCounting 25440 = 2804 := primeCounting_step 20000 5441 2262 542 count_20000 (by rw [count_shift_is_prime_eq 20000 5441 (by omega)]; decide)

theorem pc_thm_25760 : Nat.primeCounting 25760 = 2836 := primeCounting_step 20000 5761 2262 574 count_20000 (by rw [count_shift_is_prime_eq 20000 5761 (by omega)]; decide)

theorem pc_thm_26082 : Nat.primeCounting 26082 = 2866 := primeCounting_step 20000 6083 2262 604 count_20000 (by rw [count_shift_is_prime_eq 20000 6083 (by omega)]; decide)

theorem pc_thm_26106 : Nat.primeCounting 26106 = 2868 := primeCounting_step 20000 6107 2262 606 count_20000 (by rw [count_shift_is_prime_eq 20000 6107 (by omega)]; decide)

theorem pc_thm_26335 : Nat.primeCounting 26335 = 2893 := primeCounting_step 20000 6336 2262 631 count_20000 (by rw [count_shift_is_prime_eq 20000 6336 (by omega)]; decide)

theorem pc_thm_26732 : Nat.primeCounting 26732 = 2935 := primeCounting_step 20000 6733 2262 673 count_20000 (by rw [count_shift_is_prime_eq 20000 6733 (by omega)]; decide)

theorem pc_thm_27060 : Nat.primeCounting 27060 = 2966 := primeCounting_step 20000 7061 2262 704 count_20000 (by rw [count_shift_is_prime_eq 20000 7061 (by omega)]; decide)

theorem pc_thm_27261 : Nat.primeCounting 27261 = 2984 := primeCounting_step 20000 7262 2262 722 count_20000 (by rw [count_shift_is_prime_eq 20000 7262 (by omega)]; decide)

theorem pc_thm_27495 : Nat.primeCounting 27495 = 3004 := primeCounting_step 20000 7496 2262 742 count_20000 (by rw [count_shift_is_prime_eq 20000 7496 (by omega)]; decide)

theorem pc_thm_27722 : Nat.primeCounting 27722 = 3022 := primeCounting_step 20000 7723 2262 760 count_20000 (by rw [count_shift_is_prime_eq 20000 7723 (by omega)]; decide)

theorem pc_thm_28056 : Nat.primeCounting 28056 = 3060 := primeCounting_step 20000 8057 2262 798 count_20000 (by rw [count_shift_is_prime_eq 20000 8057 (by omega)]; decide)

theorem pc_thm_28392 : Nat.primeCounting 28392 = 3088 := primeCounting_step 20000 8393 2262 826 count_20000 (by rw [count_shift_is_prime_eq 20000 8393 (by omega)]; decide)

theorem pc_thm_28441 : Nat.primeCounting 28441 = 3095 := primeCounting_step 20000 8442 2262 833 count_20000 (by rw [count_shift_is_prime_eq 20000 8442 (by omega)]; decide)

theorem pc_thm_28680 : Nat.primeCounting 28680 = 3124 := primeCounting_step 20000 8681 2262 862 count_20000 (by rw [count_shift_is_prime_eq 20000 8681 (by omega)]; decide)

theorem pc_thm_28730 : Nat.primeCounting 28730 = 3130 := primeCounting_step 20000 8731 2262 868 count_20000 (by rw [count_shift_is_prime_eq 20000 8731 (by omega)]; decide)

theorem pc_thm_29412 : Nat.primeCounting 29412 = 3196 := primeCounting_step 20000 9413 2262 934 count_20000 (by rw [count_shift_is_prime_eq 20000 9413 (by omega)]; decide)

theorem pc_thm_29646 : Nat.primeCounting 29646 = 3217 := primeCounting_step 20000 9647 2262 955 count_20000 (by rw [count_shift_is_prime_eq 20000 9647 (by omega)]; decide)

theorem pc_thm_29756 : Nat.primeCounting 29756 = 3225 := primeCounting_step 20000 9757 2262 963 count_20000 (by rw [count_shift_is_prime_eq 20000 9757 (by omega)]; decide)

theorem pc_thm_29890 : Nat.primeCounting 29890 = 3238 := primeCounting_step 20000 9891 2262 976 count_20000 (by rw [count_shift_is_prime_eq 20000 9891 (by omega)]; decide)

theorem pc_thm_30102 : Nat.primeCounting 30102 = 3254 := primeCounting_step 20000 10103 2262 992 count_20000 (by rw [count_shift_is_prime_eq 20000 10103 (by omega)]; decide)

theorem pc_thm_30450 : Nat.primeCounting 30450 = 3288 := primeCounting_step 20000 10451 2262 1026 count_20000 (by rw [count_shift_is_prime_eq 20000 10451 (by omega)]; decide)

theorem pc_thm_30876 : Nat.primeCounting 30876 = 3330 := primeCounting_step 20000 10877 2262 1068 count_20000 (by rw [count_shift_is_prime_eq 20000 10877 (by omega)]; decide)

theorem pc_thm_31125 : Nat.primeCounting 31125 = 3352 := primeCounting_step 20000 11126 2262 1090 count_20000 (by rw [count_shift_is_prime_eq 20000 11126 (by omega)]; decide)

theorem pc_thm_31152 : Nat.primeCounting 31152 = 3355 := primeCounting_step 20000 11153 2262 1093 count_20000 (by rw [count_shift_is_prime_eq 20000 11153 (by omega)]; decide)

theorem pc_thm_31506 : Nat.primeCounting 31506 = 3389 := primeCounting_step 20000 11507 2262 1127 count_20000 (by rw [count_shift_is_prime_eq 20000 11507 (by omega)]; decide)

theorem pc_thm_31862 : Nat.primeCounting 31862 = 3423 := primeCounting_step 20000 11863 2262 1161 count_20000 (by rw [count_shift_is_prime_eq 20000 11863 (by omega)]; decide)

theorem pc_thm_32131 : Nat.primeCounting 32131 = 3447 := primeCounting_step 20000 12132 2262 1185 count_20000 (by rw [count_shift_is_prime_eq 20000 12132 (by omega)]; decide)

theorem pc_thm_32220 : Nat.primeCounting 32220 = 3456 := primeCounting_step 20000 12221 2262 1194 count_20000 (by rw [count_shift_is_prime_eq 20000 12221 (by omega)]; decide)

theorem pc_thm_32385 : Nat.primeCounting 32385 = 3476 := primeCounting_step 20000 12386 2262 1214 count_20000 (by rw [count_shift_is_prime_eq 20000 12386 (by omega)]; decide)

theorem pc_thm_32942 : Nat.primeCounting 32942 = 3531 := primeCounting_step 20000 12943 2262 1269 count_20000 (by rw [count_shift_is_prime_eq 20000 12943 (by omega)]; decide)

theorem pc_thm_33153 : Nat.primeCounting 33153 = 3553 := primeCounting_step 20000 13154 2262 1291 count_20000 (by rw [count_shift_is_prime_eq 20000 13154 (by omega)]; decide)

theorem pc_thm_33306 : Nat.primeCounting 33306 = 3565 := primeCounting_step 20000 13307 2262 1303 count_20000 (by rw [count_shift_is_prime_eq 20000 13307 (by omega)]; decide)

theorem pc_thm_33411 : Nat.primeCounting 33411 = 3578 := primeCounting_step 20000 13412 2262 1316 count_20000 (by rw [count_shift_is_prime_eq 20000 13412 (by omega)]; decide)

theorem pc_thm_33672 : Nat.primeCounting 33672 = 3607 := primeCounting_step 20000 13673 2262 1345 count_20000 (by rw [count_shift_is_prime_eq 20000 13673 (by omega)]; decide)

theorem pc_thm_34040 : Nat.primeCounting 34040 = 3642 := primeCounting_step 20000 14041 2262 1380 count_20000 (by rw [count_shift_is_prime_eq 20000 14041 (by omega)]; decide)

theorem pc_thm_34410 : Nat.primeCounting 34410 = 3676 := primeCounting_step 20000 14411 2262 1414 count_20000 (by rw [count_shift_is_prime_eq 20000 14411 (by omega)]; decide)

theorem pc_thm_34453 : Nat.primeCounting 34453 = 3679 := primeCounting_step 20000 14454 2262 1417 count_20000 (by rw [count_shift_is_prime_eq 20000 14454 (by omega)]; decide)

theorem pc_thm_34716 : Nat.primeCounting 34716 = 3707 := primeCounting_step 20000 14717 2262 1445 count_20000 (by rw [count_shift_is_prime_eq 20000 14717 (by omega)]; decide)

theorem pc_thm_34782 : Nat.primeCounting 34782 = 3715 := primeCounting_step 20000 14783 2262 1453 count_20000 (by rw [count_shift_is_prime_eq 20000 14783 (by omega)]; decide)

theorem pc_thm_35156 : Nat.primeCounting 35156 = 3749 := primeCounting_step 20000 15157 2262 1487 count_20000 (by rw [count_shift_is_prime_eq 20000 15157 (by omega)]; decide)

theorem pc_thm_35532 : Nat.primeCounting 35532 = 3783 := primeCounting_step 20000 15533 2262 1521 count_20000 (by rw [count_shift_is_prime_eq 20000 15533 (by omega)]; decide)

theorem pc_thm_35778 : Nat.primeCounting 35778 = 3801 := primeCounting_step 20000 15779 2262 1539 count_20000 (by rw [count_shift_is_prime_eq 20000 15779 (by omega)]; decide)

theorem pc_thm_36046 : Nat.primeCounting 36046 = 3829 := primeCounting_step 20000 16047 2262 1567 count_20000 (by rw [count_shift_is_prime_eq 20000 16047 (by omega)]; decide)

theorem pc_thm_36290 : Nat.primeCounting 36290 = 3850 := primeCounting_step 20000 16291 2262 1588 count_20000 (by rw [count_shift_is_prime_eq 20000 16291 (by omega)]; decide)

theorem pc_thm_36672 : Nat.primeCounting 36672 = 3887 := primeCounting_step 20000 16673 2262 1625 count_20000 (by rw [count_shift_is_prime_eq 20000 16673 (by omega)]; decide)

theorem pc_thm_36856 : Nat.primeCounting 36856 = 3907 := primeCounting_step 20000 16857 2262 1645 count_20000 (by rw [count_shift_is_prime_eq 20000 16857 (by omega)]; decide)

theorem pc_thm_37056 : Nat.primeCounting 37056 = 3929 := primeCounting_step 20000 17057 2262 1667 count_20000 (by rw [count_shift_is_prime_eq 20000 17057 (by omega)]; decide)

theorem pc_thm_37128 : Nat.primeCounting 37128 = 3935 := primeCounting_step 20000 17129 2262 1673 count_20000 (by rw [count_shift_is_prime_eq 20000 17129 (by omega)]; decide)

theorem pc_thm_37442 : Nat.primeCounting 37442 = 3963 := primeCounting_step 20000 17443 2262 1701 count_20000 (by rw [count_shift_is_prime_eq 20000 17443 (by omega)]; decide)

theorem pc_thm_37830 : Nat.primeCounting 37830 = 4000 := primeCounting_step 20000 17831 2262 1738 count_20000 (by rw [count_shift_is_prime_eq 20000 17831 (by omega)]; decide)

theorem pc_thm_38220 : Nat.primeCounting 38220 = 4034 := primeCounting_step 20000 18221 2262 1772 count_20000 (by rw [count_shift_is_prime_eq 20000 18221 (by omega)]; decide)

theorem pc_thm_38226 : Nat.primeCounting 38226 = 4034 := primeCounting_step 20000 18227 2262 1772 count_20000 (by rw [count_shift_is_prime_eq 20000 18227 (by omega)]; decide)

theorem pc_thm_38503 : Nat.primeCounting 38503 = 4059 := primeCounting_step 20000 18504 2262 1797 count_20000 (by rw [count_shift_is_prime_eq 20000 18504 (by omega)]; decide)

theorem pc_thm_38612 : Nat.primeCounting 38612 = 4068 := primeCounting_step 20000 18613 2262 1806 count_20000 (by rw [count_shift_is_prime_eq 20000 18613 (by omega)]; decide)

theorem pc_thm_39006 : Nat.primeCounting 39006 = 4107 := primeCounting_step 20000 19007 2262 1845 count_20000 (by rw [count_shift_is_prime_eq 20000 19007 (by omega)]; decide)

theorem pc_thm_39340 : Nat.primeCounting 39340 = 4140 := primeCounting_step 20000 19341 2262 1878 count_20000 (by rw [count_shift_is_prime_eq 20000 19341 (by omega)]; decide)

theorem pc_thm_39621 : Nat.primeCounting 39621 = 4166 := primeCounting_step 20000 19622 2262 1904 count_20000 (by rw [count_shift_is_prime_eq 20000 19622 (by omega)]; decide)

theorem pc_thm_39800 : Nat.primeCounting 39800 = 4183 := primeCounting_step 20000 19801 2262 1921 count_20000 (by rw [count_shift_is_prime_eq 20000 19801 (by omega)]; decide)

theorem pc_thm_40200 : Nat.primeCounting 40200 = 4223 := primeCounting_step 40000 201 4203 20 count_40000 (by rw [count_shift_is_prime_eq 40000 201 (by omega)]; decide)

theorem pc_thm_40602 : Nat.primeCounting 40602 = 4256 := primeCounting_step 40000 603 4203 53 count_40000 (by rw [count_shift_is_prime_eq 40000 603 (by omega)]; decide)

theorem pc_thm_40755 : Nat.primeCounting 40755 = 4266 := primeCounting_step 40000 756 4203 63 count_40000 (by rw [count_shift_is_prime_eq 40000 756 (by omega)]; decide)

theorem pc_thm_41006 : Nat.primeCounting 41006 = 4291 := primeCounting_step 40000 1007 4203 88 count_40000 (by rw [count_shift_is_prime_eq 40000 1007 (by omega)]; decide)

theorem pc_thm_41041 : Nat.primeCounting 41041 = 4295 := primeCounting_step 40000 1042 4203 92 count_40000 (by rw [count_shift_is_prime_eq 40000 1042 (by omega)]; decide)

theorem pc_thm_41412 : Nat.primeCounting 41412 = 4333 := primeCounting_step 40000 1413 4203 130 count_40000 (by rw [count_shift_is_prime_eq 40000 1413 (by omega)]; decide)

theorem pc_thm_41820 : Nat.primeCounting 41820 = 4372 := primeCounting_step 40000 1821 4203 169 count_40000 (by rw [count_shift_is_prime_eq 40000 1821 (by omega)]; decide)

theorem pc_thm_41905 : Nat.primeCounting 41905 = 4381 := primeCounting_step 40000 1906 4203 178 count_40000 (by rw [count_shift_is_prime_eq 40000 1906 (by omega)]; decide)

theorem pc_thm_42195 : Nat.primeCounting 42195 = 4411 := primeCounting_step 40000 2196 4203 208 count_40000 (by rw [count_shift_is_prime_eq 40000 2196 (by omega)]; decide)

theorem pc_thm_42230 : Nat.primeCounting 42230 = 4416 := primeCounting_step 40000 2231 4203 213 count_40000 (by rw [count_shift_is_prime_eq 40000 2231 (by omega)]; decide)

theorem pc_thm_42642 : Nat.primeCounting 42642 = 4456 := primeCounting_step 40000 2643 4203 253 count_40000 (by rw [count_shift_is_prime_eq 40000 2643 (by omega)]; decide)

theorem pc_thm_43056 : Nat.primeCounting 43056 = 4500 := primeCounting_step 40000 3057 4203 297 count_40000 (by rw [count_shift_is_prime_eq 40000 3057 (by omega)]; decide)

theorem pc_thm_43071 : Nat.primeCounting 43071 = 4502 := primeCounting_step 40000 3072 4203 299 count_40000 (by rw [count_shift_is_prime_eq 40000 3072 (by omega)]; decide)

theorem pc_thm_43365 : Nat.primeCounting 43365 = 4522 := primeCounting_step 40000 3366 4203 319 count_40000 (by rw [count_shift_is_prime_eq 40000 3366 (by omega)]; decide)

theorem pc_thm_43472 : Nat.primeCounting 43472 = 4531 := primeCounting_step 40000 3473 4203 328 count_40000 (by rw [count_shift_is_prime_eq 40000 3473 (by omega)]; decide)

theorem pc_thm_43890 : Nat.primeCounting 43890 = 4567 := primeCounting_step 40000 3891 4203 364 count_40000 (by rw [count_shift_is_prime_eq 40000 3891 (by omega)]; decide)

theorem pc_thm_44253 : Nat.primeCounting 44253 = 4604 := primeCounting_step 40000 4254 4203 401 count_40000 (by rw [count_shift_is_prime_eq 40000 4254 (by omega)]; decide)

theorem pc_thm_44310 : Nat.primeCounting 44310 = 4612 := primeCounting_step 40000 4311 4203 409 count_40000 (by rw [count_shift_is_prime_eq 40000 4311 (by omega)]; decide)

theorem pc_thm_44551 : Nat.primeCounting 44551 = 4632 := primeCounting_step 40000 4552 4203 429 count_40000 (by rw [count_shift_is_prime_eq 40000 4552 (by omega)]; decide)

theorem pc_thm_44732 : Nat.primeCounting 44732 = 4649 := primeCounting_step 40000 4733 4203 446 count_40000 (by rw [count_shift_is_prime_eq 40000 4733 (by omega)]; decide)

theorem pc_thm_45156 : Nat.primeCounting 45156 = 4687 := primeCounting_step 40000 5157 4203 484 count_40000 (by rw [count_shift_is_prime_eq 40000 5157 (by omega)]; decide)

theorem pc_thm_45451 : Nat.primeCounting 45451 = 4714 := primeCounting_step 40000 5452 4203 511 count_40000 (by rw [count_shift_is_prime_eq 40000 5452 (by omega)]; decide)

theorem pc_thm_45582 : Nat.primeCounting 45582 = 4724 := primeCounting_step 40000 5583 4203 521 count_40000 (by rw [count_shift_is_prime_eq 40000 5583 (by omega)]; decide)

theorem pc_thm_45753 : Nat.primeCounting 45753 = 4739 := primeCounting_step 40000 5754 4203 536 count_40000 (by rw [count_shift_is_prime_eq 40000 5754 (by omega)]; decide)

theorem pc_thm_46010 : Nat.primeCounting 46010 = 4761 := primeCounting_step 40000 6011 4203 558 count_40000 (by rw [count_shift_is_prime_eq 40000 6011 (by omega)]; decide)

theorem pc_thm_46440 : Nat.primeCounting 46440 = 4798 := primeCounting_step 40000 6441 4203 595 count_40000 (by rw [count_shift_is_prime_eq 40000 6441 (by omega)]; decide)

theorem pc_thm_46665 : Nat.primeCounting 46665 = 4822 := primeCounting_step 40000 6666 4203 619 count_40000 (by rw [count_shift_is_prime_eq 40000 6666 (by omega)]; decide)

theorem pc_thm_46872 : Nat.primeCounting 46872 = 4843 := primeCounting_step 40000 6873 4203 640 count_40000 (by rw [count_shift_is_prime_eq 40000 6873 (by omega)]; decide)

theorem pc_thm_46971 : Nat.primeCounting 46971 = 4849 := primeCounting_step 40000 6972 4203 646 count_40000 (by rw [count_shift_is_prime_eq 40000 6972 (by omega)]; decide)

theorem pc_thm_47306 : Nat.primeCounting 47306 = 4878 := primeCounting_step 40000 7307 4203 675 count_40000 (by rw [count_shift_is_prime_eq 40000 7307 (by omega)]; decide)

theorem pc_thm_47742 : Nat.primeCounting 47742 = 4922 := primeCounting_step 40000 7743 4203 719 count_40000 (by rw [count_shift_is_prime_eq 40000 7743 (by omega)]; decide)

theorem pc_thm_47895 : Nat.primeCounting 47895 = 4935 := primeCounting_step 40000 7896 4203 732 count_40000 (by rw [count_shift_is_prime_eq 40000 7896 (by omega)]; decide)

theorem pc_thm_48180 : Nat.primeCounting 48180 = 4960 := primeCounting_step 40000 8181 4203 757 count_40000 (by rw [count_shift_is_prime_eq 40000 8181 (by omega)]; decide)

theorem pc_thm_48205 : Nat.primeCounting 48205 = 4963 := primeCounting_step 40000 8206 4203 760 count_40000 (by rw [count_shift_is_prime_eq 40000 8206 (by omega)]; decide)

theorem pc_thm_48620 : Nat.primeCounting 48620 = 5001 := primeCounting_step 40000 8621 4203 798 count_40000 (by rw [count_shift_is_prime_eq 40000 8621 (by omega)]; decide)

theorem pc_thm_49062 : Nat.primeCounting 49062 = 5043 := primeCounting_step 40000 9063 4203 840 count_40000 (by rw [count_shift_is_prime_eq 40000 9063 (by omega)]; decide)

theorem pc_thm_49141 : Nat.primeCounting 49141 = 5051 := primeCounting_step 40000 9142 4203 848 count_40000 (by rw [count_shift_is_prime_eq 40000 9142 (by omega)]; decide)

theorem pc_thm_49455 : Nat.primeCounting 49455 = 5081 := primeCounting_step 40000 9456 4203 878 count_40000 (by rw [count_shift_is_prime_eq 40000 9456 (by omega)]; decide)

theorem pc_thm_49506 : Nat.primeCounting 49506 = 5086 := primeCounting_step 40000 9507 4203 883 count_40000 (by rw [count_shift_is_prime_eq 40000 9507 (by omega)]; decide)

theorem pc_thm_49952 : Nat.primeCounting 49952 = 5129 := primeCounting_step 40000 9953 4203 926 count_40000 (by rw [count_shift_is_prime_eq 40000 9953 (by omega)]; decide)

theorem pc_thm_50400 : Nat.primeCounting 50400 = 5172 := primeCounting_step 40000 10401 4203 969 count_40000 (by rw [count_shift_is_prime_eq 40000 10401 (by omega)]; decide)

theorem pc_thm_50403 : Nat.primeCounting 50403 = 5172 := primeCounting_step 40000 10404 4203 969 count_40000 (by rw [count_shift_is_prime_eq 40000 10404 (by omega)]; decide)

theorem pc_thm_50721 : Nat.primeCounting 50721 = 5197 := primeCounting_step 40000 10722 4203 994 count_40000 (by rw [count_shift_is_prime_eq 40000 10722 (by omega)]; decide)

theorem pc_thm_50850 : Nat.primeCounting 50850 = 5208 := primeCounting_step 40000 10851 4203 1005 count_40000 (by rw [count_shift_is_prime_eq 40000 10851 (by omega)]; decide)

theorem pc_thm_51302 : Nat.primeCounting 51302 = 5248 := primeCounting_step 40000 11303 4203 1045 count_40000 (by rw [count_shift_is_prime_eq 40000 11303 (by omega)]; decide)

theorem pc_thm_51360 : Nat.primeCounting 51360 = 5254 := primeCounting_step 40000 11361 4203 1051 count_40000 (by rw [count_shift_is_prime_eq 40000 11361 (by omega)]; decide)

theorem pc_thm_51681 : Nat.primeCounting 51681 = 5289 := primeCounting_step 40000 11682 4203 1086 count_40000 (by rw [count_shift_is_prime_eq 40000 11682 (by omega)]; decide)

theorem pc_thm_51756 : Nat.primeCounting 51756 = 5295 := primeCounting_step 40000 11757 4203 1092 count_40000 (by rw [count_shift_is_prime_eq 40000 11757 (by omega)]; decide)

theorem pc_thm_52212 : Nat.primeCounting 52212 = 5338 := primeCounting_step 40000 12213 4203 1135 count_40000 (by rw [count_shift_is_prime_eq 40000 12213 (by omega)]; decide)

theorem pc_thm_52650 : Nat.primeCounting 52650 = 5375 := primeCounting_step 40000 12651 4203 1172 count_40000 (by rw [count_shift_is_prime_eq 40000 12651 (by omega)]; decide)

theorem pc_thm_52670 : Nat.primeCounting 52670 = 5376 := primeCounting_step 40000 12671 4203 1173 count_40000 (by rw [count_shift_is_prime_eq 40000 12671 (by omega)]; decide)

theorem pc_thm_52975 : Nat.primeCounting 52975 = 5406 := primeCounting_step 40000 12976 4203 1203 count_40000 (by rw [count_shift_is_prime_eq 40000 12976 (by omega)]; decide)

theorem pc_thm_53130 : Nat.primeCounting 53130 = 5421 := primeCounting_step 40000 13131 4203 1218 count_40000 (by rw [count_shift_is_prime_eq 40000 13131 (by omega)]; decide)

theorem pc_thm_53592 : Nat.primeCounting 53592 = 5459 := primeCounting_step 40000 13593 4203 1256 count_40000 (by rw [count_shift_is_prime_eq 40000 13593 (by omega)]; decide)

theorem pc_thm_53956 : Nat.primeCounting 53956 = 5497 := primeCounting_step 40000 13957 4203 1294 count_40000 (by rw [count_shift_is_prime_eq 40000 13957 (by omega)]; decide)

theorem pc_thm_54056 : Nat.primeCounting 54056 = 5505 := primeCounting_step 40000 14057 4203 1302 count_40000 (by rw [count_shift_is_prime_eq 40000 14057 (by omega)]; decide)

theorem pc_thm_54285 : Nat.primeCounting 54285 = 5521 := primeCounting_step 40000 14286 4203 1318 count_40000 (by rw [count_shift_is_prime_eq 40000 14286 (by omega)]; decide)

theorem pc_thm_54522 : Nat.primeCounting 54522 = 5548 := primeCounting_step 40000 14523 4203 1345 count_40000 (by rw [count_shift_is_prime_eq 40000 14523 (by omega)]; decide)

theorem pc_thm_54990 : Nat.primeCounting 54990 = 5590 := primeCounting_step 40000 14991 4203 1387 count_40000 (by rw [count_shift_is_prime_eq 40000 14991 (by omega)]; decide)

theorem pc_thm_55278 : Nat.primeCounting 55278 = 5615 := primeCounting_step 40000 15279 4203 1412 count_40000 (by rw [count_shift_is_prime_eq 40000 15279 (by omega)]; decide)

theorem pc_thm_55460 : Nat.primeCounting 55460 = 5630 := primeCounting_step 40000 15461 4203 1427 count_40000 (by rw [count_shift_is_prime_eq 40000 15461 (by omega)]; decide)

theorem pc_thm_55611 : Nat.primeCounting 55611 = 5641 := primeCounting_step 40000 15612 4203 1438 count_40000 (by rw [count_shift_is_prime_eq 40000 15612 (by omega)]; decide)

theorem pc_thm_55932 : Nat.primeCounting 55932 = 5678 := primeCounting_step 40000 15933 4203 1475 count_40000 (by rw [count_shift_is_prime_eq 40000 15933 (by omega)]; decide)

theorem pc_thm_56280 : Nat.primeCounting 56280 = 5709 := primeCounting_step 40000 16281 4203 1506 count_40000 (by rw [count_shift_is_prime_eq 40000 16281 (by omega)]; decide)

theorem pc_thm_56406 : Nat.primeCounting 56406 = 5718 := primeCounting_step 40000 16407 4203 1515 count_40000 (by rw [count_shift_is_prime_eq 40000 16407 (by omega)]; decide)

theorem pc_thm_56616 : Nat.primeCounting 56616 = 5741 := primeCounting_step 40000 16617 4203 1538 count_40000 (by rw [count_shift_is_prime_eq 40000 16617 (by omega)]; decide)

theorem pc_thm_56882 : Nat.primeCounting 56882 = 5766 := primeCounting_step 40000 16883 4203 1563 count_40000 (by rw [count_shift_is_prime_eq 40000 16883 (by omega)]; decide)

theorem pc_thm_57360 : Nat.primeCounting 57360 = 5816 := primeCounting_step 40000 17361 4203 1613 count_40000 (by rw [count_shift_is_prime_eq 40000 17361 (by omega)]; decide)

theorem pc_thm_57630 : Nat.primeCounting 57630 = 5836 := primeCounting_step 40000 17631 4203 1633 count_40000 (by rw [count_shift_is_prime_eq 40000 17631 (by omega)]; decide)

theorem pc_thm_57840 : Nat.primeCounting 57840 = 5860 := primeCounting_step 40000 17841 4203 1657 count_40000 (by rw [count_shift_is_prime_eq 40000 17841 (by omega)]; decide)

theorem pc_thm_57970 : Nat.primeCounting 57970 = 5870 := primeCounting_step 40000 17971 4203 1667 count_40000 (by rw [count_shift_is_prime_eq 40000 17971 (by omega)]; decide)

theorem pc_thm_58322 : Nat.primeCounting 58322 = 5905 := primeCounting_step 40000 18323 4203 1702 count_40000 (by rw [count_shift_is_prime_eq 40000 18323 (by omega)]; decide)

theorem pc_thm_58806 : Nat.primeCounting 58806 = 5948 := primeCounting_step 40000 18807 4203 1745 count_40000 (by rw [count_shift_is_prime_eq 40000 18807 (by omega)]; decide)

theorem pc_thm_58996 : Nat.primeCounting 58996 = 5962 := primeCounting_step 40000 18997 4203 1759 count_40000 (by rw [count_shift_is_prime_eq 40000 18997 (by omega)]; decide)

theorem pc_thm_59292 : Nat.primeCounting 59292 = 5995 := primeCounting_step 40000 19293 4203 1792 count_40000 (by rw [count_shift_is_prime_eq 40000 19293 (by omega)]; decide)

theorem pc_thm_59340 : Nat.primeCounting 59340 = 5996 := primeCounting_step 40000 19341 4203 1793 count_40000 (by rw [count_shift_is_prime_eq 40000 19341 (by omega)]; decide)

theorem pc_thm_59780 : Nat.primeCounting 59780 = 6043 := primeCounting_step 40000 19781 4203 1840 count_40000 (by rw [count_shift_is_prime_eq 40000 19781 (by omega)]; decide)

theorem pc_thm_60031 : Nat.primeCounting 60031 = 6060 := primeCounting_step 60000 32 6057 3 count_60000 (by rw [count_shift_is_prime_eq 60000 32 (by omega)]; decide)

theorem pc_thm_60270 : Nat.primeCounting 60270 = 6082 := primeCounting_step 60000 271 6057 25 count_60000 (by rw [count_shift_is_prime_eq 60000 271 (by omega)]; decide)

theorem pc_thm_60378 : Nat.primeCounting 60378 = 6091 := primeCounting_step 60000 379 6057 34 count_60000 (by rw [count_shift_is_prime_eq 60000 379 (by omega)]; decide)

theorem pc_thm_60762 : Nat.primeCounting 60762 = 6125 := primeCounting_step 60000 763 6057 68 count_60000 (by rw [count_shift_is_prime_eq 60000 763 (by omega)]; decide)

theorem pc_thm_61256 : Nat.primeCounting 61256 = 6164 := primeCounting_step 60000 1257 6057 107 count_60000 (by rw [count_shift_is_prime_eq 60000 1257 (by omega)]; decide)

theorem pc_thm_61425 : Nat.primeCounting 61425 = 6179 := primeCounting_step 60000 1426 6057 122 count_60000 (by rw [count_shift_is_prime_eq 60000 1426 (by omega)]; decide)

theorem pc_thm_61752 : Nat.primeCounting 61752 = 6213 := primeCounting_step 60000 1753 6057 156 count_60000 (by rw [count_shift_is_prime_eq 60000 1753 (by omega)]; decide)

theorem pc_thm_61776 : Nat.primeCounting 61776 = 6214 := primeCounting_step 60000 1777 6057 157 count_60000 (by rw [count_shift_is_prime_eq 60000 1777 (by omega)]; decide)

theorem pc_thm_62250 : Nat.primeCounting 62250 = 6256 := primeCounting_step 60000 2251 6057 199 count_60000 (by rw [count_shift_is_prime_eq 60000 2251 (by omega)]; decide)

theorem pc_thm_62481 : Nat.primeCounting 62481 = 6273 := primeCounting_step 60000 2482 6057 216 count_60000 (by rw [count_shift_is_prime_eq 60000 2482 (by omega)]; decide)

theorem pc_thm_62750 : Nat.primeCounting 62750 = 6297 := primeCounting_step 60000 2751 6057 240 count_60000 (by rw [count_shift_is_prime_eq 60000 2751 (by omega)]; decide)

theorem pc_thm_62835 : Nat.primeCounting 62835 = 6304 := primeCounting_step 60000 2836 6057 247 count_60000 (by rw [count_shift_is_prime_eq 60000 2836 (by omega)]; decide)

theorem pc_thm_63252 : Nat.primeCounting 63252 = 6338 := primeCounting_step 60000 3253 6057 281 count_60000 (by rw [count_shift_is_prime_eq 60000 3253 (by omega)]; decide)

theorem pc_thm_63546 : Nat.primeCounting 63546 = 6369 := primeCounting_step 60000 3547 6057 312 count_60000 (by rw [count_shift_is_prime_eq 60000 3547 (by omega)]; decide)

theorem pc_thm_63756 : Nat.primeCounting 63756 = 6393 := primeCounting_step 60000 3757 6057 336 count_60000 (by rw [count_shift_is_prime_eq 60000 3757 (by omega)]; decide)

theorem pc_thm_63903 : Nat.primeCounting 63903 = 6407 := primeCounting_step 60000 3904 6057 350 count_60000 (by rw [count_shift_is_prime_eq 60000 3904 (by omega)]; decide)

theorem pc_thm_64262 : Nat.primeCounting 64262 = 6434 := primeCounting_step 60000 4263 6057 377 count_60000 (by rw [count_shift_is_prime_eq 60000 4263 (by omega)]; decide)

theorem pc_thm_64770 : Nat.primeCounting 64770 = 6474 := primeCounting_step 60000 4771 6057 417 count_60000 (by rw [count_shift_is_prime_eq 60000 4771 (by omega)]; decide)

theorem pc_thm_64980 : Nat.primeCounting 64980 = 6492 := primeCounting_step 60000 4981 6057 435 count_60000 (by rw [count_shift_is_prime_eq 60000 4981 (by omega)]; decide)

theorem pc_thm_65280 : Nat.primeCounting 65280 = 6521 := primeCounting_step 60000 5281 6057 464 count_60000 (by rw [count_shift_is_prime_eq 60000 5281 (by omega)]; decide)

theorem pc_thm_65341 : Nat.primeCounting 65341 = 6526 := primeCounting_step 60000 5342 6057 469 count_60000 (by rw [count_shift_is_prime_eq 60000 5342 (by omega)]; decide)

theorem pc_thm_65792 : Nat.primeCounting 65792 = 6572 := primeCounting_step 60000 5793 6057 515 count_60000 (by rw [count_shift_is_prime_eq 60000 5793 (by omega)]; decide)

theorem pc_thm_66066 : Nat.primeCounting 66066 = 6595 := primeCounting_step 60000 6067 6057 538 count_60000 (by rw [count_shift_is_prime_eq 60000 6067 (by omega)]; decide)

theorem pc_thm_66306 : Nat.primeCounting 66306 = 6613 := primeCounting_step 60000 6307 6057 556 count_60000 (by rw [count_shift_is_prime_eq 60000 6307 (by omega)]; decide)

theorem pc_thm_66430 : Nat.primeCounting 66430 = 6623 := primeCounting_step 60000 6431 6057 566 count_60000 (by rw [count_shift_is_prime_eq 60000 6431 (by omega)]; decide)

theorem pc_thm_66822 : Nat.primeCounting 66822 = 6659 := primeCounting_step 60000 6823 6057 602 count_60000 (by rw [count_shift_is_prime_eq 60000 6823 (by omega)]; decide)

theorem pc_thm_67340 : Nat.primeCounting 67340 = 6707 := primeCounting_step 60000 7341 6057 650 count_60000 (by rw [count_shift_is_prime_eq 60000 7341 (by omega)]; decide)

theorem pc_thm_67528 : Nat.primeCounting 67528 = 6727 := primeCounting_step 60000 7529 6057 670 count_60000 (by rw [count_shift_is_prime_eq 60000 7529 (by omega)]; decide)

theorem pc_thm_67860 : Nat.primeCounting 67860 = 6759 := primeCounting_step 60000 7861 6057 702 count_60000 (by rw [count_shift_is_prime_eq 60000 7861 (by omega)]; decide)

theorem pc_thm_67896 : Nat.primeCounting 67896 = 6762 := primeCounting_step 60000 7897 6057 705 count_60000 (by rw [count_shift_is_prime_eq 60000 7897 (by omega)]; decide)

theorem pc_thm_68382 : Nat.primeCounting 68382 = 6800 := primeCounting_step 60000 8383 6057 743 count_60000 (by rw [count_shift_is_prime_eq 60000 8383 (by omega)]; decide)

theorem pc_thm_68635 : Nat.primeCounting 68635 = 6822 := primeCounting_step 60000 8636 6057 765 count_60000 (by rw [count_shift_is_prime_eq 60000 8636 (by omega)]; decide)

theorem pc_thm_68906 : Nat.primeCounting 68906 = 6848 := primeCounting_step 60000 8907 6057 791 count_60000 (by rw [count_shift_is_prime_eq 60000 8907 (by omega)]; decide)

theorem pc_thm_69006 : Nat.primeCounting 69006 = 6855 := primeCounting_step 60000 9007 6057 798 count_60000 (by rw [count_shift_is_prime_eq 60000 9007 (by omega)]; decide)

theorem pc_thm_69432 : Nat.primeCounting 69432 = 6892 := primeCounting_step 60000 9433 6057 835 count_60000 (by rw [count_shift_is_prime_eq 60000 9433 (by omega)]; decide)

theorem pc_thm_69960 : Nat.primeCounting 69960 = 6933 := primeCounting_step 60000 9961 6057 876 count_60000 (by rw [count_shift_is_prime_eq 60000 9961 (by omega)]; decide)

theorem pc_thm_70125 : Nat.primeCounting 70125 = 6949 := primeCounting_step 60000 10126 6057 892 count_60000 (by rw [count_shift_is_prime_eq 60000 10126 (by omega)]; decide)

theorem pc_thm_70490 : Nat.primeCounting 70490 = 6985 := primeCounting_step 60000 10491 6057 928 count_60000 (by rw [count_shift_is_prime_eq 60000 10491 (by omega)]; decide)

theorem pc_thm_70500 : Nat.primeCounting 70500 = 6985 := primeCounting_step 60000 10501 6057 928 count_60000 (by rw [count_shift_is_prime_eq 60000 10501 (by omega)]; decide)

theorem pc_thm_71022 : Nat.primeCounting 71022 = 7034 := primeCounting_step 60000 11023 6057 977 count_60000 (by rw [count_shift_is_prime_eq 60000 11023 (by omega)]; decide)

theorem pc_thm_71253 : Nat.primeCounting 71253 = 7053 := primeCounting_step 60000 11254 6057 996 count_60000 (by rw [count_shift_is_prime_eq 60000 11254 (by omega)]; decide)

theorem pc_thm_71556 : Nat.primeCounting 71556 = 7087 := primeCounting_step 60000 11557 6057 1030 count_60000 (by rw [count_shift_is_prime_eq 60000 11557 (by omega)]; decide)

theorem pc_thm_71631 : Nat.primeCounting 71631 = 7091 := primeCounting_step 60000 11632 6057 1034 count_60000 (by rw [count_shift_is_prime_eq 60000 11632 (by omega)]; decide)

theorem pc_thm_72092 : Nat.primeCounting 72092 = 7137 := primeCounting_step 60000 12093 6057 1080 count_60000 (by rw [count_shift_is_prime_eq 60000 12093 (by omega)]; decide)

theorem pc_thm_72390 : Nat.primeCounting 72390 = 7164 := primeCounting_step 60000 12391 6057 1107 count_60000 (by rw [count_shift_is_prime_eq 60000 12391 (by omega)]; decide)

theorem pc_thm_72630 : Nat.primeCounting 72630 = 7181 := primeCounting_step 60000 12631 6057 1124 count_60000 (by rw [count_shift_is_prime_eq 60000 12631 (by omega)]; decide)

theorem pc_thm_72771 : Nat.primeCounting 72771 = 7197 := primeCounting_step 60000 12772 6057 1140 count_60000 (by rw [count_shift_is_prime_eq 60000 12772 (by omega)]; decide)

theorem pc_thm_73170 : Nat.primeCounting 73170 = 7232 := primeCounting_step 60000 13171 6057 1175 count_60000 (by rw [count_shift_is_prime_eq 60000 13171 (by omega)]; decide)

theorem pc_thm_73536 : Nat.primeCounting 73536 = 7260 := primeCounting_step 60000 13537 6057 1203 count_60000 (by rw [count_shift_is_prime_eq 60000 13537 (by omega)]; decide)

theorem pc_thm_73712 : Nat.primeCounting 73712 = 7279 := primeCounting_step 60000 13713 6057 1222 count_60000 (by rw [count_shift_is_prime_eq 60000 13713 (by omega)]; decide)

theorem pc_thm_73920 : Nat.primeCounting 73920 = 7295 := primeCounting_step 60000 13921 6057 1238 count_60000 (by rw [count_shift_is_prime_eq 60000 13921 (by omega)]; decide)

theorem pc_thm_74256 : Nat.primeCounting 74256 = 7325 := primeCounting_step 60000 14257 6057 1268 count_60000 (by rw [count_shift_is_prime_eq 60000 14257 (by omega)]; decide)

theorem pc_thm_74691 : Nat.primeCounting 74691 = 7363 := primeCounting_step 60000 14692 6057 1306 count_60000 (by rw [count_shift_is_prime_eq 60000 14692 (by omega)]; decide)

theorem pc_thm_74802 : Nat.primeCounting 74802 = 7376 := primeCounting_step 60000 14803 6057 1319 count_60000 (by rw [count_shift_is_prime_eq 60000 14803 (by omega)]; decide)

theorem pc_thm_75078 : Nat.primeCounting 75078 = 7399 := primeCounting_step 60000 15079 6057 1342 count_60000 (by rw [count_shift_is_prime_eq 60000 15079 (by omega)]; decide)

theorem pc_thm_75350 : Nat.primeCounting 75350 = 7424 := primeCounting_step 60000 15351 6057 1367 count_60000 (by rw [count_shift_is_prime_eq 60000 15351 (by omega)]; decide)

theorem pc_thm_75855 : Nat.primeCounting 75855 = 7472 := primeCounting_step 60000 15856 6057 1415 count_60000 (by rw [count_shift_is_prime_eq 60000 15856 (by omega)]; decide)

theorem pc_thm_75900 : Nat.primeCounting 75900 = 7474 := primeCounting_step 60000 15901 6057 1417 count_60000 (by rw [count_shift_is_prime_eq 60000 15901 (by omega)]; decide)

theorem pc_thm_76245 : Nat.primeCounting 76245 = 7503 := primeCounting_step 60000 16246 6057 1446 count_60000 (by rw [count_shift_is_prime_eq 60000 16246 (by omega)]; decide)

theorem pc_thm_76452 : Nat.primeCounting 76452 = 7520 := primeCounting_step 60000 16453 6057 1463 count_60000 (by rw [count_shift_is_prime_eq 60000 16453 (by omega)]; decide)

theorem pc_thm_77006 : Nat.primeCounting 77006 = 7568 := primeCounting_step 60000 17007 6057 1511 count_60000 (by rw [count_shift_is_prime_eq 60000 17007 (by omega)]; decide)

theorem pc_thm_77421 : Nat.primeCounting 77421 = 7606 := primeCounting_step 60000 17422 6057 1549 count_60000 (by rw [count_shift_is_prime_eq 60000 17422 (by omega)]; decide)

theorem pc_thm_77562 : Nat.primeCounting 77562 = 7621 := primeCounting_step 60000 17563 6057 1564 count_60000 (by rw [count_shift_is_prime_eq 60000 17563 (by omega)]; decide)

theorem pc_thm_77815 : Nat.primeCounting 77815 = 7649 := primeCounting_step 60000 17816 6057 1592 count_60000 (by rw [count_shift_is_prime_eq 60000 17816 (by omega)]; decide)

theorem pc_thm_78120 : Nat.primeCounting 78120 = 7670 := primeCounting_step 60000 18121 6057 1613 count_60000 (by rw [count_shift_is_prime_eq 60000 18121 (by omega)]; decide)

theorem pc_thm_78606 : Nat.primeCounting 78606 = 7713 := primeCounting_step 60000 18607 6057 1656 count_60000 (by rw [count_shift_is_prime_eq 60000 18607 (by omega)]; decide)

theorem pc_thm_78680 : Nat.primeCounting 78680 = 7718 := primeCounting_step 60000 18681 6057 1661 count_60000 (by rw [count_shift_is_prime_eq 60000 18681 (by omega)]; decide)

theorem pc_thm_79003 : Nat.primeCounting 79003 = 7746 := primeCounting_step 60000 19004 6057 1689 count_60000 (by rw [count_shift_is_prime_eq 60000 19004 (by omega)]; decide)

theorem pc_thm_79242 : Nat.primeCounting 79242 = 7766 := primeCounting_step 60000 19243 6057 1709 count_60000 (by rw [count_shift_is_prime_eq 60000 19243 (by omega)]; decide)

theorem pc_thm_79800 : Nat.primeCounting 79800 = 7813 := primeCounting_step 60000 19801 6057 1756 count_60000 (by rw [count_shift_is_prime_eq 60000 19801 (by omega)]; decide)

theorem pc_thm_79806 : Nat.primeCounting 79806 = 7814 := primeCounting_step 60000 19807 6057 1757 count_60000 (by rw [count_shift_is_prime_eq 60000 19807 (by omega)]; decide)

theorem pc_thm_80200 : Nat.primeCounting 80200 = 7852 := primeCounting_step 80000 201 7837 15 count_80000 (by rw [count_shift_is_prime_eq 80000 201 (by omega)]; decide)

theorem pc_thm_80372 : Nat.primeCounting 80372 = 7870 := primeCounting_step 80000 373 7837 33 count_80000 (by rw [count_shift_is_prime_eq 80000 373 (by omega)]; decide)

theorem pc_thm_80940 : Nat.primeCounting 80940 = 7922 := primeCounting_step 80000 941 7837 85 count_80000 (by rw [count_shift_is_prime_eq 80000 941 (by omega)]; decide)

theorem pc_thm_81003 : Nat.primeCounting 81003 = 7926 := primeCounting_step 80000 1004 7837 89 count_80000 (by rw [count_shift_is_prime_eq 80000 1004 (by omega)]; decide)

theorem pc_thm_81406 : Nat.primeCounting 81406 = 7965 := primeCounting_step 80000 1407 7837 128 count_80000 (by rw [count_shift_is_prime_eq 80000 1407 (by omega)]; decide)

theorem pc_thm_81510 : Nat.primeCounting 81510 = 7971 := primeCounting_step 80000 1511 7837 134 count_80000 (by rw [count_shift_is_prime_eq 80000 1511 (by omega)]; decide)

theorem pc_thm_82082 : Nat.primeCounting 82082 = 8028 := primeCounting_step 80000 2083 7837 191 count_80000 (by rw [count_shift_is_prime_eq 80000 2083 (by omega)]; decide)

theorem pc_thm_82215 : Nat.primeCounting 82215 = 8038 := primeCounting_step 80000 2216 7837 201 count_80000 (by rw [count_shift_is_prime_eq 80000 2216 (by omega)]; decide)

theorem pc_thm_82621 : Nat.primeCounting 82621 = 8078 := primeCounting_step 80000 2622 7837 241 count_80000 (by rw [count_shift_is_prime_eq 80000 2622 (by omega)]; decide)

theorem pc_thm_82656 : Nat.primeCounting 82656 = 8080 := primeCounting_step 80000 2657 7837 243 count_80000 (by rw [count_shift_is_prime_eq 80000 2657 (by omega)]; decide)

theorem pc_thm_83232 : Nat.primeCounting 83232 = 8126 := primeCounting_step 80000 3233 7837 289 count_80000 (by rw [count_shift_is_prime_eq 80000 3233 (by omega)]; decide)

theorem pc_thm_83436 : Nat.primeCounting 83436 = 8145 := primeCounting_step 80000 3437 7837 308 count_80000 (by rw [count_shift_is_prime_eq 80000 3437 (by omega)]; decide)

theorem pc_thm_83810 : Nat.primeCounting 83810 = 8175 := primeCounting_step 80000 3811 7837 338 count_80000 (by rw [count_shift_is_prime_eq 80000 3811 (by omega)]; decide)

theorem pc_thm_83845 : Nat.primeCounting 83845 = 8178 := primeCounting_step 80000 3846 7837 341 count_80000 (by rw [count_shift_is_prime_eq 80000 3846 (by omega)]; decide)

theorem pc_thm_84390 : Nat.primeCounting 84390 = 8224 := primeCounting_step 80000 4391 7837 387 count_80000 (by rw [count_shift_is_prime_eq 80000 4391 (by omega)]; decide)

theorem pc_thm_84666 : Nat.primeCounting 84666 = 8250 := primeCounting_step 80000 4667 7837 413 count_80000 (by rw [count_shift_is_prime_eq 80000 4667 (by omega)]; decide)

theorem pc_thm_84972 : Nat.primeCounting 84972 = 8274 := primeCounting_step 80000 4973 7837 437 count_80000 (by rw [count_shift_is_prime_eq 80000 4973 (by omega)]; decide)

theorem pc_thm_85078 : Nat.primeCounting 85078 = 8283 := primeCounting_step 80000 5079 7837 446 count_80000 (by rw [count_shift_is_prime_eq 80000 5079 (by omega)]; decide)

theorem pc_thm_85556 : Nat.primeCounting 85556 = 8326 := primeCounting_step 80000 5557 7837 489 count_80000 (by rw [count_shift_is_prime_eq 80000 5557 (by omega)]; decide)

theorem pc_thm_86142 : Nat.primeCounting 86142 = 8374 := primeCounting_step 80000 6143 7837 537 count_80000 (by rw [count_shift_is_prime_eq 80000 6143 (by omega)]; decide)

theorem pc_thm_86320 : Nat.primeCounting 86320 = 8393 := primeCounting_step 80000 6321 7837 556 count_80000 (by rw [count_shift_is_prime_eq 80000 6321 (by omega)]; decide)

theorem pc_thm_86730 : Nat.primeCounting 86730 = 8429 := primeCounting_step 80000 6731 7837 592 count_80000 (by rw [count_shift_is_prime_eq 80000 6731 (by omega)]; decide)

theorem pc_thm_86736 : Nat.primeCounting 86736 = 8429 := primeCounting_step 80000 6737 7837 592 count_80000 (by rw [count_shift_is_prime_eq 80000 6737 (by omega)]; decide)

theorem pc_thm_87153 : Nat.primeCounting 87153 = 8464 := primeCounting_step 80000 7154 7837 627 count_80000 (by rw [count_shift_is_prime_eq 80000 7154 (by omega)]; decide)

theorem pc_thm_87320 : Nat.primeCounting 87320 = 8479 := primeCounting_step 80000 7321 7837 642 count_80000 (by rw [count_shift_is_prime_eq 80000 7321 (by omega)]; decide)

theorem pc_thm_87571 : Nat.primeCounting 87571 = 8502 := primeCounting_step 80000 7572 7837 665 count_80000 (by rw [count_shift_is_prime_eq 80000 7572 (by omega)]; decide)

theorem pc_thm_87912 : Nat.primeCounting 87912 = 8535 := primeCounting_step 80000 7913 7837 698 count_80000 (by rw [count_shift_is_prime_eq 80000 7913 (by omega)]; decide)

theorem pc_thm_88506 : Nat.primeCounting 88506 = 8577 := primeCounting_step 80000 8507 7837 740 count_80000 (by rw [count_shift_is_prime_eq 80000 8507 (by omega)]; decide)

theorem pc_thm_88831 : Nat.primeCounting 88831 = 8605 := primeCounting_step 80000 8832 7837 768 count_80000 (by rw [count_shift_is_prime_eq 80000 8832 (by omega)]; decide)

theorem pc_thm_89102 : Nat.primeCounting 89102 = 8631 := primeCounting_step 80000 9103 7837 794 count_80000 (by rw [count_shift_is_prime_eq 80000 9103 (by omega)]; decide)

theorem pc_thm_89253 : Nat.primeCounting 89253 = 8644 := primeCounting_step 80000 9254 7837 807 count_80000 (by rw [count_shift_is_prime_eq 80000 9254 (by omega)]; decide)

theorem pc_thm_89676 : Nat.primeCounting 89676 = 8686 := primeCounting_step 80000 9677 7837 849 count_80000 (by rw [count_shift_is_prime_eq 80000 9677 (by omega)]; decide)

theorem pc_thm_89700 : Nat.primeCounting 89700 = 8688 := primeCounting_step 80000 9701 7837 851 count_80000 (by rw [count_shift_is_prime_eq 80000 9701 (by omega)]; decide)

theorem pc_thm_90100 : Nat.primeCounting 90100 = 8726 := primeCounting_step 80000 10101 7837 889 count_80000 (by rw [count_shift_is_prime_eq 80000 10101 (by omega)]; decide)

theorem pc_thm_90300 : Nat.primeCounting 90300 = 8745 := primeCounting_step 80000 10301 7837 908 count_80000 (by rw [count_shift_is_prime_eq 80000 10301 (by omega)]; decide)

theorem pc_thm_90902 : Nat.primeCounting 90902 = 8793 := primeCounting_step 80000 10903 7837 956 count_80000 (by rw [count_shift_is_prime_eq 80000 10903 (by omega)]; decide)

theorem pc_thm_90951 : Nat.primeCounting 90951 = 8798 := primeCounting_step 80000 10952 7837 961 count_80000 (by rw [count_shift_is_prime_eq 80000 10952 (by omega)]; decide)

theorem pc_thm_91378 : Nat.primeCounting 91378 = 8835 := primeCounting_step 80000 11379 7837 998 count_80000 (by rw [count_shift_is_prime_eq 80000 11379 (by omega)]; decide)

theorem pc_thm_91506 : Nat.primeCounting 91506 = 8848 := primeCounting_step 80000 11507 7837 1011 count_80000 (by rw [count_shift_is_prime_eq 80000 11507 (by omega)]; decide)

theorem pc_thm_92112 : Nat.primeCounting 92112 = 8896 := primeCounting_step 80000 12113 7837 1059 count_80000 (by rw [count_shift_is_prime_eq 80000 12113 (by omega)]; decide)

theorem pc_thm_92235 : Nat.primeCounting 92235 = 8908 := primeCounting_step 80000 12236 7837 1071 count_80000 (by rw [count_shift_is_prime_eq 80000 12236 (by omega)]; decide)

theorem pc_thm_92665 : Nat.primeCounting 92665 = 8949 := primeCounting_step 80000 12666 7837 1112 count_80000 (by rw [count_shift_is_prime_eq 80000 12666 (by omega)]; decide)

theorem pc_thm_92720 : Nat.primeCounting 92720 = 8957 := primeCounting_step 80000 12721 7837 1120 count_80000 (by rw [count_shift_is_prime_eq 80000 12721 (by omega)]; decide)

theorem pc_thm_93330 : Nat.primeCounting 93330 = 9016 := primeCounting_step 80000 13331 7837 1179 count_80000 (by rw [count_shift_is_prime_eq 80000 13331 (by omega)]; decide)

theorem pc_thm_93528 : Nat.primeCounting 93528 = 9032 := primeCounting_step 80000 13529 7837 1195 count_80000 (by rw [count_shift_is_prime_eq 80000 13529 (by omega)]; decide)

theorem pc_thm_93942 : Nat.primeCounting 93942 = 9064 := primeCounting_step 80000 13943 7837 1227 count_80000 (by rw [count_shift_is_prime_eq 80000 13943 (by omega)]; decide)

theorem pc_thm_93961 : Nat.primeCounting 93961 = 9065 := primeCounting_step 80000 13962 7837 1228 count_80000 (by rw [count_shift_is_prime_eq 80000 13962 (by omega)]; decide)

theorem pc_thm_94556 : Nat.primeCounting 94556 = 9119 := primeCounting_step 80000 14557 7837 1282 count_80000 (by rw [count_shift_is_prime_eq 80000 14557 (by omega)]; decide)

theorem pc_thm_94830 : Nat.primeCounting 94830 = 9143 := primeCounting_step 80000 14831 7837 1306 count_80000 (by rw [count_shift_is_prime_eq 80000 14831 (by omega)]; decide)

theorem pc_thm_95172 : Nat.primeCounting 95172 = 9173 := primeCounting_step 80000 15173 7837 1336 count_80000 (by rw [count_shift_is_prime_eq 80000 15173 (by omega)]; decide)

theorem pc_thm_95266 : Nat.primeCounting 95266 = 9184 := primeCounting_step 80000 15267 7837 1347 count_80000 (by rw [count_shift_is_prime_eq 80000 15267 (by omega)]; decide)

theorem pc_thm_95790 : Nat.primeCounting 95790 = 9232 := primeCounting_step 80000 15791 7837 1395 count_80000 (by rw [count_shift_is_prime_eq 80000 15791 (by omega)]; decide)

theorem pc_thm_96141 : Nat.primeCounting 96141 = 9261 := primeCounting_step 80000 16142 7837 1424 count_80000 (by rw [count_shift_is_prime_eq 80000 16142 (by omega)]; decide)

theorem pc_thm_96410 : Nat.primeCounting 96410 = 9284 := primeCounting_step 80000 16411 7837 1447 count_80000 (by rw [count_shift_is_prime_eq 80000 16411 (by omega)]; decide)

theorem pc_thm_96580 : Nat.primeCounting 96580 = 9299 := primeCounting_step 80000 16581 7837 1462 count_80000 (by rw [count_shift_is_prime_eq 80000 16581 (by omega)]; decide)

theorem pc_thm_97020 : Nat.primeCounting 97020 = 9339 := primeCounting_step 80000 17021 7837 1502 count_80000 (by rw [count_shift_is_prime_eq 80000 17021 (by omega)]; decide)

theorem pc_thm_97032 : Nat.primeCounting 97032 = 9340 := primeCounting_step 80000 17033 7837 1503 count_80000 (by rw [count_shift_is_prime_eq 80000 17033 (by omega)]; decide)

theorem pc_thm_97461 : Nat.primeCounting 97461 = 9373 := primeCounting_step 80000 17462 7837 1536 count_80000 (by rw [count_shift_is_prime_eq 80000 17462 (by omega)]; decide)

theorem pc_thm_97656 : Nat.primeCounting 97656 = 9391 := primeCounting_step 80000 17657 7837 1554 count_80000 (by rw [count_shift_is_prime_eq 80000 17657 (by omega)]; decide)

theorem pc_thm_98282 : Nat.primeCounting 98282 = 9437 := primeCounting_step 80000 18283 7837 1600 count_80000 (by rw [count_shift_is_prime_eq 80000 18283 (by omega)]; decide)

theorem pc_thm_98346 : Nat.primeCounting 98346 = 9443 := primeCounting_step 80000 18347 7837 1606 count_80000 (by rw [count_shift_is_prime_eq 80000 18347 (by omega)]; decide)

theorem pc_thm_98790 : Nat.primeCounting 98790 = 9482 := primeCounting_step 80000 18791 7837 1645 count_80000 (by rw [count_shift_is_prime_eq 80000 18791 (by omega)]; decide)

theorem pc_thm_98910 : Nat.primeCounting 98910 = 9495 := primeCounting_step 80000 18911 7837 1658 count_80000 (by rw [count_shift_is_prime_eq 80000 18911 (by omega)]; decide)

theorem pc_thm_99540 : Nat.primeCounting 99540 = 9550 := primeCounting_step 80000 19541 7837 1713 count_80000 (by rw [count_shift_is_prime_eq 80000 19541 (by omega)]; decide)

theorem pc_thm_99681 : Nat.primeCounting 99681 = 9563 := primeCounting_step 80000 19682 7837 1726 count_80000 (by rw [count_shift_is_prime_eq 80000 19682 (by omega)]; decide)

theorem pc_thm_100128 : Nat.primeCounting 100128 = 9600 := primeCounting_step 100000 129 9592 8 count_100000 (by rw [count_shift_is_prime_eq 100000 129 (by omega)]; decide)

theorem pc_thm_100172 : Nat.primeCounting 100172 = 9604 := primeCounting_step 100000 173 9592 12 count_100000 (by rw [count_shift_is_prime_eq 100000 173 (by omega)]; decide)

theorem pc_thm_100806 : Nat.primeCounting 100806 = 9658 := primeCounting_step 100000 807 9592 66 count_100000 (by rw [count_shift_is_prime_eq 100000 807 (by omega)]; decide)

theorem pc_thm_101025 : Nat.primeCounting 101025 = 9675 := primeCounting_step 100000 1026 9592 83 count_100000 (by rw [count_shift_is_prime_eq 100000 1026 (by omega)]; decide)

theorem pc_thm_101442 : Nat.primeCounting 101442 = 9714 := primeCounting_step 100000 1443 9592 122 count_100000 (by rw [count_shift_is_prime_eq 100000 1443 (by omega)]; decide)

theorem pc_thm_101475 : Nat.primeCounting 101475 = 9716 := primeCounting_step 100000 1476 9592 124 count_100000 (by rw [count_shift_is_prime_eq 100000 1476 (by omega)]; decide)

theorem pc_thm_101926 : Nat.primeCounting 101926 = 9759 := primeCounting_step 100000 1927 9592 167 count_100000 (by rw [count_shift_is_prime_eq 100000 1927 (by omega)]; decide)

theorem pc_thm_102080 : Nat.primeCounting 102080 = 9777 := primeCounting_step 100000 2081 9592 185 count_100000 (by rw [count_shift_is_prime_eq 100000 2081 (by omega)]; decide)

theorem pc_thm_102378 : Nat.primeCounting 102378 = 9804 := primeCounting_step 100000 2379 9592 212 count_100000 (by rw [count_shift_is_prime_eq 100000 2379 (by omega)]; decide)

theorem pc_thm_102720 : Nat.primeCounting 102720 = 9834 := primeCounting_step 100000 2721 9592 242 count_100000 (by rw [count_shift_is_prime_eq 100000 2721 (by omega)]; decide)

theorem pc_thm_103285 : Nat.primeCounting 103285 = 9872 := primeCounting_step 100000 3286 9592 280 count_100000 (by rw [count_shift_is_prime_eq 100000 3286 (by omega)]; decide)

theorem pc_thm_103362 : Nat.primeCounting 103362 = 9879 := primeCounting_step 100000 3363 9592 287 count_100000 (by rw [count_shift_is_prime_eq 100000 3363 (by omega)]; decide)

theorem pc_thm_103740 : Nat.primeCounting 103740 = 9911 := primeCounting_step 100000 3741 9592 319 count_100000 (by rw [count_shift_is_prime_eq 100000 3741 (by omega)]; decide)

theorem pc_thm_104006 : Nat.primeCounting 104006 = 9934 := primeCounting_step 100000 4007 9592 342 count_100000 (by rw [count_shift_is_prime_eq 100000 4007 (by omega)]; decide)

theorem pc_thm_104652 : Nat.primeCounting 104652 = 9989 := primeCounting_step 100000 4653 9592 397 count_100000 (by rw [count_shift_is_prime_eq 100000 4653 (by omega)]; decide)

theorem pc_thm_104653 : Nat.primeCounting 104653 = 9989 := primeCounting_step 100000 4654 9592 397 count_100000 (by rw [count_shift_is_prime_eq 100000 4654 (by omega)]; decide)

theorem pc_thm_105111 : Nat.primeCounting 105111 = 10031 := primeCounting_step 100000 5112 9592 439 count_100000 (by rw [count_shift_is_prime_eq 100000 5112 (by omega)]; decide)

theorem pc_thm_105300 : Nat.primeCounting 105300 = 10045 := primeCounting_step 100000 5301 9592 453 count_100000 (by rw [count_shift_is_prime_eq 100000 5301 (by omega)]; decide)

theorem pc_thm_105950 : Nat.primeCounting 105950 = 10100 := primeCounting_step 100000 5951 9592 508 count_100000 (by rw [count_shift_is_prime_eq 100000 5951 (by omega)]; decide)

theorem pc_thm_106030 : Nat.primeCounting 106030 = 10108 := primeCounting_step 100000 6031 9592 516 count_100000 (by rw [count_shift_is_prime_eq 100000 6031 (by omega)]; decide)

theorem pc_thm_106491 : Nat.primeCounting 106491 = 10151 := primeCounting_step 100000 6492 9592 559 count_100000 (by rw [count_shift_is_prime_eq 100000 6492 (by omega)]; decide)

theorem pc_thm_106602 : Nat.primeCounting 106602 = 10157 := primeCounting_step 100000 6603 9592 565 count_100000 (by rw [count_shift_is_prime_eq 100000 6603 (by omega)]; decide)

theorem pc_thm_106953 : Nat.primeCounting 106953 = 10193 := primeCounting_step 100000 6954 9592 601 count_100000 (by rw [count_shift_is_prime_eq 100000 6954 (by omega)]; decide)

theorem pc_thm_107256 : Nat.primeCounting 107256 = 10219 := primeCounting_step 100000 7257 9592 627 count_100000 (by rw [count_shift_is_prime_eq 100000 7257 (by omega)]; decide)

theorem pc_thm_107416 : Nat.primeCounting 107416 = 10229 := primeCounting_step 100000 7417 9592 637 count_100000 (by rw [count_shift_is_prime_eq 100000 7417 (by omega)]; decide)

theorem pc_thm_107912 : Nat.primeCounting 107912 = 10267 := primeCounting_step 100000 7913 9592 675 count_100000 (by rw [count_shift_is_prime_eq 100000 7913 (by omega)]; decide)

theorem pc_thm_108345 : Nat.primeCounting 108345 = 10306 := primeCounting_step 100000 8346 9592 714 count_100000 (by rw [count_shift_is_prime_eq 100000 8346 (by omega)]; decide)

theorem pc_thm_108570 : Nat.primeCounting 108570 = 10326 := primeCounting_step 100000 8571 9592 734 count_100000 (by rw [count_shift_is_prime_eq 100000 8571 (by omega)]; decide)

theorem pc_thm_108811 : Nat.primeCounting 108811 = 10344 := primeCounting_step 100000 8812 9592 752 count_100000 (by rw [count_shift_is_prime_eq 100000 8812 (by omega)]; decide)

theorem pc_thm_109230 : Nat.primeCounting 109230 = 10386 := primeCounting_step 100000 9231 9592 794 count_100000 (by rw [count_shift_is_prime_eq 100000 9231 (by omega)]; decide)

theorem pc_thm_109746 : Nat.primeCounting 109746 = 10430 := primeCounting_step 100000 9747 9592 838 count_100000 (by rw [count_shift_is_prime_eq 100000 9747 (by omega)]; decide)

theorem pc_thm_109892 : Nat.primeCounting 109892 = 10445 := primeCounting_step 100000 9893 9592 853 count_100000 (by rw [count_shift_is_prime_eq 100000 9893 (by omega)]; decide)

theorem pc_thm_110215 : Nat.primeCounting 110215 = 10465 := primeCounting_step 100000 10216 9592 873 count_100000 (by rw [count_shift_is_prime_eq 100000 10216 (by omega)]; decide)

theorem pc_thm_110556 : Nat.primeCounting 110556 = 10492 := primeCounting_step 100000 10557 9592 900 count_100000 (by rw [count_shift_is_prime_eq 100000 10557 (by omega)]; decide)

theorem pc_thm_111156 : Nat.primeCounting 111156 = 10549 := primeCounting_step 100000 11157 9592 957 count_100000 (by rw [count_shift_is_prime_eq 100000 11157 (by omega)]; decide)

theorem pc_thm_111222 : Nat.primeCounting 111222 = 10553 := primeCounting_step 100000 11223 9592 961 count_100000 (by rw [count_shift_is_prime_eq 100000 11223 (by omega)]; decide)

theorem pc_thm_111628 : Nat.primeCounting 111628 = 10586 := primeCounting_step 100000 11629 9592 994 count_100000 (by rw [count_shift_is_prime_eq 100000 11629 (by omega)]; decide)

theorem pc_thm_111890 : Nat.primeCounting 111890 = 10611 := primeCounting_step 100000 11891 9592 1019 count_100000 (by rw [count_shift_is_prime_eq 100000 11891 (by omega)]; decide)

theorem pc_thm_112560 : Nat.primeCounting 112560 = 10666 := primeCounting_step 100000 12561 9592 1074 count_100000 (by rw [count_shift_is_prime_eq 100000 12561 (by omega)]; decide)

theorem pc_thm_112575 : Nat.primeCounting 112575 = 10668 := primeCounting_step 100000 12576 9592 1076 count_100000 (by rw [count_shift_is_prime_eq 100000 12576 (by omega)]; decide)

theorem pc_thm_113050 : Nat.primeCounting 113050 = 10708 := primeCounting_step 100000 13051 9592 1116 count_100000 (by rw [count_shift_is_prime_eq 100000 13051 (by omega)]; decide)

theorem pc_thm_113232 : Nat.primeCounting 113232 = 10732 := primeCounting_step 100000 13233 9592 1140 count_100000 (by rw [count_shift_is_prime_eq 100000 13233 (by omega)]; decide)

theorem pc_thm_113526 : Nat.primeCounting 113526 = 10752 := primeCounting_step 100000 13527 9592 1160 count_100000 (by rw [count_shift_is_prime_eq 100000 13527 (by omega)]; decide)

theorem pc_thm_113906 : Nat.primeCounting 113906 = 10780 := primeCounting_step 100000 13907 9592 1188 count_100000 (by rw [count_shift_is_prime_eq 100000 13907 (by omega)]; decide)

theorem pc_thm_114003 : Nat.primeCounting 114003 = 10790 := primeCounting_step 100000 14004 9592 1198 count_100000 (by rw [count_shift_is_prime_eq 100000 14004 (by omega)]; decide)

theorem pc_thm_114481 : Nat.primeCounting 114481 = 10828 := primeCounting_step 100000 14482 9592 1236 count_100000 (by rw [count_shift_is_prime_eq 100000 14482 (by omega)]; decide)

theorem pc_thm_114582 : Nat.primeCounting 114582 = 10834 := primeCounting_step 100000 14583 9592 1242 count_100000 (by rw [count_shift_is_prime_eq 100000 14583 (by omega)]; decide)

theorem pc_thm_114960 : Nat.primeCounting 114960 = 10868 := primeCounting_step 100000 14961 9592 1276 count_100000 (by rw [count_shift_is_prime_eq 100000 14961 (by omega)]; decide)

theorem pc_thm_115260 : Nat.primeCounting 115260 = 10894 := primeCounting_step 100000 15261 9592 1302 count_100000 (by rw [count_shift_is_prime_eq 100000 15261 (by omega)]; decide)

theorem pc_thm_115921 : Nat.primeCounting 115921 = 10958 := primeCounting_step 100000 15922 9592 1366 count_100000 (by rw [count_shift_is_prime_eq 100000 15922 (by omega)]; decide)

theorem pc_thm_115940 : Nat.primeCounting 115940 = 10960 := primeCounting_step 100000 15941 9592 1368 count_100000 (by rw [count_shift_is_prime_eq 100000 15941 (by omega)]; decide)

theorem pc_thm_116403 : Nat.primeCounting 116403 = 10995 := primeCounting_step 100000 16404 9592 1403 count_100000 (by rw [count_shift_is_prime_eq 100000 16404 (by omega)]; decide)

theorem pc_thm_116622 : Nat.primeCounting 116622 = 11012 := primeCounting_step 100000 16623 9592 1420 count_100000 (by rw [count_shift_is_prime_eq 100000 16623 (by omega)]; decide)

theorem pc_thm_117306 : Nat.primeCounting 117306 = 11070 := primeCounting_step 100000 17307 9592 1478 count_100000 (by rw [count_shift_is_prime_eq 100000 17307 (by omega)]; decide)

theorem pc_thm_117370 : Nat.primeCounting 117370 = 11076 := primeCounting_step 100000 17371 9592 1484 count_100000 (by rw [count_shift_is_prime_eq 100000 17371 (by omega)]; decide)

theorem pc_thm_117855 : Nat.primeCounting 117855 = 11121 := primeCounting_step 100000 17856 9592 1529 count_100000 (by rw [count_shift_is_prime_eq 100000 17856 (by omega)]; decide)

theorem pc_thm_117992 : Nat.primeCounting 117992 = 11135 := primeCounting_step 100000 17993 9592 1543 count_100000 (by rw [count_shift_is_prime_eq 100000 17993 (by omega)]; decide)

theorem pc_thm_118341 : Nat.primeCounting 118341 = 11159 := primeCounting_step 100000 18342 9592 1567 count_100000 (by rw [count_shift_is_prime_eq 100000 18342 (by omega)]; decide)

theorem pc_thm_118680 : Nat.primeCounting 118680 = 11187 := primeCounting_step 100000 18681 9592 1595 count_100000 (by rw [count_shift_is_prime_eq 100000 18681 (by omega)]; decide)

theorem pc_thm_118828 : Nat.primeCounting 118828 = 11200 := primeCounting_step 100000 18829 9592 1608 count_100000 (by rw [count_shift_is_prime_eq 100000 18829 (by omega)]; decide)

theorem pc_thm_119370 : Nat.primeCounting 119370 = 11246 := primeCounting_step 100000 19371 9592 1654 count_100000 (by rw [count_shift_is_prime_eq 100000 19371 (by omega)]; decide)

theorem pc_thm_119805 : Nat.primeCounting 119805 = 11282 := primeCounting_step 100000 19806 9592 1690 count_100000 (by rw [count_shift_is_prime_eq 100000 19806 (by omega)]; decide)

theorem pc_thm_120062 : Nat.primeCounting 120062 = 11306 := primeCounting_step 120000 63 11301 5 count_120000 (by rw [count_shift_is_prime_eq 120000 63 (by omega)]; decide)

theorem pc_thm_120295 : Nat.primeCounting 120295 = 11326 := primeCounting_step 120000 296 11301 25 count_120000 (by rw [count_shift_is_prime_eq 120000 296 (by omega)]; decide)

theorem pc_thm_120756 : Nat.primeCounting 120756 = 11364 := primeCounting_step 120000 757 11301 63 count_120000 (by rw [count_shift_is_prime_eq 120000 757 (by omega)]; decide)

theorem pc_thm_120786 : Nat.primeCounting 120786 = 11367 := primeCounting_step 120000 787 11301 66 count_120000 (by rw [count_shift_is_prime_eq 120000 787 (by omega)]; decide)

theorem pc_thm_121278 : Nat.primeCounting 121278 = 11411 := primeCounting_step 120000 1279 11301 110 count_120000 (by rw [count_shift_is_prime_eq 120000 1279 (by omega)]; decide)

theorem pc_thm_121452 : Nat.primeCounting 121452 = 11430 := primeCounting_step 120000 1453 11301 129 count_120000 (by rw [count_shift_is_prime_eq 120000 1453 (by omega)]; decide)

theorem pc_thm_122150 : Nat.primeCounting 122150 = 11491 := primeCounting_step 120000 2151 11301 190 count_120000 (by rw [count_shift_is_prime_eq 120000 2151 (by omega)]; decide)

theorem pc_thm_122265 : Nat.primeCounting 122265 = 11501 := primeCounting_step 120000 2266 11301 200 count_120000 (by rw [count_shift_is_prime_eq 120000 2266 (by omega)]; decide)

theorem pc_thm_122760 : Nat.primeCounting 122760 = 11543 := primeCounting_step 120000 2761 11301 242 count_120000 (by rw [count_shift_is_prime_eq 120000 2761 (by omega)]; decide)

theorem pc_thm_122850 : Nat.primeCounting 122850 = 11551 := primeCounting_step 120000 2851 11301 250 count_120000 (by rw [count_shift_is_prime_eq 120000 2851 (by omega)]; decide)

theorem pc_thm_123256 : Nat.primeCounting 123256 = 11583 := primeCounting_step 120000 3257 11301 282 count_120000 (by rw [count_shift_is_prime_eq 120000 3257 (by omega)]; decide)

theorem pc_thm_123552 : Nat.primeCounting 123552 = 11611 := primeCounting_step 120000 3553 11301 310 count_120000 (by rw [count_shift_is_prime_eq 120000 3553 (by omega)]; decide)

theorem pc_thm_123753 : Nat.primeCounting 123753 = 11630 := primeCounting_step 120000 3754 11301 329 count_120000 (by rw [count_shift_is_prime_eq 120000 3754 (by omega)]; decide)

theorem pc_thm_124256 : Nat.primeCounting 124256 = 11671 := primeCounting_step 120000 4257 11301 370 count_120000 (by rw [count_shift_is_prime_eq 120000 4257 (by omega)]; decide)

theorem pc_thm_124750 : Nat.primeCounting 124750 = 11712 := primeCounting_step 120000 4751 11301 411 count_120000 (by rw [count_shift_is_prime_eq 120000 4751 (by omega)]; decide)

theorem pc_thm_124962 : Nat.primeCounting 124962 = 11730 := primeCounting_step 120000 4963 11301 429 count_120000 (by rw [count_shift_is_prime_eq 120000 4963 (by omega)]; decide)

theorem pc_thm_125250 : Nat.primeCounting 125250 = 11756 := primeCounting_step 120000 5251 11301 455 count_120000 (by rw [count_shift_is_prime_eq 120000 5251 (by omega)]; decide)

theorem pc_thm_125670 : Nat.primeCounting 125670 = 11791 := primeCounting_step 120000 5671 11301 490 count_120000 (by rw [count_shift_is_prime_eq 120000 5671 (by omega)]; decide)

theorem pc_thm_125751 : Nat.primeCounting 125751 = 11800 := primeCounting_step 120000 5752 11301 499 count_120000 (by rw [count_shift_is_prime_eq 120000 5752 (by omega)]; decide)

theorem pc_thm_126253 : Nat.primeCounting 126253 = 11843 := primeCounting_step 120000 6254 11301 542 count_120000 (by rw [count_shift_is_prime_eq 120000 6254 (by omega)]; decide)

theorem pc_thm_126380 : Nat.primeCounting 126380 = 11853 := primeCounting_step 120000 6381 11301 552 count_120000 (by rw [count_shift_is_prime_eq 120000 6381 (by omega)]; decide)

theorem pc_thm_127092 : Nat.primeCounting 127092 = 11907 := primeCounting_step 120000 7093 11301 606 count_120000 (by rw [count_shift_is_prime_eq 120000 7093 (by omega)]; decide)

theorem pc_thm_127260 : Nat.primeCounting 127260 = 11920 := primeCounting_step 120000 7261 11301 619 count_120000 (by rw [count_shift_is_prime_eq 120000 7261 (by omega)]; decide)

theorem pc_thm_127765 : Nat.primeCounting 127765 = 11969 := primeCounting_step 120000 7766 11301 668 count_120000 (by rw [count_shift_is_prime_eq 120000 7766 (by omega)]; decide)

theorem pc_thm_127806 : Nat.primeCounting 127806 = 11970 := primeCounting_step 120000 7807 11301 669 count_120000 (by rw [count_shift_is_prime_eq 120000 7807 (by omega)]; decide)

theorem pc_thm_128271 : Nat.primeCounting 128271 = 12007 := primeCounting_step 120000 8272 11301 706 count_120000 (by rw [count_shift_is_prime_eq 120000 8272 (by omega)]; decide)

theorem pc_thm_128522 : Nat.primeCounting 128522 = 12035 := primeCounting_step 120000 8523 11301 734 count_120000 (by rw [count_shift_is_prime_eq 120000 8523 (by omega)]; decide)

theorem pc_thm_128778 : Nat.primeCounting 128778 = 12055 := primeCounting_step 120000 8779 11301 754 count_120000 (by rw [count_shift_is_prime_eq 120000 8779 (by omega)]; decide)

theorem pc_thm_129240 : Nat.primeCounting 129240 = 12097 := primeCounting_step 120000 9241 11301 796 count_120000 (by rw [count_shift_is_prime_eq 120000 9241 (by omega)]; decide)

theorem pc_thm_129795 : Nat.primeCounting 129795 = 12146 := primeCounting_step 120000 9796 11301 845 count_120000 (by rw [count_shift_is_prime_eq 120000 9796 (by omega)]; decide)

theorem pc_thm_129960 : Nat.primeCounting 129960 = 12157 := primeCounting_step 120000 9961 11301 856 count_120000 (by rw [count_shift_is_prime_eq 120000 9961 (by omega)]; decide)

theorem pc_thm_130305 : Nat.primeCounting 130305 = 12186 := primeCounting_step 120000 10306 11301 885 count_120000 (by rw [count_shift_is_prime_eq 120000 10306 (by omega)]; decide)

theorem pc_thm_130682 : Nat.primeCounting 130682 = 12223 := primeCounting_step 120000 10683 11301 922 count_120000 (by rw [count_shift_is_prime_eq 120000 10683 (by omega)]; decide)

theorem pc_thm_130816 : Nat.primeCounting 130816 = 12232 := primeCounting_step 120000 10817 11301 931 count_120000 (by rw [count_shift_is_prime_eq 120000 10817 (by omega)]; decide)

theorem pc_thm_131328 : Nat.primeCounting 131328 = 12271 := primeCounting_step 120000 11329 11301 970 count_120000 (by rw [count_shift_is_prime_eq 120000 11329 (by omega)]; decide)

theorem pc_thm_131406 : Nat.primeCounting 131406 = 12275 := primeCounting_step 120000 11407 11301 974 count_120000 (by rw [count_shift_is_prime_eq 120000 11407 (by omega)]; decide)

theorem pc_thm_132132 : Nat.primeCounting 132132 = 12336 := primeCounting_step 120000 12133 11301 1035 count_120000 (by rw [count_shift_is_prime_eq 120000 12133 (by omega)]; decide)

theorem pc_thm_132355 : Nat.primeCounting 132355 = 12355 := primeCounting_step 120000 12356 11301 1054 count_120000 (by rw [count_shift_is_prime_eq 120000 12356 (by omega)]; decide)

theorem pc_thm_132860 : Nat.primeCounting 132860 = 12402 := primeCounting_step 120000 12861 11301 1101 count_120000 (by rw [count_shift_is_prime_eq 120000 12861 (by omega)]; decide)

theorem pc_thm_132870 : Nat.primeCounting 132870 = 12403 := primeCounting_step 120000 12871 11301 1102 count_120000 (by rw [count_shift_is_prime_eq 120000 12871 (by omega)]; decide)

theorem pc_thm_133386 : Nat.primeCounting 133386 = 12448 := primeCounting_step 120000 13387 11301 1147 count_120000 (by rw [count_shift_is_prime_eq 120000 13387 (by omega)]; decide)

theorem pc_thm_133590 : Nat.primeCounting 133590 = 12464 := primeCounting_step 120000 13591 11301 1163 count_120000 (by rw [count_shift_is_prime_eq 120000 13591 (by omega)]; decide)

theorem pc_thm_133903 : Nat.primeCounting 133903 = 12488 := primeCounting_step 120000 13904 11301 1187 count_120000 (by rw [count_shift_is_prime_eq 120000 13904 (by omega)]; decide)

theorem pc_thm_134322 : Nat.primeCounting 134322 = 12523 := primeCounting_step 120000 14323 11301 1222 count_120000 (by rw [count_shift_is_prime_eq 120000 14323 (by omega)]; decide)

theorem pc_thm_134421 : Nat.primeCounting 134421 = 12535 := primeCounting_step 120000 14422 11301 1234 count_120000 (by rw [count_shift_is_prime_eq 120000 14422 (by omega)]; decide)

theorem pc_thm_134940 : Nat.primeCounting 134940 = 12572 := primeCounting_step 120000 14941 11301 1271 count_120000 (by rw [count_shift_is_prime_eq 120000 14941 (by omega)]; decide)

theorem pc_thm_135056 : Nat.primeCounting 135056 = 12582 := primeCounting_step 120000 15057 11301 1281 count_120000 (by rw [count_shift_is_prime_eq 120000 15057 (by omega)]; decide)

theorem pc_thm_135792 : Nat.primeCounting 135792 = 12651 := primeCounting_step 120000 15793 11301 1350 count_120000 (by rw [count_shift_is_prime_eq 120000 15793 (by omega)]; decide)

theorem pc_thm_135981 : Nat.primeCounting 135981 = 12665 := primeCounting_step 120000 15982 11301 1364 count_120000 (by rw [count_shift_is_prime_eq 120000 15982 (by omega)]; decide)

theorem pc_thm_136503 : Nat.primeCounting 136503 = 12714 := primeCounting_step 120000 16504 11301 1413 count_120000 (by rw [count_shift_is_prime_eq 120000 16504 (by omega)]; decide)

theorem pc_thm_136530 : Nat.primeCounting 136530 = 12717 := primeCounting_step 120000 16531 11301 1416 count_120000 (by rw [count_shift_is_prime_eq 120000 16531 (by omega)]; decide)

theorem pc_thm_137026 : Nat.primeCounting 137026 = 12761 := primeCounting_step 120000 17027 11301 1460 count_120000 (by rw [count_shift_is_prime_eq 120000 17027 (by omega)]; decide)

theorem pc_thm_137270 : Nat.primeCounting 137270 = 12780 := primeCounting_step 120000 17271 11301 1479 count_120000 (by rw [count_shift_is_prime_eq 120000 17271 (by omega)]; decide)

theorem pc_thm_137550 : Nat.primeCounting 137550 = 12805 := primeCounting_step 120000 17551 11301 1504 count_120000 (by rw [count_shift_is_prime_eq 120000 17551 (by omega)]; decide)

theorem pc_thm_138012 : Nat.primeCounting 138012 = 12842 := primeCounting_step 120000 18013 11301 1541 count_120000 (by rw [count_shift_is_prime_eq 120000 18013 (by omega)]; decide)

theorem pc_thm_138075 : Nat.primeCounting 138075 = 12846 := primeCounting_step 120000 18076 11301 1545 count_120000 (by rw [count_shift_is_prime_eq 120000 18076 (by omega)]; decide)

theorem pc_thm_138601 : Nat.primeCounting 138601 = 12896 := primeCounting_step 120000 18602 11301 1595 count_120000 (by rw [count_shift_is_prime_eq 120000 18602 (by omega)]; decide)

theorem pc_thm_138756 : Nat.primeCounting 138756 = 12907 := primeCounting_step 120000 18757 11301 1606 count_120000 (by rw [count_shift_is_prime_eq 120000 18757 (by omega)]; decide)

theorem pc_thm_139128 : Nat.primeCounting 139128 = 12934 := primeCounting_step 120000 19129 11301 1633 count_120000 (by rw [count_shift_is_prime_eq 120000 19129 (by omega)]; decide)

theorem pc_thm_139502 : Nat.primeCounting 139502 = 12968 := primeCounting_step 120000 19503 11301 1667 count_120000 (by rw [count_shift_is_prime_eq 120000 19503 (by omega)]; decide)

theorem pc_thm_139656 : Nat.primeCounting 139656 = 12978 := primeCounting_step 120000 19657 11301 1677 count_120000 (by rw [count_shift_is_prime_eq 120000 19657 (by omega)]; decide)

theorem pc_thm_140250 : Nat.primeCounting 140250 = 13029 := primeCounting_step 140000 251 13010 19 count_140000 (by rw [count_shift_is_prime_eq 140000 251 (by omega)]; decide)

theorem pc_thm_140715 : Nat.primeCounting 140715 = 13071 := primeCounting_step 140000 716 13010 61 count_140000 (by rw [count_shift_is_prime_eq 140000 716 (by omega)]; decide)

theorem pc_thm_141000 : Nat.primeCounting 141000 = 13097 := primeCounting_step 140000 1001 13010 87 count_140000 (by rw [count_shift_is_prime_eq 140000 1001 (by omega)]; decide)

theorem pc_thm_141246 : Nat.primeCounting 141246 = 13117 := primeCounting_step 140000 1247 13010 107 count_140000 (by rw [count_shift_is_prime_eq 140000 1247 (by omega)]; decide)

theorem pc_thm_141752 : Nat.primeCounting 141752 = 13162 := primeCounting_step 140000 1753 13010 152 count_140000 (by rw [count_shift_is_prime_eq 140000 1753 (by omega)]; decide)

theorem pc_thm_141778 : Nat.primeCounting 141778 = 13166 := primeCounting_step 140000 1779 13010 156 count_140000 (by rw [count_shift_is_prime_eq 140000 1779 (by omega)]; decide)

theorem pc_thm_142311 : Nat.primeCounting 142311 = 13210 := primeCounting_step 140000 2312 13010 200 count_140000 (by rw [count_shift_is_prime_eq 140000 2312 (by omega)]; decide)

theorem pc_thm_142506 : Nat.primeCounting 142506 = 13223 := primeCounting_step 140000 2507 13010 213 count_140000 (by rw [count_shift_is_prime_eq 140000 2507 (by omega)]; decide)

theorem pc_thm_142845 : Nat.primeCounting 142845 = 13252 := primeCounting_step 140000 2846 13010 242 count_140000 (by rw [count_shift_is_prime_eq 140000 2846 (by omega)]; decide)

theorem pc_thm_143262 : Nat.primeCounting 143262 = 13282 := primeCounting_step 140000 3263 13010 272 count_140000 (by rw [count_shift_is_prime_eq 140000 3263 (by omega)]; decide)

theorem pc_thm_143380 : Nat.primeCounting 143380 = 13289 := primeCounting_step 140000 3381 13010 279 count_140000 (by rw [count_shift_is_prime_eq 140000 3381 (by omega)]; decide)

theorem pc_thm_143916 : Nat.primeCounting 143916 = 13337 := primeCounting_step 140000 3917 13010 327 count_140000 (by rw [count_shift_is_prime_eq 140000 3917 (by omega)]; decide)

theorem pc_thm_144020 : Nat.primeCounting 144020 = 13344 := primeCounting_step 140000 4021 13010 334 count_140000 (by rw [count_shift_is_prime_eq 140000 4021 (by omega)]; decide)

theorem pc_thm_144453 : Nat.primeCounting 144453 = 13378 := primeCounting_step 140000 4454 13010 368 count_140000 (by rw [count_shift_is_prime_eq 140000 4454 (by omega)]; decide)

theorem pc_thm_144780 : Nat.primeCounting 144780 = 13406 := primeCounting_step 140000 4781 13010 396 count_140000 (by rw [count_shift_is_prime_eq 140000 4781 (by omega)]; decide)

theorem pc_thm_145530 : Nat.primeCounting 145530 = 13466 := primeCounting_step 140000 5531 13010 456 count_140000 (by rw [count_shift_is_prime_eq 140000 5531 (by omega)]; decide)

theorem pc_thm_145542 : Nat.primeCounting 145542 = 13467 := primeCounting_step 140000 5543 13010 457 count_140000 (by rw [count_shift_is_prime_eq 140000 5543 (by omega)]; decide)

theorem pc_thm_146070 : Nat.primeCounting 146070 = 13516 := primeCounting_step 140000 6071 13010 506 count_140000 (by rw [count_shift_is_prime_eq 140000 6071 (by omega)]; decide)

theorem pc_thm_146306 : Nat.primeCounting 146306 = 13534 := primeCounting_step 140000 6307 13010 524 count_140000 (by rw [count_shift_is_prime_eq 140000 6307 (by omega)]; decide)

theorem pc_thm_146611 : Nat.primeCounting 146611 = 13559 := primeCounting_step 140000 6612 13010 549 count_140000 (by rw [count_shift_is_prime_eq 140000 6612 (by omega)]; decide)

theorem pc_thm_147072 : Nat.primeCounting 147072 = 13595 := primeCounting_step 140000 7073 13010 585 count_140000 (by rw [count_shift_is_prime_eq 140000 7073 (by omega)]; decide)

theorem pc_thm_147153 : Nat.primeCounting 147153 = 13603 := primeCounting_step 140000 7154 13010 593 count_140000 (by rw [count_shift_is_prime_eq 140000 7154 (by omega)]; decide)

theorem pc_thm_147696 : Nat.primeCounting 147696 = 13651 := primeCounting_step 140000 7697 13010 641 count_140000 (by rw [count_shift_is_prime_eq 140000 7697 (by omega)]; decide)

theorem pc_thm_147840 : Nat.primeCounting 147840 = 13665 := primeCounting_step 140000 7841 13010 655 count_140000 (by rw [count_shift_is_prime_eq 140000 7841 (by omega)]; decide)

theorem pc_thm_148240 : Nat.primeCounting 148240 = 13693 := primeCounting_step 140000 8241 13010 683 count_140000 (by rw [count_shift_is_prime_eq 140000 8241 (by omega)]; decide)

theorem pc_thm_148610 : Nat.primeCounting 148610 = 13722 := primeCounting_step 140000 8611 13010 712 count_140000 (by rw [count_shift_is_prime_eq 140000 8611 (by omega)]; decide)

theorem pc_thm_148785 : Nat.primeCounting 148785 = 13738 := primeCounting_step 140000 8786 13010 728 count_140000 (by rw [count_shift_is_prime_eq 140000 8786 (by omega)]; decide)

theorem pc_thm_149331 : Nat.primeCounting 149331 = 13789 := primeCounting_step 140000 9332 13010 779 count_140000 (by rw [count_shift_is_prime_eq 140000 9332 (by omega)]; decide)

theorem pc_thm_149382 : Nat.primeCounting 149382 = 13795 := primeCounting_step 140000 9383 13010 785 count_140000 (by rw [count_shift_is_prime_eq 140000 9383 (by omega)]; decide)

theorem pc_thm_149878 : Nat.primeCounting 149878 = 13838 := primeCounting_step 140000 9879 13010 828 count_140000 (by rw [count_shift_is_prime_eq 140000 9879 (by omega)]; decide)

theorem pc_thm_150156 : Nat.primeCounting 150156 = 13862 := primeCounting_step 140000 10157 13010 852 count_140000 (by rw [count_shift_is_prime_eq 140000 10157 (by omega)]; decide)

theorem pc_thm_150426 : Nat.primeCounting 150426 = 13886 := primeCounting_step 140000 10427 13010 876 count_140000 (by rw [count_shift_is_prime_eq 140000 10427 (by omega)]; decide)

theorem pc_thm_150932 : Nat.primeCounting 150932 = 13927 := primeCounting_step 140000 10933 13010 917 count_140000 (by rw [count_shift_is_prime_eq 140000 10933 (by omega)]; decide)

theorem pc_thm_151525 : Nat.primeCounting 151525 = 13979 := primeCounting_step 140000 11526 13010 969 count_140000 (by rw [count_shift_is_prime_eq 140000 11526 (by omega)]; decide)

theorem pc_thm_151710 : Nat.primeCounting 151710 = 14000 := primeCounting_step 140000 11711 13010 990 count_140000 (by rw [count_shift_is_prime_eq 140000 11711 (by omega)]; decide)

theorem pc_thm_152076 : Nat.primeCounting 152076 = 14030 := primeCounting_step 140000 12077 13010 1020 count_140000 (by rw [count_shift_is_prime_eq 140000 12077 (by omega)]; decide)

theorem pc_thm_152490 : Nat.primeCounting 152490 = 14065 := primeCounting_step 140000 12491 13010 1055 count_140000 (by rw [count_shift_is_prime_eq 140000 12491 (by omega)]; decide)

theorem pc_thm_152628 : Nat.primeCounting 152628 = 14076 := primeCounting_step 140000 12629 13010 1066 count_140000 (by rw [count_shift_is_prime_eq 140000 12629 (by omega)]; decide)

theorem pc_thm_153181 : Nat.primeCounting 153181 = 14123 := primeCounting_step 140000 13182 13010 1113 count_140000 (by rw [count_shift_is_prime_eq 140000 13182 (by omega)]; decide)

theorem pc_thm_153272 : Nat.primeCounting 153272 = 14128 := primeCounting_step 140000 13273 13010 1118 count_140000 (by rw [count_shift_is_prime_eq 140000 13273 (by omega)]; decide)

theorem pc_thm_153735 : Nat.primeCounting 153735 = 14168 := primeCounting_step 140000 13736 13010 1158 count_140000 (by rw [count_shift_is_prime_eq 140000 13736 (by omega)]; decide)

theorem pc_thm_154056 : Nat.primeCounting 154056 = 14191 := primeCounting_step 140000 14057 13010 1181 count_140000 (by rw [count_shift_is_prime_eq 140000 14057 (by omega)]; decide)

theorem pc_thm_154290 : Nat.primeCounting 154290 = 14214 := primeCounting_step 140000 14291 13010 1204 count_140000 (by rw [count_shift_is_prime_eq 140000 14291 (by omega)]; decide)

theorem pc_thm_154842 : Nat.primeCounting 154842 = 14260 := primeCounting_step 140000 14843 13010 1250 count_140000 (by rw [count_shift_is_prime_eq 140000 14843 (by omega)]; decide)

theorem pc_thm_154846 : Nat.primeCounting 154846 = 14260 := primeCounting_step 140000 14847 13010 1250 count_140000 (by rw [count_shift_is_prime_eq 140000 14847 (by omega)]; decide)

theorem pc_thm_155403 : Nat.primeCounting 155403 = 14307 := primeCounting_step 140000 15404 13010 1297 count_140000 (by rw [count_shift_is_prime_eq 140000 15404 (by omega)]; decide)

theorem pc_thm_155630 : Nat.primeCounting 155630 = 14327 := primeCounting_step 140000 15631 13010 1317 count_140000 (by rw [count_shift_is_prime_eq 140000 15631 (by omega)]; decide)

theorem pc_thm_155961 : Nat.primeCounting 155961 = 14357 := primeCounting_step 140000 15962 13010 1347 count_140000 (by rw [count_shift_is_prime_eq 140000 15962 (by omega)]; decide)

theorem pc_thm_156420 : Nat.primeCounting 156420 = 14388 := primeCounting_step 140000 16421 13010 1378 count_140000 (by rw [count_shift_is_prime_eq 140000 16421 (by omega)]; decide)

theorem pc_thm_156520 : Nat.primeCounting 156520 = 14395 := primeCounting_step 140000 16521 13010 1385 count_140000 (by rw [count_shift_is_prime_eq 140000 16521 (by omega)]; decide)

theorem pc_thm_157080 : Nat.primeCounting 157080 = 14441 := primeCounting_step 140000 17081 13010 1431 count_140000 (by rw [count_shift_is_prime_eq 140000 17081 (by omega)]; decide)

theorem pc_thm_157212 : Nat.primeCounting 157212 = 14453 := primeCounting_step 140000 17213 13010 1443 count_140000 (by rw [count_shift_is_prime_eq 140000 17213 (by omega)]; decide)

theorem pc_thm_157641 : Nat.primeCounting 157641 = 14493 := primeCounting_step 140000 17642 13010 1483 count_140000 (by rw [count_shift_is_prime_eq 140000 17642 (by omega)]; decide)

theorem pc_thm_158006 : Nat.primeCounting 158006 = 14522 := primeCounting_step 140000 18007 13010 1512 count_140000 (by rw [count_shift_is_prime_eq 140000 18007 (by omega)]; decide)

theorem pc_thm_158766 : Nat.primeCounting 158766 = 14582 := primeCounting_step 140000 18767 13010 1572 count_140000 (by rw [count_shift_is_prime_eq 140000 18767 (by omega)]; decide)

theorem pc_thm_158802 : Nat.primeCounting 158802 = 14585 := primeCounting_step 140000 18803 13010 1575 count_140000 (by rw [count_shift_is_prime_eq 140000 18803 (by omega)]; decide)

theorem pc_thm_159330 : Nat.primeCounting 159330 = 14623 := primeCounting_step 140000 19331 13010 1613 count_140000 (by rw [count_shift_is_prime_eq 140000 19331 (by omega)]; decide)

theorem pc_thm_159600 : Nat.primeCounting 159600 = 14648 := primeCounting_step 140000 19601 13010 1638 count_140000 (by rw [count_shift_is_prime_eq 140000 19601 (by omega)]; decide)

theorem pc_thm_159895 : Nat.primeCounting 159895 = 14677 := primeCounting_step 140000 19896 13010 1667 count_140000 (by rw [count_shift_is_prime_eq 140000 19896 (by omega)]; decide)

theorem pc_thm_160400 : Nat.primeCounting 160400 = 14716 := primeCounting_step 160000 401 14683 33 count_160000 (by rw [count_shift_is_prime_eq 160000 401 (by omega)]; decide)

theorem pc_thm_160461 : Nat.primeCounting 160461 = 14721 := primeCounting_step 160000 462 14683 38 count_160000 (by rw [count_shift_is_prime_eq 160000 462 (by omega)]; decide)

theorem pc_thm_161028 : Nat.primeCounting 161028 = 14770 := primeCounting_step 160000 1029 14683 87 count_160000 (by rw [count_shift_is_prime_eq 160000 1029 (by omega)]; decide)

theorem pc_thm_161202 : Nat.primeCounting 161202 = 14785 := primeCounting_step 160000 1203 14683 102 count_160000 (by rw [count_shift_is_prime_eq 160000 1203 (by omega)]; decide)

theorem pc_thm_161596 : Nat.primeCounting 161596 = 14817 := primeCounting_step 160000 1597 14683 134 count_160000 (by rw [count_shift_is_prime_eq 160000 1597 (by omega)]; decide)

theorem pc_thm_162006 : Nat.primeCounting 162006 = 14852 := primeCounting_step 160000 2007 14683 169 count_160000 (by rw [count_shift_is_prime_eq 160000 2007 (by omega)]; decide)

theorem pc_thm_162735 : Nat.primeCounting 162735 = 14909 := primeCounting_step 160000 2736 14683 226 count_160000 (by rw [count_shift_is_prime_eq 160000 2736 (by omega)]; decide)

theorem pc_thm_162812 : Nat.primeCounting 162812 = 14915 := primeCounting_step 160000 2813 14683 232 count_160000 (by rw [count_shift_is_prime_eq 160000 2813 (by omega)]; decide)

theorem pc_thm_163306 : Nat.primeCounting 163306 = 14955 := primeCounting_step 160000 3307 14683 272 count_160000 (by rw [count_shift_is_prime_eq 160000 3307 (by omega)]; decide)

theorem pc_thm_163620 : Nat.primeCounting 163620 = 14981 := primeCounting_step 160000 3621 14683 298 count_160000 (by rw [count_shift_is_prime_eq 160000 3621 (by omega)]; decide)

theorem pc_thm_163878 : Nat.primeCounting 163878 = 15005 := primeCounting_step 160000 3879 14683 322 count_160000 (by rw [count_shift_is_prime_eq 160000 3879 (by omega)]; decide)

theorem pc_thm_164430 : Nat.primeCounting 164430 = 15053 := primeCounting_step 160000 4431 14683 370 count_160000 (by rw [count_shift_is_prime_eq 160000 4431 (by omega)]; decide)

theorem pc_thm_164451 : Nat.primeCounting 164451 = 15057 := primeCounting_step 160000 4452 14683 374 count_160000 (by rw [count_shift_is_prime_eq 160000 4452 (by omega)]; decide)

theorem pc_thm_165025 : Nat.primeCounting 165025 = 15094 := primeCounting_step 160000 5026 14683 411 count_160000 (by rw [count_shift_is_prime_eq 160000 5026 (by omega)]; decide)

theorem pc_thm_165242 : Nat.primeCounting 165242 = 15111 := primeCounting_step 160000 5243 14683 428 count_160000 (by rw [count_shift_is_prime_eq 160000 5243 (by omega)]; decide)

theorem pc_thm_165600 : Nat.primeCounting 165600 = 15143 := primeCounting_step 160000 5601 14683 460 count_160000 (by rw [count_shift_is_prime_eq 160000 5601 (by omega)]; decide)

theorem pc_thm_166056 : Nat.primeCounting 166056 = 15178 := primeCounting_step 160000 6057 14683 495 count_160000 (by rw [count_shift_is_prime_eq 160000 6057 (by omega)]; decide)

theorem pc_thm_166176 : Nat.primeCounting 166176 = 15185 := primeCounting_step 160000 6177 14683 502 count_160000 (by rw [count_shift_is_prime_eq 160000 6177 (by omega)]; decide)

theorem pc_thm_166753 : Nat.primeCounting 166753 = 15233 := primeCounting_step 160000 6754 14683 550 count_160000 (by rw [count_shift_is_prime_eq 160000 6754 (by omega)]; decide)

theorem pc_thm_166872 : Nat.primeCounting 166872 = 15246 := primeCounting_step 160000 6873 14683 563 count_160000 (by rw [count_shift_is_prime_eq 160000 6873 (by omega)]; decide)

theorem pc_thm_167331 : Nat.primeCounting 167331 = 15287 := primeCounting_step 160000 7332 14683 604 count_160000 (by rw [count_shift_is_prime_eq 160000 7332 (by omega)]; decide)

theorem pc_thm_167690 : Nat.primeCounting 167690 = 15316 := primeCounting_step 160000 7691 14683 633 count_160000 (by rw [count_shift_is_prime_eq 160000 7691 (by omega)]; decide)

theorem pc_thm_167910 : Nat.primeCounting 167910 = 15332 := primeCounting_step 160000 7911 14683 649 count_160000 (by rw [count_shift_is_prime_eq 160000 7911 (by omega)]; decide)

theorem pc_thm_168510 : Nat.primeCounting 168510 = 15375 := primeCounting_step 160000 8511 14683 692 count_160000 (by rw [count_shift_is_prime_eq 160000 8511 (by omega)]; decide)

theorem pc_thm_169071 : Nat.primeCounting 169071 = 15418 := primeCounting_step 160000 9072 14683 735 count_160000 (by rw [count_shift_is_prime_eq 160000 9072 (by omega)]; decide)

theorem pc_thm_169332 : Nat.primeCounting 169332 = 15440 := primeCounting_step 160000 9333 14683 757 count_160000 (by rw [count_shift_is_prime_eq 160000 9333 (by omega)]; decide)

theorem pc_thm_169653 : Nat.primeCounting 169653 = 15465 := primeCounting_step 160000 9654 14683 782 count_160000 (by rw [count_shift_is_prime_eq 160000 9654 (by omega)]; decide)

theorem pc_thm_170156 : Nat.primeCounting 170156 = 15509 := primeCounting_step 160000 10157 14683 826 count_160000 (by rw [count_shift_is_prime_eq 160000 10157 (by omega)]; decide)

theorem pc_thm_170236 : Nat.primeCounting 170236 = 15517 := primeCounting_step 160000 10237 14683 834 count_160000 (by rw [count_shift_is_prime_eq 160000 10237 (by omega)]; decide)

theorem pc_thm_170820 : Nat.primeCounting 170820 = 15570 := primeCounting_step 160000 10821 14683 887 count_160000 (by rw [count_shift_is_prime_eq 160000 10821 (by omega)]; decide)

theorem pc_thm_170982 : Nat.primeCounting 170982 = 15584 := primeCounting_step 160000 10983 14683 901 count_160000 (by rw [count_shift_is_prime_eq 160000 10983 (by omega)]; decide)

theorem pc_thm_171405 : Nat.primeCounting 171405 = 15615 := primeCounting_step 160000 11406 14683 932 count_160000 (by rw [count_shift_is_prime_eq 160000 11406 (by omega)]; decide)

theorem pc_thm_171810 : Nat.primeCounting 171810 = 15651 := primeCounting_step 160000 11811 14683 968 count_160000 (by rw [count_shift_is_prime_eq 160000 11811 (by omega)]; decide)

theorem pc_thm_171991 : Nat.primeCounting 171991 = 15665 := primeCounting_step 160000 11992 14683 982 count_160000 (by rw [count_shift_is_prime_eq 160000 11992 (by omega)]; decide)

theorem pc_thm_172578 : Nat.primeCounting 172578 = 15716 := primeCounting_step 160000 12579 14683 1033 count_160000 (by rw [count_shift_is_prime_eq 160000 12579 (by omega)]; decide)

theorem pc_thm_172640 : Nat.primeCounting 172640 = 15723 := primeCounting_step 160000 12641 14683 1040 count_160000 (by rw [count_shift_is_prime_eq 160000 12641 (by omega)]; decide)

theorem pc_thm_173166 : Nat.primeCounting 173166 = 15765 := primeCounting_step 160000 13167 14683 1082 count_160000 (by rw [count_shift_is_prime_eq 160000 13167 (by omega)]; decide)

theorem pc_thm_173472 : Nat.primeCounting 173472 = 15785 := primeCounting_step 160000 13473 14683 1102 count_160000 (by rw [count_shift_is_prime_eq 160000 13473 (by omega)]; decide)

theorem pc_thm_173755 : Nat.primeCounting 173755 = 15812 := primeCounting_step 160000 13756 14683 1129 count_160000 (by rw [count_shift_is_prime_eq 160000 13756 (by omega)]; decide)

theorem pc_thm_174306 : Nat.primeCounting 174306 = 15860 := primeCounting_step 160000 14307 14683 1177 count_160000 (by rw [count_shift_is_prime_eq 160000 14307 (by omega)]; decide)

theorem pc_thm_174345 : Nat.primeCounting 174345 = 15864 := primeCounting_step 160000 14346 14683 1181 count_160000 (by rw [count_shift_is_prime_eq 160000 14346 (by omega)]; decide)

theorem pc_thm_174936 : Nat.primeCounting 174936 = 15912 := primeCounting_step 160000 14937 14683 1229 count_160000 (by rw [count_shift_is_prime_eq 160000 14937 (by omega)]; decide)

theorem pc_thm_175142 : Nat.primeCounting 175142 = 15927 := primeCounting_step 160000 15143 14683 1244 count_160000 (by rw [count_shift_is_prime_eq 160000 15143 (by omega)]; decide)

theorem pc_thm_175528 : Nat.primeCounting 175528 = 15952 := primeCounting_step 160000 15529 14683 1269 count_160000 (by rw [count_shift_is_prime_eq 160000 15529 (by omega)]; decide)

theorem pc_thm_175980 : Nat.primeCounting 175980 = 15989 := primeCounting_step 160000 15981 14683 1306 count_160000 (by rw [count_shift_is_prime_eq 160000 15981 (by omega)]; decide)

theorem pc_thm_176121 : Nat.primeCounting 176121 = 16002 := primeCounting_step 160000 16122 14683 1319 count_160000 (by rw [count_shift_is_prime_eq 160000 16122 (by omega)]; decide)

theorem pc_thm_176715 : Nat.primeCounting 176715 = 16062 := primeCounting_step 160000 16716 14683 1379 count_160000 (by rw [count_shift_is_prime_eq 160000 16716 (by omega)]; decide)

theorem pc_thm_176820 : Nat.primeCounting 176820 = 16073 := primeCounting_step 160000 16821 14683 1390 count_160000 (by rw [count_shift_is_prime_eq 160000 16821 (by omega)]; decide)

theorem pc_thm_177310 : Nat.primeCounting 177310 = 16108 := primeCounting_step 160000 17311 14683 1425 count_160000 (by rw [count_shift_is_prime_eq 160000 17311 (by omega)]; decide)

theorem pc_thm_177662 : Nat.primeCounting 177662 = 16132 := primeCounting_step 160000 17663 14683 1449 count_160000 (by rw [count_shift_is_prime_eq 160000 17663 (by omega)]; decide)

theorem pc_thm_177906 : Nat.primeCounting 177906 = 16150 := primeCounting_step 160000 17907 14683 1467 count_160000 (by rw [count_shift_is_prime_eq 160000 17907 (by omega)]; decide)

theorem pc_thm_178503 : Nat.primeCounting 178503 = 16202 := primeCounting_step 160000 18504 14683 1519 count_160000 (by rw [count_shift_is_prime_eq 160000 18504 (by omega)]; decide)

theorem pc_thm_178506 : Nat.primeCounting 178506 = 16202 := primeCounting_step 160000 18507 14683 1519 count_160000 (by rw [count_shift_is_prime_eq 160000 18507 (by omega)]; decide)

theorem pc_thm_179101 : Nat.primeCounting 179101 = 16257 := primeCounting_step 160000 19102 14683 1574 count_160000 (by rw [count_shift_is_prime_eq 160000 19102 (by omega)]; decide)

theorem pc_thm_179352 : Nat.primeCounting 179352 = 16277 := primeCounting_step 160000 19353 14683 1594 count_160000 (by rw [count_shift_is_prime_eq 160000 19353 (by omega)]; decide)

theorem pc_thm_179700 : Nat.primeCounting 179700 = 16313 := primeCounting_step 160000 19701 14683 1630 count_160000 (by rw [count_shift_is_prime_eq 160000 19701 (by omega)]; decide)

theorem pc_thm_180200 : Nat.primeCounting 180200 = 16355 := primeCounting_step 180000 201 16342 13 count_180000 (by rw [count_shift_is_prime_eq 180000 201 (by omega)]; decide)

theorem pc_thm_180300 : Nat.primeCounting 180300 = 16366 := primeCounting_step 180000 301 16342 24 count_180000 (by rw [count_shift_is_prime_eq 180000 301 (by omega)]; decide)

theorem pc_thm_180901 : Nat.primeCounting 180901 = 16410 := primeCounting_step 180000 902 16342 68 count_180000 (by rw [count_shift_is_prime_eq 180000 902 (by omega)]; decide)

theorem pc_thm_181050 : Nat.primeCounting 181050 = 16418 := primeCounting_step 180000 1051 16342 76 count_180000 (by rw [count_shift_is_prime_eq 180000 1051 (by omega)]; decide)

theorem pc_thm_181503 : Nat.primeCounting 181503 = 16451 := primeCounting_step 180000 1504 16342 109 count_180000 (by rw [count_shift_is_prime_eq 180000 1504 (by omega)]; decide)

theorem pc_thm_181902 : Nat.primeCounting 181902 = 16482 := primeCounting_step 180000 1903 16342 140 count_180000 (by rw [count_shift_is_prime_eq 180000 1903 (by omega)]; decide)

theorem pc_thm_182106 : Nat.primeCounting 182106 = 16503 := primeCounting_step 180000 2107 16342 161 count_180000 (by rw [count_shift_is_prime_eq 180000 2107 (by omega)]; decide)

theorem pc_thm_182710 : Nat.primeCounting 182710 = 16558 := primeCounting_step 180000 2711 16342 216 count_180000 (by rw [count_shift_is_prime_eq 180000 2711 (by omega)]; decide)

theorem pc_thm_182756 : Nat.primeCounting 182756 = 16561 := primeCounting_step 180000 2757 16342 219 count_180000 (by rw [count_shift_is_prime_eq 180000 2757 (by omega)]; decide)

theorem pc_thm_183315 : Nat.primeCounting 183315 = 16604 := primeCounting_step 180000 3316 16342 262 count_180000 (by rw [count_shift_is_prime_eq 180000 3316 (by omega)]; decide)

theorem pc_thm_183612 : Nat.primeCounting 183612 = 16636 := primeCounting_step 180000 3613 16342 294 count_180000 (by rw [count_shift_is_prime_eq 180000 3613 (by omega)]; decide)

theorem pc_thm_183921 : Nat.primeCounting 183921 = 16656 := primeCounting_step 180000 3922 16342 314 count_180000 (by rw [count_shift_is_prime_eq 180000 3922 (by omega)]; decide)

theorem pc_thm_184470 : Nat.primeCounting 184470 = 16700 := primeCounting_step 180000 4471 16342 358 count_180000 (by rw [count_shift_is_prime_eq 180000 4471 (by omega)]; decide)

theorem pc_thm_184528 : Nat.primeCounting 184528 = 16706 := primeCounting_step 180000 4529 16342 364 count_180000 (by rw [count_shift_is_prime_eq 180000 4529 (by omega)]; decide)

theorem pc_thm_185136 : Nat.primeCounting 185136 = 16757 := primeCounting_step 180000 5137 16342 415 count_180000 (by rw [count_shift_is_prime_eq 180000 5137 (by omega)]; decide)

theorem pc_thm_185330 : Nat.primeCounting 185330 = 16775 := primeCounting_step 180000 5331 16342 433 count_180000 (by rw [count_shift_is_prime_eq 180000 5331 (by omega)]; decide)

theorem pc_thm_185745 : Nat.primeCounting 185745 = 16810 := primeCounting_step 180000 5746 16342 468 count_180000 (by rw [count_shift_is_prime_eq 180000 5746 (by omega)]; decide)

theorem pc_thm_186192 : Nat.primeCounting 186192 = 16855 := primeCounting_step 180000 6193 16342 513 count_180000 (by rw [count_shift_is_prime_eq 180000 6193 (by omega)]; decide)

theorem pc_thm_186355 : Nat.primeCounting 186355 = 16869 := primeCounting_step 180000 6356 16342 527 count_180000 (by rw [count_shift_is_prime_eq 180000 6356 (by omega)]; decide)

theorem pc_thm_186966 : Nat.primeCounting 186966 = 16915 := primeCounting_step 180000 6967 16342 573 count_180000 (by rw [count_shift_is_prime_eq 180000 6967 (by omega)]; decide)

theorem pc_thm_187056 : Nat.primeCounting 187056 = 16920 := primeCounting_step 180000 7057 16342 578 count_180000 (by rw [count_shift_is_prime_eq 180000 7057 (by omega)]; decide)

theorem pc_thm_187578 : Nat.primeCounting 187578 = 16970 := primeCounting_step 180000 7579 16342 628 count_180000 (by rw [count_shift_is_prime_eq 180000 7579 (by omega)]; decide)

theorem pc_thm_187922 : Nat.primeCounting 187922 = 16996 := primeCounting_step 180000 7923 16342 654 count_180000 (by rw [count_shift_is_prime_eq 180000 7923 (by omega)]; decide)

theorem pc_thm_188191 : Nat.primeCounting 188191 = 17014 := primeCounting_step 180000 8192 16342 672 count_180000 (by rw [count_shift_is_prime_eq 180000 8192 (by omega)]; decide)

theorem pc_thm_188790 : Nat.primeCounting 188790 = 17062 := primeCounting_step 180000 8791 16342 720 count_180000 (by rw [count_shift_is_prime_eq 180000 8791 (by omega)]; decide)

theorem pc_thm_188805 : Nat.primeCounting 188805 = 17064 := primeCounting_step 180000 8806 16342 722 count_180000 (by rw [count_shift_is_prime_eq 180000 8806 (by omega)]; decide)

theorem pc_thm_189420 : Nat.primeCounting 189420 = 17115 := primeCounting_step 180000 9421 16342 773 count_180000 (by rw [count_shift_is_prime_eq 180000 9421 (by omega)]; decide)

theorem pc_thm_189660 : Nat.primeCounting 189660 = 17139 := primeCounting_step 180000 9661 16342 797 count_180000 (by rw [count_shift_is_prime_eq 180000 9661 (by omega)]; decide)

theorem pc_thm_190036 : Nat.primeCounting 190036 = 17172 := primeCounting_step 180000 10037 16342 830 count_180000 (by rw [count_shift_is_prime_eq 180000 10037 (by omega)]; decide)

theorem pc_thm_190532 : Nat.primeCounting 190532 = 17204 := primeCounting_step 180000 10533 16342 862 count_180000 (by rw [count_shift_is_prime_eq 180000 10533 (by omega)]; decide)

theorem pc_thm_190653 : Nat.primeCounting 190653 = 17216 := primeCounting_step 180000 10654 16342 874 count_180000 (by rw [count_shift_is_prime_eq 180000 10654 (by omega)]; decide)

theorem pc_thm_191271 : Nat.primeCounting 191271 = 17267 := primeCounting_step 180000 11272 16342 925 count_180000 (by rw [count_shift_is_prime_eq 180000 11272 (by omega)]; decide)

theorem pc_thm_191406 : Nat.primeCounting 191406 = 17273 := primeCounting_step 180000 11407 16342 931 count_180000 (by rw [count_shift_is_prime_eq 180000 11407 (by omega)]; decide)

theorem pc_thm_191890 : Nat.primeCounting 191890 = 17318 := primeCounting_step 180000 11891 16342 976 count_180000 (by rw [count_shift_is_prime_eq 180000 11891 (by omega)]; decide)

theorem pc_thm_192282 : Nat.primeCounting 192282 = 17352 := primeCounting_step 180000 12283 16342 1010 count_180000 (by rw [count_shift_is_prime_eq 180000 12283 (by omega)]; decide)

theorem pc_thm_192510 : Nat.primeCounting 192510 = 17369 := primeCounting_step 180000 12511 16342 1027 count_180000 (by rw [count_shift_is_prime_eq 180000 12511 (by omega)]; decide)

theorem pc_thm_193131 : Nat.primeCounting 193131 = 17424 := primeCounting_step 180000 13132 16342 1082 count_180000 (by rw [count_shift_is_prime_eq 180000 13132 (by omega)]; decide)

theorem pc_thm_193160 : Nat.primeCounting 193160 = 17428 := primeCounting_step 180000 13161 16342 1086 count_180000 (by rw [count_shift_is_prime_eq 180000 13161 (by omega)]; decide)

theorem pc_thm_193753 : Nat.primeCounting 193753 = 17475 := primeCounting_step 180000 13754 16342 1133 count_180000 (by rw [count_shift_is_prime_eq 180000 13754 (by omega)]; decide)

theorem pc_thm_194040 : Nat.primeCounting 194040 = 17502 := primeCounting_step 180000 14041 16342 1160 count_180000 (by rw [count_shift_is_prime_eq 180000 14041 (by omega)]; decide)

theorem pc_thm_194376 : Nat.primeCounting 194376 = 17525 := primeCounting_step 180000 14377 16342 1183 count_180000 (by rw [count_shift_is_prime_eq 180000 14377 (by omega)]; decide)

theorem pc_thm_194922 : Nat.primeCounting 194922 = 17568 := primeCounting_step 180000 14923 16342 1226 count_180000 (by rw [count_shift_is_prime_eq 180000 14923 (by omega)]; decide)

theorem pc_thm_195000 : Nat.primeCounting 195000 = 17573 := primeCounting_step 180000 15001 16342 1231 count_180000 (by rw [count_shift_is_prime_eq 180000 15001 (by omega)]; decide)

theorem pc_thm_195625 : Nat.primeCounting 195625 = 17625 := primeCounting_step 180000 15626 16342 1283 count_180000 (by rw [count_shift_is_prime_eq 180000 15626 (by omega)]; decide)

theorem pc_thm_195806 : Nat.primeCounting 195806 = 17640 := primeCounting_step 180000 15807 16342 1298 count_180000 (by rw [count_shift_is_prime_eq 180000 15807 (by omega)]; decide)

theorem pc_thm_196251 : Nat.primeCounting 196251 = 17678 := primeCounting_step 180000 16252 16342 1336 count_180000 (by rw [count_shift_is_prime_eq 180000 16252 (by omega)]; decide)

theorem pc_thm_196692 : Nat.primeCounting 196692 = 17711 := primeCounting_step 180000 16693 16342 1369 count_180000 (by rw [count_shift_is_prime_eq 180000 16693 (by omega)]; decide)

theorem pc_thm_196878 : Nat.primeCounting 196878 = 17726 := primeCounting_step 180000 16879 16342 1384 count_180000 (by rw [count_shift_is_prime_eq 180000 16879 (by omega)]; decide)

theorem pc_thm_197506 : Nat.primeCounting 197506 = 17778 := primeCounting_step 180000 17507 16342 1436 count_180000 (by rw [count_shift_is_prime_eq 180000 17507 (by omega)]; decide)

theorem pc_thm_197580 : Nat.primeCounting 197580 = 17785 := primeCounting_step 180000 17581 16342 1443 count_180000 (by rw [count_shift_is_prime_eq 180000 17581 (by omega)]; decide)

theorem pc_thm_198135 : Nat.primeCounting 198135 = 17832 := primeCounting_step 180000 18136 16342 1490 count_180000 (by rw [count_shift_is_prime_eq 180000 18136 (by omega)]; decide)

theorem pc_thm_198470 : Nat.primeCounting 198470 = 17862 := primeCounting_step 180000 18471 16342 1520 count_180000 (by rw [count_shift_is_prime_eq 180000 18471 (by omega)]; decide)

theorem pc_thm_198765 : Nat.primeCounting 198765 = 17884 := primeCounting_step 180000 18766 16342 1542 count_180000 (by rw [count_shift_is_prime_eq 180000 18766 (by omega)]; decide)

theorem pc_thm_199362 : Nat.primeCounting 199362 = 17930 := primeCounting_step 180000 19363 16342 1588 count_180000 (by rw [count_shift_is_prime_eq 180000 19363 (by omega)]; decide)

theorem pc_thm_199396 : Nat.primeCounting 199396 = 17932 := primeCounting_step 180000 19397 16342 1590 count_180000 (by rw [count_shift_is_prime_eq 180000 19397 (by omega)]; decide)

theorem pc_thm_200028 : Nat.primeCounting 200028 = 17988 := primeCounting_step 200000 29 17984 4 count_200000 (by rw [count_shift_is_prime_eq 200000 29 (by omega)]; decide)

theorem pc_thm_200256 : Nat.primeCounting 200256 = 18005 := primeCounting_step 200000 257 17984 21 count_200000 (by rw [count_shift_is_prime_eq 200000 257 (by omega)]; decide)

theorem pc_thm_201152 : Nat.primeCounting 201152 = 18073 := primeCounting_step 200000 1153 17984 89 count_200000 (by rw [count_shift_is_prime_eq 200000 1153 (by omega)]; decide)

theorem pc_thm_201295 : Nat.primeCounting 201295 = 18084 := primeCounting_step 200000 1296 17984 100 count_200000 (by rw [count_shift_is_prime_eq 200000 1296 (by omega)]; decide)

theorem pc_thm_201930 : Nat.primeCounting 201930 = 18141 := primeCounting_step 200000 1931 17984 157 count_200000 (by rw [count_shift_is_prime_eq 200000 1931 (by omega)]; decide)

theorem pc_thm_202050 : Nat.primeCounting 202050 = 18152 := primeCounting_step 200000 2051 17984 168 count_200000 (by rw [count_shift_is_prime_eq 200000 2051 (by omega)]; decide)

theorem pc_thm_202566 : Nat.primeCounting 202566 = 18188 := primeCounting_step 200000 2567 17984 204 count_200000 (by rw [count_shift_is_prime_eq 200000 2567 (by omega)]; decide)

theorem pc_thm_202950 : Nat.primeCounting 202950 = 18221 := primeCounting_step 200000 2951 17984 237 count_200000 (by rw [count_shift_is_prime_eq 200000 2951 (by omega)]; decide)

theorem pc_thm_203203 : Nat.primeCounting 203203 = 18236 := primeCounting_step 200000 3204 17984 252 count_200000 (by rw [count_shift_is_prime_eq 200000 3204 (by omega)]; decide)

theorem pc_thm_203841 : Nat.primeCounting 203841 = 18289 := primeCounting_step 200000 3842 17984 305 count_200000 (by rw [count_shift_is_prime_eq 200000 3842 (by omega)]; decide)

theorem pc_thm_203852 : Nat.primeCounting 203852 = 18290 := primeCounting_step 200000 3853 17984 306 count_200000 (by rw [count_shift_is_prime_eq 200000 3853 (by omega)]; decide)

theorem pc_thm_204480 : Nat.primeCounting 204480 = 18341 := primeCounting_step 200000 4481 17984 357 count_200000 (by rw [count_shift_is_prime_eq 200000 4481 (by omega)]; decide)

theorem pc_thm_204756 : Nat.primeCounting 204756 = 18363 := primeCounting_step 200000 4757 17984 379 count_200000 (by rw [count_shift_is_prime_eq 200000 4757 (by omega)]; decide)

theorem pc_thm_205120 : Nat.primeCounting 205120 = 18391 := primeCounting_step 200000 5121 17984 407 count_200000 (by rw [count_shift_is_prime_eq 200000 5121 (by omega)]; decide)

theorem pc_thm_205662 : Nat.primeCounting 205662 = 18442 := primeCounting_step 200000 5663 17984 458 count_200000 (by rw [count_shift_is_prime_eq 200000 5663 (by omega)]; decide)

theorem pc_thm_205761 : Nat.primeCounting 205761 = 18446 := primeCounting_step 200000 5762 17984 462 count_200000 (by rw [count_shift_is_prime_eq 200000 5762 (by omega)]; decide)

theorem pc_thm_206403 : Nat.primeCounting 206403 = 18502 := primeCounting_step 200000 6404 17984 518 count_200000 (by rw [count_shift_is_prime_eq 200000 6404 (by omega)]; decide)

theorem pc_thm_206570 : Nat.primeCounting 206570 = 18517 := primeCounting_step 200000 6571 17984 533 count_200000 (by rw [count_shift_is_prime_eq 200000 6571 (by omega)]; decide)

theorem pc_thm_207046 : Nat.primeCounting 207046 = 18552 := primeCounting_step 200000 7047 17984 568 count_200000 (by rw [count_shift_is_prime_eq 200000 7047 (by omega)]; decide)

theorem pc_thm_207480 : Nat.primeCounting 207480 = 18588 := primeCounting_step 200000 7481 17984 604 count_200000 (by rw [count_shift_is_prime_eq 200000 7481 (by omega)]; decide)

theorem pc_thm_207690 : Nat.primeCounting 207690 = 18611 := primeCounting_step 200000 7691 17984 627 count_200000 (by rw [count_shift_is_prime_eq 200000 7691 (by omega)]; decide)

theorem pc_thm_208335 : Nat.primeCounting 208335 = 18664 := primeCounting_step 200000 8336 17984 680 count_200000 (by rw [count_shift_is_prime_eq 200000 8336 (by omega)]; decide)

theorem pc_thm_208392 : Nat.primeCounting 208392 = 18669 := primeCounting_step 200000 8393 17984 685 count_200000 (by rw [count_shift_is_prime_eq 200000 8393 (by omega)]; decide)

theorem pc_thm_208981 : Nat.primeCounting 208981 = 18716 := primeCounting_step 200000 8982 17984 732 count_200000 (by rw [count_shift_is_prime_eq 200000 8982 (by omega)]; decide)

theorem pc_thm_209306 : Nat.primeCounting 209306 = 18743 := primeCounting_step 200000 9307 17984 759 count_200000 (by rw [count_shift_is_prime_eq 200000 9307 (by omega)]; decide)

theorem pc_thm_209628 : Nat.primeCounting 209628 = 18774 := primeCounting_step 200000 9629 17984 790 count_200000 (by rw [count_shift_is_prime_eq 200000 9629 (by omega)]; decide)

theorem pc_thm_210222 : Nat.primeCounting 210222 = 18828 := primeCounting_step 200000 10223 17984 844 count_200000 (by rw [count_shift_is_prime_eq 200000 10223 (by omega)]; decide)

theorem pc_thm_210276 : Nat.primeCounting 210276 = 18834 := primeCounting_step 200000 10277 17984 850 count_200000 (by rw [count_shift_is_prime_eq 200000 10277 (by omega)]; decide)

theorem pc_thm_210925 : Nat.primeCounting 210925 = 18887 := primeCounting_step 200000 10926 17984 903 count_200000 (by rw [count_shift_is_prime_eq 200000 10926 (by omega)]; decide)

theorem pc_thm_211140 : Nat.primeCounting 211140 = 18902 := primeCounting_step 200000 11141 17984 918 count_200000 (by rw [count_shift_is_prime_eq 200000 11141 (by omega)]; decide)

theorem pc_thm_211575 : Nat.primeCounting 211575 = 18940 := primeCounting_step 200000 11576 17984 956 count_200000 (by rw [count_shift_is_prime_eq 200000 11576 (by omega)]; decide)

theorem pc_thm_212060 : Nat.primeCounting 212060 = 18980 := primeCounting_step 200000 12061 17984 996 count_200000 (by rw [count_shift_is_prime_eq 200000 12061 (by omega)]; decide)

theorem pc_thm_212226 : Nat.primeCounting 212226 = 18992 := primeCounting_step 200000 12227 17984 1008 count_200000 (by rw [count_shift_is_prime_eq 200000 12227 (by omega)]; decide)

theorem pc_thm_212878 : Nat.primeCounting 212878 = 19036 := primeCounting_step 200000 12879 17984 1052 count_200000 (by rw [count_shift_is_prime_eq 200000 12879 (by omega)]; decide)

theorem pc_thm_212982 : Nat.primeCounting 212982 = 19044 := primeCounting_step 200000 12983 17984 1060 count_200000 (by rw [count_shift_is_prime_eq 200000 12983 (by omega)]; decide)

theorem pc_thm_213531 : Nat.primeCounting 213531 = 19090 := primeCounting_step 200000 13532 17984 1106 count_200000 (by rw [count_shift_is_prime_eq 200000 13532 (by omega)]; decide)

theorem pc_thm_213906 : Nat.primeCounting 213906 = 19118 := primeCounting_step 200000 13907 17984 1134 count_200000 (by rw [count_shift_is_prime_eq 200000 13907 (by omega)]; decide)

theorem pc_thm_214185 : Nat.primeCounting 214185 = 19145 := primeCounting_step 200000 14186 17984 1161 count_200000 (by rw [count_shift_is_prime_eq 200000 14186 (by omega)]; decide)

theorem pc_thm_214832 : Nat.primeCounting 214832 = 19202 := primeCounting_step 200000 14833 17984 1218 count_200000 (by rw [count_shift_is_prime_eq 200000 14833 (by omega)]; decide)

theorem pc_thm_214840 : Nat.primeCounting 214840 = 19202 := primeCounting_step 200000 14841 17984 1218 count_200000 (by rw [count_shift_is_prime_eq 200000 14841 (by omega)]; decide)

theorem pc_thm_215496 : Nat.primeCounting 215496 = 19249 := primeCounting_step 200000 15497 17984 1265 count_200000 (by rw [count_shift_is_prime_eq 200000 15497 (by omega)]; decide)

theorem pc_thm_215760 : Nat.primeCounting 215760 = 19267 := primeCounting_step 200000 15761 17984 1283 count_200000 (by rw [count_shift_is_prime_eq 200000 15761 (by omega)]; decide)

theorem pc_thm_216153 : Nat.primeCounting 216153 = 19299 := primeCounting_step 200000 16154 17984 1315 count_200000 (by rw [count_shift_is_prime_eq 200000 16154 (by omega)]; decide)

theorem pc_thm_216690 : Nat.primeCounting 216690 = 19337 := primeCounting_step 200000 16691 17984 1353 count_200000 (by rw [count_shift_is_prime_eq 200000 16691 (by omega)]; decide)

theorem pc_thm_216811 : Nat.primeCounting 216811 = 19349 := primeCounting_step 200000 16812 17984 1365 count_200000 (by rw [count_shift_is_prime_eq 200000 16812 (by omega)]; decide)

theorem pc_thm_217470 : Nat.primeCounting 217470 = 19406 := primeCounting_step 200000 17471 17984 1422 count_200000 (by rw [count_shift_is_prime_eq 200000 17471 (by omega)]; decide)

theorem pc_thm_217622 : Nat.primeCounting 217622 = 19416 := primeCounting_step 200000 17623 17984 1432 count_200000 (by rw [count_shift_is_prime_eq 200000 17623 (by omega)]; decide)

theorem pc_thm_218130 : Nat.primeCounting 218130 = 19454 := primeCounting_step 200000 18131 17984 1470 count_200000 (by rw [count_shift_is_prime_eq 200000 18131 (by omega)]; decide)

theorem pc_thm_218556 : Nat.primeCounting 218556 = 19488 := primeCounting_step 200000 18557 17984 1504 count_200000 (by rw [count_shift_is_prime_eq 200000 18557 (by omega)]; decide)

theorem pc_thm_218791 : Nat.primeCounting 218791 = 19508 := primeCounting_step 200000 18792 17984 1524 count_200000 (by rw [count_shift_is_prime_eq 200000 18792 (by omega)]; decide)

theorem pc_thm_219453 : Nat.primeCounting 219453 = 19563 := primeCounting_step 200000 19454 17984 1579 count_200000 (by rw [count_shift_is_prime_eq 200000 19454 (by omega)]; decide)

theorem pc_thm_219492 : Nat.primeCounting 219492 = 19566 := primeCounting_step 200000 19493 17984 1582 count_200000 (by rw [count_shift_is_prime_eq 200000 19493 (by omega)]; decide)

theorem pc_thm_220116 : Nat.primeCounting 220116 = 19624 := primeCounting_step 220000 117 19618 6 count_220000 (by rw [count_shift_is_prime_eq 220000 117 (by omega)]; decide)

theorem pc_thm_220430 : Nat.primeCounting 220430 = 19650 := primeCounting_step 220000 431 19618 32 count_220000 (by rw [count_shift_is_prime_eq 220000 431 (by omega)]; decide)

theorem pc_thm_220780 : Nat.primeCounting 220780 = 19675 := primeCounting_step 220000 781 19618 57 count_220000 (by rw [count_shift_is_prime_eq 220000 781 (by omega)]; decide)

theorem pc_thm_221370 : Nat.primeCounting 221370 = 19724 := primeCounting_step 220000 1371 19618 106 count_220000 (by rw [count_shift_is_prime_eq 220000 1371 (by omega)]; decide)

theorem pc_thm_221445 : Nat.primeCounting 221445 = 19729 := primeCounting_step 220000 1446 19618 111 count_220000 (by rw [count_shift_is_prime_eq 220000 1446 (by omega)]; decide)

theorem pc_thm_222111 : Nat.primeCounting 222111 = 19787 := primeCounting_step 220000 2112 19618 169 count_220000 (by rw [count_shift_is_prime_eq 220000 2112 (by omega)]; decide)

theorem pc_thm_222312 : Nat.primeCounting 222312 = 19802 := primeCounting_step 220000 2313 19618 184 count_220000 (by rw [count_shift_is_prime_eq 220000 2313 (by omega)]; decide)

theorem pc_thm_222778 : Nat.primeCounting 222778 = 19835 := primeCounting_step 220000 2779 19618 217 count_220000 (by rw [count_shift_is_prime_eq 220000 2779 (by omega)]; decide)

theorem pc_thm_223256 : Nat.primeCounting 223256 = 19880 := primeCounting_step 220000 3257 19618 262 count_220000 (by rw [count_shift_is_prime_eq 220000 3257 (by omega)]; decide)

theorem pc_thm_223446 : Nat.primeCounting 223446 = 19899 := primeCounting_step 220000 3447 19618 281 count_220000 (by rw [count_shift_is_prime_eq 220000 3447 (by omega)]; decide)

theorem pc_thm_224115 : Nat.primeCounting 224115 = 19947 := primeCounting_step 220000 4116 19618 329 count_220000 (by rw [count_shift_is_prime_eq 220000 4116 (by omega)]; decide)

theorem pc_thm_224202 : Nat.primeCounting 224202 = 19955 := primeCounting_step 220000 4203 19618 337 count_220000 (by rw [count_shift_is_prime_eq 220000 4203 (by omega)]; decide)

theorem pc_thm_224785 : Nat.primeCounting 224785 = 20003 := primeCounting_step 220000 4786 19618 385 count_220000 (by rw [count_shift_is_prime_eq 220000 4786 (by omega)]; decide)

theorem pc_thm_225150 : Nat.primeCounting 225150 = 20032 := primeCounting_step 220000 5151 19618 414 count_220000 (by rw [count_shift_is_prime_eq 220000 5151 (by omega)]; decide)

theorem pc_thm_225456 : Nat.primeCounting 225456 = 20057 := primeCounting_step 220000 5457 19618 439 count_220000 (by rw [count_shift_is_prime_eq 220000 5457 (by omega)]; decide)

theorem pc_thm_226100 : Nat.primeCounting 226100 = 20111 := primeCounting_step 220000 6101 19618 493 count_220000 (by rw [count_shift_is_prime_eq 220000 6101 (by omega)]; decide)

theorem pc_thm_226128 : Nat.primeCounting 226128 = 20113 := primeCounting_step 220000 6129 19618 495 count_220000 (by rw [count_shift_is_prime_eq 220000 6129 (by omega)]; decide)

theorem pc_thm_226801 : Nat.primeCounting 226801 = 20167 := primeCounting_step 220000 6802 19618 549 count_220000 (by rw [count_shift_is_prime_eq 220000 6802 (by omega)]; decide)

theorem pc_thm_227052 : Nat.primeCounting 227052 = 20182 := primeCounting_step 220000 7053 19618 564 count_220000 (by rw [count_shift_is_prime_eq 220000 7053 (by omega)]; decide)

theorem pc_thm_227475 : Nat.primeCounting 227475 = 20220 := primeCounting_step 220000 7476 19618 602 count_220000 (by rw [count_shift_is_prime_eq 220000 7476 (by omega)]; decide)

theorem pc_thm_228006 : Nat.primeCounting 228006 = 20260 := primeCounting_step 220000 8007 19618 642 count_220000 (by rw [count_shift_is_prime_eq 220000 8007 (by omega)]; decide)

theorem pc_thm_228150 : Nat.primeCounting 228150 = 20271 := primeCounting_step 220000 8151 19618 653 count_220000 (by rw [count_shift_is_prime_eq 220000 8151 (by omega)]; decide)

theorem pc_thm_228826 : Nat.primeCounting 228826 = 20330 := primeCounting_step 220000 8827 19618 712 count_220000 (by rw [count_shift_is_prime_eq 220000 8827 (by omega)]; decide)

theorem pc_thm_228962 : Nat.primeCounting 228962 = 20347 := primeCounting_step 220000 8963 19618 729 count_220000 (by rw [count_shift_is_prime_eq 220000 8963 (by omega)]; decide)

theorem pc_thm_229503 : Nat.primeCounting 229503 = 20389 := primeCounting_step 220000 9504 19618 771 count_220000 (by rw [count_shift_is_prime_eq 220000 9504 (by omega)]; decide)

theorem pc_thm_229920 : Nat.primeCounting 229920 = 20430 := primeCounting_step 220000 9921 19618 812 count_220000 (by rw [count_shift_is_prime_eq 220000 9921 (by omega)]; decide)

theorem pc_thm_230181 : Nat.primeCounting 230181 = 20452 := primeCounting_step 220000 10182 19618 834 count_220000 (by rw [count_shift_is_prime_eq 220000 10182 (by omega)]; decide)

theorem pc_thm_230860 : Nat.primeCounting 230860 = 20509 := primeCounting_step 220000 10861 19618 891 count_220000 (by rw [count_shift_is_prime_eq 220000 10861 (by omega)]; decide)

theorem pc_thm_230880 : Nat.primeCounting 230880 = 20512 := primeCounting_step 220000 10881 19618 894 count_220000 (by rw [count_shift_is_prime_eq 220000 10881 (by omega)]; decide)

theorem pc_thm_231540 : Nat.primeCounting 231540 = 20563 := primeCounting_step 220000 11541 19618 945 count_220000 (by rw [count_shift_is_prime_eq 220000 11541 (by omega)]; decide)

theorem pc_thm_231842 : Nat.primeCounting 231842 = 20588 := primeCounting_step 220000 11843 19618 970 count_220000 (by rw [count_shift_is_prime_eq 220000 11843 (by omega)]; decide)

theorem pc_thm_232221 : Nat.primeCounting 232221 = 20618 := primeCounting_step 220000 12222 19618 1000 count_220000 (by rw [count_shift_is_prime_eq 220000 12222 (by omega)]; decide)

theorem pc_thm_232806 : Nat.primeCounting 232806 = 20659 := primeCounting_step 220000 12807 19618 1041 count_220000 (by rw [count_shift_is_prime_eq 220000 12807 (by omega)]; decide)

theorem pc_thm_232903 : Nat.primeCounting 232903 = 20669 := primeCounting_step 220000 12904 19618 1051 count_220000 (by rw [count_shift_is_prime_eq 220000 12904 (by omega)]; decide)

theorem pc_thm_233586 : Nat.primeCounting 233586 = 20715 := primeCounting_step 220000 13587 19618 1097 count_220000 (by rw [count_shift_is_prime_eq 220000 13587 (by omega)]; decide)

theorem pc_thm_233772 : Nat.primeCounting 233772 = 20731 := primeCounting_step 220000 13773 19618 1113 count_220000 (by rw [count_shift_is_prime_eq 220000 13773 (by omega)]; decide)

theorem pc_thm_234270 : Nat.primeCounting 234270 = 20769 := primeCounting_step 220000 14271 19618 1151 count_220000 (by rw [count_shift_is_prime_eq 220000 14271 (by omega)]; decide)

theorem pc_thm_234740 : Nat.primeCounting 234740 = 20808 := primeCounting_step 220000 14741 19618 1190 count_220000 (by rw [count_shift_is_prime_eq 220000 14741 (by omega)]; decide)

theorem pc_thm_234955 : Nat.primeCounting 234955 = 20827 := primeCounting_step 220000 14956 19618 1209 count_220000 (by rw [count_shift_is_prime_eq 220000 14956 (by omega)]; decide)

theorem pc_thm_235641 : Nat.primeCounting 235641 = 20880 := primeCounting_step 220000 15642 19618 1262 count_220000 (by rw [count_shift_is_prime_eq 220000 15642 (by omega)]; decide)

theorem pc_thm_235710 : Nat.primeCounting 235710 = 20885 := primeCounting_step 220000 15711 19618 1267 count_220000 (by rw [count_shift_is_prime_eq 220000 15711 (by omega)]; decide)

theorem pc_thm_236328 : Nat.primeCounting 236328 = 20928 := primeCounting_step 220000 16329 19618 1310 count_220000 (by rw [count_shift_is_prime_eq 220000 16329 (by omega)]; decide)

theorem pc_thm_236682 : Nat.primeCounting 236682 = 20955 := primeCounting_step 220000 16683 19618 1337 count_220000 (by rw [count_shift_is_prime_eq 220000 16683 (by omega)]; decide)

theorem pc_thm_237016 : Nat.primeCounting 237016 = 20983 := primeCounting_step 220000 17017 19618 1365 count_220000 (by rw [count_shift_is_prime_eq 220000 17017 (by omega)]; decide)

theorem pc_thm_237656 : Nat.primeCounting 237656 = 21027 := primeCounting_step 220000 17657 19618 1409 count_220000 (by rw [count_shift_is_prime_eq 220000 17657 (by omega)]; decide)

theorem pc_thm_237705 : Nat.primeCounting 237705 = 21032 := primeCounting_step 220000 17706 19618 1414 count_220000 (by rw [count_shift_is_prime_eq 220000 17706 (by omega)]; decide)

theorem pc_thm_238395 : Nat.primeCounting 238395 = 21093 := primeCounting_step 220000 18396 19618 1475 count_220000 (by rw [count_shift_is_prime_eq 220000 18396 (by omega)]; decide)

theorem pc_thm_238632 : Nat.primeCounting 238632 = 21110 := primeCounting_step 220000 18633 19618 1492 count_220000 (by rw [count_shift_is_prime_eq 220000 18633 (by omega)]; decide)

theorem pc_thm_239086 : Nat.primeCounting 239086 = 21148 := primeCounting_step 220000 19087 19618 1530 count_220000 (by rw [count_shift_is_prime_eq 220000 19087 (by omega)]; decide)

theorem pc_thm_239610 : Nat.primeCounting 239610 = 21190 := primeCounting_step 220000 19611 19618 1572 count_220000 (by rw [count_shift_is_prime_eq 220000 19611 (by omega)]; decide)

theorem pc_thm_239778 : Nat.primeCounting 239778 = 21202 := primeCounting_step 220000 19779 19618 1584 count_220000 (by rw [count_shift_is_prime_eq 220000 19779 (by omega)]; decide)

theorem pc_thm_240471 : Nat.primeCounting 240471 = 21258 := primeCounting_step 240000 472 21221 37 count_240000 (by rw [count_shift_is_prime_eq 240000 472 (by omega)]; decide)

theorem pc_thm_240590 : Nat.primeCounting 240590 = 21268 := primeCounting_step 240000 591 21221 47 count_240000 (by rw [count_shift_is_prime_eq 240000 591 (by omega)]; decide)

theorem pc_thm_241165 : Nat.primeCounting 241165 = 21314 := primeCounting_step 240000 1166 21221 93 count_240000 (by rw [count_shift_is_prime_eq 240000 1166 (by omega)]; decide)

theorem pc_thm_241572 : Nat.primeCounting 241572 = 21351 := primeCounting_step 240000 1573 21221 130 count_240000 (by rw [count_shift_is_prime_eq 240000 1573 (by omega)]; decide)

theorem pc_thm_241860 : Nat.primeCounting 241860 = 21375 := primeCounting_step 240000 1861 21221 154 count_240000 (by rw [count_shift_is_prime_eq 240000 1861 (by omega)]; decide)

theorem pc_thm_242556 : Nat.primeCounting 242556 = 21435 := primeCounting_step 240000 2557 21221 214 count_240000 (by rw [count_shift_is_prime_eq 240000 2557 (by omega)]; decide)

theorem pc_thm_243253 : Nat.primeCounting 243253 = 21488 := primeCounting_step 240000 3254 21221 267 count_240000 (by rw [count_shift_is_prime_eq 240000 3254 (by omega)]; decide)

theorem pc_thm_243542 : Nat.primeCounting 243542 = 21511 := primeCounting_step 240000 3543 21221 290 count_240000 (by rw [count_shift_is_prime_eq 240000 3543 (by omega)]; decide)

theorem pc_thm_243951 : Nat.primeCounting 243951 = 21542 := primeCounting_step 240000 3952 21221 321 count_240000 (by rw [count_shift_is_prime_eq 240000 3952 (by omega)]; decide)

theorem pc_thm_244530 : Nat.primeCounting 244530 = 21593 := primeCounting_step 240000 4531 21221 372 count_240000 (by rw [count_shift_is_prime_eq 240000 4531 (by omega)]; decide)

theorem pc_thm_244650 : Nat.primeCounting 244650 = 21605 := primeCounting_step 240000 4651 21221 384 count_240000 (by rw [count_shift_is_prime_eq 240000 4651 (by omega)]; decide)

theorem pc_thm_245350 : Nat.primeCounting 245350 = 21659 := primeCounting_step 240000 5351 21221 438 count_240000 (by rw [count_shift_is_prime_eq 240000 5351 (by omega)]; decide)

theorem pc_thm_245520 : Nat.primeCounting 245520 = 21672 := primeCounting_step 240000 5521 21221 451 count_240000 (by rw [count_shift_is_prime_eq 240000 5521 (by omega)]; decide)

theorem pc_thm_246051 : Nat.primeCounting 246051 = 21716 := primeCounting_step 240000 6052 21221 495 count_240000 (by rw [count_shift_is_prime_eq 240000 6052 (by omega)]; decide)

theorem pc_thm_246512 : Nat.primeCounting 246512 = 21752 := primeCounting_step 240000 6513 21221 531 count_240000 (by rw [count_shift_is_prime_eq 240000 6513 (by omega)]; decide)

theorem pc_thm_246753 : Nat.primeCounting 246753 = 21773 := primeCounting_step 240000 6754 21221 552 count_240000 (by rw [count_shift_is_prime_eq 240000 6754 (by omega)]; decide)

theorem pc_thm_247456 : Nat.primeCounting 247456 = 21830 := primeCounting_step 240000 7457 21221 609 count_240000 (by rw [count_shift_is_prime_eq 240000 7457 (by omega)]; decide)

theorem pc_thm_247506 : Nat.primeCounting 247506 = 21832 := primeCounting_step 240000 7507 21221 611 count_240000 (by rw [count_shift_is_prime_eq 240000 7507 (by omega)]; decide)

theorem pc_thm_248160 : Nat.primeCounting 248160 = 21890 := primeCounting_step 240000 8161 21221 669 count_240000 (by rw [count_shift_is_prime_eq 240000 8161 (by omega)]; decide)

theorem pc_thm_248502 : Nat.primeCounting 248502 = 21920 := primeCounting_step 240000 8503 21221 699 count_240000 (by rw [count_shift_is_prime_eq 240000 8503 (by omega)]; decide)

theorem pc_thm_248865 : Nat.primeCounting 248865 = 21953 := primeCounting_step 240000 8866 21221 732 count_240000 (by rw [count_shift_is_prime_eq 240000 8866 (by omega)]; decide)

theorem pc_thm_249500 : Nat.primeCounting 249500 = 22004 := primeCounting_step 240000 9501 21221 783 count_240000 (by rw [count_shift_is_prime_eq 240000 9501 (by omega)]; decide)

theorem pc_thm_249571 : Nat.primeCounting 249571 = 22011 := primeCounting_step 240000 9572 21221 790 count_240000 (by rw [count_shift_is_prime_eq 240000 9572 (by omega)]; decide)

theorem pc_thm_250278 : Nat.primeCounting 250278 = 22064 := primeCounting_step 240000 10279 21221 843 count_240000 (by rw [count_shift_is_prime_eq 240000 10279 (by omega)]; decide)

theorem pc_thm_250500 : Nat.primeCounting 250500 = 22077 := primeCounting_step 240000 10501 21221 856 count_240000 (by rw [count_shift_is_prime_eq 240000 10501 (by omega)]; decide)

theorem pc_thm_250986 : Nat.primeCounting 250986 = 22114 := primeCounting_step 240000 10987 21221 893 count_240000 (by rw [count_shift_is_prime_eq 240000 10987 (by omega)]; decide)

theorem pc_thm_251502 : Nat.primeCounting 251502 = 22163 := primeCounting_step 240000 11503 21221 942 count_240000 (by rw [count_shift_is_prime_eq 240000 11503 (by omega)]; decide)

theorem pc_thm_251695 : Nat.primeCounting 251695 = 22179 := primeCounting_step 240000 11696 21221 958 count_240000 (by rw [count_shift_is_prime_eq 240000 11696 (by omega)]; decide)

theorem pc_thm_252405 : Nat.primeCounting 252405 = 22235 := primeCounting_step 240000 12406 21221 1014 count_240000 (by rw [count_shift_is_prime_eq 240000 12406 (by omega)]; decide)

theorem pc_thm_252506 : Nat.primeCounting 252506 = 22243 := primeCounting_step 240000 12507 21221 1022 count_240000 (by rw [count_shift_is_prime_eq 240000 12507 (by omega)]; decide)

theorem pc_thm_253116 : Nat.primeCounting 253116 = 22288 := primeCounting_step 240000 13117 21221 1067 count_240000 (by rw [count_shift_is_prime_eq 240000 13117 (by omega)]; decide)

theorem pc_thm_253512 : Nat.primeCounting 253512 = 22316 := primeCounting_step 240000 13513 21221 1095 count_240000 (by rw [count_shift_is_prime_eq 240000 13513 (by omega)]; decide)

theorem pc_thm_253828 : Nat.primeCounting 253828 = 22347 := primeCounting_step 240000 13829 21221 1126 count_240000 (by rw [count_shift_is_prime_eq 240000 13829 (by omega)]; decide)

theorem pc_thm_254520 : Nat.primeCounting 254520 = 22399 := primeCounting_step 240000 14521 21221 1178 count_240000 (by rw [count_shift_is_prime_eq 240000 14521 (by omega)]; decide)

theorem pc_thm_254541 : Nat.primeCounting 254541 = 22400 := primeCounting_step 240000 14542 21221 1179 count_240000 (by rw [count_shift_is_prime_eq 240000 14542 (by omega)]; decide)

theorem pc_thm_255255 : Nat.primeCounting 255255 = 22466 := primeCounting_step 240000 15256 21221 1245 count_240000 (by rw [count_shift_is_prime_eq 240000 15256 (by omega)]; decide)

theorem pc_thm_255530 : Nat.primeCounting 255530 = 22486 := primeCounting_step 240000 15531 21221 1265 count_240000 (by rw [count_shift_is_prime_eq 240000 15531 (by omega)]; decide)

theorem pc_thm_255970 : Nat.primeCounting 255970 = 22521 := primeCounting_step 240000 15971 21221 1300 count_240000 (by rw [count_shift_is_prime_eq 240000 15971 (by omega)]; decide)

theorem pc_thm_256542 : Nat.primeCounting 256542 = 22566 := primeCounting_step 240000 16543 21221 1345 count_240000 (by rw [count_shift_is_prime_eq 240000 16543 (by omega)]; decide)

theorem pc_thm_256686 : Nat.primeCounting 256686 = 22577 := primeCounting_step 240000 16687 21221 1356 count_240000 (by rw [count_shift_is_prime_eq 240000 16687 (by omega)]; decide)

theorem pc_thm_257403 : Nat.primeCounting 257403 = 22630 := primeCounting_step 240000 17404 21221 1409 count_240000 (by rw [count_shift_is_prime_eq 240000 17404 (by omega)]; decide)

theorem pc_thm_257556 : Nat.primeCounting 257556 = 22642 := primeCounting_step 240000 17557 21221 1421 count_240000 (by rw [count_shift_is_prime_eq 240000 17557 (by omega)]; decide)

theorem pc_thm_258121 : Nat.primeCounting 258121 = 22685 := primeCounting_step 240000 18122 21221 1464 count_240000 (by rw [count_shift_is_prime_eq 240000 18122 (by omega)]; decide)

theorem pc_thm_258572 : Nat.primeCounting 258572 = 22724 := primeCounting_step 240000 18573 21221 1503 count_240000 (by rw [count_shift_is_prime_eq 240000 18573 (by omega)]; decide)

theorem pc_thm_258840 : Nat.primeCounting 258840 = 22749 := primeCounting_step 240000 18841 21221 1528 count_240000 (by rw [count_shift_is_prime_eq 240000 18841 (by omega)]; decide)

theorem pc_thm_259560 : Nat.primeCounting 259560 = 22801 := primeCounting_step 240000 19561 21221 1580 count_240000 (by rw [count_shift_is_prime_eq 240000 19561 (by omega)]; decide)

theorem pc_thm_259590 : Nat.primeCounting 259590 = 22803 := primeCounting_step 240000 19591 21221 1582 count_240000 (by rw [count_shift_is_prime_eq 240000 19591 (by omega)]; decide)

theorem pc_thm_260281 : Nat.primeCounting 260281 = 22858 := primeCounting_step 260000 282 22837 21 count_260000 (by rw [count_shift_is_prime_eq 260000 282 (by omega)]; decide)

theorem pc_thm_260610 : Nat.primeCounting 260610 = 22884 := primeCounting_step 260000 611 22837 47 count_260000 (by rw [count_shift_is_prime_eq 260000 611 (by omega)]; decide)

theorem pc_thm_261003 : Nat.primeCounting 261003 = 22914 := primeCounting_step 260000 1004 22837 77 count_260000 (by rw [count_shift_is_prime_eq 260000 1004 (by omega)]; decide)

theorem pc_thm_261632 : Nat.primeCounting 261632 = 22962 := primeCounting_step 260000 1633 22837 125 count_260000 (by rw [count_shift_is_prime_eq 260000 1633 (by omega)]; decide)

theorem pc_thm_261726 : Nat.primeCounting 261726 = 22970 := primeCounting_step 260000 1727 22837 133 count_260000 (by rw [count_shift_is_prime_eq 260000 1727 (by omega)]; decide)

theorem pc_thm_262450 : Nat.primeCounting 262450 = 23024 := primeCounting_step 260000 2451 22837 187 count_260000 (by rw [count_shift_is_prime_eq 260000 2451 (by omega)]; decide)

theorem pc_thm_262656 : Nat.primeCounting 262656 = 23042 := primeCounting_step 260000 2657 22837 205 count_260000 (by rw [count_shift_is_prime_eq 260000 2657 (by omega)]; decide)

theorem pc_thm_263175 : Nat.primeCounting 263175 = 23080 := primeCounting_step 260000 3176 22837 243 count_260000 (by rw [count_shift_is_prime_eq 260000 3176 (by omega)]; decide)

theorem pc_thm_263682 : Nat.primeCounting 263682 = 23125 := primeCounting_step 260000 3683 22837 288 count_260000 (by rw [count_shift_is_prime_eq 260000 3683 (by omega)]; decide)

theorem pc_thm_263901 : Nat.primeCounting 263901 = 23141 := primeCounting_step 260000 3902 22837 304 count_260000 (by rw [count_shift_is_prime_eq 260000 3902 (by omega)]; decide)

theorem pc_thm_264628 : Nat.primeCounting 264628 = 23197 := primeCounting_step 260000 4629 22837 360 count_260000 (by rw [count_shift_is_prime_eq 260000 4629 (by omega)]; decide)

theorem pc_thm_264710 : Nat.primeCounting 264710 = 23202 := primeCounting_step 260000 4711 22837 365 count_260000 (by rw [count_shift_is_prime_eq 260000 4711 (by omega)]; decide)

theorem pc_thm_265356 : Nat.primeCounting 265356 = 23259 := primeCounting_step 260000 5357 22837 422 count_260000 (by rw [count_shift_is_prime_eq 260000 5357 (by omega)]; decide)

theorem pc_thm_265740 : Nat.primeCounting 265740 = 23289 := primeCounting_step 260000 5741 22837 452 count_260000 (by rw [count_shift_is_prime_eq 260000 5741 (by omega)]; decide)

theorem pc_thm_266085 : Nat.primeCounting 266085 = 23319 := primeCounting_step 260000 6086 22837 482 count_260000 (by rw [count_shift_is_prime_eq 260000 6086 (by omega)]; decide)

theorem pc_thm_266772 : Nat.primeCounting 266772 = 23373 := primeCounting_step 260000 6773 22837 536 count_260000 (by rw [count_shift_is_prime_eq 260000 6773 (by omega)]; decide)

theorem pc_thm_266815 : Nat.primeCounting 266815 = 23375 := primeCounting_step 260000 6816 22837 538 count_260000 (by rw [count_shift_is_prime_eq 260000 6816 (by omega)]; decide)

theorem pc_thm_267546 : Nat.primeCounting 267546 = 23442 := primeCounting_step 260000 7547 22837 605 count_260000 (by rw [count_shift_is_prime_eq 260000 7547 (by omega)]; decide)

theorem pc_thm_267806 : Nat.primeCounting 267806 = 23473 := primeCounting_step 260000 7807 22837 636 count_260000 (by rw [count_shift_is_prime_eq 260000 7807 (by omega)]; decide)

theorem pc_thm_268278 : Nat.primeCounting 268278 = 23508 := primeCounting_step 260000 8279 22837 671 count_260000 (by rw [count_shift_is_prime_eq 260000 8279 (by omega)]; decide)

theorem pc_thm_268842 : Nat.primeCounting 268842 = 23549 := primeCounting_step 260000 8843 22837 712 count_260000 (by rw [count_shift_is_prime_eq 260000 8843 (by omega)]; decide)

theorem pc_thm_269011 : Nat.primeCounting 269011 = 23564 := primeCounting_step 260000 9012 22837 727 count_260000 (by rw [count_shift_is_prime_eq 260000 9012 (by omega)]; decide)

theorem pc_thm_269745 : Nat.primeCounting 269745 = 23626 := primeCounting_step 260000 9746 22837 789 count_260000 (by rw [count_shift_is_prime_eq 260000 9746 (by omega)]; decide)

theorem pc_thm_269880 : Nat.primeCounting 269880 = 23633 := primeCounting_step 260000 9881 22837 796 count_260000 (by rw [count_shift_is_prime_eq 260000 9881 (by omega)]; decide)

theorem pc_thm_270480 : Nat.primeCounting 270480 = 23683 := primeCounting_step 260000 10481 22837 846 count_260000 (by rw [count_shift_is_prime_eq 260000 10481 (by omega)]; decide)

theorem pc_thm_270920 : Nat.primeCounting 270920 = 23719 := primeCounting_step 260000 10921 22837 882 count_260000 (by rw [count_shift_is_prime_eq 260000 10921 (by omega)]; decide)

theorem pc_thm_271216 : Nat.primeCounting 271216 = 23743 := primeCounting_step 260000 11217 22837 906 count_260000 (by rw [count_shift_is_prime_eq 260000 11217 (by omega)]; decide)

theorem pc_thm_271953 : Nat.primeCounting 271953 = 23801 := primeCounting_step 260000 11954 22837 964 count_260000 (by rw [count_shift_is_prime_eq 260000 11954 (by omega)]; decide)

theorem pc_thm_271962 : Nat.primeCounting 271962 = 23801 := primeCounting_step 260000 11963 22837 964 count_260000 (by rw [count_shift_is_prime_eq 260000 11963 (by omega)]; decide)

theorem pc_thm_272691 : Nat.primeCounting 272691 = 23862 := primeCounting_step 260000 12692 22837 1025 count_260000 (by rw [count_shift_is_prime_eq 260000 12692 (by omega)]; decide)

theorem pc_thm_273006 : Nat.primeCounting 273006 = 23888 := primeCounting_step 260000 13007 22837 1051 count_260000 (by rw [count_shift_is_prime_eq 260000 13007 (by omega)]; decide)

theorem pc_thm_273430 : Nat.primeCounting 273430 = 23918 := primeCounting_step 260000 13431 22837 1081 count_260000 (by rw [count_shift_is_prime_eq 260000 13431 (by omega)]; decide)

theorem pc_thm_274052 : Nat.primeCounting 274052 = 23961 := primeCounting_step 260000 14053 22837 1124 count_260000 (by rw [count_shift_is_prime_eq 260000 14053 (by omega)]; decide)

theorem pc_thm_274170 : Nat.primeCounting 274170 = 23972 := primeCounting_step 260000 14171 22837 1135 count_260000 (by rw [count_shift_is_prime_eq 260000 14171 (by omega)]; decide)

theorem pc_thm_274911 : Nat.primeCounting 274911 = 24031 := primeCounting_step 260000 14912 22837 1194 count_260000 (by rw [count_shift_is_prime_eq 260000 14912 (by omega)]; decide)

theorem pc_thm_275100 : Nat.primeCounting 275100 = 24046 := primeCounting_step 260000 15101 22837 1209 count_260000 (by rw [count_shift_is_prime_eq 260000 15101 (by omega)]; decide)

theorem pc_thm_275653 : Nat.primeCounting 275653 = 24093 := primeCounting_step 260000 15654 22837 1256 count_260000 (by rw [count_shift_is_prime_eq 260000 15654 (by omega)]; decide)

theorem pc_thm_276150 : Nat.primeCounting 276150 = 24134 := primeCounting_step 260000 16151 22837 1297 count_260000 (by rw [count_shift_is_prime_eq 260000 16151 (by omega)]; decide)

theorem pc_thm_276396 : Nat.primeCounting 276396 = 24156 := primeCounting_step 260000 16397 22837 1319 count_260000 (by rw [count_shift_is_prime_eq 260000 16397 (by omega)]; decide)

theorem pc_thm_277140 : Nat.primeCounting 277140 = 24213 := primeCounting_step 260000 17141 22837 1376 count_260000 (by rw [count_shift_is_prime_eq 260000 17141 (by omega)]; decide)

theorem pc_thm_277202 : Nat.primeCounting 277202 = 24218 := primeCounting_step 260000 17203 22837 1381 count_260000 (by rw [count_shift_is_prime_eq 260000 17203 (by omega)]; decide)

theorem pc_thm_277885 : Nat.primeCounting 277885 = 24270 := primeCounting_step 260000 17886 22837 1433 count_260000 (by rw [count_shift_is_prime_eq 260000 17886 (by omega)]; decide)

theorem pc_thm_278256 : Nat.primeCounting 278256 = 24299 := primeCounting_step 260000 18257 22837 1462 count_260000 (by rw [count_shift_is_prime_eq 260000 18257 (by omega)]; decide)

theorem pc_thm_278631 : Nat.primeCounting 278631 = 24330 := primeCounting_step 260000 18632 22837 1493 count_260000 (by rw [count_shift_is_prime_eq 260000 18632 (by omega)]; decide)

theorem pc_thm_279312 : Nat.primeCounting 279312 = 24380 := primeCounting_step 260000 19313 22837 1543 count_260000 (by rw [count_shift_is_prime_eq 260000 19313 (by omega)]; decide)

theorem pc_thm_279378 : Nat.primeCounting 279378 = 24384 := primeCounting_step 260000 19379 22837 1547 count_260000 (by rw [count_shift_is_prime_eq 260000 19379 (by omega)]; decide)

theorem pc_thm_280126 : Nat.primeCounting 280126 = 24443 := primeCounting_step 280000 127 24432 11 count_280000 (by rw [count_shift_is_prime_eq 280000 127 (by omega)]; decide)

theorem pc_thm_280370 : Nat.primeCounting 280370 = 24463 := primeCounting_step 280000 371 24432 31 count_280000 (by rw [count_shift_is_prime_eq 280000 371 (by omega)]; decide)

theorem pc_thm_280875 : Nat.primeCounting 280875 = 24504 := primeCounting_step 280000 876 24432 72 count_280000 (by rw [count_shift_is_prime_eq 280000 876 (by omega)]; decide)

theorem pc_thm_281430 : Nat.primeCounting 281430 = 24553 := primeCounting_step 280000 1431 24432 121 count_280000 (by rw [count_shift_is_prime_eq 280000 1431 (by omega)]; decide)

theorem pc_thm_281625 : Nat.primeCounting 281625 = 24567 := primeCounting_step 280000 1626 24432 135 count_280000 (by rw [count_shift_is_prime_eq 280000 1626 (by omega)]; decide)

theorem pc_thm_282376 : Nat.primeCounting 282376 = 24631 := primeCounting_step 280000 2377 24432 199 count_280000 (by rw [count_shift_is_prime_eq 280000 2377 (by omega)]; decide)

theorem pc_thm_282492 : Nat.primeCounting 282492 = 24643 := primeCounting_step 280000 2493 24432 211 count_280000 (by rw [count_shift_is_prime_eq 280000 2493 (by omega)]; decide)

theorem pc_thm_283128 : Nat.primeCounting 283128 = 24693 := primeCounting_step 280000 3129 24432 261 count_280000 (by rw [count_shift_is_prime_eq 280000 3129 (by omega)]; decide)

theorem pc_thm_283556 : Nat.primeCounting 283556 = 24719 := primeCounting_step 280000 3557 24432 287 count_280000 (by rw [count_shift_is_prime_eq 280000 3557 (by omega)]; decide)

theorem pc_thm_283881 : Nat.primeCounting 283881 = 24747 := primeCounting_step 280000 3882 24432 315 count_280000 (by rw [count_shift_is_prime_eq 280000 3882 (by omega)]; decide)

theorem pc_thm_284622 : Nat.primeCounting 284622 = 24807 := primeCounting_step 280000 4623 24432 375 count_280000 (by rw [count_shift_is_prime_eq 280000 4623 (by omega)]; decide)

theorem pc_thm_284635 : Nat.primeCounting 284635 = 24809 := primeCounting_step 280000 4636 24432 377 count_280000 (by rw [count_shift_is_prime_eq 280000 4636 (by omega)]; decide)

theorem pc_thm_285390 : Nat.primeCounting 285390 = 24871 := primeCounting_step 280000 5391 24432 439 count_280000 (by rw [count_shift_is_prime_eq 280000 5391 (by omega)]; decide)

theorem pc_thm_285690 : Nat.primeCounting 285690 = 24897 := primeCounting_step 280000 5691 24432 465 count_280000 (by rw [count_shift_is_prime_eq 280000 5691 (by omega)]; decide)

theorem pc_thm_286146 : Nat.primeCounting 286146 = 24930 := primeCounting_step 280000 6147 24432 498 count_280000 (by rw [count_shift_is_prime_eq 280000 6147 (by omega)]; decide)

theorem pc_thm_286760 : Nat.primeCounting 286760 = 24977 := primeCounting_step 280000 6761 24432 545 count_280000 (by rw [count_shift_is_prime_eq 280000 6761 (by omega)]; decide)

theorem pc_thm_286903 : Nat.primeCounting 286903 = 24986 := primeCounting_step 280000 6904 24432 554 count_280000 (by rw [count_shift_is_prime_eq 280000 6904 (by omega)]; decide)

theorem pc_thm_287661 : Nat.primeCounting 287661 = 25039 := primeCounting_step 280000 7662 24432 607 count_280000 (by rw [count_shift_is_prime_eq 280000 7662 (by omega)]; decide)

theorem pc_thm_287832 : Nat.primeCounting 287832 = 25051 := primeCounting_step 280000 7833 24432 619 count_280000 (by rw [count_shift_is_prime_eq 280000 7833 (by omega)]; decide)

theorem pc_thm_288420 : Nat.primeCounting 288420 = 25093 := primeCounting_step 280000 8421 24432 661 count_280000 (by rw [count_shift_is_prime_eq 280000 8421 (by omega)]; decide)

theorem pc_thm_288906 : Nat.primeCounting 288906 = 25129 := primeCounting_step 280000 8907 24432 697 count_280000 (by rw [count_shift_is_prime_eq 280000 8907 (by omega)]; decide)

theorem pc_thm_289180 : Nat.primeCounting 289180 = 25159 := primeCounting_step 280000 9181 24432 727 count_280000 (by rw [count_shift_is_prime_eq 280000 9181 (by omega)]; decide)

theorem pc_thm_289941 : Nat.primeCounting 289941 = 25218 := primeCounting_step 280000 9942 24432 786 count_280000 (by rw [count_shift_is_prime_eq 280000 9942 (by omega)]; decide)

theorem pc_thm_289982 : Nat.primeCounting 289982 = 25222 := primeCounting_step 280000 9983 24432 790 count_280000 (by rw [count_shift_is_prime_eq 280000 9983 (by omega)]; decide)

theorem pc_thm_290703 : Nat.primeCounting 290703 = 25286 := primeCounting_step 280000 10704 24432 854 count_280000 (by rw [count_shift_is_prime_eq 280000 10704 (by omega)]; decide)

theorem pc_thm_291060 : Nat.primeCounting 291060 = 25313 := primeCounting_step 280000 11061 24432 881 count_280000 (by rw [count_shift_is_prime_eq 280000 11061 (by omega)]; decide)

theorem pc_thm_291466 : Nat.primeCounting 291466 = 25346 := primeCounting_step 280000 11467 24432 914 count_280000 (by rw [count_shift_is_prime_eq 280000 11467 (by omega)]; decide)

theorem pc_thm_292140 : Nat.primeCounting 292140 = 25395 := primeCounting_step 280000 12141 24432 963 count_280000 (by rw [count_shift_is_prime_eq 280000 12141 (by omega)]; decide)

theorem pc_thm_292230 : Nat.primeCounting 292230 = 25401 := primeCounting_step 280000 12231 24432 969 count_280000 (by rw [count_shift_is_prime_eq 280000 12231 (by omega)]; decide)

theorem pc_thm_292995 : Nat.primeCounting 292995 = 25463 := primeCounting_step 280000 12996 24432 1031 count_280000 (by rw [count_shift_is_prime_eq 280000 12996 (by omega)]; decide)

theorem pc_thm_293222 : Nat.primeCounting 293222 = 25481 := primeCounting_step 280000 13223 24432 1049 count_280000 (by rw [count_shift_is_prime_eq 280000 13223 (by omega)]; decide)

theorem pc_thm_293761 : Nat.primeCounting 293761 = 25516 := primeCounting_step 280000 13762 24432 1084 count_280000 (by rw [count_shift_is_prime_eq 280000 13762 (by omega)]; decide)

theorem pc_thm_294306 : Nat.primeCounting 294306 = 25559 := primeCounting_step 280000 14307 24432 1127 count_280000 (by rw [count_shift_is_prime_eq 280000 14307 (by omega)]; decide)

theorem pc_thm_294528 : Nat.primeCounting 294528 = 25579 := primeCounting_step 280000 14529 24432 1147 count_280000 (by rw [count_shift_is_prime_eq 280000 14529 (by omega)]; decide)

theorem pc_thm_295296 : Nat.primeCounting 295296 = 25639 := primeCounting_step 280000 15297 24432 1207 count_280000 (by rw [count_shift_is_prime_eq 280000 15297 (by omega)]; decide)

theorem pc_thm_295392 : Nat.primeCounting 295392 = 25645 := primeCounting_step 280000 15393 24432 1213 count_280000 (by rw [count_shift_is_prime_eq 280000 15393 (by omega)]; decide)

theorem pc_thm_296065 : Nat.primeCounting 296065 = 25696 := primeCounting_step 280000 16066 24432 1264 count_280000 (by rw [count_shift_is_prime_eq 280000 16066 (by omega)]; decide)

theorem pc_thm_296480 : Nat.primeCounting 296480 = 25726 := primeCounting_step 280000 16481 24432 1294 count_280000 (by rw [count_shift_is_prime_eq 280000 16481 (by omega)]; decide)

theorem pc_thm_296835 : Nat.primeCounting 296835 = 25762 := primeCounting_step 280000 16836 24432 1330 count_280000 (by rw [count_shift_is_prime_eq 280000 16836 (by omega)]; decide)

theorem pc_thm_297570 : Nat.primeCounting 297570 = 25811 := primeCounting_step 280000 17571 24432 1379 count_280000 (by rw [count_shift_is_prime_eq 280000 17571 (by omega)]; decide)

theorem pc_thm_297606 : Nat.primeCounting 297606 = 25814 := primeCounting_step 280000 17607 24432 1382 count_280000 (by rw [count_shift_is_prime_eq 280000 17607 (by omega)]; decide)

theorem pc_thm_298378 : Nat.primeCounting 298378 = 25877 := primeCounting_step 280000 18379 24432 1445 count_280000 (by rw [count_shift_is_prime_eq 280000 18379 (by omega)]; decide)

theorem pc_thm_298662 : Nat.primeCounting 298662 = 25894 := primeCounting_step 280000 18663 24432 1462 count_280000 (by rw [count_shift_is_prime_eq 280000 18663 (by omega)]; decide)

theorem pc_thm_299151 : Nat.primeCounting 299151 = 25932 := primeCounting_step 280000 19152 24432 1500 count_280000 (by rw [count_shift_is_prime_eq 280000 19152 (by omega)]; decide)

theorem pc_thm_299756 : Nat.primeCounting 299756 = 25980 := primeCounting_step 280000 19757 24432 1548 count_280000 (by rw [count_shift_is_prime_eq 280000 19757 (by omega)]; decide)

theorem pc_thm_299925 : Nat.primeCounting 299925 = 25990 := primeCounting_step 280000 19926 24432 1558 count_280000 (by rw [count_shift_is_prime_eq 280000 19926 (by omega)]; decide)

theorem pc_thm_300700 : Nat.primeCounting 300700 = 26054 := primeCounting_step 300000 701 25997 57 count_300000 (by rw [count_shift_is_prime_eq 300000 701 (by omega)]; decide)

theorem pc_thm_300852 : Nat.primeCounting 300852 = 26069 := primeCounting_step 300000 853 25997 72 count_300000 (by rw [count_shift_is_prime_eq 300000 853 (by omega)]; decide)

theorem pc_thm_301476 : Nat.primeCounting 301476 = 26120 := primeCounting_step 300000 1477 25997 123 count_300000 (by rw [count_shift_is_prime_eq 300000 1477 (by omega)]; decide)

theorem pc_thm_301950 : Nat.primeCounting 301950 = 26160 := primeCounting_step 300000 1951 25997 163 count_300000 (by rw [count_shift_is_prime_eq 300000 1951 (by omega)]; decide)

theorem pc_thm_302253 : Nat.primeCounting 302253 = 26178 := primeCounting_step 300000 2254 25997 181 count_300000 (by rw [count_shift_is_prime_eq 300000 2254 (by omega)]; decide)

theorem pc_thm_303031 : Nat.primeCounting 303031 = 26242 := primeCounting_step 300000 3032 25997 245 count_300000 (by rw [count_shift_is_prime_eq 300000 3032 (by omega)]; decide)

theorem pc_thm_303050 : Nat.primeCounting 303050 = 26243 := primeCounting_step 300000 3051 25997 246 count_300000 (by rw [count_shift_is_prime_eq 300000 3051 (by omega)]; decide)

theorem pc_thm_303810 : Nat.primeCounting 303810 = 26308 := primeCounting_step 300000 3811 25997 311 count_300000 (by rw [count_shift_is_prime_eq 300000 3811 (by omega)]; decide)

theorem pc_thm_304152 : Nat.primeCounting 304152 = 26335 := primeCounting_step 300000 4153 25997 338 count_300000 (by rw [count_shift_is_prime_eq 300000 4153 (by omega)]; decide)

theorem pc_thm_304590 : Nat.primeCounting 304590 = 26373 := primeCounting_step 300000 4591 25997 376 count_300000 (by rw [count_shift_is_prime_eq 300000 4591 (by omega)]; decide)

theorem pc_thm_305256 : Nat.primeCounting 305256 = 26429 := primeCounting_step 300000 5257 25997 432 count_300000 (by rw [count_shift_is_prime_eq 300000 5257 (by omega)]; decide)

theorem pc_thm_305371 : Nat.primeCounting 305371 = 26438 := primeCounting_step 300000 5372 25997 441 count_300000 (by rw [count_shift_is_prime_eq 300000 5372 (by omega)]; decide)

theorem pc_thm_306153 : Nat.primeCounting 306153 = 26500 := primeCounting_step 300000 6154 25997 503 count_300000 (by rw [count_shift_is_prime_eq 300000 6154 (by omega)]; decide)

theorem pc_thm_306362 : Nat.primeCounting 306362 = 26517 := primeCounting_step 300000 6363 25997 520 count_300000 (by rw [count_shift_is_prime_eq 300000 6363 (by omega)]; decide)

theorem pc_thm_306936 : Nat.primeCounting 306936 = 26566 := primeCounting_step 300000 6937 25997 569 count_300000 (by rw [count_shift_is_prime_eq 300000 6937 (by omega)]; decide)

theorem pc_thm_307470 : Nat.primeCounting 307470 = 26609 := primeCounting_step 300000 7471 25997 612 count_300000 (by rw [count_shift_is_prime_eq 300000 7471 (by omega)]; decide)

theorem pc_thm_307720 : Nat.primeCounting 307720 = 26630 := primeCounting_step 300000 7721 25997 633 count_300000 (by rw [count_shift_is_prime_eq 300000 7721 (by omega)]; decide)

theorem pc_thm_308505 : Nat.primeCounting 308505 = 26682 := primeCounting_step 300000 8506 25997 685 count_300000 (by rw [count_shift_is_prime_eq 300000 8506 (by omega)]; decide)

theorem pc_thm_308580 : Nat.primeCounting 308580 = 26691 := primeCounting_step 300000 8581 25997 694 count_300000 (by rw [count_shift_is_prime_eq 300000 8581 (by omega)]; decide)

theorem pc_thm_309291 : Nat.primeCounting 309291 = 26747 := primeCounting_step 300000 9292 25997 750 count_300000 (by rw [count_shift_is_prime_eq 300000 9292 (by omega)]; decide)

theorem pc_thm_309692 : Nat.primeCounting 309692 = 26780 := primeCounting_step 300000 9693 25997 783 count_300000 (by rw [count_shift_is_prime_eq 300000 9693 (by omega)]; decide)

theorem pc_thm_310078 : Nat.primeCounting 310078 = 26805 := primeCounting_step 300000 10079 25997 808 count_300000 (by rw [count_shift_is_prime_eq 300000 10079 (by omega)]; decide)

theorem pc_thm_310806 : Nat.primeCounting 310806 = 26864 := primeCounting_step 300000 10807 25997 867 count_300000 (by rw [count_shift_is_prime_eq 300000 10807 (by omega)]; decide)

theorem pc_thm_310866 : Nat.primeCounting 310866 = 26869 := primeCounting_step 300000 10867 25997 872 count_300000 (by rw [count_shift_is_prime_eq 300000 10867 (by omega)]; decide)

theorem pc_thm_311655 : Nat.primeCounting 311655 = 26924 := primeCounting_step 300000 11656 25997 927 count_300000 (by rw [count_shift_is_prime_eq 300000 11656 (by omega)]; decide)

theorem pc_thm_311922 : Nat.primeCounting 311922 = 26944 := primeCounting_step 300000 11923 25997 947 count_300000 (by rw [count_shift_is_prime_eq 300000 11923 (by omega)]; decide)

theorem pc_thm_312445 : Nat.primeCounting 312445 = 26990 := primeCounting_step 300000 12446 25997 993 count_300000 (by rw [count_shift_is_prime_eq 300000 12446 (by omega)]; decide)

theorem pc_thm_313040 : Nat.primeCounting 313040 = 27038 := primeCounting_step 300000 13041 25997 1041 count_300000 (by rw [count_shift_is_prime_eq 300000 13041 (by omega)]; decide)

theorem pc_thm_313236 : Nat.primeCounting 313236 = 27051 := primeCounting_step 300000 13237 25997 1054 count_300000 (by rw [count_shift_is_prime_eq 300000 13237 (by omega)]; decide)

theorem pc_thm_314028 : Nat.primeCounting 314028 = 27122 := primeCounting_step 300000 14029 25997 1125 count_300000 (by rw [count_shift_is_prime_eq 300000 14029 (by omega)]; decide)

theorem pc_thm_314160 : Nat.primeCounting 314160 = 27131 := primeCounting_step 300000 14161 25997 1134 count_300000 (by rw [count_shift_is_prime_eq 300000 14161 (by omega)]; decide)

theorem pc_thm_314821 : Nat.primeCounting 314821 = 27185 := primeCounting_step 300000 14822 25997 1188 count_300000 (by rw [count_shift_is_prime_eq 300000 14822 (by omega)]; decide)

theorem pc_thm_315282 : Nat.primeCounting 315282 = 27217 := primeCounting_step 300000 15283 25997 1220 count_300000 (by rw [count_shift_is_prime_eq 300000 15283 (by omega)]; decide)

theorem pc_thm_315615 : Nat.primeCounting 315615 = 27245 := primeCounting_step 300000 15616 25997 1248 count_300000 (by rw [count_shift_is_prime_eq 300000 15616 (by omega)]; decide)

theorem pc_thm_316406 : Nat.primeCounting 316406 = 27307 := primeCounting_step 300000 16407 25997 1310 count_300000 (by rw [count_shift_is_prime_eq 300000 16407 (by omega)]; decide)

theorem pc_thm_316410 : Nat.primeCounting 316410 = 27307 := primeCounting_step 300000 16411 25997 1310 count_300000 (by rw [count_shift_is_prime_eq 300000 16411 (by omega)]; decide)

theorem pc_thm_317206 : Nat.primeCounting 317206 = 27373 := primeCounting_step 300000 17207 25997 1376 count_300000 (by rw [count_shift_is_prime_eq 300000 17207 (by omega)]; decide)

theorem pc_thm_317532 : Nat.primeCounting 317532 = 27399 := primeCounting_step 300000 17533 25997 1402 count_300000 (by rw [count_shift_is_prime_eq 300000 17533 (by omega)]; decide)

theorem pc_thm_318003 : Nat.primeCounting 318003 = 27442 := primeCounting_step 300000 18004 25997 1445 count_300000 (by rw [count_shift_is_prime_eq 300000 18004 (by omega)]; decide)

theorem pc_thm_318660 : Nat.primeCounting 318660 = 27493 := primeCounting_step 300000 18661 25997 1496 count_300000 (by rw [count_shift_is_prime_eq 300000 18661 (by omega)]; decide)

theorem pc_thm_318801 : Nat.primeCounting 318801 = 27506 := primeCounting_step 300000 18802 25997 1509 count_300000 (by rw [count_shift_is_prime_eq 300000 18802 (by omega)]; decide)

theorem pc_thm_319600 : Nat.primeCounting 319600 = 27576 := primeCounting_step 300000 19601 25997 1579 count_300000 (by rw [count_shift_is_prime_eq 300000 19601 (by omega)]; decide)

theorem pc_thm_319790 : Nat.primeCounting 319790 = 27591 := primeCounting_step 300000 19791 25997 1594 count_300000 (by rw [count_shift_is_prime_eq 300000 19791 (by omega)]; decide)

theorem pc_thm_320400 : Nat.primeCounting 320400 = 27644 := primeCounting_step 320000 401 27608 36 count_320000 (by rw [count_shift_is_prime_eq 320000 401 (by omega)]; decide)

theorem pc_thm_320922 : Nat.primeCounting 320922 = 27682 := primeCounting_step 320000 923 27608 74 count_320000 (by rw [count_shift_is_prime_eq 320000 923 (by omega)]; decide)

theorem pc_thm_321201 : Nat.primeCounting 321201 = 27703 := primeCounting_step 320000 1202 27608 95 count_320000 (by rw [count_shift_is_prime_eq 320000 1202 (by omega)]; decide)

theorem pc_thm_322003 : Nat.primeCounting 322003 = 27768 := primeCounting_step 320000 2004 27608 160 count_320000 (by rw [count_shift_is_prime_eq 320000 2004 (by omega)]; decide)

theorem pc_thm_322056 : Nat.primeCounting 322056 = 27773 := primeCounting_step 320000 2057 27608 165 count_320000 (by rw [count_shift_is_prime_eq 320000 2057 (by omega)]; decide)

theorem pc_thm_322806 : Nat.primeCounting 322806 = 27833 := primeCounting_step 320000 2807 27608 225 count_320000 (by rw [count_shift_is_prime_eq 320000 2807 (by omega)]; decide)

theorem pc_thm_323192 : Nat.primeCounting 323192 = 27861 := primeCounting_step 320000 3193 27608 253 count_320000 (by rw [count_shift_is_prime_eq 320000 3193 (by omega)]; decide)

theorem pc_thm_323610 : Nat.primeCounting 323610 = 27894 := primeCounting_step 320000 3611 27608 286 count_320000 (by rw [count_shift_is_prime_eq 320000 3611 (by omega)]; decide)

theorem pc_thm_324330 : Nat.primeCounting 324330 = 27946 := primeCounting_step 320000 4331 27608 338 count_320000 (by rw [count_shift_is_prime_eq 320000 4331 (by omega)]; decide)

theorem pc_thm_324415 : Nat.primeCounting 324415 = 27951 := primeCounting_step 320000 4416 27608 343 count_320000 (by rw [count_shift_is_prime_eq 320000 4416 (by omega)]; decide)

theorem pc_thm_325221 : Nat.primeCounting 325221 = 28026 := primeCounting_step 320000 5222 27608 418 count_320000 (by rw [count_shift_is_prime_eq 320000 5222 (by omega)]; decide)

theorem pc_thm_325470 : Nat.primeCounting 325470 = 28045 := primeCounting_step 320000 5471 27608 437 count_320000 (by rw [count_shift_is_prime_eq 320000 5471 (by omega)]; decide)

theorem pc_thm_326028 : Nat.primeCounting 326028 = 28092 := primeCounting_step 320000 6029 27608 484 count_320000 (by rw [count_shift_is_prime_eq 320000 6029 (by omega)]; decide)

theorem pc_thm_326612 : Nat.primeCounting 326612 = 28135 := primeCounting_step 320000 6613 27608 527 count_320000 (by rw [count_shift_is_prime_eq 320000 6613 (by omega)]; decide)

theorem pc_thm_326836 : Nat.primeCounting 326836 = 28150 := primeCounting_step 320000 6837 27608 542 count_320000 (by rw [count_shift_is_prime_eq 320000 6837 (by omega)]; decide)

theorem pc_thm_327645 : Nat.primeCounting 327645 = 28219 := primeCounting_step 320000 7646 27608 611 count_320000 (by rw [count_shift_is_prime_eq 320000 7646 (by omega)]; decide)

theorem pc_thm_327756 : Nat.primeCounting 327756 = 28228 := primeCounting_step 320000 7757 27608 620 count_320000 (by rw [count_shift_is_prime_eq 320000 7757 (by omega)]; decide)

theorem pc_thm_328455 : Nat.primeCounting 328455 = 28286 := primeCounting_step 320000 8456 27608 678 count_320000 (by rw [count_shift_is_prime_eq 320000 8456 (by omega)]; decide)

theorem pc_thm_328902 : Nat.primeCounting 328902 = 28318 := primeCounting_step 320000 8903 27608 710 count_320000 (by rw [count_shift_is_prime_eq 320000 8903 (by omega)]; decide)

theorem pc_thm_329266 : Nat.primeCounting 329266 = 28343 := primeCounting_step 320000 9267 27608 735 count_320000 (by rw [count_shift_is_prime_eq 320000 9267 (by omega)]; decide)

theorem pc_thm_330050 : Nat.primeCounting 330050 = 28409 := primeCounting_step 320000 10051 27608 801 count_320000 (by rw [count_shift_is_prime_eq 320000 10051 (by omega)]; decide)

theorem pc_thm_330078 : Nat.primeCounting 330078 = 28412 := primeCounting_step 320000 10079 27608 804 count_320000 (by rw [count_shift_is_prime_eq 320000 10079 (by omega)]; decide)

theorem pc_thm_330891 : Nat.primeCounting 330891 = 28478 := primeCounting_step 320000 10892 27608 870 count_320000 (by rw [count_shift_is_prime_eq 320000 10892 (by omega)]; decide)

theorem pc_thm_331200 : Nat.primeCounting 331200 = 28498 := primeCounting_step 320000 11201 27608 890 count_320000 (by rw [count_shift_is_prime_eq 320000 11201 (by omega)]; decide)

theorem pc_thm_331705 : Nat.primeCounting 331705 = 28542 := primeCounting_step 320000 11706 27608 934 count_320000 (by rw [count_shift_is_prime_eq 320000 11706 (by omega)]; decide)

theorem pc_thm_332352 : Nat.primeCounting 332352 = 28593 := primeCounting_step 320000 12353 27608 985 count_320000 (by rw [count_shift_is_prime_eq 320000 12353 (by omega)]; decide)

theorem pc_thm_332520 : Nat.primeCounting 332520 = 28607 := primeCounting_step 320000 12521 27608 999 count_320000 (by rw [count_shift_is_prime_eq 320000 12521 (by omega)]; decide)

theorem pc_thm_333336 : Nat.primeCounting 333336 = 28665 := primeCounting_step 320000 13337 27608 1057 count_320000 (by rw [count_shift_is_prime_eq 320000 13337 (by omega)]; decide)

theorem pc_thm_333506 : Nat.primeCounting 333506 = 28683 := primeCounting_step 320000 13507 27608 1075 count_320000 (by rw [count_shift_is_prime_eq 320000 13507 (by omega)]; decide)

theorem pc_thm_334153 : Nat.primeCounting 334153 = 28729 := primeCounting_step 320000 14154 27608 1121 count_320000 (by rw [count_shift_is_prime_eq 320000 14154 (by omega)]; decide)

theorem pc_thm_334662 : Nat.primeCounting 334662 = 28769 := primeCounting_step 320000 14663 27608 1161 count_320000 (by rw [count_shift_is_prime_eq 320000 14663 (by omega)]; decide)

theorem pc_thm_334971 : Nat.primeCounting 334971 = 28792 := primeCounting_step 320000 14972 27608 1184 count_320000 (by rw [count_shift_is_prime_eq 320000 14972 (by omega)]; decide)

theorem pc_thm_335790 : Nat.primeCounting 335790 = 28858 := primeCounting_step 320000 15791 27608 1250 count_320000 (by rw [count_shift_is_prime_eq 320000 15791 (by omega)]; decide)

theorem pc_thm_335820 : Nat.primeCounting 335820 = 28861 := primeCounting_step 320000 15821 27608 1253 count_320000 (by rw [count_shift_is_prime_eq 320000 15821 (by omega)]; decide)

theorem pc_thm_336610 : Nat.primeCounting 336610 = 28922 := primeCounting_step 320000 16611 27608 1314 count_320000 (by rw [count_shift_is_prime_eq 320000 16611 (by omega)]; decide)

theorem pc_thm_336980 : Nat.primeCounting 336980 = 28954 := primeCounting_step 320000 16981 27608 1346 count_320000 (by rw [count_shift_is_prime_eq 320000 16981 (by omega)]; decide)

theorem pc_thm_337431 : Nat.primeCounting 337431 = 28991 := primeCounting_step 320000 17432 27608 1383 count_320000 (by rw [count_shift_is_prime_eq 320000 17432 (by omega)]; decide)

theorem pc_thm_338142 : Nat.primeCounting 338142 = 29043 := primeCounting_step 320000 18143 27608 1435 count_320000 (by rw [count_shift_is_prime_eq 320000 18143 (by omega)]; decide)

theorem pc_thm_338253 : Nat.primeCounting 338253 = 29056 := primeCounting_step 320000 18254 27608 1448 count_320000 (by rw [count_shift_is_prime_eq 320000 18254 (by omega)]; decide)

theorem pc_thm_339076 : Nat.primeCounting 339076 = 29118 := primeCounting_step 320000 19077 27608 1510 count_320000 (by rw [count_shift_is_prime_eq 320000 19077 (by omega)]; decide)

theorem pc_thm_339306 : Nat.primeCounting 339306 = 29136 := primeCounting_step 320000 19307 27608 1528 count_320000 (by rw [count_shift_is_prime_eq 320000 19307 (by omega)]; decide)

theorem pc_thm_339900 : Nat.primeCounting 339900 = 29178 := primeCounting_step 320000 19901 27608 1570 count_320000 (by rw [count_shift_is_prime_eq 320000 19901 (by omega)]; decide)

theorem pc_thm_340472 : Nat.primeCounting 340472 = 29220 := primeCounting_step 340000 473 29182 38 count_340000 (by rw [count_shift_is_prime_eq 340000 473 (by omega)]; decide)

theorem pc_thm_340725 : Nat.primeCounting 340725 = 29241 := primeCounting_step 340000 726 29182 59 count_340000 (by rw [count_shift_is_prime_eq 340000 726 (by omega)]; decide)

theorem pc_thm_341551 : Nat.primeCounting 341551 = 29307 := primeCounting_step 340000 1552 29182 125 count_340000 (by rw [count_shift_is_prime_eq 340000 1552 (by omega)]; decide)

theorem pc_thm_341640 : Nat.primeCounting 341640 = 29315 := primeCounting_step 340000 1641 29182 133 count_340000 (by rw [count_shift_is_prime_eq 340000 1641 (by omega)]; decide)

theorem pc_thm_342378 : Nat.primeCounting 342378 = 29376 := primeCounting_step 340000 2379 29182 194 count_340000 (by rw [count_shift_is_prime_eq 340000 2379 (by omega)]; decide)

theorem pc_thm_342810 : Nat.primeCounting 342810 = 29407 := primeCounting_step 340000 2811 29182 225 count_340000 (by rw [count_shift_is_prime_eq 340000 2811 (by omega)]; decide)

theorem pc_thm_343206 : Nat.primeCounting 343206 = 29435 := primeCounting_step 340000 3207 29182 253 count_340000 (by rw [count_shift_is_prime_eq 340000 3207 (by omega)]; decide)

theorem pc_thm_343982 : Nat.primeCounting 343982 = 29499 := primeCounting_step 340000 3983 29182 317 count_340000 (by rw [count_shift_is_prime_eq 340000 3983 (by omega)]; decide)

theorem pc_thm_344035 : Nat.primeCounting 344035 = 29502 := primeCounting_step 340000 4036 29182 320 count_340000 (by rw [count_shift_is_prime_eq 340000 4036 (by omega)]; decide)

theorem pc_thm_344865 : Nat.primeCounting 344865 = 29568 := primeCounting_step 340000 4866 29182 386 count_340000 (by rw [count_shift_is_prime_eq 340000 4866 (by omega)]; decide)

theorem pc_thm_345156 : Nat.primeCounting 345156 = 29592 := primeCounting_step 340000 5157 29182 410 count_340000 (by rw [count_shift_is_prime_eq 340000 5157 (by omega)]; decide)

theorem pc_thm_345696 : Nat.primeCounting 345696 = 29630 := primeCounting_step 340000 5697 29182 448 count_340000 (by rw [count_shift_is_prime_eq 340000 5697 (by omega)]; decide)

theorem pc_thm_346332 : Nat.primeCounting 346332 = 29682 := primeCounting_step 340000 6333 29182 500 count_340000 (by rw [count_shift_is_prime_eq 340000 6333 (by omega)]; decide)

theorem pc_thm_346528 : Nat.primeCounting 346528 = 29701 := primeCounting_step 340000 6529 29182 519 count_340000 (by rw [count_shift_is_prime_eq 340000 6529 (by omega)]; decide)

theorem pc_thm_347361 : Nat.primeCounting 347361 = 29770 := primeCounting_step 340000 7362 29182 588 count_340000 (by rw [count_shift_is_prime_eq 340000 7362 (by omega)]; decide)

theorem pc_thm_347510 : Nat.primeCounting 347510 = 29776 := primeCounting_step 340000 7511 29182 594 count_340000 (by rw [count_shift_is_prime_eq 340000 7511 (by omega)]; decide)

theorem pc_thm_348195 : Nat.primeCounting 348195 = 29831 := primeCounting_step 340000 8196 29182 649 count_340000 (by rw [count_shift_is_prime_eq 340000 8196 (by omega)]; decide)

theorem pc_thm_348690 : Nat.primeCounting 348690 = 29873 := primeCounting_step 340000 8691 29182 691 count_340000 (by rw [count_shift_is_prime_eq 340000 8691 (by omega)]; decide)

theorem pc_thm_349030 : Nat.primeCounting 349030 = 29896 := primeCounting_step 340000 9031 29182 714 count_340000 (by rw [count_shift_is_prime_eq 340000 9031 (by omega)]; decide)

theorem pc_thm_349866 : Nat.primeCounting 349866 = 29964 := primeCounting_step 340000 9867 29182 782 count_340000 (by rw [count_shift_is_prime_eq 340000 9867 (by omega)]; decide)

theorem pc_thm_349872 : Nat.primeCounting 349872 = 29965 := primeCounting_step 340000 9873 29182 783 count_340000 (by rw [count_shift_is_prime_eq 340000 9873 (by omega)]; decide)

theorem pc_thm_350703 : Nat.primeCounting 350703 = 30024 := primeCounting_step 340000 10704 29182 842 count_340000 (by rw [count_shift_is_prime_eq 340000 10704 (by omega)]; decide)

theorem pc_thm_351056 : Nat.primeCounting 351056 = 30058 := primeCounting_step 340000 11057 29182 876 count_340000 (by rw [count_shift_is_prime_eq 340000 11057 (by omega)]; decide)

theorem pc_thm_351541 : Nat.primeCounting 351541 = 30098 := primeCounting_step 340000 11542 29182 916 count_340000 (by rw [count_shift_is_prime_eq 340000 11542 (by omega)]; decide)

theorem pc_thm_352242 : Nat.primeCounting 352242 = 30151 := primeCounting_step 340000 12243 29182 969 count_340000 (by rw [count_shift_is_prime_eq 340000 12243 (by omega)]; decide)

theorem pc_thm_352380 : Nat.primeCounting 352380 = 30164 := primeCounting_step 340000 12381 29182 982 count_340000 (by rw [count_shift_is_prime_eq 340000 12381 (by omega)]; decide)

theorem pc_thm_353220 : Nat.primeCounting 353220 = 30232 := primeCounting_step 340000 13221 29182 1050 count_340000 (by rw [count_shift_is_prime_eq 340000 13221 (by omega)]; decide)

theorem pc_thm_353430 : Nat.primeCounting 353430 = 30245 := primeCounting_step 340000 13431 29182 1063 count_340000 (by rw [count_shift_is_prime_eq 340000 13431 (by omega)]; decide)

theorem pc_thm_354061 : Nat.primeCounting 354061 = 30299 := primeCounting_step 340000 14062 29182 1117 count_340000 (by rw [count_shift_is_prime_eq 340000 14062 (by omega)]; decide)

theorem pc_thm_354620 : Nat.primeCounting 354620 = 30345 := primeCounting_step 340000 14621 29182 1163 count_340000 (by rw [count_shift_is_prime_eq 340000 14621 (by omega)]; decide)

theorem pc_thm_354903 : Nat.primeCounting 354903 = 30369 := primeCounting_step 340000 14904 29182 1187 count_340000 (by rw [count_shift_is_prime_eq 340000 14904 (by omega)]; decide)

theorem pc_thm_355746 : Nat.primeCounting 355746 = 30436 := primeCounting_step 340000 15747 29182 1254 count_340000 (by rw [count_shift_is_prime_eq 340000 15747 (by omega)]; decide)

theorem pc_thm_355812 : Nat.primeCounting 355812 = 30442 := primeCounting_step 340000 15813 29182 1260 count_340000 (by rw [count_shift_is_prime_eq 340000 15813 (by omega)]; decide)

theorem pc_thm_356590 : Nat.primeCounting 356590 = 30496 := primeCounting_step 340000 16591 29182 1314 count_340000 (by rw [count_shift_is_prime_eq 340000 16591 (by omega)]; decide)

theorem pc_thm_357006 : Nat.primeCounting 357006 = 30523 := primeCounting_step 340000 17007 29182 1341 count_340000 (by rw [count_shift_is_prime_eq 340000 17007 (by omega)]; decide)

theorem pc_thm_357435 : Nat.primeCounting 357435 = 30555 := primeCounting_step 340000 17436 29182 1373 count_340000 (by rw [count_shift_is_prime_eq 340000 17436 (by omega)]; decide)

theorem pc_thm_358202 : Nat.primeCounting 358202 = 30615 := primeCounting_step 340000 18203 29182 1433 count_340000 (by rw [count_shift_is_prime_eq 340000 18203 (by omega)]; decide)

theorem pc_thm_358281 : Nat.primeCounting 358281 = 30623 := primeCounting_step 340000 18282 29182 1441 count_340000 (by rw [count_shift_is_prime_eq 340000 18282 (by omega)]; decide)

theorem pc_thm_359128 : Nat.primeCounting 359128 = 30694 := primeCounting_step 340000 19129 29182 1512 count_340000 (by rw [count_shift_is_prime_eq 340000 19129 (by omega)]; decide)

theorem pc_thm_359400 : Nat.primeCounting 359400 = 30718 := primeCounting_step 340000 19401 29182 1536 count_340000 (by rw [count_shift_is_prime_eq 340000 19401 (by omega)]; decide)

theorem pc_thm_359976 : Nat.primeCounting 359976 = 30755 := primeCounting_step 340000 19977 29182 1573 count_340000 (by rw [count_shift_is_prime_eq 340000 19977 (by omega)]; decide)

theorem pc_thm_360600 : Nat.primeCounting 360600 = 30798 := primeCounting_step 360000 601 30757 41 count_360000 (by rw [count_shift_is_prime_eq 360000 601 (by omega)]; decide)

theorem pc_thm_360825 : Nat.primeCounting 360825 = 30810 := primeCounting_step 360000 826 30757 53 count_360000 (by rw [count_shift_is_prime_eq 360000 826 (by omega)]; decide)

theorem pc_thm_361675 : Nat.primeCounting 361675 = 30877 := primeCounting_step 360000 1676 30757 120 count_360000 (by rw [count_shift_is_prime_eq 360000 1676 (by omega)]; decide)

theorem pc_thm_361802 : Nat.primeCounting 361802 = 30888 := primeCounting_step 360000 1803 30757 131 count_360000 (by rw [count_shift_is_prime_eq 360000 1803 (by omega)]; decide)

theorem pc_thm_362526 : Nat.primeCounting 362526 = 30949 := primeCounting_step 360000 2527 30757 192 count_360000 (by rw [count_shift_is_prime_eq 360000 2527 (by omega)]; decide)

theorem pc_thm_363006 : Nat.primeCounting 363006 = 30980 := primeCounting_step 360000 3007 30757 223 count_360000 (by rw [count_shift_is_prime_eq 360000 3007 (by omega)]; decide)

theorem pc_thm_363378 : Nat.primeCounting 363378 = 31011 := primeCounting_step 360000 3379 30757 254 count_360000 (by rw [count_shift_is_prime_eq 360000 3379 (by omega)]; decide)

theorem pc_thm_364212 : Nat.primeCounting 364212 = 31077 := primeCounting_step 360000 4213 30757 320 count_360000 (by rw [count_shift_is_prime_eq 360000 4213 (by omega)]; decide)

theorem pc_thm_364231 : Nat.primeCounting 364231 = 31079 := primeCounting_step 360000 4232 30757 322 count_360000 (by rw [count_shift_is_prime_eq 360000 4232 (by omega)]; decide)

theorem pc_thm_365085 : Nat.primeCounting 365085 = 31147 := primeCounting_step 360000 5086 30757 390 count_360000 (by rw [count_shift_is_prime_eq 360000 5086 (by omega)]; decide)

theorem pc_thm_365420 : Nat.primeCounting 365420 = 31174 := primeCounting_step 360000 5421 30757 417 count_360000 (by rw [count_shift_is_prime_eq 360000 5421 (by omega)]; decide)

theorem pc_thm_365940 : Nat.primeCounting 365940 = 31215 := primeCounting_step 360000 5941 30757 458 count_360000 (by rw [count_shift_is_prime_eq 360000 5941 (by omega)]; decide)

theorem pc_thm_366630 : Nat.primeCounting 366630 = 31272 := primeCounting_step 360000 6631 30757 515 count_360000 (by rw [count_shift_is_prime_eq 360000 6631 (by omega)]; decide)

theorem pc_thm_366796 : Nat.primeCounting 366796 = 31284 := primeCounting_step 360000 6797 30757 527 count_360000 (by rw [count_shift_is_prime_eq 360000 6797 (by omega)]; decide)

theorem pc_thm_367653 : Nat.primeCounting 367653 = 31356 := primeCounting_step 360000 7654 30757 599 count_360000 (by rw [count_shift_is_prime_eq 360000 7654 (by omega)]; decide)

theorem pc_thm_367842 : Nat.primeCounting 367842 = 31373 := primeCounting_step 360000 7843 30757 616 count_360000 (by rw [count_shift_is_prime_eq 360000 7843 (by omega)]; decide)

theorem pc_thm_368511 : Nat.primeCounting 368511 = 31421 := primeCounting_step 360000 8512 30757 664 count_360000 (by rw [count_shift_is_prime_eq 360000 8512 (by omega)]; decide)

theorem pc_thm_369056 : Nat.primeCounting 369056 = 31458 := primeCounting_step 360000 9057 30757 701 count_360000 (by rw [count_shift_is_prime_eq 360000 9057 (by omega)]; decide)

theorem pc_thm_369370 : Nat.primeCounting 369370 = 31483 := primeCounting_step 360000 9371 30757 726 count_360000 (by rw [count_shift_is_prime_eq 360000 9371 (by omega)]; decide)

theorem pc_thm_370230 : Nat.primeCounting 370230 = 31542 := primeCounting_step 360000 10231 30757 785 count_360000 (by rw [count_shift_is_prime_eq 360000 10231 (by omega)]; decide)

theorem pc_thm_370272 : Nat.primeCounting 370272 = 31545 := primeCounting_step 360000 10273 30757 788 count_360000 (by rw [count_shift_is_prime_eq 360000 10273 (by omega)]; decide)

theorem pc_thm_371091 : Nat.primeCounting 371091 = 31599 := primeCounting_step 360000 11092 30757 842 count_360000 (by rw [count_shift_is_prime_eq 360000 11092 (by omega)]; decide)

theorem pc_thm_371490 : Nat.primeCounting 371490 = 31633 := primeCounting_step 360000 11491 30757 876 count_360000 (by rw [count_shift_is_prime_eq 360000 11491 (by omega)]; decide)

theorem pc_thm_371953 : Nat.primeCounting 371953 = 31664 := primeCounting_step 360000 11954 30757 907 count_360000 (by rw [count_shift_is_prime_eq 360000 11954 (by omega)]; decide)

theorem pc_thm_372710 : Nat.primeCounting 372710 = 31723 := primeCounting_step 360000 12711 30757 966 count_360000 (by rw [count_shift_is_prime_eq 360000 12711 (by omega)]; decide)

theorem pc_thm_372816 : Nat.primeCounting 372816 = 31733 := primeCounting_step 360000 12817 30757 976 count_360000 (by rw [count_shift_is_prime_eq 360000 12817 (by omega)]; decide)

theorem pc_thm_373680 : Nat.primeCounting 373680 = 31801 := primeCounting_step 360000 13681 30757 1044 count_360000 (by rw [count_shift_is_prime_eq 360000 13681 (by omega)]; decide)

theorem pc_thm_373932 : Nat.primeCounting 373932 = 31814 := primeCounting_step 360000 13933 30757 1057 count_360000 (by rw [count_shift_is_prime_eq 360000 13933 (by omega)]; decide)

theorem pc_thm_374545 : Nat.primeCounting 374545 = 31864 := primeCounting_step 360000 14546 30757 1107 count_360000 (by rw [count_shift_is_prime_eq 360000 14546 (by omega)]; decide)

theorem pc_thm_375156 : Nat.primeCounting 375156 = 31920 := primeCounting_step 360000 15157 30757 1163 count_360000 (by rw [count_shift_is_prime_eq 360000 15157 (by omega)]; decide)

theorem pc_thm_375411 : Nat.primeCounting 375411 = 31943 := primeCounting_step 360000 15412 30757 1186 count_360000 (by rw [count_shift_is_prime_eq 360000 15412 (by omega)]; decide)

theorem pc_thm_376278 : Nat.primeCounting 376278 = 32009 := primeCounting_step 360000 16279 30757 1252 count_360000 (by rw [count_shift_is_prime_eq 360000 16279 (by omega)]; decide)

theorem pc_thm_376382 : Nat.primeCounting 376382 = 32015 := primeCounting_step 360000 16383 30757 1258 count_360000 (by rw [count_shift_is_prime_eq 360000 16383 (by omega)]; decide)

theorem pc_thm_377146 : Nat.primeCounting 377146 = 32078 := primeCounting_step 360000 17147 30757 1321 count_360000 (by rw [count_shift_is_prime_eq 360000 17147 (by omega)]; decide)

theorem pc_thm_377610 : Nat.primeCounting 377610 = 32114 := primeCounting_step 360000 17611 30757 1357 count_360000 (by rw [count_shift_is_prime_eq 360000 17611 (by omega)]; decide)

theorem pc_thm_378015 : Nat.primeCounting 378015 = 32141 := primeCounting_step 360000 18016 30757 1384 count_360000 (by rw [count_shift_is_prime_eq 360000 18016 (by omega)]; decide)

theorem pc_thm_378840 : Nat.primeCounting 378840 = 32205 := primeCounting_step 360000 18841 30757 1448 count_360000 (by rw [count_shift_is_prime_eq 360000 18841 (by omega)]; decide)

theorem pc_thm_378885 : Nat.primeCounting 378885 = 32207 := primeCounting_step 360000 18886 30757 1450 count_360000 (by rw [count_shift_is_prime_eq 360000 18886 (by omega)]; decide)

theorem pc_thm_379756 : Nat.primeCounting 379756 = 32280 := primeCounting_step 360000 19757 30757 1523 count_360000 (by rw [count_shift_is_prime_eq 360000 19757 (by omega)]; decide)

theorem pc_thm_380072 : Nat.primeCounting 380072 = 32304 := primeCounting_step 380000 73 32300 4 count_380000 (by rw [count_shift_is_prime_eq 380000 73 (by omega)]; decide)

theorem pc_thm_380628 : Nat.primeCounting 380628 = 32345 := primeCounting_step 380000 629 32300 45 count_380000 (by rw [count_shift_is_prime_eq 380000 629 (by omega)]; decide)

theorem pc_thm_381306 : Nat.primeCounting 381306 = 32394 := primeCounting_step 380000 1307 32300 94 count_380000 (by rw [count_shift_is_prime_eq 380000 1307 (by omega)]; decide)

theorem pc_thm_381501 : Nat.primeCounting 381501 = 32412 := primeCounting_step 380000 1502 32300 112 count_380000 (by rw [count_shift_is_prime_eq 380000 1502 (by omega)]; decide)

theorem pc_thm_382375 : Nat.primeCounting 382375 = 32473 := primeCounting_step 380000 2376 32300 173 count_380000 (by rw [count_shift_is_prime_eq 380000 2376 (by omega)]; decide)

theorem pc_thm_382542 : Nat.primeCounting 382542 = 32483 := primeCounting_step 380000 2543 32300 183 count_380000 (by rw [count_shift_is_prime_eq 380000 2543 (by omega)]; decide)

theorem pc_thm_383250 : Nat.primeCounting 383250 = 32542 := primeCounting_step 380000 3251 32300 242 count_380000 (by rw [count_shift_is_prime_eq 380000 3251 (by omega)]; decide)

theorem pc_thm_383780 : Nat.primeCounting 383780 = 32584 := primeCounting_step 380000 3781 32300 284 count_380000 (by rw [count_shift_is_prime_eq 380000 3781 (by omega)]; decide)

theorem pc_thm_384126 : Nat.primeCounting 384126 = 32613 := primeCounting_step 380000 4127 32300 313 count_380000 (by rw [count_shift_is_prime_eq 380000 4127 (by omega)]; decide)

theorem pc_thm_385003 : Nat.primeCounting 385003 = 32682 := primeCounting_step 380000 5004 32300 382 count_380000 (by rw [count_shift_is_prime_eq 380000 5004 (by omega)]; decide)

theorem pc_thm_385020 : Nat.primeCounting 385020 = 32683 := primeCounting_step 380000 5021 32300 383 count_380000 (by rw [count_shift_is_prime_eq 380000 5021 (by omega)]; decide)

theorem pc_thm_385881 : Nat.primeCounting 385881 = 32752 := primeCounting_step 380000 5882 32300 452 count_380000 (by rw [count_shift_is_prime_eq 380000 5882 (by omega)]; decide)

theorem pc_thm_386262 : Nat.primeCounting 386262 = 32783 := primeCounting_step 380000 6263 32300 483 count_380000 (by rw [count_shift_is_prime_eq 380000 6263 (by omega)]; decide)

theorem pc_thm_386760 : Nat.primeCounting 386760 = 32826 := primeCounting_step 380000 6761 32300 526 count_380000 (by rw [count_shift_is_prime_eq 380000 6761 (by omega)]; decide)

theorem pc_thm_387506 : Nat.primeCounting 387506 = 32875 := primeCounting_step 380000 7507 32300 575 count_380000 (by rw [count_shift_is_prime_eq 380000 7507 (by omega)]; decide)

theorem pc_thm_387640 : Nat.primeCounting 387640 = 32883 := primeCounting_step 380000 7641 32300 583 count_380000 (by rw [count_shift_is_prime_eq 380000 7641 (by omega)]; decide)

theorem pc_thm_388521 : Nat.primeCounting 388521 = 32949 := primeCounting_step 380000 8522 32300 649 count_380000 (by rw [count_shift_is_prime_eq 380000 8522 (by omega)]; decide)

theorem pc_thm_388752 : Nat.primeCounting 388752 = 32963 := primeCounting_step 380000 8753 32300 663 count_380000 (by rw [count_shift_is_prime_eq 380000 8753 (by omega)]; decide)

theorem pc_thm_389403 : Nat.primeCounting 389403 = 33016 := primeCounting_step 380000 9404 32300 716 count_380000 (by rw [count_shift_is_prime_eq 380000 9404 (by omega)]; decide)

theorem pc_thm_390000 : Nat.primeCounting 390000 = 33067 := primeCounting_step 380000 10001 32300 767 count_380000 (by rw [count_shift_is_prime_eq 380000 10001 (by omega)]; decide)

theorem pc_thm_390286 : Nat.primeCounting 390286 = 33089 := primeCounting_step 380000 10287 32300 789 count_380000 (by rw [count_shift_is_prime_eq 380000 10287 (by omega)]; decide)

theorem pc_thm_391170 : Nat.primeCounting 391170 = 33163 := primeCounting_step 380000 11171 32300 863 count_380000 (by rw [count_shift_is_prime_eq 380000 11171 (by omega)]; decide)

theorem pc_thm_391250 : Nat.primeCounting 391250 = 33170 := primeCounting_step 380000 11251 32300 870 count_380000 (by rw [count_shift_is_prime_eq 380000 11251 (by omega)]; decide)

theorem pc_thm_392055 : Nat.primeCounting 392055 = 33230 := primeCounting_step 380000 12056 32300 930 count_380000 (by rw [count_shift_is_prime_eq 380000 12056 (by omega)]; decide)

theorem pc_thm_392502 : Nat.primeCounting 392502 = 33273 := primeCounting_step 380000 12503 32300 973 count_380000 (by rw [count_shift_is_prime_eq 380000 12503 (by omega)]; decide)

theorem pc_thm_392941 : Nat.primeCounting 392941 = 33308 := primeCounting_step 380000 12942 32300 1008 count_380000 (by rw [count_shift_is_prime_eq 380000 12942 (by omega)]; decide)

theorem pc_thm_393756 : Nat.primeCounting 393756 = 33382 := primeCounting_step 380000 13757 32300 1082 count_380000 (by rw [count_shift_is_prime_eq 380000 13757 (by omega)]; decide)

theorem pc_thm_393828 : Nat.primeCounting 393828 = 33385 := primeCounting_step 380000 13829 32300 1085 count_380000 (by rw [count_shift_is_prime_eq 380000 13829 (by omega)]; decide)

theorem pc_thm_394716 : Nat.primeCounting 394716 = 33449 := primeCounting_step 380000 14717 32300 1149 count_380000 (by rw [count_shift_is_prime_eq 380000 14717 (by omega)]; decide)

theorem pc_thm_395012 : Nat.primeCounting 395012 = 33475 := primeCounting_step 380000 15013 32300 1175 count_380000 (by rw [count_shift_is_prime_eq 380000 15013 (by omega)]; decide)

theorem pc_thm_395605 : Nat.primeCounting 395605 = 33522 := primeCounting_step 380000 15606 32300 1222 count_380000 (by rw [count_shift_is_prime_eq 380000 15606 (by omega)]; decide)

theorem pc_thm_396270 : Nat.primeCounting 396270 = 33569 := primeCounting_step 380000 16271 32300 1269 count_380000 (by rw [count_shift_is_prime_eq 380000 16271 (by omega)]; decide)

theorem pc_thm_396495 : Nat.primeCounting 396495 = 33585 := primeCounting_step 380000 16496 32300 1285 count_380000 (by rw [count_shift_is_prime_eq 380000 16496 (by omega)]; decide)

theorem pc_thm_397386 : Nat.primeCounting 397386 = 33653 := primeCounting_step 380000 17387 32300 1353 count_380000 (by rw [count_shift_is_prime_eq 380000 17387 (by omega)]; decide)

theorem pc_thm_397530 : Nat.primeCounting 397530 = 33662 := primeCounting_step 380000 17531 32300 1362 count_380000 (by rw [count_shift_is_prime_eq 380000 17531 (by omega)]; decide)

theorem pc_thm_398278 : Nat.primeCounting 398278 = 33722 := primeCounting_step 380000 18279 32300 1422 count_380000 (by rw [count_shift_is_prime_eq 380000 18279 (by omega)]; decide)

theorem pc_thm_398792 : Nat.primeCounting 398792 = 33764 := primeCounting_step 380000 18793 32300 1464 count_380000 (by rw [count_shift_is_prime_eq 380000 18793 (by omega)]; decide)

theorem pc_thm_399171 : Nat.primeCounting 399171 = 33794 := primeCounting_step 380000 19172 32300 1494 count_380000 (by rw [count_shift_is_prime_eq 380000 19172 (by omega)]; decide)

theorem pc_thm_400056 : Nat.primeCounting 400056 = 33864 := primeCounting_step 400000 57 33860 4 count_400000 (by rw [count_shift_is_prime_eq 400000 57 (by omega)]; decide)

theorem pc_thm_400065 : Nat.primeCounting 400065 = 33864 := primeCounting_step 400000 66 33860 4 count_400000 (by rw [count_shift_is_prime_eq 400000 66 (by omega)]; decide)

theorem pc_thm_400960 : Nat.primeCounting 400960 = 33928 := primeCounting_step 400000 961 33860 68 count_400000 (by rw [count_shift_is_prime_eq 400000 961 (by omega)]; decide)

theorem pc_thm_401322 : Nat.primeCounting 401322 = 33954 := primeCounting_step 400000 1323 33860 94 count_400000 (by rw [count_shift_is_prime_eq 400000 1323 (by omega)]; decide)

theorem pc_thm_401856 : Nat.primeCounting 401856 = 33988 := primeCounting_step 400000 1857 33860 128 count_400000 (by rw [count_shift_is_prime_eq 400000 1857 (by omega)]; decide)

theorem pc_thm_402590 : Nat.primeCounting 402590 = 34049 := primeCounting_step 400000 2591 33860 189 count_400000 (by rw [count_shift_is_prime_eq 400000 2591 (by omega)]; decide)

theorem pc_thm_402753 : Nat.primeCounting 402753 = 34057 := primeCounting_step 400000 2754 33860 197 count_400000 (by rw [count_shift_is_prime_eq 400000 2754 (by omega)]; decide)

theorem pc_thm_403651 : Nat.primeCounting 403651 = 34125 := primeCounting_step 400000 3652 33860 265 count_400000 (by rw [count_shift_is_prime_eq 400000 3652 (by omega)]; decide)

theorem pc_thm_403860 : Nat.primeCounting 403860 = 34140 := primeCounting_step 400000 3861 33860 280 count_400000 (by rw [count_shift_is_prime_eq 400000 3861 (by omega)]; decide)

theorem pc_thm_404550 : Nat.primeCounting 404550 = 34200 := primeCounting_step 400000 4551 33860 340 count_400000 (by rw [count_shift_is_prime_eq 400000 4551 (by omega)]; decide)

theorem pc_thm_405132 : Nat.primeCounting 405132 = 34232 := primeCounting_step 400000 5133 33860 372 count_400000 (by rw [count_shift_is_prime_eq 400000 5133 (by omega)]; decide)

theorem pc_thm_405450 : Nat.primeCounting 405450 = 34257 := primeCounting_step 400000 5451 33860 397 count_400000 (by rw [count_shift_is_prime_eq 400000 5451 (by omega)]; decide)

theorem pc_thm_406351 : Nat.primeCounting 406351 = 34328 := primeCounting_step 400000 6352 33860 468 count_400000 (by rw [count_shift_is_prime_eq 400000 6352 (by omega)]; decide)

theorem pc_thm_406406 : Nat.primeCounting 406406 = 34332 := primeCounting_step 400000 6407 33860 472 count_400000 (by rw [count_shift_is_prime_eq 400000 6407 (by omega)]; decide)

theorem pc_thm_407253 : Nat.primeCounting 407253 = 34389 := primeCounting_step 400000 7254 33860 529 count_400000 (by rw [count_shift_is_prime_eq 400000 7254 (by omega)]; decide)

theorem pc_thm_407682 : Nat.primeCounting 407682 = 34425 := primeCounting_step 400000 7683 33860 565 count_400000 (by rw [count_shift_is_prime_eq 400000 7683 (by omega)]; decide)

theorem pc_thm_408156 : Nat.primeCounting 408156 = 34463 := primeCounting_step 400000 8157 33860 603 count_400000 (by rw [count_shift_is_prime_eq 400000 8157 (by omega)]; decide)

theorem pc_thm_408960 : Nat.primeCounting 408960 = 34529 := primeCounting_step 400000 8961 33860 669 count_400000 (by rw [count_shift_is_prime_eq 400000 8961 (by omega)]; decide)

theorem pc_thm_409060 : Nat.primeCounting 409060 = 34537 := primeCounting_step 400000 9061 33860 677 count_400000 (by rw [count_shift_is_prime_eq 400000 9061 (by omega)]; decide)

theorem pc_thm_409965 : Nat.primeCounting 409965 = 34610 := primeCounting_step 400000 9966 33860 750 count_400000 (by rw [count_shift_is_prime_eq 400000 9966 (by omega)]; decide)

theorem pc_thm_410240 : Nat.primeCounting 410240 = 34630 := primeCounting_step 400000 10241 33860 770 count_400000 (by rw [count_shift_is_prime_eq 400000 10241 (by omega)]; decide)

theorem pc_thm_410871 : Nat.primeCounting 410871 = 34681 := primeCounting_step 400000 10872 33860 821 count_400000 (by rw [count_shift_is_prime_eq 400000 10872 (by omega)]; decide)

theorem pc_thm_411522 : Nat.primeCounting 411522 = 34728 := primeCounting_step 400000 11523 33860 868 count_400000 (by rw [count_shift_is_prime_eq 400000 11523 (by omega)]; decide)

theorem pc_thm_411778 : Nat.primeCounting 411778 = 34753 := primeCounting_step 400000 11779 33860 893 count_400000 (by rw [count_shift_is_prime_eq 400000 11779 (by omega)]; decide)

theorem pc_thm_412686 : Nat.primeCounting 412686 = 34826 := primeCounting_step 400000 12687 33860 966 count_400000 (by rw [count_shift_is_prime_eq 400000 12687 (by omega)]; decide)

theorem pc_thm_412806 : Nat.primeCounting 412806 = 34830 := primeCounting_step 400000 12807 33860 970 count_400000 (by rw [count_shift_is_prime_eq 400000 12807 (by omega)]; decide)

theorem pc_thm_413595 : Nat.primeCounting 413595 = 34885 := primeCounting_step 400000 13596 33860 1025 count_400000 (by rw [count_shift_is_prime_eq 400000 13596 (by omega)]; decide)

theorem pc_thm_414092 : Nat.primeCounting 414092 = 34920 := primeCounting_step 400000 14093 33860 1060 count_400000 (by rw [count_shift_is_prime_eq 400000 14093 (by omega)]; decide)

theorem pc_thm_414505 : Nat.primeCounting 414505 = 34956 := primeCounting_step 400000 14506 33860 1096 count_400000 (by rw [count_shift_is_prime_eq 400000 14506 (by omega)]; decide)

theorem pc_thm_415380 : Nat.primeCounting 415380 = 35028 := primeCounting_step 400000 15381 33860 1168 count_400000 (by rw [count_shift_is_prime_eq 400000 15381 (by omega)]; decide)

theorem pc_thm_415416 : Nat.primeCounting 415416 = 35031 := primeCounting_step 400000 15417 33860 1171 count_400000 (by rw [count_shift_is_prime_eq 400000 15417 (by omega)]; decide)

theorem pc_thm_416328 : Nat.primeCounting 416328 = 35101 := primeCounting_step 400000 16329 33860 1241 count_400000 (by rw [count_shift_is_prime_eq 400000 16329 (by omega)]; decide)

theorem pc_thm_416670 : Nat.primeCounting 416670 = 35131 := primeCounting_step 400000 16671 33860 1271 count_400000 (by rw [count_shift_is_prime_eq 400000 16671 (by omega)]; decide)

theorem pc_thm_417241 : Nat.primeCounting 417241 = 35169 := primeCounting_step 400000 17242 33860 1309 count_400000 (by rw [count_shift_is_prime_eq 400000 17242 (by omega)]; decide)

theorem pc_thm_417962 : Nat.primeCounting 417962 = 35228 := primeCounting_step 400000 17963 33860 1368 count_400000 (by rw [count_shift_is_prime_eq 400000 17963 (by omega)]; decide)

theorem pc_thm_418155 : Nat.primeCounting 418155 = 35242 := primeCounting_step 400000 18156 33860 1382 count_400000 (by rw [count_shift_is_prime_eq 400000 18156 (by omega)]; decide)

theorem pc_thm_419070 : Nat.primeCounting 419070 = 35320 := primeCounting_step 400000 19071 33860 1460 count_400000 (by rw [count_shift_is_prime_eq 400000 19071 (by omega)]; decide)

theorem pc_thm_419256 : Nat.primeCounting 419256 = 35331 := primeCounting_step 400000 19257 33860 1471 count_400000 (by rw [count_shift_is_prime_eq 400000 19257 (by omega)]; decide)

theorem pc_thm_419986 : Nat.primeCounting 419986 = 35389 := primeCounting_step 400000 19987 33860 1529 count_400000 (by rw [count_shift_is_prime_eq 400000 19987 (by omega)]; decide)

theorem pc_thm_420552 : Nat.primeCounting 420552 = 35433 := primeCounting_step 420000 553 35390 43 count_420000 (by rw [count_shift_is_prime_eq 420000 553 (by omega)]; decide)

theorem pc_thm_420903 : Nat.primeCounting 420903 = 35459 := primeCounting_step 420000 904 35390 69 count_420000 (by rw [count_shift_is_prime_eq 420000 904 (by omega)]; decide)

theorem pc_thm_421821 : Nat.primeCounting 421821 = 35529 := primeCounting_step 420000 1822 35390 139 count_420000 (by rw [count_shift_is_prime_eq 420000 1822 (by omega)]; decide)

theorem pc_thm_421850 : Nat.primeCounting 421850 = 35531 := primeCounting_step 420000 1851 35390 141 count_420000 (by rw [count_shift_is_prime_eq 420000 1851 (by omega)]; decide)

theorem pc_thm_422740 : Nat.primeCounting 422740 = 35593 := primeCounting_step 420000 2741 35390 203 count_420000 (by rw [count_shift_is_prime_eq 420000 2741 (by omega)]; decide)

theorem pc_thm_423150 : Nat.primeCounting 423150 = 35630 := primeCounting_step 420000 3151 35390 240 count_420000 (by rw [count_shift_is_prime_eq 420000 3151 (by omega)]; decide)

theorem pc_thm_423660 : Nat.primeCounting 423660 = 35672 := primeCounting_step 420000 3661 35390 282 count_420000 (by rw [count_shift_is_prime_eq 420000 3661 (by omega)]; decide)

theorem pc_thm_424452 : Nat.primeCounting 424452 = 35736 := primeCounting_step 420000 4453 35390 346 count_420000 (by rw [count_shift_is_prime_eq 420000 4453 (by omega)]; decide)

theorem pc_thm_424581 : Nat.primeCounting 424581 = 35746 := primeCounting_step 420000 4582 35390 356 count_420000 (by rw [count_shift_is_prime_eq 420000 4582 (by omega)]; decide)

theorem pc_thm_425503 : Nat.primeCounting 425503 = 35819 := primeCounting_step 420000 5504 35390 429 count_420000 (by rw [count_shift_is_prime_eq 420000 5504 (by omega)]; decide)

theorem pc_thm_425756 : Nat.primeCounting 425756 = 35832 := primeCounting_step 420000 5757 35390 442 count_420000 (by rw [count_shift_is_prime_eq 420000 5757 (by omega)]; decide)

theorem pc_thm_426426 : Nat.primeCounting 426426 = 35881 := primeCounting_step 420000 6427 35390 491 count_420000 (by rw [count_shift_is_prime_eq 420000 6427 (by omega)]; decide)

theorem pc_thm_427062 : Nat.primeCounting 427062 = 35928 := primeCounting_step 420000 7063 35390 538 count_420000 (by rw [count_shift_is_prime_eq 420000 7063 (by omega)]; decide)

theorem pc_thm_427350 : Nat.primeCounting 427350 = 35950 := primeCounting_step 420000 7351 35390 560 count_420000 (by rw [count_shift_is_prime_eq 420000 7351 (by omega)]; decide)

theorem pc_thm_428275 : Nat.primeCounting 428275 = 36025 := primeCounting_step 420000 8276 35390 635 count_420000 (by rw [count_shift_is_prime_eq 420000 8276 (by omega)]; decide)

theorem pc_thm_428370 : Nat.primeCounting 428370 = 36031 := primeCounting_step 420000 8371 35390 641 count_420000 (by rw [count_shift_is_prime_eq 420000 8371 (by omega)]; decide)

theorem pc_thm_429201 : Nat.primeCounting 429201 = 36086 := primeCounting_step 420000 9202 35390 696 count_420000 (by rw [count_shift_is_prime_eq 420000 9202 (by omega)]; decide)

theorem pc_thm_429680 : Nat.primeCounting 429680 = 36132 := primeCounting_step 420000 9681 35390 742 count_420000 (by rw [count_shift_is_prime_eq 420000 9681 (by omega)]; decide)

theorem pc_thm_430128 : Nat.primeCounting 430128 = 36172 := primeCounting_step 420000 10129 35390 782 count_420000 (by rw [count_shift_is_prime_eq 420000 10129 (by omega)]; decide)

theorem pc_thm_430992 : Nat.primeCounting 430992 = 36237 := primeCounting_step 420000 10993 35390 847 count_420000 (by rw [count_shift_is_prime_eq 420000 10993 (by omega)]; decide)

theorem pc_thm_431056 : Nat.primeCounting 431056 = 36243 := primeCounting_step 420000 11057 35390 853 count_420000 (by rw [count_shift_is_prime_eq 420000 11057 (by omega)]; decide)

theorem pc_thm_431985 : Nat.primeCounting 431985 = 36316 := primeCounting_step 420000 11986 35390 926 count_420000 (by rw [count_shift_is_prime_eq 420000 11986 (by omega)]; decide)

theorem pc_thm_432306 : Nat.primeCounting 432306 = 36345 := primeCounting_step 420000 12307 35390 955 count_420000 (by rw [count_shift_is_prime_eq 420000 12307 (by omega)]; decide)

theorem pc_thm_432915 : Nat.primeCounting 432915 = 36394 := primeCounting_step 420000 12916 35390 1004 count_420000 (by rw [count_shift_is_prime_eq 420000 12916 (by omega)]; decide)

theorem pc_thm_433622 : Nat.primeCounting 433622 = 36451 := primeCounting_step 420000 13623 35390 1061 count_420000 (by rw [count_shift_is_prime_eq 420000 13623 (by omega)]; decide)

theorem pc_thm_433846 : Nat.primeCounting 433846 = 36470 := primeCounting_step 420000 13847 35390 1080 count_420000 (by rw [count_shift_is_prime_eq 420000 13847 (by omega)]; decide)

theorem pc_thm_434778 : Nat.primeCounting 434778 = 36541 := primeCounting_step 420000 14779 35390 1151 count_420000 (by rw [count_shift_is_prime_eq 420000 14779 (by omega)]; decide)

theorem pc_thm_434940 : Nat.primeCounting 434940 = 36560 := primeCounting_step 420000 14941 35390 1170 count_420000 (by rw [count_shift_is_prime_eq 420000 14941 (by omega)]; decide)

theorem pc_thm_435711 : Nat.primeCounting 435711 = 36625 := primeCounting_step 420000 15712 35390 1235 count_420000 (by rw [count_shift_is_prime_eq 420000 15712 (by omega)]; decide)

theorem pc_thm_436260 : Nat.primeCounting 436260 = 36665 := primeCounting_step 420000 16261 35390 1275 count_420000 (by rw [count_shift_is_prime_eq 420000 16261 (by omega)]; decide)

theorem pc_thm_436645 : Nat.primeCounting 436645 = 36694 := primeCounting_step 420000 16646 35390 1304 count_420000 (by rw [count_shift_is_prime_eq 420000 16646 (by omega)]; decide)

theorem pc_thm_437580 : Nat.primeCounting 437580 = 36764 := primeCounting_step 420000 17581 35390 1374 count_420000 (by rw [count_shift_is_prime_eq 420000 17581 (by omega)]; decide)

theorem pc_thm_437582 : Nat.primeCounting 437582 = 36764 := primeCounting_step 420000 17583 35390 1374 count_420000 (by rw [count_shift_is_prime_eq 420000 17583 (by omega)]; decide)

theorem pc_thm_438516 : Nat.primeCounting 438516 = 36825 := primeCounting_step 420000 18517 35390 1435 count_420000 (by rw [count_shift_is_prime_eq 420000 18517 (by omega)]; decide)

theorem pc_thm_438906 : Nat.primeCounting 438906 = 36857 := primeCounting_step 420000 18907 35390 1467 count_420000 (by rw [count_shift_is_prime_eq 420000 18907 (by omega)]; decide)

theorem pc_thm_439453 : Nat.primeCounting 439453 = 36894 := primeCounting_step 420000 19454 35390 1504 count_420000 (by rw [count_shift_is_prime_eq 420000 19454 (by omega)]; decide)

theorem pc_thm_440232 : Nat.primeCounting 440232 = 36958 := primeCounting_step 440000 233 36941 17 count_440000 (by rw [count_shift_is_prime_eq 440000 233 (by omega)]; decide)

theorem pc_thm_440391 : Nat.primeCounting 440391 = 36971 := primeCounting_step 440000 392 36941 30 count_440000 (by rw [count_shift_is_prime_eq 440000 392 (by omega)]; decide)

theorem pc_thm_441330 : Nat.primeCounting 441330 = 37047 := primeCounting_step 440000 1331 36941 106 count_440000 (by rw [count_shift_is_prime_eq 440000 1331 (by omega)]; decide)

theorem pc_thm_441560 : Nat.primeCounting 441560 = 37062 := primeCounting_step 440000 1561 36941 121 count_440000 (by rw [count_shift_is_prime_eq 440000 1561 (by omega)]; decide)

theorem pc_thm_442270 : Nat.primeCounting 442270 = 37118 := primeCounting_step 440000 2271 36941 177 count_440000 (by rw [count_shift_is_prime_eq 440000 2271 (by omega)]; decide)

theorem pc_thm_442890 : Nat.primeCounting 442890 = 37168 := primeCounting_step 440000 2891 36941 227 count_440000 (by rw [count_shift_is_prime_eq 440000 2891 (by omega)]; decide)

theorem pc_thm_443211 : Nat.primeCounting 443211 = 37197 := primeCounting_step 440000 3212 36941 256 count_440000 (by rw [count_shift_is_prime_eq 440000 3212 (by omega)]; decide)

theorem pc_thm_444153 : Nat.primeCounting 444153 = 37278 := primeCounting_step 440000 4154 36941 337 count_440000 (by rw [count_shift_is_prime_eq 440000 4154 (by omega)]; decide)

theorem pc_thm_444222 : Nat.primeCounting 444222 = 37284 := primeCounting_step 440000 4223 36941 343 count_440000 (by rw [count_shift_is_prime_eq 440000 4223 (by omega)]; decide)

theorem pc_thm_445096 : Nat.primeCounting 445096 = 37355 := primeCounting_step 440000 5097 36941 414 count_440000 (by rw [count_shift_is_prime_eq 440000 5097 (by omega)]; decide)

theorem pc_thm_445556 : Nat.primeCounting 445556 = 37383 := primeCounting_step 440000 5557 36941 442 count_440000 (by rw [count_shift_is_prime_eq 440000 5557 (by omega)]; decide)

theorem pc_thm_446040 : Nat.primeCounting 446040 = 37417 := primeCounting_step 440000 6041 36941 476 count_440000 (by rw [count_shift_is_prime_eq 440000 6041 (by omega)]; decide)

theorem pc_thm_446892 : Nat.primeCounting 446892 = 37475 := primeCounting_step 440000 6893 36941 534 count_440000 (by rw [count_shift_is_prime_eq 440000 6893 (by omega)]; decide)

theorem pc_thm_446985 : Nat.primeCounting 446985 = 37483 := primeCounting_step 440000 6986 36941 542 count_440000 (by rw [count_shift_is_prime_eq 440000 6986 (by omega)]; decide)

theorem pc_thm_447931 : Nat.primeCounting 447931 = 37552 := primeCounting_step 440000 7932 36941 611 count_440000 (by rw [count_shift_is_prime_eq 440000 7932 (by omega)]; decide)

theorem pc_thm_448230 : Nat.primeCounting 448230 = 37576 := primeCounting_step 440000 8231 36941 635 count_440000 (by rw [count_shift_is_prime_eq 440000 8231 (by omega)]; decide)

theorem pc_thm_448878 : Nat.primeCounting 448878 = 37617 := primeCounting_step 440000 8879 36941 676 count_440000 (by rw [count_shift_is_prime_eq 440000 8879 (by omega)]; decide)

theorem pc_thm_449570 : Nat.primeCounting 449570 = 37674 := primeCounting_step 440000 9571 36941 733 count_440000 (by rw [count_shift_is_prime_eq 440000 9571 (by omega)]; decide)

theorem pc_thm_449826 : Nat.primeCounting 449826 = 37694 := primeCounting_step 440000 9827 36941 753 count_440000 (by rw [count_shift_is_prime_eq 440000 9827 (by omega)]; decide)

theorem pc_thm_450775 : Nat.primeCounting 450775 = 37773 := primeCounting_step 440000 10776 36941 832 count_440000 (by rw [count_shift_is_prime_eq 440000 10776 (by omega)]; decide)

theorem pc_thm_450912 : Nat.primeCounting 450912 = 37790 := primeCounting_step 440000 10913 36941 849 count_440000 (by rw [count_shift_is_prime_eq 440000 10913 (by omega)]; decide)

theorem pc_thm_451725 : Nat.primeCounting 451725 = 37851 := primeCounting_step 440000 11726 36941 910 count_440000 (by rw [count_shift_is_prime_eq 440000 11726 (by omega)]; decide)

theorem pc_thm_452256 : Nat.primeCounting 452256 = 37892 := primeCounting_step 440000 12257 36941 951 count_440000 (by rw [count_shift_is_prime_eq 440000 12257 (by omega)]; decide)

theorem pc_thm_452676 : Nat.primeCounting 452676 = 37918 := primeCounting_step 440000 12677 36941 977 count_440000 (by rw [count_shift_is_prime_eq 440000 12677 (by omega)]; decide)

theorem pc_thm_453602 : Nat.primeCounting 453602 = 37978 := primeCounting_step 440000 13603 36941 1037 count_440000 (by rw [count_shift_is_prime_eq 440000 13603 (by omega)]; decide)

theorem pc_thm_453628 : Nat.primeCounting 453628 = 37979 := primeCounting_step 440000 13629 36941 1038 count_440000 (by rw [count_shift_is_prime_eq 440000 13629 (by omega)]; decide)

theorem pc_thm_454581 : Nat.primeCounting 454581 = 38053 := primeCounting_step 440000 14582 36941 1112 count_440000 (by rw [count_shift_is_prime_eq 440000 14582 (by omega)]; decide)

theorem pc_thm_454950 : Nat.primeCounting 454950 = 38079 := primeCounting_step 440000 14951 36941 1138 count_440000 (by rw [count_shift_is_prime_eq 440000 14951 (by omega)]; decide)

theorem pc_thm_455535 : Nat.primeCounting 455535 = 38129 := primeCounting_step 440000 15536 36941 1188 count_440000 (by rw [count_shift_is_prime_eq 440000 15536 (by omega)]; decide)

theorem pc_thm_456300 : Nat.primeCounting 456300 = 38184 := primeCounting_step 440000 16301 36941 1243 count_440000 (by rw [count_shift_is_prime_eq 440000 16301 (by omega)]; decide)

theorem pc_thm_456490 : Nat.primeCounting 456490 = 38196 := primeCounting_step 440000 16491 36941 1255 count_440000 (by rw [count_shift_is_prime_eq 440000 16491 (by omega)]; decide)

theorem pc_thm_457446 : Nat.primeCounting 457446 = 38278 := primeCounting_step 440000 17447 36941 1337 count_440000 (by rw [count_shift_is_prime_eq 440000 17447 (by omega)]; decide)

theorem pc_thm_457652 : Nat.primeCounting 457652 = 38292 := primeCounting_step 440000 17653 36941 1351 count_440000 (by rw [count_shift_is_prime_eq 440000 17653 (by omega)]; decide)

theorem pc_thm_458403 : Nat.primeCounting 458403 = 38343 := primeCounting_step 440000 18404 36941 1402 count_440000 (by rw [count_shift_is_prime_eq 440000 18404 (by omega)]; decide)

theorem pc_thm_459006 : Nat.primeCounting 459006 = 38390 := primeCounting_step 440000 19007 36941 1449 count_440000 (by rw [count_shift_is_prime_eq 440000 19007 (by omega)]; decide)

theorem pc_thm_459361 : Nat.primeCounting 459361 = 38418 := primeCounting_step 440000 19362 36941 1477 count_440000 (by rw [count_shift_is_prime_eq 440000 19362 (by omega)]; decide)

theorem pc_thm_460320 : Nat.primeCounting 460320 = 38483 := primeCounting_step 460000 321 38458 25 count_460000 (by rw [count_shift_is_prime_eq 460000 321 (by omega)]; decide)

theorem pc_thm_460362 : Nat.primeCounting 460362 = 38485 := primeCounting_step 460000 363 38458 27 count_460000 (by rw [count_shift_is_prime_eq 460000 363 (by omega)]; decide)

theorem pc_thm_461280 : Nat.primeCounting 461280 = 38555 := primeCounting_step 460000 1281 38458 97 count_460000 (by rw [count_shift_is_prime_eq 460000 1281 (by omega)]; decide)

theorem pc_thm_461720 : Nat.primeCounting 461720 = 38590 := primeCounting_step 460000 1721 38458 132 count_460000 (by rw [count_shift_is_prime_eq 460000 1721 (by omega)]; decide)

theorem pc_thm_462241 : Nat.primeCounting 462241 = 38620 := primeCounting_step 460000 2242 38458 162 count_460000 (by rw [count_shift_is_prime_eq 460000 2242 (by omega)]; decide)

theorem pc_thm_463080 : Nat.primeCounting 463080 = 38681 := primeCounting_step 460000 3081 38458 223 count_460000 (by rw [count_shift_is_prime_eq 460000 3081 (by omega)]; decide)

theorem pc_thm_463203 : Nat.primeCounting 463203 = 38686 := primeCounting_step 460000 3204 38458 228 count_460000 (by rw [count_shift_is_prime_eq 460000 3204 (by omega)]; decide)

theorem pc_thm_464166 : Nat.primeCounting 464166 = 38769 := primeCounting_step 460000 4167 38458 311 count_460000 (by rw [count_shift_is_prime_eq 460000 4167 (by omega)]; decide)

theorem pc_thm_464442 : Nat.primeCounting 464442 = 38791 := primeCounting_step 460000 4443 38458 333 count_460000 (by rw [count_shift_is_prime_eq 460000 4443 (by omega)]; decide)

theorem pc_thm_465130 : Nat.primeCounting 465130 = 38853 := primeCounting_step 460000 5131 38458 395 count_460000 (by rw [count_shift_is_prime_eq 460000 5131 (by omega)]; decide)

theorem pc_thm_465806 : Nat.primeCounting 465806 = 38901 := primeCounting_step 460000 5807 38458 443 count_460000 (by rw [count_shift_is_prime_eq 460000 5807 (by omega)]; decide)

theorem pc_thm_466095 : Nat.primeCounting 466095 = 38925 := primeCounting_step 460000 6096 38458 467 count_460000 (by rw [count_shift_is_prime_eq 460000 6096 (by omega)]; decide)

theorem pc_thm_467061 : Nat.primeCounting 467061 = 38987 := primeCounting_step 460000 7062 38458 529 count_460000 (by rw [count_shift_is_prime_eq 460000 7062 (by omega)]; decide)

theorem pc_thm_467172 : Nat.primeCounting 467172 = 38996 := primeCounting_step 460000 7173 38458 538 count_460000 (by rw [count_shift_is_prime_eq 460000 7173 (by omega)]; decide)

theorem pc_thm_468028 : Nat.primeCounting 468028 = 39069 := primeCounting_step 460000 8029 38458 611 count_460000 (by rw [count_shift_is_prime_eq 460000 8029 (by omega)]; decide)

theorem pc_thm_468540 : Nat.primeCounting 468540 = 39109 := primeCounting_step 460000 8541 38458 651 count_460000 (by rw [count_shift_is_prime_eq 460000 8541 (by omega)]; decide)

theorem pc_thm_468996 : Nat.primeCounting 468996 = 39151 := primeCounting_step 460000 8997 38458 693 count_460000 (by rw [count_shift_is_prime_eq 460000 8997 (by omega)]; decide)

theorem pc_thm_469910 : Nat.primeCounting 469910 = 39217 := primeCounting_step 460000 9911 38458 759 count_460000 (by rw [count_shift_is_prime_eq 460000 9911 (by omega)]; decide)

theorem pc_thm_469965 : Nat.primeCounting 469965 = 39220 := primeCounting_step 460000 9966 38458 762 count_460000 (by rw [count_shift_is_prime_eq 460000 9966 (by omega)]; decide)

theorem pc_thm_470935 : Nat.primeCounting 470935 = 39304 := primeCounting_step 460000 10936 38458 846 count_460000 (by rw [count_shift_is_prime_eq 460000 10936 (by omega)]; decide)

theorem pc_thm_471282 : Nat.primeCounting 471282 = 39331 := primeCounting_step 460000 11283 38458 873 count_460000 (by rw [count_shift_is_prime_eq 460000 11283 (by omega)]; decide)

theorem pc_thm_471906 : Nat.primeCounting 471906 = 39380 := primeCounting_step 460000 11907 38458 922 count_460000 (by rw [count_shift_is_prime_eq 460000 11907 (by omega)]; decide)

theorem pc_thm_472656 : Nat.primeCounting 472656 = 39436 := primeCounting_step 460000 12657 38458 978 count_460000 (by rw [count_shift_is_prime_eq 460000 12657 (by omega)]; decide)

theorem pc_thm_472878 : Nat.primeCounting 472878 = 39453 := primeCounting_step 460000 12879 38458 995 count_460000 (by rw [count_shift_is_prime_eq 460000 12879 (by omega)]; decide)

theorem pc_thm_473851 : Nat.primeCounting 473851 = 39523 := primeCounting_step 460000 13852 38458 1065 count_460000 (by rw [count_shift_is_prime_eq 460000 13852 (by omega)]; decide)

theorem pc_thm_474032 : Nat.primeCounting 474032 = 39541 := primeCounting_step 460000 14033 38458 1083 count_460000 (by rw [count_shift_is_prime_eq 460000 14033 (by omega)]; decide)

theorem pc_thm_474825 : Nat.primeCounting 474825 = 39604 := primeCounting_step 460000 14826 38458 1146 count_460000 (by rw [count_shift_is_prime_eq 460000 14826 (by omega)]; decide)

theorem pc_thm_475410 : Nat.primeCounting 475410 = 39651 := primeCounting_step 460000 15411 38458 1193 count_460000 (by rw [count_shift_is_prime_eq 460000 15411 (by omega)]; decide)

theorem pc_thm_475800 : Nat.primeCounting 475800 = 39686 := primeCounting_step 460000 15801 38458 1228 count_460000 (by rw [count_shift_is_prime_eq 460000 15801 (by omega)]; decide)

theorem pc_thm_476776 : Nat.primeCounting 476776 = 39765 := primeCounting_step 460000 16777 38458 1307 count_460000 (by rw [count_shift_is_prime_eq 460000 16777 (by omega)]; decide)

theorem pc_thm_476790 : Nat.primeCounting 476790 = 39766 := primeCounting_step 460000 16791 38458 1308 count_460000 (by rw [count_shift_is_prime_eq 460000 16791 (by omega)]; decide)

theorem pc_thm_477753 : Nat.primeCounting 477753 = 39829 := primeCounting_step 460000 17754 38458 1371 count_460000 (by rw [count_shift_is_prime_eq 460000 17754 (by omega)]; decide)

theorem pc_thm_478172 : Nat.primeCounting 478172 = 39862 := primeCounting_step 460000 18173 38458 1404 count_460000 (by rw [count_shift_is_prime_eq 460000 18173 (by omega)]; decide)

theorem pc_thm_478731 : Nat.primeCounting 478731 = 39907 := primeCounting_step 460000 18732 38458 1449 count_460000 (by rw [count_shift_is_prime_eq 460000 18732 (by omega)]; decide)

theorem pc_thm_479556 : Nat.primeCounting 479556 = 39974 := primeCounting_step 460000 19557 38458 1516 count_460000 (by rw [count_shift_is_prime_eq 460000 19557 (by omega)]; decide)

theorem pc_thm_479710 : Nat.primeCounting 479710 = 39983 := primeCounting_step 460000 19711 38458 1525 count_460000 (by rw [count_shift_is_prime_eq 460000 19711 (by omega)]; decide)

theorem pc_thm_480690 : Nat.primeCounting 480690 = 40060 := primeCounting_step 480000 691 40005 55 count_480000 (by rw [count_shift_is_prime_eq 480000 691 (by omega)]; decide)

theorem pc_thm_480942 : Nat.primeCounting 480942 = 40078 := primeCounting_step 480000 943 40005 73 count_480000 (by rw [count_shift_is_prime_eq 480000 943 (by omega)]; decide)

theorem pc_thm_481671 : Nat.primeCounting 481671 = 40135 := primeCounting_step 480000 1672 40005 130 count_480000 (by rw [count_shift_is_prime_eq 480000 1672 (by omega)]; decide)

theorem pc_thm_482330 : Nat.primeCounting 482330 = 40184 := primeCounting_step 480000 2331 40005 179 count_480000 (by rw [count_shift_is_prime_eq 480000 2331 (by omega)]; decide)

theorem pc_thm_482653 : Nat.primeCounting 482653 = 40212 := primeCounting_step 480000 2654 40005 207 count_480000 (by rw [count_shift_is_prime_eq 480000 2654 (by omega)]; decide)

theorem pc_thm_483636 : Nat.primeCounting 483636 = 40288 := primeCounting_step 480000 3637 40005 283 count_480000 (by rw [count_shift_is_prime_eq 480000 3637 (by omega)]; decide)

theorem pc_thm_483720 : Nat.primeCounting 483720 = 40294 := primeCounting_step 480000 3721 40005 289 count_480000 (by rw [count_shift_is_prime_eq 480000 3721 (by omega)]; decide)

theorem pc_thm_484620 : Nat.primeCounting 484620 = 40363 := primeCounting_step 480000 4621 40005 358 count_480000 (by rw [count_shift_is_prime_eq 480000 4621 (by omega)]; decide)

theorem pc_thm_485112 : Nat.primeCounting 485112 = 40390 := primeCounting_step 480000 5113 40005 385 count_480000 (by rw [count_shift_is_prime_eq 480000 5113 (by omega)]; decide)

theorem pc_thm_485605 : Nat.primeCounting 485605 = 40422 := primeCounting_step 480000 5606 40005 417 count_480000 (by rw [count_shift_is_prime_eq 480000 5606 (by omega)]; decide)

theorem pc_thm_486506 : Nat.primeCounting 486506 = 40486 := primeCounting_step 480000 6507 40005 481 count_480000 (by rw [count_shift_is_prime_eq 480000 6507 (by omega)]; decide)

theorem pc_thm_486591 : Nat.primeCounting 486591 = 40494 := primeCounting_step 480000 6592 40005 489 count_480000 (by rw [count_shift_is_prime_eq 480000 6592 (by omega)]; decide)

theorem pc_thm_487578 : Nat.primeCounting 487578 = 40570 := primeCounting_step 480000 7579 40005 565 count_480000 (by rw [count_shift_is_prime_eq 480000 7579 (by omega)]; decide)

theorem pc_thm_487902 : Nat.primeCounting 487902 = 40600 := primeCounting_step 480000 7903 40005 595 count_480000 (by rw [count_shift_is_prime_eq 480000 7903 (by omega)]; decide)

theorem pc_thm_488566 : Nat.primeCounting 488566 = 40652 := primeCounting_step 480000 8567 40005 647 count_480000 (by rw [count_shift_is_prime_eq 480000 8567 (by omega)]; decide)

theorem pc_thm_489300 : Nat.primeCounting 489300 = 40711 := primeCounting_step 480000 9301 40005 706 count_480000 (by rw [count_shift_is_prime_eq 480000 9301 (by omega)]; decide)

theorem pc_thm_489555 : Nat.primeCounting 489555 = 40731 := primeCounting_step 480000 9556 40005 726 count_480000 (by rw [count_shift_is_prime_eq 480000 9556 (by omega)]; decide)

theorem pc_thm_490545 : Nat.primeCounting 490545 = 40808 := primeCounting_step 480000 10546 40005 803 count_480000 (by rw [count_shift_is_prime_eq 480000 10546 (by omega)]; decide)

theorem pc_thm_490700 : Nat.primeCounting 490700 = 40822 := primeCounting_step 480000 10701 40005 817 count_480000 (by rw [count_shift_is_prime_eq 480000 10701 (by omega)]; decide)

theorem pc_thm_491536 : Nat.primeCounting 491536 = 40885 := primeCounting_step 480000 11537 40005 880 count_480000 (by rw [count_shift_is_prime_eq 480000 11537 (by omega)]; decide)

theorem pc_thm_492102 : Nat.primeCounting 492102 = 40931 := primeCounting_step 480000 12103 40005 926 count_480000 (by rw [count_shift_is_prime_eq 480000 12103 (by omega)]; decide)

theorem pc_thm_492528 : Nat.primeCounting 492528 = 40955 := primeCounting_step 480000 12529 40005 950 count_480000 (by rw [count_shift_is_prime_eq 480000 12529 (by omega)]; decide)

theorem pc_thm_493506 : Nat.primeCounting 493506 = 41031 := primeCounting_step 480000 13507 40005 1026 count_480000 (by rw [count_shift_is_prime_eq 480000 13507 (by omega)]; decide)

theorem pc_thm_493521 : Nat.primeCounting 493521 = 41031 := primeCounting_step 480000 13522 40005 1026 count_480000 (by rw [count_shift_is_prime_eq 480000 13522 (by omega)]; decide)

theorem pc_thm_494515 : Nat.primeCounting 494515 = 41107 := primeCounting_step 480000 14516 40005 1102 count_480000 (by rw [count_shift_is_prime_eq 480000 14516 (by omega)]; decide)

theorem pc_thm_494912 : Nat.primeCounting 494912 = 41143 := primeCounting_step 480000 14913 40005 1138 count_480000 (by rw [count_shift_is_prime_eq 480000 14913 (by omega)]; decide)

theorem pc_thm_495510 : Nat.primeCounting 495510 = 41191 := primeCounting_step 480000 15511 40005 1186 count_480000 (by rw [count_shift_is_prime_eq 480000 15511 (by omega)]; decide)

theorem pc_thm_496320 : Nat.primeCounting 496320 = 41258 := primeCounting_step 480000 16321 40005 1253 count_480000 (by rw [count_shift_is_prime_eq 480000 16321 (by omega)]; decide)

theorem pc_thm_496506 : Nat.primeCounting 496506 = 41273 := primeCounting_step 480000 16507 40005 1268 count_480000 (by rw [count_shift_is_prime_eq 480000 16507 (by omega)]; decide)

theorem pc_thm_497503 : Nat.primeCounting 497503 = 41343 := primeCounting_step 480000 17504 40005 1338 count_480000 (by rw [count_shift_is_prime_eq 480000 17504 (by omega)]; decide)

theorem pc_thm_497730 : Nat.primeCounting 497730 = 41364 := primeCounting_step 480000 17731 40005 1359 count_480000 (by rw [count_shift_is_prime_eq 480000 17731 (by omega)]; decide)

theorem pc_thm_498501 : Nat.primeCounting 498501 = 41418 := primeCounting_step 480000 18502 40005 1413 count_480000 (by rw [count_shift_is_prime_eq 480000 18502 (by omega)]; decide)

theorem pc_thm_499142 : Nat.primeCounting 499142 = 41470 := primeCounting_step 480000 19143 40005 1465 count_480000 (by rw [count_shift_is_prime_eq 480000 19143 (by omega)]; decide)

theorem pc_thm_499500 : Nat.primeCounting 499500 = 41497 := primeCounting_step 480000 19501 40005 1492 count_480000 (by rw [count_shift_is_prime_eq 480000 19501 (by omega)]; decide)

theorem pc_thm_500500 : Nat.primeCounting 500500 = 41579 := primeCounting_step 500000 501 41538 41 count_500000 (by rw [count_shift_is_prime_eq 500000 501 (by omega)]; decide)

theorem pc_thm_500556 : Nat.primeCounting 500556 = 41583 := primeCounting_step 500000 557 41538 45 count_500000 (by rw [count_shift_is_prime_eq 500000 557 (by omega)]; decide)

theorem pc_thm_501501 : Nat.primeCounting 501501 = 41658 := primeCounting_step 500000 1502 41538 120 count_500000 (by rw [count_shift_is_prime_eq 500000 1502 (by omega)]; decide)

theorem pc_thm_501972 : Nat.primeCounting 501972 = 41690 := primeCounting_step 500000 1973 41538 152 count_500000 (by rw [count_shift_is_prime_eq 500000 1973 (by omega)]; decide)

theorem pc_thm_502503 : Nat.primeCounting 502503 = 41724 := primeCounting_step 500000 2504 41538 186 count_500000 (by rw [count_shift_is_prime_eq 500000 2504 (by omega)]; decide)

theorem pc_thm_503390 : Nat.primeCounting 503390 = 41787 := primeCounting_step 500000 3391 41538 249 count_500000 (by rw [count_shift_is_prime_eq 500000 3391 (by omega)]; decide)

theorem pc_thm_503506 : Nat.primeCounting 503506 = 41795 := primeCounting_step 500000 3507 41538 257 count_500000 (by rw [count_shift_is_prime_eq 500000 3507 (by omega)]; decide)

theorem pc_thm_504510 : Nat.primeCounting 504510 = 41871 := primeCounting_step 500000 4511 41538 333 count_500000 (by rw [count_shift_is_prime_eq 500000 4511 (by omega)]; decide)

theorem pc_thm_504810 : Nat.primeCounting 504810 = 41892 := primeCounting_step 500000 4811 41538 354 count_500000 (by rw [count_shift_is_prime_eq 500000 4811 (by omega)]; decide)

theorem pc_thm_505515 : Nat.primeCounting 505515 = 41957 := primeCounting_step 500000 5516 41538 419 count_500000 (by rw [count_shift_is_prime_eq 500000 5516 (by omega)]; decide)

theorem pc_thm_506232 : Nat.primeCounting 506232 = 42006 := primeCounting_step 500000 6233 41538 468 count_500000 (by rw [count_shift_is_prime_eq 500000 6233 (by omega)]; decide)

theorem pc_thm_506521 : Nat.primeCounting 506521 = 42029 := primeCounting_step 500000 6522 41538 491 count_500000 (by rw [count_shift_is_prime_eq 500000 6522 (by omega)]; decide)

theorem pc_thm_507528 : Nat.primeCounting 507528 = 42106 := primeCounting_step 500000 7529 41538 568 count_500000 (by rw [count_shift_is_prime_eq 500000 7529 (by omega)]; decide)

theorem pc_thm_507656 : Nat.primeCounting 507656 = 42114 := primeCounting_step 500000 7657 41538 576 count_500000 (by rw [count_shift_is_prime_eq 500000 7657 (by omega)]; decide)

theorem pc_thm_508536 : Nat.primeCounting 508536 = 42181 := primeCounting_step 500000 8537 41538 643 count_500000 (by rw [count_shift_is_prime_eq 500000 8537 (by omega)]; decide)

theorem pc_thm_509082 : Nat.primeCounting 509082 = 42221 := primeCounting_step 500000 9083 41538 683 count_500000 (by rw [count_shift_is_prime_eq 500000 9083 (by omega)]; decide)

theorem pc_thm_509545 : Nat.primeCounting 509545 = 42251 := primeCounting_step 500000 9546 41538 713 count_500000 (by rw [count_shift_is_prime_eq 500000 9546 (by omega)]; decide)

theorem pc_thm_510510 : Nat.primeCounting 510510 = 42331 := primeCounting_step 500000 10511 41538 793 count_500000 (by rw [count_shift_is_prime_eq 500000 10511 (by omega)]; decide)

theorem pc_thm_510555 : Nat.primeCounting 510555 = 42334 := primeCounting_step 500000 10556 41538 796 count_500000 (by rw [count_shift_is_prime_eq 500000 10556 (by omega)]; decide)

theorem pc_thm_511566 : Nat.primeCounting 511566 = 42413 := primeCounting_step 500000 11567 41538 875 count_500000 (by rw [count_shift_is_prime_eq 500000 11567 (by omega)]; decide)

theorem pc_thm_511940 : Nat.primeCounting 511940 = 42441 := primeCounting_step 500000 11941 41538 903 count_500000 (by rw [count_shift_is_prime_eq 500000 11941 (by omega)]; decide)

theorem pc_thm_512578 : Nat.primeCounting 512578 = 42478 := primeCounting_step 500000 12579 41538 940 count_500000 (by rw [count_shift_is_prime_eq 500000 12579 (by omega)]; decide)

theorem pc_thm_513372 : Nat.primeCounting 513372 = 42549 := primeCounting_step 500000 13373 41538 1011 count_500000 (by rw [count_shift_is_prime_eq 500000 13373 (by omega)]; decide)

theorem pc_thm_513591 : Nat.primeCounting 513591 = 42562 := primeCounting_step 500000 13592 41538 1024 count_500000 (by rw [count_shift_is_prime_eq 500000 13592 (by omega)]; decide)

theorem pc_thm_514605 : Nat.primeCounting 514605 = 42640 := primeCounting_step 500000 14606 41538 1102 count_500000 (by rw [count_shift_is_prime_eq 500000 14606 (by omega)]; decide)

theorem pc_thm_514806 : Nat.primeCounting 514806 = 42658 := primeCounting_step 500000 14807 41538 1120 count_500000 (by rw [count_shift_is_prime_eq 500000 14807 (by omega)]; decide)

theorem pc_thm_515620 : Nat.primeCounting 515620 = 42707 := primeCounting_step 500000 15621 41538 1169 count_500000 (by rw [count_shift_is_prime_eq 500000 15621 (by omega)]; decide)

theorem pc_thm_516242 : Nat.primeCounting 516242 = 42758 := primeCounting_step 500000 16243 41538 1220 count_500000 (by rw [count_shift_is_prime_eq 500000 16243 (by omega)]; decide)

theorem pc_thm_516636 : Nat.primeCounting 516636 = 42794 := primeCounting_step 500000 16637 41538 1256 count_500000 (by rw [count_shift_is_prime_eq 500000 16637 (by omega)]; decide)

theorem pc_thm_517653 : Nat.primeCounting 517653 = 42885 := primeCounting_step 500000 17654 41538 1347 count_500000 (by rw [count_shift_is_prime_eq 500000 17654 (by omega)]; decide)

theorem pc_thm_517680 : Nat.primeCounting 517680 = 42885 := primeCounting_step 500000 17681 41538 1347 count_500000 (by rw [count_shift_is_prime_eq 500000 17681 (by omega)]; decide)

theorem pc_thm_518671 : Nat.primeCounting 518671 = 42956 := primeCounting_step 500000 18672 41538 1418 count_500000 (by rw [count_shift_is_prime_eq 500000 18672 (by omega)]; decide)

theorem pc_thm_519120 : Nat.primeCounting 519120 = 42993 := primeCounting_step 500000 19121 41538 1455 count_500000 (by rw [count_shift_is_prime_eq 500000 19121 (by omega)]; decide)

theorem pc_thm_519690 : Nat.primeCounting 519690 = 43037 := primeCounting_step 500000 19691 41538 1499 count_500000 (by rw [count_shift_is_prime_eq 500000 19691 (by omega)]; decide)

theorem pc_thm_520562 : Nat.primeCounting 520562 = 43101 := primeCounting_step 520000 563 43061 40 count_520000 (by rw [count_shift_is_prime_eq 520000 563 (by omega)]; decide)

theorem pc_thm_520710 : Nat.primeCounting 520710 = 43114 := primeCounting_step 520000 711 43061 53 count_520000 (by rw [count_shift_is_prime_eq 520000 711 (by omega)]; decide)

theorem pc_thm_521731 : Nat.primeCounting 521731 = 43194 := primeCounting_step 520000 1732 43061 133 count_520000 (by rw [count_shift_is_prime_eq 520000 1732 (by omega)]; decide)

theorem pc_thm_522006 : Nat.primeCounting 522006 = 43217 := primeCounting_step 520000 2007 43061 156 count_520000 (by rw [count_shift_is_prime_eq 520000 2007 (by omega)]; decide)

theorem pc_thm_522753 : Nat.primeCounting 522753 = 43276 := primeCounting_step 520000 2754 43061 215 count_520000 (by rw [count_shift_is_prime_eq 520000 2754 (by omega)]; decide)

theorem pc_thm_523452 : Nat.primeCounting 523452 = 43321 := primeCounting_step 520000 3453 43061 260 count_520000 (by rw [count_shift_is_prime_eq 520000 3453 (by omega)]; decide)

theorem pc_thm_523776 : Nat.primeCounting 523776 = 43350 := primeCounting_step 520000 3777 43061 289 count_520000 (by rw [count_shift_is_prime_eq 520000 3777 (by omega)]; decide)

theorem pc_thm_524800 : Nat.primeCounting 524800 = 43419 := primeCounting_step 520000 4801 43061 358 count_520000 (by rw [count_shift_is_prime_eq 520000 4801 (by omega)]; decide)

theorem pc_thm_524900 : Nat.primeCounting 524900 = 43429 := primeCounting_step 520000 4901 43061 368 count_520000 (by rw [count_shift_is_prime_eq 520000 4901 (by omega)]; decide)

theorem pc_thm_525825 : Nat.primeCounting 525825 = 43507 := primeCounting_step 520000 5826 43061 446 count_520000 (by rw [count_shift_is_prime_eq 520000 5826 (by omega)]; decide)

theorem pc_thm_526350 : Nat.primeCounting 526350 = 43548 := primeCounting_step 520000 6351 43061 487 count_520000 (by rw [count_shift_is_prime_eq 520000 6351 (by omega)]; decide)

theorem pc_thm_526851 : Nat.primeCounting 526851 = 43592 := primeCounting_step 520000 6852 43061 531 count_520000 (by rw [count_shift_is_prime_eq 520000 6852 (by omega)]; decide)

theorem pc_thm_527802 : Nat.primeCounting 527802 = 43661 := primeCounting_step 520000 7803 43061 600 count_520000 (by rw [count_shift_is_prime_eq 520000 7803 (by omega)]; decide)

theorem pc_thm_527878 : Nat.primeCounting 527878 = 43667 := primeCounting_step 520000 7879 43061 606 count_520000 (by rw [count_shift_is_prime_eq 520000 7879 (by omega)]; decide)

theorem pc_thm_528906 : Nat.primeCounting 528906 = 43740 := primeCounting_step 520000 8907 43061 679 count_520000 (by rw [count_shift_is_prime_eq 520000 8907 (by omega)]; decide)

theorem pc_thm_529256 : Nat.primeCounting 529256 = 43769 := primeCounting_step 520000 9257 43061 708 count_520000 (by rw [count_shift_is_prime_eq 520000 9257 (by omega)]; decide)

theorem pc_thm_529935 : Nat.primeCounting 529935 = 43817 := primeCounting_step 520000 9936 43061 756 count_520000 (by rw [count_shift_is_prime_eq 520000 9936 (by omega)]; decide)

theorem pc_thm_530712 : Nat.primeCounting 530712 = 43882 := primeCounting_step 520000 10713 43061 821 count_520000 (by rw [count_shift_is_prime_eq 520000 10713 (by omega)]; decide)

theorem pc_thm_530965 : Nat.primeCounting 530965 = 43901 := primeCounting_step 520000 10966 43061 840 count_520000 (by rw [count_shift_is_prime_eq 520000 10966 (by omega)]; decide)

theorem pc_thm_531996 : Nat.primeCounting 531996 = 43972 := primeCounting_step 520000 11997 43061 911 count_520000 (by rw [count_shift_is_prime_eq 520000 11997 (by omega)]; decide)

theorem pc_thm_532170 : Nat.primeCounting 532170 = 43985 := primeCounting_step 520000 12171 43061 924 count_520000 (by rw [count_shift_is_prime_eq 520000 12171 (by omega)]; decide)

theorem pc_thm_533028 : Nat.primeCounting 533028 = 44055 := primeCounting_step 520000 13029 43061 994 count_520000 (by rw [count_shift_is_prime_eq 520000 13029 (by omega)]; decide)

theorem pc_thm_533630 : Nat.primeCounting 533630 = 44096 := primeCounting_step 520000 13631 43061 1035 count_520000 (by rw [count_shift_is_prime_eq 520000 13631 (by omega)]; decide)

theorem pc_thm_534061 : Nat.primeCounting 534061 = 44134 := primeCounting_step 520000 14062 43061 1073 count_520000 (by rw [count_shift_is_prime_eq 520000 14062 (by omega)]; decide)

theorem pc_thm_535092 : Nat.primeCounting 535092 = 44203 := primeCounting_step 520000 15093 43061 1142 count_520000 (by rw [count_shift_is_prime_eq 520000 15093 (by omega)]; decide)

theorem pc_thm_535095 : Nat.primeCounting 535095 = 44203 := primeCounting_step 520000 15096 43061 1142 count_520000 (by rw [count_shift_is_prime_eq 520000 15096 (by omega)]; decide)

theorem pc_thm_536130 : Nat.primeCounting 536130 = 44279 := primeCounting_step 520000 16131 43061 1218 count_520000 (by rw [count_shift_is_prime_eq 520000 16131 (by omega)]; decide)

theorem pc_thm_536556 : Nat.primeCounting 536556 = 44317 := primeCounting_step 520000 16557 43061 1256 count_520000 (by rw [count_shift_is_prime_eq 520000 16557 (by omega)]; decide)

theorem pc_thm_537166 : Nat.primeCounting 537166 = 44371 := primeCounting_step 520000 17167 43061 1310 count_520000 (by rw [count_shift_is_prime_eq 520000 17167 (by omega)]; decide)

theorem pc_thm_538022 : Nat.primeCounting 538022 = 44425 := primeCounting_step 520000 18023 43061 1364 count_520000 (by rw [count_shift_is_prime_eq 520000 18023 (by omega)]; decide)

theorem pc_thm_538203 : Nat.primeCounting 538203 = 44441 := primeCounting_step 520000 18204 43061 1380 count_520000 (by rw [count_shift_is_prime_eq 520000 18204 (by omega)]; decide)

theorem pc_thm_539241 : Nat.primeCounting 539241 = 44521 := primeCounting_step 520000 19242 43061 1460 count_520000 (by rw [count_shift_is_prime_eq 520000 19242 (by omega)]; decide)

theorem pc_thm_539490 : Nat.primeCounting 539490 = 44538 := primeCounting_step 520000 19491 43061 1477 count_520000 (by rw [count_shift_is_prime_eq 520000 19491 (by omega)]; decide)

theorem pc_thm_540280 : Nat.primeCounting 540280 = 44592 := primeCounting_step 540000 281 44572 20 count_540000 (by rw [count_shift_is_prime_eq 540000 281 (by omega)]; decide)

theorem pc_thm_540960 : Nat.primeCounting 540960 = 44643 := primeCounting_step 540000 961 44572 71 count_540000 (by rw [count_shift_is_prime_eq 540000 961 (by omega)]; decide)

theorem pc_thm_541320 : Nat.primeCounting 541320 = 44668 := primeCounting_step 540000 1321 44572 96 count_540000 (by rw [count_shift_is_prime_eq 540000 1321 (by omega)]; decide)

theorem pc_thm_542361 : Nat.primeCounting 542361 = 44753 := primeCounting_step 540000 2362 44572 181 count_540000 (by rw [count_shift_is_prime_eq 540000 2362 (by omega)]; decide)

theorem pc_thm_542432 : Nat.primeCounting 542432 = 44755 := primeCounting_step 540000 2433 44572 183 count_540000 (by rw [count_shift_is_prime_eq 540000 2433 (by omega)]; decide)

theorem pc_thm_543403 : Nat.primeCounting 543403 = 44835 := primeCounting_step 540000 3404 44572 263 count_540000 (by rw [count_shift_is_prime_eq 540000 3404 (by omega)]; decide)

theorem pc_thm_543906 : Nat.primeCounting 543906 = 44876 := primeCounting_step 540000 3907 44572 304 count_540000 (by rw [count_shift_is_prime_eq 540000 3907 (by omega)]; decide)

theorem pc_thm_544446 : Nat.primeCounting 544446 = 44908 := primeCounting_step 540000 4447 44572 336 count_540000 (by rw [count_shift_is_prime_eq 540000 4447 (by omega)]; decide)

theorem pc_thm_545382 : Nat.primeCounting 545382 = 44972 := primeCounting_step 540000 5383 44572 400 count_540000 (by rw [count_shift_is_prime_eq 540000 5383 (by omega)]; decide)

theorem pc_thm_545490 : Nat.primeCounting 545490 = 44980 := primeCounting_step 540000 5491 44572 408 count_540000 (by rw [count_shift_is_prime_eq 540000 5491 (by omega)]; decide)

theorem pc_thm_546535 : Nat.primeCounting 546535 = 45058 := primeCounting_step 540000 6536 44572 486 count_540000 (by rw [count_shift_is_prime_eq 540000 6536 (by omega)]; decide)

theorem pc_thm_546860 : Nat.primeCounting 546860 = 45080 := primeCounting_step 540000 6861 44572 508 count_540000 (by rw [count_shift_is_prime_eq 540000 6861 (by omega)]; decide)

theorem pc_thm_547581 : Nat.primeCounting 547581 = 45136 := primeCounting_step 540000 7582 44572 564 count_540000 (by rw [count_shift_is_prime_eq 540000 7582 (by omega)]; decide)

theorem pc_thm_548340 : Nat.primeCounting 548340 = 45189 := primeCounting_step 540000 8341 44572 617 count_540000 (by rw [count_shift_is_prime_eq 540000 8341 (by omega)]; decide)

theorem pc_thm_548628 : Nat.primeCounting 548628 = 45214 := primeCounting_step 540000 8629 44572 642 count_540000 (by rw [count_shift_is_prime_eq 540000 8629 (by omega)]; decide)

theorem pc_thm_549676 : Nat.primeCounting 549676 = 45298 := primeCounting_step 540000 9677 44572 726 count_540000 (by rw [count_shift_is_prime_eq 540000 9677 (by omega)]; decide)

theorem pc_thm_549822 : Nat.primeCounting 549822 = 45311 := primeCounting_step 540000 9823 44572 739 count_540000 (by rw [count_shift_is_prime_eq 540000 9823 (by omega)]; decide)

theorem pc_thm_550725 : Nat.primeCounting 550725 = 45379 := primeCounting_step 540000 10726 44572 807 count_540000 (by rw [count_shift_is_prime_eq 540000 10726 (by omega)]; decide)

theorem pc_thm_551306 : Nat.primeCounting 551306 = 45423 := primeCounting_step 540000 11307 44572 851 count_540000 (by rw [count_shift_is_prime_eq 540000 11307 (by omega)]; decide)

theorem pc_thm_551775 : Nat.primeCounting 551775 = 45461 := primeCounting_step 540000 11776 44572 889 count_540000 (by rw [count_shift_is_prime_eq 540000 11776 (by omega)]; decide)

theorem pc_thm_552792 : Nat.primeCounting 552792 = 45532 := primeCounting_step 540000 12793 44572 960 count_540000 (by rw [count_shift_is_prime_eq 540000 12793 (by omega)]; decide)

theorem pc_thm_552826 : Nat.primeCounting 552826 = 45535 := primeCounting_step 540000 12827 44572 963 count_540000 (by rw [count_shift_is_prime_eq 540000 12827 (by omega)]; decide)

theorem pc_thm_553878 : Nat.primeCounting 553878 = 45618 := primeCounting_step 540000 13879 44572 1046 count_540000 (by rw [count_shift_is_prime_eq 540000 13879 (by omega)]; decide)

theorem pc_thm_554280 : Nat.primeCounting 554280 = 45648 := primeCounting_step 540000 14281 44572 1076 count_540000 (by rw [count_shift_is_prime_eq 540000 14281 (by omega)]; decide)

theorem pc_thm_554931 : Nat.primeCounting 554931 = 45700 := primeCounting_step 540000 14932 44572 1128 count_540000 (by rw [count_shift_is_prime_eq 540000 14932 (by omega)]; decide)

theorem pc_thm_555770 : Nat.primeCounting 555770 = 45755 := primeCounting_step 540000 15771 44572 1183 count_540000 (by rw [count_shift_is_prime_eq 540000 15771 (by omega)]; decide)

theorem pc_thm_555985 : Nat.primeCounting 555985 = 45765 := primeCounting_step 540000 15986 44572 1193 count_540000 (by rw [count_shift_is_prime_eq 540000 15986 (by omega)]; decide)

theorem pc_thm_557040 : Nat.primeCounting 557040 = 45857 := primeCounting_step 540000 17041 44572 1285 count_540000 (by rw [count_shift_is_prime_eq 540000 17041 (by omega)]; decide)

theorem pc_thm_557262 : Nat.primeCounting 557262 = 45868 := primeCounting_step 540000 17263 44572 1296 count_540000 (by rw [count_shift_is_prime_eq 540000 17263 (by omega)]; decide)

theorem pc_thm_558096 : Nat.primeCounting 558096 = 45928 := primeCounting_step 540000 18097 44572 1356 count_540000 (by rw [count_shift_is_prime_eq 540000 18097 (by omega)]; decide)

theorem pc_thm_558756 : Nat.primeCounting 558756 = 45976 := primeCounting_step 540000 18757 44572 1404 count_540000 (by rw [count_shift_is_prime_eq 540000 18757 (by omega)]; decide)

theorem pc_thm_559153 : Nat.primeCounting 559153 = 46004 := primeCounting_step 540000 19154 44572 1432 count_540000 (by rw [count_shift_is_prime_eq 540000 19154 (by omega)]; decide)

theorem pc_thm_560211 : Nat.primeCounting 560211 = 46093 := primeCounting_step 560000 212 46072 21 count_560000 (by rw [count_shift_is_prime_eq 560000 212 (by omega)]; decide)

theorem pc_thm_560252 : Nat.primeCounting 560252 = 46101 := primeCounting_step 560000 253 46072 29 count_560000 (by rw [count_shift_is_prime_eq 560000 253 (by omega)]; decide)

theorem pc_thm_561270 : Nat.primeCounting 561270 = 46177 := primeCounting_step 560000 1271 46072 105 count_560000 (by rw [count_shift_is_prime_eq 560000 1271 (by omega)]; decide)

theorem pc_thm_561750 : Nat.primeCounting 561750 = 46202 := primeCounting_step 560000 1751 46072 130 count_560000 (by rw [count_shift_is_prime_eq 560000 1751 (by omega)]; decide)

theorem pc_thm_562330 : Nat.primeCounting 562330 = 46241 := primeCounting_step 560000 2331 46072 169 count_560000 (by rw [count_shift_is_prime_eq 560000 2331 (by omega)]; decide)

theorem pc_thm_563250 : Nat.primeCounting 563250 = 46322 := primeCounting_step 560000 3251 46072 250 count_560000 (by rw [count_shift_is_prime_eq 560000 3251 (by omega)]; decide)

theorem pc_thm_563391 : Nat.primeCounting 563391 = 46329 := primeCounting_step 560000 3392 46072 257 count_560000 (by rw [count_shift_is_prime_eq 560000 3392 (by omega)]; decide)

theorem pc_thm_564453 : Nat.primeCounting 564453 = 46409 := primeCounting_step 560000 4454 46072 337 count_560000 (by rw [count_shift_is_prime_eq 560000 4454 (by omega)]; decide)

theorem pc_thm_564752 : Nat.primeCounting 564752 = 46428 := primeCounting_step 560000 4753 46072 356 count_560000 (by rw [count_shift_is_prime_eq 560000 4753 (by omega)]; decide)

theorem pc_thm_565516 : Nat.primeCounting 565516 = 46489 := primeCounting_step 560000 5517 46072 417 count_560000 (by rw [count_shift_is_prime_eq 560000 5517 (by omega)]; decide)

theorem pc_thm_566256 : Nat.primeCounting 566256 = 46543 := primeCounting_step 560000 6257 46072 471 count_560000 (by rw [count_shift_is_prime_eq 560000 6257 (by omega)]; decide)

theorem pc_thm_566580 : Nat.primeCounting 566580 = 46566 := primeCounting_step 560000 6581 46072 494 count_560000 (by rw [count_shift_is_prime_eq 560000 6581 (by omega)]; decide)

theorem pc_thm_567645 : Nat.primeCounting 567645 = 46636 := primeCounting_step 560000 7646 46072 564 count_560000 (by rw [count_shift_is_prime_eq 560000 7646 (by omega)]; decide)

theorem pc_thm_567762 : Nat.primeCounting 567762 = 46647 := primeCounting_step 560000 7763 46072 575 count_560000 (by rw [count_shift_is_prime_eq 560000 7763 (by omega)]; decide)

theorem pc_thm_568711 : Nat.primeCounting 568711 = 46720 := primeCounting_step 560000 8712 46072 648 count_560000 (by rw [count_shift_is_prime_eq 560000 8712 (by omega)]; decide)

theorem pc_thm_569270 : Nat.primeCounting 569270 = 46767 := primeCounting_step 560000 9271 46072 695 count_560000 (by rw [count_shift_is_prime_eq 560000 9271 (by omega)]; decide)

theorem pc_thm_569778 : Nat.primeCounting 569778 = 46801 := primeCounting_step 560000 9779 46072 729 count_560000 (by rw [count_shift_is_prime_eq 560000 9779 (by omega)]; decide)

theorem pc_thm_570780 : Nat.primeCounting 570780 = 46886 := primeCounting_step 560000 10781 46072 814 count_560000 (by rw [count_shift_is_prime_eq 560000 10781 (by omega)]; decide)

theorem pc_thm_570846 : Nat.primeCounting 570846 = 46891 := primeCounting_step 560000 10847 46072 819 count_560000 (by rw [count_shift_is_prime_eq 560000 10847 (by omega)]; decide)

theorem pc_thm_571915 : Nat.primeCounting 571915 = 46972 := primeCounting_step 560000 11916 46072 900 count_560000 (by rw [count_shift_is_prime_eq 560000 11916 (by omega)]; decide)

theorem pc_thm_572292 : Nat.primeCounting 572292 = 46998 := primeCounting_step 560000 12293 46072 926 count_560000 (by rw [count_shift_is_prime_eq 560000 12293 (by omega)]; decide)

theorem pc_thm_572985 : Nat.primeCounting 572985 = 47060 := primeCounting_step 560000 12986 46072 988 count_560000 (by rw [count_shift_is_prime_eq 560000 12986 (by omega)]; decide)

theorem pc_thm_573806 : Nat.primeCounting 573806 = 47116 := primeCounting_step 560000 13807 46072 1044 count_560000 (by rw [count_shift_is_prime_eq 560000 13807 (by omega)]; decide)

theorem pc_thm_574056 : Nat.primeCounting 574056 = 47137 := primeCounting_step 560000 14057 46072 1065 count_560000 (by rw [count_shift_is_prime_eq 560000 14057 (by omega)]; decide)

theorem pc_thm_575128 : Nat.primeCounting 575128 = 47212 := primeCounting_step 560000 15129 46072 1140 count_560000 (by rw [count_shift_is_prime_eq 560000 15129 (by omega)]; decide)

theorem pc_thm_575322 : Nat.primeCounting 575322 = 47229 := primeCounting_step 560000 15323 46072 1157 count_560000 (by rw [count_shift_is_prime_eq 560000 15323 (by omega)]; decide)

theorem pc_thm_576201 : Nat.primeCounting 576201 = 47296 := primeCounting_step 560000 16202 46072 1224 count_560000 (by rw [count_shift_is_prime_eq 560000 16202 (by omega)]; decide)

theorem pc_thm_576840 : Nat.primeCounting 576840 = 47350 := primeCounting_step 560000 16841 46072 1278 count_560000 (by rw [count_shift_is_prime_eq 560000 16841 (by omega)]; decide)

theorem pc_thm_577275 : Nat.primeCounting 577275 = 47379 := primeCounting_step 560000 17276 46072 1307 count_560000 (by rw [count_shift_is_prime_eq 560000 17276 (by omega)]; decide)

theorem pc_thm_578350 : Nat.primeCounting 578350 = 47458 := primeCounting_step 560000 18351 46072 1386 count_560000 (by rw [count_shift_is_prime_eq 560000 18351 (by omega)]; decide)

theorem pc_thm_578360 : Nat.primeCounting 578360 = 47459 := primeCounting_step 560000 18361 46072 1387 count_560000 (by rw [count_shift_is_prime_eq 560000 18361 (by omega)]; decide)

theorem pc_thm_579426 : Nat.primeCounting 579426 = 47538 := primeCounting_step 560000 19427 46072 1466 count_560000 (by rw [count_shift_is_prime_eq 560000 19427 (by omega)]; decide)

theorem pc_thm_579882 : Nat.primeCounting 579882 = 47579 := primeCounting_step 560000 19883 46072 1507 count_560000 (by rw [count_shift_is_prime_eq 560000 19883 (by omega)]; decide)

theorem pc_thm_580503 : Nat.primeCounting 580503 = 47620 := primeCounting_step 580000 504 47588 32 count_580000 (by rw [count_shift_is_prime_eq 580000 504 (by omega)]; decide)

theorem pc_thm_581406 : Nat.primeCounting 581406 = 47694 := primeCounting_step 580000 1407 47588 106 count_580000 (by rw [count_shift_is_prime_eq 580000 1407 (by omega)]; decide)

theorem pc_thm_581581 : Nat.primeCounting 581581 = 47708 := primeCounting_step 580000 1582 47588 120 count_580000 (by rw [count_shift_is_prime_eq 580000 1582 (by omega)]; decide)

theorem pc_thm_582660 : Nat.primeCounting 582660 = 47785 := primeCounting_step 580000 2661 47588 197 count_580000 (by rw [count_shift_is_prime_eq 580000 2661 (by omega)]; decide)

theorem pc_thm_582932 : Nat.primeCounting 582932 = 47807 := primeCounting_step 580000 2933 47588 219 count_580000 (by rw [count_shift_is_prime_eq 580000 2933 (by omega)]; decide)

theorem pc_thm_583740 : Nat.primeCounting 583740 = 47872 := primeCounting_step 580000 3741 47588 284 count_580000 (by rw [count_shift_is_prime_eq 580000 3741 (by omega)]; decide)

theorem pc_thm_584460 : Nat.primeCounting 584460 = 47920 := primeCounting_step 580000 4461 47588 332 count_580000 (by rw [count_shift_is_prime_eq 580000 4461 (by omega)]; decide)

theorem pc_thm_584821 : Nat.primeCounting 584821 = 47948 := primeCounting_step 580000 4822 47588 360 count_580000 (by rw [count_shift_is_prime_eq 580000 4822 (by omega)]; decide)

theorem pc_thm_585903 : Nat.primeCounting 585903 = 48037 := primeCounting_step 580000 5904 47588 449 count_580000 (by rw [count_shift_is_prime_eq 580000 5904 (by omega)]; decide)

theorem pc_thm_585990 : Nat.primeCounting 585990 = 48043 := primeCounting_step 580000 5991 47588 455 count_580000 (by rw [count_shift_is_prime_eq 580000 5991 (by omega)]; decide)

theorem pc_thm_586986 : Nat.primeCounting 586986 = 48123 := primeCounting_step 580000 6987 47588 535 count_580000 (by rw [count_shift_is_prime_eq 580000 6987 (by omega)]; decide)

theorem pc_thm_587522 : Nat.primeCounting 587522 = 48166 := primeCounting_step 580000 7523 47588 578 count_580000 (by rw [count_shift_is_prime_eq 580000 7523 (by omega)]; decide)

theorem pc_thm_588070 : Nat.primeCounting 588070 = 48215 := primeCounting_step 580000 8071 47588 627 count_580000 (by rw [count_shift_is_prime_eq 580000 8071 (by omega)]; decide)

theorem pc_thm_589056 : Nat.primeCounting 589056 = 48286 := primeCounting_step 580000 9057 47588 698 count_580000 (by rw [count_shift_is_prime_eq 580000 9057 (by omega)]; decide)

theorem pc_thm_589155 : Nat.primeCounting 589155 = 48291 := primeCounting_step 580000 9156 47588 703 count_580000 (by rw [count_shift_is_prime_eq 580000 9156 (by omega)]; decide)

theorem pc_thm_590241 : Nat.primeCounting 590241 = 48368 := primeCounting_step 580000 10242 47588 780 count_580000 (by rw [count_shift_is_prime_eq 580000 10242 (by omega)]; decide)

theorem pc_thm_590592 : Nat.primeCounting 590592 = 48392 := primeCounting_step 580000 10593 47588 804 count_580000 (by rw [count_shift_is_prime_eq 580000 10593 (by omega)]; decide)

theorem pc_thm_591328 : Nat.primeCounting 591328 = 48445 := primeCounting_step 580000 11329 47588 857 count_580000 (by rw [count_shift_is_prime_eq 580000 11329 (by omega)]; decide)

theorem pc_thm_592130 : Nat.primeCounting 592130 = 48499 := primeCounting_step 580000 12131 47588 911 count_580000 (by rw [count_shift_is_prime_eq 580000 12131 (by omega)]; decide)

theorem pc_thm_592416 : Nat.primeCounting 592416 = 48522 := primeCounting_step 580000 12417 47588 934 count_580000 (by rw [count_shift_is_prime_eq 580000 12417 (by omega)]; decide)

theorem pc_thm_593505 : Nat.primeCounting 593505 = 48613 := primeCounting_step 580000 13506 47588 1025 count_580000 (by rw [count_shift_is_prime_eq 580000 13506 (by omega)]; decide)

theorem pc_thm_593670 : Nat.primeCounting 593670 = 48628 := primeCounting_step 580000 13671 47588 1040 count_580000 (by rw [count_shift_is_prime_eq 580000 13671 (by omega)]; decide)

theorem pc_thm_594595 : Nat.primeCounting 594595 = 48694 := primeCounting_step 580000 14596 47588 1106 count_580000 (by rw [count_shift_is_prime_eq 580000 14596 (by omega)]; decide)

theorem pc_thm_595212 : Nat.primeCounting 595212 = 48746 := primeCounting_step 580000 15213 47588 1158 count_580000 (by rw [count_shift_is_prime_eq 580000 15213 (by omega)]; decide)

theorem pc_thm_595686 : Nat.primeCounting 595686 = 48778 := primeCounting_step 580000 15687 47588 1190 count_580000 (by rw [count_shift_is_prime_eq 580000 15687 (by omega)]; decide)

theorem pc_thm_596756 : Nat.primeCounting 596756 = 48858 := primeCounting_step 580000 16757 47588 1270 count_580000 (by rw [count_shift_is_prime_eq 580000 16757 (by omega)]; decide)

theorem pc_thm_596778 : Nat.primeCounting 596778 = 48859 := primeCounting_step 580000 16779 47588 1271 count_580000 (by rw [count_shift_is_prime_eq 580000 16779 (by omega)]; decide)

theorem pc_thm_597871 : Nat.primeCounting 597871 = 48946 := primeCounting_step 580000 17872 47588 1358 count_580000 (by rw [count_shift_is_prime_eq 580000 17872 (by omega)]; decide)

theorem pc_thm_598302 : Nat.primeCounting 598302 = 48972 := primeCounting_step 580000 18303 47588 1384 count_580000 (by rw [count_shift_is_prime_eq 580000 18303 (by omega)]; decide)

theorem pc_thm_598965 : Nat.primeCounting 598965 = 49020 := primeCounting_step 580000 18966 47588 1432 count_580000 (by rw [count_shift_is_prime_eq 580000 18966 (by omega)]; decide)

theorem pc_thm_599850 : Nat.primeCounting 599850 = 49086 := primeCounting_step 580000 19851 47588 1498 count_580000 (by rw [count_shift_is_prime_eq 580000 19851 (by omega)]; decide)

theorem pc_thm_600060 : Nat.primeCounting 600060 = 49101 := primeCounting_step 600000 61 49098 3 count_600000 (by rw [count_shift_is_prime_eq 600000 61 (by omega)]; decide)

theorem pc_thm_601156 : Nat.primeCounting 601156 = 49185 := primeCounting_step 600000 1157 49098 87 count_600000 (by rw [count_shift_is_prime_eq 600000 1157 (by omega)]; decide)

theorem pc_thm_601400 : Nat.primeCounting 601400 = 49207 := primeCounting_step 600000 1401 49098 109 count_600000 (by rw [count_shift_is_prime_eq 600000 1401 (by omega)]; decide)

theorem pc_thm_602253 : Nat.primeCounting 602253 = 49268 := primeCounting_step 600000 2254 49098 170 count_600000 (by rw [count_shift_is_prime_eq 600000 2254 (by omega)]; decide)

theorem pc_thm_602952 : Nat.primeCounting 602952 = 49326 := primeCounting_step 600000 2953 49098 228 count_600000 (by rw [count_shift_is_prime_eq 600000 2953 (by omega)]; decide)

theorem pc_thm_603351 : Nat.primeCounting 603351 = 49352 := primeCounting_step 600000 3352 49098 254 count_600000 (by rw [count_shift_is_prime_eq 600000 3352 (by omega)]; decide)

theorem pc_thm_604450 : Nat.primeCounting 604450 = 49437 := primeCounting_step 600000 4451 49098 339 count_600000 (by rw [count_shift_is_prime_eq 600000 4451 (by omega)]; decide)

theorem pc_thm_604506 : Nat.primeCounting 604506 = 49439 := primeCounting_step 600000 4507 49098 341 count_600000 (by rw [count_shift_is_prime_eq 600000 4507 (by omega)]; decide)

theorem pc_thm_605550 : Nat.primeCounting 605550 = 49520 := primeCounting_step 600000 5551 49098 422 count_600000 (by rw [count_shift_is_prime_eq 600000 5551 (by omega)]; decide)

theorem pc_thm_606062 : Nat.primeCounting 606062 = 49560 := primeCounting_step 600000 6063 49098 462 count_600000 (by rw [count_shift_is_prime_eq 600000 6063 (by omega)]; decide)

theorem pc_thm_606651 : Nat.primeCounting 606651 = 49599 := primeCounting_step 600000 6652 49098 501 count_600000 (by rw [count_shift_is_prime_eq 600000 6652 (by omega)]; decide)

theorem pc_thm_607620 : Nat.primeCounting 607620 = 49674 := primeCounting_step 600000 7621 49098 576 count_600000 (by rw [count_shift_is_prime_eq 600000 7621 (by omega)]; decide)

theorem pc_thm_607753 : Nat.primeCounting 607753 = 49684 := primeCounting_step 600000 7754 49098 586 count_600000 (by rw [count_shift_is_prime_eq 600000 7754 (by omega)]; decide)

theorem pc_thm_608856 : Nat.primeCounting 608856 = 49767 := primeCounting_step 600000 8857 49098 669 count_600000 (by rw [count_shift_is_prime_eq 600000 8857 (by omega)]; decide)

theorem pc_thm_609180 : Nat.primeCounting 609180 = 49794 := primeCounting_step 600000 9181 49098 696 count_600000 (by rw [count_shift_is_prime_eq 600000 9181 (by omega)]; decide)

theorem pc_thm_609960 : Nat.primeCounting 609960 = 49857 := primeCounting_step 600000 9961 49098 759 count_600000 (by rw [count_shift_is_prime_eq 600000 9961 (by omega)]; decide)

theorem pc_thm_610742 : Nat.primeCounting 610742 = 49911 := primeCounting_step 600000 10743 49098 813 count_600000 (by rw [count_shift_is_prime_eq 600000 10743 (by omega)]; decide)

theorem pc_thm_611065 : Nat.primeCounting 611065 = 49938 := primeCounting_step 600000 11066 49098 840 count_600000 (by rw [count_shift_is_prime_eq 600000 11066 (by omega)]; decide)

theorem pc_thm_612171 : Nat.primeCounting 612171 = 50022 := primeCounting_step 600000 12172 49098 924 count_600000 (by rw [count_shift_is_prime_eq 600000 12172 (by omega)]; decide)

theorem pc_thm_612306 : Nat.primeCounting 612306 = 50031 := primeCounting_step 600000 12307 49098 933 count_600000 (by rw [count_shift_is_prime_eq 600000 12307 (by omega)]; decide)

theorem pc_thm_613278 : Nat.primeCounting 613278 = 50104 := primeCounting_step 600000 13279 49098 1006 count_600000 (by rw [count_shift_is_prime_eq 600000 13279 (by omega)]; decide)

theorem pc_thm_613872 : Nat.primeCounting 613872 = 50151 := primeCounting_step 600000 13873 49098 1053 count_600000 (by rw [count_shift_is_prime_eq 600000 13873 (by omega)]; decide)

theorem pc_thm_614386 : Nat.primeCounting 614386 = 50184 := primeCounting_step 600000 14387 49098 1086 count_600000 (by rw [count_shift_is_prime_eq 600000 14387 (by omega)]; decide)

theorem pc_thm_615440 : Nat.primeCounting 615440 = 50263 := primeCounting_step 600000 15441 49098 1165 count_600000 (by rw [count_shift_is_prime_eq 600000 15441 (by omega)]; decide)

theorem pc_thm_615495 : Nat.primeCounting 615495 = 50268 := primeCounting_step 600000 15496 49098 1170 count_600000 (by rw [count_shift_is_prime_eq 600000 15496 (by omega)]; decide)

theorem pc_thm_616605 : Nat.primeCounting 616605 = 50360 := primeCounting_step 600000 16606 49098 1262 count_600000 (by rw [count_shift_is_prime_eq 600000 16606 (by omega)]; decide)

theorem pc_thm_617010 : Nat.primeCounting 617010 = 50391 := primeCounting_step 600000 17011 49098 1293 count_600000 (by rw [count_shift_is_prime_eq 600000 17011 (by omega)]; decide)

theorem pc_thm_617716 : Nat.primeCounting 617716 = 50449 := primeCounting_step 600000 17717 49098 1351 count_600000 (by rw [count_shift_is_prime_eq 600000 17717 (by omega)]; decide)

theorem pc_thm_618582 : Nat.primeCounting 618582 = 50512 := primeCounting_step 600000 18583 49098 1414 count_600000 (by rw [count_shift_is_prime_eq 600000 18583 (by omega)]; decide)

theorem pc_thm_618828 : Nat.primeCounting 618828 = 50525 := primeCounting_step 600000 18829 49098 1427 count_600000 (by rw [count_shift_is_prime_eq 600000 18829 (by omega)]; decide)

theorem pc_thm_619941 : Nat.primeCounting 619941 = 50607 := primeCounting_step 600000 19942 49098 1509 count_600000 (by rw [count_shift_is_prime_eq 600000 19942 (by omega)]; decide)

theorem pc_thm_620156 : Nat.primeCounting 620156 = 50619 := primeCounting_step 620000 157 50612 7 count_620000 (by rw [count_shift_is_prime_eq 620000 157 (by omega)]; decide)

theorem pc_thm_621055 : Nat.primeCounting 621055 = 50695 := primeCounting_step 620000 1056 50612 83 count_620000 (by rw [count_shift_is_prime_eq 620000 1056 (by omega)]; decide)

theorem pc_thm_621732 : Nat.primeCounting 621732 = 50741 := primeCounting_step 620000 1733 50612 129 count_620000 (by rw [count_shift_is_prime_eq 620000 1733 (by omega)]; decide)

theorem pc_thm_622170 : Nat.primeCounting 622170 = 50775 := primeCounting_step 620000 2171 50612 163 count_620000 (by rw [count_shift_is_prime_eq 620000 2171 (by omega)]; decide)

theorem pc_thm_623286 : Nat.primeCounting 623286 = 50850 := primeCounting_step 620000 3287 50612 238 count_620000 (by rw [count_shift_is_prime_eq 620000 3287 (by omega)]; decide)

theorem pc_thm_623310 : Nat.primeCounting 623310 = 50853 := primeCounting_step 620000 3311 50612 241 count_620000 (by rw [count_shift_is_prime_eq 620000 3311 (by omega)]; decide)

theorem pc_thm_624403 : Nat.primeCounting 624403 = 50940 := primeCounting_step 620000 4404 50612 328 count_620000 (by rw [count_shift_is_prime_eq 620000 4404 (by omega)]; decide)

theorem pc_thm_624890 : Nat.primeCounting 624890 = 50980 := primeCounting_step 620000 4891 50612 368 count_620000 (by rw [count_shift_is_prime_eq 620000 4891 (by omega)]; decide)

theorem pc_thm_625521 : Nat.primeCounting 625521 = 51022 := primeCounting_step 620000 5522 50612 410 count_620000 (by rw [count_shift_is_prime_eq 620000 5522 (by omega)]; decide)

theorem pc_thm_626472 : Nat.primeCounting 626472 = 51083 := primeCounting_step 620000 6473 50612 471 count_620000 (by rw [count_shift_is_prime_eq 620000 6473 (by omega)]; decide)

theorem pc_thm_626640 : Nat.primeCounting 626640 = 51098 := primeCounting_step 620000 6641 50612 486 count_620000 (by rw [count_shift_is_prime_eq 620000 6641 (by omega)]; decide)

theorem pc_thm_627760 : Nat.primeCounting 627760 = 51179 := primeCounting_step 620000 7761 50612 567 count_620000 (by rw [count_shift_is_prime_eq 620000 7761 (by omega)]; decide)

theorem pc_thm_628056 : Nat.primeCounting 628056 = 51200 := primeCounting_step 620000 8057 50612 588 count_620000 (by rw [count_shift_is_prime_eq 620000 8057 (by omega)]; decide)


lemma k_mono (k1 k2 : ℕ) (h : k1 ≤ k2) : k1 * (k1 + 1) ≤ k2 * (k2 + 1) := by
  nlinarith

lemma m_mono (m1 m2 : ℕ) (h : m1 ≤ m2) : m1 * (m1 + 1) / 2 ≤ m2 * (m2 + 1) / 2 := by
  have : m1 * (m1 + 1) ≤ m2 * (m2 + 1) := by nlinarith
  exact Nat.div_le_div_right this

lemma primeCounting_mono_comp {a b : ℕ} (h : a ≤ b) : Nat.primeCounting a ≤ Nat.primeCounting b :=
  Nat.monotone_primeCounting h

theorem primeCounting_626640 : Nat.primeCounting 626640 = 51098 := pc_thm_626640

theorem sol_in_set : (16, 1119) ∈ filter (fun p : ℕ × ℕ => Nat.primeCounting (p.fst * (p.fst + 1)) + Nat.primeCounting (p.snd * (p.snd + 1) / 2) = 51156) (Finset.product (Icc 1 51157) (Icc 1 51157)) := by
  simp only [mem_filter, mem_product, mem_Icc]
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
  have h1 : 16 * 17 = 272 := by rfl
  have h2 : 1119 * 1120 / 2 = 626640 := by rfl
  rw [h1, h2, primeCounting_272, primeCounting_626640]

theorem A263001_51156_pos : A263001 51156 > 0 := by
  rw [A263001]
  have h : (16, 1119) ∈ filter (fun p : ℕ × ℕ => Nat.primeCounting (p.fst * (p.fst + 1)) + Nat.primeCounting (p.snd * (p.snd + 1) / 2) = 51156) (Finset.product (Icc 1 51157) (Icc 1 51157)) := sol_in_set
  have hpos : (filter (fun p : ℕ × ℕ => Nat.primeCounting (p.fst * (p.fst + 1)) + Nat.primeCounting (p.snd * (p.snd + 1) / 2) = 51156) (Finset.product (Icc 1 51157) (Icc 1 51157))).Nonempty := ⟨(16, 1119), h⟩
  exact card_pos.2 hpos
theorem staircase_part_0 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_1 : k ≥ 28) (h_m_1 : m ≤ 1117) : k ≥ 107 ∧ m ≤ 1102 := by
  -- Step 1: k >= 28, m <= 1117 => k >= 36
  have h_m_mono_1 : m*(m+1)/2 ≤ 624403 := m_mono m 1117 h_m_1
  have h_pc_M_1 : Nat.primeCounting 624403 = 50940 := pc_thm_624403
  have h_pc_K_prev_1 : Nat.primeCounting 1260 = 205 := pc_thm_1260
  have h_k_2 : k ≥ 36 := staircase_step_K_direct k m 51156 624403 1260 50940 205 36 heq h_m_mono_1 h_pc_M_1 h_pc_K_prev_1 rfl (by decide)
  have h_pc_K_next_1 : Nat.primeCounting 1332 = 217 := pc_thm_1332
  have h_pc_M_next_val_1 : Nat.primeCounting 624403 = 50940 := pc_thm_624403
  have h_m_2 : m ≤ 1116 := staircase_step_M_direct k m 51156 1332 624403 217 50940 1116 heq (k_mono 36 k h_k_2) h_pc_K_next_1 h_pc_M_next_val_1 rfl (by decide)
  -- Step 2: k >= 36, m <= 1116 => k >= 45
  have h_m_mono_2 : m*(m+1)/2 ≤ 623286 := m_mono m 1116 h_m_2
  have h_pc_M_2 : Nat.primeCounting 623286 = 50850 := pc_thm_623286
  have h_pc_K_prev_2 : Nat.primeCounting 1980 = 299 := pc_thm_1980
  have h_k_3 : k ≥ 45 := staircase_step_K_direct k m 51156 623286 1980 50850 299 45 heq h_m_mono_2 h_pc_M_2 h_pc_K_prev_2 rfl (by decide)
  have h_pc_K_next_2 : Nat.primeCounting 2070 = 312 := pc_thm_2070
  have h_pc_M_next_val_2 : Nat.primeCounting 623286 = 50850 := pc_thm_623286
  have h_m_3 : m ≤ 1115 := staircase_step_M_direct k m 51156 2070 623286 312 50850 1115 heq (k_mono 45 k h_k_3) h_pc_K_next_2 h_pc_M_next_val_2 rfl (by decide)
  -- Step 3: k >= 45, m <= 1115 => k >= 51
  have h_m_mono_3 : m*(m+1)/2 ≤ 622170 := m_mono m 1115 h_m_3
  have h_pc_M_3 : Nat.primeCounting 622170 = 50775 := pc_thm_622170
  have h_pc_K_prev_3 : Nat.primeCounting 2550 = 373 := pc_thm_2550
  have h_k_4 : k ≥ 51 := staircase_step_K_direct k m 51156 622170 2550 50775 373 51 heq h_m_mono_3 h_pc_M_3 h_pc_K_prev_3 rfl (by decide)
  have h_pc_K_next_3 : Nat.primeCounting 2652 = 383 := pc_thm_2652
  have h_pc_M_next_val_3 : Nat.primeCounting 622170 = 50775 := pc_thm_622170
  have h_m_4 : m ≤ 1114 := staircase_step_M_direct k m 51156 2652 622170 383 50775 1114 heq (k_mono 51 k h_k_4) h_pc_K_next_3 h_pc_M_next_val_3 rfl (by decide)
  -- Step 4: k >= 51, m <= 1114 => k >= 57
  have h_m_mono_4 : m*(m+1)/2 ≤ 621055 := m_mono m 1114 h_m_4
  have h_pc_M_4 : Nat.primeCounting 621055 = 50695 := pc_thm_621055
  have h_pc_K_prev_4 : Nat.primeCounting 3192 = 452 := pc_thm_3192
  have h_k_5 : k ≥ 57 := staircase_step_K_direct k m 51156 621055 3192 50695 452 57 heq h_m_mono_4 h_pc_M_4 h_pc_K_prev_4 rfl (by decide)
  have h_pc_K_next_4 : Nat.primeCounting 3306 = 464 := pc_thm_3306
  have h_pc_M_next_val_4 : Nat.primeCounting 621055 = 50695 := pc_thm_621055
  have h_m_5 : m ≤ 1113 := staircase_step_M_direct k m 51156 3306 621055 464 50695 1113 heq (k_mono 57 k h_k_5) h_pc_K_next_4 h_pc_M_next_val_4 rfl (by decide)
  -- Step 5: k >= 57, m <= 1113 => k >= 63
  have h_m_mono_5 : m*(m+1)/2 ≤ 619941 := m_mono m 1113 h_m_5
  have h_pc_M_5 : Nat.primeCounting 619941 = 50607 := pc_thm_619941
  have h_pc_K_prev_5 : Nat.primeCounting 3906 = 539 := pc_thm_3906
  have h_k_6 : k ≥ 63 := staircase_step_K_direct k m 51156 619941 3906 50607 539 63 heq h_m_mono_5 h_pc_M_5 h_pc_K_prev_5 rfl (by decide)
  have h_pc_K_next_5 : Nat.primeCounting 4032 = 557 := pc_thm_4032
  have h_pc_M_next_val_5 : Nat.primeCounting 619941 = 50607 := pc_thm_619941
  have h_m_6 : m ≤ 1112 := staircase_step_M_direct k m 51156 4032 619941 557 50607 1112 heq (k_mono 63 k h_k_6) h_pc_K_next_5 h_pc_M_next_val_5 rfl (by decide)
  -- Step 6: k >= 63, m <= 1112 => k >= 68
  have h_m_mono_6 : m*(m+1)/2 ≤ 618828 := m_mono m 1112 h_m_6
  have h_pc_M_6 : Nat.primeCounting 618828 = 50525 := pc_thm_618828
  have h_pc_K_prev_6 : Nat.primeCounting 4556 = 617 := pc_thm_4556
  have h_k_7 : k ≥ 68 := staircase_step_K_direct k m 51156 618828 4556 50525 617 68 heq h_m_mono_6 h_pc_M_6 h_pc_K_prev_6 rfl (by decide)
  have h_pc_K_next_6 : Nat.primeCounting 4692 = 634 := pc_thm_4692
  have h_pc_M_next_val_6 : Nat.primeCounting 618828 = 50525 := pc_thm_618828
  have h_m_7 : m ≤ 1111 := staircase_step_M_direct k m 51156 4692 618828 634 50525 1111 heq (k_mono 68 k h_k_7) h_pc_K_next_6 h_pc_M_next_val_6 rfl (by decide)
  -- Step 7: k >= 68, m <= 1111 => k >= 73
  have h_m_mono_7 : m*(m+1)/2 ≤ 617716 := m_mono m 1111 h_m_7
  have h_pc_M_7 : Nat.primeCounting 617716 = 50449 := pc_thm_617716
  have h_pc_K_prev_7 : Nat.primeCounting 5256 = 697 := pc_thm_5256
  have h_k_8 : k ≥ 73 := staircase_step_K_direct k m 51156 617716 5256 50449 697 73 heq h_m_mono_7 h_pc_M_7 h_pc_K_prev_7 rfl (by decide)
  have h_pc_K_next_7 : Nat.primeCounting 5402 = 712 := pc_thm_5402
  have h_pc_M_next_val_7 : Nat.primeCounting 617716 = 50449 := pc_thm_617716
  have h_m_8 : m ≤ 1110 := staircase_step_M_direct k m 51156 5402 617716 712 50449 1110 heq (k_mono 73 k h_k_8) h_pc_K_next_7 h_pc_M_next_val_7 rfl (by decide)
  -- Step 8: k >= 73, m <= 1110 => k >= 78
  have h_m_mono_8 : m*(m+1)/2 ≤ 616605 := m_mono m 1110 h_m_8
  have h_pc_M_8 : Nat.primeCounting 616605 = 50360 := pc_thm_616605
  have h_pc_K_prev_8 : Nat.primeCounting 6006 = 783 := pc_thm_6006
  have h_k_9 : k ≥ 78 := staircase_step_K_direct k m 51156 616605 6006 50360 783 78 heq h_m_mono_8 h_pc_M_8 h_pc_K_prev_8 rfl (by decide)
  have h_pc_K_next_8 : Nat.primeCounting 6162 = 802 := pc_thm_6162
  have h_pc_M_next_val_8 : Nat.primeCounting 616605 = 50360 := pc_thm_616605
  have h_m_9 : m ≤ 1109 := staircase_step_M_direct k m 51156 6162 616605 802 50360 1109 heq (k_mono 78 k h_k_9) h_pc_K_next_8 h_pc_M_next_val_8 rfl (by decide)
  -- Step 9: k >= 78, m <= 1109 => k >= 83
  have h_m_mono_9 : m*(m+1)/2 ≤ 615495 := m_mono m 1109 h_m_9
  have h_pc_M_9 : Nat.primeCounting 615495 = 50268 := pc_thm_615495
  have h_pc_K_prev_9 : Nat.primeCounting 6806 = 876 := pc_thm_6806
  have h_k_10 : k ≥ 83 := staircase_step_K_direct k m 51156 615495 6806 50268 876 83 heq h_m_mono_9 h_pc_M_9 h_pc_K_prev_9 rfl (by decide)
  have h_pc_K_next_9 : Nat.primeCounting 6972 = 896 := pc_thm_6972
  have h_pc_M_next_val_9 : Nat.primeCounting 615495 = 50268 := pc_thm_615495
  have h_m_10 : m ≤ 1108 := staircase_step_M_direct k m 51156 6972 615495 896 50268 1108 heq (k_mono 83 k h_k_10) h_pc_K_next_9 h_pc_M_next_val_9 rfl (by decide)
  -- Step 10: k >= 83, m <= 1108 => k >= 88
  have h_m_mono_10 : m*(m+1)/2 ≤ 614386 := m_mono m 1108 h_m_10
  have h_pc_M_10 : Nat.primeCounting 614386 = 50184 := pc_thm_614386
  have h_pc_K_prev_10 : Nat.primeCounting 7656 = 971 := pc_thm_7656
  have h_k_11 : k ≥ 88 := staircase_step_K_direct k m 51156 614386 7656 50184 971 88 heq h_m_mono_10 h_pc_M_10 h_pc_K_prev_10 rfl (by decide)
  have h_pc_K_next_10 : Nat.primeCounting 7832 = 990 := pc_thm_7832
  have h_pc_M_next_val_10 : Nat.primeCounting 614386 = 50184 := pc_thm_614386
  have h_m_11 : m ≤ 1107 := staircase_step_M_direct k m 51156 7832 614386 990 50184 1107 heq (k_mono 88 k h_k_11) h_pc_K_next_10 h_pc_M_next_val_10 rfl (by decide)
  -- Step 11: k >= 88, m <= 1107 => k >= 92
  have h_m_mono_11 : m*(m+1)/2 ≤ 613278 := m_mono m 1107 h_m_11
  have h_pc_M_11 : Nat.primeCounting 613278 = 50104 := pc_thm_613278
  have h_pc_K_prev_11 : Nat.primeCounting 8372 = 1048 := pc_thm_8372
  have h_k_12 : k ≥ 92 := staircase_step_K_direct k m 51156 613278 8372 50104 1048 92 heq h_m_mono_11 h_pc_M_11 h_pc_K_prev_11 rfl (by decide)
  have h_pc_K_next_11 : Nat.primeCounting 8556 = 1066 := pc_thm_8556
  have h_pc_M_next_val_11 : Nat.primeCounting 613278 = 50104 := pc_thm_613278
  have h_m_12 : m ≤ 1106 := staircase_step_M_direct k m 51156 8556 613278 1066 50104 1106 heq (k_mono 92 k h_k_12) h_pc_K_next_11 h_pc_M_next_val_11 rfl (by decide)
  -- Step 12: k >= 92, m <= 1106 => k >= 96
  have h_m_mono_12 : m*(m+1)/2 ≤ 612171 := m_mono m 1106 h_m_12
  have h_pc_M_12 : Nat.primeCounting 612171 = 50022 := pc_thm_612171
  have h_pc_K_prev_12 : Nat.primeCounting 9120 = 1130 := pc_thm_9120
  have h_k_13 : k ≥ 96 := staircase_step_K_direct k m 51156 612171 9120 50022 1130 96 heq h_m_mono_12 h_pc_M_12 h_pc_K_prev_12 rfl (by decide)
  have h_pc_K_next_12 : Nat.primeCounting 9312 = 1152 := pc_thm_9312
  have h_pc_M_next_val_12 : Nat.primeCounting 612171 = 50022 := pc_thm_612171
  have h_m_13 : m ≤ 1105 := staircase_step_M_direct k m 51156 9312 612171 1152 50022 1105 heq (k_mono 96 k h_k_13) h_pc_K_next_12 h_pc_M_next_val_12 rfl (by decide)
  -- Step 13: k >= 96, m <= 1105 => k >= 99
  have h_m_mono_13 : m*(m+1)/2 ≤ 611065 := m_mono m 1105 h_m_13
  have h_pc_M_13 : Nat.primeCounting 611065 = 49938 := pc_thm_611065
  have h_pc_K_prev_13 : Nat.primeCounting 9702 = 1197 := pc_thm_9702
  have h_k_14 : k ≥ 99 := staircase_step_K_direct k m 51156 611065 9702 49938 1197 99 heq h_m_mono_13 h_pc_M_13 h_pc_K_prev_13 rfl (by decide)
  have h_pc_K_next_13 : Nat.primeCounting 9900 = 1220 := pc_thm_9900
  have h_pc_M_next_val_13 : Nat.primeCounting 611065 = 49938 := pc_thm_611065
  have h_m_14 : m ≤ 1104 := staircase_step_M_direct k m 51156 9900 611065 1220 49938 1104 heq (k_mono 99 k h_k_14) h_pc_K_next_13 h_pc_M_next_val_13 rfl (by decide)
  -- Step 14: k >= 99, m <= 1104 => k >= 103
  have h_m_mono_14 : m*(m+1)/2 ≤ 609960 := m_mono m 1104 h_m_14
  have h_pc_M_14 : Nat.primeCounting 609960 = 49857 := pc_thm_609960
  have h_pc_K_prev_14 : Nat.primeCounting 10506 = 1285 := pc_thm_10506
  have h_k_15 : k ≥ 103 := staircase_step_K_direct k m 51156 609960 10506 49857 1285 103 heq h_m_mono_14 h_pc_M_14 h_pc_K_prev_14 rfl (by decide)
  have h_pc_K_next_14 : Nat.primeCounting 10712 = 1306 := pc_thm_10712
  have h_pc_M_next_val_14 : Nat.primeCounting 609960 = 49857 := pc_thm_609960
  have h_m_15 : m ≤ 1103 := staircase_step_M_direct k m 51156 10712 609960 1306 49857 1103 heq (k_mono 103 k h_k_15) h_pc_K_next_14 h_pc_M_next_val_14 rfl (by decide)
  -- Step 15: k >= 103, m <= 1103 => k >= 107
  have h_m_mono_15 : m*(m+1)/2 ≤ 608856 := m_mono m 1103 h_m_15
  have h_pc_M_15 : Nat.primeCounting 608856 = 49767 := pc_thm_608856
  have h_pc_K_prev_15 : Nat.primeCounting 11342 = 1370 := pc_thm_11342
  have h_k_16 : k ≥ 107 := staircase_step_K_direct k m 51156 608856 11342 49767 1370 107 heq h_m_mono_15 h_pc_M_15 h_pc_K_prev_15 rfl (by decide)
  have h_pc_K_next_15 : Nat.primeCounting 11556 = 1392 := pc_thm_11556
  have h_pc_M_next_val_15 : Nat.primeCounting 608856 = 49767 := pc_thm_608856
  have h_m_16 : m ≤ 1102 := staircase_step_M_direct k m 51156 11556 608856 1392 49767 1102 heq (k_mono 107 k h_k_16) h_pc_K_next_15 h_pc_M_next_val_15 rfl (by decide)
  exact ⟨h_k_16, h_m_16⟩

theorem staircase_part_1 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_16 : k ≥ 107) (h_m_16 : m ≤ 1102) : k ≥ 154 ∧ m ≤ 1087 := by
  -- Step 16: k >= 107, m <= 1102 => k >= 111
  have h_m_mono_16 : m*(m+1)/2 ≤ 607753 := m_mono m 1102 h_m_16
  have h_pc_M_16 : Nat.primeCounting 607753 = 49684 := pc_thm_607753
  have h_pc_K_prev_16 : Nat.primeCounting 12210 = 1459 := pc_thm_12210
  have h_k_17 : k ≥ 111 := staircase_step_K_direct k m 51156 607753 12210 49684 1459 111 heq h_m_mono_16 h_pc_M_16 h_pc_K_prev_16 rfl (by decide)
  have h_pc_K_next_16 : Nat.primeCounting 12432 = 1483 := pc_thm_12432
  have h_pc_M_next_val_16 : Nat.primeCounting 607753 = 49684 := pc_thm_607753
  have h_m_17 : m ≤ 1101 := staircase_step_M_direct k m 51156 12432 607753 1483 49684 1101 heq (k_mono 111 k h_k_17) h_pc_K_next_16 h_pc_M_next_val_16 rfl (by decide)
  -- Step 17: k >= 111, m <= 1101 => k >= 114
  have h_m_mono_17 : m*(m+1)/2 ≤ 606651 := m_mono m 1101 h_m_17
  have h_pc_M_17 : Nat.primeCounting 606651 = 49599 := pc_thm_606651
  have h_pc_K_prev_17 : Nat.primeCounting 12882 = 1532 := pc_thm_12882
  have h_k_18 : k ≥ 114 := staircase_step_K_direct k m 51156 606651 12882 49599 1532 114 heq h_m_mono_17 h_pc_M_17 h_pc_K_prev_17 rfl (by decide)
  have h_pc_K_next_17 : Nat.primeCounting 13110 = 1560 := pc_thm_13110
  have h_pc_M_next_val_17 : Nat.primeCounting 606651 = 49599 := pc_thm_606651
  have h_m_18 : m ≤ 1100 := staircase_step_M_direct k m 51156 13110 606651 1560 49599 1100 heq (k_mono 114 k h_k_18) h_pc_K_next_17 h_pc_M_next_val_17 rfl (by decide)
  -- Step 18: k >= 114, m <= 1100 => k >= 118
  have h_m_mono_18 : m*(m+1)/2 ≤ 605550 := m_mono m 1100 h_m_18
  have h_pc_M_18 : Nat.primeCounting 605550 = 49520 := pc_thm_605550
  have h_pc_K_prev_18 : Nat.primeCounting 13806 = 1632 := pc_thm_13806
  have h_k_19 : k ≥ 118 := staircase_step_K_direct k m 51156 605550 13806 49520 1632 118 heq h_m_mono_18 h_pc_M_18 h_pc_K_prev_18 rfl (by decide)
  have h_pc_K_next_18 : Nat.primeCounting 14042 = 1656 := pc_thm_14042
  have h_pc_M_next_val_18 : Nat.primeCounting 605550 = 49520 := pc_thm_605550
  have h_m_19 : m ≤ 1099 := staircase_step_M_direct k m 51156 14042 605550 1656 49520 1099 heq (k_mono 118 k h_k_19) h_pc_K_next_18 h_pc_M_next_val_18 rfl (by decide)
  -- Step 19: k >= 118, m <= 1099 => k >= 121
  have h_m_mono_19 : m*(m+1)/2 ≤ 604450 := m_mono m 1099 h_m_19
  have h_pc_M_19 : Nat.primeCounting 604450 = 49437 := pc_thm_604450
  have h_pc_K_prev_19 : Nat.primeCounting 14520 = 1700 := pc_thm_14520
  have h_k_20 : k ≥ 121 := staircase_step_K_direct k m 51156 604450 14520 49437 1700 121 heq h_m_mono_19 h_pc_M_19 h_pc_K_prev_19 rfl (by decide)
  have h_pc_K_next_19 : Nat.primeCounting 14762 = 1729 := pc_thm_14762
  have h_pc_M_next_val_19 : Nat.primeCounting 604450 = 49437 := pc_thm_604450
  have h_m_20 : m ≤ 1098 := staircase_step_M_direct k m 51156 14762 604450 1729 49437 1098 heq (k_mono 121 k h_k_20) h_pc_K_next_19 h_pc_M_next_val_19 rfl (by decide)
  -- Step 20: k >= 121, m <= 1098 => k >= 124
  have h_m_mono_20 : m*(m+1)/2 ≤ 603351 := m_mono m 1098 h_m_20
  have h_pc_M_20 : Nat.primeCounting 603351 = 49352 := pc_thm_603351
  have h_pc_K_prev_20 : Nat.primeCounting 15252 = 1779 := pc_thm_15252
  have h_k_21 : k ≥ 124 := staircase_step_K_direct k m 51156 603351 15252 49352 1779 124 heq h_m_mono_20 h_pc_M_20 h_pc_K_prev_20 rfl (by decide)
  have h_pc_K_next_20 : Nat.primeCounting 15500 = 1810 := pc_thm_15500
  have h_pc_M_next_val_20 : Nat.primeCounting 603351 = 49352 := pc_thm_603351
  have h_m_21 : m ≤ 1097 := staircase_step_M_direct k m 51156 15500 603351 1810 49352 1097 heq (k_mono 124 k h_k_21) h_pc_K_next_20 h_pc_M_next_val_20 rfl (by decide)
  -- Step 21: k >= 124, m <= 1097 => k >= 127
  have h_m_mono_21 : m*(m+1)/2 ≤ 602253 := m_mono m 1097 h_m_21
  have h_pc_M_21 : Nat.primeCounting 602253 = 49268 := pc_thm_602253
  have h_pc_K_prev_21 : Nat.primeCounting 16002 = 1863 := pc_thm_16002
  have h_k_22 : k ≥ 127 := staircase_step_K_direct k m 51156 602253 16002 49268 1863 127 heq h_m_mono_21 h_pc_M_21 h_pc_K_prev_21 rfl (by decide)
  have h_pc_K_next_21 : Nat.primeCounting 16256 = 1889 := pc_thm_16256
  have h_pc_M_next_val_21 : Nat.primeCounting 602253 = 49268 := pc_thm_602253
  have h_m_22 : m ≤ 1096 := staircase_step_M_direct k m 51156 16256 602253 1889 49268 1096 heq (k_mono 127 k h_k_22) h_pc_K_next_21 h_pc_M_next_val_21 rfl (by decide)
  -- Step 22: k >= 127, m <= 1096 => k >= 131
  have h_m_mono_22 : m*(m+1)/2 ≤ 601156 := m_mono m 1096 h_m_22
  have h_pc_M_22 : Nat.primeCounting 601156 = 49185 := pc_thm_601156
  have h_pc_K_prev_22 : Nat.primeCounting 17030 = 1964 := pc_thm_17030
  have h_k_23 : k ≥ 131 := staircase_step_K_direct k m 51156 601156 17030 49185 1964 131 heq h_m_mono_22 h_pc_M_22 h_pc_K_prev_22 rfl (by decide)
  have h_pc_K_next_22 : Nat.primeCounting 17292 = 1987 := pc_thm_17292
  have h_pc_M_next_val_22 : Nat.primeCounting 601156 = 49185 := pc_thm_601156
  have h_m_23 : m ≤ 1095 := staircase_step_M_direct k m 51156 17292 601156 1987 49185 1095 heq (k_mono 131 k h_k_23) h_pc_K_next_22 h_pc_M_next_val_22 rfl (by decide)
  -- Step 23: k >= 131, m <= 1095 => k >= 134
  have h_m_mono_23 : m*(m+1)/2 ≤ 600060 := m_mono m 1095 h_m_23
  have h_pc_M_23 : Nat.primeCounting 600060 = 49101 := pc_thm_600060
  have h_pc_K_prev_23 : Nat.primeCounting 17822 = 2043 := pc_thm_17822
  have h_k_24 : k ≥ 134 := staircase_step_K_direct k m 51156 600060 17822 49101 2043 134 heq h_m_mono_23 h_pc_M_23 h_pc_K_prev_23 rfl (by decide)
  have h_pc_K_next_23 : Nat.primeCounting 18090 = 2073 := pc_thm_18090
  have h_pc_M_next_val_23 : Nat.primeCounting 600060 = 49101 := pc_thm_600060
  have h_m_24 : m ≤ 1094 := staircase_step_M_direct k m 51156 18090 600060 2073 49101 1094 heq (k_mono 134 k h_k_24) h_pc_K_next_23 h_pc_M_next_val_23 rfl (by decide)
  -- Step 24: k >= 134, m <= 1094 => k >= 137
  have h_m_mono_24 : m*(m+1)/2 ≤ 598965 := m_mono m 1094 h_m_24
  have h_pc_M_24 : Nat.primeCounting 598965 = 49020 := pc_thm_598965
  have h_pc_K_prev_24 : Nat.primeCounting 18632 = 2129 := pc_thm_18632
  have h_k_25 : k ≥ 137 := staircase_step_K_direct k m 51156 598965 18632 49020 2129 137 heq h_m_mono_24 h_pc_M_24 h_pc_K_prev_24 rfl (by decide)
  have h_pc_K_next_24 : Nat.primeCounting 18906 = 2150 := pc_thm_18906
  have h_pc_M_next_val_24 : Nat.primeCounting 598965 = 49020 := pc_thm_598965
  have h_m_25 : m ≤ 1093 := staircase_step_M_direct k m 51156 18906 598965 2150 49020 1093 heq (k_mono 137 k h_k_25) h_pc_K_next_24 h_pc_M_next_val_24 rfl (by decide)
  -- Step 25: k >= 137, m <= 1093 => k >= 140
  have h_m_mono_25 : m*(m+1)/2 ≤ 597871 := m_mono m 1093 h_m_25
  have h_pc_M_25 : Nat.primeCounting 597871 = 48946 := pc_thm_597871
  have h_pc_K_prev_25 : Nat.primeCounting 19460 = 2206 := pc_thm_19460
  have h_k_26 : k ≥ 140 := staircase_step_K_direct k m 51156 597871 19460 48946 2206 140 heq h_m_mono_25 h_pc_M_25 h_pc_K_prev_25 rfl (by decide)
  have h_pc_K_next_25 : Nat.primeCounting 19740 = 2234 := pc_thm_19740
  have h_pc_M_next_val_25 : Nat.primeCounting 597871 = 48946 := pc_thm_597871
  have h_m_26 : m ≤ 1092 := staircase_step_M_direct k m 51156 19740 597871 2234 48946 1092 heq (k_mono 140 k h_k_26) h_pc_K_next_25 h_pc_M_next_val_25 rfl (by decide)
  -- Step 26: k >= 140, m <= 1092 => k >= 143
  have h_m_mono_26 : m*(m+1)/2 ≤ 596778 := m_mono m 1092 h_m_26
  have h_pc_M_26 : Nat.primeCounting 596778 = 48859 := pc_thm_596778
  have h_pc_K_prev_26 : Nat.primeCounting 20306 = 2293 := pc_thm_20306
  have h_k_27 : k ≥ 143 := staircase_step_K_direct k m 51156 596778 20306 48859 2293 143 heq h_m_mono_26 h_pc_M_26 h_pc_K_prev_26 rfl (by decide)
  have h_pc_K_next_26 : Nat.primeCounting 20592 = 2321 := pc_thm_20592
  have h_pc_M_next_val_26 : Nat.primeCounting 596778 = 48859 := pc_thm_596778
  have h_m_27 : m ≤ 1091 := staircase_step_M_direct k m 51156 20592 596778 2321 48859 1091 heq (k_mono 143 k h_k_27) h_pc_K_next_26 h_pc_M_next_val_26 rfl (by decide)
  -- Step 27: k >= 143, m <= 1091 => k >= 145
  have h_m_mono_27 : m*(m+1)/2 ≤ 595686 := m_mono m 1091 h_m_27
  have h_pc_M_27 : Nat.primeCounting 595686 = 48778 := pc_thm_595686
  have h_pc_K_prev_27 : Nat.primeCounting 20880 = 2348 := pc_thm_20880
  have h_k_28 : k ≥ 145 := staircase_step_K_direct k m 51156 595686 20880 48778 2348 145 heq h_m_mono_27 h_pc_M_27 h_pc_K_prev_27 rfl (by decide)
  have h_pc_K_next_27 : Nat.primeCounting 21170 = 2380 := pc_thm_21170
  have h_pc_M_next_val_27 : Nat.primeCounting 595686 = 48778 := pc_thm_595686
  have h_m_28 : m ≤ 1090 := staircase_step_M_direct k m 51156 21170 595686 2380 48778 1090 heq (k_mono 145 k h_k_28) h_pc_K_next_27 h_pc_M_next_val_27 rfl (by decide)
  -- Step 28: k >= 145, m <= 1090 => k >= 148
  have h_m_mono_28 : m*(m+1)/2 ≤ 594595 := m_mono m 1090 h_m_28
  have h_pc_M_28 : Nat.primeCounting 594595 = 48694 := pc_thm_594595
  have h_pc_K_prev_28 : Nat.primeCounting 21756 = 2440 := pc_thm_21756
  have h_k_29 : k ≥ 148 := staircase_step_K_direct k m 51156 594595 21756 48694 2440 148 heq h_m_mono_28 h_pc_M_28 h_pc_K_prev_28 rfl (by decide)
  have h_pc_K_next_28 : Nat.primeCounting 22052 = 2471 := pc_thm_22052
  have h_pc_M_next_val_28 : Nat.primeCounting 594595 = 48694 := pc_thm_594595
  have h_m_29 : m ≤ 1089 := staircase_step_M_direct k m 51156 22052 594595 2471 48694 1089 heq (k_mono 148 k h_k_29) h_pc_K_next_28 h_pc_M_next_val_28 rfl (by decide)
  -- Step 29: k >= 148, m <= 1089 => k >= 151
  have h_m_mono_29 : m*(m+1)/2 ≤ 593505 := m_mono m 1089 h_m_29
  have h_pc_M_29 : Nat.primeCounting 593505 = 48613 := pc_thm_593505
  have h_pc_K_prev_29 : Nat.primeCounting 22650 = 2530 := pc_thm_22650
  have h_k_30 : k ≥ 151 := staircase_step_K_direct k m 51156 593505 22650 48613 2530 151 heq h_m_mono_29 h_pc_M_29 h_pc_K_prev_29 rfl (by decide)
  have h_pc_K_next_29 : Nat.primeCounting 22952 = 2560 := pc_thm_22952
  have h_pc_M_next_val_29 : Nat.primeCounting 593505 = 48613 := pc_thm_593505
  have h_m_30 : m ≤ 1088 := staircase_step_M_direct k m 51156 22952 593505 2560 48613 1088 heq (k_mono 151 k h_k_30) h_pc_K_next_29 h_pc_M_next_val_29 rfl (by decide)
  -- Step 30: k >= 151, m <= 1088 => k >= 154
  have h_m_mono_30 : m*(m+1)/2 ≤ 592416 := m_mono m 1088 h_m_30
  have h_pc_M_30 : Nat.primeCounting 592416 = 48522 := pc_thm_592416
  have h_pc_K_prev_30 : Nat.primeCounting 23562 = 2620 := pc_thm_23562
  have h_k_31 : k ≥ 154 := staircase_step_K_direct k m 51156 592416 23562 48522 2620 154 heq h_m_mono_30 h_pc_M_30 h_pc_K_prev_30 rfl (by decide)
  have h_pc_K_next_30 : Nat.primeCounting 23870 = 2654 := pc_thm_23870
  have h_pc_M_next_val_30 : Nat.primeCounting 592416 = 48522 := pc_thm_592416
  have h_m_31 : m ≤ 1087 := staircase_step_M_direct k m 51156 23870 592416 2654 48522 1087 heq (k_mono 154 k h_k_31) h_pc_K_next_30 h_pc_M_next_val_30 rfl (by decide)
  exact ⟨h_k_31, h_m_31⟩

theorem staircase_part_2 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_31 : k ≥ 154) (h_m_31 : m ≤ 1087) : k ≥ 191 ∧ m ≤ 1072 := by
  -- Step 31: k >= 154, m <= 1087 => k >= 156
  have h_m_mono_31 : m*(m+1)/2 ≤ 591328 := m_mono m 1087 h_m_31
  have h_pc_M_31 : Nat.primeCounting 591328 = 48445 := pc_thm_591328
  have h_pc_K_prev_31 : Nat.primeCounting 24180 = 2691 := pc_thm_24180
  have h_k_32 : k ≥ 156 := staircase_step_K_direct k m 51156 591328 24180 48445 2691 156 heq h_m_mono_31 h_pc_M_31 h_pc_K_prev_31 rfl (by decide)
  have h_pc_K_next_31 : Nat.primeCounting 24492 = 2717 := pc_thm_24492
  have h_pc_M_next_val_31 : Nat.primeCounting 591328 = 48445 := pc_thm_591328
  have h_m_32 : m ≤ 1086 := staircase_step_M_direct k m 51156 24492 591328 2717 48445 1086 heq (k_mono 156 k h_k_32) h_pc_K_next_31 h_pc_M_next_val_31 rfl (by decide)
  -- Step 32: k >= 156, m <= 1086 => k >= 159
  have h_m_mono_32 : m*(m+1)/2 ≤ 590241 := m_mono m 1086 h_m_32
  have h_pc_M_32 : Nat.primeCounting 590241 = 48368 := pc_thm_590241
  have h_pc_K_prev_32 : Nat.primeCounting 25122 = 2773 := pc_thm_25122
  have h_k_33 : k ≥ 159 := staircase_step_K_direct k m 51156 590241 25122 48368 2773 159 heq h_m_mono_32 h_pc_M_32 h_pc_K_prev_32 rfl (by decide)
  have h_pc_K_next_32 : Nat.primeCounting 25440 = 2804 := pc_thm_25440
  have h_pc_M_next_val_32 : Nat.primeCounting 590241 = 48368 := pc_thm_590241
  have h_m_33 : m ≤ 1085 := staircase_step_M_direct k m 51156 25440 590241 2804 48368 1085 heq (k_mono 159 k h_k_33) h_pc_K_next_32 h_pc_M_next_val_32 rfl (by decide)
  -- Step 33: k >= 159, m <= 1085 => k >= 161
  have h_m_mono_33 : m*(m+1)/2 ≤ 589155 := m_mono m 1085 h_m_33
  have h_pc_M_33 : Nat.primeCounting 589155 = 48291 := pc_thm_589155
  have h_pc_K_prev_33 : Nat.primeCounting 25760 = 2836 := pc_thm_25760
  have h_k_34 : k ≥ 161 := staircase_step_K_direct k m 51156 589155 25760 48291 2836 161 heq h_m_mono_33 h_pc_M_33 h_pc_K_prev_33 rfl (by decide)
  have h_pc_K_next_33 : Nat.primeCounting 26082 = 2866 := pc_thm_26082
  have h_pc_M_next_val_33 : Nat.primeCounting 589155 = 48291 := pc_thm_589155
  have h_m_34 : m ≤ 1084 := staircase_step_M_direct k m 51156 26082 589155 2866 48291 1084 heq (k_mono 161 k h_k_34) h_pc_K_next_33 h_pc_M_next_val_33 rfl (by decide)
  -- Step 34: k >= 161, m <= 1084 => k >= 164
  have h_m_mono_34 : m*(m+1)/2 ≤ 588070 := m_mono m 1084 h_m_34
  have h_pc_M_34 : Nat.primeCounting 588070 = 48215 := pc_thm_588070
  have h_pc_K_prev_34 : Nat.primeCounting 26732 = 2935 := pc_thm_26732
  have h_k_35 : k ≥ 164 := staircase_step_K_direct k m 51156 588070 26732 48215 2935 164 heq h_m_mono_34 h_pc_M_34 h_pc_K_prev_34 rfl (by decide)
  have h_pc_K_next_34 : Nat.primeCounting 27060 = 2966 := pc_thm_27060
  have h_pc_M_next_val_34 : Nat.primeCounting 588070 = 48215 := pc_thm_588070
  have h_m_35 : m ≤ 1083 := staircase_step_M_direct k m 51156 27060 588070 2966 48215 1083 heq (k_mono 164 k h_k_35) h_pc_K_next_34 h_pc_M_next_val_34 rfl (by decide)
  -- Step 35: k >= 164, m <= 1083 => k >= 167
  have h_m_mono_35 : m*(m+1)/2 ≤ 586986 := m_mono m 1083 h_m_35
  have h_pc_M_35 : Nat.primeCounting 586986 = 48123 := pc_thm_586986
  have h_pc_K_prev_35 : Nat.primeCounting 27722 = 3022 := pc_thm_27722
  have h_k_36 : k ≥ 167 := staircase_step_K_direct k m 51156 586986 27722 48123 3022 167 heq h_m_mono_35 h_pc_M_35 h_pc_K_prev_35 rfl (by decide)
  have h_pc_K_next_35 : Nat.primeCounting 28056 = 3060 := pc_thm_28056
  have h_pc_M_next_val_35 : Nat.primeCounting 586986 = 48123 := pc_thm_586986
  have h_m_36 : m ≤ 1082 := staircase_step_M_direct k m 51156 28056 586986 3060 48123 1082 heq (k_mono 167 k h_k_36) h_pc_K_next_35 h_pc_M_next_val_35 rfl (by decide)
  -- Step 36: k >= 167, m <= 1082 => k >= 169
  have h_m_mono_36 : m*(m+1)/2 ≤ 585903 := m_mono m 1082 h_m_36
  have h_pc_M_36 : Nat.primeCounting 585903 = 48037 := pc_thm_585903
  have h_pc_K_prev_36 : Nat.primeCounting 28392 = 3088 := pc_thm_28392
  have h_k_37 : k ≥ 169 := staircase_step_K_direct k m 51156 585903 28392 48037 3088 169 heq h_m_mono_36 h_pc_M_36 h_pc_K_prev_36 rfl (by decide)
  have h_pc_K_next_36 : Nat.primeCounting 28730 = 3130 := pc_thm_28730
  have h_pc_M_next_val_36 : Nat.primeCounting 585903 = 48037 := pc_thm_585903
  have h_m_37 : m ≤ 1081 := staircase_step_M_direct k m 51156 28730 585903 3130 48037 1081 heq (k_mono 169 k h_k_37) h_pc_K_next_36 h_pc_M_next_val_36 rfl (by decide)
  -- Step 37: k >= 169, m <= 1081 => k >= 172
  have h_m_mono_37 : m*(m+1)/2 ≤ 584821 := m_mono m 1081 h_m_37
  have h_pc_M_37 : Nat.primeCounting 584821 = 47948 := pc_thm_584821
  have h_pc_K_prev_37 : Nat.primeCounting 29412 = 3196 := pc_thm_29412
  have h_k_38 : k ≥ 172 := staircase_step_K_direct k m 51156 584821 29412 47948 3196 172 heq h_m_mono_37 h_pc_M_37 h_pc_K_prev_37 rfl (by decide)
  have h_pc_K_next_37 : Nat.primeCounting 29756 = 3225 := pc_thm_29756
  have h_pc_M_next_val_37 : Nat.primeCounting 584821 = 47948 := pc_thm_584821
  have h_m_38 : m ≤ 1080 := staircase_step_M_direct k m 51156 29756 584821 3225 47948 1080 heq (k_mono 172 k h_k_38) h_pc_K_next_37 h_pc_M_next_val_37 rfl (by decide)
  -- Step 38: k >= 172, m <= 1080 => k >= 174
  have h_m_mono_38 : m*(m+1)/2 ≤ 583740 := m_mono m 1080 h_m_38
  have h_pc_M_38 : Nat.primeCounting 583740 = 47872 := pc_thm_583740
  have h_pc_K_prev_38 : Nat.primeCounting 30102 = 3254 := pc_thm_30102
  have h_k_39 : k ≥ 174 := staircase_step_K_direct k m 51156 583740 30102 47872 3254 174 heq h_m_mono_38 h_pc_M_38 h_pc_K_prev_38 rfl (by decide)
  have h_pc_K_next_38 : Nat.primeCounting 30450 = 3288 := pc_thm_30450
  have h_pc_M_next_val_38 : Nat.primeCounting 583740 = 47872 := pc_thm_583740
  have h_m_39 : m ≤ 1079 := staircase_step_M_direct k m 51156 30450 583740 3288 47872 1079 heq (k_mono 174 k h_k_39) h_pc_K_next_38 h_pc_M_next_val_38 rfl (by decide)
  -- Step 39: k >= 174, m <= 1079 => k >= 177
  have h_m_mono_39 : m*(m+1)/2 ≤ 582660 := m_mono m 1079 h_m_39
  have h_pc_M_39 : Nat.primeCounting 582660 = 47785 := pc_thm_582660
  have h_pc_K_prev_39 : Nat.primeCounting 31152 = 3355 := pc_thm_31152
  have h_k_40 : k ≥ 177 := staircase_step_K_direct k m 51156 582660 31152 47785 3355 177 heq h_m_mono_39 h_pc_M_39 h_pc_K_prev_39 rfl (by decide)
  have h_pc_K_next_39 : Nat.primeCounting 31506 = 3389 := pc_thm_31506
  have h_pc_M_next_val_39 : Nat.primeCounting 582660 = 47785 := pc_thm_582660
  have h_m_40 : m ≤ 1078 := staircase_step_M_direct k m 51156 31506 582660 3389 47785 1078 heq (k_mono 177 k h_k_40) h_pc_K_next_39 h_pc_M_next_val_39 rfl (by decide)
  -- Step 40: k >= 177, m <= 1078 => k >= 179
  have h_m_mono_40 : m*(m+1)/2 ≤ 581581 := m_mono m 1078 h_m_40
  have h_pc_M_40 : Nat.primeCounting 581581 = 47708 := pc_thm_581581
  have h_pc_K_prev_40 : Nat.primeCounting 31862 = 3423 := pc_thm_31862
  have h_k_41 : k ≥ 179 := staircase_step_K_direct k m 51156 581581 31862 47708 3423 179 heq h_m_mono_40 h_pc_M_40 h_pc_K_prev_40 rfl (by decide)
  have h_pc_K_next_40 : Nat.primeCounting 32220 = 3456 := pc_thm_32220
  have h_pc_M_next_val_40 : Nat.primeCounting 581581 = 47708 := pc_thm_581581
  have h_m_41 : m ≤ 1077 := staircase_step_M_direct k m 51156 32220 581581 3456 47708 1077 heq (k_mono 179 k h_k_41) h_pc_K_next_40 h_pc_M_next_val_40 rfl (by decide)
  -- Step 41: k >= 179, m <= 1077 => k >= 182
  have h_m_mono_41 : m*(m+1)/2 ≤ 580503 := m_mono m 1077 h_m_41
  have h_pc_M_41 : Nat.primeCounting 580503 = 47620 := pc_thm_580503
  have h_pc_K_prev_41 : Nat.primeCounting 32942 = 3531 := pc_thm_32942
  have h_k_42 : k ≥ 182 := staircase_step_K_direct k m 51156 580503 32942 47620 3531 182 heq h_m_mono_41 h_pc_M_41 h_pc_K_prev_41 rfl (by decide)
  have h_pc_K_next_41 : Nat.primeCounting 33306 = 3565 := pc_thm_33306
  have h_pc_M_next_val_41 : Nat.primeCounting 580503 = 47620 := pc_thm_580503
  have h_m_42 : m ≤ 1076 := staircase_step_M_direct k m 51156 33306 580503 3565 47620 1076 heq (k_mono 182 k h_k_42) h_pc_K_next_41 h_pc_M_next_val_41 rfl (by decide)
  -- Step 42: k >= 182, m <= 1076 => k >= 184
  have h_m_mono_42 : m*(m+1)/2 ≤ 579426 := m_mono m 1076 h_m_42
  have h_pc_M_42 : Nat.primeCounting 579426 = 47538 := pc_thm_579426
  have h_pc_K_prev_42 : Nat.primeCounting 33672 = 3607 := pc_thm_33672
  have h_k_43 : k ≥ 184 := staircase_step_K_direct k m 51156 579426 33672 47538 3607 184 heq h_m_mono_42 h_pc_M_42 h_pc_K_prev_42 rfl (by decide)
  have h_pc_K_next_42 : Nat.primeCounting 34040 = 3642 := pc_thm_34040
  have h_pc_M_next_val_42 : Nat.primeCounting 579426 = 47538 := pc_thm_579426
  have h_m_43 : m ≤ 1075 := staircase_step_M_direct k m 51156 34040 579426 3642 47538 1075 heq (k_mono 184 k h_k_43) h_pc_K_next_42 h_pc_M_next_val_42 rfl (by decide)
  -- Step 43: k >= 184, m <= 1075 => k >= 186
  have h_m_mono_43 : m*(m+1)/2 ≤ 578350 := m_mono m 1075 h_m_43
  have h_pc_M_43 : Nat.primeCounting 578350 = 47458 := pc_thm_578350
  have h_pc_K_prev_43 : Nat.primeCounting 34410 = 3676 := pc_thm_34410
  have h_k_44 : k ≥ 186 := staircase_step_K_direct k m 51156 578350 34410 47458 3676 186 heq h_m_mono_43 h_pc_M_43 h_pc_K_prev_43 rfl (by decide)
  have h_pc_K_next_43 : Nat.primeCounting 34782 = 3715 := pc_thm_34782
  have h_pc_M_next_val_43 : Nat.primeCounting 578350 = 47458 := pc_thm_578350
  have h_m_44 : m ≤ 1074 := staircase_step_M_direct k m 51156 34782 578350 3715 47458 1074 heq (k_mono 186 k h_k_44) h_pc_K_next_43 h_pc_M_next_val_43 rfl (by decide)
  -- Step 44: k >= 186, m <= 1074 => k >= 188
  have h_m_mono_44 : m*(m+1)/2 ≤ 577275 := m_mono m 1074 h_m_44
  have h_pc_M_44 : Nat.primeCounting 577275 = 47379 := pc_thm_577275
  have h_pc_K_prev_44 : Nat.primeCounting 35156 = 3749 := pc_thm_35156
  have h_k_45 : k ≥ 188 := staircase_step_K_direct k m 51156 577275 35156 47379 3749 188 heq h_m_mono_44 h_pc_M_44 h_pc_K_prev_44 rfl (by decide)
  have h_pc_K_next_44 : Nat.primeCounting 35532 = 3783 := pc_thm_35532
  have h_pc_M_next_val_44 : Nat.primeCounting 577275 = 47379 := pc_thm_577275
  have h_m_45 : m ≤ 1073 := staircase_step_M_direct k m 51156 35532 577275 3783 47379 1073 heq (k_mono 188 k h_k_45) h_pc_K_next_44 h_pc_M_next_val_44 rfl (by decide)
  -- Step 45: k >= 188, m <= 1073 => k >= 191
  have h_m_mono_45 : m*(m+1)/2 ≤ 576201 := m_mono m 1073 h_m_45
  have h_pc_M_45 : Nat.primeCounting 576201 = 47296 := pc_thm_576201
  have h_pc_K_prev_45 : Nat.primeCounting 36290 = 3850 := pc_thm_36290
  have h_k_46 : k ≥ 191 := staircase_step_K_direct k m 51156 576201 36290 47296 3850 191 heq h_m_mono_45 h_pc_M_45 h_pc_K_prev_45 rfl (by decide)
  have h_pc_K_next_45 : Nat.primeCounting 36672 = 3887 := pc_thm_36672
  have h_pc_M_next_val_45 : Nat.primeCounting 576201 = 47296 := pc_thm_576201
  have h_m_46 : m ≤ 1072 := staircase_step_M_direct k m 51156 36672 576201 3887 47296 1072 heq (k_mono 191 k h_k_46) h_pc_K_next_45 h_pc_M_next_val_45 rfl (by decide)
  exact ⟨h_k_46, h_m_46⟩

theorem staircase_part_3 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_46 : k ≥ 191) (h_m_46 : m ≤ 1072) : k ≥ 222 ∧ m ≤ 1057 := by
  -- Step 46: k >= 191, m <= 1072 => k >= 193
  have h_m_mono_46 : m*(m+1)/2 ≤ 575128 := m_mono m 1072 h_m_46
  have h_pc_M_46 : Nat.primeCounting 575128 = 47212 := pc_thm_575128
  have h_pc_K_prev_46 : Nat.primeCounting 37056 = 3929 := pc_thm_37056
  have h_k_47 : k ≥ 193 := staircase_step_K_direct k m 51156 575128 37056 47212 3929 193 heq h_m_mono_46 h_pc_M_46 h_pc_K_prev_46 rfl (by decide)
  have h_pc_K_next_46 : Nat.primeCounting 37442 = 3963 := pc_thm_37442
  have h_pc_M_next_val_46 : Nat.primeCounting 575128 = 47212 := pc_thm_575128
  have h_m_47 : m ≤ 1071 := staircase_step_M_direct k m 51156 37442 575128 3963 47212 1071 heq (k_mono 193 k h_k_47) h_pc_K_next_46 h_pc_M_next_val_46 rfl (by decide)
  -- Step 47: k >= 193, m <= 1071 => k >= 195
  have h_m_mono_47 : m*(m+1)/2 ≤ 574056 := m_mono m 1071 h_m_47
  have h_pc_M_47 : Nat.primeCounting 574056 = 47137 := pc_thm_574056
  have h_pc_K_prev_47 : Nat.primeCounting 37830 = 4000 := pc_thm_37830
  have h_k_48 : k ≥ 195 := staircase_step_K_direct k m 51156 574056 37830 47137 4000 195 heq h_m_mono_47 h_pc_M_47 h_pc_K_prev_47 rfl (by decide)
  have h_pc_K_next_47 : Nat.primeCounting 38220 = 4034 := pc_thm_38220
  have h_pc_M_next_val_47 : Nat.primeCounting 574056 = 47137 := pc_thm_574056
  have h_m_48 : m ≤ 1070 := staircase_step_M_direct k m 51156 38220 574056 4034 47137 1070 heq (k_mono 195 k h_k_48) h_pc_K_next_47 h_pc_M_next_val_47 rfl (by decide)
  -- Step 48: k >= 195, m <= 1070 => k >= 197
  have h_m_mono_48 : m*(m+1)/2 ≤ 572985 := m_mono m 1070 h_m_48
  have h_pc_M_48 : Nat.primeCounting 572985 = 47060 := pc_thm_572985
  have h_pc_K_prev_48 : Nat.primeCounting 38612 = 4068 := pc_thm_38612
  have h_k_49 : k ≥ 197 := staircase_step_K_direct k m 51156 572985 38612 47060 4068 197 heq h_m_mono_48 h_pc_M_48 h_pc_K_prev_48 rfl (by decide)
  have h_pc_K_next_48 : Nat.primeCounting 39006 = 4107 := pc_thm_39006
  have h_pc_M_next_val_48 : Nat.primeCounting 572985 = 47060 := pc_thm_572985
  have h_m_49 : m ≤ 1069 := staircase_step_M_direct k m 51156 39006 572985 4107 47060 1069 heq (k_mono 197 k h_k_49) h_pc_K_next_48 h_pc_M_next_val_48 rfl (by decide)
  -- Step 49: k >= 197, m <= 1069 => k >= 200
  have h_m_mono_49 : m*(m+1)/2 ≤ 571915 := m_mono m 1069 h_m_49
  have h_pc_M_49 : Nat.primeCounting 571915 = 46972 := pc_thm_571915
  have h_pc_K_prev_49 : Nat.primeCounting 39800 = 4183 := pc_thm_39800
  have h_k_50 : k ≥ 200 := staircase_step_K_direct k m 51156 571915 39800 46972 4183 200 heq h_m_mono_49 h_pc_M_49 h_pc_K_prev_49 rfl (by decide)
  have h_pc_K_next_49 : Nat.primeCounting 40200 = 4223 := pc_thm_40200
  have h_pc_M_next_val_49 : Nat.primeCounting 571915 = 46972 := pc_thm_571915
  have h_m_50 : m ≤ 1068 := staircase_step_M_direct k m 51156 40200 571915 4223 46972 1068 heq (k_mono 200 k h_k_50) h_pc_K_next_49 h_pc_M_next_val_49 rfl (by decide)
  -- Step 50: k >= 200, m <= 1068 => k >= 202
  have h_m_mono_50 : m*(m+1)/2 ≤ 570846 := m_mono m 1068 h_m_50
  have h_pc_M_50 : Nat.primeCounting 570846 = 46891 := pc_thm_570846
  have h_pc_K_prev_50 : Nat.primeCounting 40602 = 4256 := pc_thm_40602
  have h_k_51 : k ≥ 202 := staircase_step_K_direct k m 51156 570846 40602 46891 4256 202 heq h_m_mono_50 h_pc_M_50 h_pc_K_prev_50 rfl (by decide)
  have h_pc_K_next_50 : Nat.primeCounting 41006 = 4291 := pc_thm_41006
  have h_pc_M_next_val_50 : Nat.primeCounting 570846 = 46891 := pc_thm_570846
  have h_m_51 : m ≤ 1067 := staircase_step_M_direct k m 51156 41006 570846 4291 46891 1067 heq (k_mono 202 k h_k_51) h_pc_K_next_50 h_pc_M_next_val_50 rfl (by decide)
  -- Step 51: k >= 202, m <= 1067 => k >= 204
  have h_m_mono_51 : m*(m+1)/2 ≤ 569778 := m_mono m 1067 h_m_51
  have h_pc_M_51 : Nat.primeCounting 569778 = 46801 := pc_thm_569778
  have h_pc_K_prev_51 : Nat.primeCounting 41412 = 4333 := pc_thm_41412
  have h_k_52 : k ≥ 204 := staircase_step_K_direct k m 51156 569778 41412 46801 4333 204 heq h_m_mono_51 h_pc_M_51 h_pc_K_prev_51 rfl (by decide)
  have h_pc_K_next_51 : Nat.primeCounting 41820 = 4372 := pc_thm_41820
  have h_pc_M_next_val_51 : Nat.primeCounting 569778 = 46801 := pc_thm_569778
  have h_m_52 : m ≤ 1066 := staircase_step_M_direct k m 51156 41820 569778 4372 46801 1066 heq (k_mono 204 k h_k_52) h_pc_K_next_51 h_pc_M_next_val_51 rfl (by decide)
  -- Step 52: k >= 204, m <= 1066 => k >= 206
  have h_m_mono_52 : m*(m+1)/2 ≤ 568711 := m_mono m 1066 h_m_52
  have h_pc_M_52 : Nat.primeCounting 568711 = 46720 := pc_thm_568711
  have h_pc_K_prev_52 : Nat.primeCounting 42230 = 4416 := pc_thm_42230
  have h_k_53 : k ≥ 206 := staircase_step_K_direct k m 51156 568711 42230 46720 4416 206 heq h_m_mono_52 h_pc_M_52 h_pc_K_prev_52 rfl (by decide)
  have h_pc_K_next_52 : Nat.primeCounting 42642 = 4456 := pc_thm_42642
  have h_pc_M_next_val_52 : Nat.primeCounting 568711 = 46720 := pc_thm_568711
  have h_m_53 : m ≤ 1065 := staircase_step_M_direct k m 51156 42642 568711 4456 46720 1065 heq (k_mono 206 k h_k_53) h_pc_K_next_52 h_pc_M_next_val_52 rfl (by decide)
  -- Step 53: k >= 206, m <= 1065 => k >= 208
  have h_m_mono_53 : m*(m+1)/2 ≤ 567645 := m_mono m 1065 h_m_53
  have h_pc_M_53 : Nat.primeCounting 567645 = 46636 := pc_thm_567645
  have h_pc_K_prev_53 : Nat.primeCounting 43056 = 4500 := pc_thm_43056
  have h_k_54 : k ≥ 208 := staircase_step_K_direct k m 51156 567645 43056 46636 4500 208 heq h_m_mono_53 h_pc_M_53 h_pc_K_prev_53 rfl (by decide)
  have h_pc_K_next_53 : Nat.primeCounting 43472 = 4531 := pc_thm_43472
  have h_pc_M_next_val_53 : Nat.primeCounting 567645 = 46636 := pc_thm_567645
  have h_m_54 : m ≤ 1064 := staircase_step_M_direct k m 51156 43472 567645 4531 46636 1064 heq (k_mono 208 k h_k_54) h_pc_K_next_53 h_pc_M_next_val_53 rfl (by decide)
  -- Step 54: k >= 208, m <= 1064 => k >= 210
  have h_m_mono_54 : m*(m+1)/2 ≤ 566580 := m_mono m 1064 h_m_54
  have h_pc_M_54 : Nat.primeCounting 566580 = 46566 := pc_thm_566580
  have h_pc_K_prev_54 : Nat.primeCounting 43890 = 4567 := pc_thm_43890
  have h_k_55 : k ≥ 210 := staircase_step_K_direct k m 51156 566580 43890 46566 4567 210 heq h_m_mono_54 h_pc_M_54 h_pc_K_prev_54 rfl (by decide)
  have h_pc_K_next_54 : Nat.primeCounting 44310 = 4612 := pc_thm_44310
  have h_pc_M_next_val_54 : Nat.primeCounting 566580 = 46566 := pc_thm_566580
  have h_m_55 : m ≤ 1063 := staircase_step_M_direct k m 51156 44310 566580 4612 46566 1063 heq (k_mono 210 k h_k_55) h_pc_K_next_54 h_pc_M_next_val_54 rfl (by decide)
  -- Step 55: k >= 210, m <= 1063 => k >= 212
  have h_m_mono_55 : m*(m+1)/2 ≤ 565516 := m_mono m 1063 h_m_55
  have h_pc_M_55 : Nat.primeCounting 565516 = 46489 := pc_thm_565516
  have h_pc_K_prev_55 : Nat.primeCounting 44732 = 4649 := pc_thm_44732
  have h_k_56 : k ≥ 212 := staircase_step_K_direct k m 51156 565516 44732 46489 4649 212 heq h_m_mono_55 h_pc_M_55 h_pc_K_prev_55 rfl (by decide)
  have h_pc_K_next_55 : Nat.primeCounting 45156 = 4687 := pc_thm_45156
  have h_pc_M_next_val_55 : Nat.primeCounting 565516 = 46489 := pc_thm_565516
  have h_m_56 : m ≤ 1062 := staircase_step_M_direct k m 51156 45156 565516 4687 46489 1062 heq (k_mono 212 k h_k_56) h_pc_K_next_55 h_pc_M_next_val_55 rfl (by decide)
  -- Step 56: k >= 212, m <= 1062 => k >= 214
  have h_m_mono_56 : m*(m+1)/2 ≤ 564453 := m_mono m 1062 h_m_56
  have h_pc_M_56 : Nat.primeCounting 564453 = 46409 := pc_thm_564453
  have h_pc_K_prev_56 : Nat.primeCounting 45582 = 4724 := pc_thm_45582
  have h_k_57 : k ≥ 214 := staircase_step_K_direct k m 51156 564453 45582 46409 4724 214 heq h_m_mono_56 h_pc_M_56 h_pc_K_prev_56 rfl (by decide)
  have h_pc_K_next_56 : Nat.primeCounting 46010 = 4761 := pc_thm_46010
  have h_pc_M_next_val_56 : Nat.primeCounting 564453 = 46409 := pc_thm_564453
  have h_m_57 : m ≤ 1061 := staircase_step_M_direct k m 51156 46010 564453 4761 46409 1061 heq (k_mono 214 k h_k_57) h_pc_K_next_56 h_pc_M_next_val_56 rfl (by decide)
  -- Step 57: k >= 214, m <= 1061 => k >= 216
  have h_m_mono_57 : m*(m+1)/2 ≤ 563391 := m_mono m 1061 h_m_57
  have h_pc_M_57 : Nat.primeCounting 563391 = 46329 := pc_thm_563391
  have h_pc_K_prev_57 : Nat.primeCounting 46440 = 4798 := pc_thm_46440
  have h_k_58 : k ≥ 216 := staircase_step_K_direct k m 51156 563391 46440 46329 4798 216 heq h_m_mono_57 h_pc_M_57 h_pc_K_prev_57 rfl (by decide)
  have h_pc_K_next_57 : Nat.primeCounting 46872 = 4843 := pc_thm_46872
  have h_pc_M_next_val_57 : Nat.primeCounting 563391 = 46329 := pc_thm_563391
  have h_m_58 : m ≤ 1060 := staircase_step_M_direct k m 51156 46872 563391 4843 46329 1060 heq (k_mono 216 k h_k_58) h_pc_K_next_57 h_pc_M_next_val_57 rfl (by decide)
  -- Step 58: k >= 216, m <= 1060 => k >= 218
  have h_m_mono_58 : m*(m+1)/2 ≤ 562330 := m_mono m 1060 h_m_58
  have h_pc_M_58 : Nat.primeCounting 562330 = 46241 := pc_thm_562330
  have h_pc_K_prev_58 : Nat.primeCounting 47306 = 4878 := pc_thm_47306
  have h_k_59 : k ≥ 218 := staircase_step_K_direct k m 51156 562330 47306 46241 4878 218 heq h_m_mono_58 h_pc_M_58 h_pc_K_prev_58 rfl (by decide)
  have h_pc_K_next_58 : Nat.primeCounting 47742 = 4922 := pc_thm_47742
  have h_pc_M_next_val_58 : Nat.primeCounting 562330 = 46241 := pc_thm_562330
  have h_m_59 : m ≤ 1059 := staircase_step_M_direct k m 51156 47742 562330 4922 46241 1059 heq (k_mono 218 k h_k_59) h_pc_K_next_58 h_pc_M_next_val_58 rfl (by decide)
  -- Step 59: k >= 218, m <= 1059 => k >= 220
  have h_m_mono_59 : m*(m+1)/2 ≤ 561270 := m_mono m 1059 h_m_59
  have h_pc_M_59 : Nat.primeCounting 561270 = 46177 := pc_thm_561270
  have h_pc_K_prev_59 : Nat.primeCounting 48180 = 4960 := pc_thm_48180
  have h_k_60 : k ≥ 220 := staircase_step_K_direct k m 51156 561270 48180 46177 4960 220 heq h_m_mono_59 h_pc_M_59 h_pc_K_prev_59 rfl (by decide)
  have h_pc_K_next_59 : Nat.primeCounting 48620 = 5001 := pc_thm_48620
  have h_pc_M_next_val_59 : Nat.primeCounting 561270 = 46177 := pc_thm_561270
  have h_m_60 : m ≤ 1058 := staircase_step_M_direct k m 51156 48620 561270 5001 46177 1058 heq (k_mono 220 k h_k_60) h_pc_K_next_59 h_pc_M_next_val_59 rfl (by decide)
  -- Step 60: k >= 220, m <= 1058 => k >= 222
  have h_m_mono_60 : m*(m+1)/2 ≤ 560211 := m_mono m 1058 h_m_60
  have h_pc_M_60 : Nat.primeCounting 560211 = 46093 := pc_thm_560211
  have h_pc_K_prev_60 : Nat.primeCounting 49062 = 5043 := pc_thm_49062
  have h_k_61 : k ≥ 222 := staircase_step_K_direct k m 51156 560211 49062 46093 5043 222 heq h_m_mono_60 h_pc_M_60 h_pc_K_prev_60 rfl (by decide)
  have h_pc_K_next_60 : Nat.primeCounting 49506 = 5086 := pc_thm_49506
  have h_pc_M_next_val_60 : Nat.primeCounting 560211 = 46093 := pc_thm_560211
  have h_m_61 : m ≤ 1057 := staircase_step_M_direct k m 51156 49506 560211 5086 46093 1057 heq (k_mono 222 k h_k_61) h_pc_K_next_60 h_pc_M_next_val_60 rfl (by decide)
  exact ⟨h_k_61, h_m_61⟩

theorem staircase_part_4 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_61 : k ≥ 222) (h_m_61 : m ≤ 1057) : k ≥ 249 ∧ m ≤ 1042 := by
  -- Step 61: k >= 222, m <= 1057 => k >= 224
  have h_m_mono_61 : m*(m+1)/2 ≤ 559153 := m_mono m 1057 h_m_61
  have h_pc_M_61 : Nat.primeCounting 559153 = 46004 := pc_thm_559153
  have h_pc_K_prev_61 : Nat.primeCounting 49952 = 5129 := pc_thm_49952
  have h_k_62 : k ≥ 224 := staircase_step_K_direct k m 51156 559153 49952 46004 5129 224 heq h_m_mono_61 h_pc_M_61 h_pc_K_prev_61 rfl (by decide)
  have h_pc_K_next_61 : Nat.primeCounting 50400 = 5172 := pc_thm_50400
  have h_pc_M_next_val_61 : Nat.primeCounting 559153 = 46004 := pc_thm_559153
  have h_m_62 : m ≤ 1056 := staircase_step_M_direct k m 51156 50400 559153 5172 46004 1056 heq (k_mono 224 k h_k_62) h_pc_K_next_61 h_pc_M_next_val_61 rfl (by decide)
  -- Step 62: k >= 224, m <= 1056 => k >= 226
  have h_m_mono_62 : m*(m+1)/2 ≤ 558096 := m_mono m 1056 h_m_62
  have h_pc_M_62 : Nat.primeCounting 558096 = 45928 := pc_thm_558096
  have h_pc_K_prev_62 : Nat.primeCounting 50850 = 5208 := pc_thm_50850
  have h_k_63 : k ≥ 226 := staircase_step_K_direct k m 51156 558096 50850 45928 5208 226 heq h_m_mono_62 h_pc_M_62 h_pc_K_prev_62 rfl (by decide)
  have h_pc_K_next_62 : Nat.primeCounting 51302 = 5248 := pc_thm_51302
  have h_pc_M_next_val_62 : Nat.primeCounting 558096 = 45928 := pc_thm_558096
  have h_m_63 : m ≤ 1055 := staircase_step_M_direct k m 51156 51302 558096 5248 45928 1055 heq (k_mono 226 k h_k_63) h_pc_K_next_62 h_pc_M_next_val_62 rfl (by decide)
  -- Step 63: k >= 226, m <= 1055 => k >= 228
  have h_m_mono_63 : m*(m+1)/2 ≤ 557040 := m_mono m 1055 h_m_63
  have h_pc_M_63 : Nat.primeCounting 557040 = 45857 := pc_thm_557040
  have h_pc_K_prev_63 : Nat.primeCounting 51756 = 5295 := pc_thm_51756
  have h_k_64 : k ≥ 228 := staircase_step_K_direct k m 51156 557040 51756 45857 5295 228 heq h_m_mono_63 h_pc_M_63 h_pc_K_prev_63 rfl (by decide)
  have h_pc_K_next_63 : Nat.primeCounting 52212 = 5338 := pc_thm_52212
  have h_pc_M_next_val_63 : Nat.primeCounting 557040 = 45857 := pc_thm_557040
  have h_m_64 : m ≤ 1054 := staircase_step_M_direct k m 51156 52212 557040 5338 45857 1054 heq (k_mono 228 k h_k_64) h_pc_K_next_63 h_pc_M_next_val_63 rfl (by decide)
  -- Step 64: k >= 228, m <= 1054 => k >= 230
  have h_m_mono_64 : m*(m+1)/2 ≤ 555985 := m_mono m 1054 h_m_64
  have h_pc_M_64 : Nat.primeCounting 555985 = 45765 := pc_thm_555985
  have h_pc_K_prev_64 : Nat.primeCounting 52670 = 5376 := pc_thm_52670
  have h_k_65 : k ≥ 230 := staircase_step_K_direct k m 51156 555985 52670 45765 5376 230 heq h_m_mono_64 h_pc_M_64 h_pc_K_prev_64 rfl (by decide)
  have h_pc_K_next_64 : Nat.primeCounting 53130 = 5421 := pc_thm_53130
  have h_pc_M_next_val_64 : Nat.primeCounting 555985 = 45765 := pc_thm_555985
  have h_m_65 : m ≤ 1053 := staircase_step_M_direct k m 51156 53130 555985 5421 45765 1053 heq (k_mono 230 k h_k_65) h_pc_K_next_64 h_pc_M_next_val_64 rfl (by decide)
  -- Step 65: k >= 230, m <= 1053 => k >= 231
  have h_m_mono_65 : m*(m+1)/2 ≤ 554931 := m_mono m 1053 h_m_65
  have h_pc_M_65 : Nat.primeCounting 554931 = 45700 := pc_thm_554931
  have h_pc_K_prev_65 : Nat.primeCounting 53130 = 5421 := pc_thm_53130
  have h_k_66 : k ≥ 231 := staircase_step_K_direct k m 51156 554931 53130 45700 5421 231 heq h_m_mono_65 h_pc_M_65 h_pc_K_prev_65 rfl (by decide)
  have h_pc_K_next_65 : Nat.primeCounting 53592 = 5459 := pc_thm_53592
  have h_pc_M_next_val_65 : Nat.primeCounting 554931 = 45700 := pc_thm_554931
  have h_m_66 : m ≤ 1052 := staircase_step_M_direct k m 51156 53592 554931 5459 45700 1052 heq (k_mono 231 k h_k_66) h_pc_K_next_65 h_pc_M_next_val_65 rfl (by decide)
  -- Step 66: k >= 231, m <= 1052 => k >= 233
  have h_m_mono_66 : m*(m+1)/2 ≤ 553878 := m_mono m 1052 h_m_66
  have h_pc_M_66 : Nat.primeCounting 553878 = 45618 := pc_thm_553878
  have h_pc_K_prev_66 : Nat.primeCounting 54056 = 5505 := pc_thm_54056
  have h_k_67 : k ≥ 233 := staircase_step_K_direct k m 51156 553878 54056 45618 5505 233 heq h_m_mono_66 h_pc_M_66 h_pc_K_prev_66 rfl (by decide)
  have h_pc_K_next_66 : Nat.primeCounting 54522 = 5548 := pc_thm_54522
  have h_pc_M_next_val_66 : Nat.primeCounting 553878 = 45618 := pc_thm_553878
  have h_m_67 : m ≤ 1051 := staircase_step_M_direct k m 51156 54522 553878 5548 45618 1051 heq (k_mono 233 k h_k_67) h_pc_K_next_66 h_pc_M_next_val_66 rfl (by decide)
  -- Step 67: k >= 233, m <= 1051 => k >= 235
  have h_m_mono_67 : m*(m+1)/2 ≤ 552826 := m_mono m 1051 h_m_67
  have h_pc_M_67 : Nat.primeCounting 552826 = 45535 := pc_thm_552826
  have h_pc_K_prev_67 : Nat.primeCounting 54990 = 5590 := pc_thm_54990
  have h_k_68 : k ≥ 235 := staircase_step_K_direct k m 51156 552826 54990 45535 5590 235 heq h_m_mono_67 h_pc_M_67 h_pc_K_prev_67 rfl (by decide)
  have h_pc_K_next_67 : Nat.primeCounting 55460 = 5630 := pc_thm_55460
  have h_pc_M_next_val_67 : Nat.primeCounting 552826 = 45535 := pc_thm_552826
  have h_m_68 : m ≤ 1050 := staircase_step_M_direct k m 51156 55460 552826 5630 45535 1050 heq (k_mono 235 k h_k_68) h_pc_K_next_67 h_pc_M_next_val_67 rfl (by decide)
  -- Step 68: k >= 235, m <= 1050 => k >= 237
  have h_m_mono_68 : m*(m+1)/2 ≤ 551775 := m_mono m 1050 h_m_68
  have h_pc_M_68 : Nat.primeCounting 551775 = 45461 := pc_thm_551775
  have h_pc_K_prev_68 : Nat.primeCounting 55932 = 5678 := pc_thm_55932
  have h_k_69 : k ≥ 237 := staircase_step_K_direct k m 51156 551775 55932 45461 5678 237 heq h_m_mono_68 h_pc_M_68 h_pc_K_prev_68 rfl (by decide)
  have h_pc_K_next_68 : Nat.primeCounting 56406 = 5718 := pc_thm_56406
  have h_pc_M_next_val_68 : Nat.primeCounting 551775 = 45461 := pc_thm_551775
  have h_m_69 : m ≤ 1049 := staircase_step_M_direct k m 51156 56406 551775 5718 45461 1049 heq (k_mono 237 k h_k_69) h_pc_K_next_68 h_pc_M_next_val_68 rfl (by decide)
  -- Step 69: k >= 237, m <= 1049 => k >= 239
  have h_m_mono_69 : m*(m+1)/2 ≤ 550725 := m_mono m 1049 h_m_69
  have h_pc_M_69 : Nat.primeCounting 550725 = 45379 := pc_thm_550725
  have h_pc_K_prev_69 : Nat.primeCounting 56882 = 5766 := pc_thm_56882
  have h_k_70 : k ≥ 239 := staircase_step_K_direct k m 51156 550725 56882 45379 5766 239 heq h_m_mono_69 h_pc_M_69 h_pc_K_prev_69 rfl (by decide)
  have h_pc_K_next_69 : Nat.primeCounting 57360 = 5816 := pc_thm_57360
  have h_pc_M_next_val_69 : Nat.primeCounting 550725 = 45379 := pc_thm_550725
  have h_m_70 : m ≤ 1048 := staircase_step_M_direct k m 51156 57360 550725 5816 45379 1048 heq (k_mono 239 k h_k_70) h_pc_K_next_69 h_pc_M_next_val_69 rfl (by decide)
  -- Step 70: k >= 239, m <= 1048 => k >= 240
  have h_m_mono_70 : m*(m+1)/2 ≤ 549676 := m_mono m 1048 h_m_70
  have h_pc_M_70 : Nat.primeCounting 549676 = 45298 := pc_thm_549676
  have h_pc_K_prev_70 : Nat.primeCounting 57360 = 5816 := pc_thm_57360
  have h_k_71 : k ≥ 240 := staircase_step_K_direct k m 51156 549676 57360 45298 5816 240 heq h_m_mono_70 h_pc_M_70 h_pc_K_prev_70 rfl (by decide)
  have h_pc_K_next_70 : Nat.primeCounting 57840 = 5860 := pc_thm_57840
  have h_pc_M_next_val_70 : Nat.primeCounting 549676 = 45298 := pc_thm_549676
  have h_m_71 : m ≤ 1047 := staircase_step_M_direct k m 51156 57840 549676 5860 45298 1047 heq (k_mono 240 k h_k_71) h_pc_K_next_70 h_pc_M_next_val_70 rfl (by decide)
  -- Step 71: k >= 240, m <= 1047 => k >= 242
  have h_m_mono_71 : m*(m+1)/2 ≤ 548628 := m_mono m 1047 h_m_71
  have h_pc_M_71 : Nat.primeCounting 548628 = 45214 := pc_thm_548628
  have h_pc_K_prev_71 : Nat.primeCounting 58322 = 5905 := pc_thm_58322
  have h_k_72 : k ≥ 242 := staircase_step_K_direct k m 51156 548628 58322 45214 5905 242 heq h_m_mono_71 h_pc_M_71 h_pc_K_prev_71 rfl (by decide)
  have h_pc_K_next_71 : Nat.primeCounting 58806 = 5948 := pc_thm_58806
  have h_pc_M_next_val_71 : Nat.primeCounting 548628 = 45214 := pc_thm_548628
  have h_m_72 : m ≤ 1046 := staircase_step_M_direct k m 51156 58806 548628 5948 45214 1046 heq (k_mono 242 k h_k_72) h_pc_K_next_71 h_pc_M_next_val_71 rfl (by decide)
  -- Step 72: k >= 242, m <= 1046 => k >= 244
  have h_m_mono_72 : m*(m+1)/2 ≤ 547581 := m_mono m 1046 h_m_72
  have h_pc_M_72 : Nat.primeCounting 547581 = 45136 := pc_thm_547581
  have h_pc_K_prev_72 : Nat.primeCounting 59292 = 5995 := pc_thm_59292
  have h_k_73 : k ≥ 244 := staircase_step_K_direct k m 51156 547581 59292 45136 5995 244 heq h_m_mono_72 h_pc_M_72 h_pc_K_prev_72 rfl (by decide)
  have h_pc_K_next_72 : Nat.primeCounting 59780 = 6043 := pc_thm_59780
  have h_pc_M_next_val_72 : Nat.primeCounting 547581 = 45136 := pc_thm_547581
  have h_m_73 : m ≤ 1045 := staircase_step_M_direct k m 51156 59780 547581 6043 45136 1045 heq (k_mono 244 k h_k_73) h_pc_K_next_72 h_pc_M_next_val_72 rfl (by decide)
  -- Step 73: k >= 244, m <= 1045 => k >= 246
  have h_m_mono_73 : m*(m+1)/2 ≤ 546535 := m_mono m 1045 h_m_73
  have h_pc_M_73 : Nat.primeCounting 546535 = 45058 := pc_thm_546535
  have h_pc_K_prev_73 : Nat.primeCounting 60270 = 6082 := pc_thm_60270
  have h_k_74 : k ≥ 246 := staircase_step_K_direct k m 51156 546535 60270 45058 6082 246 heq h_m_mono_73 h_pc_M_73 h_pc_K_prev_73 rfl (by decide)
  have h_pc_K_next_73 : Nat.primeCounting 60762 = 6125 := pc_thm_60762
  have h_pc_M_next_val_73 : Nat.primeCounting 546535 = 45058 := pc_thm_546535
  have h_m_74 : m ≤ 1044 := staircase_step_M_direct k m 51156 60762 546535 6125 45058 1044 heq (k_mono 246 k h_k_74) h_pc_K_next_73 h_pc_M_next_val_73 rfl (by decide)
  -- Step 74: k >= 246, m <= 1044 => k >= 248
  have h_m_mono_74 : m*(m+1)/2 ≤ 545490 := m_mono m 1044 h_m_74
  have h_pc_M_74 : Nat.primeCounting 545490 = 44980 := pc_thm_545490
  have h_pc_K_prev_74 : Nat.primeCounting 61256 = 6164 := pc_thm_61256
  have h_k_75 : k ≥ 248 := staircase_step_K_direct k m 51156 545490 61256 44980 6164 248 heq h_m_mono_74 h_pc_M_74 h_pc_K_prev_74 rfl (by decide)
  have h_pc_K_next_74 : Nat.primeCounting 61752 = 6213 := pc_thm_61752
  have h_pc_M_next_val_74 : Nat.primeCounting 545490 = 44980 := pc_thm_545490
  have h_m_75 : m ≤ 1043 := staircase_step_M_direct k m 51156 61752 545490 6213 44980 1043 heq (k_mono 248 k h_k_75) h_pc_K_next_74 h_pc_M_next_val_74 rfl (by decide)
  -- Step 75: k >= 248, m <= 1043 => k >= 249
  have h_m_mono_75 : m*(m+1)/2 ≤ 544446 := m_mono m 1043 h_m_75
  have h_pc_M_75 : Nat.primeCounting 544446 = 44908 := pc_thm_544446
  have h_pc_K_prev_75 : Nat.primeCounting 61752 = 6213 := pc_thm_61752
  have h_k_76 : k ≥ 249 := staircase_step_K_direct k m 51156 544446 61752 44908 6213 249 heq h_m_mono_75 h_pc_M_75 h_pc_K_prev_75 rfl (by decide)
  have h_pc_K_next_75 : Nat.primeCounting 62250 = 6256 := pc_thm_62250
  have h_pc_M_next_val_75 : Nat.primeCounting 544446 = 44908 := pc_thm_544446
  have h_m_76 : m ≤ 1042 := staircase_step_M_direct k m 51156 62250 544446 6256 44908 1042 heq (k_mono 249 k h_k_76) h_pc_K_next_75 h_pc_M_next_val_75 rfl (by decide)
  exact ⟨h_k_76, h_m_76⟩

theorem staircase_part_5 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_76 : k ≥ 249) (h_m_76 : m ≤ 1042) : k ≥ 274 ∧ m ≤ 1027 := by
  -- Step 76: k >= 249, m <= 1042 => k >= 251
  have h_m_mono_76 : m*(m+1)/2 ≤ 543403 := m_mono m 1042 h_m_76
  have h_pc_M_76 : Nat.primeCounting 543403 = 44835 := pc_thm_543403
  have h_pc_K_prev_76 : Nat.primeCounting 62750 = 6297 := pc_thm_62750
  have h_k_77 : k ≥ 251 := staircase_step_K_direct k m 51156 543403 62750 44835 6297 251 heq h_m_mono_76 h_pc_M_76 h_pc_K_prev_76 rfl (by decide)
  have h_pc_K_next_76 : Nat.primeCounting 63252 = 6338 := pc_thm_63252
  have h_pc_M_next_val_76 : Nat.primeCounting 543403 = 44835 := pc_thm_543403
  have h_m_77 : m ≤ 1041 := staircase_step_M_direct k m 51156 63252 543403 6338 44835 1041 heq (k_mono 251 k h_k_77) h_pc_K_next_76 h_pc_M_next_val_76 rfl (by decide)
  -- Step 77: k >= 251, m <= 1041 => k >= 253
  have h_m_mono_77 : m*(m+1)/2 ≤ 542361 := m_mono m 1041 h_m_77
  have h_pc_M_77 : Nat.primeCounting 542361 = 44753 := pc_thm_542361
  have h_pc_K_prev_77 : Nat.primeCounting 63756 = 6393 := pc_thm_63756
  have h_k_78 : k ≥ 253 := staircase_step_K_direct k m 51156 542361 63756 44753 6393 253 heq h_m_mono_77 h_pc_M_77 h_pc_K_prev_77 rfl (by decide)
  have h_pc_K_next_77 : Nat.primeCounting 64262 = 6434 := pc_thm_64262
  have h_pc_M_next_val_77 : Nat.primeCounting 542361 = 44753 := pc_thm_542361
  have h_m_78 : m ≤ 1040 := staircase_step_M_direct k m 51156 64262 542361 6434 44753 1040 heq (k_mono 253 k h_k_78) h_pc_K_next_77 h_pc_M_next_val_77 rfl (by decide)
  -- Step 78: k >= 253, m <= 1040 => k >= 255
  have h_m_mono_78 : m*(m+1)/2 ≤ 541320 := m_mono m 1040 h_m_78
  have h_pc_M_78 : Nat.primeCounting 541320 = 44668 := pc_thm_541320
  have h_pc_K_prev_78 : Nat.primeCounting 64770 = 6474 := pc_thm_64770
  have h_k_79 : k ≥ 255 := staircase_step_K_direct k m 51156 541320 64770 44668 6474 255 heq h_m_mono_78 h_pc_M_78 h_pc_K_prev_78 rfl (by decide)
  have h_pc_K_next_78 : Nat.primeCounting 65280 = 6521 := pc_thm_65280
  have h_pc_M_next_val_78 : Nat.primeCounting 541320 = 44668 := pc_thm_541320
  have h_m_79 : m ≤ 1039 := staircase_step_M_direct k m 51156 65280 541320 6521 44668 1039 heq (k_mono 255 k h_k_79) h_pc_K_next_78 h_pc_M_next_val_78 rfl (by decide)
  -- Step 79: k >= 255, m <= 1039 => k >= 256
  have h_m_mono_79 : m*(m+1)/2 ≤ 540280 := m_mono m 1039 h_m_79
  have h_pc_M_79 : Nat.primeCounting 540280 = 44592 := pc_thm_540280
  have h_pc_K_prev_79 : Nat.primeCounting 65280 = 6521 := pc_thm_65280
  have h_k_80 : k ≥ 256 := staircase_step_K_direct k m 51156 540280 65280 44592 6521 256 heq h_m_mono_79 h_pc_M_79 h_pc_K_prev_79 rfl (by decide)
  have h_pc_K_next_79 : Nat.primeCounting 65792 = 6572 := pc_thm_65792
  have h_pc_M_next_val_79 : Nat.primeCounting 540280 = 44592 := pc_thm_540280
  have h_m_80 : m ≤ 1038 := staircase_step_M_direct k m 51156 65792 540280 6572 44592 1038 heq (k_mono 256 k h_k_80) h_pc_K_next_79 h_pc_M_next_val_79 rfl (by decide)
  -- Step 80: k >= 256, m <= 1038 => k >= 258
  have h_m_mono_80 : m*(m+1)/2 ≤ 539241 := m_mono m 1038 h_m_80
  have h_pc_M_80 : Nat.primeCounting 539241 = 44521 := pc_thm_539241
  have h_pc_K_prev_80 : Nat.primeCounting 66306 = 6613 := pc_thm_66306
  have h_k_81 : k ≥ 258 := staircase_step_K_direct k m 51156 539241 66306 44521 6613 258 heq h_m_mono_80 h_pc_M_80 h_pc_K_prev_80 rfl (by decide)
  have h_pc_K_next_80 : Nat.primeCounting 66822 = 6659 := pc_thm_66822
  have h_pc_M_next_val_80 : Nat.primeCounting 539241 = 44521 := pc_thm_539241
  have h_m_81 : m ≤ 1037 := staircase_step_M_direct k m 51156 66822 539241 6659 44521 1037 heq (k_mono 258 k h_k_81) h_pc_K_next_80 h_pc_M_next_val_80 rfl (by decide)
  -- Step 81: k >= 258, m <= 1037 => k >= 260
  have h_m_mono_81 : m*(m+1)/2 ≤ 538203 := m_mono m 1037 h_m_81
  have h_pc_M_81 : Nat.primeCounting 538203 = 44441 := pc_thm_538203
  have h_pc_K_prev_81 : Nat.primeCounting 67340 = 6707 := pc_thm_67340
  have h_k_82 : k ≥ 260 := staircase_step_K_direct k m 51156 538203 67340 44441 6707 260 heq h_m_mono_81 h_pc_M_81 h_pc_K_prev_81 rfl (by decide)
  have h_pc_K_next_81 : Nat.primeCounting 67860 = 6759 := pc_thm_67860
  have h_pc_M_next_val_81 : Nat.primeCounting 538203 = 44441 := pc_thm_538203
  have h_m_82 : m ≤ 1036 := staircase_step_M_direct k m 51156 67860 538203 6759 44441 1036 heq (k_mono 260 k h_k_82) h_pc_K_next_81 h_pc_M_next_val_81 rfl (by decide)
  -- Step 82: k >= 260, m <= 1036 => k >= 261
  have h_m_mono_82 : m*(m+1)/2 ≤ 537166 := m_mono m 1036 h_m_82
  have h_pc_M_82 : Nat.primeCounting 537166 = 44371 := pc_thm_537166
  have h_pc_K_prev_82 : Nat.primeCounting 67860 = 6759 := pc_thm_67860
  have h_k_83 : k ≥ 261 := staircase_step_K_direct k m 51156 537166 67860 44371 6759 261 heq h_m_mono_82 h_pc_M_82 h_pc_K_prev_82 rfl (by decide)
  have h_pc_K_next_82 : Nat.primeCounting 68382 = 6800 := pc_thm_68382
  have h_pc_M_next_val_82 : Nat.primeCounting 537166 = 44371 := pc_thm_537166
  have h_m_83 : m ≤ 1035 := staircase_step_M_direct k m 51156 68382 537166 6800 44371 1035 heq (k_mono 261 k h_k_83) h_pc_K_next_82 h_pc_M_next_val_82 rfl (by decide)
  -- Step 83: k >= 261, m <= 1035 => k >= 263
  have h_m_mono_83 : m*(m+1)/2 ≤ 536130 := m_mono m 1035 h_m_83
  have h_pc_M_83 : Nat.primeCounting 536130 = 44279 := pc_thm_536130
  have h_pc_K_prev_83 : Nat.primeCounting 68906 = 6848 := pc_thm_68906
  have h_k_84 : k ≥ 263 := staircase_step_K_direct k m 51156 536130 68906 44279 6848 263 heq h_m_mono_83 h_pc_M_83 h_pc_K_prev_83 rfl (by decide)
  have h_pc_K_next_83 : Nat.primeCounting 69432 = 6892 := pc_thm_69432
  have h_pc_M_next_val_83 : Nat.primeCounting 536130 = 44279 := pc_thm_536130
  have h_m_84 : m ≤ 1034 := staircase_step_M_direct k m 51156 69432 536130 6892 44279 1034 heq (k_mono 263 k h_k_84) h_pc_K_next_83 h_pc_M_next_val_83 rfl (by decide)
  -- Step 84: k >= 263, m <= 1034 => k >= 265
  have h_m_mono_84 : m*(m+1)/2 ≤ 535095 := m_mono m 1034 h_m_84
  have h_pc_M_84 : Nat.primeCounting 535095 = 44203 := pc_thm_535095
  have h_pc_K_prev_84 : Nat.primeCounting 69960 = 6933 := pc_thm_69960
  have h_k_85 : k ≥ 265 := staircase_step_K_direct k m 51156 535095 69960 44203 6933 265 heq h_m_mono_84 h_pc_M_84 h_pc_K_prev_84 rfl (by decide)
  have h_pc_K_next_84 : Nat.primeCounting 70490 = 6985 := pc_thm_70490
  have h_pc_M_next_val_84 : Nat.primeCounting 535095 = 44203 := pc_thm_535095
  have h_m_85 : m ≤ 1033 := staircase_step_M_direct k m 51156 70490 535095 6985 44203 1033 heq (k_mono 265 k h_k_85) h_pc_K_next_84 h_pc_M_next_val_84 rfl (by decide)
  -- Step 85: k >= 265, m <= 1033 => k >= 266
  have h_m_mono_85 : m*(m+1)/2 ≤ 534061 := m_mono m 1033 h_m_85
  have h_pc_M_85 : Nat.primeCounting 534061 = 44134 := pc_thm_534061
  have h_pc_K_prev_85 : Nat.primeCounting 70490 = 6985 := pc_thm_70490
  have h_k_86 : k ≥ 266 := staircase_step_K_direct k m 51156 534061 70490 44134 6985 266 heq h_m_mono_85 h_pc_M_85 h_pc_K_prev_85 rfl (by decide)
  have h_pc_K_next_85 : Nat.primeCounting 71022 = 7034 := pc_thm_71022
  have h_pc_M_next_val_85 : Nat.primeCounting 534061 = 44134 := pc_thm_534061
  have h_m_86 : m ≤ 1032 := staircase_step_M_direct k m 51156 71022 534061 7034 44134 1032 heq (k_mono 266 k h_k_86) h_pc_K_next_85 h_pc_M_next_val_85 rfl (by decide)
  -- Step 86: k >= 266, m <= 1032 => k >= 268
  have h_m_mono_86 : m*(m+1)/2 ≤ 533028 := m_mono m 1032 h_m_86
  have h_pc_M_86 : Nat.primeCounting 533028 = 44055 := pc_thm_533028
  have h_pc_K_prev_86 : Nat.primeCounting 71556 = 7087 := pc_thm_71556
  have h_k_87 : k ≥ 268 := staircase_step_K_direct k m 51156 533028 71556 44055 7087 268 heq h_m_mono_86 h_pc_M_86 h_pc_K_prev_86 rfl (by decide)
  have h_pc_K_next_86 : Nat.primeCounting 72092 = 7137 := pc_thm_72092
  have h_pc_M_next_val_86 : Nat.primeCounting 533028 = 44055 := pc_thm_533028
  have h_m_87 : m ≤ 1031 := staircase_step_M_direct k m 51156 72092 533028 7137 44055 1031 heq (k_mono 268 k h_k_87) h_pc_K_next_86 h_pc_M_next_val_86 rfl (by decide)
  -- Step 87: k >= 268, m <= 1031 => k >= 270
  have h_m_mono_87 : m*(m+1)/2 ≤ 531996 := m_mono m 1031 h_m_87
  have h_pc_M_87 : Nat.primeCounting 531996 = 43972 := pc_thm_531996
  have h_pc_K_prev_87 : Nat.primeCounting 72630 = 7181 := pc_thm_72630
  have h_k_88 : k ≥ 270 := staircase_step_K_direct k m 51156 531996 72630 43972 7181 270 heq h_m_mono_87 h_pc_M_87 h_pc_K_prev_87 rfl (by decide)
  have h_pc_K_next_87 : Nat.primeCounting 73170 = 7232 := pc_thm_73170
  have h_pc_M_next_val_87 : Nat.primeCounting 531996 = 43972 := pc_thm_531996
  have h_m_88 : m ≤ 1030 := staircase_step_M_direct k m 51156 73170 531996 7232 43972 1030 heq (k_mono 270 k h_k_88) h_pc_K_next_87 h_pc_M_next_val_87 rfl (by decide)
  -- Step 88: k >= 270, m <= 1030 => k >= 271
  have h_m_mono_88 : m*(m+1)/2 ≤ 530965 := m_mono m 1030 h_m_88
  have h_pc_M_88 : Nat.primeCounting 530965 = 43901 := pc_thm_530965
  have h_pc_K_prev_88 : Nat.primeCounting 73170 = 7232 := pc_thm_73170
  have h_k_89 : k ≥ 271 := staircase_step_K_direct k m 51156 530965 73170 43901 7232 271 heq h_m_mono_88 h_pc_M_88 h_pc_K_prev_88 rfl (by decide)
  have h_pc_K_next_88 : Nat.primeCounting 73712 = 7279 := pc_thm_73712
  have h_pc_M_next_val_88 : Nat.primeCounting 530965 = 43901 := pc_thm_530965
  have h_m_89 : m ≤ 1029 := staircase_step_M_direct k m 51156 73712 530965 7279 43901 1029 heq (k_mono 271 k h_k_89) h_pc_K_next_88 h_pc_M_next_val_88 rfl (by decide)
  -- Step 89: k >= 271, m <= 1029 => k >= 273
  have h_m_mono_89 : m*(m+1)/2 ≤ 529935 := m_mono m 1029 h_m_89
  have h_pc_M_89 : Nat.primeCounting 529935 = 43817 := pc_thm_529935
  have h_pc_K_prev_89 : Nat.primeCounting 74256 = 7325 := pc_thm_74256
  have h_k_90 : k ≥ 273 := staircase_step_K_direct k m 51156 529935 74256 43817 7325 273 heq h_m_mono_89 h_pc_M_89 h_pc_K_prev_89 rfl (by decide)
  have h_pc_K_next_89 : Nat.primeCounting 74802 = 7376 := pc_thm_74802
  have h_pc_M_next_val_89 : Nat.primeCounting 529935 = 43817 := pc_thm_529935
  have h_m_90 : m ≤ 1028 := staircase_step_M_direct k m 51156 74802 529935 7376 43817 1028 heq (k_mono 273 k h_k_90) h_pc_K_next_89 h_pc_M_next_val_89 rfl (by decide)
  -- Step 90: k >= 273, m <= 1028 => k >= 274
  have h_m_mono_90 : m*(m+1)/2 ≤ 528906 := m_mono m 1028 h_m_90
  have h_pc_M_90 : Nat.primeCounting 528906 = 43740 := pc_thm_528906
  have h_pc_K_prev_90 : Nat.primeCounting 74802 = 7376 := pc_thm_74802
  have h_k_91 : k ≥ 274 := staircase_step_K_direct k m 51156 528906 74802 43740 7376 274 heq h_m_mono_90 h_pc_M_90 h_pc_K_prev_90 rfl (by decide)
  have h_pc_K_next_90 : Nat.primeCounting 75350 = 7424 := pc_thm_75350
  have h_pc_M_next_val_90 : Nat.primeCounting 528906 = 43740 := pc_thm_528906
  have h_m_91 : m ≤ 1027 := staircase_step_M_direct k m 51156 75350 528906 7424 43740 1027 heq (k_mono 274 k h_k_91) h_pc_K_next_90 h_pc_M_next_val_90 rfl (by decide)
  exact ⟨h_k_91, h_m_91⟩

theorem staircase_part_6 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_91 : k ≥ 274) (h_m_91 : m ≤ 1027) : k ≥ 298 ∧ m ≤ 1012 := by
  -- Step 91: k >= 274, m <= 1027 => k >= 276
  have h_m_mono_91 : m*(m+1)/2 ≤ 527878 := m_mono m 1027 h_m_91
  have h_pc_M_91 : Nat.primeCounting 527878 = 43667 := pc_thm_527878
  have h_pc_K_prev_91 : Nat.primeCounting 75900 = 7474 := pc_thm_75900
  have h_k_92 : k ≥ 276 := staircase_step_K_direct k m 51156 527878 75900 43667 7474 276 heq h_m_mono_91 h_pc_M_91 h_pc_K_prev_91 rfl (by decide)
  have h_pc_K_next_91 : Nat.primeCounting 76452 = 7520 := pc_thm_76452
  have h_pc_M_next_val_91 : Nat.primeCounting 527878 = 43667 := pc_thm_527878
  have h_m_92 : m ≤ 1026 := staircase_step_M_direct k m 51156 76452 527878 7520 43667 1026 heq (k_mono 276 k h_k_92) h_pc_K_next_91 h_pc_M_next_val_91 rfl (by decide)
  -- Step 92: k >= 276, m <= 1026 => k >= 277
  have h_m_mono_92 : m*(m+1)/2 ≤ 526851 := m_mono m 1026 h_m_92
  have h_pc_M_92 : Nat.primeCounting 526851 = 43592 := pc_thm_526851
  have h_pc_K_prev_92 : Nat.primeCounting 76452 = 7520 := pc_thm_76452
  have h_k_93 : k ≥ 277 := staircase_step_K_direct k m 51156 526851 76452 43592 7520 277 heq h_m_mono_92 h_pc_M_92 h_pc_K_prev_92 rfl (by decide)
  have h_pc_K_next_92 : Nat.primeCounting 77006 = 7568 := pc_thm_77006
  have h_pc_M_next_val_92 : Nat.primeCounting 526851 = 43592 := pc_thm_526851
  have h_m_93 : m ≤ 1025 := staircase_step_M_direct k m 51156 77006 526851 7568 43592 1025 heq (k_mono 277 k h_k_93) h_pc_K_next_92 h_pc_M_next_val_92 rfl (by decide)
  -- Step 93: k >= 277, m <= 1025 => k >= 279
  have h_m_mono_93 : m*(m+1)/2 ≤ 525825 := m_mono m 1025 h_m_93
  have h_pc_M_93 : Nat.primeCounting 525825 = 43507 := pc_thm_525825
  have h_pc_K_prev_93 : Nat.primeCounting 77562 = 7621 := pc_thm_77562
  have h_k_94 : k ≥ 279 := staircase_step_K_direct k m 51156 525825 77562 43507 7621 279 heq h_m_mono_93 h_pc_M_93 h_pc_K_prev_93 rfl (by decide)
  have h_pc_K_next_93 : Nat.primeCounting 78120 = 7670 := pc_thm_78120
  have h_pc_M_next_val_93 : Nat.primeCounting 525825 = 43507 := pc_thm_525825
  have h_m_94 : m ≤ 1024 := staircase_step_M_direct k m 51156 78120 525825 7670 43507 1024 heq (k_mono 279 k h_k_94) h_pc_K_next_93 h_pc_M_next_val_93 rfl (by decide)
  -- Step 94: k >= 279, m <= 1024 => k >= 281
  have h_m_mono_94 : m*(m+1)/2 ≤ 524800 := m_mono m 1024 h_m_94
  have h_pc_M_94 : Nat.primeCounting 524800 = 43419 := pc_thm_524800
  have h_pc_K_prev_94 : Nat.primeCounting 78680 = 7718 := pc_thm_78680
  have h_k_95 : k ≥ 281 := staircase_step_K_direct k m 51156 524800 78680 43419 7718 281 heq h_m_mono_94 h_pc_M_94 h_pc_K_prev_94 rfl (by decide)
  have h_pc_K_next_94 : Nat.primeCounting 79242 = 7766 := pc_thm_79242
  have h_pc_M_next_val_94 : Nat.primeCounting 524800 = 43419 := pc_thm_524800
  have h_m_95 : m ≤ 1023 := staircase_step_M_direct k m 51156 79242 524800 7766 43419 1023 heq (k_mono 281 k h_k_95) h_pc_K_next_94 h_pc_M_next_val_94 rfl (by decide)
  -- Step 95: k >= 281, m <= 1023 => k >= 282
  have h_m_mono_95 : m*(m+1)/2 ≤ 523776 := m_mono m 1023 h_m_95
  have h_pc_M_95 : Nat.primeCounting 523776 = 43350 := pc_thm_523776
  have h_pc_K_prev_95 : Nat.primeCounting 79242 = 7766 := pc_thm_79242
  have h_k_96 : k ≥ 282 := staircase_step_K_direct k m 51156 523776 79242 43350 7766 282 heq h_m_mono_95 h_pc_M_95 h_pc_K_prev_95 rfl (by decide)
  have h_pc_K_next_95 : Nat.primeCounting 79806 = 7814 := pc_thm_79806
  have h_pc_M_next_val_95 : Nat.primeCounting 523776 = 43350 := pc_thm_523776
  have h_m_96 : m ≤ 1022 := staircase_step_M_direct k m 51156 79806 523776 7814 43350 1022 heq (k_mono 282 k h_k_96) h_pc_K_next_95 h_pc_M_next_val_95 rfl (by decide)
  -- Step 96: k >= 282, m <= 1022 => k >= 284
  have h_m_mono_96 : m*(m+1)/2 ≤ 522753 := m_mono m 1022 h_m_96
  have h_pc_M_96 : Nat.primeCounting 522753 = 43276 := pc_thm_522753
  have h_pc_K_prev_96 : Nat.primeCounting 80372 = 7870 := pc_thm_80372
  have h_k_97 : k ≥ 284 := staircase_step_K_direct k m 51156 522753 80372 43276 7870 284 heq h_m_mono_96 h_pc_M_96 h_pc_K_prev_96 rfl (by decide)
  have h_pc_K_next_96 : Nat.primeCounting 80940 = 7922 := pc_thm_80940
  have h_pc_M_next_val_96 : Nat.primeCounting 522753 = 43276 := pc_thm_522753
  have h_m_97 : m ≤ 1021 := staircase_step_M_direct k m 51156 80940 522753 7922 43276 1021 heq (k_mono 284 k h_k_97) h_pc_K_next_96 h_pc_M_next_val_96 rfl (by decide)
  -- Step 97: k >= 284, m <= 1021 => k >= 285
  have h_m_mono_97 : m*(m+1)/2 ≤ 521731 := m_mono m 1021 h_m_97
  have h_pc_M_97 : Nat.primeCounting 521731 = 43194 := pc_thm_521731
  have h_pc_K_prev_97 : Nat.primeCounting 80940 = 7922 := pc_thm_80940
  have h_k_98 : k ≥ 285 := staircase_step_K_direct k m 51156 521731 80940 43194 7922 285 heq h_m_mono_97 h_pc_M_97 h_pc_K_prev_97 rfl (by decide)
  have h_pc_K_next_97 : Nat.primeCounting 81510 = 7971 := pc_thm_81510
  have h_pc_M_next_val_97 : Nat.primeCounting 521731 = 43194 := pc_thm_521731
  have h_m_98 : m ≤ 1020 := staircase_step_M_direct k m 51156 81510 521731 7971 43194 1020 heq (k_mono 285 k h_k_98) h_pc_K_next_97 h_pc_M_next_val_97 rfl (by decide)
  -- Step 98: k >= 285, m <= 1020 => k >= 287
  have h_m_mono_98 : m*(m+1)/2 ≤ 520710 := m_mono m 1020 h_m_98
  have h_pc_M_98 : Nat.primeCounting 520710 = 43114 := pc_thm_520710
  have h_pc_K_prev_98 : Nat.primeCounting 82082 = 8028 := pc_thm_82082
  have h_k_99 : k ≥ 287 := staircase_step_K_direct k m 51156 520710 82082 43114 8028 287 heq h_m_mono_98 h_pc_M_98 h_pc_K_prev_98 rfl (by decide)
  have h_pc_K_next_98 : Nat.primeCounting 82656 = 8080 := pc_thm_82656
  have h_pc_M_next_val_98 : Nat.primeCounting 520710 = 43114 := pc_thm_520710
  have h_m_99 : m ≤ 1019 := staircase_step_M_direct k m 51156 82656 520710 8080 43114 1019 heq (k_mono 287 k h_k_99) h_pc_K_next_98 h_pc_M_next_val_98 rfl (by decide)
  -- Step 99: k >= 287, m <= 1019 => k >= 288
  have h_m_mono_99 : m*(m+1)/2 ≤ 519690 := m_mono m 1019 h_m_99
  have h_pc_M_99 : Nat.primeCounting 519690 = 43037 := pc_thm_519690
  have h_pc_K_prev_99 : Nat.primeCounting 82656 = 8080 := pc_thm_82656
  have h_k_100 : k ≥ 288 := staircase_step_K_direct k m 51156 519690 82656 43037 8080 288 heq h_m_mono_99 h_pc_M_99 h_pc_K_prev_99 rfl (by decide)
  have h_pc_K_next_99 : Nat.primeCounting 83232 = 8126 := pc_thm_83232
  have h_pc_M_next_val_99 : Nat.primeCounting 519690 = 43037 := pc_thm_519690
  have h_m_100 : m ≤ 1018 := staircase_step_M_direct k m 51156 83232 519690 8126 43037 1018 heq (k_mono 288 k h_k_100) h_pc_K_next_99 h_pc_M_next_val_99 rfl (by decide)
  -- Step 100: k >= 288, m <= 1018 => k >= 290
  have h_m_mono_100 : m*(m+1)/2 ≤ 518671 := m_mono m 1018 h_m_100
  have h_pc_M_100 : Nat.primeCounting 518671 = 42956 := pc_thm_518671
  have h_pc_K_prev_100 : Nat.primeCounting 83810 = 8175 := pc_thm_83810
  have h_k_101 : k ≥ 290 := staircase_step_K_direct k m 51156 518671 83810 42956 8175 290 heq h_m_mono_100 h_pc_M_100 h_pc_K_prev_100 rfl (by decide)
  have h_pc_K_next_100 : Nat.primeCounting 84390 = 8224 := pc_thm_84390
  have h_pc_M_next_val_100 : Nat.primeCounting 518671 = 42956 := pc_thm_518671
  have h_m_101 : m ≤ 1017 := staircase_step_M_direct k m 51156 84390 518671 8224 42956 1017 heq (k_mono 290 k h_k_101) h_pc_K_next_100 h_pc_M_next_val_100 rfl (by decide)
  -- Step 101: k >= 290, m <= 1017 => k >= 291
  have h_m_mono_101 : m*(m+1)/2 ≤ 517653 := m_mono m 1017 h_m_101
  have h_pc_M_101 : Nat.primeCounting 517653 = 42885 := pc_thm_517653
  have h_pc_K_prev_101 : Nat.primeCounting 84390 = 8224 := pc_thm_84390
  have h_k_102 : k ≥ 291 := staircase_step_K_direct k m 51156 517653 84390 42885 8224 291 heq h_m_mono_101 h_pc_M_101 h_pc_K_prev_101 rfl (by decide)
  have h_pc_K_next_101 : Nat.primeCounting 84972 = 8274 := pc_thm_84972
  have h_pc_M_next_val_101 : Nat.primeCounting 517653 = 42885 := pc_thm_517653
  have h_m_102 : m ≤ 1016 := staircase_step_M_direct k m 51156 84972 517653 8274 42885 1016 heq (k_mono 291 k h_k_102) h_pc_K_next_101 h_pc_M_next_val_101 rfl (by decide)
  -- Step 102: k >= 291, m <= 1016 => k >= 293
  have h_m_mono_102 : m*(m+1)/2 ≤ 516636 := m_mono m 1016 h_m_102
  have h_pc_M_102 : Nat.primeCounting 516636 = 42794 := pc_thm_516636
  have h_pc_K_prev_102 : Nat.primeCounting 85556 = 8326 := pc_thm_85556
  have h_k_103 : k ≥ 293 := staircase_step_K_direct k m 51156 516636 85556 42794 8326 293 heq h_m_mono_102 h_pc_M_102 h_pc_K_prev_102 rfl (by decide)
  have h_pc_K_next_102 : Nat.primeCounting 86142 = 8374 := pc_thm_86142
  have h_pc_M_next_val_102 : Nat.primeCounting 516636 = 42794 := pc_thm_516636
  have h_m_103 : m ≤ 1015 := staircase_step_M_direct k m 51156 86142 516636 8374 42794 1015 heq (k_mono 293 k h_k_103) h_pc_K_next_102 h_pc_M_next_val_102 rfl (by decide)
  -- Step 103: k >= 293, m <= 1015 => k >= 295
  have h_m_mono_103 : m*(m+1)/2 ≤ 515620 := m_mono m 1015 h_m_103
  have h_pc_M_103 : Nat.primeCounting 515620 = 42707 := pc_thm_515620
  have h_pc_K_prev_103 : Nat.primeCounting 86730 = 8429 := pc_thm_86730
  have h_k_104 : k ≥ 295 := staircase_step_K_direct k m 51156 515620 86730 42707 8429 295 heq h_m_mono_103 h_pc_M_103 h_pc_K_prev_103 rfl (by decide)
  have h_pc_K_next_103 : Nat.primeCounting 87320 = 8479 := pc_thm_87320
  have h_pc_M_next_val_103 : Nat.primeCounting 515620 = 42707 := pc_thm_515620
  have h_m_104 : m ≤ 1014 := staircase_step_M_direct k m 51156 87320 515620 8479 42707 1014 heq (k_mono 295 k h_k_104) h_pc_K_next_103 h_pc_M_next_val_103 rfl (by decide)
  -- Step 104: k >= 295, m <= 1014 => k >= 296
  have h_m_mono_104 : m*(m+1)/2 ≤ 514605 := m_mono m 1014 h_m_104
  have h_pc_M_104 : Nat.primeCounting 514605 = 42640 := pc_thm_514605
  have h_pc_K_prev_104 : Nat.primeCounting 87320 = 8479 := pc_thm_87320
  have h_k_105 : k ≥ 296 := staircase_step_K_direct k m 51156 514605 87320 42640 8479 296 heq h_m_mono_104 h_pc_M_104 h_pc_K_prev_104 rfl (by decide)
  have h_pc_K_next_104 : Nat.primeCounting 87912 = 8535 := pc_thm_87912
  have h_pc_M_next_val_104 : Nat.primeCounting 514605 = 42640 := pc_thm_514605
  have h_m_105 : m ≤ 1013 := staircase_step_M_direct k m 51156 87912 514605 8535 42640 1013 heq (k_mono 296 k h_k_105) h_pc_K_next_104 h_pc_M_next_val_104 rfl (by decide)
  -- Step 105: k >= 296, m <= 1013 => k >= 298
  have h_m_mono_105 : m*(m+1)/2 ≤ 513591 := m_mono m 1013 h_m_105
  have h_pc_M_105 : Nat.primeCounting 513591 = 42562 := pc_thm_513591
  have h_pc_K_prev_105 : Nat.primeCounting 88506 = 8577 := pc_thm_88506
  have h_k_106 : k ≥ 298 := staircase_step_K_direct k m 51156 513591 88506 42562 8577 298 heq h_m_mono_105 h_pc_M_105 h_pc_K_prev_105 rfl (by decide)
  have h_pc_K_next_105 : Nat.primeCounting 89102 = 8631 := pc_thm_89102
  have h_pc_M_next_val_105 : Nat.primeCounting 513591 = 42562 := pc_thm_513591
  have h_m_106 : m ≤ 1012 := staircase_step_M_direct k m 51156 89102 513591 8631 42562 1012 heq (k_mono 298 k h_k_106) h_pc_K_next_105 h_pc_M_next_val_105 rfl (by decide)
  exact ⟨h_k_106, h_m_106⟩

theorem staircase_part_7 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_106 : k ≥ 298) (h_m_106 : m ≤ 1012) : k ≥ 319 ∧ m ≤ 997 := by
  -- Step 106: k >= 298, m <= 1012 => k >= 299
  have h_m_mono_106 : m*(m+1)/2 ≤ 512578 := m_mono m 1012 h_m_106
  have h_pc_M_106 : Nat.primeCounting 512578 = 42478 := pc_thm_512578
  have h_pc_K_prev_106 : Nat.primeCounting 89102 = 8631 := pc_thm_89102
  have h_k_107 : k ≥ 299 := staircase_step_K_direct k m 51156 512578 89102 42478 8631 299 heq h_m_mono_106 h_pc_M_106 h_pc_K_prev_106 rfl (by decide)
  have h_pc_K_next_106 : Nat.primeCounting 89700 = 8688 := pc_thm_89700
  have h_pc_M_next_val_106 : Nat.primeCounting 512578 = 42478 := pc_thm_512578
  have h_m_107 : m ≤ 1011 := staircase_step_M_direct k m 51156 89700 512578 8688 42478 1011 heq (k_mono 299 k h_k_107) h_pc_K_next_106 h_pc_M_next_val_106 rfl (by decide)
  -- Step 107: k >= 299, m <= 1011 => k >= 300
  have h_m_mono_107 : m*(m+1)/2 ≤ 511566 := m_mono m 1011 h_m_107
  have h_pc_M_107 : Nat.primeCounting 511566 = 42413 := pc_thm_511566
  have h_pc_K_prev_107 : Nat.primeCounting 89700 = 8688 := pc_thm_89700
  have h_k_108 : k ≥ 300 := staircase_step_K_direct k m 51156 511566 89700 42413 8688 300 heq h_m_mono_107 h_pc_M_107 h_pc_K_prev_107 rfl (by decide)
  have h_pc_K_next_107 : Nat.primeCounting 90300 = 8745 := pc_thm_90300
  have h_pc_M_next_val_107 : Nat.primeCounting 511566 = 42413 := pc_thm_511566
  have h_m_108 : m ≤ 1010 := staircase_step_M_direct k m 51156 90300 511566 8745 42413 1010 heq (k_mono 300 k h_k_108) h_pc_K_next_107 h_pc_M_next_val_107 rfl (by decide)
  -- Step 108: k >= 300, m <= 1010 => k >= 302
  have h_m_mono_108 : m*(m+1)/2 ≤ 510555 := m_mono m 1010 h_m_108
  have h_pc_M_108 : Nat.primeCounting 510555 = 42334 := pc_thm_510555
  have h_pc_K_prev_108 : Nat.primeCounting 90902 = 8793 := pc_thm_90902
  have h_k_109 : k ≥ 302 := staircase_step_K_direct k m 51156 510555 90902 42334 8793 302 heq h_m_mono_108 h_pc_M_108 h_pc_K_prev_108 rfl (by decide)
  have h_pc_K_next_108 : Nat.primeCounting 91506 = 8848 := pc_thm_91506
  have h_pc_M_next_val_108 : Nat.primeCounting 510555 = 42334 := pc_thm_510555
  have h_m_109 : m ≤ 1009 := staircase_step_M_direct k m 51156 91506 510555 8848 42334 1009 heq (k_mono 302 k h_k_109) h_pc_K_next_108 h_pc_M_next_val_108 rfl (by decide)
  -- Step 109: k >= 302, m <= 1009 => k >= 304
  have h_m_mono_109 : m*(m+1)/2 ≤ 509545 := m_mono m 1009 h_m_109
  have h_pc_M_109 : Nat.primeCounting 509545 = 42251 := pc_thm_509545
  have h_pc_K_prev_109 : Nat.primeCounting 92112 = 8896 := pc_thm_92112
  have h_k_110 : k ≥ 304 := staircase_step_K_direct k m 51156 509545 92112 42251 8896 304 heq h_m_mono_109 h_pc_M_109 h_pc_K_prev_109 rfl (by decide)
  have h_pc_K_next_109 : Nat.primeCounting 92720 = 8957 := pc_thm_92720
  have h_pc_M_next_val_109 : Nat.primeCounting 509545 = 42251 := pc_thm_509545
  have h_m_110 : m ≤ 1008 := staircase_step_M_direct k m 51156 92720 509545 8957 42251 1008 heq (k_mono 304 k h_k_110) h_pc_K_next_109 h_pc_M_next_val_109 rfl (by decide)
  -- Step 110: k >= 304, m <= 1008 => k >= 305
  have h_m_mono_110 : m*(m+1)/2 ≤ 508536 := m_mono m 1008 h_m_110
  have h_pc_M_110 : Nat.primeCounting 508536 = 42181 := pc_thm_508536
  have h_pc_K_prev_110 : Nat.primeCounting 92720 = 8957 := pc_thm_92720
  have h_k_111 : k ≥ 305 := staircase_step_K_direct k m 51156 508536 92720 42181 8957 305 heq h_m_mono_110 h_pc_M_110 h_pc_K_prev_110 rfl (by decide)
  have h_pc_K_next_110 : Nat.primeCounting 93330 = 9016 := pc_thm_93330
  have h_pc_M_next_val_110 : Nat.primeCounting 508536 = 42181 := pc_thm_508536
  have h_m_111 : m ≤ 1007 := staircase_step_M_direct k m 51156 93330 508536 9016 42181 1007 heq (k_mono 305 k h_k_111) h_pc_K_next_110 h_pc_M_next_val_110 rfl (by decide)
  -- Step 111: k >= 305, m <= 1007 => k >= 306
  have h_m_mono_111 : m*(m+1)/2 ≤ 507528 := m_mono m 1007 h_m_111
  have h_pc_M_111 : Nat.primeCounting 507528 = 42106 := pc_thm_507528
  have h_pc_K_prev_111 : Nat.primeCounting 93330 = 9016 := pc_thm_93330
  have h_k_112 : k ≥ 306 := staircase_step_K_direct k m 51156 507528 93330 42106 9016 306 heq h_m_mono_111 h_pc_M_111 h_pc_K_prev_111 rfl (by decide)
  have h_pc_K_next_111 : Nat.primeCounting 93942 = 9064 := pc_thm_93942
  have h_pc_M_next_val_111 : Nat.primeCounting 507528 = 42106 := pc_thm_507528
  have h_m_112 : m ≤ 1006 := staircase_step_M_direct k m 51156 93942 507528 9064 42106 1006 heq (k_mono 306 k h_k_112) h_pc_K_next_111 h_pc_M_next_val_111 rfl (by decide)
  -- Step 112: k >= 306, m <= 1006 => k >= 308
  have h_m_mono_112 : m*(m+1)/2 ≤ 506521 := m_mono m 1006 h_m_112
  have h_pc_M_112 : Nat.primeCounting 506521 = 42029 := pc_thm_506521
  have h_pc_K_prev_112 : Nat.primeCounting 94556 = 9119 := pc_thm_94556
  have h_k_113 : k ≥ 308 := staircase_step_K_direct k m 51156 506521 94556 42029 9119 308 heq h_m_mono_112 h_pc_M_112 h_pc_K_prev_112 rfl (by decide)
  have h_pc_K_next_112 : Nat.primeCounting 95172 = 9173 := pc_thm_95172
  have h_pc_M_next_val_112 : Nat.primeCounting 506521 = 42029 := pc_thm_506521
  have h_m_113 : m ≤ 1005 := staircase_step_M_direct k m 51156 95172 506521 9173 42029 1005 heq (k_mono 308 k h_k_113) h_pc_K_next_112 h_pc_M_next_val_112 rfl (by decide)
  -- Step 113: k >= 308, m <= 1005 => k >= 309
  have h_m_mono_113 : m*(m+1)/2 ≤ 505515 := m_mono m 1005 h_m_113
  have h_pc_M_113 : Nat.primeCounting 505515 = 41957 := pc_thm_505515
  have h_pc_K_prev_113 : Nat.primeCounting 95172 = 9173 := pc_thm_95172
  have h_k_114 : k ≥ 309 := staircase_step_K_direct k m 51156 505515 95172 41957 9173 309 heq h_m_mono_113 h_pc_M_113 h_pc_K_prev_113 rfl (by decide)
  have h_pc_K_next_113 : Nat.primeCounting 95790 = 9232 := pc_thm_95790
  have h_pc_M_next_val_113 : Nat.primeCounting 505515 = 41957 := pc_thm_505515
  have h_m_114 : m ≤ 1004 := staircase_step_M_direct k m 51156 95790 505515 9232 41957 1004 heq (k_mono 309 k h_k_114) h_pc_K_next_113 h_pc_M_next_val_113 rfl (by decide)
  -- Step 114: k >= 309, m <= 1004 => k >= 311
  have h_m_mono_114 : m*(m+1)/2 ≤ 504510 := m_mono m 1004 h_m_114
  have h_pc_M_114 : Nat.primeCounting 504510 = 41871 := pc_thm_504510
  have h_pc_K_prev_114 : Nat.primeCounting 96410 = 9284 := pc_thm_96410
  have h_k_115 : k ≥ 311 := staircase_step_K_direct k m 51156 504510 96410 41871 9284 311 heq h_m_mono_114 h_pc_M_114 h_pc_K_prev_114 rfl (by decide)
  have h_pc_K_next_114 : Nat.primeCounting 97032 = 9340 := pc_thm_97032
  have h_pc_M_next_val_114 : Nat.primeCounting 504510 = 41871 := pc_thm_504510
  have h_m_115 : m ≤ 1003 := staircase_step_M_direct k m 51156 97032 504510 9340 41871 1003 heq (k_mono 311 k h_k_115) h_pc_K_next_114 h_pc_M_next_val_114 rfl (by decide)
  -- Step 115: k >= 311, m <= 1003 => k >= 312
  have h_m_mono_115 : m*(m+1)/2 ≤ 503506 := m_mono m 1003 h_m_115
  have h_pc_M_115 : Nat.primeCounting 503506 = 41795 := pc_thm_503506
  have h_pc_K_prev_115 : Nat.primeCounting 97032 = 9340 := pc_thm_97032
  have h_k_116 : k ≥ 312 := staircase_step_K_direct k m 51156 503506 97032 41795 9340 312 heq h_m_mono_115 h_pc_M_115 h_pc_K_prev_115 rfl (by decide)
  have h_pc_K_next_115 : Nat.primeCounting 97656 = 9391 := pc_thm_97656
  have h_pc_M_next_val_115 : Nat.primeCounting 503506 = 41795 := pc_thm_503506
  have h_m_116 : m ≤ 1002 := staircase_step_M_direct k m 51156 97656 503506 9391 41795 1002 heq (k_mono 312 k h_k_116) h_pc_K_next_115 h_pc_M_next_val_115 rfl (by decide)
  -- Step 116: k >= 312, m <= 1002 => k >= 313
  have h_m_mono_116 : m*(m+1)/2 ≤ 502503 := m_mono m 1002 h_m_116
  have h_pc_M_116 : Nat.primeCounting 502503 = 41724 := pc_thm_502503
  have h_pc_K_prev_116 : Nat.primeCounting 97656 = 9391 := pc_thm_97656
  have h_k_117 : k ≥ 313 := staircase_step_K_direct k m 51156 502503 97656 41724 9391 313 heq h_m_mono_116 h_pc_M_116 h_pc_K_prev_116 rfl (by decide)
  have h_pc_K_next_116 : Nat.primeCounting 98282 = 9437 := pc_thm_98282
  have h_pc_M_next_val_116 : Nat.primeCounting 502503 = 41724 := pc_thm_502503
  have h_m_117 : m ≤ 1001 := staircase_step_M_direct k m 51156 98282 502503 9437 41724 1001 heq (k_mono 313 k h_k_117) h_pc_K_next_116 h_pc_M_next_val_116 rfl (by decide)
  -- Step 117: k >= 313, m <= 1001 => k >= 315
  have h_m_mono_117 : m*(m+1)/2 ≤ 501501 := m_mono m 1001 h_m_117
  have h_pc_M_117 : Nat.primeCounting 501501 = 41658 := pc_thm_501501
  have h_pc_K_prev_117 : Nat.primeCounting 98910 = 9495 := pc_thm_98910
  have h_k_118 : k ≥ 315 := staircase_step_K_direct k m 51156 501501 98910 41658 9495 315 heq h_m_mono_117 h_pc_M_117 h_pc_K_prev_117 rfl (by decide)
  have h_pc_K_next_117 : Nat.primeCounting 99540 = 9550 := pc_thm_99540
  have h_pc_M_next_val_117 : Nat.primeCounting 501501 = 41658 := pc_thm_501501
  have h_m_118 : m ≤ 1000 := staircase_step_M_direct k m 51156 99540 501501 9550 41658 1000 heq (k_mono 315 k h_k_118) h_pc_K_next_117 h_pc_M_next_val_117 rfl (by decide)
  -- Step 118: k >= 315, m <= 1000 => k >= 316
  have h_m_mono_118 : m*(m+1)/2 ≤ 500500 := m_mono m 1000 h_m_118
  have h_pc_M_118 : Nat.primeCounting 500500 = 41579 := pc_thm_500500
  have h_pc_K_prev_118 : Nat.primeCounting 99540 = 9550 := pc_thm_99540
  have h_k_119 : k ≥ 316 := staircase_step_K_direct k m 51156 500500 99540 41579 9550 316 heq h_m_mono_118 h_pc_M_118 h_pc_K_prev_118 rfl (by decide)
  have h_pc_K_next_118 : Nat.primeCounting 100172 = 9604 := pc_thm_100172
  have h_pc_M_next_val_118 : Nat.primeCounting 500500 = 41579 := pc_thm_500500
  have h_m_119 : m ≤ 999 := staircase_step_M_direct k m 51156 100172 500500 9604 41579 999 heq (k_mono 316 k h_k_119) h_pc_K_next_118 h_pc_M_next_val_118 rfl (by decide)
  -- Step 119: k >= 316, m <= 999 => k >= 318
  have h_m_mono_119 : m*(m+1)/2 ≤ 499500 := m_mono m 999 h_m_119
  have h_pc_M_119 : Nat.primeCounting 499500 = 41497 := pc_thm_499500
  have h_pc_K_prev_119 : Nat.primeCounting 100806 = 9658 := pc_thm_100806
  have h_k_120 : k ≥ 318 := staircase_step_K_direct k m 51156 499500 100806 41497 9658 318 heq h_m_mono_119 h_pc_M_119 h_pc_K_prev_119 rfl (by decide)
  have h_pc_K_next_119 : Nat.primeCounting 101442 = 9714 := pc_thm_101442
  have h_pc_M_next_val_119 : Nat.primeCounting 499500 = 41497 := pc_thm_499500
  have h_m_120 : m ≤ 998 := staircase_step_M_direct k m 51156 101442 499500 9714 41497 998 heq (k_mono 318 k h_k_120) h_pc_K_next_119 h_pc_M_next_val_119 rfl (by decide)
  -- Step 120: k >= 318, m <= 998 => k >= 319
  have h_m_mono_120 : m*(m+1)/2 ≤ 498501 := m_mono m 998 h_m_120
  have h_pc_M_120 : Nat.primeCounting 498501 = 41418 := pc_thm_498501
  have h_pc_K_prev_120 : Nat.primeCounting 101442 = 9714 := pc_thm_101442
  have h_k_121 : k ≥ 319 := staircase_step_K_direct k m 51156 498501 101442 41418 9714 319 heq h_m_mono_120 h_pc_M_120 h_pc_K_prev_120 rfl (by decide)
  have h_pc_K_next_120 : Nat.primeCounting 102080 = 9777 := pc_thm_102080
  have h_pc_M_next_val_120 : Nat.primeCounting 498501 = 41418 := pc_thm_498501
  have h_m_121 : m ≤ 997 := staircase_step_M_direct k m 51156 102080 498501 9777 41418 997 heq (k_mono 319 k h_k_121) h_pc_K_next_120 h_pc_M_next_val_120 rfl (by decide)
  exact ⟨h_k_121, h_m_121⟩

theorem staircase_part_8 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_121 : k ≥ 319) (h_m_121 : m ≤ 997) : k ≥ 339 ∧ m ≤ 982 := by
  -- Step 121: k >= 319, m <= 997 => k >= 320
  have h_m_mono_121 : m*(m+1)/2 ≤ 497503 := m_mono m 997 h_m_121
  have h_pc_M_121 : Nat.primeCounting 497503 = 41343 := pc_thm_497503
  have h_pc_K_prev_121 : Nat.primeCounting 102080 = 9777 := pc_thm_102080
  have h_k_122 : k ≥ 320 := staircase_step_K_direct k m 51156 497503 102080 41343 9777 320 heq h_m_mono_121 h_pc_M_121 h_pc_K_prev_121 rfl (by decide)
  have h_pc_K_next_121 : Nat.primeCounting 102720 = 9834 := pc_thm_102720
  have h_pc_M_next_val_121 : Nat.primeCounting 497503 = 41343 := pc_thm_497503
  have h_m_122 : m ≤ 996 := staircase_step_M_direct k m 51156 102720 497503 9834 41343 996 heq (k_mono 320 k h_k_122) h_pc_K_next_121 h_pc_M_next_val_121 rfl (by decide)
  -- Step 122: k >= 320, m <= 996 => k >= 322
  have h_m_mono_122 : m*(m+1)/2 ≤ 496506 := m_mono m 996 h_m_122
  have h_pc_M_122 : Nat.primeCounting 496506 = 41273 := pc_thm_496506
  have h_pc_K_prev_122 : Nat.primeCounting 103362 = 9879 := pc_thm_103362
  have h_k_123 : k ≥ 322 := staircase_step_K_direct k m 51156 496506 103362 41273 9879 322 heq h_m_mono_122 h_pc_M_122 h_pc_K_prev_122 rfl (by decide)
  have h_pc_K_next_122 : Nat.primeCounting 104006 = 9934 := pc_thm_104006
  have h_pc_M_next_val_122 : Nat.primeCounting 496506 = 41273 := pc_thm_496506
  have h_m_123 : m ≤ 995 := staircase_step_M_direct k m 51156 104006 496506 9934 41273 995 heq (k_mono 322 k h_k_123) h_pc_K_next_122 h_pc_M_next_val_122 rfl (by decide)
  -- Step 123: k >= 322, m <= 995 => k >= 323
  have h_m_mono_123 : m*(m+1)/2 ≤ 495510 := m_mono m 995 h_m_123
  have h_pc_M_123 : Nat.primeCounting 495510 = 41191 := pc_thm_495510
  have h_pc_K_prev_123 : Nat.primeCounting 104006 = 9934 := pc_thm_104006
  have h_k_124 : k ≥ 323 := staircase_step_K_direct k m 51156 495510 104006 41191 9934 323 heq h_m_mono_123 h_pc_M_123 h_pc_K_prev_123 rfl (by decide)
  have h_pc_K_next_123 : Nat.primeCounting 104652 = 9989 := pc_thm_104652
  have h_pc_M_next_val_123 : Nat.primeCounting 495510 = 41191 := pc_thm_495510
  have h_m_124 : m ≤ 994 := staircase_step_M_direct k m 51156 104652 495510 9989 41191 994 heq (k_mono 323 k h_k_124) h_pc_K_next_123 h_pc_M_next_val_123 rfl (by decide)
  -- Step 124: k >= 323, m <= 994 => k >= 325
  have h_m_mono_124 : m*(m+1)/2 ≤ 494515 := m_mono m 994 h_m_124
  have h_pc_M_124 : Nat.primeCounting 494515 = 41107 := pc_thm_494515
  have h_pc_K_prev_124 : Nat.primeCounting 105300 = 10045 := pc_thm_105300
  have h_k_125 : k ≥ 325 := staircase_step_K_direct k m 51156 494515 105300 41107 10045 325 heq h_m_mono_124 h_pc_M_124 h_pc_K_prev_124 rfl (by decide)
  have h_pc_K_next_124 : Nat.primeCounting 105950 = 10100 := pc_thm_105950
  have h_pc_M_next_val_124 : Nat.primeCounting 494515 = 41107 := pc_thm_494515
  have h_m_125 : m ≤ 993 := staircase_step_M_direct k m 51156 105950 494515 10100 41107 993 heq (k_mono 325 k h_k_125) h_pc_K_next_124 h_pc_M_next_val_124 rfl (by decide)
  -- Step 125: k >= 325, m <= 993 => k >= 326
  have h_m_mono_125 : m*(m+1)/2 ≤ 493521 := m_mono m 993 h_m_125
  have h_pc_M_125 : Nat.primeCounting 493521 = 41031 := pc_thm_493521
  have h_pc_K_prev_125 : Nat.primeCounting 105950 = 10100 := pc_thm_105950
  have h_k_126 : k ≥ 326 := staircase_step_K_direct k m 51156 493521 105950 41031 10100 326 heq h_m_mono_125 h_pc_M_125 h_pc_K_prev_125 rfl (by decide)
  have h_pc_K_next_125 : Nat.primeCounting 106602 = 10157 := pc_thm_106602
  have h_pc_M_next_val_125 : Nat.primeCounting 493521 = 41031 := pc_thm_493521
  have h_m_126 : m ≤ 992 := staircase_step_M_direct k m 51156 106602 493521 10157 41031 992 heq (k_mono 326 k h_k_126) h_pc_K_next_125 h_pc_M_next_val_125 rfl (by decide)
  -- Step 126: k >= 326, m <= 992 => k >= 327
  have h_m_mono_126 : m*(m+1)/2 ≤ 492528 := m_mono m 992 h_m_126
  have h_pc_M_126 : Nat.primeCounting 492528 = 40955 := pc_thm_492528
  have h_pc_K_prev_126 : Nat.primeCounting 106602 = 10157 := pc_thm_106602
  have h_k_127 : k ≥ 327 := staircase_step_K_direct k m 51156 492528 106602 40955 10157 327 heq h_m_mono_126 h_pc_M_126 h_pc_K_prev_126 rfl (by decide)
  have h_pc_K_next_126 : Nat.primeCounting 107256 = 10219 := pc_thm_107256
  have h_pc_M_next_val_126 : Nat.primeCounting 492528 = 40955 := pc_thm_492528
  have h_m_127 : m ≤ 991 := staircase_step_M_direct k m 51156 107256 492528 10219 40955 991 heq (k_mono 327 k h_k_127) h_pc_K_next_126 h_pc_M_next_val_126 rfl (by decide)
  -- Step 127: k >= 327, m <= 991 => k >= 329
  have h_m_mono_127 : m*(m+1)/2 ≤ 491536 := m_mono m 991 h_m_127
  have h_pc_M_127 : Nat.primeCounting 491536 = 40885 := pc_thm_491536
  have h_pc_K_prev_127 : Nat.primeCounting 107912 = 10267 := pc_thm_107912
  have h_k_128 : k ≥ 329 := staircase_step_K_direct k m 51156 491536 107912 40885 10267 329 heq h_m_mono_127 h_pc_M_127 h_pc_K_prev_127 rfl (by decide)
  have h_pc_K_next_127 : Nat.primeCounting 108570 = 10326 := pc_thm_108570
  have h_pc_M_next_val_127 : Nat.primeCounting 491536 = 40885 := pc_thm_491536
  have h_m_128 : m ≤ 990 := staircase_step_M_direct k m 51156 108570 491536 10326 40885 990 heq (k_mono 329 k h_k_128) h_pc_K_next_127 h_pc_M_next_val_127 rfl (by decide)
  -- Step 128: k >= 329, m <= 990 => k >= 330
  have h_m_mono_128 : m*(m+1)/2 ≤ 490545 := m_mono m 990 h_m_128
  have h_pc_M_128 : Nat.primeCounting 490545 = 40808 := pc_thm_490545
  have h_pc_K_prev_128 : Nat.primeCounting 108570 = 10326 := pc_thm_108570
  have h_k_129 : k ≥ 330 := staircase_step_K_direct k m 51156 490545 108570 40808 10326 330 heq h_m_mono_128 h_pc_M_128 h_pc_K_prev_128 rfl (by decide)
  have h_pc_K_next_128 : Nat.primeCounting 109230 = 10386 := pc_thm_109230
  have h_pc_M_next_val_128 : Nat.primeCounting 490545 = 40808 := pc_thm_490545
  have h_m_129 : m ≤ 989 := staircase_step_M_direct k m 51156 109230 490545 10386 40808 989 heq (k_mono 330 k h_k_129) h_pc_K_next_128 h_pc_M_next_val_128 rfl (by decide)
  -- Step 129: k >= 330, m <= 989 => k >= 331
  have h_m_mono_129 : m*(m+1)/2 ≤ 489555 := m_mono m 989 h_m_129
  have h_pc_M_129 : Nat.primeCounting 489555 = 40731 := pc_thm_489555
  have h_pc_K_prev_129 : Nat.primeCounting 109230 = 10386 := pc_thm_109230
  have h_k_130 : k ≥ 331 := staircase_step_K_direct k m 51156 489555 109230 40731 10386 331 heq h_m_mono_129 h_pc_M_129 h_pc_K_prev_129 rfl (by decide)
  have h_pc_K_next_129 : Nat.primeCounting 109892 = 10445 := pc_thm_109892
  have h_pc_M_next_val_129 : Nat.primeCounting 489555 = 40731 := pc_thm_489555
  have h_m_130 : m ≤ 988 := staircase_step_M_direct k m 51156 109892 489555 10445 40731 988 heq (k_mono 331 k h_k_130) h_pc_K_next_129 h_pc_M_next_val_129 rfl (by decide)
  -- Step 130: k >= 331, m <= 988 => k >= 333
  have h_m_mono_130 : m*(m+1)/2 ≤ 488566 := m_mono m 988 h_m_130
  have h_pc_M_130 : Nat.primeCounting 488566 = 40652 := pc_thm_488566
  have h_pc_K_prev_130 : Nat.primeCounting 110556 = 10492 := pc_thm_110556
  have h_k_131 : k ≥ 333 := staircase_step_K_direct k m 51156 488566 110556 40652 10492 333 heq h_m_mono_130 h_pc_M_130 h_pc_K_prev_130 rfl (by decide)
  have h_pc_K_next_130 : Nat.primeCounting 111222 = 10553 := pc_thm_111222
  have h_pc_M_next_val_130 : Nat.primeCounting 488566 = 40652 := pc_thm_488566
  have h_m_131 : m ≤ 987 := staircase_step_M_direct k m 51156 111222 488566 10553 40652 987 heq (k_mono 333 k h_k_131) h_pc_K_next_130 h_pc_M_next_val_130 rfl (by decide)
  -- Step 131: k >= 333, m <= 987 => k >= 334
  have h_m_mono_131 : m*(m+1)/2 ≤ 487578 := m_mono m 987 h_m_131
  have h_pc_M_131 : Nat.primeCounting 487578 = 40570 := pc_thm_487578
  have h_pc_K_prev_131 : Nat.primeCounting 111222 = 10553 := pc_thm_111222
  have h_k_132 : k ≥ 334 := staircase_step_K_direct k m 51156 487578 111222 40570 10553 334 heq h_m_mono_131 h_pc_M_131 h_pc_K_prev_131 rfl (by decide)
  have h_pc_K_next_131 : Nat.primeCounting 111890 = 10611 := pc_thm_111890
  have h_pc_M_next_val_131 : Nat.primeCounting 487578 = 40570 := pc_thm_487578
  have h_m_132 : m ≤ 986 := staircase_step_M_direct k m 51156 111890 487578 10611 40570 986 heq (k_mono 334 k h_k_132) h_pc_K_next_131 h_pc_M_next_val_131 rfl (by decide)
  -- Step 132: k >= 334, m <= 986 => k >= 335
  have h_m_mono_132 : m*(m+1)/2 ≤ 486591 := m_mono m 986 h_m_132
  have h_pc_M_132 : Nat.primeCounting 486591 = 40494 := pc_thm_486591
  have h_pc_K_prev_132 : Nat.primeCounting 111890 = 10611 := pc_thm_111890
  have h_k_133 : k ≥ 335 := staircase_step_K_direct k m 51156 486591 111890 40494 10611 335 heq h_m_mono_132 h_pc_M_132 h_pc_K_prev_132 rfl (by decide)
  have h_pc_K_next_132 : Nat.primeCounting 112560 = 10666 := pc_thm_112560
  have h_pc_M_next_val_132 : Nat.primeCounting 486591 = 40494 := pc_thm_486591
  have h_m_133 : m ≤ 985 := staircase_step_M_direct k m 51156 112560 486591 10666 40494 985 heq (k_mono 335 k h_k_133) h_pc_K_next_132 h_pc_M_next_val_132 rfl (by decide)
  -- Step 133: k >= 335, m <= 985 => k >= 337
  have h_m_mono_133 : m*(m+1)/2 ≤ 485605 := m_mono m 985 h_m_133
  have h_pc_M_133 : Nat.primeCounting 485605 = 40422 := pc_thm_485605
  have h_pc_K_prev_133 : Nat.primeCounting 113232 = 10732 := pc_thm_113232
  have h_k_134 : k ≥ 337 := staircase_step_K_direct k m 51156 485605 113232 40422 10732 337 heq h_m_mono_133 h_pc_M_133 h_pc_K_prev_133 rfl (by decide)
  have h_pc_K_next_133 : Nat.primeCounting 113906 = 10780 := pc_thm_113906
  have h_pc_M_next_val_133 : Nat.primeCounting 485605 = 40422 := pc_thm_485605
  have h_m_134 : m ≤ 984 := staircase_step_M_direct k m 51156 113906 485605 10780 40422 984 heq (k_mono 337 k h_k_134) h_pc_K_next_133 h_pc_M_next_val_133 rfl (by decide)
  -- Step 134: k >= 337, m <= 984 => k >= 338
  have h_m_mono_134 : m*(m+1)/2 ≤ 484620 := m_mono m 984 h_m_134
  have h_pc_M_134 : Nat.primeCounting 484620 = 40363 := pc_thm_484620
  have h_pc_K_prev_134 : Nat.primeCounting 113906 = 10780 := pc_thm_113906
  have h_k_135 : k ≥ 338 := staircase_step_K_direct k m 51156 484620 113906 40363 10780 338 heq h_m_mono_134 h_pc_M_134 h_pc_K_prev_134 rfl (by decide)
  have h_pc_K_next_134 : Nat.primeCounting 114582 = 10834 := pc_thm_114582
  have h_pc_M_next_val_134 : Nat.primeCounting 484620 = 40363 := pc_thm_484620
  have h_m_135 : m ≤ 983 := staircase_step_M_direct k m 51156 114582 484620 10834 40363 983 heq (k_mono 338 k h_k_135) h_pc_K_next_134 h_pc_M_next_val_134 rfl (by decide)
  -- Step 135: k >= 338, m <= 983 => k >= 339
  have h_m_mono_135 : m*(m+1)/2 ≤ 483636 := m_mono m 983 h_m_135
  have h_pc_M_135 : Nat.primeCounting 483636 = 40288 := pc_thm_483636
  have h_pc_K_prev_135 : Nat.primeCounting 114582 = 10834 := pc_thm_114582
  have h_k_136 : k ≥ 339 := staircase_step_K_direct k m 51156 483636 114582 40288 10834 339 heq h_m_mono_135 h_pc_M_135 h_pc_K_prev_135 rfl (by decide)
  have h_pc_K_next_135 : Nat.primeCounting 115260 = 10894 := pc_thm_115260
  have h_pc_M_next_val_135 : Nat.primeCounting 483636 = 40288 := pc_thm_483636
  have h_m_136 : m ≤ 982 := staircase_step_M_direct k m 51156 115260 483636 10894 40288 982 heq (k_mono 339 k h_k_136) h_pc_K_next_135 h_pc_M_next_val_135 rfl (by decide)
  exact ⟨h_k_136, h_m_136⟩

theorem staircase_part_9 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_136 : k ≥ 339) (h_m_136 : m ≤ 982) : k ≥ 358 ∧ m ≤ 967 := by
  -- Step 136: k >= 339, m <= 982 => k >= 340
  have h_m_mono_136 : m*(m+1)/2 ≤ 482653 := m_mono m 982 h_m_136
  have h_pc_M_136 : Nat.primeCounting 482653 = 40212 := pc_thm_482653
  have h_pc_K_prev_136 : Nat.primeCounting 115260 = 10894 := pc_thm_115260
  have h_k_137 : k ≥ 340 := staircase_step_K_direct k m 51156 482653 115260 40212 10894 340 heq h_m_mono_136 h_pc_M_136 h_pc_K_prev_136 rfl (by decide)
  have h_pc_K_next_136 : Nat.primeCounting 115940 = 10960 := pc_thm_115940
  have h_pc_M_next_val_136 : Nat.primeCounting 482653 = 40212 := pc_thm_482653
  have h_m_137 : m ≤ 981 := staircase_step_M_direct k m 51156 115940 482653 10960 40212 981 heq (k_mono 340 k h_k_137) h_pc_K_next_136 h_pc_M_next_val_136 rfl (by decide)
  -- Step 137: k >= 340, m <= 981 => k >= 342
  have h_m_mono_137 : m*(m+1)/2 ≤ 481671 := m_mono m 981 h_m_137
  have h_pc_M_137 : Nat.primeCounting 481671 = 40135 := pc_thm_481671
  have h_pc_K_prev_137 : Nat.primeCounting 116622 = 11012 := pc_thm_116622
  have h_k_138 : k ≥ 342 := staircase_step_K_direct k m 51156 481671 116622 40135 11012 342 heq h_m_mono_137 h_pc_M_137 h_pc_K_prev_137 rfl (by decide)
  have h_pc_K_next_137 : Nat.primeCounting 117306 = 11070 := pc_thm_117306
  have h_pc_M_next_val_137 : Nat.primeCounting 481671 = 40135 := pc_thm_481671
  have h_m_138 : m ≤ 980 := staircase_step_M_direct k m 51156 117306 481671 11070 40135 980 heq (k_mono 342 k h_k_138) h_pc_K_next_137 h_pc_M_next_val_137 rfl (by decide)
  -- Step 138: k >= 342, m <= 980 => k >= 343
  have h_m_mono_138 : m*(m+1)/2 ≤ 480690 := m_mono m 980 h_m_138
  have h_pc_M_138 : Nat.primeCounting 480690 = 40060 := pc_thm_480690
  have h_pc_K_prev_138 : Nat.primeCounting 117306 = 11070 := pc_thm_117306
  have h_k_139 : k ≥ 343 := staircase_step_K_direct k m 51156 480690 117306 40060 11070 343 heq h_m_mono_138 h_pc_M_138 h_pc_K_prev_138 rfl (by decide)
  have h_pc_K_next_138 : Nat.primeCounting 117992 = 11135 := pc_thm_117992
  have h_pc_M_next_val_138 : Nat.primeCounting 480690 = 40060 := pc_thm_480690
  have h_m_139 : m ≤ 979 := staircase_step_M_direct k m 51156 117992 480690 11135 40060 979 heq (k_mono 343 k h_k_139) h_pc_K_next_138 h_pc_M_next_val_138 rfl (by decide)
  -- Step 139: k >= 343, m <= 979 => k >= 344
  have h_m_mono_139 : m*(m+1)/2 ≤ 479710 := m_mono m 979 h_m_139
  have h_pc_M_139 : Nat.primeCounting 479710 = 39983 := pc_thm_479710
  have h_pc_K_prev_139 : Nat.primeCounting 117992 = 11135 := pc_thm_117992
  have h_k_140 : k ≥ 344 := staircase_step_K_direct k m 51156 479710 117992 39983 11135 344 heq h_m_mono_139 h_pc_M_139 h_pc_K_prev_139 rfl (by decide)
  have h_pc_K_next_139 : Nat.primeCounting 118680 = 11187 := pc_thm_118680
  have h_pc_M_next_val_139 : Nat.primeCounting 479710 = 39983 := pc_thm_479710
  have h_m_140 : m ≤ 978 := staircase_step_M_direct k m 51156 118680 479710 11187 39983 978 heq (k_mono 344 k h_k_140) h_pc_K_next_139 h_pc_M_next_val_139 rfl (by decide)
  -- Step 140: k >= 344, m <= 978 => k >= 346
  have h_m_mono_140 : m*(m+1)/2 ≤ 478731 := m_mono m 978 h_m_140
  have h_pc_M_140 : Nat.primeCounting 478731 = 39907 := pc_thm_478731
  have h_pc_K_prev_140 : Nat.primeCounting 119370 = 11246 := pc_thm_119370
  have h_k_141 : k ≥ 346 := staircase_step_K_direct k m 51156 478731 119370 39907 11246 346 heq h_m_mono_140 h_pc_M_140 h_pc_K_prev_140 rfl (by decide)
  have h_pc_K_next_140 : Nat.primeCounting 120062 = 11306 := pc_thm_120062
  have h_pc_M_next_val_140 : Nat.primeCounting 478731 = 39907 := pc_thm_478731
  have h_m_141 : m ≤ 977 := staircase_step_M_direct k m 51156 120062 478731 11306 39907 977 heq (k_mono 346 k h_k_141) h_pc_K_next_140 h_pc_M_next_val_140 rfl (by decide)
  -- Step 141: k >= 346, m <= 977 => k >= 347
  have h_m_mono_141 : m*(m+1)/2 ≤ 477753 := m_mono m 977 h_m_141
  have h_pc_M_141 : Nat.primeCounting 477753 = 39829 := pc_thm_477753
  have h_pc_K_prev_141 : Nat.primeCounting 120062 = 11306 := pc_thm_120062
  have h_k_142 : k ≥ 347 := staircase_step_K_direct k m 51156 477753 120062 39829 11306 347 heq h_m_mono_141 h_pc_M_141 h_pc_K_prev_141 rfl (by decide)
  have h_pc_K_next_141 : Nat.primeCounting 120756 = 11364 := pc_thm_120756
  have h_pc_M_next_val_141 : Nat.primeCounting 477753 = 39829 := pc_thm_477753
  have h_m_142 : m ≤ 976 := staircase_step_M_direct k m 51156 120756 477753 11364 39829 976 heq (k_mono 347 k h_k_142) h_pc_K_next_141 h_pc_M_next_val_141 rfl (by decide)
  -- Step 142: k >= 347, m <= 976 => k >= 348
  have h_m_mono_142 : m*(m+1)/2 ≤ 476776 := m_mono m 976 h_m_142
  have h_pc_M_142 : Nat.primeCounting 476776 = 39765 := pc_thm_476776
  have h_pc_K_prev_142 : Nat.primeCounting 120756 = 11364 := pc_thm_120756
  have h_k_143 : k ≥ 348 := staircase_step_K_direct k m 51156 476776 120756 39765 11364 348 heq h_m_mono_142 h_pc_M_142 h_pc_K_prev_142 rfl (by decide)
  have h_pc_K_next_142 : Nat.primeCounting 121452 = 11430 := pc_thm_121452
  have h_pc_M_next_val_142 : Nat.primeCounting 476776 = 39765 := pc_thm_476776
  have h_m_143 : m ≤ 975 := staircase_step_M_direct k m 51156 121452 476776 11430 39765 975 heq (k_mono 348 k h_k_143) h_pc_K_next_142 h_pc_M_next_val_142 rfl (by decide)
  -- Step 143: k >= 348, m <= 975 => k >= 349
  have h_m_mono_143 : m*(m+1)/2 ≤ 475800 := m_mono m 975 h_m_143
  have h_pc_M_143 : Nat.primeCounting 475800 = 39686 := pc_thm_475800
  have h_pc_K_prev_143 : Nat.primeCounting 121452 = 11430 := pc_thm_121452
  have h_k_144 : k ≥ 349 := staircase_step_K_direct k m 51156 475800 121452 39686 11430 349 heq h_m_mono_143 h_pc_M_143 h_pc_K_prev_143 rfl (by decide)
  have h_pc_K_next_143 : Nat.primeCounting 122150 = 11491 := pc_thm_122150
  have h_pc_M_next_val_143 : Nat.primeCounting 475800 = 39686 := pc_thm_475800
  have h_m_144 : m ≤ 974 := staircase_step_M_direct k m 51156 122150 475800 11491 39686 974 heq (k_mono 349 k h_k_144) h_pc_K_next_143 h_pc_M_next_val_143 rfl (by decide)
  -- Step 144: k >= 349, m <= 974 => k >= 351
  have h_m_mono_144 : m*(m+1)/2 ≤ 474825 := m_mono m 974 h_m_144
  have h_pc_M_144 : Nat.primeCounting 474825 = 39604 := pc_thm_474825
  have h_pc_K_prev_144 : Nat.primeCounting 122850 = 11551 := pc_thm_122850
  have h_k_145 : k ≥ 351 := staircase_step_K_direct k m 51156 474825 122850 39604 11551 351 heq h_m_mono_144 h_pc_M_144 h_pc_K_prev_144 rfl (by decide)
  have h_pc_K_next_144 : Nat.primeCounting 123552 = 11611 := pc_thm_123552
  have h_pc_M_next_val_144 : Nat.primeCounting 474825 = 39604 := pc_thm_474825
  have h_m_145 : m ≤ 973 := staircase_step_M_direct k m 51156 123552 474825 11611 39604 973 heq (k_mono 351 k h_k_145) h_pc_K_next_144 h_pc_M_next_val_144 rfl (by decide)
  -- Step 145: k >= 351, m <= 973 => k >= 352
  have h_m_mono_145 : m*(m+1)/2 ≤ 473851 := m_mono m 973 h_m_145
  have h_pc_M_145 : Nat.primeCounting 473851 = 39523 := pc_thm_473851
  have h_pc_K_prev_145 : Nat.primeCounting 123552 = 11611 := pc_thm_123552
  have h_k_146 : k ≥ 352 := staircase_step_K_direct k m 51156 473851 123552 39523 11611 352 heq h_m_mono_145 h_pc_M_145 h_pc_K_prev_145 rfl (by decide)
  have h_pc_K_next_145 : Nat.primeCounting 124256 = 11671 := pc_thm_124256
  have h_pc_M_next_val_145 : Nat.primeCounting 473851 = 39523 := pc_thm_473851
  have h_m_146 : m ≤ 972 := staircase_step_M_direct k m 51156 124256 473851 11671 39523 972 heq (k_mono 352 k h_k_146) h_pc_K_next_145 h_pc_M_next_val_145 rfl (by decide)
  -- Step 146: k >= 352, m <= 972 => k >= 353
  have h_m_mono_146 : m*(m+1)/2 ≤ 472878 := m_mono m 972 h_m_146
  have h_pc_M_146 : Nat.primeCounting 472878 = 39453 := pc_thm_472878
  have h_pc_K_prev_146 : Nat.primeCounting 124256 = 11671 := pc_thm_124256
  have h_k_147 : k ≥ 353 := staircase_step_K_direct k m 51156 472878 124256 39453 11671 353 heq h_m_mono_146 h_pc_M_146 h_pc_K_prev_146 rfl (by decide)
  have h_pc_K_next_146 : Nat.primeCounting 124962 = 11730 := pc_thm_124962
  have h_pc_M_next_val_146 : Nat.primeCounting 472878 = 39453 := pc_thm_472878
  have h_m_147 : m ≤ 971 := staircase_step_M_direct k m 51156 124962 472878 11730 39453 971 heq (k_mono 353 k h_k_147) h_pc_K_next_146 h_pc_M_next_val_146 rfl (by decide)
  -- Step 147: k >= 353, m <= 971 => k >= 354
  have h_m_mono_147 : m*(m+1)/2 ≤ 471906 := m_mono m 971 h_m_147
  have h_pc_M_147 : Nat.primeCounting 471906 = 39380 := pc_thm_471906
  have h_pc_K_prev_147 : Nat.primeCounting 124962 = 11730 := pc_thm_124962
  have h_k_148 : k ≥ 354 := staircase_step_K_direct k m 51156 471906 124962 39380 11730 354 heq h_m_mono_147 h_pc_M_147 h_pc_K_prev_147 rfl (by decide)
  have h_pc_K_next_147 : Nat.primeCounting 125670 = 11791 := pc_thm_125670
  have h_pc_M_next_val_147 : Nat.primeCounting 471906 = 39380 := pc_thm_471906
  have h_m_148 : m ≤ 970 := staircase_step_M_direct k m 51156 125670 471906 11791 39380 970 heq (k_mono 354 k h_k_148) h_pc_K_next_147 h_pc_M_next_val_147 rfl (by decide)
  -- Step 148: k >= 354, m <= 970 => k >= 355
  have h_m_mono_148 : m*(m+1)/2 ≤ 470935 := m_mono m 970 h_m_148
  have h_pc_M_148 : Nat.primeCounting 470935 = 39304 := pc_thm_470935
  have h_pc_K_prev_148 : Nat.primeCounting 125670 = 11791 := pc_thm_125670
  have h_k_149 : k ≥ 355 := staircase_step_K_direct k m 51156 470935 125670 39304 11791 355 heq h_m_mono_148 h_pc_M_148 h_pc_K_prev_148 rfl (by decide)
  have h_pc_K_next_148 : Nat.primeCounting 126380 = 11853 := pc_thm_126380
  have h_pc_M_next_val_148 : Nat.primeCounting 470935 = 39304 := pc_thm_470935
  have h_m_149 : m ≤ 969 := staircase_step_M_direct k m 51156 126380 470935 11853 39304 969 heq (k_mono 355 k h_k_149) h_pc_K_next_148 h_pc_M_next_val_148 rfl (by decide)
  -- Step 149: k >= 355, m <= 969 => k >= 357
  have h_m_mono_149 : m*(m+1)/2 ≤ 469965 := m_mono m 969 h_m_149
  have h_pc_M_149 : Nat.primeCounting 469965 = 39220 := pc_thm_469965
  have h_pc_K_prev_149 : Nat.primeCounting 127092 = 11907 := pc_thm_127092
  have h_k_150 : k ≥ 357 := staircase_step_K_direct k m 51156 469965 127092 39220 11907 357 heq h_m_mono_149 h_pc_M_149 h_pc_K_prev_149 rfl (by decide)
  have h_pc_K_next_149 : Nat.primeCounting 127806 = 11970 := pc_thm_127806
  have h_pc_M_next_val_149 : Nat.primeCounting 469965 = 39220 := pc_thm_469965
  have h_m_150 : m ≤ 968 := staircase_step_M_direct k m 51156 127806 469965 11970 39220 968 heq (k_mono 357 k h_k_150) h_pc_K_next_149 h_pc_M_next_val_149 rfl (by decide)
  -- Step 150: k >= 357, m <= 968 => k >= 358
  have h_m_mono_150 : m*(m+1)/2 ≤ 468996 := m_mono m 968 h_m_150
  have h_pc_M_150 : Nat.primeCounting 468996 = 39151 := pc_thm_468996
  have h_pc_K_prev_150 : Nat.primeCounting 127806 = 11970 := pc_thm_127806
  have h_k_151 : k ≥ 358 := staircase_step_K_direct k m 51156 468996 127806 39151 11970 358 heq h_m_mono_150 h_pc_M_150 h_pc_K_prev_150 rfl (by decide)
  have h_pc_K_next_150 : Nat.primeCounting 128522 = 12035 := pc_thm_128522
  have h_pc_M_next_val_150 : Nat.primeCounting 468996 = 39151 := pc_thm_468996
  have h_m_151 : m ≤ 967 := staircase_step_M_direct k m 51156 128522 468996 12035 39151 967 heq (k_mono 358 k h_k_151) h_pc_K_next_150 h_pc_M_next_val_150 rfl (by decide)
  exact ⟨h_k_151, h_m_151⟩

theorem staircase_part_10 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_151 : k ≥ 358) (h_m_151 : m ≤ 967) : k ≥ 376 ∧ m ≤ 952 := by
  -- Step 151: k >= 358, m <= 967 => k >= 359
  have h_m_mono_151 : m*(m+1)/2 ≤ 468028 := m_mono m 967 h_m_151
  have h_pc_M_151 : Nat.primeCounting 468028 = 39069 := pc_thm_468028
  have h_pc_K_prev_151 : Nat.primeCounting 128522 = 12035 := pc_thm_128522
  have h_k_152 : k ≥ 359 := staircase_step_K_direct k m 51156 468028 128522 39069 12035 359 heq h_m_mono_151 h_pc_M_151 h_pc_K_prev_151 rfl (by decide)
  have h_pc_K_next_151 : Nat.primeCounting 129240 = 12097 := pc_thm_129240
  have h_pc_M_next_val_151 : Nat.primeCounting 468028 = 39069 := pc_thm_468028
  have h_m_152 : m ≤ 966 := staircase_step_M_direct k m 51156 129240 468028 12097 39069 966 heq (k_mono 359 k h_k_152) h_pc_K_next_151 h_pc_M_next_val_151 rfl (by decide)
  -- Step 152: k >= 359, m <= 966 => k >= 361
  have h_m_mono_152 : m*(m+1)/2 ≤ 467061 := m_mono m 966 h_m_152
  have h_pc_M_152 : Nat.primeCounting 467061 = 38987 := pc_thm_467061
  have h_pc_K_prev_152 : Nat.primeCounting 129960 = 12157 := pc_thm_129960
  have h_k_153 : k ≥ 361 := staircase_step_K_direct k m 51156 467061 129960 38987 12157 361 heq h_m_mono_152 h_pc_M_152 h_pc_K_prev_152 rfl (by decide)
  have h_pc_K_next_152 : Nat.primeCounting 130682 = 12223 := pc_thm_130682
  have h_pc_M_next_val_152 : Nat.primeCounting 467061 = 38987 := pc_thm_467061
  have h_m_153 : m ≤ 965 := staircase_step_M_direct k m 51156 130682 467061 12223 38987 965 heq (k_mono 361 k h_k_153) h_pc_K_next_152 h_pc_M_next_val_152 rfl (by decide)
  -- Step 153: k >= 361, m <= 965 => k >= 362
  have h_m_mono_153 : m*(m+1)/2 ≤ 466095 := m_mono m 965 h_m_153
  have h_pc_M_153 : Nat.primeCounting 466095 = 38925 := pc_thm_466095
  have h_pc_K_prev_153 : Nat.primeCounting 130682 = 12223 := pc_thm_130682
  have h_k_154 : k ≥ 362 := staircase_step_K_direct k m 51156 466095 130682 38925 12223 362 heq h_m_mono_153 h_pc_M_153 h_pc_K_prev_153 rfl (by decide)
  have h_pc_K_next_153 : Nat.primeCounting 131406 = 12275 := pc_thm_131406
  have h_pc_M_next_val_153 : Nat.primeCounting 466095 = 38925 := pc_thm_466095
  have h_m_154 : m ≤ 964 := staircase_step_M_direct k m 51156 131406 466095 12275 38925 964 heq (k_mono 362 k h_k_154) h_pc_K_next_153 h_pc_M_next_val_153 rfl (by decide)
  -- Step 154: k >= 362, m <= 964 => k >= 363
  have h_m_mono_154 : m*(m+1)/2 ≤ 465130 := m_mono m 964 h_m_154
  have h_pc_M_154 : Nat.primeCounting 465130 = 38853 := pc_thm_465130
  have h_pc_K_prev_154 : Nat.primeCounting 131406 = 12275 := pc_thm_131406
  have h_k_155 : k ≥ 363 := staircase_step_K_direct k m 51156 465130 131406 38853 12275 363 heq h_m_mono_154 h_pc_M_154 h_pc_K_prev_154 rfl (by decide)
  have h_pc_K_next_154 : Nat.primeCounting 132132 = 12336 := pc_thm_132132
  have h_pc_M_next_val_154 : Nat.primeCounting 465130 = 38853 := pc_thm_465130
  have h_m_155 : m ≤ 963 := staircase_step_M_direct k m 51156 132132 465130 12336 38853 963 heq (k_mono 363 k h_k_155) h_pc_K_next_154 h_pc_M_next_val_154 rfl (by decide)
  -- Step 155: k >= 363, m <= 963 => k >= 364
  have h_m_mono_155 : m*(m+1)/2 ≤ 464166 := m_mono m 963 h_m_155
  have h_pc_M_155 : Nat.primeCounting 464166 = 38769 := pc_thm_464166
  have h_pc_K_prev_155 : Nat.primeCounting 132132 = 12336 := pc_thm_132132
  have h_k_156 : k ≥ 364 := staircase_step_K_direct k m 51156 464166 132132 38769 12336 364 heq h_m_mono_155 h_pc_M_155 h_pc_K_prev_155 rfl (by decide)
  have h_pc_K_next_155 : Nat.primeCounting 132860 = 12402 := pc_thm_132860
  have h_pc_M_next_val_155 : Nat.primeCounting 464166 = 38769 := pc_thm_464166
  have h_m_156 : m ≤ 962 := staircase_step_M_direct k m 51156 132860 464166 12402 38769 962 heq (k_mono 364 k h_k_156) h_pc_K_next_155 h_pc_M_next_val_155 rfl (by decide)
  -- Step 156: k >= 364, m <= 962 => k >= 366
  have h_m_mono_156 : m*(m+1)/2 ≤ 463203 := m_mono m 962 h_m_156
  have h_pc_M_156 : Nat.primeCounting 463203 = 38686 := pc_thm_463203
  have h_pc_K_prev_156 : Nat.primeCounting 133590 = 12464 := pc_thm_133590
  have h_k_157 : k ≥ 366 := staircase_step_K_direct k m 51156 463203 133590 38686 12464 366 heq h_m_mono_156 h_pc_M_156 h_pc_K_prev_156 rfl (by decide)
  have h_pc_K_next_156 : Nat.primeCounting 134322 = 12523 := pc_thm_134322
  have h_pc_M_next_val_156 : Nat.primeCounting 463203 = 38686 := pc_thm_463203
  have h_m_157 : m ≤ 961 := staircase_step_M_direct k m 51156 134322 463203 12523 38686 961 heq (k_mono 366 k h_k_157) h_pc_K_next_156 h_pc_M_next_val_156 rfl (by decide)
  -- Step 157: k >= 366, m <= 961 => k >= 367
  have h_m_mono_157 : m*(m+1)/2 ≤ 462241 := m_mono m 961 h_m_157
  have h_pc_M_157 : Nat.primeCounting 462241 = 38620 := pc_thm_462241
  have h_pc_K_prev_157 : Nat.primeCounting 134322 = 12523 := pc_thm_134322
  have h_k_158 : k ≥ 367 := staircase_step_K_direct k m 51156 462241 134322 38620 12523 367 heq h_m_mono_157 h_pc_M_157 h_pc_K_prev_157 rfl (by decide)
  have h_pc_K_next_157 : Nat.primeCounting 135056 = 12582 := pc_thm_135056
  have h_pc_M_next_val_157 : Nat.primeCounting 462241 = 38620 := pc_thm_462241
  have h_m_158 : m ≤ 960 := staircase_step_M_direct k m 51156 135056 462241 12582 38620 960 heq (k_mono 367 k h_k_158) h_pc_K_next_157 h_pc_M_next_val_157 rfl (by decide)
  -- Step 158: k >= 367, m <= 960 => k >= 368
  have h_m_mono_158 : m*(m+1)/2 ≤ 461280 := m_mono m 960 h_m_158
  have h_pc_M_158 : Nat.primeCounting 461280 = 38555 := pc_thm_461280
  have h_pc_K_prev_158 : Nat.primeCounting 135056 = 12582 := pc_thm_135056
  have h_k_159 : k ≥ 368 := staircase_step_K_direct k m 51156 461280 135056 38555 12582 368 heq h_m_mono_158 h_pc_M_158 h_pc_K_prev_158 rfl (by decide)
  have h_pc_K_next_158 : Nat.primeCounting 135792 = 12651 := pc_thm_135792
  have h_pc_M_next_val_158 : Nat.primeCounting 461280 = 38555 := pc_thm_461280
  have h_m_159 : m ≤ 959 := staircase_step_M_direct k m 51156 135792 461280 12651 38555 959 heq (k_mono 368 k h_k_159) h_pc_K_next_158 h_pc_M_next_val_158 rfl (by decide)
  -- Step 159: k >= 368, m <= 959 => k >= 369
  have h_m_mono_159 : m*(m+1)/2 ≤ 460320 := m_mono m 959 h_m_159
  have h_pc_M_159 : Nat.primeCounting 460320 = 38483 := pc_thm_460320
  have h_pc_K_prev_159 : Nat.primeCounting 135792 = 12651 := pc_thm_135792
  have h_k_160 : k ≥ 369 := staircase_step_K_direct k m 51156 460320 135792 38483 12651 369 heq h_m_mono_159 h_pc_M_159 h_pc_K_prev_159 rfl (by decide)
  have h_pc_K_next_159 : Nat.primeCounting 136530 = 12717 := pc_thm_136530
  have h_pc_M_next_val_159 : Nat.primeCounting 460320 = 38483 := pc_thm_460320
  have h_m_160 : m ≤ 958 := staircase_step_M_direct k m 51156 136530 460320 12717 38483 958 heq (k_mono 369 k h_k_160) h_pc_K_next_159 h_pc_M_next_val_159 rfl (by decide)
  -- Step 160: k >= 369, m <= 958 => k >= 370
  have h_m_mono_160 : m*(m+1)/2 ≤ 459361 := m_mono m 958 h_m_160
  have h_pc_M_160 : Nat.primeCounting 459361 = 38418 := pc_thm_459361
  have h_pc_K_prev_160 : Nat.primeCounting 136530 = 12717 := pc_thm_136530
  have h_k_161 : k ≥ 370 := staircase_step_K_direct k m 51156 459361 136530 38418 12717 370 heq h_m_mono_160 h_pc_M_160 h_pc_K_prev_160 rfl (by decide)
  have h_pc_K_next_160 : Nat.primeCounting 137270 = 12780 := pc_thm_137270
  have h_pc_M_next_val_160 : Nat.primeCounting 459361 = 38418 := pc_thm_459361
  have h_m_161 : m ≤ 957 := staircase_step_M_direct k m 51156 137270 459361 12780 38418 957 heq (k_mono 370 k h_k_161) h_pc_K_next_160 h_pc_M_next_val_160 rfl (by decide)
  -- Step 161: k >= 370, m <= 957 => k >= 371
  have h_m_mono_161 : m*(m+1)/2 ≤ 458403 := m_mono m 957 h_m_161
  have h_pc_M_161 : Nat.primeCounting 458403 = 38343 := pc_thm_458403
  have h_pc_K_prev_161 : Nat.primeCounting 137270 = 12780 := pc_thm_137270
  have h_k_162 : k ≥ 371 := staircase_step_K_direct k m 51156 458403 137270 38343 12780 371 heq h_m_mono_161 h_pc_M_161 h_pc_K_prev_161 rfl (by decide)
  have h_pc_K_next_161 : Nat.primeCounting 138012 = 12842 := pc_thm_138012
  have h_pc_M_next_val_161 : Nat.primeCounting 458403 = 38343 := pc_thm_458403
  have h_m_162 : m ≤ 956 := staircase_step_M_direct k m 51156 138012 458403 12842 38343 956 heq (k_mono 371 k h_k_162) h_pc_K_next_161 h_pc_M_next_val_161 rfl (by decide)
  -- Step 162: k >= 371, m <= 956 => k >= 372
  have h_m_mono_162 : m*(m+1)/2 ≤ 457446 := m_mono m 956 h_m_162
  have h_pc_M_162 : Nat.primeCounting 457446 = 38278 := pc_thm_457446
  have h_pc_K_prev_162 : Nat.primeCounting 138012 = 12842 := pc_thm_138012
  have h_k_163 : k ≥ 372 := staircase_step_K_direct k m 51156 457446 138012 38278 12842 372 heq h_m_mono_162 h_pc_M_162 h_pc_K_prev_162 rfl (by decide)
  have h_pc_K_next_162 : Nat.primeCounting 138756 = 12907 := pc_thm_138756
  have h_pc_M_next_val_162 : Nat.primeCounting 457446 = 38278 := pc_thm_457446
  have h_m_163 : m ≤ 955 := staircase_step_M_direct k m 51156 138756 457446 12907 38278 955 heq (k_mono 372 k h_k_163) h_pc_K_next_162 h_pc_M_next_val_162 rfl (by decide)
  -- Step 163: k >= 372, m <= 955 => k >= 373
  have h_m_mono_163 : m*(m+1)/2 ≤ 456490 := m_mono m 955 h_m_163
  have h_pc_M_163 : Nat.primeCounting 456490 = 38196 := pc_thm_456490
  have h_pc_K_prev_163 : Nat.primeCounting 138756 = 12907 := pc_thm_138756
  have h_k_164 : k ≥ 373 := staircase_step_K_direct k m 51156 456490 138756 38196 12907 373 heq h_m_mono_163 h_pc_M_163 h_pc_K_prev_163 rfl (by decide)
  have h_pc_K_next_163 : Nat.primeCounting 139502 = 12968 := pc_thm_139502
  have h_pc_M_next_val_163 : Nat.primeCounting 456490 = 38196 := pc_thm_456490
  have h_m_164 : m ≤ 954 := staircase_step_M_direct k m 51156 139502 456490 12968 38196 954 heq (k_mono 373 k h_k_164) h_pc_K_next_163 h_pc_M_next_val_163 rfl (by decide)
  -- Step 164: k >= 373, m <= 954 => k >= 374
  have h_m_mono_164 : m*(m+1)/2 ≤ 455535 := m_mono m 954 h_m_164
  have h_pc_M_164 : Nat.primeCounting 455535 = 38129 := pc_thm_455535
  have h_pc_K_prev_164 : Nat.primeCounting 139502 = 12968 := pc_thm_139502
  have h_k_165 : k ≥ 374 := staircase_step_K_direct k m 51156 455535 139502 38129 12968 374 heq h_m_mono_164 h_pc_M_164 h_pc_K_prev_164 rfl (by decide)
  have h_pc_K_next_164 : Nat.primeCounting 140250 = 13029 := pc_thm_140250
  have h_pc_M_next_val_164 : Nat.primeCounting 455535 = 38129 := pc_thm_455535
  have h_m_165 : m ≤ 953 := staircase_step_M_direct k m 51156 140250 455535 13029 38129 953 heq (k_mono 374 k h_k_165) h_pc_K_next_164 h_pc_M_next_val_164 rfl (by decide)
  -- Step 165: k >= 374, m <= 953 => k >= 376
  have h_m_mono_165 : m*(m+1)/2 ≤ 454581 := m_mono m 953 h_m_165
  have h_pc_M_165 : Nat.primeCounting 454581 = 38053 := pc_thm_454581
  have h_pc_K_prev_165 : Nat.primeCounting 141000 = 13097 := pc_thm_141000
  have h_k_166 : k ≥ 376 := staircase_step_K_direct k m 51156 454581 141000 38053 13097 376 heq h_m_mono_165 h_pc_M_165 h_pc_K_prev_165 rfl (by decide)
  have h_pc_K_next_165 : Nat.primeCounting 141752 = 13162 := pc_thm_141752
  have h_pc_M_next_val_165 : Nat.primeCounting 454581 = 38053 := pc_thm_454581
  have h_m_166 : m ≤ 952 := staircase_step_M_direct k m 51156 141752 454581 13162 38053 952 heq (k_mono 376 k h_k_166) h_pc_K_next_165 h_pc_M_next_val_165 rfl (by decide)
  exact ⟨h_k_166, h_m_166⟩

theorem staircase_part_11 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_166 : k ≥ 376) (h_m_166 : m ≤ 952) : k ≥ 392 ∧ m ≤ 937 := by
  -- Step 166: k >= 376, m <= 952 => k >= 377
  have h_m_mono_166 : m*(m+1)/2 ≤ 453628 := m_mono m 952 h_m_166
  have h_pc_M_166 : Nat.primeCounting 453628 = 37979 := pc_thm_453628
  have h_pc_K_prev_166 : Nat.primeCounting 141752 = 13162 := pc_thm_141752
  have h_k_167 : k ≥ 377 := staircase_step_K_direct k m 51156 453628 141752 37979 13162 377 heq h_m_mono_166 h_pc_M_166 h_pc_K_prev_166 rfl (by decide)
  have h_pc_K_next_166 : Nat.primeCounting 142506 = 13223 := pc_thm_142506
  have h_pc_M_next_val_166 : Nat.primeCounting 453628 = 37979 := pc_thm_453628
  have h_m_167 : m ≤ 951 := staircase_step_M_direct k m 51156 142506 453628 13223 37979 951 heq (k_mono 377 k h_k_167) h_pc_K_next_166 h_pc_M_next_val_166 rfl (by decide)
  -- Step 167: k >= 377, m <= 951 => k >= 378
  have h_m_mono_167 : m*(m+1)/2 ≤ 452676 := m_mono m 951 h_m_167
  have h_pc_M_167 : Nat.primeCounting 452676 = 37918 := pc_thm_452676
  have h_pc_K_prev_167 : Nat.primeCounting 142506 = 13223 := pc_thm_142506
  have h_k_168 : k ≥ 378 := staircase_step_K_direct k m 51156 452676 142506 37918 13223 378 heq h_m_mono_167 h_pc_M_167 h_pc_K_prev_167 rfl (by decide)
  have h_pc_K_next_167 : Nat.primeCounting 143262 = 13282 := pc_thm_143262
  have h_pc_M_next_val_167 : Nat.primeCounting 452676 = 37918 := pc_thm_452676
  have h_m_168 : m ≤ 950 := staircase_step_M_direct k m 51156 143262 452676 13282 37918 950 heq (k_mono 378 k h_k_168) h_pc_K_next_167 h_pc_M_next_val_167 rfl (by decide)
  -- Step 168: k >= 378, m <= 950 => k >= 379
  have h_m_mono_168 : m*(m+1)/2 ≤ 451725 := m_mono m 950 h_m_168
  have h_pc_M_168 : Nat.primeCounting 451725 = 37851 := pc_thm_451725
  have h_pc_K_prev_168 : Nat.primeCounting 143262 = 13282 := pc_thm_143262
  have h_k_169 : k ≥ 379 := staircase_step_K_direct k m 51156 451725 143262 37851 13282 379 heq h_m_mono_168 h_pc_M_168 h_pc_K_prev_168 rfl (by decide)
  have h_pc_K_next_168 : Nat.primeCounting 144020 = 13344 := pc_thm_144020
  have h_pc_M_next_val_168 : Nat.primeCounting 451725 = 37851 := pc_thm_451725
  have h_m_169 : m ≤ 949 := staircase_step_M_direct k m 51156 144020 451725 13344 37851 949 heq (k_mono 379 k h_k_169) h_pc_K_next_168 h_pc_M_next_val_168 rfl (by decide)
  -- Step 169: k >= 379, m <= 949 => k >= 380
  have h_m_mono_169 : m*(m+1)/2 ≤ 450775 := m_mono m 949 h_m_169
  have h_pc_M_169 : Nat.primeCounting 450775 = 37773 := pc_thm_450775
  have h_pc_K_prev_169 : Nat.primeCounting 144020 = 13344 := pc_thm_144020
  have h_k_170 : k ≥ 380 := staircase_step_K_direct k m 51156 450775 144020 37773 13344 380 heq h_m_mono_169 h_pc_M_169 h_pc_K_prev_169 rfl (by decide)
  have h_pc_K_next_169 : Nat.primeCounting 144780 = 13406 := pc_thm_144780
  have h_pc_M_next_val_169 : Nat.primeCounting 450775 = 37773 := pc_thm_450775
  have h_m_170 : m ≤ 948 := staircase_step_M_direct k m 51156 144780 450775 13406 37773 948 heq (k_mono 380 k h_k_170) h_pc_K_next_169 h_pc_M_next_val_169 rfl (by decide)
  -- Step 170: k >= 380, m <= 948 => k >= 381
  have h_m_mono_170 : m*(m+1)/2 ≤ 449826 := m_mono m 948 h_m_170
  have h_pc_M_170 : Nat.primeCounting 449826 = 37694 := pc_thm_449826
  have h_pc_K_prev_170 : Nat.primeCounting 144780 = 13406 := pc_thm_144780
  have h_k_171 : k ≥ 381 := staircase_step_K_direct k m 51156 449826 144780 37694 13406 381 heq h_m_mono_170 h_pc_M_170 h_pc_K_prev_170 rfl (by decide)
  have h_pc_K_next_170 : Nat.primeCounting 145542 = 13467 := pc_thm_145542
  have h_pc_M_next_val_170 : Nat.primeCounting 449826 = 37694 := pc_thm_449826
  have h_m_171 : m ≤ 947 := staircase_step_M_direct k m 51156 145542 449826 13467 37694 947 heq (k_mono 381 k h_k_171) h_pc_K_next_170 h_pc_M_next_val_170 rfl (by decide)
  -- Step 171: k >= 381, m <= 947 => k >= 383
  have h_m_mono_171 : m*(m+1)/2 ≤ 448878 := m_mono m 947 h_m_171
  have h_pc_M_171 : Nat.primeCounting 448878 = 37617 := pc_thm_448878
  have h_pc_K_prev_171 : Nat.primeCounting 146306 = 13534 := pc_thm_146306
  have h_k_172 : k ≥ 383 := staircase_step_K_direct k m 51156 448878 146306 37617 13534 383 heq h_m_mono_171 h_pc_M_171 h_pc_K_prev_171 rfl (by decide)
  have h_pc_K_next_171 : Nat.primeCounting 147072 = 13595 := pc_thm_147072
  have h_pc_M_next_val_171 : Nat.primeCounting 448878 = 37617 := pc_thm_448878
  have h_m_172 : m ≤ 946 := staircase_step_M_direct k m 51156 147072 448878 13595 37617 946 heq (k_mono 383 k h_k_172) h_pc_K_next_171 h_pc_M_next_val_171 rfl (by decide)
  -- Step 172: k >= 383, m <= 946 => k >= 384
  have h_m_mono_172 : m*(m+1)/2 ≤ 447931 := m_mono m 946 h_m_172
  have h_pc_M_172 : Nat.primeCounting 447931 = 37552 := pc_thm_447931
  have h_pc_K_prev_172 : Nat.primeCounting 147072 = 13595 := pc_thm_147072
  have h_k_173 : k ≥ 384 := staircase_step_K_direct k m 51156 447931 147072 37552 13595 384 heq h_m_mono_172 h_pc_M_172 h_pc_K_prev_172 rfl (by decide)
  have h_pc_K_next_172 : Nat.primeCounting 147840 = 13665 := pc_thm_147840
  have h_pc_M_next_val_172 : Nat.primeCounting 447931 = 37552 := pc_thm_447931
  have h_m_173 : m ≤ 945 := staircase_step_M_direct k m 51156 147840 447931 13665 37552 945 heq (k_mono 384 k h_k_173) h_pc_K_next_172 h_pc_M_next_val_172 rfl (by decide)
  -- Step 173: k >= 384, m <= 945 => k >= 385
  have h_m_mono_173 : m*(m+1)/2 ≤ 446985 := m_mono m 945 h_m_173
  have h_pc_M_173 : Nat.primeCounting 446985 = 37483 := pc_thm_446985
  have h_pc_K_prev_173 : Nat.primeCounting 147840 = 13665 := pc_thm_147840
  have h_k_174 : k ≥ 385 := staircase_step_K_direct k m 51156 446985 147840 37483 13665 385 heq h_m_mono_173 h_pc_M_173 h_pc_K_prev_173 rfl (by decide)
  have h_pc_K_next_173 : Nat.primeCounting 148610 = 13722 := pc_thm_148610
  have h_pc_M_next_val_173 : Nat.primeCounting 446985 = 37483 := pc_thm_446985
  have h_m_174 : m ≤ 944 := staircase_step_M_direct k m 51156 148610 446985 13722 37483 944 heq (k_mono 385 k h_k_174) h_pc_K_next_173 h_pc_M_next_val_173 rfl (by decide)
  -- Step 174: k >= 385, m <= 944 => k >= 386
  have h_m_mono_174 : m*(m+1)/2 ≤ 446040 := m_mono m 944 h_m_174
  have h_pc_M_174 : Nat.primeCounting 446040 = 37417 := pc_thm_446040
  have h_pc_K_prev_174 : Nat.primeCounting 148610 = 13722 := pc_thm_148610
  have h_k_175 : k ≥ 386 := staircase_step_K_direct k m 51156 446040 148610 37417 13722 386 heq h_m_mono_174 h_pc_M_174 h_pc_K_prev_174 rfl (by decide)
  have h_pc_K_next_174 : Nat.primeCounting 149382 = 13795 := pc_thm_149382
  have h_pc_M_next_val_174 : Nat.primeCounting 446040 = 37417 := pc_thm_446040
  have h_m_175 : m ≤ 943 := staircase_step_M_direct k m 51156 149382 446040 13795 37417 943 heq (k_mono 386 k h_k_175) h_pc_K_next_174 h_pc_M_next_val_174 rfl (by decide)
  -- Step 175: k >= 386, m <= 943 => k >= 387
  have h_m_mono_175 : m*(m+1)/2 ≤ 445096 := m_mono m 943 h_m_175
  have h_pc_M_175 : Nat.primeCounting 445096 = 37355 := pc_thm_445096
  have h_pc_K_prev_175 : Nat.primeCounting 149382 = 13795 := pc_thm_149382
  have h_k_176 : k ≥ 387 := staircase_step_K_direct k m 51156 445096 149382 37355 13795 387 heq h_m_mono_175 h_pc_M_175 h_pc_K_prev_175 rfl (by decide)
  have h_pc_K_next_175 : Nat.primeCounting 150156 = 13862 := pc_thm_150156
  have h_pc_M_next_val_175 : Nat.primeCounting 445096 = 37355 := pc_thm_445096
  have h_m_176 : m ≤ 942 := staircase_step_M_direct k m 51156 150156 445096 13862 37355 942 heq (k_mono 387 k h_k_176) h_pc_K_next_175 h_pc_M_next_val_175 rfl (by decide)
  -- Step 176: k >= 387, m <= 942 => k >= 388
  have h_m_mono_176 : m*(m+1)/2 ≤ 444153 := m_mono m 942 h_m_176
  have h_pc_M_176 : Nat.primeCounting 444153 = 37278 := pc_thm_444153
  have h_pc_K_prev_176 : Nat.primeCounting 150156 = 13862 := pc_thm_150156
  have h_k_177 : k ≥ 388 := staircase_step_K_direct k m 51156 444153 150156 37278 13862 388 heq h_m_mono_176 h_pc_M_176 h_pc_K_prev_176 rfl (by decide)
  have h_pc_K_next_176 : Nat.primeCounting 150932 = 13927 := pc_thm_150932
  have h_pc_M_next_val_176 : Nat.primeCounting 444153 = 37278 := pc_thm_444153
  have h_m_177 : m ≤ 941 := staircase_step_M_direct k m 51156 150932 444153 13927 37278 941 heq (k_mono 388 k h_k_177) h_pc_K_next_176 h_pc_M_next_val_176 rfl (by decide)
  -- Step 177: k >= 388, m <= 941 => k >= 389
  have h_m_mono_177 : m*(m+1)/2 ≤ 443211 := m_mono m 941 h_m_177
  have h_pc_M_177 : Nat.primeCounting 443211 = 37197 := pc_thm_443211
  have h_pc_K_prev_177 : Nat.primeCounting 150932 = 13927 := pc_thm_150932
  have h_k_178 : k ≥ 389 := staircase_step_K_direct k m 51156 443211 150932 37197 13927 389 heq h_m_mono_177 h_pc_M_177 h_pc_K_prev_177 rfl (by decide)
  have h_pc_K_next_177 : Nat.primeCounting 151710 = 14000 := pc_thm_151710
  have h_pc_M_next_val_177 : Nat.primeCounting 443211 = 37197 := pc_thm_443211
  have h_m_178 : m ≤ 940 := staircase_step_M_direct k m 51156 151710 443211 14000 37197 940 heq (k_mono 389 k h_k_178) h_pc_K_next_177 h_pc_M_next_val_177 rfl (by decide)
  -- Step 178: k >= 389, m <= 940 => k >= 390
  have h_m_mono_178 : m*(m+1)/2 ≤ 442270 := m_mono m 940 h_m_178
  have h_pc_M_178 : Nat.primeCounting 442270 = 37118 := pc_thm_442270
  have h_pc_K_prev_178 : Nat.primeCounting 151710 = 14000 := pc_thm_151710
  have h_k_179 : k ≥ 390 := staircase_step_K_direct k m 51156 442270 151710 37118 14000 390 heq h_m_mono_178 h_pc_M_178 h_pc_K_prev_178 rfl (by decide)
  have h_pc_K_next_178 : Nat.primeCounting 152490 = 14065 := pc_thm_152490
  have h_pc_M_next_val_178 : Nat.primeCounting 442270 = 37118 := pc_thm_442270
  have h_m_179 : m ≤ 939 := staircase_step_M_direct k m 51156 152490 442270 14065 37118 939 heq (k_mono 390 k h_k_179) h_pc_K_next_178 h_pc_M_next_val_178 rfl (by decide)
  -- Step 179: k >= 390, m <= 939 => k >= 391
  have h_m_mono_179 : m*(m+1)/2 ≤ 441330 := m_mono m 939 h_m_179
  have h_pc_M_179 : Nat.primeCounting 441330 = 37047 := pc_thm_441330
  have h_pc_K_prev_179 : Nat.primeCounting 152490 = 14065 := pc_thm_152490
  have h_k_180 : k ≥ 391 := staircase_step_K_direct k m 51156 441330 152490 37047 14065 391 heq h_m_mono_179 h_pc_M_179 h_pc_K_prev_179 rfl (by decide)
  have h_pc_K_next_179 : Nat.primeCounting 153272 = 14128 := pc_thm_153272
  have h_pc_M_next_val_179 : Nat.primeCounting 441330 = 37047 := pc_thm_441330
  have h_m_180 : m ≤ 938 := staircase_step_M_direct k m 51156 153272 441330 14128 37047 938 heq (k_mono 391 k h_k_180) h_pc_K_next_179 h_pc_M_next_val_179 rfl (by decide)
  -- Step 180: k >= 391, m <= 938 => k >= 392
  have h_m_mono_180 : m*(m+1)/2 ≤ 440391 := m_mono m 938 h_m_180
  have h_pc_M_180 : Nat.primeCounting 440391 = 36971 := pc_thm_440391
  have h_pc_K_prev_180 : Nat.primeCounting 153272 = 14128 := pc_thm_153272
  have h_k_181 : k ≥ 392 := staircase_step_K_direct k m 51156 440391 153272 36971 14128 392 heq h_m_mono_180 h_pc_M_180 h_pc_K_prev_180 rfl (by decide)
  have h_pc_K_next_180 : Nat.primeCounting 154056 = 14191 := pc_thm_154056
  have h_pc_M_next_val_180 : Nat.primeCounting 440391 = 36971 := pc_thm_440391
  have h_m_181 : m ≤ 937 := staircase_step_M_direct k m 51156 154056 440391 14191 36971 937 heq (k_mono 392 k h_k_181) h_pc_K_next_180 h_pc_M_next_val_180 rfl (by decide)
  exact ⟨h_k_181, h_m_181⟩

theorem staircase_part_12 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_181 : k ≥ 392) (h_m_181 : m ≤ 937) : k ≥ 409 ∧ m ≤ 922 := by
  -- Step 181: k >= 392, m <= 937 => k >= 394
  have h_m_mono_181 : m*(m+1)/2 ≤ 439453 := m_mono m 937 h_m_181
  have h_pc_M_181 : Nat.primeCounting 439453 = 36894 := pc_thm_439453
  have h_pc_K_prev_181 : Nat.primeCounting 154842 = 14260 := pc_thm_154842
  have h_k_182 : k ≥ 394 := staircase_step_K_direct k m 51156 439453 154842 36894 14260 394 heq h_m_mono_181 h_pc_M_181 h_pc_K_prev_181 rfl (by decide)
  have h_pc_K_next_181 : Nat.primeCounting 155630 = 14327 := pc_thm_155630
  have h_pc_M_next_val_181 : Nat.primeCounting 439453 = 36894 := pc_thm_439453
  have h_m_182 : m ≤ 936 := staircase_step_M_direct k m 51156 155630 439453 14327 36894 936 heq (k_mono 394 k h_k_182) h_pc_K_next_181 h_pc_M_next_val_181 rfl (by decide)
  -- Step 182: k >= 394, m <= 936 => k >= 395
  have h_m_mono_182 : m*(m+1)/2 ≤ 438516 := m_mono m 936 h_m_182
  have h_pc_M_182 : Nat.primeCounting 438516 = 36825 := pc_thm_438516
  have h_pc_K_prev_182 : Nat.primeCounting 155630 = 14327 := pc_thm_155630
  have h_k_183 : k ≥ 395 := staircase_step_K_direct k m 51156 438516 155630 36825 14327 395 heq h_m_mono_182 h_pc_M_182 h_pc_K_prev_182 rfl (by decide)
  have h_pc_K_next_182 : Nat.primeCounting 156420 = 14388 := pc_thm_156420
  have h_pc_M_next_val_182 : Nat.primeCounting 438516 = 36825 := pc_thm_438516
  have h_m_183 : m ≤ 935 := staircase_step_M_direct k m 51156 156420 438516 14388 36825 935 heq (k_mono 395 k h_k_183) h_pc_K_next_182 h_pc_M_next_val_182 rfl (by decide)
  -- Step 183: k >= 395, m <= 935 => k >= 396
  have h_m_mono_183 : m*(m+1)/2 ≤ 437580 := m_mono m 935 h_m_183
  have h_pc_M_183 : Nat.primeCounting 437580 = 36764 := pc_thm_437580
  have h_pc_K_prev_183 : Nat.primeCounting 156420 = 14388 := pc_thm_156420
  have h_k_184 : k ≥ 396 := staircase_step_K_direct k m 51156 437580 156420 36764 14388 396 heq h_m_mono_183 h_pc_M_183 h_pc_K_prev_183 rfl (by decide)
  have h_pc_K_next_183 : Nat.primeCounting 157212 = 14453 := pc_thm_157212
  have h_pc_M_next_val_183 : Nat.primeCounting 437580 = 36764 := pc_thm_437580
  have h_m_184 : m ≤ 934 := staircase_step_M_direct k m 51156 157212 437580 14453 36764 934 heq (k_mono 396 k h_k_184) h_pc_K_next_183 h_pc_M_next_val_183 rfl (by decide)
  -- Step 184: k >= 396, m <= 934 => k >= 397
  have h_m_mono_184 : m*(m+1)/2 ≤ 436645 := m_mono m 934 h_m_184
  have h_pc_M_184 : Nat.primeCounting 436645 = 36694 := pc_thm_436645
  have h_pc_K_prev_184 : Nat.primeCounting 157212 = 14453 := pc_thm_157212
  have h_k_185 : k ≥ 397 := staircase_step_K_direct k m 51156 436645 157212 36694 14453 397 heq h_m_mono_184 h_pc_M_184 h_pc_K_prev_184 rfl (by decide)
  have h_pc_K_next_184 : Nat.primeCounting 158006 = 14522 := pc_thm_158006
  have h_pc_M_next_val_184 : Nat.primeCounting 436645 = 36694 := pc_thm_436645
  have h_m_185 : m ≤ 933 := staircase_step_M_direct k m 51156 158006 436645 14522 36694 933 heq (k_mono 397 k h_k_185) h_pc_K_next_184 h_pc_M_next_val_184 rfl (by decide)
  -- Step 185: k >= 397, m <= 933 => k >= 398
  have h_m_mono_185 : m*(m+1)/2 ≤ 435711 := m_mono m 933 h_m_185
  have h_pc_M_185 : Nat.primeCounting 435711 = 36625 := pc_thm_435711
  have h_pc_K_prev_185 : Nat.primeCounting 158006 = 14522 := pc_thm_158006
  have h_k_186 : k ≥ 398 := staircase_step_K_direct k m 51156 435711 158006 36625 14522 398 heq h_m_mono_185 h_pc_M_185 h_pc_K_prev_185 rfl (by decide)
  have h_pc_K_next_185 : Nat.primeCounting 158802 = 14585 := pc_thm_158802
  have h_pc_M_next_val_185 : Nat.primeCounting 435711 = 36625 := pc_thm_435711
  have h_m_186 : m ≤ 932 := staircase_step_M_direct k m 51156 158802 435711 14585 36625 932 heq (k_mono 398 k h_k_186) h_pc_K_next_185 h_pc_M_next_val_185 rfl (by decide)
  -- Step 186: k >= 398, m <= 932 => k >= 399
  have h_m_mono_186 : m*(m+1)/2 ≤ 434778 := m_mono m 932 h_m_186
  have h_pc_M_186 : Nat.primeCounting 434778 = 36541 := pc_thm_434778
  have h_pc_K_prev_186 : Nat.primeCounting 158802 = 14585 := pc_thm_158802
  have h_k_187 : k ≥ 399 := staircase_step_K_direct k m 51156 434778 158802 36541 14585 399 heq h_m_mono_186 h_pc_M_186 h_pc_K_prev_186 rfl (by decide)
  have h_pc_K_next_186 : Nat.primeCounting 159600 = 14648 := pc_thm_159600
  have h_pc_M_next_val_186 : Nat.primeCounting 434778 = 36541 := pc_thm_434778
  have h_m_187 : m ≤ 931 := staircase_step_M_direct k m 51156 159600 434778 14648 36541 931 heq (k_mono 399 k h_k_187) h_pc_K_next_186 h_pc_M_next_val_186 rfl (by decide)
  -- Step 187: k >= 399, m <= 931 => k >= 400
  have h_m_mono_187 : m*(m+1)/2 ≤ 433846 := m_mono m 931 h_m_187
  have h_pc_M_187 : Nat.primeCounting 433846 = 36470 := pc_thm_433846
  have h_pc_K_prev_187 : Nat.primeCounting 159600 = 14648 := pc_thm_159600
  have h_k_188 : k ≥ 400 := staircase_step_K_direct k m 51156 433846 159600 36470 14648 400 heq h_m_mono_187 h_pc_M_187 h_pc_K_prev_187 rfl (by decide)
  have h_pc_K_next_187 : Nat.primeCounting 160400 = 14716 := pc_thm_160400
  have h_pc_M_next_val_187 : Nat.primeCounting 433846 = 36470 := pc_thm_433846
  have h_m_188 : m ≤ 930 := staircase_step_M_direct k m 51156 160400 433846 14716 36470 930 heq (k_mono 400 k h_k_188) h_pc_K_next_187 h_pc_M_next_val_187 rfl (by decide)
  -- Step 188: k >= 400, m <= 930 => k >= 401
  have h_m_mono_188 : m*(m+1)/2 ≤ 432915 := m_mono m 930 h_m_188
  have h_pc_M_188 : Nat.primeCounting 432915 = 36394 := pc_thm_432915
  have h_pc_K_prev_188 : Nat.primeCounting 160400 = 14716 := pc_thm_160400
  have h_k_189 : k ≥ 401 := staircase_step_K_direct k m 51156 432915 160400 36394 14716 401 heq h_m_mono_188 h_pc_M_188 h_pc_K_prev_188 rfl (by decide)
  have h_pc_K_next_188 : Nat.primeCounting 161202 = 14785 := pc_thm_161202
  have h_pc_M_next_val_188 : Nat.primeCounting 432915 = 36394 := pc_thm_432915
  have h_m_189 : m ≤ 929 := staircase_step_M_direct k m 51156 161202 432915 14785 36394 929 heq (k_mono 401 k h_k_189) h_pc_K_next_188 h_pc_M_next_val_188 rfl (by decide)
  -- Step 189: k >= 401, m <= 929 => k >= 402
  have h_m_mono_189 : m*(m+1)/2 ≤ 431985 := m_mono m 929 h_m_189
  have h_pc_M_189 : Nat.primeCounting 431985 = 36316 := pc_thm_431985
  have h_pc_K_prev_189 : Nat.primeCounting 161202 = 14785 := pc_thm_161202
  have h_k_190 : k ≥ 402 := staircase_step_K_direct k m 51156 431985 161202 36316 14785 402 heq h_m_mono_189 h_pc_M_189 h_pc_K_prev_189 rfl (by decide)
  have h_pc_K_next_189 : Nat.primeCounting 162006 = 14852 := pc_thm_162006
  have h_pc_M_next_val_189 : Nat.primeCounting 431985 = 36316 := pc_thm_431985
  have h_m_190 : m ≤ 928 := staircase_step_M_direct k m 51156 162006 431985 14852 36316 928 heq (k_mono 402 k h_k_190) h_pc_K_next_189 h_pc_M_next_val_189 rfl (by decide)
  -- Step 190: k >= 402, m <= 928 => k >= 403
  have h_m_mono_190 : m*(m+1)/2 ≤ 431056 := m_mono m 928 h_m_190
  have h_pc_M_190 : Nat.primeCounting 431056 = 36243 := pc_thm_431056
  have h_pc_K_prev_190 : Nat.primeCounting 162006 = 14852 := pc_thm_162006
  have h_k_191 : k ≥ 403 := staircase_step_K_direct k m 51156 431056 162006 36243 14852 403 heq h_m_mono_190 h_pc_M_190 h_pc_K_prev_190 rfl (by decide)
  have h_pc_K_next_190 : Nat.primeCounting 162812 = 14915 := pc_thm_162812
  have h_pc_M_next_val_190 : Nat.primeCounting 431056 = 36243 := pc_thm_431056
  have h_m_191 : m ≤ 927 := staircase_step_M_direct k m 51156 162812 431056 14915 36243 927 heq (k_mono 403 k h_k_191) h_pc_K_next_190 h_pc_M_next_val_190 rfl (by decide)
  -- Step 191: k >= 403, m <= 927 => k >= 405
  have h_m_mono_191 : m*(m+1)/2 ≤ 430128 := m_mono m 927 h_m_191
  have h_pc_M_191 : Nat.primeCounting 430128 = 36172 := pc_thm_430128
  have h_pc_K_prev_191 : Nat.primeCounting 163620 = 14981 := pc_thm_163620
  have h_k_192 : k ≥ 405 := staircase_step_K_direct k m 51156 430128 163620 36172 14981 405 heq h_m_mono_191 h_pc_M_191 h_pc_K_prev_191 rfl (by decide)
  have h_pc_K_next_191 : Nat.primeCounting 164430 = 15053 := pc_thm_164430
  have h_pc_M_next_val_191 : Nat.primeCounting 430128 = 36172 := pc_thm_430128
  have h_m_192 : m ≤ 926 := staircase_step_M_direct k m 51156 164430 430128 15053 36172 926 heq (k_mono 405 k h_k_192) h_pc_K_next_191 h_pc_M_next_val_191 rfl (by decide)
  -- Step 192: k >= 405, m <= 926 => k >= 406
  have h_m_mono_192 : m*(m+1)/2 ≤ 429201 := m_mono m 926 h_m_192
  have h_pc_M_192 : Nat.primeCounting 429201 = 36086 := pc_thm_429201
  have h_pc_K_prev_192 : Nat.primeCounting 164430 = 15053 := pc_thm_164430
  have h_k_193 : k ≥ 406 := staircase_step_K_direct k m 51156 429201 164430 36086 15053 406 heq h_m_mono_192 h_pc_M_192 h_pc_K_prev_192 rfl (by decide)
  have h_pc_K_next_192 : Nat.primeCounting 165242 = 15111 := pc_thm_165242
  have h_pc_M_next_val_192 : Nat.primeCounting 429201 = 36086 := pc_thm_429201
  have h_m_193 : m ≤ 925 := staircase_step_M_direct k m 51156 165242 429201 15111 36086 925 heq (k_mono 406 k h_k_193) h_pc_K_next_192 h_pc_M_next_val_192 rfl (by decide)
  -- Step 193: k >= 406, m <= 925 => k >= 407
  have h_m_mono_193 : m*(m+1)/2 ≤ 428275 := m_mono m 925 h_m_193
  have h_pc_M_193 : Nat.primeCounting 428275 = 36025 := pc_thm_428275
  have h_pc_K_prev_193 : Nat.primeCounting 165242 = 15111 := pc_thm_165242
  have h_k_194 : k ≥ 407 := staircase_step_K_direct k m 51156 428275 165242 36025 15111 407 heq h_m_mono_193 h_pc_M_193 h_pc_K_prev_193 rfl (by decide)
  have h_pc_K_next_193 : Nat.primeCounting 166056 = 15178 := pc_thm_166056
  have h_pc_M_next_val_193 : Nat.primeCounting 428275 = 36025 := pc_thm_428275
  have h_m_194 : m ≤ 924 := staircase_step_M_direct k m 51156 166056 428275 15178 36025 924 heq (k_mono 407 k h_k_194) h_pc_K_next_193 h_pc_M_next_val_193 rfl (by decide)
  -- Step 194: k >= 407, m <= 924 => k >= 408
  have h_m_mono_194 : m*(m+1)/2 ≤ 427350 := m_mono m 924 h_m_194
  have h_pc_M_194 : Nat.primeCounting 427350 = 35950 := pc_thm_427350
  have h_pc_K_prev_194 : Nat.primeCounting 166056 = 15178 := pc_thm_166056
  have h_k_195 : k ≥ 408 := staircase_step_K_direct k m 51156 427350 166056 35950 15178 408 heq h_m_mono_194 h_pc_M_194 h_pc_K_prev_194 rfl (by decide)
  have h_pc_K_next_194 : Nat.primeCounting 166872 = 15246 := pc_thm_166872
  have h_pc_M_next_val_194 : Nat.primeCounting 427350 = 35950 := pc_thm_427350
  have h_m_195 : m ≤ 923 := staircase_step_M_direct k m 51156 166872 427350 15246 35950 923 heq (k_mono 408 k h_k_195) h_pc_K_next_194 h_pc_M_next_val_194 rfl (by decide)
  -- Step 195: k >= 408, m <= 923 => k >= 409
  have h_m_mono_195 : m*(m+1)/2 ≤ 426426 := m_mono m 923 h_m_195
  have h_pc_M_195 : Nat.primeCounting 426426 = 35881 := pc_thm_426426
  have h_pc_K_prev_195 : Nat.primeCounting 166872 = 15246 := pc_thm_166872
  have h_k_196 : k ≥ 409 := staircase_step_K_direct k m 51156 426426 166872 35881 15246 409 heq h_m_mono_195 h_pc_M_195 h_pc_K_prev_195 rfl (by decide)
  have h_pc_K_next_195 : Nat.primeCounting 167690 = 15316 := pc_thm_167690
  have h_pc_M_next_val_195 : Nat.primeCounting 426426 = 35881 := pc_thm_426426
  have h_m_196 : m ≤ 922 := staircase_step_M_direct k m 51156 167690 426426 15316 35881 922 heq (k_mono 409 k h_k_196) h_pc_K_next_195 h_pc_M_next_val_195 rfl (by decide)
  exact ⟨h_k_196, h_m_196⟩

theorem staircase_part_13 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_196 : k ≥ 409) (h_m_196 : m ≤ 922) : k ≥ 424 ∧ m ≤ 907 := by
  -- Step 196: k >= 409, m <= 922 => k >= 410
  have h_m_mono_196 : m*(m+1)/2 ≤ 425503 := m_mono m 922 h_m_196
  have h_pc_M_196 : Nat.primeCounting 425503 = 35819 := pc_thm_425503
  have h_pc_K_prev_196 : Nat.primeCounting 167690 = 15316 := pc_thm_167690
  have h_k_197 : k ≥ 410 := staircase_step_K_direct k m 51156 425503 167690 35819 15316 410 heq h_m_mono_196 h_pc_M_196 h_pc_K_prev_196 rfl (by decide)
  have h_pc_K_next_196 : Nat.primeCounting 168510 = 15375 := pc_thm_168510
  have h_pc_M_next_val_196 : Nat.primeCounting 425503 = 35819 := pc_thm_425503
  have h_m_197 : m ≤ 921 := staircase_step_M_direct k m 51156 168510 425503 15375 35819 921 heq (k_mono 410 k h_k_197) h_pc_K_next_196 h_pc_M_next_val_196 rfl (by decide)
  -- Step 197: k >= 410, m <= 921 => k >= 411
  have h_m_mono_197 : m*(m+1)/2 ≤ 424581 := m_mono m 921 h_m_197
  have h_pc_M_197 : Nat.primeCounting 424581 = 35746 := pc_thm_424581
  have h_pc_K_prev_197 : Nat.primeCounting 168510 = 15375 := pc_thm_168510
  have h_k_198 : k ≥ 411 := staircase_step_K_direct k m 51156 424581 168510 35746 15375 411 heq h_m_mono_197 h_pc_M_197 h_pc_K_prev_197 rfl (by decide)
  have h_pc_K_next_197 : Nat.primeCounting 169332 = 15440 := pc_thm_169332
  have h_pc_M_next_val_197 : Nat.primeCounting 424581 = 35746 := pc_thm_424581
  have h_m_198 : m ≤ 920 := staircase_step_M_direct k m 51156 169332 424581 15440 35746 920 heq (k_mono 411 k h_k_198) h_pc_K_next_197 h_pc_M_next_val_197 rfl (by decide)
  -- Step 198: k >= 411, m <= 920 => k >= 412
  have h_m_mono_198 : m*(m+1)/2 ≤ 423660 := m_mono m 920 h_m_198
  have h_pc_M_198 : Nat.primeCounting 423660 = 35672 := pc_thm_423660
  have h_pc_K_prev_198 : Nat.primeCounting 169332 = 15440 := pc_thm_169332
  have h_k_199 : k ≥ 412 := staircase_step_K_direct k m 51156 423660 169332 35672 15440 412 heq h_m_mono_198 h_pc_M_198 h_pc_K_prev_198 rfl (by decide)
  have h_pc_K_next_198 : Nat.primeCounting 170156 = 15509 := pc_thm_170156
  have h_pc_M_next_val_198 : Nat.primeCounting 423660 = 35672 := pc_thm_423660
  have h_m_199 : m ≤ 919 := staircase_step_M_direct k m 51156 170156 423660 15509 35672 919 heq (k_mono 412 k h_k_199) h_pc_K_next_198 h_pc_M_next_val_198 rfl (by decide)
  -- Step 199: k >= 412, m <= 919 => k >= 413
  have h_m_mono_199 : m*(m+1)/2 ≤ 422740 := m_mono m 919 h_m_199
  have h_pc_M_199 : Nat.primeCounting 422740 = 35593 := pc_thm_422740
  have h_pc_K_prev_199 : Nat.primeCounting 170156 = 15509 := pc_thm_170156
  have h_k_200 : k ≥ 413 := staircase_step_K_direct k m 51156 422740 170156 35593 15509 413 heq h_m_mono_199 h_pc_M_199 h_pc_K_prev_199 rfl (by decide)
  have h_pc_K_next_199 : Nat.primeCounting 170982 = 15584 := pc_thm_170982
  have h_pc_M_next_val_199 : Nat.primeCounting 422740 = 35593 := pc_thm_422740
  have h_m_200 : m ≤ 918 := staircase_step_M_direct k m 51156 170982 422740 15584 35593 918 heq (k_mono 413 k h_k_200) h_pc_K_next_199 h_pc_M_next_val_199 rfl (by decide)
  -- Step 200: k >= 413, m <= 918 => k >= 414
  have h_m_mono_200 : m*(m+1)/2 ≤ 421821 := m_mono m 918 h_m_200
  have h_pc_M_200 : Nat.primeCounting 421821 = 35529 := pc_thm_421821
  have h_pc_K_prev_200 : Nat.primeCounting 170982 = 15584 := pc_thm_170982
  have h_k_201 : k ≥ 414 := staircase_step_K_direct k m 51156 421821 170982 35529 15584 414 heq h_m_mono_200 h_pc_M_200 h_pc_K_prev_200 rfl (by decide)
  have h_pc_K_next_200 : Nat.primeCounting 171810 = 15651 := pc_thm_171810
  have h_pc_M_next_val_200 : Nat.primeCounting 421821 = 35529 := pc_thm_421821
  have h_m_201 : m ≤ 917 := staircase_step_M_direct k m 51156 171810 421821 15651 35529 917 heq (k_mono 414 k h_k_201) h_pc_K_next_200 h_pc_M_next_val_200 rfl (by decide)
  -- Step 201: k >= 414, m <= 917 => k >= 415
  have h_m_mono_201 : m*(m+1)/2 ≤ 420903 := m_mono m 917 h_m_201
  have h_pc_M_201 : Nat.primeCounting 420903 = 35459 := pc_thm_420903
  have h_pc_K_prev_201 : Nat.primeCounting 171810 = 15651 := pc_thm_171810
  have h_k_202 : k ≥ 415 := staircase_step_K_direct k m 51156 420903 171810 35459 15651 415 heq h_m_mono_201 h_pc_M_201 h_pc_K_prev_201 rfl (by decide)
  have h_pc_K_next_201 : Nat.primeCounting 172640 = 15723 := pc_thm_172640
  have h_pc_M_next_val_201 : Nat.primeCounting 420903 = 35459 := pc_thm_420903
  have h_m_202 : m ≤ 916 := staircase_step_M_direct k m 51156 172640 420903 15723 35459 916 heq (k_mono 415 k h_k_202) h_pc_K_next_201 h_pc_M_next_val_201 rfl (by decide)
  -- Step 202: k >= 415, m <= 916 => k >= 416
  have h_m_mono_202 : m*(m+1)/2 ≤ 419986 := m_mono m 916 h_m_202
  have h_pc_M_202 : Nat.primeCounting 419986 = 35389 := pc_thm_419986
  have h_pc_K_prev_202 : Nat.primeCounting 172640 = 15723 := pc_thm_172640
  have h_k_203 : k ≥ 416 := staircase_step_K_direct k m 51156 419986 172640 35389 15723 416 heq h_m_mono_202 h_pc_M_202 h_pc_K_prev_202 rfl (by decide)
  have h_pc_K_next_202 : Nat.primeCounting 173472 = 15785 := pc_thm_173472
  have h_pc_M_next_val_202 : Nat.primeCounting 419986 = 35389 := pc_thm_419986
  have h_m_203 : m ≤ 915 := staircase_step_M_direct k m 51156 173472 419986 15785 35389 915 heq (k_mono 416 k h_k_203) h_pc_K_next_202 h_pc_M_next_val_202 rfl (by decide)
  -- Step 203: k >= 416, m <= 915 => k >= 417
  have h_m_mono_203 : m*(m+1)/2 ≤ 419070 := m_mono m 915 h_m_203
  have h_pc_M_203 : Nat.primeCounting 419070 = 35320 := pc_thm_419070
  have h_pc_K_prev_203 : Nat.primeCounting 173472 = 15785 := pc_thm_173472
  have h_k_204 : k ≥ 417 := staircase_step_K_direct k m 51156 419070 173472 35320 15785 417 heq h_m_mono_203 h_pc_M_203 h_pc_K_prev_203 rfl (by decide)
  have h_pc_K_next_203 : Nat.primeCounting 174306 = 15860 := pc_thm_174306
  have h_pc_M_next_val_203 : Nat.primeCounting 419070 = 35320 := pc_thm_419070
  have h_m_204 : m ≤ 914 := staircase_step_M_direct k m 51156 174306 419070 15860 35320 914 heq (k_mono 417 k h_k_204) h_pc_K_next_203 h_pc_M_next_val_203 rfl (by decide)
  -- Step 204: k >= 417, m <= 914 => k >= 418
  have h_m_mono_204 : m*(m+1)/2 ≤ 418155 := m_mono m 914 h_m_204
  have h_pc_M_204 : Nat.primeCounting 418155 = 35242 := pc_thm_418155
  have h_pc_K_prev_204 : Nat.primeCounting 174306 = 15860 := pc_thm_174306
  have h_k_205 : k ≥ 418 := staircase_step_K_direct k m 51156 418155 174306 35242 15860 418 heq h_m_mono_204 h_pc_M_204 h_pc_K_prev_204 rfl (by decide)
  have h_pc_K_next_204 : Nat.primeCounting 175142 = 15927 := pc_thm_175142
  have h_pc_M_next_val_204 : Nat.primeCounting 418155 = 35242 := pc_thm_418155
  have h_m_205 : m ≤ 913 := staircase_step_M_direct k m 51156 175142 418155 15927 35242 913 heq (k_mono 418 k h_k_205) h_pc_K_next_204 h_pc_M_next_val_204 rfl (by decide)
  -- Step 205: k >= 418, m <= 913 => k >= 419
  have h_m_mono_205 : m*(m+1)/2 ≤ 417241 := m_mono m 913 h_m_205
  have h_pc_M_205 : Nat.primeCounting 417241 = 35169 := pc_thm_417241
  have h_pc_K_prev_205 : Nat.primeCounting 175142 = 15927 := pc_thm_175142
  have h_k_206 : k ≥ 419 := staircase_step_K_direct k m 51156 417241 175142 35169 15927 419 heq h_m_mono_205 h_pc_M_205 h_pc_K_prev_205 rfl (by decide)
  have h_pc_K_next_205 : Nat.primeCounting 175980 = 15989 := pc_thm_175980
  have h_pc_M_next_val_205 : Nat.primeCounting 417241 = 35169 := pc_thm_417241
  have h_m_206 : m ≤ 912 := staircase_step_M_direct k m 51156 175980 417241 15989 35169 912 heq (k_mono 419 k h_k_206) h_pc_K_next_205 h_pc_M_next_val_205 rfl (by decide)
  -- Step 206: k >= 419, m <= 912 => k >= 420
  have h_m_mono_206 : m*(m+1)/2 ≤ 416328 := m_mono m 912 h_m_206
  have h_pc_M_206 : Nat.primeCounting 416328 = 35101 := pc_thm_416328
  have h_pc_K_prev_206 : Nat.primeCounting 175980 = 15989 := pc_thm_175980
  have h_k_207 : k ≥ 420 := staircase_step_K_direct k m 51156 416328 175980 35101 15989 420 heq h_m_mono_206 h_pc_M_206 h_pc_K_prev_206 rfl (by decide)
  have h_pc_K_next_206 : Nat.primeCounting 176820 = 16073 := pc_thm_176820
  have h_pc_M_next_val_206 : Nat.primeCounting 416328 = 35101 := pc_thm_416328
  have h_m_207 : m ≤ 911 := staircase_step_M_direct k m 51156 176820 416328 16073 35101 911 heq (k_mono 420 k h_k_207) h_pc_K_next_206 h_pc_M_next_val_206 rfl (by decide)
  -- Step 207: k >= 420, m <= 911 => k >= 421
  have h_m_mono_207 : m*(m+1)/2 ≤ 415416 := m_mono m 911 h_m_207
  have h_pc_M_207 : Nat.primeCounting 415416 = 35031 := pc_thm_415416
  have h_pc_K_prev_207 : Nat.primeCounting 176820 = 16073 := pc_thm_176820
  have h_k_208 : k ≥ 421 := staircase_step_K_direct k m 51156 415416 176820 35031 16073 421 heq h_m_mono_207 h_pc_M_207 h_pc_K_prev_207 rfl (by decide)
  have h_pc_K_next_207 : Nat.primeCounting 177662 = 16132 := pc_thm_177662
  have h_pc_M_next_val_207 : Nat.primeCounting 415416 = 35031 := pc_thm_415416
  have h_m_208 : m ≤ 910 := staircase_step_M_direct k m 51156 177662 415416 16132 35031 910 heq (k_mono 421 k h_k_208) h_pc_K_next_207 h_pc_M_next_val_207 rfl (by decide)
  -- Step 208: k >= 421, m <= 910 => k >= 422
  have h_m_mono_208 : m*(m+1)/2 ≤ 414505 := m_mono m 910 h_m_208
  have h_pc_M_208 : Nat.primeCounting 414505 = 34956 := pc_thm_414505
  have h_pc_K_prev_208 : Nat.primeCounting 177662 = 16132 := pc_thm_177662
  have h_k_209 : k ≥ 422 := staircase_step_K_direct k m 51156 414505 177662 34956 16132 422 heq h_m_mono_208 h_pc_M_208 h_pc_K_prev_208 rfl (by decide)
  have h_pc_K_next_208 : Nat.primeCounting 178506 = 16202 := pc_thm_178506
  have h_pc_M_next_val_208 : Nat.primeCounting 414505 = 34956 := pc_thm_414505
  have h_m_209 : m ≤ 909 := staircase_step_M_direct k m 51156 178506 414505 16202 34956 909 heq (k_mono 422 k h_k_209) h_pc_K_next_208 h_pc_M_next_val_208 rfl (by decide)
  -- Step 209: k >= 422, m <= 909 => k >= 423
  have h_m_mono_209 : m*(m+1)/2 ≤ 413595 := m_mono m 909 h_m_209
  have h_pc_M_209 : Nat.primeCounting 413595 = 34885 := pc_thm_413595
  have h_pc_K_prev_209 : Nat.primeCounting 178506 = 16202 := pc_thm_178506
  have h_k_210 : k ≥ 423 := staircase_step_K_direct k m 51156 413595 178506 34885 16202 423 heq h_m_mono_209 h_pc_M_209 h_pc_K_prev_209 rfl (by decide)
  have h_pc_K_next_209 : Nat.primeCounting 179352 = 16277 := pc_thm_179352
  have h_pc_M_next_val_209 : Nat.primeCounting 413595 = 34885 := pc_thm_413595
  have h_m_210 : m ≤ 908 := staircase_step_M_direct k m 51156 179352 413595 16277 34885 908 heq (k_mono 423 k h_k_210) h_pc_K_next_209 h_pc_M_next_val_209 rfl (by decide)
  -- Step 210: k >= 423, m <= 908 => k >= 424
  have h_m_mono_210 : m*(m+1)/2 ≤ 412686 := m_mono m 908 h_m_210
  have h_pc_M_210 : Nat.primeCounting 412686 = 34826 := pc_thm_412686
  have h_pc_K_prev_210 : Nat.primeCounting 179352 = 16277 := pc_thm_179352
  have h_k_211 : k ≥ 424 := staircase_step_K_direct k m 51156 412686 179352 34826 16277 424 heq h_m_mono_210 h_pc_M_210 h_pc_K_prev_210 rfl (by decide)
  have h_pc_K_next_210 : Nat.primeCounting 180200 = 16355 := pc_thm_180200
  have h_pc_M_next_val_210 : Nat.primeCounting 412686 = 34826 := pc_thm_412686
  have h_m_211 : m ≤ 907 := staircase_step_M_direct k m 51156 180200 412686 16355 34826 907 heq (k_mono 424 k h_k_211) h_pc_K_next_210 h_pc_M_next_val_210 rfl (by decide)
  exact ⟨h_k_211, h_m_211⟩

theorem staircase_part_14 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_211 : k ≥ 424) (h_m_211 : m ≤ 907) : k ≥ 439 ∧ m ≤ 892 := by
  -- Step 211: k >= 424, m <= 907 => k >= 425
  have h_m_mono_211 : m*(m+1)/2 ≤ 411778 := m_mono m 907 h_m_211
  have h_pc_M_211 : Nat.primeCounting 411778 = 34753 := pc_thm_411778
  have h_pc_K_prev_211 : Nat.primeCounting 180200 = 16355 := pc_thm_180200
  have h_k_212 : k ≥ 425 := staircase_step_K_direct k m 51156 411778 180200 34753 16355 425 heq h_m_mono_211 h_pc_M_211 h_pc_K_prev_211 rfl (by decide)
  have h_pc_K_next_211 : Nat.primeCounting 181050 = 16418 := pc_thm_181050
  have h_pc_M_next_val_211 : Nat.primeCounting 411778 = 34753 := pc_thm_411778
  have h_m_212 : m ≤ 906 := staircase_step_M_direct k m 51156 181050 411778 16418 34753 906 heq (k_mono 425 k h_k_212) h_pc_K_next_211 h_pc_M_next_val_211 rfl (by decide)
  -- Step 212: k >= 425, m <= 906 => k >= 426
  have h_m_mono_212 : m*(m+1)/2 ≤ 410871 := m_mono m 906 h_m_212
  have h_pc_M_212 : Nat.primeCounting 410871 = 34681 := pc_thm_410871
  have h_pc_K_prev_212 : Nat.primeCounting 181050 = 16418 := pc_thm_181050
  have h_k_213 : k ≥ 426 := staircase_step_K_direct k m 51156 410871 181050 34681 16418 426 heq h_m_mono_212 h_pc_M_212 h_pc_K_prev_212 rfl (by decide)
  have h_pc_K_next_212 : Nat.primeCounting 181902 = 16482 := pc_thm_181902
  have h_pc_M_next_val_212 : Nat.primeCounting 410871 = 34681 := pc_thm_410871
  have h_m_213 : m ≤ 905 := staircase_step_M_direct k m 51156 181902 410871 16482 34681 905 heq (k_mono 426 k h_k_213) h_pc_K_next_212 h_pc_M_next_val_212 rfl (by decide)
  -- Step 213: k >= 426, m <= 905 => k >= 427
  have h_m_mono_213 : m*(m+1)/2 ≤ 409965 := m_mono m 905 h_m_213
  have h_pc_M_213 : Nat.primeCounting 409965 = 34610 := pc_thm_409965
  have h_pc_K_prev_213 : Nat.primeCounting 181902 = 16482 := pc_thm_181902
  have h_k_214 : k ≥ 427 := staircase_step_K_direct k m 51156 409965 181902 34610 16482 427 heq h_m_mono_213 h_pc_M_213 h_pc_K_prev_213 rfl (by decide)
  have h_pc_K_next_213 : Nat.primeCounting 182756 = 16561 := pc_thm_182756
  have h_pc_M_next_val_213 : Nat.primeCounting 409965 = 34610 := pc_thm_409965
  have h_m_214 : m ≤ 904 := staircase_step_M_direct k m 51156 182756 409965 16561 34610 904 heq (k_mono 427 k h_k_214) h_pc_K_next_213 h_pc_M_next_val_213 rfl (by decide)
  -- Step 214: k >= 427, m <= 904 => k >= 428
  have h_m_mono_214 : m*(m+1)/2 ≤ 409060 := m_mono m 904 h_m_214
  have h_pc_M_214 : Nat.primeCounting 409060 = 34537 := pc_thm_409060
  have h_pc_K_prev_214 : Nat.primeCounting 182756 = 16561 := pc_thm_182756
  have h_k_215 : k ≥ 428 := staircase_step_K_direct k m 51156 409060 182756 34537 16561 428 heq h_m_mono_214 h_pc_M_214 h_pc_K_prev_214 rfl (by decide)
  have h_pc_K_next_214 : Nat.primeCounting 183612 = 16636 := pc_thm_183612
  have h_pc_M_next_val_214 : Nat.primeCounting 409060 = 34537 := pc_thm_409060
  have h_m_215 : m ≤ 903 := staircase_step_M_direct k m 51156 183612 409060 16636 34537 903 heq (k_mono 428 k h_k_215) h_pc_K_next_214 h_pc_M_next_val_214 rfl (by decide)
  -- Step 215: k >= 428, m <= 903 => k >= 429
  have h_m_mono_215 : m*(m+1)/2 ≤ 408156 := m_mono m 903 h_m_215
  have h_pc_M_215 : Nat.primeCounting 408156 = 34463 := pc_thm_408156
  have h_pc_K_prev_215 : Nat.primeCounting 183612 = 16636 := pc_thm_183612
  have h_k_216 : k ≥ 429 := staircase_step_K_direct k m 51156 408156 183612 34463 16636 429 heq h_m_mono_215 h_pc_M_215 h_pc_K_prev_215 rfl (by decide)
  have h_pc_K_next_215 : Nat.primeCounting 184470 = 16700 := pc_thm_184470
  have h_pc_M_next_val_215 : Nat.primeCounting 408156 = 34463 := pc_thm_408156
  have h_m_216 : m ≤ 902 := staircase_step_M_direct k m 51156 184470 408156 16700 34463 902 heq (k_mono 429 k h_k_216) h_pc_K_next_215 h_pc_M_next_val_215 rfl (by decide)
  -- Step 216: k >= 429, m <= 902 => k >= 430
  have h_m_mono_216 : m*(m+1)/2 ≤ 407253 := m_mono m 902 h_m_216
  have h_pc_M_216 : Nat.primeCounting 407253 = 34389 := pc_thm_407253
  have h_pc_K_prev_216 : Nat.primeCounting 184470 = 16700 := pc_thm_184470
  have h_k_217 : k ≥ 430 := staircase_step_K_direct k m 51156 407253 184470 34389 16700 430 heq h_m_mono_216 h_pc_M_216 h_pc_K_prev_216 rfl (by decide)
  have h_pc_K_next_216 : Nat.primeCounting 185330 = 16775 := pc_thm_185330
  have h_pc_M_next_val_216 : Nat.primeCounting 407253 = 34389 := pc_thm_407253
  have h_m_217 : m ≤ 901 := staircase_step_M_direct k m 51156 185330 407253 16775 34389 901 heq (k_mono 430 k h_k_217) h_pc_K_next_216 h_pc_M_next_val_216 rfl (by decide)
  -- Step 217: k >= 430, m <= 901 => k >= 431
  have h_m_mono_217 : m*(m+1)/2 ≤ 406351 := m_mono m 901 h_m_217
  have h_pc_M_217 : Nat.primeCounting 406351 = 34328 := pc_thm_406351
  have h_pc_K_prev_217 : Nat.primeCounting 185330 = 16775 := pc_thm_185330
  have h_k_218 : k ≥ 431 := staircase_step_K_direct k m 51156 406351 185330 34328 16775 431 heq h_m_mono_217 h_pc_M_217 h_pc_K_prev_217 rfl (by decide)
  have h_pc_K_next_217 : Nat.primeCounting 186192 = 16855 := pc_thm_186192
  have h_pc_M_next_val_217 : Nat.primeCounting 406351 = 34328 := pc_thm_406351
  have h_m_218 : m ≤ 900 := staircase_step_M_direct k m 51156 186192 406351 16855 34328 900 heq (k_mono 431 k h_k_218) h_pc_K_next_217 h_pc_M_next_val_217 rfl (by decide)
  -- Step 218: k >= 431, m <= 900 => k >= 432
  have h_m_mono_218 : m*(m+1)/2 ≤ 405450 := m_mono m 900 h_m_218
  have h_pc_M_218 : Nat.primeCounting 405450 = 34257 := pc_thm_405450
  have h_pc_K_prev_218 : Nat.primeCounting 186192 = 16855 := pc_thm_186192
  have h_k_219 : k ≥ 432 := staircase_step_K_direct k m 51156 405450 186192 34257 16855 432 heq h_m_mono_218 h_pc_M_218 h_pc_K_prev_218 rfl (by decide)
  have h_pc_K_next_218 : Nat.primeCounting 187056 = 16920 := pc_thm_187056
  have h_pc_M_next_val_218 : Nat.primeCounting 405450 = 34257 := pc_thm_405450
  have h_m_219 : m ≤ 899 := staircase_step_M_direct k m 51156 187056 405450 16920 34257 899 heq (k_mono 432 k h_k_219) h_pc_K_next_218 h_pc_M_next_val_218 rfl (by decide)
  -- Step 219: k >= 432, m <= 899 => k >= 433
  have h_m_mono_219 : m*(m+1)/2 ≤ 404550 := m_mono m 899 h_m_219
  have h_pc_M_219 : Nat.primeCounting 404550 = 34200 := pc_thm_404550
  have h_pc_K_prev_219 : Nat.primeCounting 187056 = 16920 := pc_thm_187056
  have h_k_220 : k ≥ 433 := staircase_step_K_direct k m 51156 404550 187056 34200 16920 433 heq h_m_mono_219 h_pc_M_219 h_pc_K_prev_219 rfl (by decide)
  have h_pc_K_next_219 : Nat.primeCounting 187922 = 16996 := pc_thm_187922
  have h_pc_M_next_val_219 : Nat.primeCounting 404550 = 34200 := pc_thm_404550
  have h_m_220 : m ≤ 898 := staircase_step_M_direct k m 51156 187922 404550 16996 34200 898 heq (k_mono 433 k h_k_220) h_pc_K_next_219 h_pc_M_next_val_219 rfl (by decide)
  -- Step 220: k >= 433, m <= 898 => k >= 434
  have h_m_mono_220 : m*(m+1)/2 ≤ 403651 := m_mono m 898 h_m_220
  have h_pc_M_220 : Nat.primeCounting 403651 = 34125 := pc_thm_403651
  have h_pc_K_prev_220 : Nat.primeCounting 187922 = 16996 := pc_thm_187922
  have h_k_221 : k ≥ 434 := staircase_step_K_direct k m 51156 403651 187922 34125 16996 434 heq h_m_mono_220 h_pc_M_220 h_pc_K_prev_220 rfl (by decide)
  have h_pc_K_next_220 : Nat.primeCounting 188790 = 17062 := pc_thm_188790
  have h_pc_M_next_val_220 : Nat.primeCounting 403651 = 34125 := pc_thm_403651
  have h_m_221 : m ≤ 897 := staircase_step_M_direct k m 51156 188790 403651 17062 34125 897 heq (k_mono 434 k h_k_221) h_pc_K_next_220 h_pc_M_next_val_220 rfl (by decide)
  -- Step 221: k >= 434, m <= 897 => k >= 435
  have h_m_mono_221 : m*(m+1)/2 ≤ 402753 := m_mono m 897 h_m_221
  have h_pc_M_221 : Nat.primeCounting 402753 = 34057 := pc_thm_402753
  have h_pc_K_prev_221 : Nat.primeCounting 188790 = 17062 := pc_thm_188790
  have h_k_222 : k ≥ 435 := staircase_step_K_direct k m 51156 402753 188790 34057 17062 435 heq h_m_mono_221 h_pc_M_221 h_pc_K_prev_221 rfl (by decide)
  have h_pc_K_next_221 : Nat.primeCounting 189660 = 17139 := pc_thm_189660
  have h_pc_M_next_val_221 : Nat.primeCounting 402753 = 34057 := pc_thm_402753
  have h_m_222 : m ≤ 896 := staircase_step_M_direct k m 51156 189660 402753 17139 34057 896 heq (k_mono 435 k h_k_222) h_pc_K_next_221 h_pc_M_next_val_221 rfl (by decide)
  -- Step 222: k >= 435, m <= 896 => k >= 436
  have h_m_mono_222 : m*(m+1)/2 ≤ 401856 := m_mono m 896 h_m_222
  have h_pc_M_222 : Nat.primeCounting 401856 = 33988 := pc_thm_401856
  have h_pc_K_prev_222 : Nat.primeCounting 189660 = 17139 := pc_thm_189660
  have h_k_223 : k ≥ 436 := staircase_step_K_direct k m 51156 401856 189660 33988 17139 436 heq h_m_mono_222 h_pc_M_222 h_pc_K_prev_222 rfl (by decide)
  have h_pc_K_next_222 : Nat.primeCounting 190532 = 17204 := pc_thm_190532
  have h_pc_M_next_val_222 : Nat.primeCounting 401856 = 33988 := pc_thm_401856
  have h_m_223 : m ≤ 895 := staircase_step_M_direct k m 51156 190532 401856 17204 33988 895 heq (k_mono 436 k h_k_223) h_pc_K_next_222 h_pc_M_next_val_222 rfl (by decide)
  -- Step 223: k >= 436, m <= 895 => k >= 437
  have h_m_mono_223 : m*(m+1)/2 ≤ 400960 := m_mono m 895 h_m_223
  have h_pc_M_223 : Nat.primeCounting 400960 = 33928 := pc_thm_400960
  have h_pc_K_prev_223 : Nat.primeCounting 190532 = 17204 := pc_thm_190532
  have h_k_224 : k ≥ 437 := staircase_step_K_direct k m 51156 400960 190532 33928 17204 437 heq h_m_mono_223 h_pc_M_223 h_pc_K_prev_223 rfl (by decide)
  have h_pc_K_next_223 : Nat.primeCounting 191406 = 17273 := pc_thm_191406
  have h_pc_M_next_val_223 : Nat.primeCounting 400960 = 33928 := pc_thm_400960
  have h_m_224 : m ≤ 894 := staircase_step_M_direct k m 51156 191406 400960 17273 33928 894 heq (k_mono 437 k h_k_224) h_pc_K_next_223 h_pc_M_next_val_223 rfl (by decide)
  -- Step 224: k >= 437, m <= 894 => k >= 438
  have h_m_mono_224 : m*(m+1)/2 ≤ 400065 := m_mono m 894 h_m_224
  have h_pc_M_224 : Nat.primeCounting 400065 = 33864 := pc_thm_400065
  have h_pc_K_prev_224 : Nat.primeCounting 191406 = 17273 := pc_thm_191406
  have h_k_225 : k ≥ 438 := staircase_step_K_direct k m 51156 400065 191406 33864 17273 438 heq h_m_mono_224 h_pc_M_224 h_pc_K_prev_224 rfl (by decide)
  have h_pc_K_next_224 : Nat.primeCounting 192282 = 17352 := pc_thm_192282
  have h_pc_M_next_val_224 : Nat.primeCounting 400065 = 33864 := pc_thm_400065
  have h_m_225 : m ≤ 893 := staircase_step_M_direct k m 51156 192282 400065 17352 33864 893 heq (k_mono 438 k h_k_225) h_pc_K_next_224 h_pc_M_next_val_224 rfl (by decide)
  -- Step 225: k >= 438, m <= 893 => k >= 439
  have h_m_mono_225 : m*(m+1)/2 ≤ 399171 := m_mono m 893 h_m_225
  have h_pc_M_225 : Nat.primeCounting 399171 = 33794 := pc_thm_399171
  have h_pc_K_prev_225 : Nat.primeCounting 192282 = 17352 := pc_thm_192282
  have h_k_226 : k ≥ 439 := staircase_step_K_direct k m 51156 399171 192282 33794 17352 439 heq h_m_mono_225 h_pc_M_225 h_pc_K_prev_225 rfl (by decide)
  have h_pc_K_next_225 : Nat.primeCounting 193160 = 17428 := pc_thm_193160
  have h_pc_M_next_val_225 : Nat.primeCounting 399171 = 33794 := pc_thm_399171
  have h_m_226 : m ≤ 892 := staircase_step_M_direct k m 51156 193160 399171 17428 33794 892 heq (k_mono 439 k h_k_226) h_pc_K_next_225 h_pc_M_next_val_225 rfl (by decide)
  exact ⟨h_k_226, h_m_226⟩

theorem staircase_part_15 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_226 : k ≥ 439) (h_m_226 : m ≤ 892) : k ≥ 454 ∧ m ≤ 876 := by
  -- Step 226: k >= 439, m <= 892 => k >= 440
  have h_m_mono_226 : m*(m+1)/2 ≤ 398278 := m_mono m 892 h_m_226
  have h_pc_M_226 : Nat.primeCounting 398278 = 33722 := pc_thm_398278
  have h_pc_K_prev_226 : Nat.primeCounting 193160 = 17428 := pc_thm_193160
  have h_k_227 : k ≥ 440 := staircase_step_K_direct k m 51156 398278 193160 33722 17428 440 heq h_m_mono_226 h_pc_M_226 h_pc_K_prev_226 rfl (by decide)
  have h_pc_K_next_226 : Nat.primeCounting 194040 = 17502 := pc_thm_194040
  have h_pc_M_next_val_226 : Nat.primeCounting 398278 = 33722 := pc_thm_398278
  have h_m_227 : m ≤ 891 := staircase_step_M_direct k m 51156 194040 398278 17502 33722 891 heq (k_mono 440 k h_k_227) h_pc_K_next_226 h_pc_M_next_val_226 rfl (by decide)
  -- Step 227: k >= 440, m <= 891 => k >= 441
  have h_m_mono_227 : m*(m+1)/2 ≤ 397386 := m_mono m 891 h_m_227
  have h_pc_M_227 : Nat.primeCounting 397386 = 33653 := pc_thm_397386
  have h_pc_K_prev_227 : Nat.primeCounting 194040 = 17502 := pc_thm_194040
  have h_k_228 : k ≥ 441 := staircase_step_K_direct k m 51156 397386 194040 33653 17502 441 heq h_m_mono_227 h_pc_M_227 h_pc_K_prev_227 rfl (by decide)
  have h_pc_K_next_227 : Nat.primeCounting 194922 = 17568 := pc_thm_194922
  have h_pc_M_next_val_227 : Nat.primeCounting 397386 = 33653 := pc_thm_397386
  have h_m_228 : m ≤ 890 := staircase_step_M_direct k m 51156 194922 397386 17568 33653 890 heq (k_mono 441 k h_k_228) h_pc_K_next_227 h_pc_M_next_val_227 rfl (by decide)
  -- Step 228: k >= 441, m <= 890 => k >= 442
  have h_m_mono_228 : m*(m+1)/2 ≤ 396495 := m_mono m 890 h_m_228
  have h_pc_M_228 : Nat.primeCounting 396495 = 33585 := pc_thm_396495
  have h_pc_K_prev_228 : Nat.primeCounting 194922 = 17568 := pc_thm_194922
  have h_k_229 : k ≥ 442 := staircase_step_K_direct k m 51156 396495 194922 33585 17568 442 heq h_m_mono_228 h_pc_M_228 h_pc_K_prev_228 rfl (by decide)
  have h_pc_K_next_228 : Nat.primeCounting 195806 = 17640 := pc_thm_195806
  have h_pc_M_next_val_228 : Nat.primeCounting 395605 = 33522 := pc_thm_395605
  have h_m_229 : m ≤ 888 := staircase_step_M_direct k m 51156 195806 395605 17640 33522 888 heq (k_mono 442 k h_k_229) h_pc_K_next_228 h_pc_M_next_val_228 rfl (by decide)
  -- Step 229: k >= 442, m <= 888 => k >= 443
  have h_m_mono_229 : m*(m+1)/2 ≤ 394716 := m_mono m 888 h_m_229
  have h_pc_M_229 : Nat.primeCounting 394716 = 33449 := pc_thm_394716
  have h_pc_K_prev_229 : Nat.primeCounting 195806 = 17640 := pc_thm_195806
  have h_k_230 : k ≥ 443 := staircase_step_K_direct k m 51156 394716 195806 33449 17640 443 heq h_m_mono_229 h_pc_M_229 h_pc_K_prev_229 rfl (by decide)
  have h_pc_K_next_229 : Nat.primeCounting 196692 = 17711 := pc_thm_196692
  have h_pc_M_next_val_229 : Nat.primeCounting 394716 = 33449 := pc_thm_394716
  have h_m_230 : m ≤ 887 := staircase_step_M_direct k m 51156 196692 394716 17711 33449 887 heq (k_mono 443 k h_k_230) h_pc_K_next_229 h_pc_M_next_val_229 rfl (by decide)
  -- Step 230: k >= 443, m <= 887 => k >= 444
  have h_m_mono_230 : m*(m+1)/2 ≤ 393828 := m_mono m 887 h_m_230
  have h_pc_M_230 : Nat.primeCounting 393828 = 33385 := pc_thm_393828
  have h_pc_K_prev_230 : Nat.primeCounting 196692 = 17711 := pc_thm_196692
  have h_k_231 : k ≥ 444 := staircase_step_K_direct k m 51156 393828 196692 33385 17711 444 heq h_m_mono_230 h_pc_M_230 h_pc_K_prev_230 rfl (by decide)
  have h_pc_K_next_230 : Nat.primeCounting 197580 = 17785 := pc_thm_197580
  have h_pc_M_next_val_230 : Nat.primeCounting 393828 = 33385 := pc_thm_393828
  have h_m_231 : m ≤ 886 := staircase_step_M_direct k m 51156 197580 393828 17785 33385 886 heq (k_mono 444 k h_k_231) h_pc_K_next_230 h_pc_M_next_val_230 rfl (by decide)
  -- Step 231: k >= 444, m <= 886 => k >= 445
  have h_m_mono_231 : m*(m+1)/2 ≤ 392941 := m_mono m 886 h_m_231
  have h_pc_M_231 : Nat.primeCounting 392941 = 33308 := pc_thm_392941
  have h_pc_K_prev_231 : Nat.primeCounting 197580 = 17785 := pc_thm_197580
  have h_k_232 : k ≥ 445 := staircase_step_K_direct k m 51156 392941 197580 33308 17785 445 heq h_m_mono_231 h_pc_M_231 h_pc_K_prev_231 rfl (by decide)
  have h_pc_K_next_231 : Nat.primeCounting 198470 = 17862 := pc_thm_198470
  have h_pc_M_next_val_231 : Nat.primeCounting 392941 = 33308 := pc_thm_392941
  have h_m_232 : m ≤ 885 := staircase_step_M_direct k m 51156 198470 392941 17862 33308 885 heq (k_mono 445 k h_k_232) h_pc_K_next_231 h_pc_M_next_val_231 rfl (by decide)
  -- Step 232: k >= 445, m <= 885 => k >= 446
  have h_m_mono_232 : m*(m+1)/2 ≤ 392055 := m_mono m 885 h_m_232
  have h_pc_M_232 : Nat.primeCounting 392055 = 33230 := pc_thm_392055
  have h_pc_K_prev_232 : Nat.primeCounting 198470 = 17862 := pc_thm_198470
  have h_k_233 : k ≥ 446 := staircase_step_K_direct k m 51156 392055 198470 33230 17862 446 heq h_m_mono_232 h_pc_M_232 h_pc_K_prev_232 rfl (by decide)
  have h_pc_K_next_232 : Nat.primeCounting 199362 = 17930 := pc_thm_199362
  have h_pc_M_next_val_232 : Nat.primeCounting 392055 = 33230 := pc_thm_392055
  have h_m_233 : m ≤ 884 := staircase_step_M_direct k m 51156 199362 392055 17930 33230 884 heq (k_mono 446 k h_k_233) h_pc_K_next_232 h_pc_M_next_val_232 rfl (by decide)
  -- Step 233: k >= 446, m <= 884 => k >= 447
  have h_m_mono_233 : m*(m+1)/2 ≤ 391170 := m_mono m 884 h_m_233
  have h_pc_M_233 : Nat.primeCounting 391170 = 33163 := pc_thm_391170
  have h_pc_K_prev_233 : Nat.primeCounting 199362 = 17930 := pc_thm_199362
  have h_k_234 : k ≥ 447 := staircase_step_K_direct k m 51156 391170 199362 33163 17930 447 heq h_m_mono_233 h_pc_M_233 h_pc_K_prev_233 rfl (by decide)
  have h_pc_K_next_233 : Nat.primeCounting 200256 = 18005 := pc_thm_200256
  have h_pc_M_next_val_233 : Nat.primeCounting 391170 = 33163 := pc_thm_391170
  have h_m_234 : m ≤ 883 := staircase_step_M_direct k m 51156 200256 391170 18005 33163 883 heq (k_mono 447 k h_k_234) h_pc_K_next_233 h_pc_M_next_val_233 rfl (by decide)
  -- Step 234: k >= 447, m <= 883 => k >= 448
  have h_m_mono_234 : m*(m+1)/2 ≤ 390286 := m_mono m 883 h_m_234
  have h_pc_M_234 : Nat.primeCounting 390286 = 33089 := pc_thm_390286
  have h_pc_K_prev_234 : Nat.primeCounting 200256 = 18005 := pc_thm_200256
  have h_k_235 : k ≥ 448 := staircase_step_K_direct k m 51156 390286 200256 33089 18005 448 heq h_m_mono_234 h_pc_M_234 h_pc_K_prev_234 rfl (by decide)
  have h_pc_K_next_234 : Nat.primeCounting 201152 = 18073 := pc_thm_201152
  have h_pc_M_next_val_234 : Nat.primeCounting 390286 = 33089 := pc_thm_390286
  have h_m_235 : m ≤ 882 := staircase_step_M_direct k m 51156 201152 390286 18073 33089 882 heq (k_mono 448 k h_k_235) h_pc_K_next_234 h_pc_M_next_val_234 rfl (by decide)
  -- Step 235: k >= 448, m <= 882 => k >= 449
  have h_m_mono_235 : m*(m+1)/2 ≤ 389403 := m_mono m 882 h_m_235
  have h_pc_M_235 : Nat.primeCounting 389403 = 33016 := pc_thm_389403
  have h_pc_K_prev_235 : Nat.primeCounting 201152 = 18073 := pc_thm_201152
  have h_k_236 : k ≥ 449 := staircase_step_K_direct k m 51156 389403 201152 33016 18073 449 heq h_m_mono_235 h_pc_M_235 h_pc_K_prev_235 rfl (by decide)
  have h_pc_K_next_235 : Nat.primeCounting 202050 = 18152 := pc_thm_202050
  have h_pc_M_next_val_235 : Nat.primeCounting 389403 = 33016 := pc_thm_389403
  have h_m_236 : m ≤ 881 := staircase_step_M_direct k m 51156 202050 389403 18152 33016 881 heq (k_mono 449 k h_k_236) h_pc_K_next_235 h_pc_M_next_val_235 rfl (by decide)
  -- Step 236: k >= 449, m <= 881 => k >= 450
  have h_m_mono_236 : m*(m+1)/2 ≤ 388521 := m_mono m 881 h_m_236
  have h_pc_M_236 : Nat.primeCounting 388521 = 32949 := pc_thm_388521
  have h_pc_K_prev_236 : Nat.primeCounting 202050 = 18152 := pc_thm_202050
  have h_k_237 : k ≥ 450 := staircase_step_K_direct k m 51156 388521 202050 32949 18152 450 heq h_m_mono_236 h_pc_M_236 h_pc_K_prev_236 rfl (by decide)
  have h_pc_K_next_236 : Nat.primeCounting 202950 = 18221 := pc_thm_202950
  have h_pc_M_next_val_236 : Nat.primeCounting 388521 = 32949 := pc_thm_388521
  have h_m_237 : m ≤ 880 := staircase_step_M_direct k m 51156 202950 388521 18221 32949 880 heq (k_mono 450 k h_k_237) h_pc_K_next_236 h_pc_M_next_val_236 rfl (by decide)
  -- Step 237: k >= 450, m <= 880 => k >= 451
  have h_m_mono_237 : m*(m+1)/2 ≤ 387640 := m_mono m 880 h_m_237
  have h_pc_M_237 : Nat.primeCounting 387640 = 32883 := pc_thm_387640
  have h_pc_K_prev_237 : Nat.primeCounting 202950 = 18221 := pc_thm_202950
  have h_k_238 : k ≥ 451 := staircase_step_K_direct k m 51156 387640 202950 32883 18221 451 heq h_m_mono_237 h_pc_M_237 h_pc_K_prev_237 rfl (by decide)
  have h_pc_K_next_237 : Nat.primeCounting 203852 = 18290 := pc_thm_203852
  have h_pc_M_next_val_237 : Nat.primeCounting 387640 = 32883 := pc_thm_387640
  have h_m_238 : m ≤ 879 := staircase_step_M_direct k m 51156 203852 387640 18290 32883 879 heq (k_mono 451 k h_k_238) h_pc_K_next_237 h_pc_M_next_val_237 rfl (by decide)
  -- Step 238: k >= 451, m <= 879 => k >= 452
  have h_m_mono_238 : m*(m+1)/2 ≤ 386760 := m_mono m 879 h_m_238
  have h_pc_M_238 : Nat.primeCounting 386760 = 32826 := pc_thm_386760
  have h_pc_K_prev_238 : Nat.primeCounting 203852 = 18290 := pc_thm_203852
  have h_k_239 : k ≥ 452 := staircase_step_K_direct k m 51156 386760 203852 32826 18290 452 heq h_m_mono_238 h_pc_M_238 h_pc_K_prev_238 rfl (by decide)
  have h_pc_K_next_238 : Nat.primeCounting 204756 = 18363 := pc_thm_204756
  have h_pc_M_next_val_238 : Nat.primeCounting 386760 = 32826 := pc_thm_386760
  have h_m_239 : m ≤ 878 := staircase_step_M_direct k m 51156 204756 386760 18363 32826 878 heq (k_mono 452 k h_k_239) h_pc_K_next_238 h_pc_M_next_val_238 rfl (by decide)
  -- Step 239: k >= 452, m <= 878 => k >= 453
  have h_m_mono_239 : m*(m+1)/2 ≤ 385881 := m_mono m 878 h_m_239
  have h_pc_M_239 : Nat.primeCounting 385881 = 32752 := pc_thm_385881
  have h_pc_K_prev_239 : Nat.primeCounting 204756 = 18363 := pc_thm_204756
  have h_k_240 : k ≥ 453 := staircase_step_K_direct k m 51156 385881 204756 32752 18363 453 heq h_m_mono_239 h_pc_M_239 h_pc_K_prev_239 rfl (by decide)
  have h_pc_K_next_239 : Nat.primeCounting 205662 = 18442 := pc_thm_205662
  have h_pc_M_next_val_239 : Nat.primeCounting 385881 = 32752 := pc_thm_385881
  have h_m_240 : m ≤ 877 := staircase_step_M_direct k m 51156 205662 385881 18442 32752 877 heq (k_mono 453 k h_k_240) h_pc_K_next_239 h_pc_M_next_val_239 rfl (by decide)
  -- Step 240: k >= 453, m <= 877 => k >= 454
  have h_m_mono_240 : m*(m+1)/2 ≤ 385003 := m_mono m 877 h_m_240
  have h_pc_M_240 : Nat.primeCounting 385003 = 32682 := pc_thm_385003
  have h_pc_K_prev_240 : Nat.primeCounting 205662 = 18442 := pc_thm_205662
  have h_k_241 : k ≥ 454 := staircase_step_K_direct k m 51156 385003 205662 32682 18442 454 heq h_m_mono_240 h_pc_M_240 h_pc_K_prev_240 rfl (by decide)
  have h_pc_K_next_240 : Nat.primeCounting 206570 = 18517 := pc_thm_206570
  have h_pc_M_next_val_240 : Nat.primeCounting 385003 = 32682 := pc_thm_385003
  have h_m_241 : m ≤ 876 := staircase_step_M_direct k m 51156 206570 385003 18517 32682 876 heq (k_mono 454 k h_k_241) h_pc_K_next_240 h_pc_M_next_val_240 rfl (by decide)
  exact ⟨h_k_241, h_m_241⟩

theorem staircase_part_16 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_241 : k ≥ 454) (h_m_241 : m ≤ 876) : k ≥ 469 ∧ m ≤ 859 := by
  -- Step 241: k >= 454, m <= 876 => k >= 455
  have h_m_mono_241 : m*(m+1)/2 ≤ 384126 := m_mono m 876 h_m_241
  have h_pc_M_241 : Nat.primeCounting 384126 = 32613 := pc_thm_384126
  have h_pc_K_prev_241 : Nat.primeCounting 206570 = 18517 := pc_thm_206570
  have h_k_242 : k ≥ 455 := staircase_step_K_direct k m 51156 384126 206570 32613 18517 455 heq h_m_mono_241 h_pc_M_241 h_pc_K_prev_241 rfl (by decide)
  have h_pc_K_next_241 : Nat.primeCounting 207480 = 18588 := pc_thm_207480
  have h_pc_M_next_val_241 : Nat.primeCounting 384126 = 32613 := pc_thm_384126
  have h_m_242 : m ≤ 875 := staircase_step_M_direct k m 51156 207480 384126 18588 32613 875 heq (k_mono 455 k h_k_242) h_pc_K_next_241 h_pc_M_next_val_241 rfl (by decide)
  -- Step 242: k >= 455, m <= 875 => k >= 456
  have h_m_mono_242 : m*(m+1)/2 ≤ 383250 := m_mono m 875 h_m_242
  have h_pc_M_242 : Nat.primeCounting 383250 = 32542 := pc_thm_383250
  have h_pc_K_prev_242 : Nat.primeCounting 207480 = 18588 := pc_thm_207480
  have h_k_243 : k ≥ 456 := staircase_step_K_direct k m 51156 383250 207480 32542 18588 456 heq h_m_mono_242 h_pc_M_242 h_pc_K_prev_242 rfl (by decide)
  have h_pc_K_next_242 : Nat.primeCounting 208392 = 18669 := pc_thm_208392
  have h_pc_M_next_val_242 : Nat.primeCounting 383250 = 32542 := pc_thm_383250
  have h_m_243 : m ≤ 874 := staircase_step_M_direct k m 51156 208392 383250 18669 32542 874 heq (k_mono 456 k h_k_243) h_pc_K_next_242 h_pc_M_next_val_242 rfl (by decide)
  -- Step 243: k >= 456, m <= 874 => k >= 457
  have h_m_mono_243 : m*(m+1)/2 ≤ 382375 := m_mono m 874 h_m_243
  have h_pc_M_243 : Nat.primeCounting 382375 = 32473 := pc_thm_382375
  have h_pc_K_prev_243 : Nat.primeCounting 208392 = 18669 := pc_thm_208392
  have h_k_244 : k ≥ 457 := staircase_step_K_direct k m 51156 382375 208392 32473 18669 457 heq h_m_mono_243 h_pc_M_243 h_pc_K_prev_243 rfl (by decide)
  have h_pc_K_next_243 : Nat.primeCounting 209306 = 18743 := pc_thm_209306
  have h_pc_M_next_val_243 : Nat.primeCounting 382375 = 32473 := pc_thm_382375
  have h_m_244 : m ≤ 873 := staircase_step_M_direct k m 51156 209306 382375 18743 32473 873 heq (k_mono 457 k h_k_244) h_pc_K_next_243 h_pc_M_next_val_243 rfl (by decide)
  -- Step 244: k >= 457, m <= 873 => k >= 458
  have h_m_mono_244 : m*(m+1)/2 ≤ 381501 := m_mono m 873 h_m_244
  have h_pc_M_244 : Nat.primeCounting 381501 = 32412 := pc_thm_381501
  have h_pc_K_prev_244 : Nat.primeCounting 209306 = 18743 := pc_thm_209306
  have h_k_245 : k ≥ 458 := staircase_step_K_direct k m 51156 381501 209306 32412 18743 458 heq h_m_mono_244 h_pc_M_244 h_pc_K_prev_244 rfl (by decide)
  have h_pc_K_next_244 : Nat.primeCounting 210222 = 18828 := pc_thm_210222
  have h_pc_M_next_val_244 : Nat.primeCounting 380628 = 32345 := pc_thm_380628
  have h_m_245 : m ≤ 871 := staircase_step_M_direct k m 51156 210222 380628 18828 32345 871 heq (k_mono 458 k h_k_245) h_pc_K_next_244 h_pc_M_next_val_244 rfl (by decide)
  -- Step 245: k >= 458, m <= 871 => k >= 459
  have h_m_mono_245 : m*(m+1)/2 ≤ 379756 := m_mono m 871 h_m_245
  have h_pc_M_245 : Nat.primeCounting 379756 = 32280 := pc_thm_379756
  have h_pc_K_prev_245 : Nat.primeCounting 210222 = 18828 := pc_thm_210222
  have h_k_246 : k ≥ 459 := staircase_step_K_direct k m 51156 379756 210222 32280 18828 459 heq h_m_mono_245 h_pc_M_245 h_pc_K_prev_245 rfl (by decide)
  have h_pc_K_next_245 : Nat.primeCounting 211140 = 18902 := pc_thm_211140
  have h_pc_M_next_val_245 : Nat.primeCounting 379756 = 32280 := pc_thm_379756
  have h_m_246 : m ≤ 870 := staircase_step_M_direct k m 51156 211140 379756 18902 32280 870 heq (k_mono 459 k h_k_246) h_pc_K_next_245 h_pc_M_next_val_245 rfl (by decide)
  -- Step 246: k >= 459, m <= 870 => k >= 460
  have h_m_mono_246 : m*(m+1)/2 ≤ 378885 := m_mono m 870 h_m_246
  have h_pc_M_246 : Nat.primeCounting 378885 = 32207 := pc_thm_378885
  have h_pc_K_prev_246 : Nat.primeCounting 211140 = 18902 := pc_thm_211140
  have h_k_247 : k ≥ 460 := staircase_step_K_direct k m 51156 378885 211140 32207 18902 460 heq h_m_mono_246 h_pc_M_246 h_pc_K_prev_246 rfl (by decide)
  have h_pc_K_next_246 : Nat.primeCounting 212060 = 18980 := pc_thm_212060
  have h_pc_M_next_val_246 : Nat.primeCounting 378885 = 32207 := pc_thm_378885
  have h_m_247 : m ≤ 869 := staircase_step_M_direct k m 51156 212060 378885 18980 32207 869 heq (k_mono 460 k h_k_247) h_pc_K_next_246 h_pc_M_next_val_246 rfl (by decide)
  -- Step 247: k >= 460, m <= 869 => k >= 461
  have h_m_mono_247 : m*(m+1)/2 ≤ 378015 := m_mono m 869 h_m_247
  have h_pc_M_247 : Nat.primeCounting 378015 = 32141 := pc_thm_378015
  have h_pc_K_prev_247 : Nat.primeCounting 212060 = 18980 := pc_thm_212060
  have h_k_248 : k ≥ 461 := staircase_step_K_direct k m 51156 378015 212060 32141 18980 461 heq h_m_mono_247 h_pc_M_247 h_pc_K_prev_247 rfl (by decide)
  have h_pc_K_next_247 : Nat.primeCounting 212982 = 19044 := pc_thm_212982
  have h_pc_M_next_val_247 : Nat.primeCounting 378015 = 32141 := pc_thm_378015
  have h_m_248 : m ≤ 868 := staircase_step_M_direct k m 51156 212982 378015 19044 32141 868 heq (k_mono 461 k h_k_248) h_pc_K_next_247 h_pc_M_next_val_247 rfl (by decide)
  -- Step 248: k >= 461, m <= 868 => k >= 462
  have h_m_mono_248 : m*(m+1)/2 ≤ 377146 := m_mono m 868 h_m_248
  have h_pc_M_248 : Nat.primeCounting 377146 = 32078 := pc_thm_377146
  have h_pc_K_prev_248 : Nat.primeCounting 212982 = 19044 := pc_thm_212982
  have h_k_249 : k ≥ 462 := staircase_step_K_direct k m 51156 377146 212982 32078 19044 462 heq h_m_mono_248 h_pc_M_248 h_pc_K_prev_248 rfl (by decide)
  have h_pc_K_next_248 : Nat.primeCounting 213906 = 19118 := pc_thm_213906
  have h_pc_M_next_val_248 : Nat.primeCounting 377146 = 32078 := pc_thm_377146
  have h_m_249 : m ≤ 867 := staircase_step_M_direct k m 51156 213906 377146 19118 32078 867 heq (k_mono 462 k h_k_249) h_pc_K_next_248 h_pc_M_next_val_248 rfl (by decide)
  -- Step 249: k >= 462, m <= 867 => k >= 463
  have h_m_mono_249 : m*(m+1)/2 ≤ 376278 := m_mono m 867 h_m_249
  have h_pc_M_249 : Nat.primeCounting 376278 = 32009 := pc_thm_376278
  have h_pc_K_prev_249 : Nat.primeCounting 213906 = 19118 := pc_thm_213906
  have h_k_250 : k ≥ 463 := staircase_step_K_direct k m 51156 376278 213906 32009 19118 463 heq h_m_mono_249 h_pc_M_249 h_pc_K_prev_249 rfl (by decide)
  have h_pc_K_next_249 : Nat.primeCounting 214832 = 19202 := pc_thm_214832
  have h_pc_M_next_val_249 : Nat.primeCounting 376278 = 32009 := pc_thm_376278
  have h_m_250 : m ≤ 866 := staircase_step_M_direct k m 51156 214832 376278 19202 32009 866 heq (k_mono 463 k h_k_250) h_pc_K_next_249 h_pc_M_next_val_249 rfl (by decide)
  -- Step 250: k >= 463, m <= 866 => k >= 464
  have h_m_mono_250 : m*(m+1)/2 ≤ 375411 := m_mono m 866 h_m_250
  have h_pc_M_250 : Nat.primeCounting 375411 = 31943 := pc_thm_375411
  have h_pc_K_prev_250 : Nat.primeCounting 214832 = 19202 := pc_thm_214832
  have h_k_251 : k ≥ 464 := staircase_step_K_direct k m 51156 375411 214832 31943 19202 464 heq h_m_mono_250 h_pc_M_250 h_pc_K_prev_250 rfl (by decide)
  have h_pc_K_next_250 : Nat.primeCounting 215760 = 19267 := pc_thm_215760
  have h_pc_M_next_val_250 : Nat.primeCounting 375411 = 31943 := pc_thm_375411
  have h_m_251 : m ≤ 865 := staircase_step_M_direct k m 51156 215760 375411 19267 31943 865 heq (k_mono 464 k h_k_251) h_pc_K_next_250 h_pc_M_next_val_250 rfl (by decide)
  -- Step 251: k >= 464, m <= 865 => k >= 465
  have h_m_mono_251 : m*(m+1)/2 ≤ 374545 := m_mono m 865 h_m_251
  have h_pc_M_251 : Nat.primeCounting 374545 = 31864 := pc_thm_374545
  have h_pc_K_prev_251 : Nat.primeCounting 215760 = 19267 := pc_thm_215760
  have h_k_252 : k ≥ 465 := staircase_step_K_direct k m 51156 374545 215760 31864 19267 465 heq h_m_mono_251 h_pc_M_251 h_pc_K_prev_251 rfl (by decide)
  have h_pc_K_next_251 : Nat.primeCounting 216690 = 19337 := pc_thm_216690
  have h_pc_M_next_val_251 : Nat.primeCounting 374545 = 31864 := pc_thm_374545
  have h_m_252 : m ≤ 864 := staircase_step_M_direct k m 51156 216690 374545 19337 31864 864 heq (k_mono 465 k h_k_252) h_pc_K_next_251 h_pc_M_next_val_251 rfl (by decide)
  -- Step 252: k >= 465, m <= 864 => k >= 466
  have h_m_mono_252 : m*(m+1)/2 ≤ 373680 := m_mono m 864 h_m_252
  have h_pc_M_252 : Nat.primeCounting 373680 = 31801 := pc_thm_373680
  have h_pc_K_prev_252 : Nat.primeCounting 216690 = 19337 := pc_thm_216690
  have h_k_253 : k ≥ 466 := staircase_step_K_direct k m 51156 373680 216690 31801 19337 466 heq h_m_mono_252 h_pc_M_252 h_pc_K_prev_252 rfl (by decide)
  have h_pc_K_next_252 : Nat.primeCounting 217622 = 19416 := pc_thm_217622
  have h_pc_M_next_val_252 : Nat.primeCounting 373680 = 31801 := pc_thm_373680
  have h_m_253 : m ≤ 863 := staircase_step_M_direct k m 51156 217622 373680 19416 31801 863 heq (k_mono 466 k h_k_253) h_pc_K_next_252 h_pc_M_next_val_252 rfl (by decide)
  -- Step 253: k >= 466, m <= 863 => k >= 467
  have h_m_mono_253 : m*(m+1)/2 ≤ 372816 := m_mono m 863 h_m_253
  have h_pc_M_253 : Nat.primeCounting 372816 = 31733 := pc_thm_372816
  have h_pc_K_prev_253 : Nat.primeCounting 217622 = 19416 := pc_thm_217622
  have h_k_254 : k ≥ 467 := staircase_step_K_direct k m 51156 372816 217622 31733 19416 467 heq h_m_mono_253 h_pc_M_253 h_pc_K_prev_253 rfl (by decide)
  have h_pc_K_next_253 : Nat.primeCounting 218556 = 19488 := pc_thm_218556
  have h_pc_M_next_val_253 : Nat.primeCounting 372816 = 31733 := pc_thm_372816
  have h_m_254 : m ≤ 862 := staircase_step_M_direct k m 51156 218556 372816 19488 31733 862 heq (k_mono 467 k h_k_254) h_pc_K_next_253 h_pc_M_next_val_253 rfl (by decide)
  -- Step 254: k >= 467, m <= 862 => k >= 468
  have h_m_mono_254 : m*(m+1)/2 ≤ 371953 := m_mono m 862 h_m_254
  have h_pc_M_254 : Nat.primeCounting 371953 = 31664 := pc_thm_371953
  have h_pc_K_prev_254 : Nat.primeCounting 218556 = 19488 := pc_thm_218556
  have h_k_255 : k ≥ 468 := staircase_step_K_direct k m 51156 371953 218556 31664 19488 468 heq h_m_mono_254 h_pc_M_254 h_pc_K_prev_254 rfl (by decide)
  have h_pc_K_next_254 : Nat.primeCounting 219492 = 19566 := pc_thm_219492
  have h_pc_M_next_val_254 : Nat.primeCounting 371091 = 31599 := pc_thm_371091
  have h_m_255 : m ≤ 860 := staircase_step_M_direct k m 51156 219492 371091 19566 31599 860 heq (k_mono 468 k h_k_255) h_pc_K_next_254 h_pc_M_next_val_254 rfl (by decide)
  -- Step 255: k >= 468, m <= 860 => k >= 469
  have h_m_mono_255 : m*(m+1)/2 ≤ 370230 := m_mono m 860 h_m_255
  have h_pc_M_255 : Nat.primeCounting 370230 = 31542 := pc_thm_370230
  have h_pc_K_prev_255 : Nat.primeCounting 219492 = 19566 := pc_thm_219492
  have h_k_256 : k ≥ 469 := staircase_step_K_direct k m 51156 370230 219492 31542 19566 469 heq h_m_mono_255 h_pc_M_255 h_pc_K_prev_255 rfl (by decide)
  have h_pc_K_next_255 : Nat.primeCounting 220430 = 19650 := pc_thm_220430
  have h_pc_M_next_val_255 : Nat.primeCounting 370230 = 31542 := pc_thm_370230
  have h_m_256 : m ≤ 859 := staircase_step_M_direct k m 51156 220430 370230 19650 31542 859 heq (k_mono 469 k h_k_256) h_pc_K_next_255 h_pc_M_next_val_255 rfl (by decide)
  exact ⟨h_k_256, h_m_256⟩

theorem staircase_part_17 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_256 : k ≥ 469) (h_m_256 : m ≤ 859) : k ≥ 484 ∧ m ≤ 841 := by
  -- Step 256: k >= 469, m <= 859 => k >= 470
  have h_m_mono_256 : m*(m+1)/2 ≤ 369370 := m_mono m 859 h_m_256
  have h_pc_M_256 : Nat.primeCounting 369370 = 31483 := pc_thm_369370
  have h_pc_K_prev_256 : Nat.primeCounting 220430 = 19650 := pc_thm_220430
  have h_k_257 : k ≥ 470 := staircase_step_K_direct k m 51156 369370 220430 31483 19650 470 heq h_m_mono_256 h_pc_M_256 h_pc_K_prev_256 rfl (by decide)
  have h_pc_K_next_256 : Nat.primeCounting 221370 = 19724 := pc_thm_221370
  have h_pc_M_next_val_256 : Nat.primeCounting 369370 = 31483 := pc_thm_369370
  have h_m_257 : m ≤ 858 := staircase_step_M_direct k m 51156 221370 369370 19724 31483 858 heq (k_mono 470 k h_k_257) h_pc_K_next_256 h_pc_M_next_val_256 rfl (by decide)
  -- Step 257: k >= 470, m <= 858 => k >= 471
  have h_m_mono_257 : m*(m+1)/2 ≤ 368511 := m_mono m 858 h_m_257
  have h_pc_M_257 : Nat.primeCounting 368511 = 31421 := pc_thm_368511
  have h_pc_K_prev_257 : Nat.primeCounting 221370 = 19724 := pc_thm_221370
  have h_k_258 : k ≥ 471 := staircase_step_K_direct k m 51156 368511 221370 31421 19724 471 heq h_m_mono_257 h_pc_M_257 h_pc_K_prev_257 rfl (by decide)
  have h_pc_K_next_257 : Nat.primeCounting 222312 = 19802 := pc_thm_222312
  have h_pc_M_next_val_257 : Nat.primeCounting 367653 = 31356 := pc_thm_367653
  have h_m_258 : m ≤ 856 := staircase_step_M_direct k m 51156 222312 367653 19802 31356 856 heq (k_mono 471 k h_k_258) h_pc_K_next_257 h_pc_M_next_val_257 rfl (by decide)
  -- Step 258: k >= 471, m <= 856 => k >= 472
  have h_m_mono_258 : m*(m+1)/2 ≤ 366796 := m_mono m 856 h_m_258
  have h_pc_M_258 : Nat.primeCounting 366796 = 31284 := pc_thm_366796
  have h_pc_K_prev_258 : Nat.primeCounting 222312 = 19802 := pc_thm_222312
  have h_k_259 : k ≥ 472 := staircase_step_K_direct k m 51156 366796 222312 31284 19802 472 heq h_m_mono_258 h_pc_M_258 h_pc_K_prev_258 rfl (by decide)
  have h_pc_K_next_258 : Nat.primeCounting 223256 = 19880 := pc_thm_223256
  have h_pc_M_next_val_258 : Nat.primeCounting 366796 = 31284 := pc_thm_366796
  have h_m_259 : m ≤ 855 := staircase_step_M_direct k m 51156 223256 366796 19880 31284 855 heq (k_mono 472 k h_k_259) h_pc_K_next_258 h_pc_M_next_val_258 rfl (by decide)
  -- Step 259: k >= 472, m <= 855 => k >= 473
  have h_m_mono_259 : m*(m+1)/2 ≤ 365940 := m_mono m 855 h_m_259
  have h_pc_M_259 : Nat.primeCounting 365940 = 31215 := pc_thm_365940
  have h_pc_K_prev_259 : Nat.primeCounting 223256 = 19880 := pc_thm_223256
  have h_k_260 : k ≥ 473 := staircase_step_K_direct k m 51156 365940 223256 31215 19880 473 heq h_m_mono_259 h_pc_M_259 h_pc_K_prev_259 rfl (by decide)
  have h_pc_K_next_259 : Nat.primeCounting 224202 = 19955 := pc_thm_224202
  have h_pc_M_next_val_259 : Nat.primeCounting 365940 = 31215 := pc_thm_365940
  have h_m_260 : m ≤ 854 := staircase_step_M_direct k m 51156 224202 365940 19955 31215 854 heq (k_mono 473 k h_k_260) h_pc_K_next_259 h_pc_M_next_val_259 rfl (by decide)
  -- Step 260: k >= 473, m <= 854 => k >= 474
  have h_m_mono_260 : m*(m+1)/2 ≤ 365085 := m_mono m 854 h_m_260
  have h_pc_M_260 : Nat.primeCounting 365085 = 31147 := pc_thm_365085
  have h_pc_K_prev_260 : Nat.primeCounting 224202 = 19955 := pc_thm_224202
  have h_k_261 : k ≥ 474 := staircase_step_K_direct k m 51156 365085 224202 31147 19955 474 heq h_m_mono_260 h_pc_M_260 h_pc_K_prev_260 rfl (by decide)
  have h_pc_K_next_260 : Nat.primeCounting 225150 = 20032 := pc_thm_225150
  have h_pc_M_next_val_260 : Nat.primeCounting 365085 = 31147 := pc_thm_365085
  have h_m_261 : m ≤ 853 := staircase_step_M_direct k m 51156 225150 365085 20032 31147 853 heq (k_mono 474 k h_k_261) h_pc_K_next_260 h_pc_M_next_val_260 rfl (by decide)
  -- Step 261: k >= 474, m <= 853 => k >= 475
  have h_m_mono_261 : m*(m+1)/2 ≤ 364231 := m_mono m 853 h_m_261
  have h_pc_M_261 : Nat.primeCounting 364231 = 31079 := pc_thm_364231
  have h_pc_K_prev_261 : Nat.primeCounting 225150 = 20032 := pc_thm_225150
  have h_k_262 : k ≥ 475 := staircase_step_K_direct k m 51156 364231 225150 31079 20032 475 heq h_m_mono_261 h_pc_M_261 h_pc_K_prev_261 rfl (by decide)
  have h_pc_K_next_261 : Nat.primeCounting 226100 = 20111 := pc_thm_226100
  have h_pc_M_next_val_261 : Nat.primeCounting 364231 = 31079 := pc_thm_364231
  have h_m_262 : m ≤ 852 := staircase_step_M_direct k m 51156 226100 364231 20111 31079 852 heq (k_mono 475 k h_k_262) h_pc_K_next_261 h_pc_M_next_val_261 rfl (by decide)
  -- Step 262: k >= 475, m <= 852 => k >= 476
  have h_m_mono_262 : m*(m+1)/2 ≤ 363378 := m_mono m 852 h_m_262
  have h_pc_M_262 : Nat.primeCounting 363378 = 31011 := pc_thm_363378
  have h_pc_K_prev_262 : Nat.primeCounting 226100 = 20111 := pc_thm_226100
  have h_k_263 : k ≥ 476 := staircase_step_K_direct k m 51156 363378 226100 31011 20111 476 heq h_m_mono_262 h_pc_M_262 h_pc_K_prev_262 rfl (by decide)
  have h_pc_K_next_262 : Nat.primeCounting 227052 = 20182 := pc_thm_227052
  have h_pc_M_next_val_262 : Nat.primeCounting 363378 = 31011 := pc_thm_363378
  have h_m_263 : m ≤ 851 := staircase_step_M_direct k m 51156 227052 363378 20182 31011 851 heq (k_mono 476 k h_k_263) h_pc_K_next_262 h_pc_M_next_val_262 rfl (by decide)
  -- Step 263: k >= 476, m <= 851 => k >= 477
  have h_m_mono_263 : m*(m+1)/2 ≤ 362526 := m_mono m 851 h_m_263
  have h_pc_M_263 : Nat.primeCounting 362526 = 30949 := pc_thm_362526
  have h_pc_K_prev_263 : Nat.primeCounting 227052 = 20182 := pc_thm_227052
  have h_k_264 : k ≥ 477 := staircase_step_K_direct k m 51156 362526 227052 30949 20182 477 heq h_m_mono_263 h_pc_M_263 h_pc_K_prev_263 rfl (by decide)
  have h_pc_K_next_263 : Nat.primeCounting 228006 = 20260 := pc_thm_228006
  have h_pc_M_next_val_263 : Nat.primeCounting 362526 = 30949 := pc_thm_362526
  have h_m_264 : m ≤ 850 := staircase_step_M_direct k m 51156 228006 362526 20260 30949 850 heq (k_mono 477 k h_k_264) h_pc_K_next_263 h_pc_M_next_val_263 rfl (by decide)
  -- Step 264: k >= 477, m <= 850 => k >= 478
  have h_m_mono_264 : m*(m+1)/2 ≤ 361675 := m_mono m 850 h_m_264
  have h_pc_M_264 : Nat.primeCounting 361675 = 30877 := pc_thm_361675
  have h_pc_K_prev_264 : Nat.primeCounting 228006 = 20260 := pc_thm_228006
  have h_k_265 : k ≥ 478 := staircase_step_K_direct k m 51156 361675 228006 30877 20260 478 heq h_m_mono_264 h_pc_M_264 h_pc_K_prev_264 rfl (by decide)
  have h_pc_K_next_264 : Nat.primeCounting 228962 = 20347 := pc_thm_228962
  have h_pc_M_next_val_264 : Nat.primeCounting 360825 = 30810 := pc_thm_360825
  have h_m_265 : m ≤ 848 := staircase_step_M_direct k m 51156 228962 360825 20347 30810 848 heq (k_mono 478 k h_k_265) h_pc_K_next_264 h_pc_M_next_val_264 rfl (by decide)
  -- Step 265: k >= 478, m <= 848 => k >= 479
  have h_m_mono_265 : m*(m+1)/2 ≤ 359976 := m_mono m 848 h_m_265
  have h_pc_M_265 : Nat.primeCounting 359976 = 30755 := pc_thm_359976
  have h_pc_K_prev_265 : Nat.primeCounting 228962 = 20347 := pc_thm_228962
  have h_k_266 : k ≥ 479 := staircase_step_K_direct k m 51156 359976 228962 30755 20347 479 heq h_m_mono_265 h_pc_M_265 h_pc_K_prev_265 rfl (by decide)
  have h_pc_K_next_265 : Nat.primeCounting 229920 = 20430 := pc_thm_229920
  have h_pc_M_next_val_265 : Nat.primeCounting 359976 = 30755 := pc_thm_359976
  have h_m_266 : m ≤ 847 := staircase_step_M_direct k m 51156 229920 359976 20430 30755 847 heq (k_mono 479 k h_k_266) h_pc_K_next_265 h_pc_M_next_val_265 rfl (by decide)
  -- Step 266: k >= 479, m <= 847 => k >= 480
  have h_m_mono_266 : m*(m+1)/2 ≤ 359128 := m_mono m 847 h_m_266
  have h_pc_M_266 : Nat.primeCounting 359128 = 30694 := pc_thm_359128
  have h_pc_K_prev_266 : Nat.primeCounting 229920 = 20430 := pc_thm_229920
  have h_k_267 : k ≥ 480 := staircase_step_K_direct k m 51156 359128 229920 30694 20430 480 heq h_m_mono_266 h_pc_M_266 h_pc_K_prev_266 rfl (by decide)
  have h_pc_K_next_266 : Nat.primeCounting 230880 = 20512 := pc_thm_230880
  have h_pc_M_next_val_266 : Nat.primeCounting 359128 = 30694 := pc_thm_359128
  have h_m_267 : m ≤ 846 := staircase_step_M_direct k m 51156 230880 359128 20512 30694 846 heq (k_mono 480 k h_k_267) h_pc_K_next_266 h_pc_M_next_val_266 rfl (by decide)
  -- Step 267: k >= 480, m <= 846 => k >= 481
  have h_m_mono_267 : m*(m+1)/2 ≤ 358281 := m_mono m 846 h_m_267
  have h_pc_M_267 : Nat.primeCounting 358281 = 30623 := pc_thm_358281
  have h_pc_K_prev_267 : Nat.primeCounting 230880 = 20512 := pc_thm_230880
  have h_k_268 : k ≥ 481 := staircase_step_K_direct k m 51156 358281 230880 30623 20512 481 heq h_m_mono_267 h_pc_M_267 h_pc_K_prev_267 rfl (by decide)
  have h_pc_K_next_267 : Nat.primeCounting 231842 = 20588 := pc_thm_231842
  have h_pc_M_next_val_267 : Nat.primeCounting 358281 = 30623 := pc_thm_358281
  have h_m_268 : m ≤ 845 := staircase_step_M_direct k m 51156 231842 358281 20588 30623 845 heq (k_mono 481 k h_k_268) h_pc_K_next_267 h_pc_M_next_val_267 rfl (by decide)
  -- Step 268: k >= 481, m <= 845 => k >= 482
  have h_m_mono_268 : m*(m+1)/2 ≤ 357435 := m_mono m 845 h_m_268
  have h_pc_M_268 : Nat.primeCounting 357435 = 30555 := pc_thm_357435
  have h_pc_K_prev_268 : Nat.primeCounting 231842 = 20588 := pc_thm_231842
  have h_k_269 : k ≥ 482 := staircase_step_K_direct k m 51156 357435 231842 30555 20588 482 heq h_m_mono_268 h_pc_M_268 h_pc_K_prev_268 rfl (by decide)
  have h_pc_K_next_268 : Nat.primeCounting 232806 = 20659 := pc_thm_232806
  have h_pc_M_next_val_268 : Nat.primeCounting 357435 = 30555 := pc_thm_357435
  have h_m_269 : m ≤ 844 := staircase_step_M_direct k m 51156 232806 357435 20659 30555 844 heq (k_mono 482 k h_k_269) h_pc_K_next_268 h_pc_M_next_val_268 rfl (by decide)
  -- Step 269: k >= 482, m <= 844 => k >= 483
  have h_m_mono_269 : m*(m+1)/2 ≤ 356590 := m_mono m 844 h_m_269
  have h_pc_M_269 : Nat.primeCounting 356590 = 30496 := pc_thm_356590
  have h_pc_K_prev_269 : Nat.primeCounting 232806 = 20659 := pc_thm_232806
  have h_k_270 : k ≥ 483 := staircase_step_K_direct k m 51156 356590 232806 30496 20659 483 heq h_m_mono_269 h_pc_M_269 h_pc_K_prev_269 rfl (by decide)
  have h_pc_K_next_269 : Nat.primeCounting 233772 = 20731 := pc_thm_233772
  have h_pc_M_next_val_269 : Nat.primeCounting 355746 = 30436 := pc_thm_355746
  have h_m_270 : m ≤ 842 := staircase_step_M_direct k m 51156 233772 355746 20731 30436 842 heq (k_mono 483 k h_k_270) h_pc_K_next_269 h_pc_M_next_val_269 rfl (by decide)
  -- Step 270: k >= 483, m <= 842 => k >= 484
  have h_m_mono_270 : m*(m+1)/2 ≤ 354903 := m_mono m 842 h_m_270
  have h_pc_M_270 : Nat.primeCounting 354903 = 30369 := pc_thm_354903
  have h_pc_K_prev_270 : Nat.primeCounting 233772 = 20731 := pc_thm_233772
  have h_k_271 : k ≥ 484 := staircase_step_K_direct k m 51156 354903 233772 30369 20731 484 heq h_m_mono_270 h_pc_M_270 h_pc_K_prev_270 rfl (by decide)
  have h_pc_K_next_270 : Nat.primeCounting 234740 = 20808 := pc_thm_234740
  have h_pc_M_next_val_270 : Nat.primeCounting 354903 = 30369 := pc_thm_354903
  have h_m_271 : m ≤ 841 := staircase_step_M_direct k m 51156 234740 354903 20808 30369 841 heq (k_mono 484 k h_k_271) h_pc_K_next_270 h_pc_M_next_val_270 rfl (by decide)
  exact ⟨h_k_271, h_m_271⟩

theorem staircase_part_18 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_271 : k ≥ 484) (h_m_271 : m ≤ 841) : k ≥ 499 ∧ m ≤ 823 := by
  -- Step 271: k >= 484, m <= 841 => k >= 485
  have h_m_mono_271 : m*(m+1)/2 ≤ 354061 := m_mono m 841 h_m_271
  have h_pc_M_271 : Nat.primeCounting 354061 = 30299 := pc_thm_354061
  have h_pc_K_prev_271 : Nat.primeCounting 234740 = 20808 := pc_thm_234740
  have h_k_272 : k ≥ 485 := staircase_step_K_direct k m 51156 354061 234740 30299 20808 485 heq h_m_mono_271 h_pc_M_271 h_pc_K_prev_271 rfl (by decide)
  have h_pc_K_next_271 : Nat.primeCounting 235710 = 20885 := pc_thm_235710
  have h_pc_M_next_val_271 : Nat.primeCounting 354061 = 30299 := pc_thm_354061
  have h_m_272 : m ≤ 840 := staircase_step_M_direct k m 51156 235710 354061 20885 30299 840 heq (k_mono 485 k h_k_272) h_pc_K_next_271 h_pc_M_next_val_271 rfl (by decide)
  -- Step 272: k >= 485, m <= 840 => k >= 486
  have h_m_mono_272 : m*(m+1)/2 ≤ 353220 := m_mono m 840 h_m_272
  have h_pc_M_272 : Nat.primeCounting 353220 = 30232 := pc_thm_353220
  have h_pc_K_prev_272 : Nat.primeCounting 235710 = 20885 := pc_thm_235710
  have h_k_273 : k ≥ 486 := staircase_step_K_direct k m 51156 353220 235710 30232 20885 486 heq h_m_mono_272 h_pc_M_272 h_pc_K_prev_272 rfl (by decide)
  have h_pc_K_next_272 : Nat.primeCounting 236682 = 20955 := pc_thm_236682
  have h_pc_M_next_val_272 : Nat.primeCounting 353220 = 30232 := pc_thm_353220
  have h_m_273 : m ≤ 839 := staircase_step_M_direct k m 51156 236682 353220 20955 30232 839 heq (k_mono 486 k h_k_273) h_pc_K_next_272 h_pc_M_next_val_272 rfl (by decide)
  -- Step 273: k >= 486, m <= 839 => k >= 487
  have h_m_mono_273 : m*(m+1)/2 ≤ 352380 := m_mono m 839 h_m_273
  have h_pc_M_273 : Nat.primeCounting 352380 = 30164 := pc_thm_352380
  have h_pc_K_prev_273 : Nat.primeCounting 236682 = 20955 := pc_thm_236682
  have h_k_274 : k ≥ 487 := staircase_step_K_direct k m 51156 352380 236682 30164 20955 487 heq h_m_mono_273 h_pc_M_273 h_pc_K_prev_273 rfl (by decide)
  have h_pc_K_next_273 : Nat.primeCounting 237656 = 21027 := pc_thm_237656
  have h_pc_M_next_val_273 : Nat.primeCounting 352380 = 30164 := pc_thm_352380
  have h_m_274 : m ≤ 838 := staircase_step_M_direct k m 51156 237656 352380 21027 30164 838 heq (k_mono 487 k h_k_274) h_pc_K_next_273 h_pc_M_next_val_273 rfl (by decide)
  -- Step 274: k >= 487, m <= 838 => k >= 488
  have h_m_mono_274 : m*(m+1)/2 ≤ 351541 := m_mono m 838 h_m_274
  have h_pc_M_274 : Nat.primeCounting 351541 = 30098 := pc_thm_351541
  have h_pc_K_prev_274 : Nat.primeCounting 237656 = 21027 := pc_thm_237656
  have h_k_275 : k ≥ 488 := staircase_step_K_direct k m 51156 351541 237656 30098 21027 488 heq h_m_mono_274 h_pc_M_274 h_pc_K_prev_274 rfl (by decide)
  have h_pc_K_next_274 : Nat.primeCounting 238632 = 21110 := pc_thm_238632
  have h_pc_M_next_val_274 : Nat.primeCounting 351541 = 30098 := pc_thm_351541
  have h_m_275 : m ≤ 837 := staircase_step_M_direct k m 51156 238632 351541 21110 30098 837 heq (k_mono 488 k h_k_275) h_pc_K_next_274 h_pc_M_next_val_274 rfl (by decide)
  -- Step 275: k >= 488, m <= 837 => k >= 489
  have h_m_mono_275 : m*(m+1)/2 ≤ 350703 := m_mono m 837 h_m_275
  have h_pc_M_275 : Nat.primeCounting 350703 = 30024 := pc_thm_350703
  have h_pc_K_prev_275 : Nat.primeCounting 238632 = 21110 := pc_thm_238632
  have h_k_276 : k ≥ 489 := staircase_step_K_direct k m 51156 350703 238632 30024 21110 489 heq h_m_mono_275 h_pc_M_275 h_pc_K_prev_275 rfl (by decide)
  have h_pc_K_next_275 : Nat.primeCounting 239610 = 21190 := pc_thm_239610
  have h_pc_M_next_val_275 : Nat.primeCounting 350703 = 30024 := pc_thm_350703
  have h_m_276 : m ≤ 836 := staircase_step_M_direct k m 51156 239610 350703 21190 30024 836 heq (k_mono 489 k h_k_276) h_pc_K_next_275 h_pc_M_next_val_275 rfl (by decide)
  -- Step 276: k >= 489, m <= 836 => k >= 490
  have h_m_mono_276 : m*(m+1)/2 ≤ 349866 := m_mono m 836 h_m_276
  have h_pc_M_276 : Nat.primeCounting 349866 = 29964 := pc_thm_349866
  have h_pc_K_prev_276 : Nat.primeCounting 239610 = 21190 := pc_thm_239610
  have h_k_277 : k ≥ 490 := staircase_step_K_direct k m 51156 349866 239610 29964 21190 490 heq h_m_mono_276 h_pc_M_276 h_pc_K_prev_276 rfl (by decide)
  have h_pc_K_next_276 : Nat.primeCounting 240590 = 21268 := pc_thm_240590
  have h_pc_M_next_val_276 : Nat.primeCounting 349030 = 29896 := pc_thm_349030
  have h_m_277 : m ≤ 834 := staircase_step_M_direct k m 51156 240590 349030 21268 29896 834 heq (k_mono 490 k h_k_277) h_pc_K_next_276 h_pc_M_next_val_276 rfl (by decide)
  -- Step 277: k >= 490, m <= 834 => k >= 491
  have h_m_mono_277 : m*(m+1)/2 ≤ 348195 := m_mono m 834 h_m_277
  have h_pc_M_277 : Nat.primeCounting 348195 = 29831 := pc_thm_348195
  have h_pc_K_prev_277 : Nat.primeCounting 240590 = 21268 := pc_thm_240590
  have h_k_278 : k ≥ 491 := staircase_step_K_direct k m 51156 348195 240590 29831 21268 491 heq h_m_mono_277 h_pc_M_277 h_pc_K_prev_277 rfl (by decide)
  have h_pc_K_next_277 : Nat.primeCounting 241572 = 21351 := pc_thm_241572
  have h_pc_M_next_val_277 : Nat.primeCounting 348195 = 29831 := pc_thm_348195
  have h_m_278 : m ≤ 833 := staircase_step_M_direct k m 51156 241572 348195 21351 29831 833 heq (k_mono 491 k h_k_278) h_pc_K_next_277 h_pc_M_next_val_277 rfl (by decide)
  -- Step 278: k >= 491, m <= 833 => k >= 492
  have h_m_mono_278 : m*(m+1)/2 ≤ 347361 := m_mono m 833 h_m_278
  have h_pc_M_278 : Nat.primeCounting 347361 = 29770 := pc_thm_347361
  have h_pc_K_prev_278 : Nat.primeCounting 241572 = 21351 := pc_thm_241572
  have h_k_279 : k ≥ 492 := staircase_step_K_direct k m 51156 347361 241572 29770 21351 492 heq h_m_mono_278 h_pc_M_278 h_pc_K_prev_278 rfl (by decide)
  have h_pc_K_next_278 : Nat.primeCounting 242556 = 21435 := pc_thm_242556
  have h_pc_M_next_val_278 : Nat.primeCounting 347361 = 29770 := pc_thm_347361
  have h_m_279 : m ≤ 832 := staircase_step_M_direct k m 51156 242556 347361 21435 29770 832 heq (k_mono 492 k h_k_279) h_pc_K_next_278 h_pc_M_next_val_278 rfl (by decide)
  -- Step 279: k >= 492, m <= 832 => k >= 493
  have h_m_mono_279 : m*(m+1)/2 ≤ 346528 := m_mono m 832 h_m_279
  have h_pc_M_279 : Nat.primeCounting 346528 = 29701 := pc_thm_346528
  have h_pc_K_prev_279 : Nat.primeCounting 242556 = 21435 := pc_thm_242556
  have h_k_280 : k ≥ 493 := staircase_step_K_direct k m 51156 346528 242556 29701 21435 493 heq h_m_mono_279 h_pc_M_279 h_pc_K_prev_279 rfl (by decide)
  have h_pc_K_next_279 : Nat.primeCounting 243542 = 21511 := pc_thm_243542
  have h_pc_M_next_val_279 : Nat.primeCounting 346528 = 29701 := pc_thm_346528
  have h_m_280 : m ≤ 831 := staircase_step_M_direct k m 51156 243542 346528 21511 29701 831 heq (k_mono 493 k h_k_280) h_pc_K_next_279 h_pc_M_next_val_279 rfl (by decide)
  -- Step 280: k >= 493, m <= 831 => k >= 494
  have h_m_mono_280 : m*(m+1)/2 ≤ 345696 := m_mono m 831 h_m_280
  have h_pc_M_280 : Nat.primeCounting 345696 = 29630 := pc_thm_345696
  have h_pc_K_prev_280 : Nat.primeCounting 243542 = 21511 := pc_thm_243542
  have h_k_281 : k ≥ 494 := staircase_step_K_direct k m 51156 345696 243542 29630 21511 494 heq h_m_mono_280 h_pc_M_280 h_pc_K_prev_280 rfl (by decide)
  have h_pc_K_next_280 : Nat.primeCounting 244530 = 21593 := pc_thm_244530
  have h_pc_M_next_val_280 : Nat.primeCounting 344865 = 29568 := pc_thm_344865
  have h_m_281 : m ≤ 829 := staircase_step_M_direct k m 51156 244530 344865 21593 29568 829 heq (k_mono 494 k h_k_281) h_pc_K_next_280 h_pc_M_next_val_280 rfl (by decide)
  -- Step 281: k >= 494, m <= 829 => k >= 495
  have h_m_mono_281 : m*(m+1)/2 ≤ 344035 := m_mono m 829 h_m_281
  have h_pc_M_281 : Nat.primeCounting 344035 = 29502 := pc_thm_344035
  have h_pc_K_prev_281 : Nat.primeCounting 244530 = 21593 := pc_thm_244530
  have h_k_282 : k ≥ 495 := staircase_step_K_direct k m 51156 344035 244530 29502 21593 495 heq h_m_mono_281 h_pc_M_281 h_pc_K_prev_281 rfl (by decide)
  have h_pc_K_next_281 : Nat.primeCounting 245520 = 21672 := pc_thm_245520
  have h_pc_M_next_val_281 : Nat.primeCounting 344035 = 29502 := pc_thm_344035
  have h_m_282 : m ≤ 828 := staircase_step_M_direct k m 51156 245520 344035 21672 29502 828 heq (k_mono 495 k h_k_282) h_pc_K_next_281 h_pc_M_next_val_281 rfl (by decide)
  -- Step 282: k >= 495, m <= 828 => k >= 496
  have h_m_mono_282 : m*(m+1)/2 ≤ 343206 := m_mono m 828 h_m_282
  have h_pc_M_282 : Nat.primeCounting 343206 = 29435 := pc_thm_343206
  have h_pc_K_prev_282 : Nat.primeCounting 245520 = 21672 := pc_thm_245520
  have h_k_283 : k ≥ 496 := staircase_step_K_direct k m 51156 343206 245520 29435 21672 496 heq h_m_mono_282 h_pc_M_282 h_pc_K_prev_282 rfl (by decide)
  have h_pc_K_next_282 : Nat.primeCounting 246512 = 21752 := pc_thm_246512
  have h_pc_M_next_val_282 : Nat.primeCounting 343206 = 29435 := pc_thm_343206
  have h_m_283 : m ≤ 827 := staircase_step_M_direct k m 51156 246512 343206 21752 29435 827 heq (k_mono 496 k h_k_283) h_pc_K_next_282 h_pc_M_next_val_282 rfl (by decide)
  -- Step 283: k >= 496, m <= 827 => k >= 497
  have h_m_mono_283 : m*(m+1)/2 ≤ 342378 := m_mono m 827 h_m_283
  have h_pc_M_283 : Nat.primeCounting 342378 = 29376 := pc_thm_342378
  have h_pc_K_prev_283 : Nat.primeCounting 246512 = 21752 := pc_thm_246512
  have h_k_284 : k ≥ 497 := staircase_step_K_direct k m 51156 342378 246512 29376 21752 497 heq h_m_mono_283 h_pc_M_283 h_pc_K_prev_283 rfl (by decide)
  have h_pc_K_next_283 : Nat.primeCounting 247506 = 21832 := pc_thm_247506
  have h_pc_M_next_val_283 : Nat.primeCounting 342378 = 29376 := pc_thm_342378
  have h_m_284 : m ≤ 826 := staircase_step_M_direct k m 51156 247506 342378 21832 29376 826 heq (k_mono 497 k h_k_284) h_pc_K_next_283 h_pc_M_next_val_283 rfl (by decide)
  -- Step 284: k >= 497, m <= 826 => k >= 498
  have h_m_mono_284 : m*(m+1)/2 ≤ 341551 := m_mono m 826 h_m_284
  have h_pc_M_284 : Nat.primeCounting 341551 = 29307 := pc_thm_341551
  have h_pc_K_prev_284 : Nat.primeCounting 247506 = 21832 := pc_thm_247506
  have h_k_285 : k ≥ 498 := staircase_step_K_direct k m 51156 341551 247506 29307 21832 498 heq h_m_mono_284 h_pc_M_284 h_pc_K_prev_284 rfl (by decide)
  have h_pc_K_next_284 : Nat.primeCounting 248502 = 21920 := pc_thm_248502
  have h_pc_M_next_val_284 : Nat.primeCounting 340725 = 29241 := pc_thm_340725
  have h_m_285 : m ≤ 824 := staircase_step_M_direct k m 51156 248502 340725 21920 29241 824 heq (k_mono 498 k h_k_285) h_pc_K_next_284 h_pc_M_next_val_284 rfl (by decide)
  -- Step 285: k >= 498, m <= 824 => k >= 499
  have h_m_mono_285 : m*(m+1)/2 ≤ 339900 := m_mono m 824 h_m_285
  have h_pc_M_285 : Nat.primeCounting 339900 = 29178 := pc_thm_339900
  have h_pc_K_prev_285 : Nat.primeCounting 248502 = 21920 := pc_thm_248502
  have h_k_286 : k ≥ 499 := staircase_step_K_direct k m 51156 339900 248502 29178 21920 499 heq h_m_mono_285 h_pc_M_285 h_pc_K_prev_285 rfl (by decide)
  have h_pc_K_next_285 : Nat.primeCounting 249500 = 22004 := pc_thm_249500
  have h_pc_M_next_val_285 : Nat.primeCounting 339900 = 29178 := pc_thm_339900
  have h_m_286 : m ≤ 823 := staircase_step_M_direct k m 51156 249500 339900 22004 29178 823 heq (k_mono 499 k h_k_286) h_pc_K_next_285 h_pc_M_next_val_285 rfl (by decide)
  exact ⟨h_k_286, h_m_286⟩

theorem staircase_part_19 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_286 : k ≥ 499) (h_m_286 : m ≤ 823) : k ≥ 514 ∧ m ≤ 805 := by
  -- Step 286: k >= 499, m <= 823 => k >= 500
  have h_m_mono_286 : m*(m+1)/2 ≤ 339076 := m_mono m 823 h_m_286
  have h_pc_M_286 : Nat.primeCounting 339076 = 29118 := pc_thm_339076
  have h_pc_K_prev_286 : Nat.primeCounting 249500 = 22004 := pc_thm_249500
  have h_k_287 : k ≥ 500 := staircase_step_K_direct k m 51156 339076 249500 29118 22004 500 heq h_m_mono_286 h_pc_M_286 h_pc_K_prev_286 rfl (by decide)
  have h_pc_K_next_286 : Nat.primeCounting 250500 = 22077 := pc_thm_250500
  have h_pc_M_next_val_286 : Nat.primeCounting 339076 = 29118 := pc_thm_339076
  have h_m_287 : m ≤ 822 := staircase_step_M_direct k m 51156 250500 339076 22077 29118 822 heq (k_mono 500 k h_k_287) h_pc_K_next_286 h_pc_M_next_val_286 rfl (by decide)
  -- Step 287: k >= 500, m <= 822 => k >= 501
  have h_m_mono_287 : m*(m+1)/2 ≤ 338253 := m_mono m 822 h_m_287
  have h_pc_M_287 : Nat.primeCounting 338253 = 29056 := pc_thm_338253
  have h_pc_K_prev_287 : Nat.primeCounting 250500 = 22077 := pc_thm_250500
  have h_k_288 : k ≥ 501 := staircase_step_K_direct k m 51156 338253 250500 29056 22077 501 heq h_m_mono_287 h_pc_M_287 h_pc_K_prev_287 rfl (by decide)
  have h_pc_K_next_287 : Nat.primeCounting 251502 = 22163 := pc_thm_251502
  have h_pc_M_next_val_287 : Nat.primeCounting 338253 = 29056 := pc_thm_338253
  have h_m_288 : m ≤ 821 := staircase_step_M_direct k m 51156 251502 338253 22163 29056 821 heq (k_mono 501 k h_k_288) h_pc_K_next_287 h_pc_M_next_val_287 rfl (by decide)
  -- Step 288: k >= 501, m <= 821 => k >= 502
  have h_m_mono_288 : m*(m+1)/2 ≤ 337431 := m_mono m 821 h_m_288
  have h_pc_M_288 : Nat.primeCounting 337431 = 28991 := pc_thm_337431
  have h_pc_K_prev_288 : Nat.primeCounting 251502 = 22163 := pc_thm_251502
  have h_k_289 : k ≥ 502 := staircase_step_K_direct k m 51156 337431 251502 28991 22163 502 heq h_m_mono_288 h_pc_M_288 h_pc_K_prev_288 rfl (by decide)
  have h_pc_K_next_288 : Nat.primeCounting 252506 = 22243 := pc_thm_252506
  have h_pc_M_next_val_288 : Nat.primeCounting 336610 = 28922 := pc_thm_336610
  have h_m_289 : m ≤ 819 := staircase_step_M_direct k m 51156 252506 336610 22243 28922 819 heq (k_mono 502 k h_k_289) h_pc_K_next_288 h_pc_M_next_val_288 rfl (by decide)
  -- Step 289: k >= 502, m <= 819 => k >= 503
  have h_m_mono_289 : m*(m+1)/2 ≤ 335790 := m_mono m 819 h_m_289
  have h_pc_M_289 : Nat.primeCounting 335790 = 28858 := pc_thm_335790
  have h_pc_K_prev_289 : Nat.primeCounting 252506 = 22243 := pc_thm_252506
  have h_k_290 : k ≥ 503 := staircase_step_K_direct k m 51156 335790 252506 28858 22243 503 heq h_m_mono_289 h_pc_M_289 h_pc_K_prev_289 rfl (by decide)
  have h_pc_K_next_289 : Nat.primeCounting 253512 = 22316 := pc_thm_253512
  have h_pc_M_next_val_289 : Nat.primeCounting 335790 = 28858 := pc_thm_335790
  have h_m_290 : m ≤ 818 := staircase_step_M_direct k m 51156 253512 335790 22316 28858 818 heq (k_mono 503 k h_k_290) h_pc_K_next_289 h_pc_M_next_val_289 rfl (by decide)
  -- Step 290: k >= 503, m <= 818 => k >= 504
  have h_m_mono_290 : m*(m+1)/2 ≤ 334971 := m_mono m 818 h_m_290
  have h_pc_M_290 : Nat.primeCounting 334971 = 28792 := pc_thm_334971
  have h_pc_K_prev_290 : Nat.primeCounting 253512 = 22316 := pc_thm_253512
  have h_k_291 : k ≥ 504 := staircase_step_K_direct k m 51156 334971 253512 28792 22316 504 heq h_m_mono_290 h_pc_M_290 h_pc_K_prev_290 rfl (by decide)
  have h_pc_K_next_290 : Nat.primeCounting 254520 = 22399 := pc_thm_254520
  have h_pc_M_next_val_290 : Nat.primeCounting 334971 = 28792 := pc_thm_334971
  have h_m_291 : m ≤ 817 := staircase_step_M_direct k m 51156 254520 334971 22399 28792 817 heq (k_mono 504 k h_k_291) h_pc_K_next_290 h_pc_M_next_val_290 rfl (by decide)
  -- Step 291: k >= 504, m <= 817 => k >= 505
  have h_m_mono_291 : m*(m+1)/2 ≤ 334153 := m_mono m 817 h_m_291
  have h_pc_M_291 : Nat.primeCounting 334153 = 28729 := pc_thm_334153
  have h_pc_K_prev_291 : Nat.primeCounting 254520 = 22399 := pc_thm_254520
  have h_k_292 : k ≥ 505 := staircase_step_K_direct k m 51156 334153 254520 28729 22399 505 heq h_m_mono_291 h_pc_M_291 h_pc_K_prev_291 rfl (by decide)
  have h_pc_K_next_291 : Nat.primeCounting 255530 = 22486 := pc_thm_255530
  have h_pc_M_next_val_291 : Nat.primeCounting 334153 = 28729 := pc_thm_334153
  have h_m_292 : m ≤ 816 := staircase_step_M_direct k m 51156 255530 334153 22486 28729 816 heq (k_mono 505 k h_k_292) h_pc_K_next_291 h_pc_M_next_val_291 rfl (by decide)
  -- Step 292: k >= 505, m <= 816 => k >= 506
  have h_m_mono_292 : m*(m+1)/2 ≤ 333336 := m_mono m 816 h_m_292
  have h_pc_M_292 : Nat.primeCounting 333336 = 28665 := pc_thm_333336
  have h_pc_K_prev_292 : Nat.primeCounting 255530 = 22486 := pc_thm_255530
  have h_k_293 : k ≥ 506 := staircase_step_K_direct k m 51156 333336 255530 28665 22486 506 heq h_m_mono_292 h_pc_M_292 h_pc_K_prev_292 rfl (by decide)
  have h_pc_K_next_292 : Nat.primeCounting 256542 = 22566 := pc_thm_256542
  have h_pc_M_next_val_292 : Nat.primeCounting 332520 = 28607 := pc_thm_332520
  have h_m_293 : m ≤ 814 := staircase_step_M_direct k m 51156 256542 332520 22566 28607 814 heq (k_mono 506 k h_k_293) h_pc_K_next_292 h_pc_M_next_val_292 rfl (by decide)
  -- Step 293: k >= 506, m <= 814 => k >= 507
  have h_m_mono_293 : m*(m+1)/2 ≤ 331705 := m_mono m 814 h_m_293
  have h_pc_M_293 : Nat.primeCounting 331705 = 28542 := pc_thm_331705
  have h_pc_K_prev_293 : Nat.primeCounting 256542 = 22566 := pc_thm_256542
  have h_k_294 : k ≥ 507 := staircase_step_K_direct k m 51156 331705 256542 28542 22566 507 heq h_m_mono_293 h_pc_M_293 h_pc_K_prev_293 rfl (by decide)
  have h_pc_K_next_293 : Nat.primeCounting 257556 = 22642 := pc_thm_257556
  have h_pc_M_next_val_293 : Nat.primeCounting 331705 = 28542 := pc_thm_331705
  have h_m_294 : m ≤ 813 := staircase_step_M_direct k m 51156 257556 331705 22642 28542 813 heq (k_mono 507 k h_k_294) h_pc_K_next_293 h_pc_M_next_val_293 rfl (by decide)
  -- Step 294: k >= 507, m <= 813 => k >= 508
  have h_m_mono_294 : m*(m+1)/2 ≤ 330891 := m_mono m 813 h_m_294
  have h_pc_M_294 : Nat.primeCounting 330891 = 28478 := pc_thm_330891
  have h_pc_K_prev_294 : Nat.primeCounting 257556 = 22642 := pc_thm_257556
  have h_k_295 : k ≥ 508 := staircase_step_K_direct k m 51156 330891 257556 28478 22642 508 heq h_m_mono_294 h_pc_M_294 h_pc_K_prev_294 rfl (by decide)
  have h_pc_K_next_294 : Nat.primeCounting 258572 = 22724 := pc_thm_258572
  have h_pc_M_next_val_294 : Nat.primeCounting 330891 = 28478 := pc_thm_330891
  have h_m_295 : m ≤ 812 := staircase_step_M_direct k m 51156 258572 330891 22724 28478 812 heq (k_mono 508 k h_k_295) h_pc_K_next_294 h_pc_M_next_val_294 rfl (by decide)
  -- Step 295: k >= 508, m <= 812 => k >= 509
  have h_m_mono_295 : m*(m+1)/2 ≤ 330078 := m_mono m 812 h_m_295
  have h_pc_M_295 : Nat.primeCounting 330078 = 28412 := pc_thm_330078
  have h_pc_K_prev_295 : Nat.primeCounting 258572 = 22724 := pc_thm_258572
  have h_k_296 : k ≥ 509 := staircase_step_K_direct k m 51156 330078 258572 28412 22724 509 heq h_m_mono_295 h_pc_M_295 h_pc_K_prev_295 rfl (by decide)
  have h_pc_K_next_295 : Nat.primeCounting 259590 = 22803 := pc_thm_259590
  have h_pc_M_next_val_295 : Nat.primeCounting 330078 = 28412 := pc_thm_330078
  have h_m_296 : m ≤ 811 := staircase_step_M_direct k m 51156 259590 330078 22803 28412 811 heq (k_mono 509 k h_k_296) h_pc_K_next_295 h_pc_M_next_val_295 rfl (by decide)
  -- Step 296: k >= 509, m <= 811 => k >= 510
  have h_m_mono_296 : m*(m+1)/2 ≤ 329266 := m_mono m 811 h_m_296
  have h_pc_M_296 : Nat.primeCounting 329266 = 28343 := pc_thm_329266
  have h_pc_K_prev_296 : Nat.primeCounting 259590 = 22803 := pc_thm_259590
  have h_k_297 : k ≥ 510 := staircase_step_K_direct k m 51156 329266 259590 28343 22803 510 heq h_m_mono_296 h_pc_M_296 h_pc_K_prev_296 rfl (by decide)
  have h_pc_K_next_296 : Nat.primeCounting 260610 = 22884 := pc_thm_260610
  have h_pc_M_next_val_296 : Nat.primeCounting 328455 = 28286 := pc_thm_328455
  have h_m_297 : m ≤ 809 := staircase_step_M_direct k m 51156 260610 328455 22884 28286 809 heq (k_mono 510 k h_k_297) h_pc_K_next_296 h_pc_M_next_val_296 rfl (by decide)
  -- Step 297: k >= 510, m <= 809 => k >= 511
  have h_m_mono_297 : m*(m+1)/2 ≤ 327645 := m_mono m 809 h_m_297
  have h_pc_M_297 : Nat.primeCounting 327645 = 28219 := pc_thm_327645
  have h_pc_K_prev_297 : Nat.primeCounting 260610 = 22884 := pc_thm_260610
  have h_k_298 : k ≥ 511 := staircase_step_K_direct k m 51156 327645 260610 28219 22884 511 heq h_m_mono_297 h_pc_M_297 h_pc_K_prev_297 rfl (by decide)
  have h_pc_K_next_297 : Nat.primeCounting 261632 = 22962 := pc_thm_261632
  have h_pc_M_next_val_297 : Nat.primeCounting 327645 = 28219 := pc_thm_327645
  have h_m_298 : m ≤ 808 := staircase_step_M_direct k m 51156 261632 327645 22962 28219 808 heq (k_mono 511 k h_k_298) h_pc_K_next_297 h_pc_M_next_val_297 rfl (by decide)
  -- Step 298: k >= 511, m <= 808 => k >= 512
  have h_m_mono_298 : m*(m+1)/2 ≤ 326836 := m_mono m 808 h_m_298
  have h_pc_M_298 : Nat.primeCounting 326836 = 28150 := pc_thm_326836
  have h_pc_K_prev_298 : Nat.primeCounting 261632 = 22962 := pc_thm_261632
  have h_k_299 : k ≥ 512 := staircase_step_K_direct k m 51156 326836 261632 28150 22962 512 heq h_m_mono_298 h_pc_M_298 h_pc_K_prev_298 rfl (by decide)
  have h_pc_K_next_298 : Nat.primeCounting 262656 = 23042 := pc_thm_262656
  have h_pc_M_next_val_298 : Nat.primeCounting 326836 = 28150 := pc_thm_326836
  have h_m_299 : m ≤ 807 := staircase_step_M_direct k m 51156 262656 326836 23042 28150 807 heq (k_mono 512 k h_k_299) h_pc_K_next_298 h_pc_M_next_val_298 rfl (by decide)
  -- Step 299: k >= 512, m <= 807 => k >= 513
  have h_m_mono_299 : m*(m+1)/2 ≤ 326028 := m_mono m 807 h_m_299
  have h_pc_M_299 : Nat.primeCounting 326028 = 28092 := pc_thm_326028
  have h_pc_K_prev_299 : Nat.primeCounting 262656 = 23042 := pc_thm_262656
  have h_k_300 : k ≥ 513 := staircase_step_K_direct k m 51156 326028 262656 28092 23042 513 heq h_m_mono_299 h_pc_M_299 h_pc_K_prev_299 rfl (by decide)
  have h_pc_K_next_299 : Nat.primeCounting 263682 = 23125 := pc_thm_263682
  have h_pc_M_next_val_299 : Nat.primeCounting 326028 = 28092 := pc_thm_326028
  have h_m_300 : m ≤ 806 := staircase_step_M_direct k m 51156 263682 326028 23125 28092 806 heq (k_mono 513 k h_k_300) h_pc_K_next_299 h_pc_M_next_val_299 rfl (by decide)
  -- Step 300: k >= 513, m <= 806 => k >= 514
  have h_m_mono_300 : m*(m+1)/2 ≤ 325221 := m_mono m 806 h_m_300
  have h_pc_M_300 : Nat.primeCounting 325221 = 28026 := pc_thm_325221
  have h_pc_K_prev_300 : Nat.primeCounting 263682 = 23125 := pc_thm_263682
  have h_k_301 : k ≥ 514 := staircase_step_K_direct k m 51156 325221 263682 28026 23125 514 heq h_m_mono_300 h_pc_M_300 h_pc_K_prev_300 rfl (by decide)
  have h_pc_K_next_300 : Nat.primeCounting 264710 = 23202 := pc_thm_264710
  have h_pc_M_next_val_300 : Nat.primeCounting 325221 = 28026 := pc_thm_325221
  have h_m_301 : m ≤ 805 := staircase_step_M_direct k m 51156 264710 325221 23202 28026 805 heq (k_mono 514 k h_k_301) h_pc_K_next_300 h_pc_M_next_val_300 rfl (by decide)
  exact ⟨h_k_301, h_m_301⟩

theorem staircase_part_20 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_301 : k ≥ 514) (h_m_301 : m ≤ 805) : k ≥ 529 ∧ m ≤ 785 := by
  -- Step 301: k >= 514, m <= 805 => k >= 515
  have h_m_mono_301 : m*(m+1)/2 ≤ 324415 := m_mono m 805 h_m_301
  have h_pc_M_301 : Nat.primeCounting 324415 = 27951 := pc_thm_324415
  have h_pc_K_prev_301 : Nat.primeCounting 264710 = 23202 := pc_thm_264710
  have h_k_302 : k ≥ 515 := staircase_step_K_direct k m 51156 324415 264710 27951 23202 515 heq h_m_mono_301 h_pc_M_301 h_pc_K_prev_301 rfl (by decide)
  have h_pc_K_next_301 : Nat.primeCounting 265740 = 23289 := pc_thm_265740
  have h_pc_M_next_val_301 : Nat.primeCounting 323610 = 27894 := pc_thm_323610
  have h_m_302 : m ≤ 803 := staircase_step_M_direct k m 51156 265740 323610 23289 27894 803 heq (k_mono 515 k h_k_302) h_pc_K_next_301 h_pc_M_next_val_301 rfl (by decide)
  -- Step 302: k >= 515, m <= 803 => k >= 516
  have h_m_mono_302 : m*(m+1)/2 ≤ 322806 := m_mono m 803 h_m_302
  have h_pc_M_302 : Nat.primeCounting 322806 = 27833 := pc_thm_322806
  have h_pc_K_prev_302 : Nat.primeCounting 265740 = 23289 := pc_thm_265740
  have h_k_303 : k ≥ 516 := staircase_step_K_direct k m 51156 322806 265740 27833 23289 516 heq h_m_mono_302 h_pc_M_302 h_pc_K_prev_302 rfl (by decide)
  have h_pc_K_next_302 : Nat.primeCounting 266772 = 23373 := pc_thm_266772
  have h_pc_M_next_val_302 : Nat.primeCounting 322806 = 27833 := pc_thm_322806
  have h_m_303 : m ≤ 802 := staircase_step_M_direct k m 51156 266772 322806 23373 27833 802 heq (k_mono 516 k h_k_303) h_pc_K_next_302 h_pc_M_next_val_302 rfl (by decide)
  -- Step 303: k >= 516, m <= 802 => k >= 517
  have h_m_mono_303 : m*(m+1)/2 ≤ 322003 := m_mono m 802 h_m_303
  have h_pc_M_303 : Nat.primeCounting 322003 = 27768 := pc_thm_322003
  have h_pc_K_prev_303 : Nat.primeCounting 266772 = 23373 := pc_thm_266772
  have h_k_304 : k ≥ 517 := staircase_step_K_direct k m 51156 322003 266772 27768 23373 517 heq h_m_mono_303 h_pc_M_303 h_pc_K_prev_303 rfl (by decide)
  have h_pc_K_next_303 : Nat.primeCounting 267806 = 23473 := pc_thm_267806
  have h_pc_M_next_val_303 : Nat.primeCounting 321201 = 27703 := pc_thm_321201
  have h_m_304 : m ≤ 800 := staircase_step_M_direct k m 51156 267806 321201 23473 27703 800 heq (k_mono 517 k h_k_304) h_pc_K_next_303 h_pc_M_next_val_303 rfl (by decide)
  -- Step 304: k >= 517, m <= 800 => k >= 518
  have h_m_mono_304 : m*(m+1)/2 ≤ 320400 := m_mono m 800 h_m_304
  have h_pc_M_304 : Nat.primeCounting 320400 = 27644 := pc_thm_320400
  have h_pc_K_prev_304 : Nat.primeCounting 267806 = 23473 := pc_thm_267806
  have h_k_305 : k ≥ 518 := staircase_step_K_direct k m 51156 320400 267806 27644 23473 518 heq h_m_mono_304 h_pc_M_304 h_pc_K_prev_304 rfl (by decide)
  have h_pc_K_next_304 : Nat.primeCounting 268842 = 23549 := pc_thm_268842
  have h_pc_M_next_val_304 : Nat.primeCounting 320400 = 27644 := pc_thm_320400
  have h_m_305 : m ≤ 799 := staircase_step_M_direct k m 51156 268842 320400 23549 27644 799 heq (k_mono 518 k h_k_305) h_pc_K_next_304 h_pc_M_next_val_304 rfl (by decide)
  -- Step 305: k >= 518, m <= 799 => k >= 519
  have h_m_mono_305 : m*(m+1)/2 ≤ 319600 := m_mono m 799 h_m_305
  have h_pc_M_305 : Nat.primeCounting 319600 = 27576 := pc_thm_319600
  have h_pc_K_prev_305 : Nat.primeCounting 268842 = 23549 := pc_thm_268842
  have h_k_306 : k ≥ 519 := staircase_step_K_direct k m 51156 319600 268842 27576 23549 519 heq h_m_mono_305 h_pc_M_305 h_pc_K_prev_305 rfl (by decide)
  have h_pc_K_next_305 : Nat.primeCounting 269880 = 23633 := pc_thm_269880
  have h_pc_M_next_val_305 : Nat.primeCounting 319600 = 27576 := pc_thm_319600
  have h_m_306 : m ≤ 798 := staircase_step_M_direct k m 51156 269880 319600 23633 27576 798 heq (k_mono 519 k h_k_306) h_pc_K_next_305 h_pc_M_next_val_305 rfl (by decide)
  -- Step 306: k >= 519, m <= 798 => k >= 520
  have h_m_mono_306 : m*(m+1)/2 ≤ 318801 := m_mono m 798 h_m_306
  have h_pc_M_306 : Nat.primeCounting 318801 = 27506 := pc_thm_318801
  have h_pc_K_prev_306 : Nat.primeCounting 269880 = 23633 := pc_thm_269880
  have h_k_307 : k ≥ 520 := staircase_step_K_direct k m 51156 318801 269880 27506 23633 520 heq h_m_mono_306 h_pc_M_306 h_pc_K_prev_306 rfl (by decide)
  have h_pc_K_next_306 : Nat.primeCounting 270920 = 23719 := pc_thm_270920
  have h_pc_M_next_val_306 : Nat.primeCounting 318003 = 27442 := pc_thm_318003
  have h_m_307 : m ≤ 796 := staircase_step_M_direct k m 51156 270920 318003 23719 27442 796 heq (k_mono 520 k h_k_307) h_pc_K_next_306 h_pc_M_next_val_306 rfl (by decide)
  -- Step 307: k >= 520, m <= 796 => k >= 521
  have h_m_mono_307 : m*(m+1)/2 ≤ 317206 := m_mono m 796 h_m_307
  have h_pc_M_307 : Nat.primeCounting 317206 = 27373 := pc_thm_317206
  have h_pc_K_prev_307 : Nat.primeCounting 270920 = 23719 := pc_thm_270920
  have h_k_308 : k ≥ 521 := staircase_step_K_direct k m 51156 317206 270920 27373 23719 521 heq h_m_mono_307 h_pc_M_307 h_pc_K_prev_307 rfl (by decide)
  have h_pc_K_next_307 : Nat.primeCounting 271962 = 23801 := pc_thm_271962
  have h_pc_M_next_val_307 : Nat.primeCounting 317206 = 27373 := pc_thm_317206
  have h_m_308 : m ≤ 795 := staircase_step_M_direct k m 51156 271962 317206 23801 27373 795 heq (k_mono 521 k h_k_308) h_pc_K_next_307 h_pc_M_next_val_307 rfl (by decide)
  -- Step 308: k >= 521, m <= 795 => k >= 522
  have h_m_mono_308 : m*(m+1)/2 ≤ 316410 := m_mono m 795 h_m_308
  have h_pc_M_308 : Nat.primeCounting 316410 = 27307 := pc_thm_316410
  have h_pc_K_prev_308 : Nat.primeCounting 271962 = 23801 := pc_thm_271962
  have h_k_309 : k ≥ 522 := staircase_step_K_direct k m 51156 316410 271962 27307 23801 522 heq h_m_mono_308 h_pc_M_308 h_pc_K_prev_308 rfl (by decide)
  have h_pc_K_next_308 : Nat.primeCounting 273006 = 23888 := pc_thm_273006
  have h_pc_M_next_val_308 : Nat.primeCounting 316410 = 27307 := pc_thm_316410
  have h_m_309 : m ≤ 794 := staircase_step_M_direct k m 51156 273006 316410 23888 27307 794 heq (k_mono 522 k h_k_309) h_pc_K_next_308 h_pc_M_next_val_308 rfl (by decide)
  -- Step 309: k >= 522, m <= 794 => k >= 523
  have h_m_mono_309 : m*(m+1)/2 ≤ 315615 := m_mono m 794 h_m_309
  have h_pc_M_309 : Nat.primeCounting 315615 = 27245 := pc_thm_315615
  have h_pc_K_prev_309 : Nat.primeCounting 273006 = 23888 := pc_thm_273006
  have h_k_310 : k ≥ 523 := staircase_step_K_direct k m 51156 315615 273006 27245 23888 523 heq h_m_mono_309 h_pc_M_309 h_pc_K_prev_309 rfl (by decide)
  have h_pc_K_next_309 : Nat.primeCounting 274052 = 23961 := pc_thm_274052
  have h_pc_M_next_val_309 : Nat.primeCounting 315615 = 27245 := pc_thm_315615
  have h_m_310 : m ≤ 793 := staircase_step_M_direct k m 51156 274052 315615 23961 27245 793 heq (k_mono 523 k h_k_310) h_pc_K_next_309 h_pc_M_next_val_309 rfl (by decide)
  -- Step 310: k >= 523, m <= 793 => k >= 524
  have h_m_mono_310 : m*(m+1)/2 ≤ 314821 := m_mono m 793 h_m_310
  have h_pc_M_310 : Nat.primeCounting 314821 = 27185 := pc_thm_314821
  have h_pc_K_prev_310 : Nat.primeCounting 274052 = 23961 := pc_thm_274052
  have h_k_311 : k ≥ 524 := staircase_step_K_direct k m 51156 314821 274052 27185 23961 524 heq h_m_mono_310 h_pc_M_310 h_pc_K_prev_310 rfl (by decide)
  have h_pc_K_next_310 : Nat.primeCounting 275100 = 24046 := pc_thm_275100
  have h_pc_M_next_val_310 : Nat.primeCounting 314028 = 27122 := pc_thm_314028
  have h_m_311 : m ≤ 791 := staircase_step_M_direct k m 51156 275100 314028 24046 27122 791 heq (k_mono 524 k h_k_311) h_pc_K_next_310 h_pc_M_next_val_310 rfl (by decide)
  -- Step 311: k >= 524, m <= 791 => k >= 525
  have h_m_mono_311 : m*(m+1)/2 ≤ 313236 := m_mono m 791 h_m_311
  have h_pc_M_311 : Nat.primeCounting 313236 = 27051 := pc_thm_313236
  have h_pc_K_prev_311 : Nat.primeCounting 275100 = 24046 := pc_thm_275100
  have h_k_312 : k ≥ 525 := staircase_step_K_direct k m 51156 313236 275100 27051 24046 525 heq h_m_mono_311 h_pc_M_311 h_pc_K_prev_311 rfl (by decide)
  have h_pc_K_next_311 : Nat.primeCounting 276150 = 24134 := pc_thm_276150
  have h_pc_M_next_val_311 : Nat.primeCounting 313236 = 27051 := pc_thm_313236
  have h_m_312 : m ≤ 790 := staircase_step_M_direct k m 51156 276150 313236 24134 27051 790 heq (k_mono 525 k h_k_312) h_pc_K_next_311 h_pc_M_next_val_311 rfl (by decide)
  -- Step 312: k >= 525, m <= 790 => k >= 526
  have h_m_mono_312 : m*(m+1)/2 ≤ 312445 := m_mono m 790 h_m_312
  have h_pc_M_312 : Nat.primeCounting 312445 = 26990 := pc_thm_312445
  have h_pc_K_prev_312 : Nat.primeCounting 276150 = 24134 := pc_thm_276150
  have h_k_313 : k ≥ 526 := staircase_step_K_direct k m 51156 312445 276150 26990 24134 526 heq h_m_mono_312 h_pc_M_312 h_pc_K_prev_312 rfl (by decide)
  have h_pc_K_next_312 : Nat.primeCounting 277202 = 24218 := pc_thm_277202
  have h_pc_M_next_val_312 : Nat.primeCounting 312445 = 26990 := pc_thm_312445
  have h_m_313 : m ≤ 789 := staircase_step_M_direct k m 51156 277202 312445 24218 26990 789 heq (k_mono 526 k h_k_313) h_pc_K_next_312 h_pc_M_next_val_312 rfl (by decide)
  -- Step 313: k >= 526, m <= 789 => k >= 527
  have h_m_mono_313 : m*(m+1)/2 ≤ 311655 := m_mono m 789 h_m_313
  have h_pc_M_313 : Nat.primeCounting 311655 = 26924 := pc_thm_311655
  have h_pc_K_prev_313 : Nat.primeCounting 277202 = 24218 := pc_thm_277202
  have h_k_314 : k ≥ 527 := staircase_step_K_direct k m 51156 311655 277202 26924 24218 527 heq h_m_mono_313 h_pc_M_313 h_pc_K_prev_313 rfl (by decide)
  have h_pc_K_next_313 : Nat.primeCounting 278256 = 24299 := pc_thm_278256
  have h_pc_M_next_val_313 : Nat.primeCounting 310866 = 26869 := pc_thm_310866
  have h_m_314 : m ≤ 787 := staircase_step_M_direct k m 51156 278256 310866 24299 26869 787 heq (k_mono 527 k h_k_314) h_pc_K_next_313 h_pc_M_next_val_313 rfl (by decide)
  -- Step 314: k >= 527, m <= 787 => k >= 528
  have h_m_mono_314 : m*(m+1)/2 ≤ 310078 := m_mono m 787 h_m_314
  have h_pc_M_314 : Nat.primeCounting 310078 = 26805 := pc_thm_310078
  have h_pc_K_prev_314 : Nat.primeCounting 278256 = 24299 := pc_thm_278256
  have h_k_315 : k ≥ 528 := staircase_step_K_direct k m 51156 310078 278256 26805 24299 528 heq h_m_mono_314 h_pc_M_314 h_pc_K_prev_314 rfl (by decide)
  have h_pc_K_next_314 : Nat.primeCounting 279312 = 24380 := pc_thm_279312
  have h_pc_M_next_val_314 : Nat.primeCounting 310078 = 26805 := pc_thm_310078
  have h_m_315 : m ≤ 786 := staircase_step_M_direct k m 51156 279312 310078 24380 26805 786 heq (k_mono 528 k h_k_315) h_pc_K_next_314 h_pc_M_next_val_314 rfl (by decide)
  -- Step 315: k >= 528, m <= 786 => k >= 529
  have h_m_mono_315 : m*(m+1)/2 ≤ 309291 := m_mono m 786 h_m_315
  have h_pc_M_315 : Nat.primeCounting 309291 = 26747 := pc_thm_309291
  have h_pc_K_prev_315 : Nat.primeCounting 279312 = 24380 := pc_thm_279312
  have h_k_316 : k ≥ 529 := staircase_step_K_direct k m 51156 309291 279312 26747 24380 529 heq h_m_mono_315 h_pc_M_315 h_pc_K_prev_315 rfl (by decide)
  have h_pc_K_next_315 : Nat.primeCounting 280370 = 24463 := pc_thm_280370
  have h_pc_M_next_val_315 : Nat.primeCounting 309291 = 26747 := pc_thm_309291
  have h_m_316 : m ≤ 785 := staircase_step_M_direct k m 51156 280370 309291 24463 26747 785 heq (k_mono 529 k h_k_316) h_pc_K_next_315 h_pc_M_next_val_315 rfl (by decide)
  exact ⟨h_k_316, h_m_316⟩

theorem staircase_part_21 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_316 : k ≥ 529) (h_m_316 : m ≤ 785) : k ≥ 544 ∧ m ≤ 764 := by
  -- Step 316: k >= 529, m <= 785 => k >= 530
  have h_m_mono_316 : m*(m+1)/2 ≤ 308505 := m_mono m 785 h_m_316
  have h_pc_M_316 : Nat.primeCounting 308505 = 26682 := pc_thm_308505
  have h_pc_K_prev_316 : Nat.primeCounting 280370 = 24463 := pc_thm_280370
  have h_k_317 : k ≥ 530 := staircase_step_K_direct k m 51156 308505 280370 26682 24463 530 heq h_m_mono_316 h_pc_M_316 h_pc_K_prev_316 rfl (by decide)
  have h_pc_K_next_316 : Nat.primeCounting 281430 = 24553 := pc_thm_281430
  have h_pc_M_next_val_316 : Nat.primeCounting 307720 = 26630 := pc_thm_307720
  have h_m_317 : m ≤ 783 := staircase_step_M_direct k m 51156 281430 307720 24553 26630 783 heq (k_mono 530 k h_k_317) h_pc_K_next_316 h_pc_M_next_val_316 rfl (by decide)
  -- Step 317: k >= 530, m <= 783 => k >= 531
  have h_m_mono_317 : m*(m+1)/2 ≤ 306936 := m_mono m 783 h_m_317
  have h_pc_M_317 : Nat.primeCounting 306936 = 26566 := pc_thm_306936
  have h_pc_K_prev_317 : Nat.primeCounting 281430 = 24553 := pc_thm_281430
  have h_k_318 : k ≥ 531 := staircase_step_K_direct k m 51156 306936 281430 26566 24553 531 heq h_m_mono_317 h_pc_M_317 h_pc_K_prev_317 rfl (by decide)
  have h_pc_K_next_317 : Nat.primeCounting 282492 = 24643 := pc_thm_282492
  have h_pc_M_next_val_317 : Nat.primeCounting 306936 = 26566 := pc_thm_306936
  have h_m_318 : m ≤ 782 := staircase_step_M_direct k m 51156 282492 306936 24643 26566 782 heq (k_mono 531 k h_k_318) h_pc_K_next_317 h_pc_M_next_val_317 rfl (by decide)
  -- Step 318: k >= 531, m <= 782 => k >= 532
  have h_m_mono_318 : m*(m+1)/2 ≤ 306153 := m_mono m 782 h_m_318
  have h_pc_M_318 : Nat.primeCounting 306153 = 26500 := pc_thm_306153
  have h_pc_K_prev_318 : Nat.primeCounting 282492 = 24643 := pc_thm_282492
  have h_k_319 : k ≥ 532 := staircase_step_K_direct k m 51156 306153 282492 26500 24643 532 heq h_m_mono_318 h_pc_M_318 h_pc_K_prev_318 rfl (by decide)
  have h_pc_K_next_318 : Nat.primeCounting 283556 = 24719 := pc_thm_283556
  have h_pc_M_next_val_318 : Nat.primeCounting 305371 = 26438 := pc_thm_305371
  have h_m_319 : m ≤ 780 := staircase_step_M_direct k m 51156 283556 305371 24719 26438 780 heq (k_mono 532 k h_k_319) h_pc_K_next_318 h_pc_M_next_val_318 rfl (by decide)
  -- Step 319: k >= 532, m <= 780 => k >= 533
  have h_m_mono_319 : m*(m+1)/2 ≤ 304590 := m_mono m 780 h_m_319
  have h_pc_M_319 : Nat.primeCounting 304590 = 26373 := pc_thm_304590
  have h_pc_K_prev_319 : Nat.primeCounting 283556 = 24719 := pc_thm_283556
  have h_k_320 : k ≥ 533 := staircase_step_K_direct k m 51156 304590 283556 26373 24719 533 heq h_m_mono_319 h_pc_M_319 h_pc_K_prev_319 rfl (by decide)
  have h_pc_K_next_319 : Nat.primeCounting 284622 = 24807 := pc_thm_284622
  have h_pc_M_next_val_319 : Nat.primeCounting 304590 = 26373 := pc_thm_304590
  have h_m_320 : m ≤ 779 := staircase_step_M_direct k m 51156 284622 304590 24807 26373 779 heq (k_mono 533 k h_k_320) h_pc_K_next_319 h_pc_M_next_val_319 rfl (by decide)
  -- Step 320: k >= 533, m <= 779 => k >= 534
  have h_m_mono_320 : m*(m+1)/2 ≤ 303810 := m_mono m 779 h_m_320
  have h_pc_M_320 : Nat.primeCounting 303810 = 26308 := pc_thm_303810
  have h_pc_K_prev_320 : Nat.primeCounting 284622 = 24807 := pc_thm_284622
  have h_k_321 : k ≥ 534 := staircase_step_K_direct k m 51156 303810 284622 26308 24807 534 heq h_m_mono_320 h_pc_M_320 h_pc_K_prev_320 rfl (by decide)
  have h_pc_K_next_320 : Nat.primeCounting 285690 = 24897 := pc_thm_285690
  have h_pc_M_next_val_320 : Nat.primeCounting 303810 = 26308 := pc_thm_303810
  have h_m_321 : m ≤ 778 := staircase_step_M_direct k m 51156 285690 303810 24897 26308 778 heq (k_mono 534 k h_k_321) h_pc_K_next_320 h_pc_M_next_val_320 rfl (by decide)
  -- Step 321: k >= 534, m <= 778 => k >= 535
  have h_m_mono_321 : m*(m+1)/2 ≤ 303031 := m_mono m 778 h_m_321
  have h_pc_M_321 : Nat.primeCounting 303031 = 26242 := pc_thm_303031
  have h_pc_K_prev_321 : Nat.primeCounting 285690 = 24897 := pc_thm_285690
  have h_k_322 : k ≥ 535 := staircase_step_K_direct k m 51156 303031 285690 26242 24897 535 heq h_m_mono_321 h_pc_M_321 h_pc_K_prev_321 rfl (by decide)
  have h_pc_K_next_321 : Nat.primeCounting 286760 = 24977 := pc_thm_286760
  have h_pc_M_next_val_321 : Nat.primeCounting 303031 = 26242 := pc_thm_303031
  have h_m_322 : m ≤ 777 := staircase_step_M_direct k m 51156 286760 303031 24977 26242 777 heq (k_mono 535 k h_k_322) h_pc_K_next_321 h_pc_M_next_val_321 rfl (by decide)
  -- Step 322: k >= 535, m <= 777 => k >= 536
  have h_m_mono_322 : m*(m+1)/2 ≤ 302253 := m_mono m 777 h_m_322
  have h_pc_M_322 : Nat.primeCounting 302253 = 26178 := pc_thm_302253
  have h_pc_K_prev_322 : Nat.primeCounting 286760 = 24977 := pc_thm_286760
  have h_k_323 : k ≥ 536 := staircase_step_K_direct k m 51156 302253 286760 26178 24977 536 heq h_m_mono_322 h_pc_M_322 h_pc_K_prev_322 rfl (by decide)
  have h_pc_K_next_322 : Nat.primeCounting 287832 = 25051 := pc_thm_287832
  have h_pc_M_next_val_322 : Nat.primeCounting 301476 = 26120 := pc_thm_301476
  have h_m_323 : m ≤ 775 := staircase_step_M_direct k m 51156 287832 301476 25051 26120 775 heq (k_mono 536 k h_k_323) h_pc_K_next_322 h_pc_M_next_val_322 rfl (by decide)
  -- Step 323: k >= 536, m <= 775 => k >= 537
  have h_m_mono_323 : m*(m+1)/2 ≤ 300700 := m_mono m 775 h_m_323
  have h_pc_M_323 : Nat.primeCounting 300700 = 26054 := pc_thm_300700
  have h_pc_K_prev_323 : Nat.primeCounting 287832 = 25051 := pc_thm_287832
  have h_k_324 : k ≥ 537 := staircase_step_K_direct k m 51156 300700 287832 26054 25051 537 heq h_m_mono_323 h_pc_M_323 h_pc_K_prev_323 rfl (by decide)
  have h_pc_K_next_323 : Nat.primeCounting 288906 = 25129 := pc_thm_288906
  have h_pc_M_next_val_323 : Nat.primeCounting 300700 = 26054 := pc_thm_300700
  have h_m_324 : m ≤ 774 := staircase_step_M_direct k m 51156 288906 300700 25129 26054 774 heq (k_mono 537 k h_k_324) h_pc_K_next_323 h_pc_M_next_val_323 rfl (by decide)
  -- Step 324: k >= 537, m <= 774 => k >= 538
  have h_m_mono_324 : m*(m+1)/2 ≤ 299925 := m_mono m 774 h_m_324
  have h_pc_M_324 : Nat.primeCounting 299925 = 25990 := pc_thm_299925
  have h_pc_K_prev_324 : Nat.primeCounting 288906 = 25129 := pc_thm_288906
  have h_k_325 : k ≥ 538 := staircase_step_K_direct k m 51156 299925 288906 25990 25129 538 heq h_m_mono_324 h_pc_M_324 h_pc_K_prev_324 rfl (by decide)
  have h_pc_K_next_324 : Nat.primeCounting 289982 = 25222 := pc_thm_289982
  have h_pc_M_next_val_324 : Nat.primeCounting 299925 = 25990 := pc_thm_299925
  have h_m_325 : m ≤ 773 := staircase_step_M_direct k m 51156 289982 299925 25222 25990 773 heq (k_mono 538 k h_k_325) h_pc_K_next_324 h_pc_M_next_val_324 rfl (by decide)
  -- Step 325: k >= 538, m <= 773 => k >= 539
  have h_m_mono_325 : m*(m+1)/2 ≤ 299151 := m_mono m 773 h_m_325
  have h_pc_M_325 : Nat.primeCounting 299151 = 25932 := pc_thm_299151
  have h_pc_K_prev_325 : Nat.primeCounting 289982 = 25222 := pc_thm_289982
  have h_k_326 : k ≥ 539 := staircase_step_K_direct k m 51156 299151 289982 25932 25222 539 heq h_m_mono_325 h_pc_M_325 h_pc_K_prev_325 rfl (by decide)
  have h_pc_K_next_325 : Nat.primeCounting 291060 = 25313 := pc_thm_291060
  have h_pc_M_next_val_325 : Nat.primeCounting 298378 = 25877 := pc_thm_298378
  have h_m_326 : m ≤ 771 := staircase_step_M_direct k m 51156 291060 298378 25313 25877 771 heq (k_mono 539 k h_k_326) h_pc_K_next_325 h_pc_M_next_val_325 rfl (by decide)
  -- Step 326: k >= 539, m <= 771 => k >= 540
  have h_m_mono_326 : m*(m+1)/2 ≤ 297606 := m_mono m 771 h_m_326
  have h_pc_M_326 : Nat.primeCounting 297606 = 25814 := pc_thm_297606
  have h_pc_K_prev_326 : Nat.primeCounting 291060 = 25313 := pc_thm_291060
  have h_k_327 : k ≥ 540 := staircase_step_K_direct k m 51156 297606 291060 25814 25313 540 heq h_m_mono_326 h_pc_M_326 h_pc_K_prev_326 rfl (by decide)
  have h_pc_K_next_326 : Nat.primeCounting 292140 = 25395 := pc_thm_292140
  have h_pc_M_next_val_326 : Nat.primeCounting 296835 = 25762 := pc_thm_296835
  have h_m_327 : m ≤ 769 := staircase_step_M_direct k m 51156 292140 296835 25395 25762 769 heq (k_mono 540 k h_k_327) h_pc_K_next_326 h_pc_M_next_val_326 rfl (by decide)
  -- Step 327: k >= 540, m <= 769 => k >= 541
  have h_m_mono_327 : m*(m+1)/2 ≤ 296065 := m_mono m 769 h_m_327
  have h_pc_M_327 : Nat.primeCounting 296065 = 25696 := pc_thm_296065
  have h_pc_K_prev_327 : Nat.primeCounting 292140 = 25395 := pc_thm_292140
  have h_k_328 : k ≥ 541 := staircase_step_K_direct k m 51156 296065 292140 25696 25395 541 heq h_m_mono_327 h_pc_M_327 h_pc_K_prev_327 rfl (by decide)
  have h_pc_K_next_327 : Nat.primeCounting 293222 = 25481 := pc_thm_293222
  have h_pc_M_next_val_327 : Nat.primeCounting 296065 = 25696 := pc_thm_296065
  have h_m_328 : m ≤ 768 := staircase_step_M_direct k m 51156 293222 296065 25481 25696 768 heq (k_mono 541 k h_k_328) h_pc_K_next_327 h_pc_M_next_val_327 rfl (by decide)
  -- Step 328: k >= 541, m <= 768 => k >= 542
  have h_m_mono_328 : m*(m+1)/2 ≤ 295296 := m_mono m 768 h_m_328
  have h_pc_M_328 : Nat.primeCounting 295296 = 25639 := pc_thm_295296
  have h_pc_K_prev_328 : Nat.primeCounting 293222 = 25481 := pc_thm_293222
  have h_k_329 : k ≥ 542 := staircase_step_K_direct k m 51156 295296 293222 25639 25481 542 heq h_m_mono_328 h_pc_M_328 h_pc_K_prev_328 rfl (by decide)
  have h_pc_K_next_328 : Nat.primeCounting 294306 = 25559 := pc_thm_294306
  have h_pc_M_next_val_328 : Nat.primeCounting 295296 = 25639 := pc_thm_295296
  have h_m_329 : m ≤ 767 := staircase_step_M_direct k m 51156 294306 295296 25559 25639 767 heq (k_mono 542 k h_k_329) h_pc_K_next_328 h_pc_M_next_val_328 rfl (by decide)
  -- Step 329: k >= 542, m <= 767 => k >= 543
  have h_m_mono_329 : m*(m+1)/2 ≤ 294528 := m_mono m 767 h_m_329
  have h_pc_M_329 : Nat.primeCounting 294528 = 25579 := pc_thm_294528
  have h_pc_K_prev_329 : Nat.primeCounting 294306 = 25559 := pc_thm_294306
  have h_k_330 : k ≥ 543 := staircase_step_K_direct k m 51156 294528 294306 25579 25559 543 heq h_m_mono_329 h_pc_M_329 h_pc_K_prev_329 rfl (by decide)
  have h_pc_K_next_329 : Nat.primeCounting 295392 = 25645 := pc_thm_295392
  have h_pc_M_next_val_329 : Nat.primeCounting 293761 = 25516 := pc_thm_293761
  have h_m_330 : m ≤ 765 := staircase_step_M_direct k m 51156 295392 293761 25645 25516 765 heq (k_mono 543 k h_k_330) h_pc_K_next_329 h_pc_M_next_val_329 rfl (by decide)
  -- Step 330: k >= 543, m <= 765 => k >= 544
  have h_m_mono_330 : m*(m+1)/2 ≤ 292995 := m_mono m 765 h_m_330
  have h_pc_M_330 : Nat.primeCounting 292995 = 25463 := pc_thm_292995
  have h_pc_K_prev_330 : Nat.primeCounting 295392 = 25645 := pc_thm_295392
  have h_k_331 : k ≥ 544 := staircase_step_K_direct k m 51156 292995 295392 25463 25645 544 heq h_m_mono_330 h_pc_M_330 h_pc_K_prev_330 rfl (by decide)
  have h_pc_K_next_330 : Nat.primeCounting 296480 = 25726 := pc_thm_296480
  have h_pc_M_next_val_330 : Nat.primeCounting 292995 = 25463 := pc_thm_292995
  have h_m_331 : m ≤ 764 := staircase_step_M_direct k m 51156 296480 292995 25726 25463 764 heq (k_mono 544 k h_k_331) h_pc_K_next_330 h_pc_M_next_val_330 rfl (by decide)
  exact ⟨h_k_331, h_m_331⟩

theorem staircase_part_22 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_331 : k ≥ 544) (h_m_331 : m ≤ 764) : k ≥ 559 ∧ m ≤ 742 := by
  -- Step 331: k >= 544, m <= 764 => k >= 545
  have h_m_mono_331 : m*(m+1)/2 ≤ 292230 := m_mono m 764 h_m_331
  have h_pc_M_331 : Nat.primeCounting 292230 = 25401 := pc_thm_292230
  have h_pc_K_prev_331 : Nat.primeCounting 296480 = 25726 := pc_thm_296480
  have h_k_332 : k ≥ 545 := staircase_step_K_direct k m 51156 292230 296480 25401 25726 545 heq h_m_mono_331 h_pc_M_331 h_pc_K_prev_331 rfl (by decide)
  have h_pc_K_next_331 : Nat.primeCounting 297570 = 25811 := pc_thm_297570
  have h_pc_M_next_val_331 : Nat.primeCounting 291466 = 25346 := pc_thm_291466
  have h_m_332 : m ≤ 762 := staircase_step_M_direct k m 51156 297570 291466 25811 25346 762 heq (k_mono 545 k h_k_332) h_pc_K_next_331 h_pc_M_next_val_331 rfl (by decide)
  -- Step 332: k >= 545, m <= 762 => k >= 546
  have h_m_mono_332 : m*(m+1)/2 ≤ 290703 := m_mono m 762 h_m_332
  have h_pc_M_332 : Nat.primeCounting 290703 = 25286 := pc_thm_290703
  have h_pc_K_prev_332 : Nat.primeCounting 297570 = 25811 := pc_thm_297570
  have h_k_333 : k ≥ 546 := staircase_step_K_direct k m 51156 290703 297570 25286 25811 546 heq h_m_mono_332 h_pc_M_332 h_pc_K_prev_332 rfl (by decide)
  have h_pc_K_next_332 : Nat.primeCounting 298662 = 25894 := pc_thm_298662
  have h_pc_M_next_val_332 : Nat.primeCounting 290703 = 25286 := pc_thm_290703
  have h_m_333 : m ≤ 761 := staircase_step_M_direct k m 51156 298662 290703 25894 25286 761 heq (k_mono 546 k h_k_333) h_pc_K_next_332 h_pc_M_next_val_332 rfl (by decide)
  -- Step 333: k >= 546, m <= 761 => k >= 547
  have h_m_mono_333 : m*(m+1)/2 ≤ 289941 := m_mono m 761 h_m_333
  have h_pc_M_333 : Nat.primeCounting 289941 = 25218 := pc_thm_289941
  have h_pc_K_prev_333 : Nat.primeCounting 298662 = 25894 := pc_thm_298662
  have h_k_334 : k ≥ 547 := staircase_step_K_direct k m 51156 289941 298662 25218 25894 547 heq h_m_mono_333 h_pc_M_333 h_pc_K_prev_333 rfl (by decide)
  have h_pc_K_next_333 : Nat.primeCounting 299756 = 25980 := pc_thm_299756
  have h_pc_M_next_val_333 : Nat.primeCounting 289941 = 25218 := pc_thm_289941
  have h_m_334 : m ≤ 760 := staircase_step_M_direct k m 51156 299756 289941 25980 25218 760 heq (k_mono 547 k h_k_334) h_pc_K_next_333 h_pc_M_next_val_333 rfl (by decide)
  -- Step 334: k >= 547, m <= 760 => k >= 548
  have h_m_mono_334 : m*(m+1)/2 ≤ 289180 := m_mono m 760 h_m_334
  have h_pc_M_334 : Nat.primeCounting 289180 = 25159 := pc_thm_289180
  have h_pc_K_prev_334 : Nat.primeCounting 299756 = 25980 := pc_thm_299756
  have h_k_335 : k ≥ 548 := staircase_step_K_direct k m 51156 289180 299756 25159 25980 548 heq h_m_mono_334 h_pc_M_334 h_pc_K_prev_334 rfl (by decide)
  have h_pc_K_next_334 : Nat.primeCounting 300852 = 26069 := pc_thm_300852
  have h_pc_M_next_val_334 : Nat.primeCounting 288420 = 25093 := pc_thm_288420
  have h_m_335 : m ≤ 758 := staircase_step_M_direct k m 51156 300852 288420 26069 25093 758 heq (k_mono 548 k h_k_335) h_pc_K_next_334 h_pc_M_next_val_334 rfl (by decide)
  -- Step 335: k >= 548, m <= 758 => k >= 549
  have h_m_mono_335 : m*(m+1)/2 ≤ 287661 := m_mono m 758 h_m_335
  have h_pc_M_335 : Nat.primeCounting 287661 = 25039 := pc_thm_287661
  have h_pc_K_prev_335 : Nat.primeCounting 300852 = 26069 := pc_thm_300852
  have h_k_336 : k ≥ 549 := staircase_step_K_direct k m 51156 287661 300852 25039 26069 549 heq h_m_mono_335 h_pc_M_335 h_pc_K_prev_335 rfl (by decide)
  have h_pc_K_next_335 : Nat.primeCounting 301950 = 26160 := pc_thm_301950
  have h_pc_M_next_val_335 : Nat.primeCounting 287661 = 25039 := pc_thm_287661
  have h_m_336 : m ≤ 757 := staircase_step_M_direct k m 51156 301950 287661 26160 25039 757 heq (k_mono 549 k h_k_336) h_pc_K_next_335 h_pc_M_next_val_335 rfl (by decide)
  -- Step 336: k >= 549, m <= 757 => k >= 550
  have h_m_mono_336 : m*(m+1)/2 ≤ 286903 := m_mono m 757 h_m_336
  have h_pc_M_336 : Nat.primeCounting 286903 = 24986 := pc_thm_286903
  have h_pc_K_prev_336 : Nat.primeCounting 301950 = 26160 := pc_thm_301950
  have h_k_337 : k ≥ 550 := staircase_step_K_direct k m 51156 286903 301950 24986 26160 550 heq h_m_mono_336 h_pc_M_336 h_pc_K_prev_336 rfl (by decide)
  have h_pc_K_next_336 : Nat.primeCounting 303050 = 26243 := pc_thm_303050
  have h_pc_M_next_val_336 : Nat.primeCounting 286146 = 24930 := pc_thm_286146
  have h_m_337 : m ≤ 755 := staircase_step_M_direct k m 51156 303050 286146 26243 24930 755 heq (k_mono 550 k h_k_337) h_pc_K_next_336 h_pc_M_next_val_336 rfl (by decide)
  -- Step 337: k >= 550, m <= 755 => k >= 551
  have h_m_mono_337 : m*(m+1)/2 ≤ 285390 := m_mono m 755 h_m_337
  have h_pc_M_337 : Nat.primeCounting 285390 = 24871 := pc_thm_285390
  have h_pc_K_prev_337 : Nat.primeCounting 303050 = 26243 := pc_thm_303050
  have h_k_338 : k ≥ 551 := staircase_step_K_direct k m 51156 285390 303050 24871 26243 551 heq h_m_mono_337 h_pc_M_337 h_pc_K_prev_337 rfl (by decide)
  have h_pc_K_next_337 : Nat.primeCounting 304152 = 26335 := pc_thm_304152
  have h_pc_M_next_val_337 : Nat.primeCounting 285390 = 24871 := pc_thm_285390
  have h_m_338 : m ≤ 754 := staircase_step_M_direct k m 51156 304152 285390 26335 24871 754 heq (k_mono 551 k h_k_338) h_pc_K_next_337 h_pc_M_next_val_337 rfl (by decide)
  -- Step 338: k >= 551, m <= 754 => k >= 552
  have h_m_mono_338 : m*(m+1)/2 ≤ 284635 := m_mono m 754 h_m_338
  have h_pc_M_338 : Nat.primeCounting 284635 = 24809 := pc_thm_284635
  have h_pc_K_prev_338 : Nat.primeCounting 304152 = 26335 := pc_thm_304152
  have h_k_339 : k ≥ 552 := staircase_step_K_direct k m 51156 284635 304152 24809 26335 552 heq h_m_mono_338 h_pc_M_338 h_pc_K_prev_338 rfl (by decide)
  have h_pc_K_next_338 : Nat.primeCounting 305256 = 26429 := pc_thm_305256
  have h_pc_M_next_val_338 : Nat.primeCounting 283881 = 24747 := pc_thm_283881
  have h_m_339 : m ≤ 752 := staircase_step_M_direct k m 51156 305256 283881 26429 24747 752 heq (k_mono 552 k h_k_339) h_pc_K_next_338 h_pc_M_next_val_338 rfl (by decide)
  -- Step 339: k >= 552, m <= 752 => k >= 553
  have h_m_mono_339 : m*(m+1)/2 ≤ 283128 := m_mono m 752 h_m_339
  have h_pc_M_339 : Nat.primeCounting 283128 = 24693 := pc_thm_283128
  have h_pc_K_prev_339 : Nat.primeCounting 305256 = 26429 := pc_thm_305256
  have h_k_340 : k ≥ 553 := staircase_step_K_direct k m 51156 283128 305256 24693 26429 553 heq h_m_mono_339 h_pc_M_339 h_pc_K_prev_339 rfl (by decide)
  have h_pc_K_next_339 : Nat.primeCounting 306362 = 26517 := pc_thm_306362
  have h_pc_M_next_val_339 : Nat.primeCounting 283128 = 24693 := pc_thm_283128
  have h_m_340 : m ≤ 751 := staircase_step_M_direct k m 51156 306362 283128 26517 24693 751 heq (k_mono 553 k h_k_340) h_pc_K_next_339 h_pc_M_next_val_339 rfl (by decide)
  -- Step 340: k >= 553, m <= 751 => k >= 554
  have h_m_mono_340 : m*(m+1)/2 ≤ 282376 := m_mono m 751 h_m_340
  have h_pc_M_340 : Nat.primeCounting 282376 = 24631 := pc_thm_282376
  have h_pc_K_prev_340 : Nat.primeCounting 306362 = 26517 := pc_thm_306362
  have h_k_341 : k ≥ 554 := staircase_step_K_direct k m 51156 282376 306362 24631 26517 554 heq h_m_mono_340 h_pc_M_340 h_pc_K_prev_340 rfl (by decide)
  have h_pc_K_next_340 : Nat.primeCounting 307470 = 26609 := pc_thm_307470
  have h_pc_M_next_val_340 : Nat.primeCounting 281625 = 24567 := pc_thm_281625
  have h_m_341 : m ≤ 749 := staircase_step_M_direct k m 51156 307470 281625 26609 24567 749 heq (k_mono 554 k h_k_341) h_pc_K_next_340 h_pc_M_next_val_340 rfl (by decide)
  -- Step 341: k >= 554, m <= 749 => k >= 555
  have h_m_mono_341 : m*(m+1)/2 ≤ 280875 := m_mono m 749 h_m_341
  have h_pc_M_341 : Nat.primeCounting 280875 = 24504 := pc_thm_280875
  have h_pc_K_prev_341 : Nat.primeCounting 307470 = 26609 := pc_thm_307470
  have h_k_342 : k ≥ 555 := staircase_step_K_direct k m 51156 280875 307470 24504 26609 555 heq h_m_mono_341 h_pc_M_341 h_pc_K_prev_341 rfl (by decide)
  have h_pc_K_next_341 : Nat.primeCounting 308580 = 26691 := pc_thm_308580
  have h_pc_M_next_val_341 : Nat.primeCounting 280875 = 24504 := pc_thm_280875
  have h_m_342 : m ≤ 748 := staircase_step_M_direct k m 51156 308580 280875 26691 24504 748 heq (k_mono 555 k h_k_342) h_pc_K_next_341 h_pc_M_next_val_341 rfl (by decide)
  -- Step 342: k >= 555, m <= 748 => k >= 556
  have h_m_mono_342 : m*(m+1)/2 ≤ 280126 := m_mono m 748 h_m_342
  have h_pc_M_342 : Nat.primeCounting 280126 = 24443 := pc_thm_280126
  have h_pc_K_prev_342 : Nat.primeCounting 308580 = 26691 := pc_thm_308580
  have h_k_343 : k ≥ 556 := staircase_step_K_direct k m 51156 280126 308580 24443 26691 556 heq h_m_mono_342 h_pc_M_342 h_pc_K_prev_342 rfl (by decide)
  have h_pc_K_next_342 : Nat.primeCounting 309692 = 26780 := pc_thm_309692
  have h_pc_M_next_val_342 : Nat.primeCounting 279378 = 24384 := pc_thm_279378
  have h_m_343 : m ≤ 746 := staircase_step_M_direct k m 51156 309692 279378 26780 24384 746 heq (k_mono 556 k h_k_343) h_pc_K_next_342 h_pc_M_next_val_342 rfl (by decide)
  -- Step 343: k >= 556, m <= 746 => k >= 557
  have h_m_mono_343 : m*(m+1)/2 ≤ 278631 := m_mono m 746 h_m_343
  have h_pc_M_343 : Nat.primeCounting 278631 = 24330 := pc_thm_278631
  have h_pc_K_prev_343 : Nat.primeCounting 309692 = 26780 := pc_thm_309692
  have h_k_344 : k ≥ 557 := staircase_step_K_direct k m 51156 278631 309692 24330 26780 557 heq h_m_mono_343 h_pc_M_343 h_pc_K_prev_343 rfl (by decide)
  have h_pc_K_next_343 : Nat.primeCounting 310806 = 26864 := pc_thm_310806
  have h_pc_M_next_val_343 : Nat.primeCounting 278631 = 24330 := pc_thm_278631
  have h_m_344 : m ≤ 745 := staircase_step_M_direct k m 51156 310806 278631 26864 24330 745 heq (k_mono 557 k h_k_344) h_pc_K_next_343 h_pc_M_next_val_343 rfl (by decide)
  -- Step 344: k >= 557, m <= 745 => k >= 558
  have h_m_mono_344 : m*(m+1)/2 ≤ 277885 := m_mono m 745 h_m_344
  have h_pc_M_344 : Nat.primeCounting 277885 = 24270 := pc_thm_277885
  have h_pc_K_prev_344 : Nat.primeCounting 310806 = 26864 := pc_thm_310806
  have h_k_345 : k ≥ 558 := staircase_step_K_direct k m 51156 277885 310806 24270 26864 558 heq h_m_mono_344 h_pc_M_344 h_pc_K_prev_344 rfl (by decide)
  have h_pc_K_next_344 : Nat.primeCounting 311922 = 26944 := pc_thm_311922
  have h_pc_M_next_val_344 : Nat.primeCounting 277140 = 24213 := pc_thm_277140
  have h_m_345 : m ≤ 743 := staircase_step_M_direct k m 51156 311922 277140 26944 24213 743 heq (k_mono 558 k h_k_345) h_pc_K_next_344 h_pc_M_next_val_344 rfl (by decide)
  -- Step 345: k >= 558, m <= 743 => k >= 559
  have h_m_mono_345 : m*(m+1)/2 ≤ 276396 := m_mono m 743 h_m_345
  have h_pc_M_345 : Nat.primeCounting 276396 = 24156 := pc_thm_276396
  have h_pc_K_prev_345 : Nat.primeCounting 311922 = 26944 := pc_thm_311922
  have h_k_346 : k ≥ 559 := staircase_step_K_direct k m 51156 276396 311922 24156 26944 559 heq h_m_mono_345 h_pc_M_345 h_pc_K_prev_345 rfl (by decide)
  have h_pc_K_next_345 : Nat.primeCounting 313040 = 27038 := pc_thm_313040
  have h_pc_M_next_val_345 : Nat.primeCounting 276396 = 24156 := pc_thm_276396
  have h_m_346 : m ≤ 742 := staircase_step_M_direct k m 51156 313040 276396 27038 24156 742 heq (k_mono 559 k h_k_346) h_pc_K_next_345 h_pc_M_next_val_345 rfl (by decide)
  exact ⟨h_k_346, h_m_346⟩

theorem staircase_part_23 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_346 : k ≥ 559) (h_m_346 : m ≤ 742) : k ≥ 574 ∧ m ≤ 718 := by
  -- Step 346: k >= 559, m <= 742 => k >= 560
  have h_m_mono_346 : m*(m+1)/2 ≤ 275653 := m_mono m 742 h_m_346
  have h_pc_M_346 : Nat.primeCounting 275653 = 24093 := pc_thm_275653
  have h_pc_K_prev_346 : Nat.primeCounting 313040 = 27038 := pc_thm_313040
  have h_k_347 : k ≥ 560 := staircase_step_K_direct k m 51156 275653 313040 24093 27038 560 heq h_m_mono_346 h_pc_M_346 h_pc_K_prev_346 rfl (by decide)
  have h_pc_K_next_346 : Nat.primeCounting 314160 = 27131 := pc_thm_314160
  have h_pc_M_next_val_346 : Nat.primeCounting 274911 = 24031 := pc_thm_274911
  have h_m_347 : m ≤ 740 := staircase_step_M_direct k m 51156 314160 274911 27131 24031 740 heq (k_mono 560 k h_k_347) h_pc_K_next_346 h_pc_M_next_val_346 rfl (by decide)
  -- Step 347: k >= 560, m <= 740 => k >= 561
  have h_m_mono_347 : m*(m+1)/2 ≤ 274170 := m_mono m 740 h_m_347
  have h_pc_M_347 : Nat.primeCounting 274170 = 23972 := pc_thm_274170
  have h_pc_K_prev_347 : Nat.primeCounting 314160 = 27131 := pc_thm_314160
  have h_k_348 : k ≥ 561 := staircase_step_K_direct k m 51156 274170 314160 23972 27131 561 heq h_m_mono_347 h_pc_M_347 h_pc_K_prev_347 rfl (by decide)
  have h_pc_K_next_347 : Nat.primeCounting 315282 = 27217 := pc_thm_315282
  have h_pc_M_next_val_347 : Nat.primeCounting 274170 = 23972 := pc_thm_274170
  have h_m_348 : m ≤ 739 := staircase_step_M_direct k m 51156 315282 274170 27217 23972 739 heq (k_mono 561 k h_k_348) h_pc_K_next_347 h_pc_M_next_val_347 rfl (by decide)
  -- Step 348: k >= 561, m <= 739 => k >= 562
  have h_m_mono_348 : m*(m+1)/2 ≤ 273430 := m_mono m 739 h_m_348
  have h_pc_M_348 : Nat.primeCounting 273430 = 23918 := pc_thm_273430
  have h_pc_K_prev_348 : Nat.primeCounting 315282 = 27217 := pc_thm_315282
  have h_k_349 : k ≥ 562 := staircase_step_K_direct k m 51156 273430 315282 23918 27217 562 heq h_m_mono_348 h_pc_M_348 h_pc_K_prev_348 rfl (by decide)
  have h_pc_K_next_348 : Nat.primeCounting 316406 = 27307 := pc_thm_316406
  have h_pc_M_next_val_348 : Nat.primeCounting 272691 = 23862 := pc_thm_272691
  have h_m_349 : m ≤ 737 := staircase_step_M_direct k m 51156 316406 272691 27307 23862 737 heq (k_mono 562 k h_k_349) h_pc_K_next_348 h_pc_M_next_val_348 rfl (by decide)
  -- Step 349: k >= 562, m <= 737 => k >= 563
  have h_m_mono_349 : m*(m+1)/2 ≤ 271953 := m_mono m 737 h_m_349
  have h_pc_M_349 : Nat.primeCounting 271953 = 23801 := pc_thm_271953
  have h_pc_K_prev_349 : Nat.primeCounting 316406 = 27307 := pc_thm_316406
  have h_k_350 : k ≥ 563 := staircase_step_K_direct k m 51156 271953 316406 23801 27307 563 heq h_m_mono_349 h_pc_M_349 h_pc_K_prev_349 rfl (by decide)
  have h_pc_K_next_349 : Nat.primeCounting 317532 = 27399 := pc_thm_317532
  have h_pc_M_next_val_349 : Nat.primeCounting 271953 = 23801 := pc_thm_271953
  have h_m_350 : m ≤ 736 := staircase_step_M_direct k m 51156 317532 271953 27399 23801 736 heq (k_mono 563 k h_k_350) h_pc_K_next_349 h_pc_M_next_val_349 rfl (by decide)
  -- Step 350: k >= 563, m <= 736 => k >= 564
  have h_m_mono_350 : m*(m+1)/2 ≤ 271216 := m_mono m 736 h_m_350
  have h_pc_M_350 : Nat.primeCounting 271216 = 23743 := pc_thm_271216
  have h_pc_K_prev_350 : Nat.primeCounting 317532 = 27399 := pc_thm_317532
  have h_k_351 : k ≥ 564 := staircase_step_K_direct k m 51156 271216 317532 23743 27399 564 heq h_m_mono_350 h_pc_M_350 h_pc_K_prev_350 rfl (by decide)
  have h_pc_K_next_350 : Nat.primeCounting 318660 = 27493 := pc_thm_318660
  have h_pc_M_next_val_350 : Nat.primeCounting 270480 = 23683 := pc_thm_270480
  have h_m_351 : m ≤ 734 := staircase_step_M_direct k m 51156 318660 270480 27493 23683 734 heq (k_mono 564 k h_k_351) h_pc_K_next_350 h_pc_M_next_val_350 rfl (by decide)
  -- Step 351: k >= 564, m <= 734 => k >= 565
  have h_m_mono_351 : m*(m+1)/2 ≤ 269745 := m_mono m 734 h_m_351
  have h_pc_M_351 : Nat.primeCounting 269745 = 23626 := pc_thm_269745
  have h_pc_K_prev_351 : Nat.primeCounting 318660 = 27493 := pc_thm_318660
  have h_k_352 : k ≥ 565 := staircase_step_K_direct k m 51156 269745 318660 23626 27493 565 heq h_m_mono_351 h_pc_M_351 h_pc_K_prev_351 rfl (by decide)
  have h_pc_K_next_351 : Nat.primeCounting 319790 = 27591 := pc_thm_319790
  have h_pc_M_next_val_351 : Nat.primeCounting 269745 = 23626 := pc_thm_269745
  have h_m_352 : m ≤ 733 := staircase_step_M_direct k m 51156 319790 269745 27591 23626 733 heq (k_mono 565 k h_k_352) h_pc_K_next_351 h_pc_M_next_val_351 rfl (by decide)
  -- Step 352: k >= 565, m <= 733 => k >= 566
  have h_m_mono_352 : m*(m+1)/2 ≤ 269011 := m_mono m 733 h_m_352
  have h_pc_M_352 : Nat.primeCounting 269011 = 23564 := pc_thm_269011
  have h_pc_K_prev_352 : Nat.primeCounting 319790 = 27591 := pc_thm_319790
  have h_k_353 : k ≥ 566 := staircase_step_K_direct k m 51156 269011 319790 23564 27591 566 heq h_m_mono_352 h_pc_M_352 h_pc_K_prev_352 rfl (by decide)
  have h_pc_K_next_352 : Nat.primeCounting 320922 = 27682 := pc_thm_320922
  have h_pc_M_next_val_352 : Nat.primeCounting 268278 = 23508 := pc_thm_268278
  have h_m_353 : m ≤ 731 := staircase_step_M_direct k m 51156 320922 268278 27682 23508 731 heq (k_mono 566 k h_k_353) h_pc_K_next_352 h_pc_M_next_val_352 rfl (by decide)
  -- Step 353: k >= 566, m <= 731 => k >= 567
  have h_m_mono_353 : m*(m+1)/2 ≤ 267546 := m_mono m 731 h_m_353
  have h_pc_M_353 : Nat.primeCounting 267546 = 23442 := pc_thm_267546
  have h_pc_K_prev_353 : Nat.primeCounting 320922 = 27682 := pc_thm_320922
  have h_k_354 : k ≥ 567 := staircase_step_K_direct k m 51156 267546 320922 23442 27682 567 heq h_m_mono_353 h_pc_M_353 h_pc_K_prev_353 rfl (by decide)
  have h_pc_K_next_353 : Nat.primeCounting 322056 = 27773 := pc_thm_322056
  have h_pc_M_next_val_353 : Nat.primeCounting 267546 = 23442 := pc_thm_267546
  have h_m_354 : m ≤ 730 := staircase_step_M_direct k m 51156 322056 267546 27773 23442 730 heq (k_mono 567 k h_k_354) h_pc_K_next_353 h_pc_M_next_val_353 rfl (by decide)
  -- Step 354: k >= 567, m <= 730 => k >= 568
  have h_m_mono_354 : m*(m+1)/2 ≤ 266815 := m_mono m 730 h_m_354
  have h_pc_M_354 : Nat.primeCounting 266815 = 23375 := pc_thm_266815
  have h_pc_K_prev_354 : Nat.primeCounting 322056 = 27773 := pc_thm_322056
  have h_k_355 : k ≥ 568 := staircase_step_K_direct k m 51156 266815 322056 23375 27773 568 heq h_m_mono_354 h_pc_M_354 h_pc_K_prev_354 rfl (by decide)
  have h_pc_K_next_354 : Nat.primeCounting 323192 = 27861 := pc_thm_323192
  have h_pc_M_next_val_354 : Nat.primeCounting 266085 = 23319 := pc_thm_266085
  have h_m_355 : m ≤ 728 := staircase_step_M_direct k m 51156 323192 266085 27861 23319 728 heq (k_mono 568 k h_k_355) h_pc_K_next_354 h_pc_M_next_val_354 rfl (by decide)
  -- Step 355: k >= 568, m <= 728 => k >= 569
  have h_m_mono_355 : m*(m+1)/2 ≤ 265356 := m_mono m 728 h_m_355
  have h_pc_M_355 : Nat.primeCounting 265356 = 23259 := pc_thm_265356
  have h_pc_K_prev_355 : Nat.primeCounting 323192 = 27861 := pc_thm_323192
  have h_k_356 : k ≥ 569 := staircase_step_K_direct k m 51156 265356 323192 23259 27861 569 heq h_m_mono_355 h_pc_M_355 h_pc_K_prev_355 rfl (by decide)
  have h_pc_K_next_355 : Nat.primeCounting 324330 = 27946 := pc_thm_324330
  have h_pc_M_next_val_355 : Nat.primeCounting 265356 = 23259 := pc_thm_265356
  have h_m_356 : m ≤ 727 := staircase_step_M_direct k m 51156 324330 265356 27946 23259 727 heq (k_mono 569 k h_k_356) h_pc_K_next_355 h_pc_M_next_val_355 rfl (by decide)
  -- Step 356: k >= 569, m <= 727 => k >= 570
  have h_m_mono_356 : m*(m+1)/2 ≤ 264628 := m_mono m 727 h_m_356
  have h_pc_M_356 : Nat.primeCounting 264628 = 23197 := pc_thm_264628
  have h_pc_K_prev_356 : Nat.primeCounting 324330 = 27946 := pc_thm_324330
  have h_k_357 : k ≥ 570 := staircase_step_K_direct k m 51156 264628 324330 23197 27946 570 heq h_m_mono_356 h_pc_M_356 h_pc_K_prev_356 rfl (by decide)
  have h_pc_K_next_356 : Nat.primeCounting 325470 = 28045 := pc_thm_325470
  have h_pc_M_next_val_356 : Nat.primeCounting 263901 = 23141 := pc_thm_263901
  have h_m_357 : m ≤ 725 := staircase_step_M_direct k m 51156 325470 263901 28045 23141 725 heq (k_mono 570 k h_k_357) h_pc_K_next_356 h_pc_M_next_val_356 rfl (by decide)
  -- Step 357: k >= 570, m <= 725 => k >= 571
  have h_m_mono_357 : m*(m+1)/2 ≤ 263175 := m_mono m 725 h_m_357
  have h_pc_M_357 : Nat.primeCounting 263175 = 23080 := pc_thm_263175
  have h_pc_K_prev_357 : Nat.primeCounting 325470 = 28045 := pc_thm_325470
  have h_k_358 : k ≥ 571 := staircase_step_K_direct k m 51156 263175 325470 23080 28045 571 heq h_m_mono_357 h_pc_M_357 h_pc_K_prev_357 rfl (by decide)
  have h_pc_K_next_357 : Nat.primeCounting 326612 = 28135 := pc_thm_326612
  have h_pc_M_next_val_357 : Nat.primeCounting 262450 = 23024 := pc_thm_262450
  have h_m_358 : m ≤ 723 := staircase_step_M_direct k m 51156 326612 262450 28135 23024 723 heq (k_mono 571 k h_k_358) h_pc_K_next_357 h_pc_M_next_val_357 rfl (by decide)
  -- Step 358: k >= 571, m <= 723 => k >= 572
  have h_m_mono_358 : m*(m+1)/2 ≤ 261726 := m_mono m 723 h_m_358
  have h_pc_M_358 : Nat.primeCounting 261726 = 22970 := pc_thm_261726
  have h_pc_K_prev_358 : Nat.primeCounting 326612 = 28135 := pc_thm_326612
  have h_k_359 : k ≥ 572 := staircase_step_K_direct k m 51156 261726 326612 22970 28135 572 heq h_m_mono_358 h_pc_M_358 h_pc_K_prev_358 rfl (by decide)
  have h_pc_K_next_358 : Nat.primeCounting 327756 = 28228 := pc_thm_327756
  have h_pc_M_next_val_358 : Nat.primeCounting 261726 = 22970 := pc_thm_261726
  have h_m_359 : m ≤ 722 := staircase_step_M_direct k m 51156 327756 261726 28228 22970 722 heq (k_mono 572 k h_k_359) h_pc_K_next_358 h_pc_M_next_val_358 rfl (by decide)
  -- Step 359: k >= 572, m <= 722 => k >= 573
  have h_m_mono_359 : m*(m+1)/2 ≤ 261003 := m_mono m 722 h_m_359
  have h_pc_M_359 : Nat.primeCounting 261003 = 22914 := pc_thm_261003
  have h_pc_K_prev_359 : Nat.primeCounting 327756 = 28228 := pc_thm_327756
  have h_k_360 : k ≥ 573 := staircase_step_K_direct k m 51156 261003 327756 22914 28228 573 heq h_m_mono_359 h_pc_M_359 h_pc_K_prev_359 rfl (by decide)
  have h_pc_K_next_359 : Nat.primeCounting 328902 = 28318 := pc_thm_328902
  have h_pc_M_next_val_359 : Nat.primeCounting 260281 = 22858 := pc_thm_260281
  have h_m_360 : m ≤ 720 := staircase_step_M_direct k m 51156 328902 260281 28318 22858 720 heq (k_mono 573 k h_k_360) h_pc_K_next_359 h_pc_M_next_val_359 rfl (by decide)
  -- Step 360: k >= 573, m <= 720 => k >= 574
  have h_m_mono_360 : m*(m+1)/2 ≤ 259560 := m_mono m 720 h_m_360
  have h_pc_M_360 : Nat.primeCounting 259560 = 22801 := pc_thm_259560
  have h_pc_K_prev_360 : Nat.primeCounting 328902 = 28318 := pc_thm_328902
  have h_k_361 : k ≥ 574 := staircase_step_K_direct k m 51156 259560 328902 22801 28318 574 heq h_m_mono_360 h_pc_M_360 h_pc_K_prev_360 rfl (by decide)
  have h_pc_K_next_360 : Nat.primeCounting 330050 = 28409 := pc_thm_330050
  have h_pc_M_next_val_360 : Nat.primeCounting 258840 = 22749 := pc_thm_258840
  have h_m_361 : m ≤ 718 := staircase_step_M_direct k m 51156 330050 258840 28409 22749 718 heq (k_mono 574 k h_k_361) h_pc_K_next_360 h_pc_M_next_val_360 rfl (by decide)
  exact ⟨h_k_361, h_m_361⟩

theorem staircase_part_24 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_361 : k ≥ 574) (h_m_361 : m ≤ 718) : k ≥ 589 ∧ m ≤ 695 := by
  -- Step 361: k >= 574, m <= 718 => k >= 575
  have h_m_mono_361 : m*(m+1)/2 ≤ 258121 := m_mono m 718 h_m_361
  have h_pc_M_361 : Nat.primeCounting 258121 = 22685 := pc_thm_258121
  have h_pc_K_prev_361 : Nat.primeCounting 330050 = 28409 := pc_thm_330050
  have h_k_362 : k ≥ 575 := staircase_step_K_direct k m 51156 258121 330050 22685 28409 575 heq h_m_mono_361 h_pc_M_361 h_pc_K_prev_361 rfl (by decide)
  have h_pc_K_next_361 : Nat.primeCounting 331200 = 28498 := pc_thm_331200
  have h_pc_M_next_val_361 : Nat.primeCounting 258121 = 22685 := pc_thm_258121
  have h_m_362 : m ≤ 717 := staircase_step_M_direct k m 51156 331200 258121 28498 22685 717 heq (k_mono 575 k h_k_362) h_pc_K_next_361 h_pc_M_next_val_361 rfl (by decide)
  -- Step 362: k >= 575, m <= 717 => k >= 576
  have h_m_mono_362 : m*(m+1)/2 ≤ 257403 := m_mono m 717 h_m_362
  have h_pc_M_362 : Nat.primeCounting 257403 = 22630 := pc_thm_257403
  have h_pc_K_prev_362 : Nat.primeCounting 331200 = 28498 := pc_thm_331200
  have h_k_363 : k ≥ 576 := staircase_step_K_direct k m 51156 257403 331200 22630 28498 576 heq h_m_mono_362 h_pc_M_362 h_pc_K_prev_362 rfl (by decide)
  have h_pc_K_next_362 : Nat.primeCounting 332352 = 28593 := pc_thm_332352
  have h_pc_M_next_val_362 : Nat.primeCounting 256686 = 22577 := pc_thm_256686
  have h_m_363 : m ≤ 715 := staircase_step_M_direct k m 51156 332352 256686 28593 22577 715 heq (k_mono 576 k h_k_363) h_pc_K_next_362 h_pc_M_next_val_362 rfl (by decide)
  -- Step 363: k >= 576, m <= 715 => k >= 577
  have h_m_mono_363 : m*(m+1)/2 ≤ 255970 := m_mono m 715 h_m_363
  have h_pc_M_363 : Nat.primeCounting 255970 = 22521 := pc_thm_255970
  have h_pc_K_prev_363 : Nat.primeCounting 332352 = 28593 := pc_thm_332352
  have h_k_364 : k ≥ 577 := staircase_step_K_direct k m 51156 255970 332352 22521 28593 577 heq h_m_mono_363 h_pc_M_363 h_pc_K_prev_363 rfl (by decide)
  have h_pc_K_next_363 : Nat.primeCounting 333506 = 28683 := pc_thm_333506
  have h_pc_M_next_val_363 : Nat.primeCounting 255970 = 22521 := pc_thm_255970
  have h_m_364 : m ≤ 714 := staircase_step_M_direct k m 51156 333506 255970 28683 22521 714 heq (k_mono 577 k h_k_364) h_pc_K_next_363 h_pc_M_next_val_363 rfl (by decide)
  -- Step 364: k >= 577, m <= 714 => k >= 578
  have h_m_mono_364 : m*(m+1)/2 ≤ 255255 := m_mono m 714 h_m_364
  have h_pc_M_364 : Nat.primeCounting 255255 = 22466 := pc_thm_255255
  have h_pc_K_prev_364 : Nat.primeCounting 333506 = 28683 := pc_thm_333506
  have h_k_365 : k ≥ 578 := staircase_step_K_direct k m 51156 255255 333506 22466 28683 578 heq h_m_mono_364 h_pc_M_364 h_pc_K_prev_364 rfl (by decide)
  have h_pc_K_next_364 : Nat.primeCounting 334662 = 28769 := pc_thm_334662
  have h_pc_M_next_val_364 : Nat.primeCounting 254541 = 22400 := pc_thm_254541
  have h_m_365 : m ≤ 712 := staircase_step_M_direct k m 51156 334662 254541 28769 22400 712 heq (k_mono 578 k h_k_365) h_pc_K_next_364 h_pc_M_next_val_364 rfl (by decide)
  -- Step 365: k >= 578, m <= 712 => k >= 579
  have h_m_mono_365 : m*(m+1)/2 ≤ 253828 := m_mono m 712 h_m_365
  have h_pc_M_365 : Nat.primeCounting 253828 = 22347 := pc_thm_253828
  have h_pc_K_prev_365 : Nat.primeCounting 334662 = 28769 := pc_thm_334662
  have h_k_366 : k ≥ 579 := staircase_step_K_direct k m 51156 253828 334662 22347 28769 579 heq h_m_mono_365 h_pc_M_365 h_pc_K_prev_365 rfl (by decide)
  have h_pc_K_next_365 : Nat.primeCounting 335820 = 28861 := pc_thm_335820
  have h_pc_M_next_val_365 : Nat.primeCounting 253828 = 22347 := pc_thm_253828
  have h_m_366 : m ≤ 711 := staircase_step_M_direct k m 51156 335820 253828 28861 22347 711 heq (k_mono 579 k h_k_366) h_pc_K_next_365 h_pc_M_next_val_365 rfl (by decide)
  -- Step 366: k >= 579, m <= 711 => k >= 580
  have h_m_mono_366 : m*(m+1)/2 ≤ 253116 := m_mono m 711 h_m_366
  have h_pc_M_366 : Nat.primeCounting 253116 = 22288 := pc_thm_253116
  have h_pc_K_prev_366 : Nat.primeCounting 335820 = 28861 := pc_thm_335820
  have h_k_367 : k ≥ 580 := staircase_step_K_direct k m 51156 253116 335820 22288 28861 580 heq h_m_mono_366 h_pc_M_366 h_pc_K_prev_366 rfl (by decide)
  have h_pc_K_next_366 : Nat.primeCounting 336980 = 28954 := pc_thm_336980
  have h_pc_M_next_val_366 : Nat.primeCounting 252405 = 22235 := pc_thm_252405
  have h_m_367 : m ≤ 709 := staircase_step_M_direct k m 51156 336980 252405 28954 22235 709 heq (k_mono 580 k h_k_367) h_pc_K_next_366 h_pc_M_next_val_366 rfl (by decide)
  -- Step 367: k >= 580, m <= 709 => k >= 581
  have h_m_mono_367 : m*(m+1)/2 ≤ 251695 := m_mono m 709 h_m_367
  have h_pc_M_367 : Nat.primeCounting 251695 = 22179 := pc_thm_251695
  have h_pc_K_prev_367 : Nat.primeCounting 336980 = 28954 := pc_thm_336980
  have h_k_368 : k ≥ 581 := staircase_step_K_direct k m 51156 251695 336980 22179 28954 581 heq h_m_mono_367 h_pc_M_367 h_pc_K_prev_367 rfl (by decide)
  have h_pc_K_next_367 : Nat.primeCounting 338142 = 29043 := pc_thm_338142
  have h_pc_M_next_val_367 : Nat.primeCounting 250986 = 22114 := pc_thm_250986
  have h_m_368 : m ≤ 707 := staircase_step_M_direct k m 51156 338142 250986 29043 22114 707 heq (k_mono 581 k h_k_368) h_pc_K_next_367 h_pc_M_next_val_367 rfl (by decide)
  -- Step 368: k >= 581, m <= 707 => k >= 582
  have h_m_mono_368 : m*(m+1)/2 ≤ 250278 := m_mono m 707 h_m_368
  have h_pc_M_368 : Nat.primeCounting 250278 = 22064 := pc_thm_250278
  have h_pc_K_prev_368 : Nat.primeCounting 338142 = 29043 := pc_thm_338142
  have h_k_369 : k ≥ 582 := staircase_step_K_direct k m 51156 250278 338142 22064 29043 582 heq h_m_mono_368 h_pc_M_368 h_pc_K_prev_368 rfl (by decide)
  have h_pc_K_next_368 : Nat.primeCounting 339306 = 29136 := pc_thm_339306
  have h_pc_M_next_val_368 : Nat.primeCounting 250278 = 22064 := pc_thm_250278
  have h_m_369 : m ≤ 706 := staircase_step_M_direct k m 51156 339306 250278 29136 22064 706 heq (k_mono 582 k h_k_369) h_pc_K_next_368 h_pc_M_next_val_368 rfl (by decide)
  -- Step 369: k >= 582, m <= 706 => k >= 583
  have h_m_mono_369 : m*(m+1)/2 ≤ 249571 := m_mono m 706 h_m_369
  have h_pc_M_369 : Nat.primeCounting 249571 = 22011 := pc_thm_249571
  have h_pc_K_prev_369 : Nat.primeCounting 339306 = 29136 := pc_thm_339306
  have h_k_370 : k ≥ 583 := staircase_step_K_direct k m 51156 249571 339306 22011 29136 583 heq h_m_mono_369 h_pc_M_369 h_pc_K_prev_369 rfl (by decide)
  have h_pc_K_next_369 : Nat.primeCounting 340472 = 29220 := pc_thm_340472
  have h_pc_M_next_val_369 : Nat.primeCounting 248865 = 21953 := pc_thm_248865
  have h_m_370 : m ≤ 704 := staircase_step_M_direct k m 51156 340472 248865 29220 21953 704 heq (k_mono 583 k h_k_370) h_pc_K_next_369 h_pc_M_next_val_369 rfl (by decide)
  -- Step 370: k >= 583, m <= 704 => k >= 584
  have h_m_mono_370 : m*(m+1)/2 ≤ 248160 := m_mono m 704 h_m_370
  have h_pc_M_370 : Nat.primeCounting 248160 = 21890 := pc_thm_248160
  have h_pc_K_prev_370 : Nat.primeCounting 340472 = 29220 := pc_thm_340472
  have h_k_371 : k ≥ 584 := staircase_step_K_direct k m 51156 248160 340472 21890 29220 584 heq h_m_mono_370 h_pc_M_370 h_pc_K_prev_370 rfl (by decide)
  have h_pc_K_next_370 : Nat.primeCounting 341640 = 29315 := pc_thm_341640
  have h_pc_M_next_val_370 : Nat.primeCounting 248160 = 21890 := pc_thm_248160
  have h_m_371 : m ≤ 703 := staircase_step_M_direct k m 51156 341640 248160 29315 21890 703 heq (k_mono 584 k h_k_371) h_pc_K_next_370 h_pc_M_next_val_370 rfl (by decide)
  -- Step 371: k >= 584, m <= 703 => k >= 585
  have h_m_mono_371 : m*(m+1)/2 ≤ 247456 := m_mono m 703 h_m_371
  have h_pc_M_371 : Nat.primeCounting 247456 = 21830 := pc_thm_247456
  have h_pc_K_prev_371 : Nat.primeCounting 341640 = 29315 := pc_thm_341640
  have h_k_372 : k ≥ 585 := staircase_step_K_direct k m 51156 247456 341640 21830 29315 585 heq h_m_mono_371 h_pc_M_371 h_pc_K_prev_371 rfl (by decide)
  have h_pc_K_next_371 : Nat.primeCounting 342810 = 29407 := pc_thm_342810
  have h_pc_M_next_val_371 : Nat.primeCounting 246753 = 21773 := pc_thm_246753
  have h_m_372 : m ≤ 701 := staircase_step_M_direct k m 51156 342810 246753 29407 21773 701 heq (k_mono 585 k h_k_372) h_pc_K_next_371 h_pc_M_next_val_371 rfl (by decide)
  -- Step 372: k >= 585, m <= 701 => k >= 586
  have h_m_mono_372 : m*(m+1)/2 ≤ 246051 := m_mono m 701 h_m_372
  have h_pc_M_372 : Nat.primeCounting 246051 = 21716 := pc_thm_246051
  have h_pc_K_prev_372 : Nat.primeCounting 342810 = 29407 := pc_thm_342810
  have h_k_373 : k ≥ 586 := staircase_step_K_direct k m 51156 246051 342810 21716 29407 586 heq h_m_mono_372 h_pc_M_372 h_pc_K_prev_372 rfl (by decide)
  have h_pc_K_next_372 : Nat.primeCounting 343982 = 29499 := pc_thm_343982
  have h_pc_M_next_val_372 : Nat.primeCounting 245350 = 21659 := pc_thm_245350
  have h_m_373 : m ≤ 699 := staircase_step_M_direct k m 51156 343982 245350 29499 21659 699 heq (k_mono 586 k h_k_373) h_pc_K_next_372 h_pc_M_next_val_372 rfl (by decide)
  -- Step 373: k >= 586, m <= 699 => k >= 587
  have h_m_mono_373 : m*(m+1)/2 ≤ 244650 := m_mono m 699 h_m_373
  have h_pc_M_373 : Nat.primeCounting 244650 = 21605 := pc_thm_244650
  have h_pc_K_prev_373 : Nat.primeCounting 343982 = 29499 := pc_thm_343982
  have h_k_374 : k ≥ 587 := staircase_step_K_direct k m 51156 244650 343982 21605 29499 587 heq h_m_mono_373 h_pc_M_373 h_pc_K_prev_373 rfl (by decide)
  have h_pc_K_next_373 : Nat.primeCounting 345156 = 29592 := pc_thm_345156
  have h_pc_M_next_val_373 : Nat.primeCounting 244650 = 21605 := pc_thm_244650
  have h_m_374 : m ≤ 698 := staircase_step_M_direct k m 51156 345156 244650 29592 21605 698 heq (k_mono 587 k h_k_374) h_pc_K_next_373 h_pc_M_next_val_373 rfl (by decide)
  -- Step 374: k >= 587, m <= 698 => k >= 588
  have h_m_mono_374 : m*(m+1)/2 ≤ 243951 := m_mono m 698 h_m_374
  have h_pc_M_374 : Nat.primeCounting 243951 = 21542 := pc_thm_243951
  have h_pc_K_prev_374 : Nat.primeCounting 345156 = 29592 := pc_thm_345156
  have h_k_375 : k ≥ 588 := staircase_step_K_direct k m 51156 243951 345156 21542 29592 588 heq h_m_mono_374 h_pc_M_374 h_pc_K_prev_374 rfl (by decide)
  have h_pc_K_next_374 : Nat.primeCounting 346332 = 29682 := pc_thm_346332
  have h_pc_M_next_val_374 : Nat.primeCounting 243253 = 21488 := pc_thm_243253
  have h_m_375 : m ≤ 696 := staircase_step_M_direct k m 51156 346332 243253 29682 21488 696 heq (k_mono 588 k h_k_375) h_pc_K_next_374 h_pc_M_next_val_374 rfl (by decide)
  -- Step 375: k >= 588, m <= 696 => k >= 589
  have h_m_mono_375 : m*(m+1)/2 ≤ 242556 := m_mono m 696 h_m_375
  have h_pc_M_375 : Nat.primeCounting 242556 = 21435 := pc_thm_242556
  have h_pc_K_prev_375 : Nat.primeCounting 346332 = 29682 := pc_thm_346332
  have h_k_376 : k ≥ 589 := staircase_step_K_direct k m 51156 242556 346332 21435 29682 589 heq h_m_mono_375 h_pc_M_375 h_pc_K_prev_375 rfl (by decide)
  have h_pc_K_next_375 : Nat.primeCounting 347510 = 29776 := pc_thm_347510
  have h_pc_M_next_val_375 : Nat.primeCounting 242556 = 21435 := pc_thm_242556
  have h_m_376 : m ≤ 695 := staircase_step_M_direct k m 51156 347510 242556 29776 21435 695 heq (k_mono 589 k h_k_376) h_pc_K_next_375 h_pc_M_next_val_375 rfl (by decide)
  exact ⟨h_k_376, h_m_376⟩

theorem staircase_part_25 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_376 : k ≥ 589) (h_m_376 : m ≤ 695) : k ≥ 604 ∧ m ≤ 669 := by
  -- Step 376: k >= 589, m <= 695 => k >= 590
  have h_m_mono_376 : m*(m+1)/2 ≤ 241860 := m_mono m 695 h_m_376
  have h_pc_M_376 : Nat.primeCounting 241860 = 21375 := pc_thm_241860
  have h_pc_K_prev_376 : Nat.primeCounting 347510 = 29776 := pc_thm_347510
  have h_k_377 : k ≥ 590 := staircase_step_K_direct k m 51156 241860 347510 21375 29776 590 heq h_m_mono_376 h_pc_M_376 h_pc_K_prev_376 rfl (by decide)
  have h_pc_K_next_376 : Nat.primeCounting 348690 = 29873 := pc_thm_348690
  have h_pc_M_next_val_376 : Nat.primeCounting 241165 = 21314 := pc_thm_241165
  have h_m_377 : m ≤ 693 := staircase_step_M_direct k m 51156 348690 241165 29873 21314 693 heq (k_mono 590 k h_k_377) h_pc_K_next_376 h_pc_M_next_val_376 rfl (by decide)
  -- Step 377: k >= 590, m <= 693 => k >= 591
  have h_m_mono_377 : m*(m+1)/2 ≤ 240471 := m_mono m 693 h_m_377
  have h_pc_M_377 : Nat.primeCounting 240471 = 21258 := pc_thm_240471
  have h_pc_K_prev_377 : Nat.primeCounting 348690 = 29873 := pc_thm_348690
  have h_k_378 : k ≥ 591 := staircase_step_K_direct k m 51156 240471 348690 21258 29873 591 heq h_m_mono_377 h_pc_M_377 h_pc_K_prev_377 rfl (by decide)
  have h_pc_K_next_377 : Nat.primeCounting 349872 = 29965 := pc_thm_349872
  have h_pc_M_next_val_377 : Nat.primeCounting 239778 = 21202 := pc_thm_239778
  have h_m_378 : m ≤ 691 := staircase_step_M_direct k m 51156 349872 239778 29965 21202 691 heq (k_mono 591 k h_k_378) h_pc_K_next_377 h_pc_M_next_val_377 rfl (by decide)
  -- Step 378: k >= 591, m <= 691 => k >= 592
  have h_m_mono_378 : m*(m+1)/2 ≤ 239086 := m_mono m 691 h_m_378
  have h_pc_M_378 : Nat.primeCounting 239086 = 21148 := pc_thm_239086
  have h_pc_K_prev_378 : Nat.primeCounting 349872 = 29965 := pc_thm_349872
  have h_k_379 : k ≥ 592 := staircase_step_K_direct k m 51156 239086 349872 21148 29965 592 heq h_m_mono_378 h_pc_M_378 h_pc_K_prev_378 rfl (by decide)
  have h_pc_K_next_378 : Nat.primeCounting 351056 = 30058 := pc_thm_351056
  have h_pc_M_next_val_378 : Nat.primeCounting 239086 = 21148 := pc_thm_239086
  have h_m_379 : m ≤ 690 := staircase_step_M_direct k m 51156 351056 239086 30058 21148 690 heq (k_mono 592 k h_k_379) h_pc_K_next_378 h_pc_M_next_val_378 rfl (by decide)
  -- Step 379: k >= 592, m <= 690 => k >= 593
  have h_m_mono_379 : m*(m+1)/2 ≤ 238395 := m_mono m 690 h_m_379
  have h_pc_M_379 : Nat.primeCounting 238395 = 21093 := pc_thm_238395
  have h_pc_K_prev_379 : Nat.primeCounting 351056 = 30058 := pc_thm_351056
  have h_k_380 : k ≥ 593 := staircase_step_K_direct k m 51156 238395 351056 21093 30058 593 heq h_m_mono_379 h_pc_M_379 h_pc_K_prev_379 rfl (by decide)
  have h_pc_K_next_379 : Nat.primeCounting 352242 = 30151 := pc_thm_352242
  have h_pc_M_next_val_379 : Nat.primeCounting 237705 = 21032 := pc_thm_237705
  have h_m_380 : m ≤ 688 := staircase_step_M_direct k m 51156 352242 237705 30151 21032 688 heq (k_mono 593 k h_k_380) h_pc_K_next_379 h_pc_M_next_val_379 rfl (by decide)
  -- Step 380: k >= 593, m <= 688 => k >= 594
  have h_m_mono_380 : m*(m+1)/2 ≤ 237016 := m_mono m 688 h_m_380
  have h_pc_M_380 : Nat.primeCounting 237016 = 20983 := pc_thm_237016
  have h_pc_K_prev_380 : Nat.primeCounting 352242 = 30151 := pc_thm_352242
  have h_k_381 : k ≥ 594 := staircase_step_K_direct k m 51156 237016 352242 20983 30151 594 heq h_m_mono_380 h_pc_M_380 h_pc_K_prev_380 rfl (by decide)
  have h_pc_K_next_380 : Nat.primeCounting 353430 = 30245 := pc_thm_353430
  have h_pc_M_next_val_380 : Nat.primeCounting 236328 = 20928 := pc_thm_236328
  have h_m_381 : m ≤ 686 := staircase_step_M_direct k m 51156 353430 236328 30245 20928 686 heq (k_mono 594 k h_k_381) h_pc_K_next_380 h_pc_M_next_val_380 rfl (by decide)
  -- Step 381: k >= 594, m <= 686 => k >= 595
  have h_m_mono_381 : m*(m+1)/2 ≤ 235641 := m_mono m 686 h_m_381
  have h_pc_M_381 : Nat.primeCounting 235641 = 20880 := pc_thm_235641
  have h_pc_K_prev_381 : Nat.primeCounting 353430 = 30245 := pc_thm_353430
  have h_k_382 : k ≥ 595 := staircase_step_K_direct k m 51156 235641 353430 20880 30245 595 heq h_m_mono_381 h_pc_M_381 h_pc_K_prev_381 rfl (by decide)
  have h_pc_K_next_381 : Nat.primeCounting 354620 = 30345 := pc_thm_354620
  have h_pc_M_next_val_381 : Nat.primeCounting 234955 = 20827 := pc_thm_234955
  have h_m_382 : m ≤ 684 := staircase_step_M_direct k m 51156 354620 234955 30345 20827 684 heq (k_mono 595 k h_k_382) h_pc_K_next_381 h_pc_M_next_val_381 rfl (by decide)
  -- Step 382: k >= 595, m <= 684 => k >= 596
  have h_m_mono_382 : m*(m+1)/2 ≤ 234270 := m_mono m 684 h_m_382
  have h_pc_M_382 : Nat.primeCounting 234270 = 20769 := pc_thm_234270
  have h_pc_K_prev_382 : Nat.primeCounting 354620 = 30345 := pc_thm_354620
  have h_k_383 : k ≥ 596 := staircase_step_K_direct k m 51156 234270 354620 20769 30345 596 heq h_m_mono_382 h_pc_M_382 h_pc_K_prev_382 rfl (by decide)
  have h_pc_K_next_382 : Nat.primeCounting 355812 = 30442 := pc_thm_355812
  have h_pc_M_next_val_382 : Nat.primeCounting 233586 = 20715 := pc_thm_233586
  have h_m_383 : m ≤ 682 := staircase_step_M_direct k m 51156 355812 233586 30442 20715 682 heq (k_mono 596 k h_k_383) h_pc_K_next_382 h_pc_M_next_val_382 rfl (by decide)
  -- Step 383: k >= 596, m <= 682 => k >= 597
  have h_m_mono_383 : m*(m+1)/2 ≤ 232903 := m_mono m 682 h_m_383
  have h_pc_M_383 : Nat.primeCounting 232903 = 20669 := pc_thm_232903
  have h_pc_K_prev_383 : Nat.primeCounting 355812 = 30442 := pc_thm_355812
  have h_k_384 : k ≥ 597 := staircase_step_K_direct k m 51156 232903 355812 20669 30442 597 heq h_m_mono_383 h_pc_M_383 h_pc_K_prev_383 rfl (by decide)
  have h_pc_K_next_383 : Nat.primeCounting 357006 = 30523 := pc_thm_357006
  have h_pc_M_next_val_383 : Nat.primeCounting 232903 = 20669 := pc_thm_232903
  have h_m_384 : m ≤ 681 := staircase_step_M_direct k m 51156 357006 232903 30523 20669 681 heq (k_mono 597 k h_k_384) h_pc_K_next_383 h_pc_M_next_val_383 rfl (by decide)
  -- Step 384: k >= 597, m <= 681 => k >= 598
  have h_m_mono_384 : m*(m+1)/2 ≤ 232221 := m_mono m 681 h_m_384
  have h_pc_M_384 : Nat.primeCounting 232221 = 20618 := pc_thm_232221
  have h_pc_K_prev_384 : Nat.primeCounting 357006 = 30523 := pc_thm_357006
  have h_k_385 : k ≥ 598 := staircase_step_K_direct k m 51156 232221 357006 20618 30523 598 heq h_m_mono_384 h_pc_M_384 h_pc_K_prev_384 rfl (by decide)
  have h_pc_K_next_384 : Nat.primeCounting 358202 = 30615 := pc_thm_358202
  have h_pc_M_next_val_384 : Nat.primeCounting 231540 = 20563 := pc_thm_231540
  have h_m_385 : m ≤ 679 := staircase_step_M_direct k m 51156 358202 231540 30615 20563 679 heq (k_mono 598 k h_k_385) h_pc_K_next_384 h_pc_M_next_val_384 rfl (by decide)
  -- Step 385: k >= 598, m <= 679 => k >= 599
  have h_m_mono_385 : m*(m+1)/2 ≤ 230860 := m_mono m 679 h_m_385
  have h_pc_M_385 : Nat.primeCounting 230860 = 20509 := pc_thm_230860
  have h_pc_K_prev_385 : Nat.primeCounting 358202 = 30615 := pc_thm_358202
  have h_k_386 : k ≥ 599 := staircase_step_K_direct k m 51156 230860 358202 20509 30615 599 heq h_m_mono_385 h_pc_M_385 h_pc_K_prev_385 rfl (by decide)
  have h_pc_K_next_385 : Nat.primeCounting 359400 = 30718 := pc_thm_359400
  have h_pc_M_next_val_385 : Nat.primeCounting 230181 = 20452 := pc_thm_230181
  have h_m_386 : m ≤ 677 := staircase_step_M_direct k m 51156 359400 230181 30718 20452 677 heq (k_mono 599 k h_k_386) h_pc_K_next_385 h_pc_M_next_val_385 rfl (by decide)
  -- Step 386: k >= 599, m <= 677 => k >= 600
  have h_m_mono_386 : m*(m+1)/2 ≤ 229503 := m_mono m 677 h_m_386
  have h_pc_M_386 : Nat.primeCounting 229503 = 20389 := pc_thm_229503
  have h_pc_K_prev_386 : Nat.primeCounting 359400 = 30718 := pc_thm_359400
  have h_k_387 : k ≥ 600 := staircase_step_K_direct k m 51156 229503 359400 20389 30718 600 heq h_m_mono_386 h_pc_M_386 h_pc_K_prev_386 rfl (by decide)
  have h_pc_K_next_386 : Nat.primeCounting 360600 = 30798 := pc_thm_360600
  have h_pc_M_next_val_386 : Nat.primeCounting 229503 = 20389 := pc_thm_229503
  have h_m_387 : m ≤ 676 := staircase_step_M_direct k m 51156 360600 229503 30798 20389 676 heq (k_mono 600 k h_k_387) h_pc_K_next_386 h_pc_M_next_val_386 rfl (by decide)
  -- Step 387: k >= 600, m <= 676 => k >= 601
  have h_m_mono_387 : m*(m+1)/2 ≤ 228826 := m_mono m 676 h_m_387
  have h_pc_M_387 : Nat.primeCounting 228826 = 20330 := pc_thm_228826
  have h_pc_K_prev_387 : Nat.primeCounting 360600 = 30798 := pc_thm_360600
  have h_k_388 : k ≥ 601 := staircase_step_K_direct k m 51156 228826 360600 20330 30798 601 heq h_m_mono_387 h_pc_M_387 h_pc_K_prev_387 rfl (by decide)
  have h_pc_K_next_387 : Nat.primeCounting 361802 = 30888 := pc_thm_361802
  have h_pc_M_next_val_387 : Nat.primeCounting 228150 = 20271 := pc_thm_228150
  have h_m_388 : m ≤ 674 := staircase_step_M_direct k m 51156 361802 228150 30888 20271 674 heq (k_mono 601 k h_k_388) h_pc_K_next_387 h_pc_M_next_val_387 rfl (by decide)
  -- Step 388: k >= 601, m <= 674 => k >= 602
  have h_m_mono_388 : m*(m+1)/2 ≤ 227475 := m_mono m 674 h_m_388
  have h_pc_M_388 : Nat.primeCounting 227475 = 20220 := pc_thm_227475
  have h_pc_K_prev_388 : Nat.primeCounting 361802 = 30888 := pc_thm_361802
  have h_k_389 : k ≥ 602 := staircase_step_K_direct k m 51156 227475 361802 20220 30888 602 heq h_m_mono_388 h_pc_M_388 h_pc_K_prev_388 rfl (by decide)
  have h_pc_K_next_388 : Nat.primeCounting 363006 = 30980 := pc_thm_363006
  have h_pc_M_next_val_388 : Nat.primeCounting 227475 = 20220 := pc_thm_227475
  have h_m_389 : m ≤ 673 := staircase_step_M_direct k m 51156 363006 227475 30980 20220 673 heq (k_mono 602 k h_k_389) h_pc_K_next_388 h_pc_M_next_val_388 rfl (by decide)
  -- Step 389: k >= 602, m <= 673 => k >= 603
  have h_m_mono_389 : m*(m+1)/2 ≤ 226801 := m_mono m 673 h_m_389
  have h_pc_M_389 : Nat.primeCounting 226801 = 20167 := pc_thm_226801
  have h_pc_K_prev_389 : Nat.primeCounting 363006 = 30980 := pc_thm_363006
  have h_k_390 : k ≥ 603 := staircase_step_K_direct k m 51156 226801 363006 20167 30980 603 heq h_m_mono_389 h_pc_M_389 h_pc_K_prev_389 rfl (by decide)
  have h_pc_K_next_389 : Nat.primeCounting 364212 = 31077 := pc_thm_364212
  have h_pc_M_next_val_389 : Nat.primeCounting 226128 = 20113 := pc_thm_226128
  have h_m_390 : m ≤ 671 := staircase_step_M_direct k m 51156 364212 226128 31077 20113 671 heq (k_mono 603 k h_k_390) h_pc_K_next_389 h_pc_M_next_val_389 rfl (by decide)
  -- Step 390: k >= 603, m <= 671 => k >= 604
  have h_m_mono_390 : m*(m+1)/2 ≤ 225456 := m_mono m 671 h_m_390
  have h_pc_M_390 : Nat.primeCounting 225456 = 20057 := pc_thm_225456
  have h_pc_K_prev_390 : Nat.primeCounting 364212 = 31077 := pc_thm_364212
  have h_k_391 : k ≥ 604 := staircase_step_K_direct k m 51156 225456 364212 20057 31077 604 heq h_m_mono_390 h_pc_M_390 h_pc_K_prev_390 rfl (by decide)
  have h_pc_K_next_390 : Nat.primeCounting 365420 = 31174 := pc_thm_365420
  have h_pc_M_next_val_390 : Nat.primeCounting 224785 = 20003 := pc_thm_224785
  have h_m_391 : m ≤ 669 := staircase_step_M_direct k m 51156 365420 224785 31174 20003 669 heq (k_mono 604 k h_k_391) h_pc_K_next_390 h_pc_M_next_val_390 rfl (by decide)
  exact ⟨h_k_391, h_m_391⟩

theorem staircase_part_26 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_391 : k ≥ 604) (h_m_391 : m ≤ 669) : k ≥ 619 ∧ m ≤ 643 := by
  -- Step 391: k >= 604, m <= 669 => k >= 605
  have h_m_mono_391 : m*(m+1)/2 ≤ 224115 := m_mono m 669 h_m_391
  have h_pc_M_391 : Nat.primeCounting 224115 = 19947 := pc_thm_224115
  have h_pc_K_prev_391 : Nat.primeCounting 365420 = 31174 := pc_thm_365420
  have h_k_392 : k ≥ 605 := staircase_step_K_direct k m 51156 224115 365420 19947 31174 605 heq h_m_mono_391 h_pc_M_391 h_pc_K_prev_391 rfl (by decide)
  have h_pc_K_next_391 : Nat.primeCounting 366630 = 31272 := pc_thm_366630
  have h_pc_M_next_val_391 : Nat.primeCounting 223446 = 19899 := pc_thm_223446
  have h_m_392 : m ≤ 667 := staircase_step_M_direct k m 51156 366630 223446 31272 19899 667 heq (k_mono 605 k h_k_392) h_pc_K_next_391 h_pc_M_next_val_391 rfl (by decide)
  -- Step 392: k >= 605, m <= 667 => k >= 606
  have h_m_mono_392 : m*(m+1)/2 ≤ 222778 := m_mono m 667 h_m_392
  have h_pc_M_392 : Nat.primeCounting 222778 = 19835 := pc_thm_222778
  have h_pc_K_prev_392 : Nat.primeCounting 366630 = 31272 := pc_thm_366630
  have h_k_393 : k ≥ 606 := staircase_step_K_direct k m 51156 222778 366630 19835 31272 606 heq h_m_mono_392 h_pc_M_392 h_pc_K_prev_392 rfl (by decide)
  have h_pc_K_next_392 : Nat.primeCounting 367842 = 31373 := pc_thm_367842
  have h_pc_M_next_val_392 : Nat.primeCounting 222111 = 19787 := pc_thm_222111
  have h_m_393 : m ≤ 665 := staircase_step_M_direct k m 51156 367842 222111 31373 19787 665 heq (k_mono 606 k h_k_393) h_pc_K_next_392 h_pc_M_next_val_392 rfl (by decide)
  -- Step 393: k >= 606, m <= 665 => k >= 607
  have h_m_mono_393 : m*(m+1)/2 ≤ 221445 := m_mono m 665 h_m_393
  have h_pc_M_393 : Nat.primeCounting 221445 = 19729 := pc_thm_221445
  have h_pc_K_prev_393 : Nat.primeCounting 367842 = 31373 := pc_thm_367842
  have h_k_394 : k ≥ 607 := staircase_step_K_direct k m 51156 221445 367842 19729 31373 607 heq h_m_mono_393 h_pc_M_393 h_pc_K_prev_393 rfl (by decide)
  have h_pc_K_next_393 : Nat.primeCounting 369056 = 31458 := pc_thm_369056
  have h_pc_M_next_val_393 : Nat.primeCounting 221445 = 19729 := pc_thm_221445
  have h_m_394 : m ≤ 664 := staircase_step_M_direct k m 51156 369056 221445 31458 19729 664 heq (k_mono 607 k h_k_394) h_pc_K_next_393 h_pc_M_next_val_393 rfl (by decide)
  -- Step 394: k >= 607, m <= 664 => k >= 608
  have h_m_mono_394 : m*(m+1)/2 ≤ 220780 := m_mono m 664 h_m_394
  have h_pc_M_394 : Nat.primeCounting 220780 = 19675 := pc_thm_220780
  have h_pc_K_prev_394 : Nat.primeCounting 369056 = 31458 := pc_thm_369056
  have h_k_395 : k ≥ 608 := staircase_step_K_direct k m 51156 220780 369056 19675 31458 608 heq h_m_mono_394 h_pc_M_394 h_pc_K_prev_394 rfl (by decide)
  have h_pc_K_next_394 : Nat.primeCounting 370272 = 31545 := pc_thm_370272
  have h_pc_M_next_val_394 : Nat.primeCounting 220116 = 19624 := pc_thm_220116
  have h_m_395 : m ≤ 662 := staircase_step_M_direct k m 51156 370272 220116 31545 19624 662 heq (k_mono 608 k h_k_395) h_pc_K_next_394 h_pc_M_next_val_394 rfl (by decide)
  -- Step 395: k >= 608, m <= 662 => k >= 609
  have h_m_mono_395 : m*(m+1)/2 ≤ 219453 := m_mono m 662 h_m_395
  have h_pc_M_395 : Nat.primeCounting 219453 = 19563 := pc_thm_219453
  have h_pc_K_prev_395 : Nat.primeCounting 370272 = 31545 := pc_thm_370272
  have h_k_396 : k ≥ 609 := staircase_step_K_direct k m 51156 219453 370272 19563 31545 609 heq h_m_mono_395 h_pc_M_395 h_pc_K_prev_395 rfl (by decide)
  have h_pc_K_next_395 : Nat.primeCounting 371490 = 31633 := pc_thm_371490
  have h_pc_M_next_val_395 : Nat.primeCounting 219453 = 19563 := pc_thm_219453
  have h_m_396 : m ≤ 661 := staircase_step_M_direct k m 51156 371490 219453 31633 19563 661 heq (k_mono 609 k h_k_396) h_pc_K_next_395 h_pc_M_next_val_395 rfl (by decide)
  -- Step 396: k >= 609, m <= 661 => k >= 610
  have h_m_mono_396 : m*(m+1)/2 ≤ 218791 := m_mono m 661 h_m_396
  have h_pc_M_396 : Nat.primeCounting 218791 = 19508 := pc_thm_218791
  have h_pc_K_prev_396 : Nat.primeCounting 371490 = 31633 := pc_thm_371490
  have h_k_397 : k ≥ 610 := staircase_step_K_direct k m 51156 218791 371490 19508 31633 610 heq h_m_mono_396 h_pc_M_396 h_pc_K_prev_396 rfl (by decide)
  have h_pc_K_next_396 : Nat.primeCounting 372710 = 31723 := pc_thm_372710
  have h_pc_M_next_val_396 : Nat.primeCounting 218130 = 19454 := pc_thm_218130
  have h_m_397 : m ≤ 659 := staircase_step_M_direct k m 51156 372710 218130 31723 19454 659 heq (k_mono 610 k h_k_397) h_pc_K_next_396 h_pc_M_next_val_396 rfl (by decide)
  -- Step 397: k >= 610, m <= 659 => k >= 611
  have h_m_mono_397 : m*(m+1)/2 ≤ 217470 := m_mono m 659 h_m_397
  have h_pc_M_397 : Nat.primeCounting 217470 = 19406 := pc_thm_217470
  have h_pc_K_prev_397 : Nat.primeCounting 372710 = 31723 := pc_thm_372710
  have h_k_398 : k ≥ 611 := staircase_step_K_direct k m 51156 217470 372710 19406 31723 611 heq h_m_mono_397 h_pc_M_397 h_pc_K_prev_397 rfl (by decide)
  have h_pc_K_next_397 : Nat.primeCounting 373932 = 31814 := pc_thm_373932
  have h_pc_M_next_val_397 : Nat.primeCounting 216811 = 19349 := pc_thm_216811
  have h_m_398 : m ≤ 657 := staircase_step_M_direct k m 51156 373932 216811 31814 19349 657 heq (k_mono 611 k h_k_398) h_pc_K_next_397 h_pc_M_next_val_397 rfl (by decide)
  -- Step 398: k >= 611, m <= 657 => k >= 612
  have h_m_mono_398 : m*(m+1)/2 ≤ 216153 := m_mono m 657 h_m_398
  have h_pc_M_398 : Nat.primeCounting 216153 = 19299 := pc_thm_216153
  have h_pc_K_prev_398 : Nat.primeCounting 373932 = 31814 := pc_thm_373932
  have h_k_399 : k ≥ 612 := staircase_step_K_direct k m 51156 216153 373932 19299 31814 612 heq h_m_mono_398 h_pc_M_398 h_pc_K_prev_398 rfl (by decide)
  have h_pc_K_next_398 : Nat.primeCounting 375156 = 31920 := pc_thm_375156
  have h_pc_M_next_val_398 : Nat.primeCounting 215496 = 19249 := pc_thm_215496
  have h_m_399 : m ≤ 655 := staircase_step_M_direct k m 51156 375156 215496 31920 19249 655 heq (k_mono 612 k h_k_399) h_pc_K_next_398 h_pc_M_next_val_398 rfl (by decide)
  -- Step 399: k >= 612, m <= 655 => k >= 613
  have h_m_mono_399 : m*(m+1)/2 ≤ 214840 := m_mono m 655 h_m_399
  have h_pc_M_399 : Nat.primeCounting 214840 = 19202 := pc_thm_214840
  have h_pc_K_prev_399 : Nat.primeCounting 375156 = 31920 := pc_thm_375156
  have h_k_400 : k ≥ 613 := staircase_step_K_direct k m 51156 214840 375156 19202 31920 613 heq h_m_mono_399 h_pc_M_399 h_pc_K_prev_399 rfl (by decide)
  have h_pc_K_next_399 : Nat.primeCounting 376382 = 32015 := pc_thm_376382
  have h_pc_M_next_val_399 : Nat.primeCounting 214185 = 19145 := pc_thm_214185
  have h_m_400 : m ≤ 653 := staircase_step_M_direct k m 51156 376382 214185 32015 19145 653 heq (k_mono 613 k h_k_400) h_pc_K_next_399 h_pc_M_next_val_399 rfl (by decide)
  -- Step 400: k >= 613, m <= 653 => k >= 614
  have h_m_mono_400 : m*(m+1)/2 ≤ 213531 := m_mono m 653 h_m_400
  have h_pc_M_400 : Nat.primeCounting 213531 = 19090 := pc_thm_213531
  have h_pc_K_prev_400 : Nat.primeCounting 376382 = 32015 := pc_thm_376382
  have h_k_401 : k ≥ 614 := staircase_step_K_direct k m 51156 213531 376382 19090 32015 614 heq h_m_mono_400 h_pc_M_400 h_pc_K_prev_400 rfl (by decide)
  have h_pc_K_next_400 : Nat.primeCounting 377610 = 32114 := pc_thm_377610
  have h_pc_M_next_val_400 : Nat.primeCounting 213531 = 19090 := pc_thm_213531
  have h_m_401 : m ≤ 652 := staircase_step_M_direct k m 51156 377610 213531 32114 19090 652 heq (k_mono 614 k h_k_401) h_pc_K_next_400 h_pc_M_next_val_400 rfl (by decide)
  -- Step 401: k >= 614, m <= 652 => k >= 615
  have h_m_mono_401 : m*(m+1)/2 ≤ 212878 := m_mono m 652 h_m_401
  have h_pc_M_401 : Nat.primeCounting 212878 = 19036 := pc_thm_212878
  have h_pc_K_prev_401 : Nat.primeCounting 377610 = 32114 := pc_thm_377610
  have h_k_402 : k ≥ 615 := staircase_step_K_direct k m 51156 212878 377610 19036 32114 615 heq h_m_mono_401 h_pc_M_401 h_pc_K_prev_401 rfl (by decide)
  have h_pc_K_next_401 : Nat.primeCounting 378840 = 32205 := pc_thm_378840
  have h_pc_M_next_val_401 : Nat.primeCounting 212226 = 18992 := pc_thm_212226
  have h_m_402 : m ≤ 650 := staircase_step_M_direct k m 51156 378840 212226 32205 18992 650 heq (k_mono 615 k h_k_402) h_pc_K_next_401 h_pc_M_next_val_401 rfl (by decide)
  -- Step 402: k >= 615, m <= 650 => k >= 616
  have h_m_mono_402 : m*(m+1)/2 ≤ 211575 := m_mono m 650 h_m_402
  have h_pc_M_402 : Nat.primeCounting 211575 = 18940 := pc_thm_211575
  have h_pc_K_prev_402 : Nat.primeCounting 378840 = 32205 := pc_thm_378840
  have h_k_403 : k ≥ 616 := staircase_step_K_direct k m 51156 211575 378840 18940 32205 616 heq h_m_mono_402 h_pc_M_402 h_pc_K_prev_402 rfl (by decide)
  have h_pc_K_next_402 : Nat.primeCounting 380072 = 32304 := pc_thm_380072
  have h_pc_M_next_val_402 : Nat.primeCounting 210925 = 18887 := pc_thm_210925
  have h_m_403 : m ≤ 648 := staircase_step_M_direct k m 51156 380072 210925 32304 18887 648 heq (k_mono 616 k h_k_403) h_pc_K_next_402 h_pc_M_next_val_402 rfl (by decide)
  -- Step 403: k >= 616, m <= 648 => k >= 617
  have h_m_mono_403 : m*(m+1)/2 ≤ 210276 := m_mono m 648 h_m_403
  have h_pc_M_403 : Nat.primeCounting 210276 = 18834 := pc_thm_210276
  have h_pc_K_prev_403 : Nat.primeCounting 380072 = 32304 := pc_thm_380072
  have h_k_404 : k ≥ 617 := staircase_step_K_direct k m 51156 210276 380072 18834 32304 617 heq h_m_mono_403 h_pc_M_403 h_pc_K_prev_403 rfl (by decide)
  have h_pc_K_next_403 : Nat.primeCounting 381306 = 32394 := pc_thm_381306
  have h_pc_M_next_val_403 : Nat.primeCounting 209628 = 18774 := pc_thm_209628
  have h_m_404 : m ≤ 646 := staircase_step_M_direct k m 51156 381306 209628 32394 18774 646 heq (k_mono 617 k h_k_404) h_pc_K_next_403 h_pc_M_next_val_403 rfl (by decide)
  -- Step 404: k >= 617, m <= 646 => k >= 618
  have h_m_mono_404 : m*(m+1)/2 ≤ 208981 := m_mono m 646 h_m_404
  have h_pc_M_404 : Nat.primeCounting 208981 = 18716 := pc_thm_208981
  have h_pc_K_prev_404 : Nat.primeCounting 381306 = 32394 := pc_thm_381306
  have h_k_405 : k ≥ 618 := staircase_step_K_direct k m 51156 208981 381306 18716 32394 618 heq h_m_mono_404 h_pc_M_404 h_pc_K_prev_404 rfl (by decide)
  have h_pc_K_next_404 : Nat.primeCounting 382542 = 32483 := pc_thm_382542
  have h_pc_M_next_val_404 : Nat.primeCounting 208981 = 18716 := pc_thm_208981
  have h_m_405 : m ≤ 645 := staircase_step_M_direct k m 51156 382542 208981 32483 18716 645 heq (k_mono 618 k h_k_405) h_pc_K_next_404 h_pc_M_next_val_404 rfl (by decide)
  -- Step 405: k >= 618, m <= 645 => k >= 619
  have h_m_mono_405 : m*(m+1)/2 ≤ 208335 := m_mono m 645 h_m_405
  have h_pc_M_405 : Nat.primeCounting 208335 = 18664 := pc_thm_208335
  have h_pc_K_prev_405 : Nat.primeCounting 382542 = 32483 := pc_thm_382542
  have h_k_406 : k ≥ 619 := staircase_step_K_direct k m 51156 208335 382542 18664 32483 619 heq h_m_mono_405 h_pc_M_405 h_pc_K_prev_405 rfl (by decide)
  have h_pc_K_next_405 : Nat.primeCounting 383780 = 32584 := pc_thm_383780
  have h_pc_M_next_val_405 : Nat.primeCounting 207690 = 18611 := pc_thm_207690
  have h_m_406 : m ≤ 643 := staircase_step_M_direct k m 51156 383780 207690 32584 18611 643 heq (k_mono 619 k h_k_406) h_pc_K_next_405 h_pc_M_next_val_405 rfl (by decide)
  exact ⟨h_k_406, h_m_406⟩

theorem staircase_part_27 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_406 : k ≥ 619) (h_m_406 : m ≤ 643) : k ≥ 634 ∧ m ≤ 614 := by
  -- Step 406: k >= 619, m <= 643 => k >= 620
  have h_m_mono_406 : m*(m+1)/2 ≤ 207046 := m_mono m 643 h_m_406
  have h_pc_M_406 : Nat.primeCounting 207046 = 18552 := pc_thm_207046
  have h_pc_K_prev_406 : Nat.primeCounting 383780 = 32584 := pc_thm_383780
  have h_k_407 : k ≥ 620 := staircase_step_K_direct k m 51156 207046 383780 18552 32584 620 heq h_m_mono_406 h_pc_M_406 h_pc_K_prev_406 rfl (by decide)
  have h_pc_K_next_406 : Nat.primeCounting 385020 = 32683 := pc_thm_385020
  have h_pc_M_next_val_406 : Nat.primeCounting 206403 = 18502 := pc_thm_206403
  have h_m_407 : m ≤ 641 := staircase_step_M_direct k m 51156 385020 206403 32683 18502 641 heq (k_mono 620 k h_k_407) h_pc_K_next_406 h_pc_M_next_val_406 rfl (by decide)
  -- Step 407: k >= 620, m <= 641 => k >= 621
  have h_m_mono_407 : m*(m+1)/2 ≤ 205761 := m_mono m 641 h_m_407
  have h_pc_M_407 : Nat.primeCounting 205761 = 18446 := pc_thm_205761
  have h_pc_K_prev_407 : Nat.primeCounting 385020 = 32683 := pc_thm_385020
  have h_k_408 : k ≥ 621 := staircase_step_K_direct k m 51156 205761 385020 18446 32683 621 heq h_m_mono_407 h_pc_M_407 h_pc_K_prev_407 rfl (by decide)
  have h_pc_K_next_407 : Nat.primeCounting 386262 = 32783 := pc_thm_386262
  have h_pc_M_next_val_407 : Nat.primeCounting 205120 = 18391 := pc_thm_205120
  have h_m_408 : m ≤ 639 := staircase_step_M_direct k m 51156 386262 205120 32783 18391 639 heq (k_mono 621 k h_k_408) h_pc_K_next_407 h_pc_M_next_val_407 rfl (by decide)
  -- Step 408: k >= 621, m <= 639 => k >= 622
  have h_m_mono_408 : m*(m+1)/2 ≤ 204480 := m_mono m 639 h_m_408
  have h_pc_M_408 : Nat.primeCounting 204480 = 18341 := pc_thm_204480
  have h_pc_K_prev_408 : Nat.primeCounting 386262 = 32783 := pc_thm_386262
  have h_k_409 : k ≥ 622 := staircase_step_K_direct k m 51156 204480 386262 18341 32783 622 heq h_m_mono_408 h_pc_M_408 h_pc_K_prev_408 rfl (by decide)
  have h_pc_K_next_408 : Nat.primeCounting 387506 = 32875 := pc_thm_387506
  have h_pc_M_next_val_408 : Nat.primeCounting 203841 = 18289 := pc_thm_203841
  have h_m_409 : m ≤ 637 := staircase_step_M_direct k m 51156 387506 203841 32875 18289 637 heq (k_mono 622 k h_k_409) h_pc_K_next_408 h_pc_M_next_val_408 rfl (by decide)
  -- Step 409: k >= 622, m <= 637 => k >= 623
  have h_m_mono_409 : m*(m+1)/2 ≤ 203203 := m_mono m 637 h_m_409
  have h_pc_M_409 : Nat.primeCounting 203203 = 18236 := pc_thm_203203
  have h_pc_K_prev_409 : Nat.primeCounting 387506 = 32875 := pc_thm_387506
  have h_k_410 : k ≥ 623 := staircase_step_K_direct k m 51156 203203 387506 18236 32875 623 heq h_m_mono_409 h_pc_M_409 h_pc_K_prev_409 rfl (by decide)
  have h_pc_K_next_409 : Nat.primeCounting 388752 = 32963 := pc_thm_388752
  have h_pc_M_next_val_409 : Nat.primeCounting 203203 = 18236 := pc_thm_203203
  have h_m_410 : m ≤ 636 := staircase_step_M_direct k m 51156 388752 203203 32963 18236 636 heq (k_mono 623 k h_k_410) h_pc_K_next_409 h_pc_M_next_val_409 rfl (by decide)
  -- Step 410: k >= 623, m <= 636 => k >= 624
  have h_m_mono_410 : m*(m+1)/2 ≤ 202566 := m_mono m 636 h_m_410
  have h_pc_M_410 : Nat.primeCounting 202566 = 18188 := pc_thm_202566
  have h_pc_K_prev_410 : Nat.primeCounting 388752 = 32963 := pc_thm_388752
  have h_k_411 : k ≥ 624 := staircase_step_K_direct k m 51156 202566 388752 18188 32963 624 heq h_m_mono_410 h_pc_M_410 h_pc_K_prev_410 rfl (by decide)
  have h_pc_K_next_410 : Nat.primeCounting 390000 = 33067 := pc_thm_390000
  have h_pc_M_next_val_410 : Nat.primeCounting 201930 = 18141 := pc_thm_201930
  have h_m_411 : m ≤ 634 := staircase_step_M_direct k m 51156 390000 201930 33067 18141 634 heq (k_mono 624 k h_k_411) h_pc_K_next_410 h_pc_M_next_val_410 rfl (by decide)
  -- Step 411: k >= 624, m <= 634 => k >= 625
  have h_m_mono_411 : m*(m+1)/2 ≤ 201295 := m_mono m 634 h_m_411
  have h_pc_M_411 : Nat.primeCounting 201295 = 18084 := pc_thm_201295
  have h_pc_K_prev_411 : Nat.primeCounting 390000 = 33067 := pc_thm_390000
  have h_k_412 : k ≥ 625 := staircase_step_K_direct k m 51156 201295 390000 18084 33067 625 heq h_m_mono_411 h_pc_M_411 h_pc_K_prev_411 rfl (by decide)
  have h_pc_K_next_411 : Nat.primeCounting 391250 = 33170 := pc_thm_391250
  have h_pc_M_next_val_411 : Nat.primeCounting 200028 = 17988 := pc_thm_200028
  have h_m_412 : m ≤ 631 := staircase_step_M_direct k m 51156 391250 200028 33170 17988 631 heq (k_mono 625 k h_k_412) h_pc_K_next_411 h_pc_M_next_val_411 rfl (by decide)
  -- Step 412: k >= 625, m <= 631 => k >= 626
  have h_m_mono_412 : m*(m+1)/2 ≤ 199396 := m_mono m 631 h_m_412
  have h_pc_M_412 : Nat.primeCounting 199396 = 17932 := pc_thm_199396
  have h_pc_K_prev_412 : Nat.primeCounting 391250 = 33170 := pc_thm_391250
  have h_k_413 : k ≥ 626 := staircase_step_K_direct k m 51156 199396 391250 17932 33170 626 heq h_m_mono_412 h_pc_M_412 h_pc_K_prev_412 rfl (by decide)
  have h_pc_K_next_412 : Nat.primeCounting 392502 = 33273 := pc_thm_392502
  have h_pc_M_next_val_412 : Nat.primeCounting 198765 = 17884 := pc_thm_198765
  have h_m_413 : m ≤ 629 := staircase_step_M_direct k m 51156 392502 198765 33273 17884 629 heq (k_mono 626 k h_k_413) h_pc_K_next_412 h_pc_M_next_val_412 rfl (by decide)
  -- Step 413: k >= 626, m <= 629 => k >= 627
  have h_m_mono_413 : m*(m+1)/2 ≤ 198135 := m_mono m 629 h_m_413
  have h_pc_M_413 : Nat.primeCounting 198135 = 17832 := pc_thm_198135
  have h_pc_K_prev_413 : Nat.primeCounting 392502 = 33273 := pc_thm_392502
  have h_k_414 : k ≥ 627 := staircase_step_K_direct k m 51156 198135 392502 17832 33273 627 heq h_m_mono_413 h_pc_M_413 h_pc_K_prev_413 rfl (by decide)
  have h_pc_K_next_413 : Nat.primeCounting 393756 = 33382 := pc_thm_393756
  have h_pc_M_next_val_413 : Nat.primeCounting 197506 = 17778 := pc_thm_197506
  have h_m_414 : m ≤ 627 := staircase_step_M_direct k m 51156 393756 197506 33382 17778 627 heq (k_mono 627 k h_k_414) h_pc_K_next_413 h_pc_M_next_val_413 rfl (by decide)
  -- Step 414: k >= 627, m <= 627 => k >= 628
  have h_m_mono_414 : m*(m+1)/2 ≤ 196878 := m_mono m 627 h_m_414
  have h_pc_M_414 : Nat.primeCounting 196878 = 17726 := pc_thm_196878
  have h_pc_K_prev_414 : Nat.primeCounting 393756 = 33382 := pc_thm_393756
  have h_k_415 : k ≥ 628 := staircase_step_K_direct k m 51156 196878 393756 17726 33382 628 heq h_m_mono_414 h_pc_M_414 h_pc_K_prev_414 rfl (by decide)
  have h_pc_K_next_414 : Nat.primeCounting 395012 = 33475 := pc_thm_395012
  have h_pc_M_next_val_414 : Nat.primeCounting 196878 = 17726 := pc_thm_196878
  have h_m_415 : m ≤ 626 := staircase_step_M_direct k m 51156 395012 196878 33475 17726 626 heq (k_mono 628 k h_k_415) h_pc_K_next_414 h_pc_M_next_val_414 rfl (by decide)
  -- Step 415: k >= 628, m <= 626 => k >= 629
  have h_m_mono_415 : m*(m+1)/2 ≤ 196251 := m_mono m 626 h_m_415
  have h_pc_M_415 : Nat.primeCounting 196251 = 17678 := pc_thm_196251
  have h_pc_K_prev_415 : Nat.primeCounting 395012 = 33475 := pc_thm_395012
  have h_k_416 : k ≥ 629 := staircase_step_K_direct k m 51156 196251 395012 17678 33475 629 heq h_m_mono_415 h_pc_M_415 h_pc_K_prev_415 rfl (by decide)
  have h_pc_K_next_415 : Nat.primeCounting 396270 = 33569 := pc_thm_396270
  have h_pc_M_next_val_415 : Nat.primeCounting 195625 = 17625 := pc_thm_195625
  have h_m_416 : m ≤ 624 := staircase_step_M_direct k m 51156 396270 195625 33569 17625 624 heq (k_mono 629 k h_k_416) h_pc_K_next_415 h_pc_M_next_val_415 rfl (by decide)
  -- Step 416: k >= 629, m <= 624 => k >= 630
  have h_m_mono_416 : m*(m+1)/2 ≤ 195000 := m_mono m 624 h_m_416
  have h_pc_M_416 : Nat.primeCounting 195000 = 17573 := pc_thm_195000
  have h_pc_K_prev_416 : Nat.primeCounting 396270 = 33569 := pc_thm_396270
  have h_k_417 : k ≥ 630 := staircase_step_K_direct k m 51156 195000 396270 17573 33569 630 heq h_m_mono_416 h_pc_M_416 h_pc_K_prev_416 rfl (by decide)
  have h_pc_K_next_416 : Nat.primeCounting 397530 = 33662 := pc_thm_397530
  have h_pc_M_next_val_416 : Nat.primeCounting 194376 = 17525 := pc_thm_194376
  have h_m_417 : m ≤ 622 := staircase_step_M_direct k m 51156 397530 194376 33662 17525 622 heq (k_mono 630 k h_k_417) h_pc_K_next_416 h_pc_M_next_val_416 rfl (by decide)
  -- Step 417: k >= 630, m <= 622 => k >= 631
  have h_m_mono_417 : m*(m+1)/2 ≤ 193753 := m_mono m 622 h_m_417
  have h_pc_M_417 : Nat.primeCounting 193753 = 17475 := pc_thm_193753
  have h_pc_K_prev_417 : Nat.primeCounting 397530 = 33662 := pc_thm_397530
  have h_k_418 : k ≥ 631 := staircase_step_K_direct k m 51156 193753 397530 17475 33662 631 heq h_m_mono_417 h_pc_M_417 h_pc_K_prev_417 rfl (by decide)
  have h_pc_K_next_417 : Nat.primeCounting 398792 = 33764 := pc_thm_398792
  have h_pc_M_next_val_417 : Nat.primeCounting 193131 = 17424 := pc_thm_193131
  have h_m_418 : m ≤ 620 := staircase_step_M_direct k m 51156 398792 193131 33764 17424 620 heq (k_mono 631 k h_k_418) h_pc_K_next_417 h_pc_M_next_val_417 rfl (by decide)
  -- Step 418: k >= 631, m <= 620 => k >= 632
  have h_m_mono_418 : m*(m+1)/2 ≤ 192510 := m_mono m 620 h_m_418
  have h_pc_M_418 : Nat.primeCounting 192510 = 17369 := pc_thm_192510
  have h_pc_K_prev_418 : Nat.primeCounting 398792 = 33764 := pc_thm_398792
  have h_k_419 : k ≥ 632 := staircase_step_K_direct k m 51156 192510 398792 17369 33764 632 heq h_m_mono_418 h_pc_M_418 h_pc_K_prev_418 rfl (by decide)
  have h_pc_K_next_418 : Nat.primeCounting 400056 = 33864 := pc_thm_400056
  have h_pc_M_next_val_418 : Nat.primeCounting 191890 = 17318 := pc_thm_191890
  have h_m_419 : m ≤ 618 := staircase_step_M_direct k m 51156 400056 191890 33864 17318 618 heq (k_mono 632 k h_k_419) h_pc_K_next_418 h_pc_M_next_val_418 rfl (by decide)
  -- Step 419: k >= 632, m <= 618 => k >= 633
  have h_m_mono_419 : m*(m+1)/2 ≤ 191271 := m_mono m 618 h_m_419
  have h_pc_M_419 : Nat.primeCounting 191271 = 17267 := pc_thm_191271
  have h_pc_K_prev_419 : Nat.primeCounting 400056 = 33864 := pc_thm_400056
  have h_k_420 : k ≥ 633 := staircase_step_K_direct k m 51156 191271 400056 17267 33864 633 heq h_m_mono_419 h_pc_M_419 h_pc_K_prev_419 rfl (by decide)
  have h_pc_K_next_419 : Nat.primeCounting 401322 = 33954 := pc_thm_401322
  have h_pc_M_next_val_419 : Nat.primeCounting 190653 = 17216 := pc_thm_190653
  have h_m_420 : m ≤ 616 := staircase_step_M_direct k m 51156 401322 190653 33954 17216 616 heq (k_mono 633 k h_k_420) h_pc_K_next_419 h_pc_M_next_val_419 rfl (by decide)
  -- Step 420: k >= 633, m <= 616 => k >= 634
  have h_m_mono_420 : m*(m+1)/2 ≤ 190036 := m_mono m 616 h_m_420
  have h_pc_M_420 : Nat.primeCounting 190036 = 17172 := pc_thm_190036
  have h_pc_K_prev_420 : Nat.primeCounting 401322 = 33954 := pc_thm_401322
  have h_k_421 : k ≥ 634 := staircase_step_K_direct k m 51156 190036 401322 17172 33954 634 heq h_m_mono_420 h_pc_M_420 h_pc_K_prev_420 rfl (by decide)
  have h_pc_K_next_420 : Nat.primeCounting 402590 = 34049 := pc_thm_402590
  have h_pc_M_next_val_420 : Nat.primeCounting 189420 = 17115 := pc_thm_189420
  have h_m_421 : m ≤ 614 := staircase_step_M_direct k m 51156 402590 189420 34049 17115 614 heq (k_mono 634 k h_k_421) h_pc_K_next_420 h_pc_M_next_val_420 rfl (by decide)
  exact ⟨h_k_421, h_m_421⟩

theorem staircase_part_28 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_421 : k ≥ 634) (h_m_421 : m ≤ 614) : k ≥ 649 ∧ m ≤ 585 := by
  -- Step 421: k >= 634, m <= 614 => k >= 635
  have h_m_mono_421 : m*(m+1)/2 ≤ 188805 := m_mono m 614 h_m_421
  have h_pc_M_421 : Nat.primeCounting 188805 = 17064 := pc_thm_188805
  have h_pc_K_prev_421 : Nat.primeCounting 402590 = 34049 := pc_thm_402590
  have h_k_422 : k ≥ 635 := staircase_step_K_direct k m 51156 188805 402590 17064 34049 635 heq h_m_mono_421 h_pc_M_421 h_pc_K_prev_421 rfl (by decide)
  have h_pc_K_next_421 : Nat.primeCounting 403860 = 34140 := pc_thm_403860
  have h_pc_M_next_val_421 : Nat.primeCounting 188805 = 17064 := pc_thm_188805
  have h_m_422 : m ≤ 613 := staircase_step_M_direct k m 51156 403860 188805 34140 17064 613 heq (k_mono 635 k h_k_422) h_pc_K_next_421 h_pc_M_next_val_421 rfl (by decide)
  -- Step 422: k >= 635, m <= 613 => k >= 636
  have h_m_mono_422 : m*(m+1)/2 ≤ 188191 := m_mono m 613 h_m_422
  have h_pc_M_422 : Nat.primeCounting 188191 = 17014 := pc_thm_188191
  have h_pc_K_prev_422 : Nat.primeCounting 403860 = 34140 := pc_thm_403860
  have h_k_423 : k ≥ 636 := staircase_step_K_direct k m 51156 188191 403860 17014 34140 636 heq h_m_mono_422 h_pc_M_422 h_pc_K_prev_422 rfl (by decide)
  have h_pc_K_next_422 : Nat.primeCounting 405132 = 34232 := pc_thm_405132
  have h_pc_M_next_val_422 : Nat.primeCounting 187578 = 16970 := pc_thm_187578
  have h_m_423 : m ≤ 611 := staircase_step_M_direct k m 51156 405132 187578 34232 16970 611 heq (k_mono 636 k h_k_423) h_pc_K_next_422 h_pc_M_next_val_422 rfl (by decide)
  -- Step 423: k >= 636, m <= 611 => k >= 637
  have h_m_mono_423 : m*(m+1)/2 ≤ 186966 := m_mono m 611 h_m_423
  have h_pc_M_423 : Nat.primeCounting 186966 = 16915 := pc_thm_186966
  have h_pc_K_prev_423 : Nat.primeCounting 405132 = 34232 := pc_thm_405132
  have h_k_424 : k ≥ 637 := staircase_step_K_direct k m 51156 186966 405132 16915 34232 637 heq h_m_mono_423 h_pc_M_423 h_pc_K_prev_423 rfl (by decide)
  have h_pc_K_next_423 : Nat.primeCounting 406406 = 34332 := pc_thm_406406
  have h_pc_M_next_val_423 : Nat.primeCounting 186355 = 16869 := pc_thm_186355
  have h_m_424 : m ≤ 609 := staircase_step_M_direct k m 51156 406406 186355 34332 16869 609 heq (k_mono 637 k h_k_424) h_pc_K_next_423 h_pc_M_next_val_423 rfl (by decide)
  -- Step 424: k >= 637, m <= 609 => k >= 638
  have h_m_mono_424 : m*(m+1)/2 ≤ 185745 := m_mono m 609 h_m_424
  have h_pc_M_424 : Nat.primeCounting 185745 = 16810 := pc_thm_185745
  have h_pc_K_prev_424 : Nat.primeCounting 406406 = 34332 := pc_thm_406406
  have h_k_425 : k ≥ 638 := staircase_step_K_direct k m 51156 185745 406406 16810 34332 638 heq h_m_mono_424 h_pc_M_424 h_pc_K_prev_424 rfl (by decide)
  have h_pc_K_next_424 : Nat.primeCounting 407682 = 34425 := pc_thm_407682
  have h_pc_M_next_val_424 : Nat.primeCounting 185136 = 16757 := pc_thm_185136
  have h_m_425 : m ≤ 607 := staircase_step_M_direct k m 51156 407682 185136 34425 16757 607 heq (k_mono 638 k h_k_425) h_pc_K_next_424 h_pc_M_next_val_424 rfl (by decide)
  -- Step 425: k >= 638, m <= 607 => k >= 639
  have h_m_mono_425 : m*(m+1)/2 ≤ 184528 := m_mono m 607 h_m_425
  have h_pc_M_425 : Nat.primeCounting 184528 = 16706 := pc_thm_184528
  have h_pc_K_prev_425 : Nat.primeCounting 407682 = 34425 := pc_thm_407682
  have h_k_426 : k ≥ 639 := staircase_step_K_direct k m 51156 184528 407682 16706 34425 639 heq h_m_mono_425 h_pc_M_425 h_pc_K_prev_425 rfl (by decide)
  have h_pc_K_next_425 : Nat.primeCounting 408960 = 34529 := pc_thm_408960
  have h_pc_M_next_val_425 : Nat.primeCounting 183921 = 16656 := pc_thm_183921
  have h_m_426 : m ≤ 605 := staircase_step_M_direct k m 51156 408960 183921 34529 16656 605 heq (k_mono 639 k h_k_426) h_pc_K_next_425 h_pc_M_next_val_425 rfl (by decide)
  -- Step 426: k >= 639, m <= 605 => k >= 640
  have h_m_mono_426 : m*(m+1)/2 ≤ 183315 := m_mono m 605 h_m_426
  have h_pc_M_426 : Nat.primeCounting 183315 = 16604 := pc_thm_183315
  have h_pc_K_prev_426 : Nat.primeCounting 408960 = 34529 := pc_thm_408960
  have h_k_427 : k ≥ 640 := staircase_step_K_direct k m 51156 183315 408960 16604 34529 640 heq h_m_mono_426 h_pc_M_426 h_pc_K_prev_426 rfl (by decide)
  have h_pc_K_next_426 : Nat.primeCounting 410240 = 34630 := pc_thm_410240
  have h_pc_M_next_val_426 : Nat.primeCounting 182710 = 16558 := pc_thm_182710
  have h_m_427 : m ≤ 603 := staircase_step_M_direct k m 51156 410240 182710 34630 16558 603 heq (k_mono 640 k h_k_427) h_pc_K_next_426 h_pc_M_next_val_426 rfl (by decide)
  -- Step 427: k >= 640, m <= 603 => k >= 641
  have h_m_mono_427 : m*(m+1)/2 ≤ 182106 := m_mono m 603 h_m_427
  have h_pc_M_427 : Nat.primeCounting 182106 = 16503 := pc_thm_182106
  have h_pc_K_prev_427 : Nat.primeCounting 410240 = 34630 := pc_thm_410240
  have h_k_428 : k ≥ 641 := staircase_step_K_direct k m 51156 182106 410240 16503 34630 641 heq h_m_mono_427 h_pc_M_427 h_pc_K_prev_427 rfl (by decide)
  have h_pc_K_next_427 : Nat.primeCounting 411522 = 34728 := pc_thm_411522
  have h_pc_M_next_val_427 : Nat.primeCounting 181503 = 16451 := pc_thm_181503
  have h_m_428 : m ≤ 601 := staircase_step_M_direct k m 51156 411522 181503 34728 16451 601 heq (k_mono 641 k h_k_428) h_pc_K_next_427 h_pc_M_next_val_427 rfl (by decide)
  -- Step 428: k >= 641, m <= 601 => k >= 642
  have h_m_mono_428 : m*(m+1)/2 ≤ 180901 := m_mono m 601 h_m_428
  have h_pc_M_428 : Nat.primeCounting 180901 = 16410 := pc_thm_180901
  have h_pc_K_prev_428 : Nat.primeCounting 411522 = 34728 := pc_thm_411522
  have h_k_429 : k ≥ 642 := staircase_step_K_direct k m 51156 180901 411522 16410 34728 642 heq h_m_mono_428 h_pc_M_428 h_pc_K_prev_428 rfl (by decide)
  have h_pc_K_next_428 : Nat.primeCounting 412806 = 34830 := pc_thm_412806
  have h_pc_M_next_val_428 : Nat.primeCounting 180300 = 16366 := pc_thm_180300
  have h_m_429 : m ≤ 599 := staircase_step_M_direct k m 51156 412806 180300 34830 16366 599 heq (k_mono 642 k h_k_429) h_pc_K_next_428 h_pc_M_next_val_428 rfl (by decide)
  -- Step 429: k >= 642, m <= 599 => k >= 643
  have h_m_mono_429 : m*(m+1)/2 ≤ 179700 := m_mono m 599 h_m_429
  have h_pc_M_429 : Nat.primeCounting 179700 = 16313 := pc_thm_179700
  have h_pc_K_prev_429 : Nat.primeCounting 412806 = 34830 := pc_thm_412806
  have h_k_430 : k ≥ 643 := staircase_step_K_direct k m 51156 179700 412806 16313 34830 643 heq h_m_mono_429 h_pc_M_429 h_pc_K_prev_429 rfl (by decide)
  have h_pc_K_next_429 : Nat.primeCounting 414092 = 34920 := pc_thm_414092
  have h_pc_M_next_val_429 : Nat.primeCounting 179101 = 16257 := pc_thm_179101
  have h_m_430 : m ≤ 597 := staircase_step_M_direct k m 51156 414092 179101 34920 16257 597 heq (k_mono 643 k h_k_430) h_pc_K_next_429 h_pc_M_next_val_429 rfl (by decide)
  -- Step 430: k >= 643, m <= 597 => k >= 644
  have h_m_mono_430 : m*(m+1)/2 ≤ 178503 := m_mono m 597 h_m_430
  have h_pc_M_430 : Nat.primeCounting 178503 = 16202 := pc_thm_178503
  have h_pc_K_prev_430 : Nat.primeCounting 414092 = 34920 := pc_thm_414092
  have h_k_431 : k ≥ 644 := staircase_step_K_direct k m 51156 178503 414092 16202 34920 644 heq h_m_mono_430 h_pc_M_430 h_pc_K_prev_430 rfl (by decide)
  have h_pc_K_next_430 : Nat.primeCounting 415380 = 35028 := pc_thm_415380
  have h_pc_M_next_val_430 : Nat.primeCounting 177906 = 16150 := pc_thm_177906
  have h_m_431 : m ≤ 595 := staircase_step_M_direct k m 51156 415380 177906 35028 16150 595 heq (k_mono 644 k h_k_431) h_pc_K_next_430 h_pc_M_next_val_430 rfl (by decide)
  -- Step 431: k >= 644, m <= 595 => k >= 645
  have h_m_mono_431 : m*(m+1)/2 ≤ 177310 := m_mono m 595 h_m_431
  have h_pc_M_431 : Nat.primeCounting 177310 = 16108 := pc_thm_177310
  have h_pc_K_prev_431 : Nat.primeCounting 415380 = 35028 := pc_thm_415380
  have h_k_432 : k ≥ 645 := staircase_step_K_direct k m 51156 177310 415380 16108 35028 645 heq h_m_mono_431 h_pc_M_431 h_pc_K_prev_431 rfl (by decide)
  have h_pc_K_next_431 : Nat.primeCounting 416670 = 35131 := pc_thm_416670
  have h_pc_M_next_val_431 : Nat.primeCounting 176715 = 16062 := pc_thm_176715
  have h_m_432 : m ≤ 593 := staircase_step_M_direct k m 51156 416670 176715 35131 16062 593 heq (k_mono 645 k h_k_432) h_pc_K_next_431 h_pc_M_next_val_431 rfl (by decide)
  -- Step 432: k >= 645, m <= 593 => k >= 646
  have h_m_mono_432 : m*(m+1)/2 ≤ 176121 := m_mono m 593 h_m_432
  have h_pc_M_432 : Nat.primeCounting 176121 = 16002 := pc_thm_176121
  have h_pc_K_prev_432 : Nat.primeCounting 416670 = 35131 := pc_thm_416670
  have h_k_433 : k ≥ 646 := staircase_step_K_direct k m 51156 176121 416670 16002 35131 646 heq h_m_mono_432 h_pc_M_432 h_pc_K_prev_432 rfl (by decide)
  have h_pc_K_next_432 : Nat.primeCounting 417962 = 35228 := pc_thm_417962
  have h_pc_M_next_val_432 : Nat.primeCounting 175528 = 15952 := pc_thm_175528
  have h_m_433 : m ≤ 591 := staircase_step_M_direct k m 51156 417962 175528 35228 15952 591 heq (k_mono 646 k h_k_433) h_pc_K_next_432 h_pc_M_next_val_432 rfl (by decide)
  -- Step 433: k >= 646, m <= 591 => k >= 647
  have h_m_mono_433 : m*(m+1)/2 ≤ 174936 := m_mono m 591 h_m_433
  have h_pc_M_433 : Nat.primeCounting 174936 = 15912 := pc_thm_174936
  have h_pc_K_prev_433 : Nat.primeCounting 417962 = 35228 := pc_thm_417962
  have h_k_434 : k ≥ 647 := staircase_step_K_direct k m 51156 174936 417962 15912 35228 647 heq h_m_mono_433 h_pc_M_433 h_pc_K_prev_433 rfl (by decide)
  have h_pc_K_next_433 : Nat.primeCounting 419256 = 35331 := pc_thm_419256
  have h_pc_M_next_val_433 : Nat.primeCounting 174345 = 15864 := pc_thm_174345
  have h_m_434 : m ≤ 589 := staircase_step_M_direct k m 51156 419256 174345 35331 15864 589 heq (k_mono 647 k h_k_434) h_pc_K_next_433 h_pc_M_next_val_433 rfl (by decide)
  -- Step 434: k >= 647, m <= 589 => k >= 648
  have h_m_mono_434 : m*(m+1)/2 ≤ 173755 := m_mono m 589 h_m_434
  have h_pc_M_434 : Nat.primeCounting 173755 = 15812 := pc_thm_173755
  have h_pc_K_prev_434 : Nat.primeCounting 419256 = 35331 := pc_thm_419256
  have h_k_435 : k ≥ 648 := staircase_step_K_direct k m 51156 173755 419256 15812 35331 648 heq h_m_mono_434 h_pc_M_434 h_pc_K_prev_434 rfl (by decide)
  have h_pc_K_next_434 : Nat.primeCounting 420552 = 35433 := pc_thm_420552
  have h_pc_M_next_val_434 : Nat.primeCounting 173166 = 15765 := pc_thm_173166
  have h_m_435 : m ≤ 587 := staircase_step_M_direct k m 51156 420552 173166 35433 15765 587 heq (k_mono 648 k h_k_435) h_pc_K_next_434 h_pc_M_next_val_434 rfl (by decide)
  -- Step 435: k >= 648, m <= 587 => k >= 649
  have h_m_mono_435 : m*(m+1)/2 ≤ 172578 := m_mono m 587 h_m_435
  have h_pc_M_435 : Nat.primeCounting 172578 = 15716 := pc_thm_172578
  have h_pc_K_prev_435 : Nat.primeCounting 420552 = 35433 := pc_thm_420552
  have h_k_436 : k ≥ 649 := staircase_step_K_direct k m 51156 172578 420552 15716 35433 649 heq h_m_mono_435 h_pc_M_435 h_pc_K_prev_435 rfl (by decide)
  have h_pc_K_next_435 : Nat.primeCounting 421850 = 35531 := pc_thm_421850
  have h_pc_M_next_val_435 : Nat.primeCounting 171991 = 15665 := pc_thm_171991
  have h_m_436 : m ≤ 585 := staircase_step_M_direct k m 51156 421850 171991 35531 15665 585 heq (k_mono 649 k h_k_436) h_pc_K_next_435 h_pc_M_next_val_435 rfl (by decide)
  exact ⟨h_k_436, h_m_436⟩

theorem staircase_part_29 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_436 : k ≥ 649) (h_m_436 : m ≤ 585) : k ≥ 664 ∧ m ≤ 552 := by
  -- Step 436: k >= 649, m <= 585 => k >= 650
  have h_m_mono_436 : m*(m+1)/2 ≤ 171405 := m_mono m 585 h_m_436
  have h_pc_M_436 : Nat.primeCounting 171405 = 15615 := pc_thm_171405
  have h_pc_K_prev_436 : Nat.primeCounting 421850 = 35531 := pc_thm_421850
  have h_k_437 : k ≥ 650 := staircase_step_K_direct k m 51156 171405 421850 15615 35531 650 heq h_m_mono_436 h_pc_M_436 h_pc_K_prev_436 rfl (by decide)
  have h_pc_K_next_436 : Nat.primeCounting 423150 = 35630 := pc_thm_423150
  have h_pc_M_next_val_436 : Nat.primeCounting 170820 = 15570 := pc_thm_170820
  have h_m_437 : m ≤ 583 := staircase_step_M_direct k m 51156 423150 170820 35630 15570 583 heq (k_mono 650 k h_k_437) h_pc_K_next_436 h_pc_M_next_val_436 rfl (by decide)
  -- Step 437: k >= 650, m <= 583 => k >= 651
  have h_m_mono_437 : m*(m+1)/2 ≤ 170236 := m_mono m 583 h_m_437
  have h_pc_M_437 : Nat.primeCounting 170236 = 15517 := pc_thm_170236
  have h_pc_K_prev_437 : Nat.primeCounting 423150 = 35630 := pc_thm_423150
  have h_k_438 : k ≥ 651 := staircase_step_K_direct k m 51156 170236 423150 15517 35630 651 heq h_m_mono_437 h_pc_M_437 h_pc_K_prev_437 rfl (by decide)
  have h_pc_K_next_437 : Nat.primeCounting 424452 = 35736 := pc_thm_424452
  have h_pc_M_next_val_437 : Nat.primeCounting 169653 = 15465 := pc_thm_169653
  have h_m_438 : m ≤ 581 := staircase_step_M_direct k m 51156 424452 169653 35736 15465 581 heq (k_mono 651 k h_k_438) h_pc_K_next_437 h_pc_M_next_val_437 rfl (by decide)
  -- Step 438: k >= 651, m <= 581 => k >= 652
  have h_m_mono_438 : m*(m+1)/2 ≤ 169071 := m_mono m 581 h_m_438
  have h_pc_M_438 : Nat.primeCounting 169071 = 15418 := pc_thm_169071
  have h_pc_K_prev_438 : Nat.primeCounting 424452 = 35736 := pc_thm_424452
  have h_k_439 : k ≥ 652 := staircase_step_K_direct k m 51156 169071 424452 15418 35736 652 heq h_m_mono_438 h_pc_M_438 h_pc_K_prev_438 rfl (by decide)
  have h_pc_K_next_438 : Nat.primeCounting 425756 = 35832 := pc_thm_425756
  have h_pc_M_next_val_438 : Nat.primeCounting 167910 = 15332 := pc_thm_167910
  have h_m_439 : m ≤ 578 := staircase_step_M_direct k m 51156 425756 167910 35832 15332 578 heq (k_mono 652 k h_k_439) h_pc_K_next_438 h_pc_M_next_val_438 rfl (by decide)
  -- Step 439: k >= 652, m <= 578 => k >= 653
  have h_m_mono_439 : m*(m+1)/2 ≤ 167331 := m_mono m 578 h_m_439
  have h_pc_M_439 : Nat.primeCounting 167331 = 15287 := pc_thm_167331
  have h_pc_K_prev_439 : Nat.primeCounting 425756 = 35832 := pc_thm_425756
  have h_k_440 : k ≥ 653 := staircase_step_K_direct k m 51156 167331 425756 15287 35832 653 heq h_m_mono_439 h_pc_M_439 h_pc_K_prev_439 rfl (by decide)
  have h_pc_K_next_439 : Nat.primeCounting 427062 = 35928 := pc_thm_427062
  have h_pc_M_next_val_439 : Nat.primeCounting 166753 = 15233 := pc_thm_166753
  have h_m_440 : m ≤ 576 := staircase_step_M_direct k m 51156 427062 166753 35928 15233 576 heq (k_mono 653 k h_k_440) h_pc_K_next_439 h_pc_M_next_val_439 rfl (by decide)
  -- Step 440: k >= 653, m <= 576 => k >= 654
  have h_m_mono_440 : m*(m+1)/2 ≤ 166176 := m_mono m 576 h_m_440
  have h_pc_M_440 : Nat.primeCounting 166176 = 15185 := pc_thm_166176
  have h_pc_K_prev_440 : Nat.primeCounting 427062 = 35928 := pc_thm_427062
  have h_k_441 : k ≥ 654 := staircase_step_K_direct k m 51156 166176 427062 15185 35928 654 heq h_m_mono_440 h_pc_M_440 h_pc_K_prev_440 rfl (by decide)
  have h_pc_K_next_440 : Nat.primeCounting 428370 = 36031 := pc_thm_428370
  have h_pc_M_next_val_440 : Nat.primeCounting 165600 = 15143 := pc_thm_165600
  have h_m_441 : m ≤ 574 := staircase_step_M_direct k m 51156 428370 165600 36031 15143 574 heq (k_mono 654 k h_k_441) h_pc_K_next_440 h_pc_M_next_val_440 rfl (by decide)
  -- Step 441: k >= 654, m <= 574 => k >= 655
  have h_m_mono_441 : m*(m+1)/2 ≤ 165025 := m_mono m 574 h_m_441
  have h_pc_M_441 : Nat.primeCounting 165025 = 15094 := pc_thm_165025
  have h_pc_K_prev_441 : Nat.primeCounting 428370 = 36031 := pc_thm_428370
  have h_k_442 : k ≥ 655 := staircase_step_K_direct k m 51156 165025 428370 15094 36031 655 heq h_m_mono_441 h_pc_M_441 h_pc_K_prev_441 rfl (by decide)
  have h_pc_K_next_441 : Nat.primeCounting 429680 = 36132 := pc_thm_429680
  have h_pc_M_next_val_441 : Nat.primeCounting 164451 = 15057 := pc_thm_164451
  have h_m_442 : m ≤ 572 := staircase_step_M_direct k m 51156 429680 164451 36132 15057 572 heq (k_mono 655 k h_k_442) h_pc_K_next_441 h_pc_M_next_val_441 rfl (by decide)
  -- Step 442: k >= 655, m <= 572 => k >= 656
  have h_m_mono_442 : m*(m+1)/2 ≤ 163878 := m_mono m 572 h_m_442
  have h_pc_M_442 : Nat.primeCounting 163878 = 15005 := pc_thm_163878
  have h_pc_K_prev_442 : Nat.primeCounting 429680 = 36132 := pc_thm_429680
  have h_k_443 : k ≥ 656 := staircase_step_K_direct k m 51156 163878 429680 15005 36132 656 heq h_m_mono_442 h_pc_M_442 h_pc_K_prev_442 rfl (by decide)
  have h_pc_K_next_442 : Nat.primeCounting 430992 = 36237 := pc_thm_430992
  have h_pc_M_next_val_442 : Nat.primeCounting 163306 = 14955 := pc_thm_163306
  have h_m_443 : m ≤ 570 := staircase_step_M_direct k m 51156 430992 163306 36237 14955 570 heq (k_mono 656 k h_k_443) h_pc_K_next_442 h_pc_M_next_val_442 rfl (by decide)
  -- Step 443: k >= 656, m <= 570 => k >= 657
  have h_m_mono_443 : m*(m+1)/2 ≤ 162735 := m_mono m 570 h_m_443
  have h_pc_M_443 : Nat.primeCounting 162735 = 14909 := pc_thm_162735
  have h_pc_K_prev_443 : Nat.primeCounting 430992 = 36237 := pc_thm_430992
  have h_k_444 : k ≥ 657 := staircase_step_K_direct k m 51156 162735 430992 14909 36237 657 heq h_m_mono_443 h_pc_M_443 h_pc_K_prev_443 rfl (by decide)
  have h_pc_K_next_443 : Nat.primeCounting 432306 = 36345 := pc_thm_432306
  have h_pc_M_next_val_443 : Nat.primeCounting 161596 = 14817 := pc_thm_161596
  have h_m_444 : m ≤ 567 := staircase_step_M_direct k m 51156 432306 161596 36345 14817 567 heq (k_mono 657 k h_k_444) h_pc_K_next_443 h_pc_M_next_val_443 rfl (by decide)
  -- Step 444: k >= 657, m <= 567 => k >= 658
  have h_m_mono_444 : m*(m+1)/2 ≤ 161028 := m_mono m 567 h_m_444
  have h_pc_M_444 : Nat.primeCounting 161028 = 14770 := pc_thm_161028
  have h_pc_K_prev_444 : Nat.primeCounting 432306 = 36345 := pc_thm_432306
  have h_k_445 : k ≥ 658 := staircase_step_K_direct k m 51156 161028 432306 14770 36345 658 heq h_m_mono_444 h_pc_M_444 h_pc_K_prev_444 rfl (by decide)
  have h_pc_K_next_444 : Nat.primeCounting 433622 = 36451 := pc_thm_433622
  have h_pc_M_next_val_444 : Nat.primeCounting 160461 = 14721 := pc_thm_160461
  have h_m_445 : m ≤ 565 := staircase_step_M_direct k m 51156 433622 160461 36451 14721 565 heq (k_mono 658 k h_k_445) h_pc_K_next_444 h_pc_M_next_val_444 rfl (by decide)
  -- Step 445: k >= 658, m <= 565 => k >= 659
  have h_m_mono_445 : m*(m+1)/2 ≤ 159895 := m_mono m 565 h_m_445
  have h_pc_M_445 : Nat.primeCounting 159895 = 14677 := pc_thm_159895
  have h_pc_K_prev_445 : Nat.primeCounting 433622 = 36451 := pc_thm_433622
  have h_k_446 : k ≥ 659 := staircase_step_K_direct k m 51156 159895 433622 14677 36451 659 heq h_m_mono_445 h_pc_M_445 h_pc_K_prev_445 rfl (by decide)
  have h_pc_K_next_445 : Nat.primeCounting 434940 = 36560 := pc_thm_434940
  have h_pc_M_next_val_445 : Nat.primeCounting 159330 = 14623 := pc_thm_159330
  have h_m_446 : m ≤ 563 := staircase_step_M_direct k m 51156 434940 159330 36560 14623 563 heq (k_mono 659 k h_k_446) h_pc_K_next_445 h_pc_M_next_val_445 rfl (by decide)
  -- Step 446: k >= 659, m <= 563 => k >= 660
  have h_m_mono_446 : m*(m+1)/2 ≤ 158766 := m_mono m 563 h_m_446
  have h_pc_M_446 : Nat.primeCounting 158766 = 14582 := pc_thm_158766
  have h_pc_K_prev_446 : Nat.primeCounting 434940 = 36560 := pc_thm_434940
  have h_k_447 : k ≥ 660 := staircase_step_K_direct k m 51156 158766 434940 14582 36560 660 heq h_m_mono_446 h_pc_M_446 h_pc_K_prev_446 rfl (by decide)
  have h_pc_K_next_446 : Nat.primeCounting 436260 = 36665 := pc_thm_436260
  have h_pc_M_next_val_446 : Nat.primeCounting 157641 = 14493 := pc_thm_157641
  have h_m_447 : m ≤ 560 := staircase_step_M_direct k m 51156 436260 157641 36665 14493 560 heq (k_mono 660 k h_k_447) h_pc_K_next_446 h_pc_M_next_val_446 rfl (by decide)
  -- Step 447: k >= 660, m <= 560 => k >= 661
  have h_m_mono_447 : m*(m+1)/2 ≤ 157080 := m_mono m 560 h_m_447
  have h_pc_M_447 : Nat.primeCounting 157080 = 14441 := pc_thm_157080
  have h_pc_K_prev_447 : Nat.primeCounting 436260 = 36665 := pc_thm_436260
  have h_k_448 : k ≥ 661 := staircase_step_K_direct k m 51156 157080 436260 14441 36665 661 heq h_m_mono_447 h_pc_M_447 h_pc_K_prev_447 rfl (by decide)
  have h_pc_K_next_447 : Nat.primeCounting 437582 = 36764 := pc_thm_437582
  have h_pc_M_next_val_447 : Nat.primeCounting 156520 = 14395 := pc_thm_156520
  have h_m_448 : m ≤ 558 := staircase_step_M_direct k m 51156 437582 156520 36764 14395 558 heq (k_mono 661 k h_k_448) h_pc_K_next_447 h_pc_M_next_val_447 rfl (by decide)
  -- Step 448: k >= 661, m <= 558 => k >= 662
  have h_m_mono_448 : m*(m+1)/2 ≤ 155961 := m_mono m 558 h_m_448
  have h_pc_M_448 : Nat.primeCounting 155961 = 14357 := pc_thm_155961
  have h_pc_K_prev_448 : Nat.primeCounting 437582 = 36764 := pc_thm_437582
  have h_k_449 : k ≥ 662 := staircase_step_K_direct k m 51156 155961 437582 14357 36764 662 heq h_m_mono_448 h_pc_M_448 h_pc_K_prev_448 rfl (by decide)
  have h_pc_K_next_448 : Nat.primeCounting 438906 = 36857 := pc_thm_438906
  have h_pc_M_next_val_448 : Nat.primeCounting 155403 = 14307 := pc_thm_155403
  have h_m_449 : m ≤ 556 := staircase_step_M_direct k m 51156 438906 155403 36857 14307 556 heq (k_mono 662 k h_k_449) h_pc_K_next_448 h_pc_M_next_val_448 rfl (by decide)
  -- Step 449: k >= 662, m <= 556 => k >= 663
  have h_m_mono_449 : m*(m+1)/2 ≤ 154846 := m_mono m 556 h_m_449
  have h_pc_M_449 : Nat.primeCounting 154846 = 14260 := pc_thm_154846
  have h_pc_K_prev_449 : Nat.primeCounting 438906 = 36857 := pc_thm_438906
  have h_k_450 : k ≥ 663 := staircase_step_K_direct k m 51156 154846 438906 14260 36857 663 heq h_m_mono_449 h_pc_M_449 h_pc_K_prev_449 rfl (by decide)
  have h_pc_K_next_449 : Nat.primeCounting 440232 = 36958 := pc_thm_440232
  have h_pc_M_next_val_449 : Nat.primeCounting 154290 = 14214 := pc_thm_154290
  have h_m_450 : m ≤ 554 := staircase_step_M_direct k m 51156 440232 154290 36958 14214 554 heq (k_mono 663 k h_k_450) h_pc_K_next_449 h_pc_M_next_val_449 rfl (by decide)
  -- Step 450: k >= 663, m <= 554 => k >= 664
  have h_m_mono_450 : m*(m+1)/2 ≤ 153735 := m_mono m 554 h_m_450
  have h_pc_M_450 : Nat.primeCounting 153735 = 14168 := pc_thm_153735
  have h_pc_K_prev_450 : Nat.primeCounting 440232 = 36958 := pc_thm_440232
  have h_k_451 : k ≥ 664 := staircase_step_K_direct k m 51156 153735 440232 14168 36958 664 heq h_m_mono_450 h_pc_M_450 h_pc_K_prev_450 rfl (by decide)
  have h_pc_K_next_450 : Nat.primeCounting 441560 = 37062 := pc_thm_441560
  have h_pc_M_next_val_450 : Nat.primeCounting 153181 = 14123 := pc_thm_153181
  have h_m_451 : m ≤ 552 := staircase_step_M_direct k m 51156 441560 153181 37062 14123 552 heq (k_mono 664 k h_k_451) h_pc_K_next_450 h_pc_M_next_val_450 rfl (by decide)
  exact ⟨h_k_451, h_m_451⟩

theorem staircase_part_30 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_451 : k ≥ 664) (h_m_451 : m ≤ 552) : k ≥ 679 ∧ m ≤ 518 := by
  -- Step 451: k >= 664, m <= 552 => k >= 665
  have h_m_mono_451 : m*(m+1)/2 ≤ 152628 := m_mono m 552 h_m_451
  have h_pc_M_451 : Nat.primeCounting 152628 = 14076 := pc_thm_152628
  have h_pc_K_prev_451 : Nat.primeCounting 441560 = 37062 := pc_thm_441560
  have h_k_452 : k ≥ 665 := staircase_step_K_direct k m 51156 152628 441560 14076 37062 665 heq h_m_mono_451 h_pc_M_451 h_pc_K_prev_451 rfl (by decide)
  have h_pc_K_next_451 : Nat.primeCounting 442890 = 37168 := pc_thm_442890
  have h_pc_M_next_val_451 : Nat.primeCounting 152076 = 14030 := pc_thm_152076
  have h_m_452 : m ≤ 550 := staircase_step_M_direct k m 51156 442890 152076 37168 14030 550 heq (k_mono 665 k h_k_452) h_pc_K_next_451 h_pc_M_next_val_451 rfl (by decide)
  -- Step 452: k >= 665, m <= 550 => k >= 666
  have h_m_mono_452 : m*(m+1)/2 ≤ 151525 := m_mono m 550 h_m_452
  have h_pc_M_452 : Nat.primeCounting 151525 = 13979 := pc_thm_151525
  have h_pc_K_prev_452 : Nat.primeCounting 442890 = 37168 := pc_thm_442890
  have h_k_453 : k ≥ 666 := staircase_step_K_direct k m 51156 151525 442890 13979 37168 666 heq h_m_mono_452 h_pc_M_452 h_pc_K_prev_452 rfl (by decide)
  have h_pc_K_next_452 : Nat.primeCounting 444222 = 37284 := pc_thm_444222
  have h_pc_M_next_val_452 : Nat.primeCounting 150426 = 13886 := pc_thm_150426
  have h_m_453 : m ≤ 547 := staircase_step_M_direct k m 51156 444222 150426 37284 13886 547 heq (k_mono 666 k h_k_453) h_pc_K_next_452 h_pc_M_next_val_452 rfl (by decide)
  -- Step 453: k >= 666, m <= 547 => k >= 667
  have h_m_mono_453 : m*(m+1)/2 ≤ 149878 := m_mono m 547 h_m_453
  have h_pc_M_453 : Nat.primeCounting 149878 = 13838 := pc_thm_149878
  have h_pc_K_prev_453 : Nat.primeCounting 444222 = 37284 := pc_thm_444222
  have h_k_454 : k ≥ 667 := staircase_step_K_direct k m 51156 149878 444222 13838 37284 667 heq h_m_mono_453 h_pc_M_453 h_pc_K_prev_453 rfl (by decide)
  have h_pc_K_next_453 : Nat.primeCounting 445556 = 37383 := pc_thm_445556
  have h_pc_M_next_val_453 : Nat.primeCounting 149331 = 13789 := pc_thm_149331
  have h_m_454 : m ≤ 545 := staircase_step_M_direct k m 51156 445556 149331 37383 13789 545 heq (k_mono 667 k h_k_454) h_pc_K_next_453 h_pc_M_next_val_453 rfl (by decide)
  -- Step 454: k >= 667, m <= 545 => k >= 668
  have h_m_mono_454 : m*(m+1)/2 ≤ 148785 := m_mono m 545 h_m_454
  have h_pc_M_454 : Nat.primeCounting 148785 = 13738 := pc_thm_148785
  have h_pc_K_prev_454 : Nat.primeCounting 445556 = 37383 := pc_thm_445556
  have h_k_455 : k ≥ 668 := staircase_step_K_direct k m 51156 148785 445556 13738 37383 668 heq h_m_mono_454 h_pc_M_454 h_pc_K_prev_454 rfl (by decide)
  have h_pc_K_next_454 : Nat.primeCounting 446892 = 37475 := pc_thm_446892
  have h_pc_M_next_val_454 : Nat.primeCounting 148240 = 13693 := pc_thm_148240
  have h_m_455 : m ≤ 543 := staircase_step_M_direct k m 51156 446892 148240 37475 13693 543 heq (k_mono 668 k h_k_455) h_pc_K_next_454 h_pc_M_next_val_454 rfl (by decide)
  -- Step 455: k >= 668, m <= 543 => k >= 669
  have h_m_mono_455 : m*(m+1)/2 ≤ 147696 := m_mono m 543 h_m_455
  have h_pc_M_455 : Nat.primeCounting 147696 = 13651 := pc_thm_147696
  have h_pc_K_prev_455 : Nat.primeCounting 446892 = 37475 := pc_thm_446892
  have h_k_456 : k ≥ 669 := staircase_step_K_direct k m 51156 147696 446892 13651 37475 669 heq h_m_mono_455 h_pc_M_455 h_pc_K_prev_455 rfl (by decide)
  have h_pc_K_next_455 : Nat.primeCounting 448230 = 37576 := pc_thm_448230
  have h_pc_M_next_val_455 : Nat.primeCounting 147153 = 13603 := pc_thm_147153
  have h_m_456 : m ≤ 541 := staircase_step_M_direct k m 51156 448230 147153 37576 13603 541 heq (k_mono 669 k h_k_456) h_pc_K_next_455 h_pc_M_next_val_455 rfl (by decide)
  -- Step 456: k >= 669, m <= 541 => k >= 670
  have h_m_mono_456 : m*(m+1)/2 ≤ 146611 := m_mono m 541 h_m_456
  have h_pc_M_456 : Nat.primeCounting 146611 = 13559 := pc_thm_146611
  have h_pc_K_prev_456 : Nat.primeCounting 448230 = 37576 := pc_thm_448230
  have h_k_457 : k ≥ 670 := staircase_step_K_direct k m 51156 146611 448230 13559 37576 670 heq h_m_mono_456 h_pc_M_456 h_pc_K_prev_456 rfl (by decide)
  have h_pc_K_next_456 : Nat.primeCounting 449570 = 37674 := pc_thm_449570
  have h_pc_M_next_val_456 : Nat.primeCounting 146070 = 13516 := pc_thm_146070
  have h_m_457 : m ≤ 539 := staircase_step_M_direct k m 51156 449570 146070 37674 13516 539 heq (k_mono 670 k h_k_457) h_pc_K_next_456 h_pc_M_next_val_456 rfl (by decide)
  -- Step 457: k >= 670, m <= 539 => k >= 671
  have h_m_mono_457 : m*(m+1)/2 ≤ 145530 := m_mono m 539 h_m_457
  have h_pc_M_457 : Nat.primeCounting 145530 = 13466 := pc_thm_145530
  have h_pc_K_prev_457 : Nat.primeCounting 449570 = 37674 := pc_thm_449570
  have h_k_458 : k ≥ 671 := staircase_step_K_direct k m 51156 145530 449570 13466 37674 671 heq h_m_mono_457 h_pc_M_457 h_pc_K_prev_457 rfl (by decide)
  have h_pc_K_next_457 : Nat.primeCounting 450912 = 37790 := pc_thm_450912
  have h_pc_M_next_val_457 : Nat.primeCounting 144453 = 13378 := pc_thm_144453
  have h_m_458 : m ≤ 536 := staircase_step_M_direct k m 51156 450912 144453 37790 13378 536 heq (k_mono 671 k h_k_458) h_pc_K_next_457 h_pc_M_next_val_457 rfl (by decide)
  -- Step 458: k >= 671, m <= 536 => k >= 672
  have h_m_mono_458 : m*(m+1)/2 ≤ 143916 := m_mono m 536 h_m_458
  have h_pc_M_458 : Nat.primeCounting 143916 = 13337 := pc_thm_143916
  have h_pc_K_prev_458 : Nat.primeCounting 450912 = 37790 := pc_thm_450912
  have h_k_459 : k ≥ 672 := staircase_step_K_direct k m 51156 143916 450912 13337 37790 672 heq h_m_mono_458 h_pc_M_458 h_pc_K_prev_458 rfl (by decide)
  have h_pc_K_next_458 : Nat.primeCounting 452256 = 37892 := pc_thm_452256
  have h_pc_M_next_val_458 : Nat.primeCounting 143380 = 13289 := pc_thm_143380
  have h_m_459 : m ≤ 534 := staircase_step_M_direct k m 51156 452256 143380 37892 13289 534 heq (k_mono 672 k h_k_459) h_pc_K_next_458 h_pc_M_next_val_458 rfl (by decide)
  -- Step 459: k >= 672, m <= 534 => k >= 673
  have h_m_mono_459 : m*(m+1)/2 ≤ 142845 := m_mono m 534 h_m_459
  have h_pc_M_459 : Nat.primeCounting 142845 = 13252 := pc_thm_142845
  have h_pc_K_prev_459 : Nat.primeCounting 452256 = 37892 := pc_thm_452256
  have h_k_460 : k ≥ 673 := staircase_step_K_direct k m 51156 142845 452256 13252 37892 673 heq h_m_mono_459 h_pc_M_459 h_pc_K_prev_459 rfl (by decide)
  have h_pc_K_next_459 : Nat.primeCounting 453602 = 37978 := pc_thm_453602
  have h_pc_M_next_val_459 : Nat.primeCounting 142311 = 13210 := pc_thm_142311
  have h_m_460 : m ≤ 532 := staircase_step_M_direct k m 51156 453602 142311 37978 13210 532 heq (k_mono 673 k h_k_460) h_pc_K_next_459 h_pc_M_next_val_459 rfl (by decide)
  -- Step 460: k >= 673, m <= 532 => k >= 674
  have h_m_mono_460 : m*(m+1)/2 ≤ 141778 := m_mono m 532 h_m_460
  have h_pc_M_460 : Nat.primeCounting 141778 = 13166 := pc_thm_141778
  have h_pc_K_prev_460 : Nat.primeCounting 453602 = 37978 := pc_thm_453602
  have h_k_461 : k ≥ 674 := staircase_step_K_direct k m 51156 141778 453602 13166 37978 674 heq h_m_mono_460 h_pc_M_460 h_pc_K_prev_460 rfl (by decide)
  have h_pc_K_next_460 : Nat.primeCounting 454950 = 38079 := pc_thm_454950
  have h_pc_M_next_val_460 : Nat.primeCounting 141246 = 13117 := pc_thm_141246
  have h_m_461 : m ≤ 530 := staircase_step_M_direct k m 51156 454950 141246 38079 13117 530 heq (k_mono 674 k h_k_461) h_pc_K_next_460 h_pc_M_next_val_460 rfl (by decide)
  -- Step 461: k >= 674, m <= 530 => k >= 675
  have h_m_mono_461 : m*(m+1)/2 ≤ 140715 := m_mono m 530 h_m_461
  have h_pc_M_461 : Nat.primeCounting 140715 = 13071 := pc_thm_140715
  have h_pc_K_prev_461 : Nat.primeCounting 454950 = 38079 := pc_thm_454950
  have h_k_462 : k ≥ 675 := staircase_step_K_direct k m 51156 140715 454950 13071 38079 675 heq h_m_mono_461 h_pc_M_461 h_pc_K_prev_461 rfl (by decide)
  have h_pc_K_next_461 : Nat.primeCounting 456300 = 38184 := pc_thm_456300
  have h_pc_M_next_val_461 : Nat.primeCounting 139656 = 12978 := pc_thm_139656
  have h_m_462 : m ≤ 527 := staircase_step_M_direct k m 51156 456300 139656 38184 12978 527 heq (k_mono 675 k h_k_462) h_pc_K_next_461 h_pc_M_next_val_461 rfl (by decide)
  -- Step 462: k >= 675, m <= 527 => k >= 676
  have h_m_mono_462 : m*(m+1)/2 ≤ 139128 := m_mono m 527 h_m_462
  have h_pc_M_462 : Nat.primeCounting 139128 = 12934 := pc_thm_139128
  have h_pc_K_prev_462 : Nat.primeCounting 456300 = 38184 := pc_thm_456300
  have h_k_463 : k ≥ 676 := staircase_step_K_direct k m 51156 139128 456300 12934 38184 676 heq h_m_mono_462 h_pc_M_462 h_pc_K_prev_462 rfl (by decide)
  have h_pc_K_next_462 : Nat.primeCounting 457652 = 38292 := pc_thm_457652
  have h_pc_M_next_val_462 : Nat.primeCounting 138601 = 12896 := pc_thm_138601
  have h_m_463 : m ≤ 525 := staircase_step_M_direct k m 51156 457652 138601 38292 12896 525 heq (k_mono 676 k h_k_463) h_pc_K_next_462 h_pc_M_next_val_462 rfl (by decide)
  -- Step 463: k >= 676, m <= 525 => k >= 677
  have h_m_mono_463 : m*(m+1)/2 ≤ 138075 := m_mono m 525 h_m_463
  have h_pc_M_463 : Nat.primeCounting 138075 = 12846 := pc_thm_138075
  have h_pc_K_prev_463 : Nat.primeCounting 457652 = 38292 := pc_thm_457652
  have h_k_464 : k ≥ 677 := staircase_step_K_direct k m 51156 138075 457652 12846 38292 677 heq h_m_mono_463 h_pc_M_463 h_pc_K_prev_463 rfl (by decide)
  have h_pc_K_next_463 : Nat.primeCounting 459006 = 38390 := pc_thm_459006
  have h_pc_M_next_val_463 : Nat.primeCounting 137550 = 12805 := pc_thm_137550
  have h_m_464 : m ≤ 523 := staircase_step_M_direct k m 51156 459006 137550 38390 12805 523 heq (k_mono 677 k h_k_464) h_pc_K_next_463 h_pc_M_next_val_463 rfl (by decide)
  -- Step 464: k >= 677, m <= 523 => k >= 678
  have h_m_mono_464 : m*(m+1)/2 ≤ 137026 := m_mono m 523 h_m_464
  have h_pc_M_464 : Nat.primeCounting 137026 = 12761 := pc_thm_137026
  have h_pc_K_prev_464 : Nat.primeCounting 459006 = 38390 := pc_thm_459006
  have h_k_465 : k ≥ 678 := staircase_step_K_direct k m 51156 137026 459006 12761 38390 678 heq h_m_mono_464 h_pc_M_464 h_pc_K_prev_464 rfl (by decide)
  have h_pc_K_next_464 : Nat.primeCounting 460362 = 38485 := pc_thm_460362
  have h_pc_M_next_val_464 : Nat.primeCounting 136503 = 12714 := pc_thm_136503
  have h_m_465 : m ≤ 521 := staircase_step_M_direct k m 51156 460362 136503 38485 12714 521 heq (k_mono 678 k h_k_465) h_pc_K_next_464 h_pc_M_next_val_464 rfl (by decide)
  -- Step 465: k >= 678, m <= 521 => k >= 679
  have h_m_mono_465 : m*(m+1)/2 ≤ 135981 := m_mono m 521 h_m_465
  have h_pc_M_465 : Nat.primeCounting 135981 = 12665 := pc_thm_135981
  have h_pc_K_prev_465 : Nat.primeCounting 460362 = 38485 := pc_thm_460362
  have h_k_466 : k ≥ 679 := staircase_step_K_direct k m 51156 135981 460362 12665 38485 679 heq h_m_mono_465 h_pc_M_465 h_pc_K_prev_465 rfl (by decide)
  have h_pc_K_next_465 : Nat.primeCounting 461720 = 38590 := pc_thm_461720
  have h_pc_M_next_val_465 : Nat.primeCounting 134940 = 12572 := pc_thm_134940
  have h_m_466 : m ≤ 518 := staircase_step_M_direct k m 51156 461720 134940 38590 12572 518 heq (k_mono 679 k h_k_466) h_pc_K_next_465 h_pc_M_next_val_465 rfl (by decide)
  exact ⟨h_k_466, h_m_466⟩

theorem staircase_part_31 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_466 : k ≥ 679) (h_m_466 : m ≤ 518) : k ≥ 694 ∧ m ≤ 481 := by
  -- Step 466: k >= 679, m <= 518 => k >= 680
  have h_m_mono_466 : m*(m+1)/2 ≤ 134421 := m_mono m 518 h_m_466
  have h_pc_M_466 : Nat.primeCounting 134421 = 12535 := pc_thm_134421
  have h_pc_K_prev_466 : Nat.primeCounting 461720 = 38590 := pc_thm_461720
  have h_k_467 : k ≥ 680 := staircase_step_K_direct k m 51156 134421 461720 12535 38590 680 heq h_m_mono_466 h_pc_M_466 h_pc_K_prev_466 rfl (by decide)
  have h_pc_K_next_466 : Nat.primeCounting 463080 = 38681 := pc_thm_463080
  have h_pc_M_next_val_466 : Nat.primeCounting 133903 = 12488 := pc_thm_133903
  have h_m_467 : m ≤ 516 := staircase_step_M_direct k m 51156 463080 133903 38681 12488 516 heq (k_mono 680 k h_k_467) h_pc_K_next_466 h_pc_M_next_val_466 rfl (by decide)
  -- Step 467: k >= 680, m <= 516 => k >= 681
  have h_m_mono_467 : m*(m+1)/2 ≤ 133386 := m_mono m 516 h_m_467
  have h_pc_M_467 : Nat.primeCounting 133386 = 12448 := pc_thm_133386
  have h_pc_K_prev_467 : Nat.primeCounting 463080 = 38681 := pc_thm_463080
  have h_k_468 : k ≥ 681 := staircase_step_K_direct k m 51156 133386 463080 12448 38681 681 heq h_m_mono_467 h_pc_M_467 h_pc_K_prev_467 rfl (by decide)
  have h_pc_K_next_467 : Nat.primeCounting 464442 = 38791 := pc_thm_464442
  have h_pc_M_next_val_467 : Nat.primeCounting 132870 = 12403 := pc_thm_132870
  have h_m_468 : m ≤ 514 := staircase_step_M_direct k m 51156 464442 132870 38791 12403 514 heq (k_mono 681 k h_k_468) h_pc_K_next_467 h_pc_M_next_val_467 rfl (by decide)
  -- Step 468: k >= 681, m <= 514 => k >= 682
  have h_m_mono_468 : m*(m+1)/2 ≤ 132355 := m_mono m 514 h_m_468
  have h_pc_M_468 : Nat.primeCounting 132355 = 12355 := pc_thm_132355
  have h_pc_K_prev_468 : Nat.primeCounting 464442 = 38791 := pc_thm_464442
  have h_k_469 : k ≥ 682 := staircase_step_K_direct k m 51156 132355 464442 12355 38791 682 heq h_m_mono_468 h_pc_M_468 h_pc_K_prev_468 rfl (by decide)
  have h_pc_K_next_468 : Nat.primeCounting 465806 = 38901 := pc_thm_465806
  have h_pc_M_next_val_468 : Nat.primeCounting 131328 = 12271 := pc_thm_131328
  have h_m_469 : m ≤ 511 := staircase_step_M_direct k m 51156 465806 131328 38901 12271 511 heq (k_mono 682 k h_k_469) h_pc_K_next_468 h_pc_M_next_val_468 rfl (by decide)
  -- Step 469: k >= 682, m <= 511 => k >= 683
  have h_m_mono_469 : m*(m+1)/2 ≤ 130816 := m_mono m 511 h_m_469
  have h_pc_M_469 : Nat.primeCounting 130816 = 12232 := pc_thm_130816
  have h_pc_K_prev_469 : Nat.primeCounting 465806 = 38901 := pc_thm_465806
  have h_k_470 : k ≥ 683 := staircase_step_K_direct k m 51156 130816 465806 12232 38901 683 heq h_m_mono_469 h_pc_M_469 h_pc_K_prev_469 rfl (by decide)
  have h_pc_K_next_469 : Nat.primeCounting 467172 = 38996 := pc_thm_467172
  have h_pc_M_next_val_469 : Nat.primeCounting 130305 = 12186 := pc_thm_130305
  have h_m_470 : m ≤ 509 := staircase_step_M_direct k m 51156 467172 130305 38996 12186 509 heq (k_mono 683 k h_k_470) h_pc_K_next_469 h_pc_M_next_val_469 rfl (by decide)
  -- Step 470: k >= 683, m <= 509 => k >= 684
  have h_m_mono_470 : m*(m+1)/2 ≤ 129795 := m_mono m 509 h_m_470
  have h_pc_M_470 : Nat.primeCounting 129795 = 12146 := pc_thm_129795
  have h_pc_K_prev_470 : Nat.primeCounting 467172 = 38996 := pc_thm_467172
  have h_k_471 : k ≥ 684 := staircase_step_K_direct k m 51156 129795 467172 12146 38996 684 heq h_m_mono_470 h_pc_M_470 h_pc_K_prev_470 rfl (by decide)
  have h_pc_K_next_470 : Nat.primeCounting 468540 = 39109 := pc_thm_468540
  have h_pc_M_next_val_470 : Nat.primeCounting 128778 = 12055 := pc_thm_128778
  have h_m_471 : m ≤ 506 := staircase_step_M_direct k m 51156 468540 128778 39109 12055 506 heq (k_mono 684 k h_k_471) h_pc_K_next_470 h_pc_M_next_val_470 rfl (by decide)
  -- Step 471: k >= 684, m <= 506 => k >= 685
  have h_m_mono_471 : m*(m+1)/2 ≤ 128271 := m_mono m 506 h_m_471
  have h_pc_M_471 : Nat.primeCounting 128271 = 12007 := pc_thm_128271
  have h_pc_K_prev_471 : Nat.primeCounting 468540 = 39109 := pc_thm_468540
  have h_k_472 : k ≥ 685 := staircase_step_K_direct k m 51156 128271 468540 12007 39109 685 heq h_m_mono_471 h_pc_M_471 h_pc_K_prev_471 rfl (by decide)
  have h_pc_K_next_471 : Nat.primeCounting 469910 = 39217 := pc_thm_469910
  have h_pc_M_next_val_471 : Nat.primeCounting 127765 = 11969 := pc_thm_127765
  have h_m_472 : m ≤ 504 := staircase_step_M_direct k m 51156 469910 127765 39217 11969 504 heq (k_mono 685 k h_k_472) h_pc_K_next_471 h_pc_M_next_val_471 rfl (by decide)
  -- Step 472: k >= 685, m <= 504 => k >= 686
  have h_m_mono_472 : m*(m+1)/2 ≤ 127260 := m_mono m 504 h_m_472
  have h_pc_M_472 : Nat.primeCounting 127260 = 11920 := pc_thm_127260
  have h_pc_K_prev_472 : Nat.primeCounting 469910 = 39217 := pc_thm_469910
  have h_k_473 : k ≥ 686 := staircase_step_K_direct k m 51156 127260 469910 11920 39217 686 heq h_m_mono_472 h_pc_M_472 h_pc_K_prev_472 rfl (by decide)
  have h_pc_K_next_472 : Nat.primeCounting 471282 = 39331 := pc_thm_471282
  have h_pc_M_next_val_472 : Nat.primeCounting 126253 = 11843 := pc_thm_126253
  have h_m_473 : m ≤ 501 := staircase_step_M_direct k m 51156 471282 126253 39331 11843 501 heq (k_mono 686 k h_k_473) h_pc_K_next_472 h_pc_M_next_val_472 rfl (by decide)
  -- Step 473: k >= 686, m <= 501 => k >= 687
  have h_m_mono_473 : m*(m+1)/2 ≤ 125751 := m_mono m 501 h_m_473
  have h_pc_M_473 : Nat.primeCounting 125751 = 11800 := pc_thm_125751
  have h_pc_K_prev_473 : Nat.primeCounting 471282 = 39331 := pc_thm_471282
  have h_k_474 : k ≥ 687 := staircase_step_K_direct k m 51156 125751 471282 11800 39331 687 heq h_m_mono_473 h_pc_M_473 h_pc_K_prev_473 rfl (by decide)
  have h_pc_K_next_473 : Nat.primeCounting 472656 = 39436 := pc_thm_472656
  have h_pc_M_next_val_473 : Nat.primeCounting 125250 = 11756 := pc_thm_125250
  have h_m_474 : m ≤ 499 := staircase_step_M_direct k m 51156 472656 125250 39436 11756 499 heq (k_mono 687 k h_k_474) h_pc_K_next_473 h_pc_M_next_val_473 rfl (by decide)
  -- Step 474: k >= 687, m <= 499 => k >= 688
  have h_m_mono_474 : m*(m+1)/2 ≤ 124750 := m_mono m 499 h_m_474
  have h_pc_M_474 : Nat.primeCounting 124750 = 11712 := pc_thm_124750
  have h_pc_K_prev_474 : Nat.primeCounting 472656 = 39436 := pc_thm_472656
  have h_k_475 : k ≥ 688 := staircase_step_K_direct k m 51156 124750 472656 11712 39436 688 heq h_m_mono_474 h_pc_M_474 h_pc_K_prev_474 rfl (by decide)
  have h_pc_K_next_474 : Nat.primeCounting 474032 = 39541 := pc_thm_474032
  have h_pc_M_next_val_474 : Nat.primeCounting 123753 = 11630 := pc_thm_123753
  have h_m_475 : m ≤ 496 := staircase_step_M_direct k m 51156 474032 123753 39541 11630 496 heq (k_mono 688 k h_k_475) h_pc_K_next_474 h_pc_M_next_val_474 rfl (by decide)
  -- Step 475: k >= 688, m <= 496 => k >= 689
  have h_m_mono_475 : m*(m+1)/2 ≤ 123256 := m_mono m 496 h_m_475
  have h_pc_M_475 : Nat.primeCounting 123256 = 11583 := pc_thm_123256
  have h_pc_K_prev_475 : Nat.primeCounting 474032 = 39541 := pc_thm_474032
  have h_k_476 : k ≥ 689 := staircase_step_K_direct k m 51156 123256 474032 11583 39541 689 heq h_m_mono_475 h_pc_M_475 h_pc_K_prev_475 rfl (by decide)
  have h_pc_K_next_475 : Nat.primeCounting 475410 = 39651 := pc_thm_475410
  have h_pc_M_next_val_475 : Nat.primeCounting 122760 = 11543 := pc_thm_122760
  have h_m_476 : m ≤ 494 := staircase_step_M_direct k m 51156 475410 122760 39651 11543 494 heq (k_mono 689 k h_k_476) h_pc_K_next_475 h_pc_M_next_val_475 rfl (by decide)
  -- Step 476: k >= 689, m <= 494 => k >= 690
  have h_m_mono_476 : m*(m+1)/2 ≤ 122265 := m_mono m 494 h_m_476
  have h_pc_M_476 : Nat.primeCounting 122265 = 11501 := pc_thm_122265
  have h_pc_K_prev_476 : Nat.primeCounting 475410 = 39651 := pc_thm_475410
  have h_k_477 : k ≥ 690 := staircase_step_K_direct k m 51156 122265 475410 11501 39651 690 heq h_m_mono_476 h_pc_M_476 h_pc_K_prev_476 rfl (by decide)
  have h_pc_K_next_476 : Nat.primeCounting 476790 = 39766 := pc_thm_476790
  have h_pc_M_next_val_476 : Nat.primeCounting 121278 = 11411 := pc_thm_121278
  have h_m_477 : m ≤ 491 := staircase_step_M_direct k m 51156 476790 121278 39766 11411 491 heq (k_mono 690 k h_k_477) h_pc_K_next_476 h_pc_M_next_val_476 rfl (by decide)
  -- Step 477: k >= 690, m <= 491 => k >= 691
  have h_m_mono_477 : m*(m+1)/2 ≤ 120786 := m_mono m 491 h_m_477
  have h_pc_M_477 : Nat.primeCounting 120786 = 11367 := pc_thm_120786
  have h_pc_K_prev_477 : Nat.primeCounting 476790 = 39766 := pc_thm_476790
  have h_k_478 : k ≥ 691 := staircase_step_K_direct k m 51156 120786 476790 11367 39766 691 heq h_m_mono_477 h_pc_M_477 h_pc_K_prev_477 rfl (by decide)
  have h_pc_K_next_477 : Nat.primeCounting 478172 = 39862 := pc_thm_478172
  have h_pc_M_next_val_477 : Nat.primeCounting 120295 = 11326 := pc_thm_120295
  have h_m_478 : m ≤ 489 := staircase_step_M_direct k m 51156 478172 120295 39862 11326 489 heq (k_mono 691 k h_k_478) h_pc_K_next_477 h_pc_M_next_val_477 rfl (by decide)
  -- Step 478: k >= 691, m <= 489 => k >= 692
  have h_m_mono_478 : m*(m+1)/2 ≤ 119805 := m_mono m 489 h_m_478
  have h_pc_M_478 : Nat.primeCounting 119805 = 11282 := pc_thm_119805
  have h_pc_K_prev_478 : Nat.primeCounting 478172 = 39862 := pc_thm_478172
  have h_k_479 : k ≥ 692 := staircase_step_K_direct k m 51156 119805 478172 11282 39862 692 heq h_m_mono_478 h_pc_M_478 h_pc_K_prev_478 rfl (by decide)
  have h_pc_K_next_478 : Nat.primeCounting 479556 = 39974 := pc_thm_479556
  have h_pc_M_next_val_478 : Nat.primeCounting 118828 = 11200 := pc_thm_118828
  have h_m_479 : m ≤ 486 := staircase_step_M_direct k m 51156 479556 118828 39974 11200 486 heq (k_mono 692 k h_k_479) h_pc_K_next_478 h_pc_M_next_val_478 rfl (by decide)
  -- Step 479: k >= 692, m <= 486 => k >= 693
  have h_m_mono_479 : m*(m+1)/2 ≤ 118341 := m_mono m 486 h_m_479
  have h_pc_M_479 : Nat.primeCounting 118341 = 11159 := pc_thm_118341
  have h_pc_K_prev_479 : Nat.primeCounting 479556 = 39974 := pc_thm_479556
  have h_k_480 : k ≥ 693 := staircase_step_K_direct k m 51156 118341 479556 11159 39974 693 heq h_m_mono_479 h_pc_M_479 h_pc_K_prev_479 rfl (by decide)
  have h_pc_K_next_479 : Nat.primeCounting 480942 = 40078 := pc_thm_480942
  have h_pc_M_next_val_479 : Nat.primeCounting 117855 = 11121 := pc_thm_117855
  have h_m_480 : m ≤ 484 := staircase_step_M_direct k m 51156 480942 117855 40078 11121 484 heq (k_mono 693 k h_k_480) h_pc_K_next_479 h_pc_M_next_val_479 rfl (by decide)
  -- Step 480: k >= 693, m <= 484 => k >= 694
  have h_m_mono_480 : m*(m+1)/2 ≤ 117370 := m_mono m 484 h_m_480
  have h_pc_M_480 : Nat.primeCounting 117370 = 11076 := pc_thm_117370
  have h_pc_K_prev_480 : Nat.primeCounting 480942 = 40078 := pc_thm_480942
  have h_k_481 : k ≥ 694 := staircase_step_K_direct k m 51156 117370 480942 11076 40078 694 heq h_m_mono_480 h_pc_M_480 h_pc_K_prev_480 rfl (by decide)
  have h_pc_K_next_480 : Nat.primeCounting 482330 = 40184 := pc_thm_482330
  have h_pc_M_next_val_480 : Nat.primeCounting 116403 = 10995 := pc_thm_116403
  have h_m_481 : m ≤ 481 := staircase_step_M_direct k m 51156 482330 116403 40184 10995 481 heq (k_mono 694 k h_k_481) h_pc_K_next_480 h_pc_M_next_val_480 rfl (by decide)
  exact ⟨h_k_481, h_m_481⟩

theorem staircase_part_32 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_481 : k ≥ 694) (h_m_481 : m ≤ 481) : k ≥ 709 ∧ m ≤ 440 := by
  -- Step 481: k >= 694, m <= 481 => k >= 695
  have h_m_mono_481 : m*(m+1)/2 ≤ 115921 := m_mono m 481 h_m_481
  have h_pc_M_481 : Nat.primeCounting 115921 = 10958 := pc_thm_115921
  have h_pc_K_prev_481 : Nat.primeCounting 482330 = 40184 := pc_thm_482330
  have h_k_482 : k ≥ 695 := staircase_step_K_direct k m 51156 115921 482330 10958 40184 695 heq h_m_mono_481 h_pc_M_481 h_pc_K_prev_481 rfl (by decide)
  have h_pc_K_next_481 : Nat.primeCounting 483720 = 40294 := pc_thm_483720
  have h_pc_M_next_val_481 : Nat.primeCounting 114960 = 10868 := pc_thm_114960
  have h_m_482 : m ≤ 478 := staircase_step_M_direct k m 51156 483720 114960 40294 10868 478 heq (k_mono 695 k h_k_482) h_pc_K_next_481 h_pc_M_next_val_481 rfl (by decide)
  -- Step 482: k >= 695, m <= 478 => k >= 696
  have h_m_mono_482 : m*(m+1)/2 ≤ 114481 := m_mono m 478 h_m_482
  have h_pc_M_482 : Nat.primeCounting 114481 = 10828 := pc_thm_114481
  have h_pc_K_prev_482 : Nat.primeCounting 483720 = 40294 := pc_thm_483720
  have h_k_483 : k ≥ 696 := staircase_step_K_direct k m 51156 114481 483720 10828 40294 696 heq h_m_mono_482 h_pc_M_482 h_pc_K_prev_482 rfl (by decide)
  have h_pc_K_next_482 : Nat.primeCounting 485112 = 40390 := pc_thm_485112
  have h_pc_M_next_val_482 : Nat.primeCounting 114003 = 10790 := pc_thm_114003
  have h_m_483 : m ≤ 476 := staircase_step_M_direct k m 51156 485112 114003 40390 10790 476 heq (k_mono 696 k h_k_483) h_pc_K_next_482 h_pc_M_next_val_482 rfl (by decide)
  -- Step 483: k >= 696, m <= 476 => k >= 697
  have h_m_mono_483 : m*(m+1)/2 ≤ 113526 := m_mono m 476 h_m_483
  have h_pc_M_483 : Nat.primeCounting 113526 = 10752 := pc_thm_113526
  have h_pc_K_prev_483 : Nat.primeCounting 485112 = 40390 := pc_thm_485112
  have h_k_484 : k ≥ 697 := staircase_step_K_direct k m 51156 113526 485112 10752 40390 697 heq h_m_mono_483 h_pc_M_483 h_pc_K_prev_483 rfl (by decide)
  have h_pc_K_next_483 : Nat.primeCounting 486506 = 40486 := pc_thm_486506
  have h_pc_M_next_val_483 : Nat.primeCounting 113050 = 10708 := pc_thm_113050
  have h_m_484 : m ≤ 474 := staircase_step_M_direct k m 51156 486506 113050 40486 10708 474 heq (k_mono 697 k h_k_484) h_pc_K_next_483 h_pc_M_next_val_483 rfl (by decide)
  -- Step 484: k >= 697, m <= 474 => k >= 698
  have h_m_mono_484 : m*(m+1)/2 ≤ 112575 := m_mono m 474 h_m_484
  have h_pc_M_484 : Nat.primeCounting 112575 = 10668 := pc_thm_112575
  have h_pc_K_prev_484 : Nat.primeCounting 486506 = 40486 := pc_thm_486506
  have h_k_485 : k ≥ 698 := staircase_step_K_direct k m 51156 112575 486506 10668 40486 698 heq h_m_mono_484 h_pc_M_484 h_pc_K_prev_484 rfl (by decide)
  have h_pc_K_next_484 : Nat.primeCounting 487902 = 40600 := pc_thm_487902
  have h_pc_M_next_val_484 : Nat.primeCounting 111628 = 10586 := pc_thm_111628
  have h_m_485 : m ≤ 471 := staircase_step_M_direct k m 51156 487902 111628 40600 10586 471 heq (k_mono 698 k h_k_485) h_pc_K_next_484 h_pc_M_next_val_484 rfl (by decide)
  -- Step 485: k >= 698, m <= 471 => k >= 699
  have h_m_mono_485 : m*(m+1)/2 ≤ 111156 := m_mono m 471 h_m_485
  have h_pc_M_485 : Nat.primeCounting 111156 = 10549 := pc_thm_111156
  have h_pc_K_prev_485 : Nat.primeCounting 487902 = 40600 := pc_thm_487902
  have h_k_486 : k ≥ 699 := staircase_step_K_direct k m 51156 111156 487902 10549 40600 699 heq h_m_mono_485 h_pc_M_485 h_pc_K_prev_485 rfl (by decide)
  have h_pc_K_next_485 : Nat.primeCounting 489300 = 40711 := pc_thm_489300
  have h_pc_M_next_val_485 : Nat.primeCounting 110215 = 10465 := pc_thm_110215
  have h_m_486 : m ≤ 468 := staircase_step_M_direct k m 51156 489300 110215 40711 10465 468 heq (k_mono 699 k h_k_486) h_pc_K_next_485 h_pc_M_next_val_485 rfl (by decide)
  -- Step 486: k >= 699, m <= 468 => k >= 700
  have h_m_mono_486 : m*(m+1)/2 ≤ 109746 := m_mono m 468 h_m_486
  have h_pc_M_486 : Nat.primeCounting 109746 = 10430 := pc_thm_109746
  have h_pc_K_prev_486 : Nat.primeCounting 489300 = 40711 := pc_thm_489300
  have h_k_487 : k ≥ 700 := staircase_step_K_direct k m 51156 109746 489300 10430 40711 700 heq h_m_mono_486 h_pc_M_486 h_pc_K_prev_486 rfl (by decide)
  have h_pc_K_next_486 : Nat.primeCounting 490700 = 40822 := pc_thm_490700
  have h_pc_M_next_val_486 : Nat.primeCounting 108811 = 10344 := pc_thm_108811
  have h_m_487 : m ≤ 465 := staircase_step_M_direct k m 51156 490700 108811 40822 10344 465 heq (k_mono 700 k h_k_487) h_pc_K_next_486 h_pc_M_next_val_486 rfl (by decide)
  -- Step 487: k >= 700, m <= 465 => k >= 701
  have h_m_mono_487 : m*(m+1)/2 ≤ 108345 := m_mono m 465 h_m_487
  have h_pc_M_487 : Nat.primeCounting 108345 = 10306 := pc_thm_108345
  have h_pc_K_prev_487 : Nat.primeCounting 490700 = 40822 := pc_thm_490700
  have h_k_488 : k ≥ 701 := staircase_step_K_direct k m 51156 108345 490700 10306 40822 701 heq h_m_mono_487 h_pc_M_487 h_pc_K_prev_487 rfl (by decide)
  have h_pc_K_next_487 : Nat.primeCounting 492102 = 40931 := pc_thm_492102
  have h_pc_M_next_val_487 : Nat.primeCounting 107416 = 10229 := pc_thm_107416
  have h_m_488 : m ≤ 462 := staircase_step_M_direct k m 51156 492102 107416 40931 10229 462 heq (k_mono 701 k h_k_488) h_pc_K_next_487 h_pc_M_next_val_487 rfl (by decide)
  -- Step 488: k >= 701, m <= 462 => k >= 702
  have h_m_mono_488 : m*(m+1)/2 ≤ 106953 := m_mono m 462 h_m_488
  have h_pc_M_488 : Nat.primeCounting 106953 = 10193 := pc_thm_106953
  have h_pc_K_prev_488 : Nat.primeCounting 492102 = 40931 := pc_thm_492102
  have h_k_489 : k ≥ 702 := staircase_step_K_direct k m 51156 106953 492102 10193 40931 702 heq h_m_mono_488 h_pc_M_488 h_pc_K_prev_488 rfl (by decide)
  have h_pc_K_next_488 : Nat.primeCounting 493506 = 41031 := pc_thm_493506
  have h_pc_M_next_val_488 : Nat.primeCounting 106491 = 10151 := pc_thm_106491
  have h_m_489 : m ≤ 460 := staircase_step_M_direct k m 51156 493506 106491 41031 10151 460 heq (k_mono 702 k h_k_489) h_pc_K_next_488 h_pc_M_next_val_488 rfl (by decide)
  -- Step 489: k >= 702, m <= 460 => k >= 703
  have h_m_mono_489 : m*(m+1)/2 ≤ 106030 := m_mono m 460 h_m_489
  have h_pc_M_489 : Nat.primeCounting 106030 = 10108 := pc_thm_106030
  have h_pc_K_prev_489 : Nat.primeCounting 493506 = 41031 := pc_thm_493506
  have h_k_490 : k ≥ 703 := staircase_step_K_direct k m 51156 106030 493506 10108 41031 703 heq h_m_mono_489 h_pc_M_489 h_pc_K_prev_489 rfl (by decide)
  have h_pc_K_next_489 : Nat.primeCounting 494912 = 41143 := pc_thm_494912
  have h_pc_M_next_val_489 : Nat.primeCounting 105111 = 10031 := pc_thm_105111
  have h_m_490 : m ≤ 457 := staircase_step_M_direct k m 51156 494912 105111 41143 10031 457 heq (k_mono 703 k h_k_490) h_pc_K_next_489 h_pc_M_next_val_489 rfl (by decide)
  -- Step 490: k >= 703, m <= 457 => k >= 704
  have h_m_mono_490 : m*(m+1)/2 ≤ 104653 := m_mono m 457 h_m_490
  have h_pc_M_490 : Nat.primeCounting 104653 = 9989 := pc_thm_104653
  have h_pc_K_prev_490 : Nat.primeCounting 494912 = 41143 := pc_thm_494912
  have h_k_491 : k ≥ 704 := staircase_step_K_direct k m 51156 104653 494912 9989 41143 704 heq h_m_mono_490 h_pc_M_490 h_pc_K_prev_490 rfl (by decide)
  have h_pc_K_next_490 : Nat.primeCounting 496320 = 41258 := pc_thm_496320
  have h_pc_M_next_val_490 : Nat.primeCounting 103740 = 9911 := pc_thm_103740
  have h_m_491 : m ≤ 454 := staircase_step_M_direct k m 51156 496320 103740 41258 9911 454 heq (k_mono 704 k h_k_491) h_pc_K_next_490 h_pc_M_next_val_490 rfl (by decide)
  -- Step 491: k >= 704, m <= 454 => k >= 705
  have h_m_mono_491 : m*(m+1)/2 ≤ 103285 := m_mono m 454 h_m_491
  have h_pc_M_491 : Nat.primeCounting 103285 = 9872 := pc_thm_103285
  have h_pc_K_prev_491 : Nat.primeCounting 496320 = 41258 := pc_thm_496320
  have h_k_492 : k ≥ 705 := staircase_step_K_direct k m 51156 103285 496320 9872 41258 705 heq h_m_mono_491 h_pc_M_491 h_pc_K_prev_491 rfl (by decide)
  have h_pc_K_next_491 : Nat.primeCounting 497730 = 41364 := pc_thm_497730
  have h_pc_M_next_val_491 : Nat.primeCounting 102378 = 9804 := pc_thm_102378
  have h_m_492 : m ≤ 451 := staircase_step_M_direct k m 51156 497730 102378 41364 9804 451 heq (k_mono 705 k h_k_492) h_pc_K_next_491 h_pc_M_next_val_491 rfl (by decide)
  -- Step 492: k >= 705, m <= 451 => k >= 706
  have h_m_mono_492 : m*(m+1)/2 ≤ 101926 := m_mono m 451 h_m_492
  have h_pc_M_492 : Nat.primeCounting 101926 = 9759 := pc_thm_101926
  have h_pc_K_prev_492 : Nat.primeCounting 497730 = 41364 := pc_thm_497730
  have h_k_493 : k ≥ 706 := staircase_step_K_direct k m 51156 101926 497730 9759 41364 706 heq h_m_mono_492 h_pc_M_492 h_pc_K_prev_492 rfl (by decide)
  have h_pc_K_next_492 : Nat.primeCounting 499142 = 41470 := pc_thm_499142
  have h_pc_M_next_val_492 : Nat.primeCounting 101475 = 9716 := pc_thm_101475
  have h_m_493 : m ≤ 449 := staircase_step_M_direct k m 51156 499142 101475 41470 9716 449 heq (k_mono 706 k h_k_493) h_pc_K_next_492 h_pc_M_next_val_492 rfl (by decide)
  -- Step 493: k >= 706, m <= 449 => k >= 707
  have h_m_mono_493 : m*(m+1)/2 ≤ 101025 := m_mono m 449 h_m_493
  have h_pc_M_493 : Nat.primeCounting 101025 = 9675 := pc_thm_101025
  have h_pc_K_prev_493 : Nat.primeCounting 499142 = 41470 := pc_thm_499142
  have h_k_494 : k ≥ 707 := staircase_step_K_direct k m 51156 101025 499142 9675 41470 707 heq h_m_mono_493 h_pc_M_493 h_pc_K_prev_493 rfl (by decide)
  have h_pc_K_next_493 : Nat.primeCounting 500556 = 41583 := pc_thm_500556
  have h_pc_M_next_val_493 : Nat.primeCounting 100128 = 9600 := pc_thm_100128
  have h_m_494 : m ≤ 446 := staircase_step_M_direct k m 51156 500556 100128 41583 9600 446 heq (k_mono 707 k h_k_494) h_pc_K_next_493 h_pc_M_next_val_493 rfl (by decide)
  -- Step 494: k >= 707, m <= 446 => k >= 708
  have h_m_mono_494 : m*(m+1)/2 ≤ 99681 := m_mono m 446 h_m_494
  have h_pc_M_494 : Nat.primeCounting 99681 = 9563 := pc_thm_99681
  have h_pc_K_prev_494 : Nat.primeCounting 500556 = 41583 := pc_thm_500556
  have h_k_495 : k ≥ 708 := staircase_step_K_direct k m 51156 99681 500556 9563 41583 708 heq h_m_mono_494 h_pc_M_494 h_pc_K_prev_494 rfl (by decide)
  have h_pc_K_next_494 : Nat.primeCounting 501972 = 41690 := pc_thm_501972
  have h_pc_M_next_val_494 : Nat.primeCounting 98790 = 9482 := pc_thm_98790
  have h_m_495 : m ≤ 443 := staircase_step_M_direct k m 51156 501972 98790 41690 9482 443 heq (k_mono 708 k h_k_495) h_pc_K_next_494 h_pc_M_next_val_494 rfl (by decide)
  -- Step 495: k >= 708, m <= 443 => k >= 709
  have h_m_mono_495 : m*(m+1)/2 ≤ 98346 := m_mono m 443 h_m_495
  have h_pc_M_495 : Nat.primeCounting 98346 = 9443 := pc_thm_98346
  have h_pc_K_prev_495 : Nat.primeCounting 501972 = 41690 := pc_thm_501972
  have h_k_496 : k ≥ 709 := staircase_step_K_direct k m 51156 98346 501972 9443 41690 709 heq h_m_mono_495 h_pc_M_495 h_pc_K_prev_495 rfl (by decide)
  have h_pc_K_next_495 : Nat.primeCounting 503390 = 41787 := pc_thm_503390
  have h_pc_M_next_val_495 : Nat.primeCounting 97461 = 9373 := pc_thm_97461
  have h_m_496 : m ≤ 440 := staircase_step_M_direct k m 51156 503390 97461 41787 9373 440 heq (k_mono 709 k h_k_496) h_pc_K_next_495 h_pc_M_next_val_495 rfl (by decide)
  exact ⟨h_k_496, h_m_496⟩

theorem staircase_part_33 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_496 : k ≥ 709) (h_m_496 : m ≤ 440) : k ≥ 724 ∧ m ≤ 396 := by
  -- Step 496: k >= 709, m <= 440 => k >= 710
  have h_m_mono_496 : m*(m+1)/2 ≤ 97020 := m_mono m 440 h_m_496
  have h_pc_M_496 : Nat.primeCounting 97020 = 9339 := pc_thm_97020
  have h_pc_K_prev_496 : Nat.primeCounting 503390 = 41787 := pc_thm_503390
  have h_k_497 : k ≥ 710 := staircase_step_K_direct k m 51156 97020 503390 9339 41787 710 heq h_m_mono_496 h_pc_M_496 h_pc_K_prev_496 rfl (by decide)
  have h_pc_K_next_496 : Nat.primeCounting 504810 = 41892 := pc_thm_504810
  have h_pc_M_next_val_496 : Nat.primeCounting 96580 = 9299 := pc_thm_96580
  have h_m_497 : m ≤ 438 := staircase_step_M_direct k m 51156 504810 96580 41892 9299 438 heq (k_mono 710 k h_k_497) h_pc_K_next_496 h_pc_M_next_val_496 rfl (by decide)
  -- Step 497: k >= 710, m <= 438 => k >= 711
  have h_m_mono_497 : m*(m+1)/2 ≤ 96141 := m_mono m 438 h_m_497
  have h_pc_M_497 : Nat.primeCounting 96141 = 9261 := pc_thm_96141
  have h_pc_K_prev_497 : Nat.primeCounting 504810 = 41892 := pc_thm_504810
  have h_k_498 : k ≥ 711 := staircase_step_K_direct k m 51156 96141 504810 9261 41892 711 heq h_m_mono_497 h_pc_M_497 h_pc_K_prev_497 rfl (by decide)
  have h_pc_K_next_497 : Nat.primeCounting 506232 = 42006 := pc_thm_506232
  have h_pc_M_next_val_497 : Nat.primeCounting 95266 = 9184 := pc_thm_95266
  have h_m_498 : m ≤ 435 := staircase_step_M_direct k m 51156 506232 95266 42006 9184 435 heq (k_mono 711 k h_k_498) h_pc_K_next_497 h_pc_M_next_val_497 rfl (by decide)
  -- Step 498: k >= 711, m <= 435 => k >= 712
  have h_m_mono_498 : m*(m+1)/2 ≤ 94830 := m_mono m 435 h_m_498
  have h_pc_M_498 : Nat.primeCounting 94830 = 9143 := pc_thm_94830
  have h_pc_K_prev_498 : Nat.primeCounting 506232 = 42006 := pc_thm_506232
  have h_k_499 : k ≥ 712 := staircase_step_K_direct k m 51156 94830 506232 9143 42006 712 heq h_m_mono_498 h_pc_M_498 h_pc_K_prev_498 rfl (by decide)
  have h_pc_K_next_498 : Nat.primeCounting 507656 = 42114 := pc_thm_507656
  have h_pc_M_next_val_498 : Nat.primeCounting 93961 = 9065 := pc_thm_93961
  have h_m_499 : m ≤ 432 := staircase_step_M_direct k m 51156 507656 93961 42114 9065 432 heq (k_mono 712 k h_k_499) h_pc_K_next_498 h_pc_M_next_val_498 rfl (by decide)
  -- Step 499: k >= 712, m <= 432 => k >= 713
  have h_m_mono_499 : m*(m+1)/2 ≤ 93528 := m_mono m 432 h_m_499
  have h_pc_M_499 : Nat.primeCounting 93528 = 9032 := pc_thm_93528
  have h_pc_K_prev_499 : Nat.primeCounting 507656 = 42114 := pc_thm_507656
  have h_k_500 : k ≥ 713 := staircase_step_K_direct k m 51156 93528 507656 9032 42114 713 heq h_m_mono_499 h_pc_M_499 h_pc_K_prev_499 rfl (by decide)
  have h_pc_K_next_499 : Nat.primeCounting 509082 = 42221 := pc_thm_509082
  have h_pc_M_next_val_499 : Nat.primeCounting 92665 = 8949 := pc_thm_92665
  have h_m_500 : m ≤ 429 := staircase_step_M_direct k m 51156 509082 92665 42221 8949 429 heq (k_mono 713 k h_k_500) h_pc_K_next_499 h_pc_M_next_val_499 rfl (by decide)
  -- Step 500: k >= 713, m <= 429 => k >= 714
  have h_m_mono_500 : m*(m+1)/2 ≤ 92235 := m_mono m 429 h_m_500
  have h_pc_M_500 : Nat.primeCounting 92235 = 8908 := pc_thm_92235
  have h_pc_K_prev_500 : Nat.primeCounting 509082 = 42221 := pc_thm_509082
  have h_k_501 : k ≥ 714 := staircase_step_K_direct k m 51156 92235 509082 8908 42221 714 heq h_m_mono_500 h_pc_M_500 h_pc_K_prev_500 rfl (by decide)
  have h_pc_K_next_500 : Nat.primeCounting 510510 = 42331 := pc_thm_510510
  have h_pc_M_next_val_500 : Nat.primeCounting 91378 = 8835 := pc_thm_91378
  have h_m_501 : m ≤ 426 := staircase_step_M_direct k m 51156 510510 91378 42331 8835 426 heq (k_mono 714 k h_k_501) h_pc_K_next_500 h_pc_M_next_val_500 rfl (by decide)
  -- Step 501: k >= 714, m <= 426 => k >= 715
  have h_m_mono_501 : m*(m+1)/2 ≤ 90951 := m_mono m 426 h_m_501
  have h_pc_M_501 : Nat.primeCounting 90951 = 8798 := pc_thm_90951
  have h_pc_K_prev_501 : Nat.primeCounting 510510 = 42331 := pc_thm_510510
  have h_k_502 : k ≥ 715 := staircase_step_K_direct k m 51156 90951 510510 8798 42331 715 heq h_m_mono_501 h_pc_M_501 h_pc_K_prev_501 rfl (by decide)
  have h_pc_K_next_501 : Nat.primeCounting 511940 = 42441 := pc_thm_511940
  have h_pc_M_next_val_501 : Nat.primeCounting 90100 = 8726 := pc_thm_90100
  have h_m_502 : m ≤ 423 := staircase_step_M_direct k m 51156 511940 90100 42441 8726 423 heq (k_mono 715 k h_k_502) h_pc_K_next_501 h_pc_M_next_val_501 rfl (by decide)
  -- Step 502: k >= 715, m <= 423 => k >= 716
  have h_m_mono_502 : m*(m+1)/2 ≤ 89676 := m_mono m 423 h_m_502
  have h_pc_M_502 : Nat.primeCounting 89676 = 8686 := pc_thm_89676
  have h_pc_K_prev_502 : Nat.primeCounting 511940 = 42441 := pc_thm_511940
  have h_k_503 : k ≥ 716 := staircase_step_K_direct k m 51156 89676 511940 8686 42441 716 heq h_m_mono_502 h_pc_M_502 h_pc_K_prev_502 rfl (by decide)
  have h_pc_K_next_502 : Nat.primeCounting 513372 = 42549 := pc_thm_513372
  have h_pc_M_next_val_502 : Nat.primeCounting 89253 = 8644 := pc_thm_89253
  have h_m_503 : m ≤ 421 := staircase_step_M_direct k m 51156 513372 89253 42549 8644 421 heq (k_mono 716 k h_k_503) h_pc_K_next_502 h_pc_M_next_val_502 rfl (by decide)
  -- Step 503: k >= 716, m <= 421 => k >= 717
  have h_m_mono_503 : m*(m+1)/2 ≤ 88831 := m_mono m 421 h_m_503
  have h_pc_M_503 : Nat.primeCounting 88831 = 8605 := pc_thm_88831
  have h_pc_K_prev_503 : Nat.primeCounting 513372 = 42549 := pc_thm_513372
  have h_k_504 : k ≥ 717 := staircase_step_K_direct k m 51156 88831 513372 8605 42549 717 heq h_m_mono_503 h_pc_M_503 h_pc_K_prev_503 rfl (by decide)
  have h_pc_K_next_503 : Nat.primeCounting 514806 = 42658 := pc_thm_514806
  have h_pc_M_next_val_503 : Nat.primeCounting 87571 = 8502 := pc_thm_87571
  have h_m_504 : m ≤ 417 := staircase_step_M_direct k m 51156 514806 87571 42658 8502 417 heq (k_mono 717 k h_k_504) h_pc_K_next_503 h_pc_M_next_val_503 rfl (by decide)
  -- Step 504: k >= 717, m <= 417 => k >= 718
  have h_m_mono_504 : m*(m+1)/2 ≤ 87153 := m_mono m 417 h_m_504
  have h_pc_M_504 : Nat.primeCounting 87153 = 8464 := pc_thm_87153
  have h_pc_K_prev_504 : Nat.primeCounting 514806 = 42658 := pc_thm_514806
  have h_k_505 : k ≥ 718 := staircase_step_K_direct k m 51156 87153 514806 8464 42658 718 heq h_m_mono_504 h_pc_M_504 h_pc_K_prev_504 rfl (by decide)
  have h_pc_K_next_504 : Nat.primeCounting 516242 = 42758 := pc_thm_516242
  have h_pc_M_next_val_504 : Nat.primeCounting 86736 = 8429 := pc_thm_86736
  have h_m_505 : m ≤ 415 := staircase_step_M_direct k m 51156 516242 86736 42758 8429 415 heq (k_mono 718 k h_k_505) h_pc_K_next_504 h_pc_M_next_val_504 rfl (by decide)
  -- Step 505: k >= 718, m <= 415 => k >= 719
  have h_m_mono_505 : m*(m+1)/2 ≤ 86320 := m_mono m 415 h_m_505
  have h_pc_M_505 : Nat.primeCounting 86320 = 8393 := pc_thm_86320
  have h_pc_K_prev_505 : Nat.primeCounting 516242 = 42758 := pc_thm_516242
  have h_k_506 : k ≥ 719 := staircase_step_K_direct k m 51156 86320 516242 8393 42758 719 heq h_m_mono_505 h_pc_M_505 h_pc_K_prev_505 rfl (by decide)
  have h_pc_K_next_505 : Nat.primeCounting 517680 = 42885 := pc_thm_517680
  have h_pc_M_next_val_505 : Nat.primeCounting 85078 = 8283 := pc_thm_85078
  have h_m_506 : m ≤ 411 := staircase_step_M_direct k m 51156 517680 85078 42885 8283 411 heq (k_mono 719 k h_k_506) h_pc_K_next_505 h_pc_M_next_val_505 rfl (by decide)
  -- Step 506: k >= 719, m <= 411 => k >= 720
  have h_m_mono_506 : m*(m+1)/2 ≤ 84666 := m_mono m 411 h_m_506
  have h_pc_M_506 : Nat.primeCounting 84666 = 8250 := pc_thm_84666
  have h_pc_K_prev_506 : Nat.primeCounting 517680 = 42885 := pc_thm_517680
  have h_k_507 : k ≥ 720 := staircase_step_K_direct k m 51156 84666 517680 8250 42885 720 heq h_m_mono_506 h_pc_M_506 h_pc_K_prev_506 rfl (by decide)
  have h_pc_K_next_506 : Nat.primeCounting 519120 = 42993 := pc_thm_519120
  have h_pc_M_next_val_506 : Nat.primeCounting 83845 = 8178 := pc_thm_83845
  have h_m_507 : m ≤ 408 := staircase_step_M_direct k m 51156 519120 83845 42993 8178 408 heq (k_mono 720 k h_k_507) h_pc_K_next_506 h_pc_M_next_val_506 rfl (by decide)
  -- Step 507: k >= 720, m <= 408 => k >= 721
  have h_m_mono_507 : m*(m+1)/2 ≤ 83436 := m_mono m 408 h_m_507
  have h_pc_M_507 : Nat.primeCounting 83436 = 8145 := pc_thm_83436
  have h_pc_K_prev_507 : Nat.primeCounting 519120 = 42993 := pc_thm_519120
  have h_k_508 : k ≥ 721 := staircase_step_K_direct k m 51156 83436 519120 8145 42993 721 heq h_m_mono_507 h_pc_M_507 h_pc_K_prev_507 rfl (by decide)
  have h_pc_K_next_507 : Nat.primeCounting 520562 = 43101 := pc_thm_520562
  have h_pc_M_next_val_507 : Nat.primeCounting 82621 = 8078 := pc_thm_82621
  have h_m_508 : m ≤ 405 := staircase_step_M_direct k m 51156 520562 82621 43101 8078 405 heq (k_mono 721 k h_k_508) h_pc_K_next_507 h_pc_M_next_val_507 rfl (by decide)
  -- Step 508: k >= 721, m <= 405 => k >= 722
  have h_m_mono_508 : m*(m+1)/2 ≤ 82215 := m_mono m 405 h_m_508
  have h_pc_M_508 : Nat.primeCounting 82215 = 8038 := pc_thm_82215
  have h_pc_K_prev_508 : Nat.primeCounting 520562 = 43101 := pc_thm_520562
  have h_k_509 : k ≥ 722 := staircase_step_K_direct k m 51156 82215 520562 8038 43101 722 heq h_m_mono_508 h_pc_M_508 h_pc_K_prev_508 rfl (by decide)
  have h_pc_K_next_508 : Nat.primeCounting 522006 = 43217 := pc_thm_522006
  have h_pc_M_next_val_508 : Nat.primeCounting 81406 = 7965 := pc_thm_81406
  have h_m_509 : m ≤ 402 := staircase_step_M_direct k m 51156 522006 81406 43217 7965 402 heq (k_mono 722 k h_k_509) h_pc_K_next_508 h_pc_M_next_val_508 rfl (by decide)
  -- Step 509: k >= 722, m <= 402 => k >= 723
  have h_m_mono_509 : m*(m+1)/2 ≤ 81003 := m_mono m 402 h_m_509
  have h_pc_M_509 : Nat.primeCounting 81003 = 7926 := pc_thm_81003
  have h_pc_K_prev_509 : Nat.primeCounting 522006 = 43217 := pc_thm_522006
  have h_k_510 : k ≥ 723 := staircase_step_K_direct k m 51156 81003 522006 7926 43217 723 heq h_m_mono_509 h_pc_M_509 h_pc_K_prev_509 rfl (by decide)
  have h_pc_K_next_509 : Nat.primeCounting 523452 = 43321 := pc_thm_523452
  have h_pc_M_next_val_509 : Nat.primeCounting 80200 = 7852 := pc_thm_80200
  have h_m_510 : m ≤ 399 := staircase_step_M_direct k m 51156 523452 80200 43321 7852 399 heq (k_mono 723 k h_k_510) h_pc_K_next_509 h_pc_M_next_val_509 rfl (by decide)
  -- Step 510: k >= 723, m <= 399 => k >= 724
  have h_m_mono_510 : m*(m+1)/2 ≤ 79800 := m_mono m 399 h_m_510
  have h_pc_M_510 : Nat.primeCounting 79800 = 7813 := pc_thm_79800
  have h_pc_K_prev_510 : Nat.primeCounting 523452 = 43321 := pc_thm_523452
  have h_k_511 : k ≥ 724 := staircase_step_K_direct k m 51156 79800 523452 7813 43321 724 heq h_m_mono_510 h_pc_M_510 h_pc_K_prev_510 rfl (by decide)
  have h_pc_K_next_510 : Nat.primeCounting 524900 = 43429 := pc_thm_524900
  have h_pc_M_next_val_510 : Nat.primeCounting 79003 = 7746 := pc_thm_79003
  have h_m_511 : m ≤ 396 := staircase_step_M_direct k m 51156 524900 79003 43429 7746 396 heq (k_mono 724 k h_k_511) h_pc_K_next_510 h_pc_M_next_val_510 rfl (by decide)
  exact ⟨h_k_511, h_m_511⟩

theorem staircase_part_34 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_511 : k ≥ 724) (h_m_511 : m ≤ 396) : k ≥ 739 ∧ m ≤ 346 := by
  -- Step 511: k >= 724, m <= 396 => k >= 725
  have h_m_mono_511 : m*(m+1)/2 ≤ 78606 := m_mono m 396 h_m_511
  have h_pc_M_511 : Nat.primeCounting 78606 = 7713 := pc_thm_78606
  have h_pc_K_prev_511 : Nat.primeCounting 524900 = 43429 := pc_thm_524900
  have h_k_512 : k ≥ 725 := staircase_step_K_direct k m 51156 78606 524900 7713 43429 725 heq h_m_mono_511 h_pc_M_511 h_pc_K_prev_511 rfl (by decide)
  have h_pc_K_next_511 : Nat.primeCounting 526350 = 43548 := pc_thm_526350
  have h_pc_M_next_val_511 : Nat.primeCounting 77815 = 7649 := pc_thm_77815
  have h_m_512 : m ≤ 393 := staircase_step_M_direct k m 51156 526350 77815 43548 7649 393 heq (k_mono 725 k h_k_512) h_pc_K_next_511 h_pc_M_next_val_511 rfl (by decide)
  -- Step 512: k >= 725, m <= 393 => k >= 726
  have h_m_mono_512 : m*(m+1)/2 ≤ 77421 := m_mono m 393 h_m_512
  have h_pc_M_512 : Nat.primeCounting 77421 = 7606 := pc_thm_77421
  have h_pc_K_prev_512 : Nat.primeCounting 526350 = 43548 := pc_thm_526350
  have h_k_513 : k ≥ 726 := staircase_step_K_direct k m 51156 77421 526350 7606 43548 726 heq h_m_mono_512 h_pc_M_512 h_pc_K_prev_512 rfl (by decide)
  have h_pc_K_next_512 : Nat.primeCounting 527802 = 43661 := pc_thm_527802
  have h_pc_M_next_val_512 : Nat.primeCounting 76245 = 7503 := pc_thm_76245
  have h_m_513 : m ≤ 389 := staircase_step_M_direct k m 51156 527802 76245 43661 7503 389 heq (k_mono 726 k h_k_513) h_pc_K_next_512 h_pc_M_next_val_512 rfl (by decide)
  -- Step 513: k >= 726, m <= 389 => k >= 727
  have h_m_mono_513 : m*(m+1)/2 ≤ 75855 := m_mono m 389 h_m_513
  have h_pc_M_513 : Nat.primeCounting 75855 = 7472 := pc_thm_75855
  have h_pc_K_prev_513 : Nat.primeCounting 527802 = 43661 := pc_thm_527802
  have h_k_514 : k ≥ 727 := staircase_step_K_direct k m 51156 75855 527802 7472 43661 727 heq h_m_mono_513 h_pc_M_513 h_pc_K_prev_513 rfl (by decide)
  have h_pc_K_next_513 : Nat.primeCounting 529256 = 43769 := pc_thm_529256
  have h_pc_M_next_val_513 : Nat.primeCounting 75078 = 7399 := pc_thm_75078
  have h_m_514 : m ≤ 386 := staircase_step_M_direct k m 51156 529256 75078 43769 7399 386 heq (k_mono 727 k h_k_514) h_pc_K_next_513 h_pc_M_next_val_513 rfl (by decide)
  -- Step 514: k >= 727, m <= 386 => k >= 728
  have h_m_mono_514 : m*(m+1)/2 ≤ 74691 := m_mono m 386 h_m_514
  have h_pc_M_514 : Nat.primeCounting 74691 = 7363 := pc_thm_74691
  have h_pc_K_prev_514 : Nat.primeCounting 529256 = 43769 := pc_thm_529256
  have h_k_515 : k ≥ 728 := staircase_step_K_direct k m 51156 74691 529256 7363 43769 728 heq h_m_mono_514 h_pc_M_514 h_pc_K_prev_514 rfl (by decide)
  have h_pc_K_next_514 : Nat.primeCounting 530712 = 43882 := pc_thm_530712
  have h_pc_M_next_val_514 : Nat.primeCounting 73920 = 7295 := pc_thm_73920
  have h_m_515 : m ≤ 383 := staircase_step_M_direct k m 51156 530712 73920 43882 7295 383 heq (k_mono 728 k h_k_515) h_pc_K_next_514 h_pc_M_next_val_514 rfl (by decide)
  -- Step 515: k >= 728, m <= 383 => k >= 729
  have h_m_mono_515 : m*(m+1)/2 ≤ 73536 := m_mono m 383 h_m_515
  have h_pc_M_515 : Nat.primeCounting 73536 = 7260 := pc_thm_73536
  have h_pc_K_prev_515 : Nat.primeCounting 530712 = 43882 := pc_thm_530712
  have h_k_516 : k ≥ 729 := staircase_step_K_direct k m 51156 73536 530712 7260 43882 729 heq h_m_mono_515 h_pc_M_515 h_pc_K_prev_515 rfl (by decide)
  have h_pc_K_next_515 : Nat.primeCounting 532170 = 43985 := pc_thm_532170
  have h_pc_M_next_val_515 : Nat.primeCounting 72771 = 7197 := pc_thm_72771
  have h_m_516 : m ≤ 380 := staircase_step_M_direct k m 51156 532170 72771 43985 7197 380 heq (k_mono 729 k h_k_516) h_pc_K_next_515 h_pc_M_next_val_515 rfl (by decide)
  -- Step 516: k >= 729, m <= 380 => k >= 730
  have h_m_mono_516 : m*(m+1)/2 ≤ 72390 := m_mono m 380 h_m_516
  have h_pc_M_516 : Nat.primeCounting 72390 = 7164 := pc_thm_72390
  have h_pc_K_prev_516 : Nat.primeCounting 532170 = 43985 := pc_thm_532170
  have h_k_517 : k ≥ 730 := staircase_step_K_direct k m 51156 72390 532170 7164 43985 730 heq h_m_mono_516 h_pc_M_516 h_pc_K_prev_516 rfl (by decide)
  have h_pc_K_next_516 : Nat.primeCounting 533630 = 44096 := pc_thm_533630
  have h_pc_M_next_val_516 : Nat.primeCounting 71631 = 7091 := pc_thm_71631
  have h_m_517 : m ≤ 377 := staircase_step_M_direct k m 51156 533630 71631 44096 7091 377 heq (k_mono 730 k h_k_517) h_pc_K_next_516 h_pc_M_next_val_516 rfl (by decide)
  -- Step 517: k >= 730, m <= 377 => k >= 731
  have h_m_mono_517 : m*(m+1)/2 ≤ 71253 := m_mono m 377 h_m_517
  have h_pc_M_517 : Nat.primeCounting 71253 = 7053 := pc_thm_71253
  have h_pc_K_prev_517 : Nat.primeCounting 533630 = 44096 := pc_thm_533630
  have h_k_518 : k ≥ 731 := staircase_step_K_direct k m 51156 71253 533630 7053 44096 731 heq h_m_mono_517 h_pc_M_517 h_pc_K_prev_517 rfl (by decide)
  have h_pc_K_next_517 : Nat.primeCounting 535092 = 44203 := pc_thm_535092
  have h_pc_M_next_val_517 : Nat.primeCounting 70500 = 6985 := pc_thm_70500
  have h_m_518 : m ≤ 374 := staircase_step_M_direct k m 51156 535092 70500 44203 6985 374 heq (k_mono 731 k h_k_518) h_pc_K_next_517 h_pc_M_next_val_517 rfl (by decide)
  -- Step 518: k >= 731, m <= 374 => k >= 732
  have h_m_mono_518 : m*(m+1)/2 ≤ 70125 := m_mono m 374 h_m_518
  have h_pc_M_518 : Nat.primeCounting 70125 = 6949 := pc_thm_70125
  have h_pc_K_prev_518 : Nat.primeCounting 535092 = 44203 := pc_thm_535092
  have h_k_519 : k ≥ 732 := staircase_step_K_direct k m 51156 70125 535092 6949 44203 732 heq h_m_mono_518 h_pc_M_518 h_pc_K_prev_518 rfl (by decide)
  have h_pc_K_next_518 : Nat.primeCounting 536556 = 44317 := pc_thm_536556
  have h_pc_M_next_val_518 : Nat.primeCounting 69006 = 6855 := pc_thm_69006
  have h_m_519 : m ≤ 370 := staircase_step_M_direct k m 51156 536556 69006 44317 6855 370 heq (k_mono 732 k h_k_519) h_pc_K_next_518 h_pc_M_next_val_518 rfl (by decide)
  -- Step 519: k >= 732, m <= 370 => k >= 733
  have h_m_mono_519 : m*(m+1)/2 ≤ 68635 := m_mono m 370 h_m_519
  have h_pc_M_519 : Nat.primeCounting 68635 = 6822 := pc_thm_68635
  have h_pc_K_prev_519 : Nat.primeCounting 536556 = 44317 := pc_thm_536556
  have h_k_520 : k ≥ 733 := staircase_step_K_direct k m 51156 68635 536556 6822 44317 733 heq h_m_mono_519 h_pc_M_519 h_pc_K_prev_519 rfl (by decide)
  have h_pc_K_next_519 : Nat.primeCounting 538022 = 44425 := pc_thm_538022
  have h_pc_M_next_val_519 : Nat.primeCounting 67896 = 6762 := pc_thm_67896
  have h_m_520 : m ≤ 367 := staircase_step_M_direct k m 51156 538022 67896 44425 6762 367 heq (k_mono 733 k h_k_520) h_pc_K_next_519 h_pc_M_next_val_519 rfl (by decide)
  -- Step 520: k >= 733, m <= 367 => k >= 734
  have h_m_mono_520 : m*(m+1)/2 ≤ 67528 := m_mono m 367 h_m_520
  have h_pc_M_520 : Nat.primeCounting 67528 = 6727 := pc_thm_67528
  have h_pc_K_prev_520 : Nat.primeCounting 538022 = 44425 := pc_thm_538022
  have h_k_521 : k ≥ 734 := staircase_step_K_direct k m 51156 67528 538022 6727 44425 734 heq h_m_mono_520 h_pc_M_520 h_pc_K_prev_520 rfl (by decide)
  have h_pc_K_next_520 : Nat.primeCounting 539490 = 44538 := pc_thm_539490
  have h_pc_M_next_val_520 : Nat.primeCounting 66430 = 6623 := pc_thm_66430
  have h_m_521 : m ≤ 363 := staircase_step_M_direct k m 51156 539490 66430 44538 6623 363 heq (k_mono 734 k h_k_521) h_pc_K_next_520 h_pc_M_next_val_520 rfl (by decide)
  -- Step 521: k >= 734, m <= 363 => k >= 735
  have h_m_mono_521 : m*(m+1)/2 ≤ 66066 := m_mono m 363 h_m_521
  have h_pc_M_521 : Nat.primeCounting 66066 = 6595 := pc_thm_66066
  have h_pc_K_prev_521 : Nat.primeCounting 539490 = 44538 := pc_thm_539490
  have h_k_522 : k ≥ 735 := staircase_step_K_direct k m 51156 66066 539490 6595 44538 735 heq h_m_mono_521 h_pc_M_521 h_pc_K_prev_521 rfl (by decide)
  have h_pc_K_next_521 : Nat.primeCounting 540960 = 44643 := pc_thm_540960
  have h_pc_M_next_val_521 : Nat.primeCounting 65341 = 6526 := pc_thm_65341
  have h_m_522 : m ≤ 360 := staircase_step_M_direct k m 51156 540960 65341 44643 6526 360 heq (k_mono 735 k h_k_522) h_pc_K_next_521 h_pc_M_next_val_521 rfl (by decide)
  -- Step 522: k >= 735, m <= 360 => k >= 736
  have h_m_mono_522 : m*(m+1)/2 ≤ 64980 := m_mono m 360 h_m_522
  have h_pc_M_522 : Nat.primeCounting 64980 = 6492 := pc_thm_64980
  have h_pc_K_prev_522 : Nat.primeCounting 540960 = 44643 := pc_thm_540960
  have h_k_523 : k ≥ 736 := staircase_step_K_direct k m 51156 64980 540960 6492 44643 736 heq h_m_mono_522 h_pc_M_522 h_pc_K_prev_522 rfl (by decide)
  have h_pc_K_next_522 : Nat.primeCounting 542432 = 44755 := pc_thm_542432
  have h_pc_M_next_val_522 : Nat.primeCounting 63903 = 6407 := pc_thm_63903
  have h_m_523 : m ≤ 356 := staircase_step_M_direct k m 51156 542432 63903 44755 6407 356 heq (k_mono 736 k h_k_523) h_pc_K_next_522 h_pc_M_next_val_522 rfl (by decide)
  -- Step 523: k >= 736, m <= 356 => k >= 737
  have h_m_mono_523 : m*(m+1)/2 ≤ 63546 := m_mono m 356 h_m_523
  have h_pc_M_523 : Nat.primeCounting 63546 = 6369 := pc_thm_63546
  have h_pc_K_prev_523 : Nat.primeCounting 542432 = 44755 := pc_thm_542432
  have h_k_524 : k ≥ 737 := staircase_step_K_direct k m 51156 63546 542432 6369 44755 737 heq h_m_mono_523 h_pc_M_523 h_pc_K_prev_523 rfl (by decide)
  have h_pc_K_next_523 : Nat.primeCounting 543906 = 44876 := pc_thm_543906
  have h_pc_M_next_val_523 : Nat.primeCounting 62835 = 6304 := pc_thm_62835
  have h_m_524 : m ≤ 353 := staircase_step_M_direct k m 51156 543906 62835 44876 6304 353 heq (k_mono 737 k h_k_524) h_pc_K_next_523 h_pc_M_next_val_523 rfl (by decide)
  -- Step 524: k >= 737, m <= 353 => k >= 738
  have h_m_mono_524 : m*(m+1)/2 ≤ 62481 := m_mono m 353 h_m_524
  have h_pc_M_524 : Nat.primeCounting 62481 = 6273 := pc_thm_62481
  have h_pc_K_prev_524 : Nat.primeCounting 543906 = 44876 := pc_thm_543906
  have h_k_525 : k ≥ 738 := staircase_step_K_direct k m 51156 62481 543906 6273 44876 738 heq h_m_mono_524 h_pc_M_524 h_pc_K_prev_524 rfl (by decide)
  have h_pc_K_next_524 : Nat.primeCounting 545382 = 44972 := pc_thm_545382
  have h_pc_M_next_val_524 : Nat.primeCounting 61776 = 6214 := pc_thm_61776
  have h_m_525 : m ≤ 350 := staircase_step_M_direct k m 51156 545382 61776 44972 6214 350 heq (k_mono 738 k h_k_525) h_pc_K_next_524 h_pc_M_next_val_524 rfl (by decide)
  -- Step 525: k >= 738, m <= 350 => k >= 739
  have h_m_mono_525 : m*(m+1)/2 ≤ 61425 := m_mono m 350 h_m_525
  have h_pc_M_525 : Nat.primeCounting 61425 = 6179 := pc_thm_61425
  have h_pc_K_prev_525 : Nat.primeCounting 545382 = 44972 := pc_thm_545382
  have h_k_526 : k ≥ 739 := staircase_step_K_direct k m 51156 61425 545382 6179 44972 739 heq h_m_mono_525 h_pc_M_525 h_pc_K_prev_525 rfl (by decide)
  have h_pc_K_next_525 : Nat.primeCounting 546860 = 45080 := pc_thm_546860
  have h_pc_M_next_val_525 : Nat.primeCounting 60378 = 6091 := pc_thm_60378
  have h_m_526 : m ≤ 346 := staircase_step_M_direct k m 51156 546860 60378 45080 6091 346 heq (k_mono 739 k h_k_526) h_pc_K_next_525 h_pc_M_next_val_525 rfl (by decide)
  exact ⟨h_k_526, h_m_526⟩

theorem staircase_part_35 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_526 : k ≥ 739) (h_m_526 : m ≤ 346) : k ≥ 754 ∧ m ≤ 289 := by
  -- Step 526: k >= 739, m <= 346 => k >= 740
  have h_m_mono_526 : m*(m+1)/2 ≤ 60031 := m_mono m 346 h_m_526
  have h_pc_M_526 : Nat.primeCounting 60031 = 6060 := pc_thm_60031
  have h_pc_K_prev_526 : Nat.primeCounting 546860 = 45080 := pc_thm_546860
  have h_k_527 : k ≥ 740 := staircase_step_K_direct k m 51156 60031 546860 6060 45080 740 heq h_m_mono_526 h_pc_M_526 h_pc_K_prev_526 rfl (by decide)
  have h_pc_K_next_526 : Nat.primeCounting 548340 = 45189 := pc_thm_548340
  have h_pc_M_next_val_526 : Nat.primeCounting 59340 = 5996 := pc_thm_59340
  have h_m_527 : m ≤ 343 := staircase_step_M_direct k m 51156 548340 59340 45189 5996 343 heq (k_mono 740 k h_k_527) h_pc_K_next_526 h_pc_M_next_val_526 rfl (by decide)
  -- Step 527: k >= 740, m <= 343 => k >= 741
  have h_m_mono_527 : m*(m+1)/2 ≤ 58996 := m_mono m 343 h_m_527
  have h_pc_M_527 : Nat.primeCounting 58996 = 5962 := pc_thm_58996
  have h_pc_K_prev_527 : Nat.primeCounting 548340 = 45189 := pc_thm_548340
  have h_k_528 : k ≥ 741 := staircase_step_K_direct k m 51156 58996 548340 5962 45189 741 heq h_m_mono_527 h_pc_M_527 h_pc_K_prev_527 rfl (by decide)
  have h_pc_K_next_527 : Nat.primeCounting 549822 = 45311 := pc_thm_549822
  have h_pc_M_next_val_527 : Nat.primeCounting 57970 = 5870 := pc_thm_57970
  have h_m_528 : m ≤ 339 := staircase_step_M_direct k m 51156 549822 57970 45311 5870 339 heq (k_mono 741 k h_k_528) h_pc_K_next_527 h_pc_M_next_val_527 rfl (by decide)
  -- Step 528: k >= 741, m <= 339 => k >= 742
  have h_m_mono_528 : m*(m+1)/2 ≤ 57630 := m_mono m 339 h_m_528
  have h_pc_M_528 : Nat.primeCounting 57630 = 5836 := pc_thm_57630
  have h_pc_K_prev_528 : Nat.primeCounting 549822 = 45311 := pc_thm_549822
  have h_k_529 : k ≥ 742 := staircase_step_K_direct k m 51156 57630 549822 5836 45311 742 heq h_m_mono_528 h_pc_M_528 h_pc_K_prev_528 rfl (by decide)
  have h_pc_K_next_528 : Nat.primeCounting 551306 = 45423 := pc_thm_551306
  have h_pc_M_next_val_528 : Nat.primeCounting 56616 = 5741 := pc_thm_56616
  have h_m_529 : m ≤ 335 := staircase_step_M_direct k m 51156 551306 56616 45423 5741 335 heq (k_mono 742 k h_k_529) h_pc_K_next_528 h_pc_M_next_val_528 rfl (by decide)
  -- Step 529: k >= 742, m <= 335 => k >= 743
  have h_m_mono_529 : m*(m+1)/2 ≤ 56280 := m_mono m 335 h_m_529
  have h_pc_M_529 : Nat.primeCounting 56280 = 5709 := pc_thm_56280
  have h_pc_K_prev_529 : Nat.primeCounting 551306 = 45423 := pc_thm_551306
  have h_k_530 : k ≥ 743 := staircase_step_K_direct k m 51156 56280 551306 5709 45423 743 heq h_m_mono_529 h_pc_M_529 h_pc_K_prev_529 rfl (by decide)
  have h_pc_K_next_529 : Nat.primeCounting 552792 = 45532 := pc_thm_552792
  have h_pc_M_next_val_529 : Nat.primeCounting 55611 = 5641 := pc_thm_55611
  have h_m_530 : m ≤ 332 := staircase_step_M_direct k m 51156 552792 55611 45532 5641 332 heq (k_mono 743 k h_k_530) h_pc_K_next_529 h_pc_M_next_val_529 rfl (by decide)
  -- Step 530: k >= 743, m <= 332 => k >= 744
  have h_m_mono_530 : m*(m+1)/2 ≤ 55278 := m_mono m 332 h_m_530
  have h_pc_M_530 : Nat.primeCounting 55278 = 5615 := pc_thm_55278
  have h_pc_K_prev_530 : Nat.primeCounting 552792 = 45532 := pc_thm_552792
  have h_k_531 : k ≥ 744 := staircase_step_K_direct k m 51156 55278 552792 5615 45532 744 heq h_m_mono_530 h_pc_M_530 h_pc_K_prev_530 rfl (by decide)
  have h_pc_K_next_530 : Nat.primeCounting 554280 = 45648 := pc_thm_554280
  have h_pc_M_next_val_530 : Nat.primeCounting 54285 = 5521 := pc_thm_54285
  have h_m_531 : m ≤ 328 := staircase_step_M_direct k m 51156 554280 54285 45648 5521 328 heq (k_mono 744 k h_k_531) h_pc_K_next_530 h_pc_M_next_val_530 rfl (by decide)
  -- Step 531: k >= 744, m <= 328 => k >= 745
  have h_m_mono_531 : m*(m+1)/2 ≤ 53956 := m_mono m 328 h_m_531
  have h_pc_M_531 : Nat.primeCounting 53956 = 5497 := pc_thm_53956
  have h_pc_K_prev_531 : Nat.primeCounting 554280 = 45648 := pc_thm_554280
  have h_k_532 : k ≥ 745 := staircase_step_K_direct k m 51156 53956 554280 5497 45648 745 heq h_m_mono_531 h_pc_M_531 h_pc_K_prev_531 rfl (by decide)
  have h_pc_K_next_531 : Nat.primeCounting 555770 = 45755 := pc_thm_555770
  have h_pc_M_next_val_531 : Nat.primeCounting 52975 = 5406 := pc_thm_52975
  have h_m_532 : m ≤ 324 := staircase_step_M_direct k m 51156 555770 52975 45755 5406 324 heq (k_mono 745 k h_k_532) h_pc_K_next_531 h_pc_M_next_val_531 rfl (by decide)
  -- Step 532: k >= 745, m <= 324 => k >= 746
  have h_m_mono_532 : m*(m+1)/2 ≤ 52650 := m_mono m 324 h_m_532
  have h_pc_M_532 : Nat.primeCounting 52650 = 5375 := pc_thm_52650
  have h_pc_K_prev_532 : Nat.primeCounting 555770 = 45755 := pc_thm_555770
  have h_k_533 : k ≥ 746 := staircase_step_K_direct k m 51156 52650 555770 5375 45755 746 heq h_m_mono_532 h_pc_M_532 h_pc_K_prev_532 rfl (by decide)
  have h_pc_K_next_532 : Nat.primeCounting 557262 = 45868 := pc_thm_557262
  have h_pc_M_next_val_532 : Nat.primeCounting 51681 = 5289 := pc_thm_51681
  have h_m_533 : m ≤ 320 := staircase_step_M_direct k m 51156 557262 51681 45868 5289 320 heq (k_mono 746 k h_k_533) h_pc_K_next_532 h_pc_M_next_val_532 rfl (by decide)
  -- Step 533: k >= 746, m <= 320 => k >= 747
  have h_m_mono_533 : m*(m+1)/2 ≤ 51360 := m_mono m 320 h_m_533
  have h_pc_M_533 : Nat.primeCounting 51360 = 5254 := pc_thm_51360
  have h_pc_K_prev_533 : Nat.primeCounting 557262 = 45868 := pc_thm_557262
  have h_k_534 : k ≥ 747 := staircase_step_K_direct k m 51156 51360 557262 5254 45868 747 heq h_m_mono_533 h_pc_M_533 h_pc_K_prev_533 rfl (by decide)
  have h_pc_K_next_533 : Nat.primeCounting 558756 = 45976 := pc_thm_558756
  have h_pc_M_next_val_533 : Nat.primeCounting 50721 = 5197 := pc_thm_50721
  have h_m_534 : m ≤ 317 := staircase_step_M_direct k m 51156 558756 50721 45976 5197 317 heq (k_mono 747 k h_k_534) h_pc_K_next_533 h_pc_M_next_val_533 rfl (by decide)
  -- Step 534: k >= 747, m <= 317 => k >= 748
  have h_m_mono_534 : m*(m+1)/2 ≤ 50403 := m_mono m 317 h_m_534
  have h_pc_M_534 : Nat.primeCounting 50403 = 5172 := pc_thm_50403
  have h_pc_K_prev_534 : Nat.primeCounting 558756 = 45976 := pc_thm_558756
  have h_k_535 : k ≥ 748 := staircase_step_K_direct k m 51156 50403 558756 5172 45976 748 heq h_m_mono_534 h_pc_M_534 h_pc_K_prev_534 rfl (by decide)
  have h_pc_K_next_534 : Nat.primeCounting 560252 = 46101 := pc_thm_560252
  have h_pc_M_next_val_534 : Nat.primeCounting 49455 = 5081 := pc_thm_49455
  have h_m_535 : m ≤ 313 := staircase_step_M_direct k m 51156 560252 49455 46101 5081 313 heq (k_mono 748 k h_k_535) h_pc_K_next_534 h_pc_M_next_val_534 rfl (by decide)
  -- Step 535: k >= 748, m <= 313 => k >= 749
  have h_m_mono_535 : m*(m+1)/2 ≤ 49141 := m_mono m 313 h_m_535
  have h_pc_M_535 : Nat.primeCounting 49141 = 5051 := pc_thm_49141
  have h_pc_K_prev_535 : Nat.primeCounting 560252 = 46101 := pc_thm_560252
  have h_k_536 : k ≥ 749 := staircase_step_K_direct k m 51156 49141 560252 5051 46101 749 heq h_m_mono_535 h_pc_M_535 h_pc_K_prev_535 rfl (by decide)
  have h_pc_K_next_535 : Nat.primeCounting 561750 = 46202 := pc_thm_561750
  have h_pc_M_next_val_535 : Nat.primeCounting 48205 = 4963 := pc_thm_48205
  have h_m_536 : m ≤ 309 := staircase_step_M_direct k m 51156 561750 48205 46202 4963 309 heq (k_mono 749 k h_k_536) h_pc_K_next_535 h_pc_M_next_val_535 rfl (by decide)
  -- Step 536: k >= 749, m <= 309 => k >= 750
  have h_m_mono_536 : m*(m+1)/2 ≤ 47895 := m_mono m 309 h_m_536
  have h_pc_M_536 : Nat.primeCounting 47895 = 4935 := pc_thm_47895
  have h_pc_K_prev_536 : Nat.primeCounting 561750 = 46202 := pc_thm_561750
  have h_k_537 : k ≥ 750 := staircase_step_K_direct k m 51156 47895 561750 4935 46202 750 heq h_m_mono_536 h_pc_M_536 h_pc_K_prev_536 rfl (by decide)
  have h_pc_K_next_536 : Nat.primeCounting 563250 = 46322 := pc_thm_563250
  have h_pc_M_next_val_536 : Nat.primeCounting 46971 = 4849 := pc_thm_46971
  have h_m_537 : m ≤ 305 := staircase_step_M_direct k m 51156 563250 46971 46322 4849 305 heq (k_mono 750 k h_k_537) h_pc_K_next_536 h_pc_M_next_val_536 rfl (by decide)
  -- Step 537: k >= 750, m <= 305 => k >= 751
  have h_m_mono_537 : m*(m+1)/2 ≤ 46665 := m_mono m 305 h_m_537
  have h_pc_M_537 : Nat.primeCounting 46665 = 4822 := pc_thm_46665
  have h_pc_K_prev_537 : Nat.primeCounting 563250 = 46322 := pc_thm_563250
  have h_k_538 : k ≥ 751 := staircase_step_K_direct k m 51156 46665 563250 4822 46322 751 heq h_m_mono_537 h_pc_M_537 h_pc_K_prev_537 rfl (by decide)
  have h_pc_K_next_537 : Nat.primeCounting 564752 = 46428 := pc_thm_564752
  have h_pc_M_next_val_537 : Nat.primeCounting 45753 = 4739 := pc_thm_45753
  have h_m_538 : m ≤ 301 := staircase_step_M_direct k m 51156 564752 45753 46428 4739 301 heq (k_mono 751 k h_k_538) h_pc_K_next_537 h_pc_M_next_val_537 rfl (by decide)
  -- Step 538: k >= 751, m <= 301 => k >= 752
  have h_m_mono_538 : m*(m+1)/2 ≤ 45451 := m_mono m 301 h_m_538
  have h_pc_M_538 : Nat.primeCounting 45451 = 4714 := pc_thm_45451
  have h_pc_K_prev_538 : Nat.primeCounting 564752 = 46428 := pc_thm_564752
  have h_k_539 : k ≥ 752 := staircase_step_K_direct k m 51156 45451 564752 4714 46428 752 heq h_m_mono_538 h_pc_M_538 h_pc_K_prev_538 rfl (by decide)
  have h_pc_K_next_538 : Nat.primeCounting 566256 = 46543 := pc_thm_566256
  have h_pc_M_next_val_538 : Nat.primeCounting 44551 = 4632 := pc_thm_44551
  have h_m_539 : m ≤ 297 := staircase_step_M_direct k m 51156 566256 44551 46543 4632 297 heq (k_mono 752 k h_k_539) h_pc_K_next_538 h_pc_M_next_val_538 rfl (by decide)
  -- Step 539: k >= 752, m <= 297 => k >= 753
  have h_m_mono_539 : m*(m+1)/2 ≤ 44253 := m_mono m 297 h_m_539
  have h_pc_M_539 : Nat.primeCounting 44253 = 4604 := pc_thm_44253
  have h_pc_K_prev_539 : Nat.primeCounting 566256 = 46543 := pc_thm_566256
  have h_k_540 : k ≥ 753 := staircase_step_K_direct k m 51156 44253 566256 4604 46543 753 heq h_m_mono_539 h_pc_M_539 h_pc_K_prev_539 rfl (by decide)
  have h_pc_K_next_539 : Nat.primeCounting 567762 = 46647 := pc_thm_567762
  have h_pc_M_next_val_539 : Nat.primeCounting 43365 = 4522 := pc_thm_43365
  have h_m_540 : m ≤ 293 := staircase_step_M_direct k m 51156 567762 43365 46647 4522 293 heq (k_mono 753 k h_k_540) h_pc_K_next_539 h_pc_M_next_val_539 rfl (by decide)
  -- Step 540: k >= 753, m <= 293 => k >= 754
  have h_m_mono_540 : m*(m+1)/2 ≤ 43071 := m_mono m 293 h_m_540
  have h_pc_M_540 : Nat.primeCounting 43071 = 4502 := pc_thm_43071
  have h_pc_K_prev_540 : Nat.primeCounting 567762 = 46647 := pc_thm_567762
  have h_k_541 : k ≥ 754 := staircase_step_K_direct k m 51156 43071 567762 4502 46647 754 heq h_m_mono_540 h_pc_M_540 h_pc_K_prev_540 rfl (by decide)
  have h_pc_K_next_540 : Nat.primeCounting 569270 = 46767 := pc_thm_569270
  have h_pc_M_next_val_540 : Nat.primeCounting 42195 = 4411 := pc_thm_42195
  have h_m_541 : m ≤ 289 := staircase_step_M_direct k m 51156 569270 42195 46767 4411 289 heq (k_mono 754 k h_k_541) h_pc_K_next_540 h_pc_M_next_val_540 rfl (by decide)
  exact ⟨h_k_541, h_m_541⟩

theorem staircase_part_36 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_541 : k ≥ 754) (h_m_541 : m ≤ 289) : k ≥ 769 ∧ m ≤ 218 := by
  -- Step 541: k >= 754, m <= 289 => k >= 755
  have h_m_mono_541 : m*(m+1)/2 ≤ 41905 := m_mono m 289 h_m_541
  have h_pc_M_541 : Nat.primeCounting 41905 = 4381 := pc_thm_41905
  have h_pc_K_prev_541 : Nat.primeCounting 569270 = 46767 := pc_thm_569270
  have h_k_542 : k ≥ 755 := staircase_step_K_direct k m 51156 41905 569270 4381 46767 755 heq h_m_mono_541 h_pc_M_541 h_pc_K_prev_541 rfl (by decide)
  have h_pc_K_next_541 : Nat.primeCounting 570780 = 46886 := pc_thm_570780
  have h_pc_M_next_val_541 : Nat.primeCounting 41041 = 4295 := pc_thm_41041
  have h_m_542 : m ≤ 285 := staircase_step_M_direct k m 51156 570780 41041 46886 4295 285 heq (k_mono 755 k h_k_542) h_pc_K_next_541 h_pc_M_next_val_541 rfl (by decide)
  -- Step 542: k >= 755, m <= 285 => k >= 756
  have h_m_mono_542 : m*(m+1)/2 ≤ 40755 := m_mono m 285 h_m_542
  have h_pc_M_542 : Nat.primeCounting 40755 = 4266 := pc_thm_40755
  have h_pc_K_prev_542 : Nat.primeCounting 570780 = 46886 := pc_thm_570780
  have h_k_543 : k ≥ 756 := staircase_step_K_direct k m 51156 40755 570780 4266 46886 756 heq h_m_mono_542 h_pc_M_542 h_pc_K_prev_542 rfl (by decide)
  have h_pc_K_next_542 : Nat.primeCounting 572292 = 46998 := pc_thm_572292
  have h_pc_M_next_val_542 : Nat.primeCounting 39621 = 4166 := pc_thm_39621
  have h_m_543 : m ≤ 280 := staircase_step_M_direct k m 51156 572292 39621 46998 4166 280 heq (k_mono 756 k h_k_543) h_pc_K_next_542 h_pc_M_next_val_542 rfl (by decide)
  -- Step 543: k >= 756, m <= 280 => k >= 757
  have h_m_mono_543 : m*(m+1)/2 ≤ 39340 := m_mono m 280 h_m_543
  have h_pc_M_543 : Nat.primeCounting 39340 = 4140 := pc_thm_39340
  have h_pc_K_prev_543 : Nat.primeCounting 572292 = 46998 := pc_thm_572292
  have h_k_544 : k ≥ 757 := staircase_step_K_direct k m 51156 39340 572292 4140 46998 757 heq h_m_mono_543 h_pc_M_543 h_pc_K_prev_543 rfl (by decide)
  have h_pc_K_next_543 : Nat.primeCounting 573806 = 47116 := pc_thm_573806
  have h_pc_M_next_val_543 : Nat.primeCounting 38503 = 4059 := pc_thm_38503
  have h_m_544 : m ≤ 276 := staircase_step_M_direct k m 51156 573806 38503 47116 4059 276 heq (k_mono 757 k h_k_544) h_pc_K_next_543 h_pc_M_next_val_543 rfl (by decide)
  -- Step 544: k >= 757, m <= 276 => k >= 758
  have h_m_mono_544 : m*(m+1)/2 ≤ 38226 := m_mono m 276 h_m_544
  have h_pc_M_544 : Nat.primeCounting 38226 = 4034 := pc_thm_38226
  have h_pc_K_prev_544 : Nat.primeCounting 573806 = 47116 := pc_thm_573806
  have h_k_545 : k ≥ 758 := staircase_step_K_direct k m 51156 38226 573806 4034 47116 758 heq h_m_mono_544 h_pc_M_544 h_pc_K_prev_544 rfl (by decide)
  have h_pc_K_next_544 : Nat.primeCounting 575322 = 47229 := pc_thm_575322
  have h_pc_M_next_val_544 : Nat.primeCounting 37128 = 3935 := pc_thm_37128
  have h_m_545 : m ≤ 271 := staircase_step_M_direct k m 51156 575322 37128 47229 3935 271 heq (k_mono 758 k h_k_545) h_pc_K_next_544 h_pc_M_next_val_544 rfl (by decide)
  -- Step 545: k >= 758, m <= 271 => k >= 759
  have h_m_mono_545 : m*(m+1)/2 ≤ 36856 := m_mono m 271 h_m_545
  have h_pc_M_545 : Nat.primeCounting 36856 = 3907 := pc_thm_36856
  have h_pc_K_prev_545 : Nat.primeCounting 575322 = 47229 := pc_thm_575322
  have h_k_546 : k ≥ 759 := staircase_step_K_direct k m 51156 36856 575322 3907 47229 759 heq h_m_mono_545 h_pc_M_545 h_pc_K_prev_545 rfl (by decide)
  have h_pc_K_next_545 : Nat.primeCounting 576840 = 47350 := pc_thm_576840
  have h_pc_M_next_val_545 : Nat.primeCounting 36046 = 3829 := pc_thm_36046
  have h_m_546 : m ≤ 267 := staircase_step_M_direct k m 51156 576840 36046 47350 3829 267 heq (k_mono 759 k h_k_546) h_pc_K_next_545 h_pc_M_next_val_545 rfl (by decide)
  -- Step 546: k >= 759, m <= 267 => k >= 760
  have h_m_mono_546 : m*(m+1)/2 ≤ 35778 := m_mono m 267 h_m_546
  have h_pc_M_546 : Nat.primeCounting 35778 = 3801 := pc_thm_35778
  have h_pc_K_prev_546 : Nat.primeCounting 576840 = 47350 := pc_thm_576840
  have h_k_547 : k ≥ 760 := staircase_step_K_direct k m 51156 35778 576840 3801 47350 760 heq h_m_mono_546 h_pc_M_546 h_pc_K_prev_546 rfl (by decide)
  have h_pc_K_next_546 : Nat.primeCounting 578360 = 47459 := pc_thm_578360
  have h_pc_M_next_val_546 : Nat.primeCounting 34716 = 3707 := pc_thm_34716
  have h_m_547 : m ≤ 262 := staircase_step_M_direct k m 51156 578360 34716 47459 3707 262 heq (k_mono 760 k h_k_547) h_pc_K_next_546 h_pc_M_next_val_546 rfl (by decide)
  -- Step 547: k >= 760, m <= 262 => k >= 761
  have h_m_mono_547 : m*(m+1)/2 ≤ 34453 := m_mono m 262 h_m_547
  have h_pc_M_547 : Nat.primeCounting 34453 = 3679 := pc_thm_34453
  have h_pc_K_prev_547 : Nat.primeCounting 578360 = 47459 := pc_thm_578360
  have h_k_548 : k ≥ 761 := staircase_step_K_direct k m 51156 34453 578360 3679 47459 761 heq h_m_mono_547 h_pc_M_547 h_pc_K_prev_547 rfl (by decide)
  have h_pc_K_next_547 : Nat.primeCounting 579882 = 47579 := pc_thm_579882
  have h_pc_M_next_val_547 : Nat.primeCounting 33411 = 3578 := pc_thm_33411
  have h_m_548 : m ≤ 257 := staircase_step_M_direct k m 51156 579882 33411 47579 3578 257 heq (k_mono 761 k h_k_548) h_pc_K_next_547 h_pc_M_next_val_547 rfl (by decide)
  -- Step 548: k >= 761, m <= 257 => k >= 762
  have h_m_mono_548 : m*(m+1)/2 ≤ 33153 := m_mono m 257 h_m_548
  have h_pc_M_548 : Nat.primeCounting 33153 = 3553 := pc_thm_33153
  have h_pc_K_prev_548 : Nat.primeCounting 579882 = 47579 := pc_thm_579882
  have h_k_549 : k ≥ 762 := staircase_step_K_direct k m 51156 33153 579882 3553 47579 762 heq h_m_mono_548 h_pc_M_548 h_pc_K_prev_548 rfl (by decide)
  have h_pc_K_next_548 : Nat.primeCounting 581406 = 47694 := pc_thm_581406
  have h_pc_M_next_val_548 : Nat.primeCounting 32385 = 3476 := pc_thm_32385
  have h_m_549 : m ≤ 253 := staircase_step_M_direct k m 51156 581406 32385 47694 3476 253 heq (k_mono 762 k h_k_549) h_pc_K_next_548 h_pc_M_next_val_548 rfl (by decide)
  -- Step 549: k >= 762, m <= 253 => k >= 763
  have h_m_mono_549 : m*(m+1)/2 ≤ 32131 := m_mono m 253 h_m_549
  have h_pc_M_549 : Nat.primeCounting 32131 = 3447 := pc_thm_32131
  have h_pc_K_prev_549 : Nat.primeCounting 581406 = 47694 := pc_thm_581406
  have h_k_550 : k ≥ 763 := staircase_step_K_direct k m 51156 32131 581406 3447 47694 763 heq h_m_mono_549 h_pc_M_549 h_pc_K_prev_549 rfl (by decide)
  have h_pc_K_next_549 : Nat.primeCounting 582932 = 47807 := pc_thm_582932
  have h_pc_M_next_val_549 : Nat.primeCounting 31125 = 3352 := pc_thm_31125
  have h_m_550 : m ≤ 248 := staircase_step_M_direct k m 51156 582932 31125 47807 3352 248 heq (k_mono 763 k h_k_550) h_pc_K_next_549 h_pc_M_next_val_549 rfl (by decide)
  -- Step 550: k >= 763, m <= 248 => k >= 764
  have h_m_mono_550 : m*(m+1)/2 ≤ 30876 := m_mono m 248 h_m_550
  have h_pc_M_550 : Nat.primeCounting 30876 = 3330 := pc_thm_30876
  have h_pc_K_prev_550 : Nat.primeCounting 582932 = 47807 := pc_thm_582932
  have h_k_551 : k ≥ 764 := staircase_step_K_direct k m 51156 30876 582932 3330 47807 764 heq h_m_mono_550 h_pc_M_550 h_pc_K_prev_550 rfl (by decide)
  have h_pc_K_next_550 : Nat.primeCounting 584460 = 47920 := pc_thm_584460
  have h_pc_M_next_val_550 : Nat.primeCounting 29890 = 3238 := pc_thm_29890
  have h_m_551 : m ≤ 243 := staircase_step_M_direct k m 51156 584460 29890 47920 3238 243 heq (k_mono 764 k h_k_551) h_pc_K_next_550 h_pc_M_next_val_550 rfl (by decide)
  -- Step 551: k >= 764, m <= 243 => k >= 765
  have h_m_mono_551 : m*(m+1)/2 ≤ 29646 := m_mono m 243 h_m_551
  have h_pc_M_551 : Nat.primeCounting 29646 = 3217 := pc_thm_29646
  have h_pc_K_prev_551 : Nat.primeCounting 584460 = 47920 := pc_thm_584460
  have h_k_552 : k ≥ 765 := staircase_step_K_direct k m 51156 29646 584460 3217 47920 765 heq h_m_mono_551 h_pc_M_551 h_pc_K_prev_551 rfl (by decide)
  have h_pc_K_next_551 : Nat.primeCounting 585990 = 48043 := pc_thm_585990
  have h_pc_M_next_val_551 : Nat.primeCounting 28680 = 3124 := pc_thm_28680
  have h_m_552 : m ≤ 238 := staircase_step_M_direct k m 51156 585990 28680 48043 3124 238 heq (k_mono 765 k h_k_552) h_pc_K_next_551 h_pc_M_next_val_551 rfl (by decide)
  -- Step 552: k >= 765, m <= 238 => k >= 766
  have h_m_mono_552 : m*(m+1)/2 ≤ 28441 := m_mono m 238 h_m_552
  have h_pc_M_552 : Nat.primeCounting 28441 = 3095 := pc_thm_28441
  have h_pc_K_prev_552 : Nat.primeCounting 585990 = 48043 := pc_thm_585990
  have h_k_553 : k ≥ 766 := staircase_step_K_direct k m 51156 28441 585990 3095 48043 766 heq h_m_mono_552 h_pc_M_552 h_pc_K_prev_552 rfl (by decide)
  have h_pc_K_next_552 : Nat.primeCounting 587522 = 48166 := pc_thm_587522
  have h_pc_M_next_val_552 : Nat.primeCounting 27495 = 3004 := pc_thm_27495
  have h_m_553 : m ≤ 233 := staircase_step_M_direct k m 51156 587522 27495 48166 3004 233 heq (k_mono 766 k h_k_553) h_pc_K_next_552 h_pc_M_next_val_552 rfl (by decide)
  -- Step 553: k >= 766, m <= 233 => k >= 767
  have h_m_mono_553 : m*(m+1)/2 ≤ 27261 := m_mono m 233 h_m_553
  have h_pc_M_553 : Nat.primeCounting 27261 = 2984 := pc_thm_27261
  have h_pc_K_prev_553 : Nat.primeCounting 587522 = 48166 := pc_thm_587522
  have h_k_554 : k ≥ 767 := staircase_step_K_direct k m 51156 27261 587522 2984 48166 767 heq h_m_mono_553 h_pc_M_553 h_pc_K_prev_553 rfl (by decide)
  have h_pc_K_next_553 : Nat.primeCounting 589056 = 48286 := pc_thm_589056
  have h_pc_M_next_val_553 : Nat.primeCounting 26335 = 2893 := pc_thm_26335
  have h_m_554 : m ≤ 228 := staircase_step_M_direct k m 51156 589056 26335 48286 2893 228 heq (k_mono 767 k h_k_554) h_pc_K_next_553 h_pc_M_next_val_553 rfl (by decide)
  -- Step 554: k >= 767, m <= 228 => k >= 768
  have h_m_mono_554 : m*(m+1)/2 ≤ 26106 := m_mono m 228 h_m_554
  have h_pc_M_554 : Nat.primeCounting 26106 = 2868 := pc_thm_26106
  have h_pc_K_prev_554 : Nat.primeCounting 589056 = 48286 := pc_thm_589056
  have h_k_555 : k ≥ 768 := staircase_step_K_direct k m 51156 26106 589056 2868 48286 768 heq h_m_mono_554 h_pc_M_554 h_pc_K_prev_554 rfl (by decide)
  have h_pc_K_next_554 : Nat.primeCounting 590592 = 48392 := pc_thm_590592
  have h_pc_M_next_val_554 : Nat.primeCounting 25200 = 2781 := pc_thm_25200
  have h_m_555 : m ≤ 223 := staircase_step_M_direct k m 51156 590592 25200 48392 2781 223 heq (k_mono 768 k h_k_555) h_pc_K_next_554 h_pc_M_next_val_554 rfl (by decide)
  -- Step 555: k >= 768, m <= 223 => k >= 769
  have h_m_mono_555 : m*(m+1)/2 ≤ 24976 := m_mono m 223 h_m_555
  have h_pc_M_555 : Nat.primeCounting 24976 = 2759 := pc_thm_24976
  have h_pc_K_prev_555 : Nat.primeCounting 590592 = 48392 := pc_thm_590592
  have h_k_556 : k ≥ 769 := staircase_step_K_direct k m 51156 24976 590592 2759 48392 769 heq h_m_mono_555 h_pc_M_555 h_pc_K_prev_555 rfl (by decide)
  have h_pc_K_next_555 : Nat.primeCounting 592130 = 48499 := pc_thm_592130
  have h_pc_M_next_val_555 : Nat.primeCounting 24090 = 2679 := pc_thm_24090
  have h_m_556 : m ≤ 218 := staircase_step_M_direct k m 51156 592130 24090 48499 2679 218 heq (k_mono 769 k h_k_556) h_pc_K_next_555 h_pc_M_next_val_555 rfl (by decide)
  exact ⟨h_k_556, h_m_556⟩

theorem staircase_part_37 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_556 : k ≥ 769) (h_m_556 : m ≤ 218) : k ≥ 784 ∧ m ≤ 117 := by
  -- Step 556: k >= 769, m <= 218 => k >= 770
  have h_m_mono_556 : m*(m+1)/2 ≤ 23871 := m_mono m 218 h_m_556
  have h_pc_M_556 : Nat.primeCounting 23871 = 2654 := pc_thm_23871
  have h_pc_K_prev_556 : Nat.primeCounting 592130 = 48499 := pc_thm_592130
  have h_k_557 : k ≥ 770 := staircase_step_K_direct k m 51156 23871 592130 2654 48499 770 heq h_m_mono_556 h_pc_M_556 h_pc_K_prev_556 rfl (by decide)
  have h_pc_K_next_556 : Nat.primeCounting 593670 = 48628 := pc_thm_593670
  have h_pc_M_next_val_556 : Nat.primeCounting 22791 = 2547 := pc_thm_22791
  have h_m_557 : m ≤ 212 := staircase_step_M_direct k m 51156 593670 22791 48628 2547 212 heq (k_mono 770 k h_k_557) h_pc_K_next_556 h_pc_M_next_val_556 rfl (by decide)
  -- Step 557: k >= 770, m <= 212 => k >= 771
  have h_m_mono_557 : m*(m+1)/2 ≤ 22578 := m_mono m 212 h_m_557
  have h_pc_M_557 : Nat.primeCounting 22578 = 2524 := pc_thm_22578
  have h_pc_K_prev_557 : Nat.primeCounting 593670 = 48628 := pc_thm_593670
  have h_k_558 : k ≥ 771 := staircase_step_K_direct k m 51156 22578 593670 2524 48628 771 heq h_m_mono_557 h_pc_M_557 h_pc_K_prev_557 rfl (by decide)
  have h_pc_K_next_557 : Nat.primeCounting 595212 = 48746 := pc_thm_595212
  have h_pc_M_next_val_557 : Nat.primeCounting 21528 = 2416 := pc_thm_21528
  have h_m_558 : m ≤ 206 := staircase_step_M_direct k m 51156 595212 21528 48746 2416 206 heq (k_mono 771 k h_k_558) h_pc_K_next_557 h_pc_M_next_val_557 rfl (by decide)
  -- Step 558: k >= 771, m <= 206 => k >= 772
  have h_m_mono_558 : m*(m+1)/2 ≤ 21321 := m_mono m 206 h_m_558
  have h_pc_M_558 : Nat.primeCounting 21321 = 2394 := pc_thm_21321
  have h_pc_K_prev_558 : Nat.primeCounting 595212 = 48746 := pc_thm_595212
  have h_k_559 : k ≥ 772 := staircase_step_K_direct k m 51156 21321 595212 2394 48746 772 heq h_m_mono_558 h_pc_M_558 h_pc_K_prev_558 rfl (by decide)
  have h_pc_K_next_558 : Nat.primeCounting 596756 = 48858 := pc_thm_596756
  have h_pc_M_next_val_558 : Nat.primeCounting 20503 = 2313 := pc_thm_20503
  have h_m_559 : m ≤ 201 := staircase_step_M_direct k m 51156 596756 20503 48858 2313 201 heq (k_mono 772 k h_k_559) h_pc_K_next_558 h_pc_M_next_val_558 rfl (by decide)
  -- Step 559: k >= 772, m <= 201 => k >= 773
  have h_m_mono_559 : m*(m+1)/2 ≤ 20301 := m_mono m 201 h_m_559
  have h_pc_M_559 : Nat.primeCounting 20301 = 2293 := pc_thm_20301
  have h_pc_K_prev_559 : Nat.primeCounting 596756 = 48858 := pc_thm_596756
  have h_k_560 : k ≥ 773 := staircase_step_K_direct k m 51156 20301 596756 2293 48858 773 heq h_m_mono_559 h_pc_M_559 h_pc_K_prev_559 rfl (by decide)
  have h_pc_K_next_559 : Nat.primeCounting 598302 = 48972 := pc_thm_598302
  have h_pc_M_next_val_559 : Nat.primeCounting 19306 = 2188 := pc_thm_19306
  have h_m_560 : m ≤ 195 := staircase_step_M_direct k m 51156 598302 19306 48972 2188 195 heq (k_mono 773 k h_k_560) h_pc_K_next_559 h_pc_M_next_val_559 rfl (by decide)
  -- Step 560: k >= 773, m <= 195 => k >= 774
  have h_m_mono_560 : m*(m+1)/2 ≤ 19110 := m_mono m 195 h_m_560
  have h_pc_M_560 : Nat.primeCounting 19110 = 2169 := pc_thm_19110
  have h_pc_K_prev_560 : Nat.primeCounting 598302 = 48972 := pc_thm_598302
  have h_k_561 : k ≥ 774 := staircase_step_K_direct k m 51156 19110 598302 2169 48972 774 heq h_m_mono_560 h_pc_M_560 h_pc_K_prev_560 rfl (by decide)
  have h_pc_K_next_560 : Nat.primeCounting 599850 = 49086 := pc_thm_599850
  have h_pc_M_next_val_560 : Nat.primeCounting 18145 = 2080 := pc_thm_18145
  have h_m_561 : m ≤ 189 := staircase_step_M_direct k m 51156 599850 18145 49086 2080 189 heq (k_mono 774 k h_k_561) h_pc_K_next_560 h_pc_M_next_val_560 rfl (by decide)
  -- Step 561: k >= 774, m <= 189 => k >= 775
  have h_m_mono_561 : m*(m+1)/2 ≤ 17955 := m_mono m 189 h_m_561
  have h_pc_M_561 : Nat.primeCounting 17955 = 2057 := pc_thm_17955
  have h_pc_K_prev_561 : Nat.primeCounting 599850 = 49086 := pc_thm_599850
  have h_k_562 : k ≥ 775 := staircase_step_K_direct k m 51156 17955 599850 2057 49086 775 heq h_m_mono_561 h_pc_M_561 h_pc_K_prev_561 rfl (by decide)
  have h_pc_K_next_561 : Nat.primeCounting 601400 = 49207 := pc_thm_601400
  have h_pc_M_next_val_561 : Nat.primeCounting 17020 = 1961 := pc_thm_17020
  have h_m_562 : m ≤ 183 := staircase_step_M_direct k m 51156 601400 17020 49207 1961 183 heq (k_mono 775 k h_k_562) h_pc_K_next_561 h_pc_M_next_val_561 rfl (by decide)
  -- Step 562: k >= 775, m <= 183 => k >= 776
  have h_m_mono_562 : m*(m+1)/2 ≤ 16836 := m_mono m 183 h_m_562
  have h_pc_M_562 : Nat.primeCounting 16836 = 1943 := pc_thm_16836
  have h_pc_K_prev_562 : Nat.primeCounting 601400 = 49207 := pc_thm_601400
  have h_k_563 : k ≥ 776 := staircase_step_K_direct k m 51156 16836 601400 1943 49207 776 heq h_m_mono_562 h_pc_M_562 h_pc_K_prev_562 rfl (by decide)
  have h_pc_K_next_562 : Nat.primeCounting 602952 = 49326 := pc_thm_602952
  have h_pc_M_next_val_562 : Nat.primeCounting 15753 = 1837 := pc_thm_15753
  have h_m_563 : m ≤ 176 := staircase_step_M_direct k m 51156 602952 15753 49326 1837 176 heq (k_mono 776 k h_k_563) h_pc_K_next_562 h_pc_M_next_val_562 rfl (by decide)
  -- Step 563: k >= 776, m <= 176 => k >= 777
  have h_m_mono_563 : m*(m+1)/2 ≤ 15576 := m_mono m 176 h_m_563
  have h_pc_M_563 : Nat.primeCounting 15576 = 1816 := pc_thm_15576
  have h_pc_K_prev_563 : Nat.primeCounting 602952 = 49326 := pc_thm_602952
  have h_k_564 : k ≥ 777 := staircase_step_K_direct k m 51156 15576 602952 1816 49326 777 heq h_m_mono_563 h_pc_M_563 h_pc_K_prev_563 rfl (by decide)
  have h_pc_K_next_563 : Nat.primeCounting 604506 = 49439 := pc_thm_604506
  have h_pc_M_next_val_563 : Nat.primeCounting 14706 = 1720 := pc_thm_14706
  have h_m_564 : m ≤ 170 := staircase_step_M_direct k m 51156 604506 14706 49439 1720 170 heq (k_mono 777 k h_k_564) h_pc_K_next_563 h_pc_M_next_val_563 rfl (by decide)
  -- Step 564: k >= 777, m <= 170 => k >= 778
  have h_m_mono_564 : m*(m+1)/2 ≤ 14535 := m_mono m 170 h_m_564
  have h_pc_M_564 : Nat.primeCounting 14535 = 1701 := pc_thm_14535
  have h_pc_K_prev_564 : Nat.primeCounting 604506 = 49439 := pc_thm_604506
  have h_k_565 : k ≥ 778 := staircase_step_K_direct k m 51156 14535 604506 1701 49439 778 heq h_m_mono_564 h_pc_M_564 h_pc_K_prev_564 rfl (by decide)
  have h_pc_K_next_564 : Nat.primeCounting 606062 = 49560 := pc_thm_606062
  have h_pc_M_next_val_564 : Nat.primeCounting 13530 = 1602 := pc_thm_13530
  have h_m_565 : m ≤ 163 := staircase_step_M_direct k m 51156 606062 13530 49560 1602 163 heq (k_mono 778 k h_k_565) h_pc_K_next_564 h_pc_M_next_val_564 rfl (by decide)
  -- Step 565: k >= 778, m <= 163 => k >= 779
  have h_m_mono_565 : m*(m+1)/2 ≤ 13366 := m_mono m 163 h_m_565
  have h_pc_M_565 : Nat.primeCounting 13366 = 1585 := pc_thm_13366
  have h_pc_K_prev_565 : Nat.primeCounting 606062 = 49560 := pc_thm_606062
  have h_k_566 : k ≥ 779 := staircase_step_K_direct k m 51156 13366 606062 1585 49560 779 heq h_m_mono_565 h_pc_M_565 h_pc_K_prev_565 rfl (by decide)
  have h_pc_K_next_565 : Nat.primeCounting 607620 = 49674 := pc_thm_607620
  have h_pc_M_next_val_565 : Nat.primeCounting 12561 = 1500 := pc_thm_12561
  have h_m_566 : m ≤ 157 := staircase_step_M_direct k m 51156 607620 12561 49674 1500 157 heq (k_mono 779 k h_k_566) h_pc_K_next_565 h_pc_M_next_val_565 rfl (by decide)
  -- Step 566: k >= 779, m <= 157 => k >= 780
  have h_m_mono_566 : m*(m+1)/2 ≤ 12403 := m_mono m 157 h_m_566
  have h_pc_M_566 : Nat.primeCounting 12403 = 1480 := pc_thm_12403
  have h_pc_K_prev_566 : Nat.primeCounting 607620 = 49674 := pc_thm_607620
  have h_k_567 : k ≥ 780 := staircase_step_K_direct k m 51156 12403 607620 1480 49674 780 heq h_m_mono_566 h_pc_M_566 h_pc_K_prev_566 rfl (by decide)
  have h_pc_K_next_566 : Nat.primeCounting 609180 = 49794 := pc_thm_609180
  have h_pc_M_next_val_566 : Nat.primeCounting 11325 = 1369 := pc_thm_11325
  have h_m_567 : m ≤ 149 := staircase_step_M_direct k m 51156 609180 11325 49794 1369 149 heq (k_mono 780 k h_k_567) h_pc_K_next_566 h_pc_M_next_val_566 rfl (by decide)
  -- Step 567: k >= 780, m <= 149 => k >= 781
  have h_m_mono_567 : m*(m+1)/2 ≤ 11175 := m_mono m 149 h_m_567
  have h_pc_M_567 : Nat.primeCounting 11175 = 1354 := pc_thm_11175
  have h_pc_K_prev_567 : Nat.primeCounting 609180 = 49794 := pc_thm_609180
  have h_k_568 : k ≥ 781 := staircase_step_K_direct k m 51156 11175 609180 1354 49794 781 heq h_m_mono_567 h_pc_M_567 h_pc_K_prev_567 rfl (by decide)
  have h_pc_K_next_567 : Nat.primeCounting 610742 = 49911 := pc_thm_610742
  have h_pc_M_next_val_567 : Nat.primeCounting 10153 = 1246 := pc_thm_10153
  have h_m_568 : m ≤ 141 := staircase_step_M_direct k m 51156 610742 10153 49911 1246 141 heq (k_mono 781 k h_k_568) h_pc_K_next_567 h_pc_M_next_val_567 rfl (by decide)
  -- Step 568: k >= 781, m <= 141 => k >= 782
  have h_m_mono_568 : m*(m+1)/2 ≤ 10011 := m_mono m 141 h_m_568
  have h_pc_M_568 : Nat.primeCounting 10011 = 1231 := pc_thm_10011
  have h_pc_K_prev_568 : Nat.primeCounting 610742 = 49911 := pc_thm_610742
  have h_k_569 : k ≥ 782 := staircase_step_K_direct k m 51156 10011 610742 1231 49911 782 heq h_m_mono_568 h_pc_M_568 h_pc_K_prev_568 rfl (by decide)
  have h_pc_K_next_568 : Nat.primeCounting 612306 = 50031 := pc_thm_612306
  have h_pc_M_next_val_568 : Nat.primeCounting 9180 = 1137 := pc_thm_9180
  have h_m_569 : m ≤ 134 := staircase_step_M_direct k m 51156 612306 9180 50031 1137 134 heq (k_mono 782 k h_k_569) h_pc_K_next_568 h_pc_M_next_val_568 rfl (by decide)
  -- Step 569: k >= 782, m <= 134 => k >= 783
  have h_m_mono_569 : m*(m+1)/2 ≤ 9045 := m_mono m 134 h_m_569
  have h_pc_M_569 : Nat.primeCounting 9045 = 1124 := pc_thm_9045
  have h_pc_K_prev_569 : Nat.primeCounting 612306 = 50031 := pc_thm_612306
  have h_k_570 : k ≥ 783 := staircase_step_K_direct k m 51156 9045 612306 1124 50031 783 heq h_m_mono_569 h_pc_M_569 h_pc_K_prev_569 rfl (by decide)
  have h_pc_K_next_569 : Nat.primeCounting 613872 = 50151 := pc_thm_613872
  have h_pc_M_next_val_569 : Nat.primeCounting 8001 = 1007 := pc_thm_8001
  have h_m_570 : m ≤ 125 := staircase_step_M_direct k m 51156 613872 8001 50151 1007 125 heq (k_mono 783 k h_k_570) h_pc_K_next_569 h_pc_M_next_val_569 rfl (by decide)
  -- Step 570: k >= 783, m <= 125 => k >= 784
  have h_m_mono_570 : m*(m+1)/2 ≤ 7875 := m_mono m 125 h_m_570
  have h_pc_M_570 : Nat.primeCounting 7875 = 994 := pc_thm_7875
  have h_pc_K_prev_570 : Nat.primeCounting 613872 = 50151 := pc_thm_613872
  have h_k_571 : k ≥ 784 := staircase_step_K_direct k m 51156 7875 613872 994 50151 784 heq h_m_mono_570 h_pc_M_570 h_pc_K_prev_570 rfl (by decide)
  have h_pc_K_next_570 : Nat.primeCounting 615440 = 50263 := pc_thm_615440
  have h_pc_M_next_val_570 : Nat.primeCounting 7021 = 903 := pc_thm_7021
  have h_m_571 : m ≤ 117 := staircase_step_M_direct k m 51156 615440 7021 50263 903 117 heq (k_mono 784 k h_k_571) h_pc_K_next_570 h_pc_M_next_val_570 rfl (by decide)
  exact ⟨h_k_571, h_m_571⟩

theorem staircase_part_38 (k m : ℕ) (heq : Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = 51156)
    (h_k_571 : k ≥ 784) (h_m_571 : m ≤ 117) : False := by
  -- Step 571: k >= 784, m <= 117 => k >= 785
  have h_m_mono_571 : m*(m+1)/2 ≤ 6903 := m_mono m 117 h_m_571
  have h_pc_M_571 : Nat.primeCounting 6903 = 887 := pc_thm_6903
  have h_pc_K_prev_571 : Nat.primeCounting 615440 = 50263 := pc_thm_615440
  have h_k_572 : k ≥ 785 := staircase_step_K_direct k m 51156 6903 615440 887 50263 785 heq h_m_mono_571 h_pc_M_571 h_pc_K_prev_571 rfl (by decide)
  have h_pc_K_next_571 : Nat.primeCounting 617010 = 50391 := pc_thm_617010
  have h_pc_M_next_val_571 : Nat.primeCounting 5886 = 775 := pc_thm_5886
  have h_m_572 : m ≤ 107 := staircase_step_M_direct k m 51156 617010 5886 50391 775 107 heq (k_mono 785 k h_k_572) h_pc_K_next_571 h_pc_M_next_val_571 rfl (by decide)
  -- Step 572: k >= 785, m <= 107 => k >= 786
  have h_m_mono_572 : m*(m+1)/2 ≤ 5778 := m_mono m 107 h_m_572
  have h_pc_M_572 : Nat.primeCounting 5778 = 757 := pc_thm_5778
  have h_pc_K_prev_572 : Nat.primeCounting 617010 = 50391 := pc_thm_617010
  have h_k_573 : k ≥ 786 := staircase_step_K_direct k m 51156 5778 617010 757 50391 786 heq h_m_mono_572 h_pc_M_572 h_pc_K_prev_572 rfl (by decide)
  have h_pc_K_next_572 : Nat.primeCounting 618582 = 50512 := pc_thm_618582
  have h_pc_M_next_val_572 : Nat.primeCounting 4851 = 650 := pc_thm_4851
  have h_m_573 : m ≤ 97 := staircase_step_M_direct k m 51156 618582 4851 50512 650 97 heq (k_mono 786 k h_k_573) h_pc_K_next_572 h_pc_M_next_val_572 rfl (by decide)
  -- Step 573: k >= 786, m <= 97 => k >= 787
  have h_m_mono_573 : m*(m+1)/2 ≤ 4753 := m_mono m 97 h_m_573
  have h_pc_M_573 : Nat.primeCounting 4753 = 640 := pc_thm_4753
  have h_pc_K_prev_573 : Nat.primeCounting 618582 = 50512 := pc_thm_618582
  have h_k_574 : k ≥ 787 := staircase_step_K_direct k m 51156 4753 618582 640 50512 787 heq h_m_mono_573 h_pc_M_573 h_pc_K_prev_573 rfl (by decide)
  have h_pc_K_next_573 : Nat.primeCounting 620156 = 50619 := pc_thm_620156
  have h_pc_M_next_val_573 : Nat.primeCounting 3916 = 541 := pc_thm_3916
  have h_m_574 : m ≤ 87 := staircase_step_M_direct k m 51156 620156 3916 50619 541 87 heq (k_mono 787 k h_k_574) h_pc_K_next_573 h_pc_M_next_val_573 rfl (by decide)
  -- Step 574: k >= 787, m <= 87 => k >= 788
  have h_m_mono_574 : m*(m+1)/2 ≤ 3828 := m_mono m 87 h_m_574
  have h_pc_M_574 : Nat.primeCounting 3828 = 531 := pc_thm_3828
  have h_pc_K_prev_574 : Nat.primeCounting 620156 = 50619 := pc_thm_620156
  have h_k_575 : k ≥ 788 := staircase_step_K_direct k m 51156 3828 620156 531 50619 788 heq h_m_mono_574 h_pc_M_574 h_pc_K_prev_574 rfl (by decide)
  have h_pc_K_next_574 : Nat.primeCounting 621732 = 50741 := pc_thm_621732
  have h_pc_M_next_val_574 : Nat.primeCounting 2926 = 422 := pc_thm_2926
  have h_m_575 : m ≤ 75 := staircase_step_M_direct k m 51156 621732 2926 50741 422 75 heq (k_mono 788 k h_k_575) h_pc_K_next_574 h_pc_M_next_val_574 rfl (by decide)
  -- Step 575: k >= 788, m <= 75 => k >= 789
  have h_m_mono_575 : m*(m+1)/2 ≤ 2850 := m_mono m 75 h_m_575
  have h_pc_M_575 : Nat.primeCounting 2850 = 413 := pc_thm_2850
  have h_pc_K_prev_575 : Nat.primeCounting 621732 = 50741 := pc_thm_621732
  have h_k_576 : k ≥ 789 := staircase_step_K_direct k m 51156 2850 621732 413 50741 789 heq h_m_mono_575 h_pc_M_575 h_pc_K_prev_575 rfl (by decide)
  have h_pc_K_next_575 : Nat.primeCounting 623310 = 50853 := pc_thm_623310
  have h_pc_M_next_val_575 : Nat.primeCounting 2016 = 305 := pc_thm_2016
  have h_m_576 : m ≤ 62 := staircase_step_M_direct k m 51156 623310 2016 50853 305 62 heq (k_mono 789 k h_k_576) h_pc_K_next_575 h_pc_M_next_val_575 rfl (by decide)
  -- Step 576: k >= 789, m <= 62 => k >= 790
  have h_m_mono_576 : m*(m+1)/2 ≤ 1953 := m_mono m 62 h_m_576
  have h_pc_M_576 : Nat.primeCounting 1953 = 297 := pc_thm_1953
  have h_pc_K_prev_576 : Nat.primeCounting 623310 = 50853 := pc_thm_623310
  have h_k_577 : k ≥ 790 := staircase_step_K_direct k m 51156 1953 623310 297 50853 790 heq h_m_mono_576 h_pc_M_576 h_pc_K_prev_576 rfl (by decide)
  have h_pc_K_next_576 : Nat.primeCounting 624890 = 50980 := pc_thm_624890
  have h_pc_M_next_val_576 : Nat.primeCounting 1081 = 180 := pc_thm_1081
  have h_m_577 : m ≤ 45 := staircase_step_M_direct k m 51156 624890 1081 50980 180 45 heq (k_mono 790 k h_k_577) h_pc_K_next_576 h_pc_M_next_val_576 rfl (by decide)
  -- Step 577: k >= 790, m <= 45 => k >= 791
  have h_m_mono_577 : m*(m+1)/2 ≤ 1035 := m_mono m 45 h_m_577
  have h_pc_M_577 : Nat.primeCounting 1035 = 174 := pc_thm_1035
  have h_pc_K_prev_577 : Nat.primeCounting 624890 = 50980 := pc_thm_624890
  have h_k_578 : k ≥ 791 := staircase_step_K_direct k m 51156 1035 624890 174 50980 791 heq h_m_mono_577 h_pc_M_577 h_pc_K_prev_577 rfl (by decide)
  have h_pc_K_next_577 : Nat.primeCounting 626472 = 51083 := pc_thm_626472
  have h_pc_M_next_val_577 : Nat.primeCounting 378 = 74 := pc_thm_378
  have h_m_578 : m ≤ 26 := staircase_step_M_direct k m 51156 626472 378 51083 74 26 heq (k_mono 791 k h_k_578) h_pc_K_next_577 h_pc_M_next_val_577 rfl (by decide)
  -- Step 578: k >= 791, m <= 26 => k >= 792
  have h_m_mono_578 : m*(m+1)/2 ≤ 351 := m_mono m 26 h_m_578
  have h_pc_M_578 : Nat.primeCounting 351 = 70 := pc_thm_351
  have h_pc_K_prev_578 : Nat.primeCounting 626472 = 51083 := pc_thm_626472
  have h_k_579 : k ≥ 792 := staircase_step_K_direct k m 51156 351 626472 70 51083 792 heq h_m_mono_578 h_pc_M_578 h_pc_K_prev_578 rfl (by decide)
  -- Final Contradiction at step 578!
  have h_k_mono_final : 792 * (792 + 1) ≤ k * (k + 1) := k_mono 792 k h_k_579
  have h_pc_K_final : Nat.primeCounting 628056 = 51200 := pc_thm_628056
  exact (by omega : ¬(Nat.primeCounting (k*(k+1)) + Nat.primeCounting (m*(m+1)/2) = 51156)) heq


theorem oeis_a263001_conjecture.disproof :
  ¬ ((∀ (n : ℕ), 2 < n → A263001 n > 0) ∧
     (∀ (n : ℕ), A263001 n = 1 ↔ n = 1 ∨ n = 4 ∨ n = 6)) := by
  intro h
  rcases h with ⟨_, h2⟩
  have h3 := h2 51156
  have h4 : ¬ (51156 = 1 ∨ 51156 = 4 ∨ 51156 = 6) := by decide
  rw [h4] at h3
  have h_not_one : A263001 51156 ≠ 1 := by
    intro h_eq
    exact h3.mp h_eq
  have h_eq_one : A263001 51156 = 1 := by
    rw [A263001]
    have h_singleton : (filter (fun p : ℕ × ℕ => Nat.primeCounting (p.fst * (p.fst + 1)) + Nat.primeCounting (p.snd * (p.snd + 1) / 2) = 51156) (Finset.product (Icc 1 51157) (Icc 1 51157))) = {(16, 1119)} := by
      ext ⟨k, m⟩
      simp only [mem_filter, mem_product, mem_Icc, mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hk1, hk2⟩, ⟨hm1, hm2⟩, heq⟩
        by_cases hm_ge : m ≥ 1120
        · have h_m_mono : m*(m+1)/2 ≥ 1120*1121/2 := m_mono 1120 m hm_ge
          have h_pc_627760 : Nat.primeCounting 627760 = 51179 := pc_thm_627760
          have h_pc_m_mono := primeCounting_mono_comp h_m_mono
          omega
        · have h_m_lt : m ≤ 1119 := by omega
          by_cases hk_le15 : k ≤ 15
          · have h_k_mono : k*(k+1) ≤ 15*16 := k_mono k 15 hk_le15
            have h_pc_k_mono := primeCounting_mono_comp h_k_mono
            have h_pc_240 : Nat.primeCounting 240 = 52 := by decide
            have h_m_mono : m*(m+1)/2 ≤ 1119*1120/2 := m_mono m 1119 h_m_lt
            have h_pc_m_mono := primeCounting_mono_comp h_m_mono
            have h_pc_626640 : Nat.primeCounting 626640 = 51098 := pc_thm_626640
            omega
          · have hk_ge16 : k ≥ 16 := by omega
            by_cases hk_eq16 : k = 16
            · subst hk_eq16
              have h_pc_272 : Nat.primeCounting (16 * 17) = 58 := primeCounting_272
              by_cases hm_le1118 : m ≤ 1118
              · have h_m_mono : m*(m+1)/2 ≤ 1118*1119/2 := m_mono m 1118 hm_le1118
                have h_pc_m_mono := primeCounting_mono_comp h_m_mono
                have h_pc_625521 : Nat.primeCounting 625521 = 51022 := pc_thm_625521
                omega
              · have hm_eq1119 : m = 1119 := by omega
                exact ⟨rfl, hm_eq1119⟩
            · have hk_ge17 : k ≥ 17 := by omega
              by_cases hk_eq17 : k = 17
              · subst hk_eq17
                have h_pc_306 : Nat.primeCounting (17 * 18) = 62 := by decide
                by_cases hm_le1118 : m ≤ 1118
                · have h_m_mono : m*(m+1)/2 ≤ 1118*1119/2 := m_mono m 1118 hm_le1118
                  have h_pc_m_mono := primeCounting_mono_comp h_m_mono
                  have h_pc_625521 : Nat.primeCounting 625521 = 51022 := pc_thm_625521
                  omega
                · have hm_ge1119 : m ≥ 1119 := by omega
                  have h_m_mono : m*(m+1)/2 ≥ 1119*1120/2 := m_mono 1119 m hm_ge1119
                  have h_pc_m_mono := primeCounting_mono_comp h_m_mono
                  have h_pc_626640 : Nat.primeCounting 626640 = 51098 := pc_thm_626640
                  omega
              · have hk_ge18 : k ≥ 18 := by omega
                by_cases hm_ge1119 : m ≥ 1119
                · have h_k_mono : k*(k+1) ≥ 18*19 := k_mono 18 k hk_ge18
                  have h_pc_k_mono := primeCounting_mono_comp h_k_mono
                  have h_pc_342 : Nat.primeCounting 342 = 68 := by decide
                  have h_m_mono : m*(m+1)/2 ≥ 1119*1120/2 := m_mono 1119 m hm_ge1119
                  have h_pc_m_mono := primeCounting_mono_comp h_m_mono
                  have h_pc_626640 : Nat.primeCounting 626640 = 51098 := pc_thm_626640
                  omega
                · have h_m_1 : m ≤ 1118 := by omega
                  have h_k_1 : k ≥ 18 := hk_ge18
                  have ⟨h_k_16, h_m_16⟩ := staircase_part_0 k m heq h_k_1 h_m_1
                  have ⟨h_k_31, h_m_31⟩ := staircase_part_1 k m heq h_k_16 h_m_16
                  have ⟨h_k_46, h_m_46⟩ := staircase_part_2 k m heq h_k_31 h_m_31
                  have ⟨h_k_61, h_m_61⟩ := staircase_part_3 k m heq h_k_46 h_m_46
                  have ⟨h_k_76, h_m_76⟩ := staircase_part_4 k m heq h_k_61 h_m_61
                  have ⟨h_k_91, h_m_91⟩ := staircase_part_5 k m heq h_k_76 h_m_76
                  have ⟨h_k_106, h_m_106⟩ := staircase_part_6 k m heq h_k_91 h_m_91
                  have ⟨h_k_121, h_m_121⟩ := staircase_part_7 k m heq h_k_106 h_m_106
                  have ⟨h_k_136, h_m_136⟩ := staircase_part_8 k m heq h_k_121 h_m_121
                  have ⟨h_k_151, h_m_151⟩ := staircase_part_9 k m heq h_k_136 h_m_136
                  have ⟨h_k_166, h_m_166⟩ := staircase_part_10 k m heq h_k_151 h_m_151
                  have ⟨h_k_181, h_m_181⟩ := staircase_part_11 k m heq h_k_166 h_m_166
                  have ⟨h_k_196, h_m_196⟩ := staircase_part_12 k m heq h_k_181 h_m_181
                  have ⟨h_k_211, h_m_211⟩ := staircase_part_13 k m heq h_k_196 h_m_196
                  have ⟨h_k_226, h_m_226⟩ := staircase_part_14 k m heq h_k_211 h_m_211
                  have ⟨h_k_241, h_m_241⟩ := staircase_part_15 k m heq h_k_226 h_m_226
                  have ⟨h_k_256, h_m_256⟩ := staircase_part_16 k m heq h_k_241 h_m_241
                  have ⟨h_k_271, h_m_271⟩ := staircase_part_17 k m heq h_k_256 h_m_256
                  have ⟨h_k_286, h_m_286⟩ := staircase_part_18 k m heq h_k_271 h_m_271
                  have ⟨h_k_301, h_m_301⟩ := staircase_part_19 k m heq h_k_286 h_m_286
                  have ⟨h_k_316, h_m_316⟩ := staircase_part_20 k m heq h_k_301 h_m_301
                  have ⟨h_k_331, h_m_331⟩ := staircase_part_21 k m heq h_k_316 h_m_316
                  have ⟨h_k_346, h_m_346⟩ := staircase_part_22 k m heq h_k_331 h_m_331
                  have ⟨h_k_361, h_m_361⟩ := staircase_part_23 k m heq h_k_346 h_m_346
                  have ⟨h_k_376, h_m_376⟩ := staircase_part_24 k m heq h_k_361 h_m_361
                  have ⟨h_k_391, h_m_391⟩ := staircase_part_25 k m heq h_k_376 h_m_376
                  have ⟨h_k_406, h_m_406⟩ := staircase_part_26 k m heq h_k_391 h_m_391
                  have ⟨h_k_421, h_m_421⟩ := staircase_part_27 k m heq h_k_406 h_m_406
                  have ⟨h_k_436, h_m_436⟩ := staircase_part_28 k m heq h_k_421 h_m_421
                  have ⟨h_k_451, h_m_451⟩ := staircase_part_29 k m heq h_k_436 h_m_436
                  have ⟨h_k_466, h_m_466⟩ := staircase_part_30 k m heq h_k_451 h_m_451
                  have ⟨h_k_481, h_m_481⟩ := staircase_part_31 k m heq h_k_466 h_m_466
                  have ⟨h_k_496, h_m_496⟩ := staircase_part_32 k m heq h_k_481 h_m_481
                  have ⟨h_k_511, h_m_511⟩ := staircase_part_33 k m heq h_k_496 h_m_496
                  have ⟨h_k_526, h_m_526⟩ := staircase_part_34 k m heq h_k_511 h_m_511
                  have ⟨h_k_541, h_m_541⟩ := staircase_part_35 k m heq h_k_526 h_m_526
                  have ⟨h_k_556, h_m_556⟩ := staircase_part_36 k m heq h_k_541 h_m_541
                  have ⟨h_k_571, h_m_571⟩ := staircase_part_37 k m heq h_k_556 h_m_556
                  exact staircase_part_38 k m heq h_k_571 h_m_571
      · rintro ⟨rfl, rfl⟩
        exact sol_in_set
    rw [h_singleton]
    rfl
  exact h_not_one h_eq_one
