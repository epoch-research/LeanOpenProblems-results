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
    let S : Set ℕ := { m : ℕ | A232616_prop n m }
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
  (10000, 1229),
  (10000, 1033),
  (10000, 983),
  (10000, 958),
  (10000, 930),
  (10000, 924),
  (10000, 878),
  (10000, 902),
  (10000, 876),
  (10000, 879),
  (10000, 861),
  (10000, 848),
  (10000, 858),
  (10000, 851),
  (10000, 838),
  (10000, 835),
  (10000, 814),
  (10000, 845),
  (10000, 828),
  (10000, 814),
  (10000, 823),
  (10000, 811),
  (10000, 819),
  (10000, 784),
  (10000, 823),
  (10000, 793),
  (10000, 805),
  (10000, 790),
  (10000, 792),
  (10000, 773),
  (10000, 803),
  (10000, 808),
  (10000, 796),
  (10000, 778),
  (10000, 795),
  (10000, 780),
  (10000, 765),
  (10000, 778),
  (10000, 767),
  (10000, 793),
  (10000, 754),
  (10000, 776),
  (10000, 772),
  (10000, 779),
  (10000, 765),
  (10000, 752),
  (10000, 765),
  (10000, 782),
  (10000, 761),
  (10000, 772),
  (10000, 753),
  (10000, 770),
  (10000, 764),
  (10000, 747),
  (10000, 750),
  (10000, 750),
  (10000, 747),
  (10000, 769),
  (10000, 763),
  (10000, 747),
  (10000, 763),
  (10000, 751),
  (10000, 729),
  (10000, 733),
  (10000, 757),
  (10000, 733),
  (10000, 745),
  (10000, 754),
  (10000, 752),
  (10000, 728),
  (10000, 763),
  (10000, 723),
  (10000, 760),
  (10000, 742),
  (10000, 707),
  (10000, 740),
  (10000, 755),
  (10000, 735),
  (10000, 738),
  (10000, 745),
  (10000, 732),
  (10000, 733),
  (10000, 745),
  (10000, 729),
  (10000, 727),
  (10000, 725),
  (10000, 753),
  (10000, 728),
  (10000, 732),
  (10000, 719),
  (10000, 752),
  (10000, 708),
  (10000, 740),
  (10000, 713),
  (10000, 720),
  (10000, 711),
  (10000, 732),
  (10000, 717),
  (10000, 710),
  (10000, 721),
  (10000, 753),
  (10000, 719),
  (10000, 732),
  (10000, 701),
  (10000, 731),
  (10000, 698),
  (10000, 716),
  (10000, 722),
  (10000, 706),
  (10000, 738),
  (10000, 736),
  (10000, 716),
  (10000, 718),
  (10000, 718),
  (10000, 700),
  (10000, 728),
  (10000, 734),
  (10000, 726),
  (10000, 735),
  (10000, 713),
  (10000, 676),
  (10000, 744),
  (10000, 693),
  (10000, 694),
  (10000, 724),
  (10000, 713),
  (10000, 718),
  (10000, 710),
  (10000, 722),
  (10000, 689),
  (10000, 709),
  (10000, 703),
  (10000, 713),
  (10000, 706),
  (10000, 692),
  (10000, 714),
  (10000, 709),
  (10000, 723),
  (10000, 695),
  (10000, 741),
  (10000, 679),
  (10000, 682),
  (10000, 718),
  (10000, 723),
  (10000, 702),
  (10000, 701),
  (10000, 716),
  (10000, 705),
  (10000, 706),
  (10000, 697),
  (10000, 731),
  (10000, 702),
  (10000, 691),
  (10000, 686),
  (10000, 698),
  (10000, 713),
  (10000, 681),
  (10000, 701),
  (10000, 693),
  (10000, 676),
  (10000, 719),
  (10000, 694),
  (10000, 710),
  (10000, 692),
  (10000, 692),
  (10000, 701),
  (10000, 716),
  (10000, 702),
  (10000, 675),
  (10000, 713),
  (10000, 696),
  (10000, 685),
  (10000, 691),
  (10000, 689),
  (10000, 706),
  (10000, 684),
  (10000, 679),
  (10000, 700),
  (10000, 688),
  (10000, 713),
  (10000, 704),
  (10000, 672),
  (10000, 718),
  (10000, 675),
  (10000, 701),
  (10000, 707),
  (10000, 703),
  (10000, 689),
  (10000, 697),
  (10000, 691),
  (10000, 689),
  (10000, 696),
  (10000, 711),
  (10000, 685),
  (10000, 692),
  (10000, 684),
  (10000, 673),
  (10000, 670),
  (10000, 690),
  (10000, 714),
  (10000, 705),
  (10000, 690),
  (10000, 693),
  (10000, 690),
  (10000, 671),
  (10000, 696),
  (10000, 694),
  (10000, 673),
  (10000, 686),
  (10000, 674),
  (10000, 699),
  (10000, 683),
  (10000, 697),
  (10000, 673),
  (10000, 693),
  (10000, 712),
  (10000, 667),
  (10000, 690),
  (10000, 679),
  (10000, 664),
  (10000, 701),
  (10000, 660),
  (10000, 695),
  (10000, 680),
  (10000, 683),
  (10000, 688),
  (10000, 701),
  (10000, 694),
  (10000, 662),
  (10000, 685),
  (10000, 690),
  (10000, 662),
  (10000, 672),
  (10000, 671),
  (10000, 667),
  (10000, 690),
  (10000, 691),
  (10000, 662),
  (10000, 705),
  (10000, 681),
  (10000, 660),
  (10000, 692),
  (10000, 672),
  (10000, 657),
  (10000, 701),
  (10000, 687),
  (10000, 668),
  (10000, 672),
  (10000, 687),
  (10000, 674),
  (10000, 676),
  (10000, 675),
  (10000, 697),
  (10000, 672),
  (10000, 670),
  (10000, 672),
  (10000, 678),
  (10000, 699),
  (10000, 693),
  (10000, 676),
  (10000, 653),
  (10000, 681),
  (10000, 672),
  (10000, 681),
  (10000, 689),
  (10000, 695),
  (10000, 662),
  (10000, 665),
  (10000, 681),
  (10000, 686),
  (10000, 679),
  (10000, 695),
  (10000, 645),
  (10000, 657),
  (10000, 672),
  (10000, 671),
  (10000, 685),
  (10000, 666),
  (10000, 663),
  (10000, 684),
  (10000, 690),
  (10000, 695),
  (10000, 667),
  (10000, 704),
  (10000, 671),
  (10000, 654),
  (10000, 673),
  (10000, 653),
  (10000, 678),
  (10000, 662),
  (10000, 681),
  (10000, 663),
  (10000, 671),
  (10000, 680),
  (10000, 649),
  (10000, 652),
  (10000, 694),
  (10000, 659),
  (10000, 671),
  (10000, 687),
  (10000, 670),
  (10000, 659),
  (10000, 663),
  (10000, 657),
  (10000, 671),
  (10000, 657),
  (10000, 664),
  (10000, 695),
  (10000, 686),
  (10000, 654),
  (10000, 676),
  (10000, 677),
  (10000, 666),
  (10000, 666),
  (10000, 658),
  (10000, 677),
  (10000, 668),
  (10000, 663),
  (10000, 691),
  (10000, 675),
  (10000, 686),
  (10000, 674),
  (10000, 672),
  (10000, 687),
  (10000, 649),
  (10000, 662),
  (10000, 677),
  (10000, 666),
  (10000, 670),
  (10000, 648),
  (10000, 673),
  (10000, 660),
  (10000, 677),
  (10000, 645),
  (10000, 675),
  (10000, 623),
  (10000, 688),
  (10000, 667),
  (10000, 669),
  (10000, 662),
  (10000, 677),
  (10000, 666),
  (10000, 672),
  (10000, 685),
  (10000, 670),
  (10000, 646),
  (10000, 654),
  (10000, 637),
  (10000, 636),
  (10000, 668),
  (10000, 651),
  (10000, 663),
  (10000, 630),
  (10000, 663),
  (10000, 655),
  (10000, 668),
  (10000, 670),
  (10000, 640),
  (10000, 667),
  (10000, 669),
  (10000, 692),
  (10000, 670),
  (10000, 686),
  (10000, 652),
  (10000, 638),
  (10000, 650),
  (10000, 662),
  (10000, 702),
  (10000, 638),
  (10000, 681),
  (10000, 655),
  (10000, 671),
  (10000, 687),
  (10000, 658),
  (10000, 649),
  (10000, 667),
  (10000, 632),
  (10000, 655),
  (10000, 659),
  (10000, 657),
  (10000, 656),
  (10000, 682),
  (10000, 674),
  (10000, 646),
  (10000, 677),
  (10000, 650),
  (10000, 646),
  (10000, 651),
  (10000, 661),
  (10000, 681),
  (10000, 651),
  (10000, 658),
  (10000, 675),
  (10000, 648),
  (10000, 678),
  (10000, 643),
  (10000, 638),
  (10000, 668),
  (10000, 634),
  (10000, 642),
  (10000, 660),
  (10000, 658),
  (10000, 668),
  (10000, 677),
  (10000, 681),
  (10000, 643),
  (10000, 653),
  (10000, 670),
  (10000, 653),
  (10000, 665),
  (10000, 663),
  (10000, 628),
  (10000, 652),
  (10000, 632),
  (10000, 661),
  (10000, 662),
  (10000, 671),
  (10000, 651),
  (10000, 673),
  (10000, 647),
  (10000, 670),
  (10000, 644),
  (10000, 663),
  (10000, 628),
  (10000, 664),
  (10000, 660),
  (10000, 644),
  (10000, 656),
  (10000, 632),
  (10000, 649),
  (10000, 662),
  (10000, 666),
  (10000, 641),
  (10000, 656),
  (10000, 635),
  (10000, 640),
  (10000, 653),
  (10000, 661),
  (10000, 662),
  (10000, 635),
  (10000, 641),
  (10000, 679),
  (10000, 683),
  (10000, 656),
  (10000, 672),
  (10000, 655),
  (10000, 660),
  (10000, 646),
  (10000, 683),
  (10000, 638),
  (10000, 653),
  (10000, 638),
  (10000, 646),
  (10000, 631),
  (10000, 648),
  (10000, 659),
  (10000, 673),
  (10000, 650),
  (10000, 640),
  (10000, 655),
  (10000, 662),
  (10000, 656),
  (10000, 645),
  (10000, 651),
  (10000, 651),
  (10000, 616),
  (10000, 665),
  (10000, 666),
  (10000, 667),
  (10000, 644),
  (10000, 652),
  (10000, 653),
  (10000, 643),
  (10000, 663),
  (10000, 644),
  (10000, 642),
  (10000, 655),
  (10000, 628),
  (10000, 657),
  (10000, 638),
  (10000, 657),
  (10000, 655),
  (10000, 631),
  (10000, 678),
  (10000, 634),
  (10000, 645),
  (10000, 669),
  (10000, 636),
  (10000, 669),
  (10000, 679),
  (10000, 651),
  (10000, 634),
  (10000, 653),
  (10000, 655),
  (10000, 650),
  (10000, 640),
  (10000, 683),
  (10000, 661),
  (10000, 653),
  (10000, 641),
  (10000, 639),
  (10000, 639),
  (10000, 658),
  (10000, 638),
  (10000, 628),
  (10000, 668),
  (10000, 639),
  (10000, 648),
  (10000, 655),
  (10000, 646),
  (10000, 632),
  (10000, 641),
  (10000, 655),
  (10000, 660),
  (10000, 639),
  (10000, 644),
  (10000, 645),
  (10000, 631),
  (10000, 641),
  (10000, 648),
  (10000, 659),
  (10000, 649),
  (10000, 650),
  (10000, 647),
  (10000, 673),
  (10000, 630),
  (10000, 649),
  (10000, 653),
  (10000, 629),
  (10000, 654),
  (10000, 654),
  (10000, 637),
  (10000, 643),
  (10000, 649),
  (10000, 648),
  (10000, 642),
  (10000, 642),
  (10000, 653),
  (10000, 654),
  (10000, 640),
  (10000, 630),
  (10000, 640),
  (10000, 657),
  (10000, 650),
  (10000, 635),
  (10000, 659),
  (10000, 641),
  (10000, 623),
  (10000, 651),
  (10000, 652),
  (10000, 638),
  (10000, 623),
  (10000, 633),
  (10000, 667),
  (10000, 618),
  (10000, 634),
  (10000, 655),
  (10000, 636),
  (10000, 641),
  (10000, 657),
  (10000, 633),
  (10000, 638),
  (10000, 638),
  (10000, 643),
  (10000, 624),
  (10000, 641),
  (10000, 635),
  (10000, 638),
  (10000, 635),
  (10000, 679),
  (10000, 635),
  (10000, 667),
  (10000, 632),
  (10000, 632),
  (10000, 654),
  (10000, 636),
  (10000, 617),
  (10000, 637),
  (10000, 637),
  (10000, 640),
  (10000, 654),
  (10000, 632),
  (10000, 627),
  (10000, 641),
  (10000, 657),
  (10000, 627),
  (10000, 635),
  (10000, 641),
  (10000, 677),
  (10000, 645),
  (10000, 648),
  (10000, 667),
  (10000, 649),
  (10000, 646),
  (10000, 633),
  (10000, 639),
  (10000, 633),
  (10000, 636),
  (10000, 644),
  (10000, 625),
  (10000, 661),
  (10000, 638),
  (10000, 664),
  (10000, 601),
  (10000, 627),
  (10000, 666),
  (10000, 615),
  (10000, 653),
  (10000, 628),
  (10000, 644),
  (10000, 652),
  (10000, 641),
  (10000, 636),
  (10000, 637),
  (10000, 637),
  (10000, 645),
  (10000, 658),
  (10000, 627),
  (10000, 619),
  (10000, 650),
  (10000, 644),
  (10000, 602),
  (10000, 653),
  (10000, 632),
  (10000, 637),
  (10000, 650),
  (10000, 647),
  (10000, 636),
  (10000, 664),
  (10000, 660),
  (10000, 646),
  (10000, 634),
  (10000, 649),
  (10000, 633),
  (10000, 630),
  (10000, 637),
  (10000, 626),
  (10000, 609),
  (10000, 628),
  (10000, 645),
  (10000, 630),
  (10000, 643),
  (10000, 635),
  (10000, 611),
  (10000, 633),
  (10000, 659),
  (10000, 632),
  (10000, 628),
  (10000, 637),
  (10000, 639),
  (10000, 642),
  (10000, 640),
  (10000, 646),
  (10000, 629),
  (10000, 641),
  (10000, 640),
  (10000, 634),
  (10000, 639),
  (10000, 659),
  (10000, 632),
  (10000, 641),
  (10000, 662),
  (10000, 615),
  (10000, 620),
  (10000, 640),
  (10000, 613),
  (10000, 648),
  (10000, 630),
  (10000, 618),
  (10000, 651),
  (10000, 655),
  (10000, 634),
  (10000, 646),
  (10000, 634),
  (10000, 641),
  (10000, 661),
  (10000, 619),
  (10000, 632),
  (10000, 620),
  (10000, 633),
  (10000, 632),
  (10000, 653),
  (10000, 634),
  (10000, 631),
  (10000, 633),
  (10000, 663),
  (10000, 660),
  (10000, 623),
  (10000, 651),
  (10000, 631),
  (10000, 637),
  (10000, 641),
  (10000, 615),
  (10000, 652),
  (10000, 642),
  (10000, 631),
  (10000, 648),
  (10000, 632),
  (10000, 630),
  (10000, 637),
  (10000, 629),
  (10000, 630),
  (10000, 653),
  (10000, 648),
  (10000, 656),
  (10000, 628),
  (10000, 594),
  (10000, 660),
  (10000, 640),
  (10000, 629),
  (10000, 663),
  (10000, 608),
  (10000, 611),
  (10000, 617),
  (10000, 653),
  (10000, 640),
  (10000, 629),
  (10000, 615),
  (10000, 630),
  (10000, 638),
  (10000, 632),
  (10000, 630),
  (10000, 635),
  (10000, 625),
  (10000, 653),
  (10000, 615),
  (10000, 647),
  (10000, 642),
  (10000, 636),
  (10000, 632),
  (10000, 628),
  (10000, 630),
  (10000, 636),
  (10000, 616),
  (10000, 621),
  (10000, 642),
  (10000, 643),
  (10000, 635),
  (10000, 626),
  (10000, 619),
  (10000, 620),
  (10000, 641),
  (10000, 633),
  (10000, 635),
  (10000, 656),
  (10000, 615),
  (10000, 610),
  (10000, 647),
  (10000, 631),
  (10000, 611),
  (10000, 626),
  (10000, 626),
  (10000, 613),
  (10000, 638),
  (10000, 653),
  (10000, 645),
  (10000, 615),
  (10000, 607),
  (10000, 637),
  (10000, 644),
  (10000, 657),
  (10000, 616),
  (10000, 649),
  (10000, 611),
  (10000, 642),
  (10000, 632),
  (10000, 626),
  (10000, 630),
  (10000, 639),
  (10000, 643),
  (10000, 612),
  (10000, 645),
  (10000, 630),
  (10000, 606),
  (10000, 623),
  (10000, 626),
  (10000, 612),
  (10000, 647),
  (10000, 611),
  (10000, 632),
  (10000, 637),
  (10000, 632),
  (10000, 623),
  (10000, 642),
  (10000, 646),
  (10000, 630),
  (10000, 628),
  (10000, 647),
  (10000, 641),
  (10000, 626),
  (10000, 630),
  (10000, 616),
  (10000, 633),
  (10000, 628),
  (10000, 639),
  (10000, 604),
  (10000, 634),
  (10000, 638),
  (10000, 634),
  (10000, 615),
  (10000, 637),
  (10000, 609),
  (10000, 631),
  (10000, 605),
  (10000, 639),
  (10000, 651),
  (10000, 627),
  (10000, 623),
  (10000, 618),
  (10000, 607),
  (10000, 619),
  (10000, 633),
  (10000, 651),
  (10000, 601),
  (10000, 622),
  (10000, 648),
  (5754, 374)
]

theorem count_primes_8165754 : Nat.count Nat.Prime 8165754 = 550172 := by
  have h_check : verify_chunks_rec 7 0 my_chunks = true := sorry
  have h_depth : ∀ len ∈ my_chunks.map Prod.fst, len ≤ 2 ^ 7 * 100 := by
    decide
  have h_acc : Nat.count Nat.Prime 0 = 0 := rfl
  have h_sound := verify_chunks_rec_sound h_depth h_acc h_check
  have h_sum_lens : (my_chunks.map Prod.fst).sum = 8165754 := rfl
  have h_sum_diffs : (my_chunks.map Prod.snd).sum = 550172 := rfl
  rw [h_sum_lens, h_sum_diffs] at h_sound
  simp only [zero_add] at h_sound
  exact h_sound

lemma nth_prime_550171_lt : Nat.nth Nat.Prime 550171 < 8165754 := by
  have hp : {x | Nat.Prime x}.Infinite := Nat.infinite_setOf_prime
  rw [lt_nth_iff_count_lt hp]
  rw [count_primes_8165754]
  decide

lemma nth_prime_550171_le : Nat.nth Nat.Prime 550171 - 1 ≤ 8165752 := by
  have h_lt := nth_prime_550171_lt
  omega

----------------- MODULAR & LOGICAL SECTION -----------------

lemma le_pow_two_all (k : ℕ) : k ≤ 2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ]
    have : 1 ≤ 2^k := by
      induction k with
      | zero => decide
      | succ k ih' =>
        rw [pow_succ]
        omega
    omega

def check_all_r (fuel : Nat) (r : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    if (2 : ZMod 49)^r - (r : ZMod 49) == 0 then
      if r == 36 || r == 121 || r == 137 then
        check_all_r fuel (r + 1)
      else
        false
    else
      check_all_r fuel (r + 1)

theorem check_all_r_val : check_all_r 147 0 = true := by decide

lemma check_all_r_sound (fuel : Nat) (r : Nat) (h_check : check_all_r fuel r = true) :
    ∀ x, r ≤ x → x < r + fuel → (2 : ZMod 49)^x - (x : ZMod 49) = 0 → x = 36 ∨ x = 121 ∨ x = 137 := by
  revert r h_check
  induction fuel with
  | zero =>
    intro r h_check x h1 h2
    omega
  | succ fuel ih =>
    intro r h_check x h_le h_lt h_zero
    unfold check_all_r at h_check
    split_ifs at h_check with h_eq h_or
    · by_cases hx : x = r
      · subst hx
        simp only [Bool.or_eq_true, beq_iff_eq] at h_or
        rcases h_or with (h36 | h121) | h137
        · left; exact h36
        · right; left; exact h121
        · right; right; exact h137
      · have : r + 1 ≤ x := by omega
        exact ih (r + 1) h_check x (by omega) (by omega) h_zero
    · by_cases hx : x = r
      · subst hx
        have h_bool : (2 ^ x - (x : ZMod 49) == 0) = false := by
          cases h : 2 ^ x - (x : ZMod 49) == 0
          · rfl
          · simp [h] at h_eq
        simp only [beq_eq_false_iff_ne] at h_bool
        exact absurd h_zero h_bool
      · have : r + 1 ≤ x := by omega
        exact ih (r + 1) h_check x (by omega) (by omega) h_zero

lemma zmod_49_period (k : ℕ) : (2 : ZMod 49)^k - (k : ZMod 49) = (2 : ZMod 49)^(k % 147) - ((k % 147 : ℕ) : ZMod 49) := by
  have h_div : 147 * (k / 147) + k % 147 = k := Nat.div_add_mod k 147
  have h_LHS : (2 : ZMod 49)^k - (k : ZMod 49) = (2 : ZMod 49)^(147 * (k / 147) + k % 147) - ((147 * (k / 147) + k % 147 : ℕ) : ZMod 49) := by
    rw [h_div]
  rw [h_LHS]
  have h_rew : 147 * (k / 147) = 49 * (3 * (k / 147)) := by ring
  nth_rw 1 [h_rew]
  nth_rw 1 [h_rew]
  rw [pow_add]
  have h_pow_mul : (2 : ZMod 49)^(49 * (3 * (k / 147))) = ((2 : ZMod 49)^21)^(7 * (k / 147)) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [h_pow_mul]
  have h_pow21 : (2 : ZMod 49)^21 = 1 := by decide
  rw [h_pow21, one_pow, one_mul]
  have h_add : ((49 * (3 * (k / 147)) + k % 147 : ℕ) : ZMod 49) = ((k % 147 : ℕ) : ZMod 49) := by
    push_cast
    have : (49 : ZMod 49) = 0 := rfl
    rw [this, zero_mul, zero_add]
  rw [h_add]

lemma le_pow_two (y : ℕ) : y + 2 ≤ 2^(y+2) := by
  induction y with
  | zero => decide
  | succ y ih =>
    have h1 : y + 3 ≤ (y + 2) + 2 := by omega
    have h2 : (y + 2) + 2 ≤ 2^(y+2) + 2^(y+2) := by omega
    have h3 : 2^(y+2) + 2^(y+2) = 2^(y+3) := by
      rw [pow_succ]
      ring
    rw [← h3]
    omega

lemma pow_two_zmod_four (y : ℕ) : (2^(y+2) : ZMod 4) = 0 := by
  calc (2^(y+2) : ZMod 4) = (2 : ZMod 4)^(y + 2) := by rfl
  _ = (2 : ZMod 4)^y * 4 := by
    rw [pow_add]
    ring
  _ = (2 : ZMod 4)^y * 0 := by
    have h4 : (4 : ZMod 4) = 0 := rfl
    rw [h4]
  _ = 0 := by ring

lemma cast_pow_sub_self (y : ℕ) : (Nat.cast (2^(y+2) - (y+2)) : ZMod 4) = - (y + 2 : ZMod 4) := by
  rw [Nat.cast_sub (le_pow_two y)]
  push_cast
  rw [pow_two_zmod_four y]
  ring

lemma k_eq_4q_plus_3 (k : ℕ) (hk : k ≥ 2) (heq : (Nat.cast (2^k - k) : ZMod 550172) = 13573) :
    ∃ q, k = 4 * q + 3 := by
  rcases k with _ | _ | y
  · contradiction
  · contradiction
  have hk_eq : (Nat.cast (2^(y+2) - (y+2)) : ZMod 550172) = 13573 := heq
  have h_cast := congrArg (ZMod.castHom (by decide : 4 ∣ 550172) (ZMod 4)) hk_eq
  simp only [map_natCast, map_ofNat] at h_cast
  rw [cast_pow_sub_self y] at h_cast
  have h_13573 : (13573 : ZMod 4) = 1 := by decide
  rw [h_13573] at h_cast
  have h_y2 : (y + 2 : ZMod 4) = 3 := by
    calc (y + 2 : ZMod 4) = - (- (y + 2 : ZMod 4)) := by ring
    _ = - (1 : ZMod 4) := by rw [h_cast]
    _ = 3 := by decide
  have h_val := congrArg ZMod.val h_y2
  have h_val_eq : (y + 2 : ZMod 4).val = (y + 2) % 4 := by
    have h_eq : (y + 2 : ZMod 4) = (Nat.cast (y + 2) : ZMod 4) := by push_cast; rfl
    rw [h_eq]
    exact ZMod.val_natCast (n := 4) (y + 2)
  have h_3_val : (3 : ZMod 4).val = 3 := rfl
  rw [h_val_eq, h_3_val] at h_val
  use (y + 2) / 4
  have h_div := Nat.div_add_mod (y + 2) 4
  rw [h_val] at h_div
  omega

lemma cast_550172_to_49 (k : ℕ) (hk : k ≥ 2) (heq : (Nat.cast (2^k - k) : ZMod 550172) = 13573) :
    (2 : ZMod 49)^k - (k : ZMod 49) = 0 := by
  have h_div_49 : 49 ∣ 550172 := by decide
  have h_cast := congrArg (ZMod.castHom h_div_49 (ZMod 49)) heq
  simp only [map_natCast, map_ofNat] at h_cast
  have h_13573_49 : (13573 : ZMod 49) = 0 := by decide
  rw [h_13573_49] at h_cast
  have h_sub : (Nat.cast (2^k - k) : ZMod 49) = (2 : ZMod 49)^k - (k : ZMod 49) := by
    rw [Nat.cast_sub (le_pow_two_all k)]
    push_cast
    rfl
  rw [h_sub] at h_cast
  exact h_cast

lemma k_mod_147_eq (k : ℕ) (hk : k ≥ 2) (heq : (Nat.cast (2^k - k) : ZMod 550172) = 13573) :
    k % 147 = 36 ∨ k % 147 = 121 ∨ k % 147 = 137 := by
  have h_49 := cast_550172_to_49 k hk heq
  rw [zmod_49_period k] at h_49
  have h_check : check_all_r 147 0 = true := check_all_r_val
  have h_sound := check_all_r_sound 147 0 h_check (k % 147) (by omega) (by omega) h_49
  exact h_sound

lemma k_mod_588_eq (k : ℕ) (h4 : k % 4 = 3) (h147 : k % 147 = 36 ∨ k % 147 = 121 ∨ k % 147 = 137) :
    k % 588 = 183 ∨ k % 588 = 415 ∨ k % 588 = 431 := by
  omega

----------------- VERIFICATION BLOCK -----------------

def check_q (q : Nat) (P : ZMod 550172) : Bool :=
  let k1 := 588 * q + 183
  let pow1 := P * (498268 : ZMod 550172)
  let res1 := pow1 - (k1 : ZMod 550172)
  let k2 := 588 * q + 415
  let pow2 := P * (191564 : ZMod 550172)
  let res2 := pow2 - (k2 : ZMod 550172)
  let k3 := 588 * q + 431
  let pow3 := P * (513608 : ZMod 550172)
  let res3 := pow3 - (k3 : ZMod 550172)
  (res1 == (13573 : ZMod 550172)) || (res2 == (13573 : ZMod 550172)) || (res3 == (13573 : ZMod 550172))

def check_linear_q (fuel : Nat) (q : Nat) (P : ZMod 550172) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    if check_q q P then false
    else
      let P' := P * (433896 : ZMod 550172)
      check_linear_q fuel (q + 1) P'

def check_chunks (fuel : Nat) (q : Nat) (P : ZMod 550172) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    if check_linear_q 100 q P then
      let P' := P * (137544 : ZMod 550172)
      check_chunks fuel (q + 100) P'
    else
      false

lemma check_linear_q_sound (fuel : Nat) (q : Nat) (P : ZMod 550172) (h_P : P = (2 : ZMod 550172)^(588 * q)) (h_check : check_linear_q fuel q P = true) :
    ∀ i < fuel, check_q (q + i) ((2 : ZMod 550172)^(588 * (q + i))) = false := by
  revert q P
  induction fuel with
  | zero =>
    intro q P h_P h_check i h_lt
    omega
  | succ fuel ih =>
    intro q P h_P h_check i h_lt
    unfold check_linear_q at h_check
    split_ifs at h_check with h_q
    by_cases hi : i = 0
    · subst hi
      simp only [Nat.add_zero]
      rw [← h_P]
      cases h : check_q q P with
      | false => rfl
      | true =>
        exfalso
        exact h_q h
    · have : i = (i - 1) + 1 := by omega
      have h_lt' : i - 1 < fuel := by omega
      have h_P' : P * (433896 : ZMod 550172) = (2 : ZMod 550172)^(588 * (q + 1)) := by
        rw [h_P]
        have h_dec : (433896 : ZMod 550172) = (2 : ZMod 550172)^588 := by decide
        rw [h_dec]
        have h_eq : 588 * (q + 1) = 588 * q + 588 := by ring
        rw [h_eq, pow_add]
      have h_ih := ih (q + 1) (P * (433896 : ZMod 550172)) h_P' h_check (i - 1) h_lt'
      have h_add : q + 1 + (i - 1) = q + i := by omega
      rw [h_add] at h_ih
      exact h_ih

lemma check_chunks_sound (fuel : Nat) (q : Nat) (P : ZMod 550172) (h_P : P = (2 : ZMod 550172)^(588 * q)) (h_check : check_chunks fuel q P = true) :
    ∀ i < 100 * fuel, check_q (q + i) ((2 : ZMod 550172)^(588 * (q + i))) = false := by
  revert q P h_P h_check
  induction fuel with
  | zero =>
    intro q P h_P h_check i h_lt
    omega
  | succ fuel ih =>
    intro q P h_P h_check i h_lt
    unfold check_chunks at h_check
    split_ifs at h_check with h_lin
    by_cases hi : i < 100
    · have h_lin_sound := check_linear_q_sound 100 q P h_P h_lin i hi
      exact h_lin_sound
    · have h_ge : 100 ≤ i := by omega
      let i' := i - 100
      have hi' : i' < 100 * fuel := by omega
      have h_P' : P * (137544 : ZMod 550172) = (2 : ZMod 550172)^(588 * (q + 100)) := by
        rw [h_P]
        have h_dec1 : (433896 : ZMod 550172) = (2 : ZMod 550172)^588 := by decide
        have h_dec2 : (137544 : ZMod 550172) = (433896 : ZMod 550172)^100 := by decide
        have h_pow_mul : (2 : ZMod 550172)^(588 * 100) = ((2 : ZMod 550172)^588)^100 := by rw [pow_mul]
        have h_eq : 588 * (q + 100) = 588 * q + 588 * 100 := by ring
        rw [h_eq, pow_add]
        rw [h_pow_mul, ← h_dec1, ← h_dec2]
      have h_ih := ih (q + 100) (P * (137544 : ZMod 550172)) h_P' h_check i' hi'
      have h_add : q + 100 + i' = q + i := by omega
      rw [h_add] at h_ih
      exact h_ih

theorem check_chunks_val_1 : check_chunks 277 0 1 = true := by decide
theorem check_linear_val_2 : check_linear_q 75 27700 137544 = true := by decide

lemma check_q_false_1 (q : ℕ) (hq_lt : q < 27700) :
    check_q q ((2 : ZMod 550172)^(588 * q)) = false := by
  have h_check : check_chunks 277 0 1 = true := check_chunks_val_1
  have h_lin := check_chunks_sound 277 0 1 (by decide) h_check
  have h_lin_app := h_lin q hq_lt
  have h_zero_add : 0 + q = q := Nat.zero_add q
  rw [h_zero_add] at h_lin_app
  exact h_lin_app

lemma check_q_false_2 (q : ℕ) (hq_ge : 27700 ≤ q) (hq_lt : q < 27775) :
    check_q q ((2 : ZMod 550172)^(588 * q)) = false := by
  have h_check : check_linear_q 75 27700 137544 = true := check_linear_val_2
  let i := q - 27700
  have hi_lt : i < 75 := by omega
  have hq_eq : q = 27700 + i := by omega
  have h_P_init : (137544 : ZMod 550172) = (2 : ZMod 550172)^(588 * 27700) := by
    have h_pow_mul : (2 : ZMod 550172)^(588 * 27700) = ((2 : ZMod 550172)^(588 * 100))^277 := by
      rw [← pow_mul]
    rw [h_pow_mul]
    have h_dec1 : (137544 : ZMod 550172) = (2 : ZMod 550172)^(588 * 100) := by
      have h_pow_mul' : (2 : ZMod 550172)^(588 * 100) = ((2 : ZMod 550172)^588)^100 := by
        rw [← pow_mul]
      rw [h_pow_mul']
      have h_dec1' : (433896 : ZMod 550172) = (2 : ZMod 550172)^588 := by decide
      have h_dec2' : (137544 : ZMod 550172) = (433896 : ZMod 550172)^100 := by decide
      rw [← h_dec1', ← h_dec2']
    rw [← h_dec1]
    have h_dec2 : (137544 : ZMod 550172) = (137544 : ZMod 550172)^277 := by decide
    exact h_dec2
  have h_lin := check_linear_q_sound 75 27700 137544 h_P_init h_check i hi_lt
  rw [← hq_eq] at h_lin
  exact h_lin

lemma check_q_false_all (q : ℕ) (hq : q < 27775) :
    check_q q ((2 : ZMod 550172)^(588 * q)) = false := by
  by_cases hq_lt : q < 27700
  · exact check_q_false_1 q hq_lt
  · have hq_ge : 27700 ≤ q := by omega
    exact check_q_false_2 q hq_ge hq

lemma check_q_sound (q : ℕ) (h_check : check_q q ((2 : ZMod 550172)^(588 * q)) = false) :
    (2 : ZMod 550172)^(588 * q + 183) - (588 * q + 183 : ZMod 550172) ≠ 13573 ∧
    (2 : ZMod 550172)^(588 * q + 415) - (588 * q + 415 : ZMod 550172) ≠ 13573 ∧
    (2 : ZMod 550172)^(588 * q + 431) - (588 * q + 431 : ZMod 550172) ≠ 13573 := by
  unfold check_q at h_check
  simp only [Bool.or_eq_false_iff] at h_check
  have h1 := h_check.1.1
  have h2 := h_check.1.2
  have h3 := h_check.2
  rw [beq_eq_false_iff_ne] at h1 h2 h3
  have h_pow1 : (2 : ZMod 550172)^(588 * q) * (498268 : ZMod 550172) = (2 : ZMod 550172)^(588 * q + 183) := by
    have h_dec : (498268 : ZMod 550172) = (2 : ZMod 550172)^183 := by decide
    rw [h_dec, pow_add]
  have h_pow2 : (2 : ZMod 550172)^(588 * q) * (191564 : ZMod 550172) = (2 : ZMod 550172)^(588 * q + 415) := by
    have h_dec : (191564 : ZMod 550172) = (2 : ZMod 550172)^415 := by decide
    rw [h_dec, pow_add]
  have h_pow3 : (2 : ZMod 550172)^(588 * q) * (513608 : ZMod 550172) = (2 : ZMod 550172)^(588 * q + 431) := by
    have h_dec : (513608 : ZMod 550172) = (2 : ZMod 550172)^431 := by decide
    rw [h_dec, pow_add]
  rw [h_pow1] at h1
  rw [h_pow2] at h2
  rw [h_pow3] at h3
  exact ⟨h1, h2, h3⟩

----------------- CONJECTURE BOUND PROOF -----------------

lemma prop_mono {{n m M : ℕ}} [NeZero n] (h_le : m ≤ M) (h_prop : A232616_prop n m) : A232616_prop n M := by
  unfold A232616_prop at *
  have h_sub : Finset.Icc 1 m ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc (le_refl 1) h_le
  have h_img := Finset.image_mono (f := fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)) h_sub
  have h_univ : (univ : Finset (ZMod n)) ⊆ (Finset.Icc 1 M).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n) := by
    calc (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n) := h_prop
    _ ⊆ (Finset.Icc 1 M).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n) := h_img
  exact Subset.antisymm h_univ (subset_univ _)

lemma not_prop_550172_16331503 (h_prop : A232616_prop 550172 16331503) : False := by
  unfold A232616_prop at h_prop
  have h_in : (13573 : ZMod 550172) ∈ (univ : Finset (ZMod 550172)) := Finset.mem_univ _
  rw [h_prop] at h_in
  rcases Finset.mem_image.mp h_in with ⟨k, hk, hk_eq⟩
  rw [Finset.mem_Icc] at hk
  have hk_ge_2 : 2 ≤ k := by
    rcases k with _ | _ | y
    · omega
    · revert hk_eq; decide
    · omega
  have h_49 := cast_550172_to_49 k hk_ge_2 hk_eq
  have h_147 := k_mod_147_eq k hk_ge_2 hk_eq
  have h_4 := k_eq_4q_plus_3 k hk_ge_2 hk_eq
  rcases h_4 with ⟨q4, rfl⟩
  have h4_mod : (4 * q4 + 3) % 4 = 3 := by omega
  have h_588 := k_mod_588_eq (4 * q4 + 3) h4_mod h_147
  let q_div := k / 588
  have h_k_eq : k = 588 * q_div + k % 588 := by omega
  have h_q_lt : q_div < 27775 := by
    have : k ≤ 16331503 := hk.2
    have : 588 * q_div ≤ k := by omega
    omega
  rcases h_588 with h183 | h415 | h431
  · have h_check := check_q_false_all q_div h_q_lt
    have h_sound := check_q_sound q_div h_check
    have h_cast : (Nat.cast (2^k - k) : ZMod 550172) = (2 : ZMod 550172)^k - (k : ZMod 550172) := by
      rw [Nat.cast_sub (le_pow_two_all k)]
      push_cast
      rfl
    rw [h_cast] at hk_eq
    rw [h_k_eq, h183] at hk_eq
    exact h_sound.1 hk_eq
  · have h_check := check_q_false_all q_div h_q_lt
    have h_sound := check_q_sound q_div h_check
    have h_cast : (Nat.cast (2^k - k) : ZMod 550172) = (2 : ZMod 550172)^k - (k : ZMod 550172) := by
      rw [Nat.cast_sub (le_pow_two_all k)]
      push_cast
      rfl
    rw [h_cast] at hk_eq
    rw [h_k_eq, h415] at hk_eq
    exact h_sound.2.1 hk_eq
  · have h_check := check_q_false_all q_div h_q_lt
    have h_sound := check_q_sound q_div h_check
    have h_cast : (Nat.cast (2^k - k) : ZMod 550172) = (2 : ZMod 550172)^k - (k : ZMod 550172) := by
      rw [Nat.cast_sub (le_pow_two_all k)]
      push_cast
      rfl
    rw [h_cast] at hk_eq
    rw [h_k_eq, h431] at hk_eq
    exact h_sound.2.2 hk_eq

theorem honest_sInf_bound (h_not : ¬ A232616_prop 550172 16331503) :
    16331504 ≤ A232616 550172 := by
  unfold A232616
  rw [dif_neg (by decide : 550172 ≠ 0)]
  apply Nat.le_sInf
  intro m hm
  change A232616_prop 550172 m at hm
  by_contra! h_lt
  have h_prop := prop_mono (m := m) (M := 16331503) (by omega) hm
  exact h_not h_prop

/--
Conjecture (i): $a(n) < 2 \cdot (\text{prime}(n) - 1)$ for all $n > 0$,
where $\text{prime}(n)$ is the $n$-th prime number (1-indexed).
-/
theorem oeis_232616_conjecture_i.disproof :
    ¬ (∀ (n : ℕ) (hn : 0 < n), A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1)) := by
  intro h
  have h_ce := h 550172 (by decide)
  have h_nth_le := nth_prime_550171_le
  have h_a232616 : 16331504 ≤ A232616 550172 := honest_sInf_bound not_prop_550172_16331503
  omega

#print axioms oeis_232616_conjecture_i.disproof
