import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option exponentiation.threshold 10000000
set_option maxRecDepth 5000000
set_option maxHeartbeats 0

open Nat Set Finset

/-- A384237: Number of divisors $d$ of $n$ such that $d^d \equiv d \pmod n$. -/
def A384237 (n : ℕ) : ℕ :=
  (n.divisors.filter fun d : ℕ => (d ^ d) % n = d % n).card

def A384237_list (n : ℕ) : ℕ :=
  (((List.Ico 1 (n + 1)).filter (· ∣ n)).filter fun d => (d ^ d) % n = d % n).length

theorem A384237_eq_list (n : ℕ) : A384237 n = A384237_list n := by
  rfl

def pow_mod_loop (base exp mod acc : ℕ) : ℕ :=
  match exp with
  | 0 => acc % mod
  | exp + 1 => pow_mod_loop base exp mod (acc * base % mod)

theorem pow_mod_loop_eq (base exp mod acc : ℕ) :
  pow_mod_loop base exp mod acc = (acc * base ^ exp) % mod := by
  induction exp generalizing acc with
  | zero =>
    simp [pow_mod_loop]
  | succ exp ih =>
    unfold pow_mod_loop
    rw [ih]
    rw [pow_succ]
    have h1 : ((acc * base % mod) * base ^ exp) % mod = ((acc * base) * base ^ exp) % mod := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [h1]
    congr 1
    ring

def pow_mod_fast (base exp mod : ℕ) : ℕ :=
  pow_mod_loop base exp mod 1

theorem pow_mod_fast_eq (base exp mod : ℕ) : pow_mod_fast base exp mod = (base ^ exp) % mod := by
  unfold pow_mod_fast
  rw [pow_mod_loop_eq]
  rw [one_mul]

def A384237_fast (n : ℕ) : ℕ :=
  (((List.Ico 1 (n + 1)).filter fun d => n % d = 0).filter fun d => pow_mod_fast d d n = d % n).length

theorem A384237_eq_fast (n : ℕ) : A384237 n = A384237_fast n := by
  rw [A384237_eq_list]
  unfold A384237_list A384237_fast
  apply congrArg List.length
  have h_inner : (List.Ico 1 (n + 1)).filter (· ∣ n) = (List.Ico 1 (n + 1)).filter fun d => n % d = 0 := by
    apply List.filter_congr
    intro x _
    simp only [decide_eq_decide]
    exact Nat.dvd_iff_mod_eq_zero
  rw [h_inner]
  apply List.filter_congr
  intro x _
  simp only [decide_eq_decide]
  rw [pow_mod_fast_eq]



def A384237_direct_loop (n d acc : ℕ) : ℕ :=
  match d with
  | 0 => acc
  | d + 1 =>
    let acc' := if n % (d + 1) = 0 then
                  if pow_mod_fast (d + 1) (d + 1) n = (d + 1) % n then acc + 1
                  else acc
                else acc
    A384237_direct_loop n d acc'

theorem A384237_direct_loop_eq (n d acc : ℕ) :
  A384237_direct_loop n d acc = acc + (((List.Ico 1 (d + 1)).filter fun x => n % x = 0).filter fun x => pow_mod_fast x x n = x % n).length := by
  induction d generalizing acc with
  | zero =>
    simp [A384237_direct_loop]
  | succ d ih =>
    unfold A384237_direct_loop
    rw [ih]
    have h_split : List.Ico 1 (d + 1 + 1) = List.Ico 1 (d + 1) ++ [d + 1] := by
      apply List.Ico.succ_top
      omega
    rw [h_split, List.filter_append, List.filter_append]
    simp only [List.length_append]
    split_ifs with h1 h2
    · simp [h1, h2]; omega
    · simp [h1, h2]
    · simp [h1]

def A384237_direct (n : ℕ) : ℕ :=
  A384237_direct_loop n n 0

theorem A384237_direct_eq_fast (n : ℕ) :
  A384237_direct n = A384237_fast n := by
  unfold A384237_direct A384237_fast
  rw [A384237_direct_loop_eq]
  rw [zero_add]


theorem A384237_filter_coprime {n : ℕ} {d : ℕ} (hd : d ∈ n.divisors) (h_eq : (d ^ d) % n = d % n) :
  Nat.Coprime d (n / d) := by
  have h_mem := Nat.mem_divisors.mp hd
  have h_div := h_mem.1
  have hn_ne := h_mem.2
  have hn_pos : n > 0 := Nat.pos_of_ne_zero hn_ne
  have hd_pos : d > 0 := by
    by_contra! h_zero
    have : d = 0 := Nat.le_zero.mp h_zero
    subst this
    simp at h_div
    subst h_div
    contradiction
  let k := n / d
  have h_mul : n = d * k := (Nat.mul_div_cancel' h_div).symm
  have h_mul_pos : d * k > 0 := by
    rw [← h_mul]
    exact hn_pos
  have hk_pos : k > 0 := by
    by_contra! h_zero
    have : k = 0 := Nat.le_zero.mp h_zero
    have h_dz : d * 0 = 0 := mul_zero d
    rw [this, h_dz] at h_mul_pos
    contradiction
  -- now show Nat.Coprime d k
  unfold Nat.Coprime
  let g := d.gcd k
  have hg_dvd_d : g ∣ d := d.gcd_dvd_left k
  have hg_dvd_k : g ∣ k := d.gcd_dvd_right k
  have hg_pos : g > 0 := Nat.gcd_pos_of_pos_left k hd_pos
  -- if d = 1, then g = 1
  by_cases hd1 : d = 1
  · subst hd1
    simp
  · have hd_gt1 : d > 1 := by omega
    have h_pow_eq : d ^ d = d * d ^ (d - 1) := by
      have h_eq_sub : d = d - 1 + 1 := (Nat.sub_add_cancel (by omega)).symm
      nth_rw 2 [h_eq_sub]
      rw [pow_succ, mul_comm]
    have h_mul_mod_d : (d * d ^ (d - 1)) % (d * k) = d * (d ^ (d - 1) % k) := Nat.mul_mod_mul_left d (d ^ (d - 1)) k
    have h_mul_mod_1 : d % (d * k) = d * (1 % k) := by
      have h_d1 : d = d * 1 := (mul_one d).symm
      nth_rw 1 [h_d1]
      rw [Nat.mul_mod_mul_left]
    rw [← h_mul] at h_mul_mod_d h_mul_mod_1
    rw [h_pow_eq] at h_eq
    rw [h_mul_mod_d, h_mul_mod_1] at h_eq
    have h_eq_cancel : d ^ (d - 1) % k = 1 % k := Nat.eq_of_mul_eq_mul_left hd_pos h_eq
    -- now we have d ^ (d - 1) % k = 1 % k
    -- we want to show g = 1, since g ∣ 1 we are done
    -- we show g ∣ 1
    have h_mod_g : (d ^ (d - 1) % k) % g = (1 % k) % g := by rw [h_eq_cancel]
    rw [Nat.mod_mod_of_dvd _ hg_dvd_k] at h_mod_g
    rw [Nat.mod_mod_of_dvd _ hg_dvd_k] at h_mod_g
    -- so d ^ (d - 1) % g = 1 % g
    -- but g ∣ d and d - 1 >= 1, so g ∣ d ^ (d - 1)
    have hd_sub_pos : d - 1 ≥ 1 := by omega
    have hg_dvd_pow : g ∣ d ^ (d - 1) := dvd_pow hg_dvd_d (by omega)
    have h_pow_g : d ^ (d - 1) % g = 0 := Nat.mod_eq_zero_of_dvd hg_dvd_pow
    rw [h_pow_g] at h_mod_g
    -- 0 = 1 % g
    have hg_dvd_one : g ∣ 1 := Nat.dvd_of_mod_eq_zero h_mod_g.symm
    exact Nat.eq_one_of_dvd_one hg_dvd_one


def count_unitary_divs_loop (n d acc : ℕ) : ℕ :=
  match d with
  | 0 => acc
  | d + 1 =>
    let acc' := if n % (d + 1) = 0 then
                  if (d + 1).gcd (n / (d + 1)) = 1 then acc + 1
                  else acc
                else acc
    count_unitary_divs_loop n d acc'

theorem count_unitary_divs_loop_eq (n d acc : ℕ) :
  count_unitary_divs_loop n d acc = acc + (((List.Ico 1 (d + 1)).filter fun x => n % x = 0).filter fun x => x.gcd (n / x) = 1).length := by
  induction d generalizing acc with
  | zero =>
    simp [count_unitary_divs_loop]
  | succ d ih =>
    unfold count_unitary_divs_loop
    rw [ih]
    have h_split : List.Ico 1 (d + 1 + 1) = List.Ico 1 (d + 1) ++ [d + 1] := by
      apply List.Ico.succ_top
      omega
    rw [h_split, List.filter_append, List.filter_append]
    simp only [List.length_append]
    split_ifs with h1 h2
    · simp [h1, h2]; omega
    · simp [h1, h2]
    · simp [h1]

def count_unitary_divs (n : ℕ) : ℕ :=
  count_unitary_divs_loop n n 0

theorem count_unitary_divs_eq (n : ℕ) :
  count_unitary_divs n = (((List.Ico 1 (n + 1)).filter fun x => n % x = 0).filter fun x => x.gcd (n / x) = 1).length := by
  unfold count_unitary_divs
  rw [count_unitary_divs_loop_eq]
  rw [zero_add]

theorem count_unitary_divs_eq_card (n : ℕ) :
  count_unitary_divs n = (n.divisors.filter fun d => d.gcd (n / d) = 1).card := by
  rw [count_unitary_divs_eq]
  have h_inner : (List.Ico 1 (n + 1)).filter (· ∣ n) = (List.Ico 1 (n + 1)).filter fun d => n % d = 0 := by
    apply List.filter_congr
    intro x _
    simp only [decide_eq_decide]
    exact Nat.dvd_iff_mod_eq_zero
  rw [← h_inner]
  rfl

theorem A384237_le_unitary_bound (n : ℕ) : A384237 n ≤ count_unitary_divs n := by
  rw [count_unitary_divs_eq_card]
  unfold A384237
  apply Finset.card_le_card
  intro d hd
  rw [Finset.mem_filter] at hd ⊢
  rcases hd with ⟨hd_div, hd_eq⟩
  refine ⟨hd_div, ?_⟩
  have h_coprime : Nat.Coprime d (n / d) := A384237_filter_coprime hd_div hd_eq
  exact h_coprime


def count_unitary_divs_sqrt_loop (n d acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if d * d > n then acc
    else
      let acc' := if n % d = 0 then
                    if d.gcd (n / d) = 1 then
                      if d * d = n then acc + 1
                      else acc + 2
                    else acc
                  else acc
      count_unitary_divs_sqrt_loop n (d + 1) acc' fuel

def count_unitary_divs_sqrt (n : ℕ) : ℕ :=
  count_unitary_divs_sqrt_loop n 1 0 n

theorem count_eq_all_0 : ∀ k < 20, count_unitary_divs k = count_unitary_divs_sqrt k := by decide
theorem count_eq_all_1 : ∀ k < 20, count_unitary_divs (20 + k) = count_unitary_divs_sqrt (20 + k) := by decide
theorem count_eq_all_2 : ∀ k < 20, count_unitary_divs (40 + k) = count_unitary_divs_sqrt (40 + k) := by decide
theorem count_eq_all_3 : ∀ k < 20, count_unitary_divs (60 + k) = count_unitary_divs_sqrt (60 + k) := by decide
theorem count_eq_all_4 : ∀ k < 20, count_unitary_divs (80 + k) = count_unitary_divs_sqrt (80 + k) := by decide
theorem count_eq_all_5 : ∀ k < 20, count_unitary_divs (100 + k) = count_unitary_divs_sqrt (100 + k) := by decide
theorem count_eq_all_6 : ∀ k < 20, count_unitary_divs (120 + k) = count_unitary_divs_sqrt (120 + k) := by decide
theorem count_eq_all_7 : ∀ k < 20, count_unitary_divs (140 + k) = count_unitary_divs_sqrt (140 + k) := by decide
theorem count_eq_all_8 : ∀ k < 20, count_unitary_divs (160 + k) = count_unitary_divs_sqrt (160 + k) := by decide
theorem count_eq_all_9 : ∀ k < 20, count_unitary_divs (180 + k) = count_unitary_divs_sqrt (180 + k) := by decide
theorem count_eq_all_10 : ∀ k < 20, count_unitary_divs (200 + k) = count_unitary_divs_sqrt (200 + k) := by decide
theorem count_eq_all_11 : ∀ k < 20, count_unitary_divs (220 + k) = count_unitary_divs_sqrt (220 + k) := by decide
theorem count_eq_all_12 : ∀ k < 20, count_unitary_divs (240 + k) = count_unitary_divs_sqrt (240 + k) := by decide
theorem count_eq_all_13 : ∀ k < 20, count_unitary_divs (260 + k) = count_unitary_divs_sqrt (260 + k) := by decide
theorem count_eq_all_14 : ∀ k < 20, count_unitary_divs (280 + k) = count_unitary_divs_sqrt (280 + k) := by decide
theorem count_eq_all_15 : ∀ k < 20, count_unitary_divs (300 + k) = count_unitary_divs_sqrt (300 + k) := by decide
theorem count_eq_all_16 : ∀ k < 20, count_unitary_divs (320 + k) = count_unitary_divs_sqrt (320 + k) := by decide
theorem count_eq_all_17 : ∀ k < 20, count_unitary_divs (340 + k) = count_unitary_divs_sqrt (340 + k) := by decide
theorem count_eq_all_18 : ∀ k < 20, count_unitary_divs (360 + k) = count_unitary_divs_sqrt (360 + k) := by decide
theorem count_eq_all_19 : ∀ k < 20, count_unitary_divs (380 + k) = count_unitary_divs_sqrt (380 + k) := by decide
theorem count_eq_all_20 : ∀ k < 20, count_unitary_divs (400 + k) = count_unitary_divs_sqrt (400 + k) := by decide
theorem count_eq_all_21 : ∀ k < 20, count_unitary_divs (420 + k) = count_unitary_divs_sqrt (420 + k) := by decide
theorem count_eq_all_22 : ∀ k < 20, count_unitary_divs (440 + k) = count_unitary_divs_sqrt (440 + k) := by decide
theorem count_eq_all_23 : ∀ k < 20, count_unitary_divs (460 + k) = count_unitary_divs_sqrt (460 + k) := by decide
theorem count_eq_all_24 : ∀ k < 20, count_unitary_divs (480 + k) = count_unitary_divs_sqrt (480 + k) := by decide
theorem count_eq_all_25 : ∀ k < 20, count_unitary_divs (500 + k) = count_unitary_divs_sqrt (500 + k) := by decide
theorem count_eq_all_26 : ∀ k < 20, count_unitary_divs (520 + k) = count_unitary_divs_sqrt (520 + k) := by decide
theorem count_eq_all_27 : ∀ k < 20, count_unitary_divs (540 + k) = count_unitary_divs_sqrt (540 + k) := by decide
theorem count_eq_all_28 : ∀ k < 20, count_unitary_divs (560 + k) = count_unitary_divs_sqrt (560 + k) := by decide
theorem count_eq_all_29 : ∀ k < 20, count_unitary_divs (580 + k) = count_unitary_divs_sqrt (580 + k) := by decide
theorem count_eq_all_30 : ∀ k < 20, count_unitary_divs (600 + k) = count_unitary_divs_sqrt (600 + k) := by decide
theorem count_eq_all_31 : ∀ k < 20, count_unitary_divs (620 + k) = count_unitary_divs_sqrt (620 + k) := by decide
theorem count_eq_all_32 : ∀ k < 20, count_unitary_divs (640 + k) = count_unitary_divs_sqrt (640 + k) := by decide
theorem count_eq_all_33 : ∀ k < 20, count_unitary_divs (660 + k) = count_unitary_divs_sqrt (660 + k) := by decide
theorem count_eq_all_34 : ∀ k < 20, count_unitary_divs (680 + k) = count_unitary_divs_sqrt (680 + k) := by decide
theorem count_eq_all_35 : ∀ k < 20, count_unitary_divs (700 + k) = count_unitary_divs_sqrt (700 + k) := by decide
theorem count_eq_all_36 : ∀ k < 20, count_unitary_divs (720 + k) = count_unitary_divs_sqrt (720 + k) := by decide
theorem count_eq_all_37 : ∀ k < 20, count_unitary_divs (740 + k) = count_unitary_divs_sqrt (740 + k) := by decide
theorem count_eq_all_38 : ∀ k < 20, count_unitary_divs (760 + k) = count_unitary_divs_sqrt (760 + k) := by decide
theorem count_eq_all_39 : ∀ k < 20, count_unitary_divs (780 + k) = count_unitary_divs_sqrt (780 + k) := by decide
theorem count_eq_all_40 : ∀ k < 20, count_unitary_divs (800 + k) = count_unitary_divs_sqrt (800 + k) := by decide
theorem count_eq_all_41 : ∀ k < 20, count_unitary_divs (820 + k) = count_unitary_divs_sqrt (820 + k) := by decide
theorem count_eq_all_42 : ∀ k < 20, count_unitary_divs (840 + k) = count_unitary_divs_sqrt (840 + k) := by decide
theorem count_eq_all_43 : ∀ k < 20, count_unitary_divs (860 + k) = count_unitary_divs_sqrt (860 + k) := by decide
theorem count_eq_all_44 : ∀ k < 20, count_unitary_divs (880 + k) = count_unitary_divs_sqrt (880 + k) := by decide
theorem count_eq_all_45 : ∀ k < 20, count_unitary_divs (900 + k) = count_unitary_divs_sqrt (900 + k) := by decide
theorem count_eq_all_46 : ∀ k < 20, count_unitary_divs (920 + k) = count_unitary_divs_sqrt (920 + k) := by decide
theorem count_eq_all_47 : ∀ k < 20, count_unitary_divs (940 + k) = count_unitary_divs_sqrt (940 + k) := by decide
theorem count_eq_all_48 : ∀ k < 20, count_unitary_divs (960 + k) = count_unitary_divs_sqrt (960 + k) := by decide
theorem count_eq_all_49 : ∀ k < 20, count_unitary_divs (980 + k) = count_unitary_divs_sqrt (980 + k) := by decide
theorem count_eq_all_50 : ∀ k < 20, count_unitary_divs (1000 + k) = count_unitary_divs_sqrt (1000 + k) := by decide
theorem count_eq_all_51 : ∀ k < 20, count_unitary_divs (1020 + k) = count_unitary_divs_sqrt (1020 + k) := by decide
theorem count_eq_all_52 : ∀ k < 20, count_unitary_divs (1040 + k) = count_unitary_divs_sqrt (1040 + k) := by decide
theorem count_eq_all_53 : ∀ k < 20, count_unitary_divs (1060 + k) = count_unitary_divs_sqrt (1060 + k) := by decide
theorem count_eq_all_54 : ∀ k < 20, count_unitary_divs (1080 + k) = count_unitary_divs_sqrt (1080 + k) := by decide
theorem count_eq_all_55 : ∀ k < 20, count_unitary_divs (1100 + k) = count_unitary_divs_sqrt (1100 + k) := by decide
theorem count_eq_all_56 : ∀ k < 20, count_unitary_divs (1120 + k) = count_unitary_divs_sqrt (1120 + k) := by decide
theorem count_eq_all_57 : ∀ k < 20, count_unitary_divs (1140 + k) = count_unitary_divs_sqrt (1140 + k) := by decide
theorem count_eq_all_58 : ∀ k < 20, count_unitary_divs (1160 + k) = count_unitary_divs_sqrt (1160 + k) := by decide
theorem count_eq_all_59 : ∀ k < 20, count_unitary_divs (1180 + k) = count_unitary_divs_sqrt (1180 + k) := by decide
theorem count_eq_all_60 : ∀ k < 20, count_unitary_divs (1200 + k) = count_unitary_divs_sqrt (1200 + k) := by decide
theorem count_eq_all_61 : ∀ k < 20, count_unitary_divs (1220 + k) = count_unitary_divs_sqrt (1220 + k) := by decide
theorem count_eq_all_62 : ∀ k < 20, count_unitary_divs (1240 + k) = count_unitary_divs_sqrt (1240 + k) := by decide
theorem count_eq_all_63 : ∀ k < 20, count_unitary_divs (1260 + k) = count_unitary_divs_sqrt (1260 + k) := by decide
theorem count_eq_all_64 : ∀ k < 20, count_unitary_divs (1280 + k) = count_unitary_divs_sqrt (1280 + k) := by decide
theorem count_eq_all_65 : ∀ k < 20, count_unitary_divs (1300 + k) = count_unitary_divs_sqrt (1300 + k) := by decide
theorem count_eq_all_66 : ∀ k < 20, count_unitary_divs (1320 + k) = count_unitary_divs_sqrt (1320 + k) := by decide
theorem count_eq_all_67 : ∀ k < 20, count_unitary_divs (1340 + k) = count_unitary_divs_sqrt (1340 + k) := by decide
theorem count_eq_all_68 : ∀ k < 20, count_unitary_divs (1360 + k) = count_unitary_divs_sqrt (1360 + k) := by decide
theorem count_eq_all_69 : ∀ k < 20, count_unitary_divs (1380 + k) = count_unitary_divs_sqrt (1380 + k) := by decide
theorem count_eq_all_70 : ∀ k < 20, count_unitary_divs (1400 + k) = count_unitary_divs_sqrt (1400 + k) := by decide
theorem count_eq_all_71 : ∀ k < 20, count_unitary_divs (1420 + k) = count_unitary_divs_sqrt (1420 + k) := by decide
theorem count_eq_all_72 : ∀ k < 20, count_unitary_divs (1440 + k) = count_unitary_divs_sqrt (1440 + k) := by decide
theorem count_eq_all_73 : ∀ k < 20, count_unitary_divs (1460 + k) = count_unitary_divs_sqrt (1460 + k) := by decide
theorem count_eq_all_74 : ∀ k < 20, count_unitary_divs (1480 + k) = count_unitary_divs_sqrt (1480 + k) := by decide
theorem count_eq_all_75 : ∀ k < 20, count_unitary_divs (1500 + k) = count_unitary_divs_sqrt (1500 + k) := by decide
theorem count_eq_all_76 : ∀ k < 20, count_unitary_divs (1520 + k) = count_unitary_divs_sqrt (1520 + k) := by decide
theorem count_eq_all_77 : ∀ k < 20, count_unitary_divs (1540 + k) = count_unitary_divs_sqrt (1540 + k) := by decide
theorem count_eq_all_78 : ∀ k < 20, count_unitary_divs (1560 + k) = count_unitary_divs_sqrt (1560 + k) := by decide
theorem count_eq_all_79 : ∀ k < 20, count_unitary_divs (1580 + k) = count_unitary_divs_sqrt (1580 + k) := by decide
theorem count_eq_all_80 : ∀ k < 20, count_unitary_divs (1600 + k) = count_unitary_divs_sqrt (1600 + k) := by decide
theorem count_eq_all_81 : ∀ k < 20, count_unitary_divs (1620 + k) = count_unitary_divs_sqrt (1620 + k) := by decide
theorem count_eq_all_82 : ∀ k < 20, count_unitary_divs (1640 + k) = count_unitary_divs_sqrt (1640 + k) := by decide
theorem count_eq_all_83 : ∀ k < 20, count_unitary_divs (1660 + k) = count_unitary_divs_sqrt (1660 + k) := by decide
theorem count_eq_all_84 : ∀ k < 20, count_unitary_divs (1680 + k) = count_unitary_divs_sqrt (1680 + k) := by decide
theorem count_eq_all_85 : ∀ k < 20, count_unitary_divs (1700 + k) = count_unitary_divs_sqrt (1700 + k) := by decide
theorem count_eq_all_86 : ∀ k < 20, count_unitary_divs (1720 + k) = count_unitary_divs_sqrt (1720 + k) := by decide
theorem count_eq_all_87 : ∀ k < 20, count_unitary_divs (1740 + k) = count_unitary_divs_sqrt (1740 + k) := by decide
theorem count_eq_all_88 : ∀ k < 20, count_unitary_divs (1760 + k) = count_unitary_divs_sqrt (1760 + k) := by decide
theorem count_eq_all_89 : ∀ k < 20, count_unitary_divs (1780 + k) = count_unitary_divs_sqrt (1780 + k) := by decide
theorem count_eq_all_90 : ∀ k < 20, count_unitary_divs (1800 + k) = count_unitary_divs_sqrt (1800 + k) := by decide
theorem count_eq_all_91 : ∀ k < 20, count_unitary_divs (1820 + k) = count_unitary_divs_sqrt (1820 + k) := by decide
theorem count_eq_all_92 : ∀ k < 20, count_unitary_divs (1840 + k) = count_unitary_divs_sqrt (1840 + k) := by decide
theorem count_eq_all_93 : ∀ k < 20, count_unitary_divs (1860 + k) = count_unitary_divs_sqrt (1860 + k) := by decide
theorem count_eq_all_94 : ∀ k < 20, count_unitary_divs (1880 + k) = count_unitary_divs_sqrt (1880 + k) := by decide
theorem count_eq_all_95 : ∀ k < 20, count_unitary_divs (1900 + k) = count_unitary_divs_sqrt (1900 + k) := by decide
theorem count_eq_all_96 : ∀ k < 20, count_unitary_divs (1920 + k) = count_unitary_divs_sqrt (1920 + k) := by decide
theorem count_eq_all_97 : ∀ k < 20, count_unitary_divs (1940 + k) = count_unitary_divs_sqrt (1940 + k) := by decide
theorem count_eq_all_98 : ∀ k < 20, count_unitary_divs (1960 + k) = count_unitary_divs_sqrt (1960 + k) := by decide
theorem count_eq_all_99 : ∀ k < 20, count_unitary_divs (1980 + k) = count_unitary_divs_sqrt (1980 + k) := by decide
theorem count_eq_all_100 : ∀ k < 20, count_unitary_divs (2000 + k) = count_unitary_divs_sqrt (2000 + k) := by decide
theorem count_eq_all_101 : ∀ k < 20, count_unitary_divs (2020 + k) = count_unitary_divs_sqrt (2020 + k) := by decide
theorem count_eq_all_102 : ∀ k < 20, count_unitary_divs (2040 + k) = count_unitary_divs_sqrt (2040 + k) := by decide
theorem count_eq_all_103 : ∀ k < 20, count_unitary_divs (2060 + k) = count_unitary_divs_sqrt (2060 + k) := by decide
theorem count_eq_all_104 : ∀ k < 20, count_unitary_divs (2080 + k) = count_unitary_divs_sqrt (2080 + k) := by decide
theorem count_eq_all_105 : ∀ k < 20, count_unitary_divs (2100 + k) = count_unitary_divs_sqrt (2100 + k) := by decide
theorem count_eq_all_106 : ∀ k < 20, count_unitary_divs (2120 + k) = count_unitary_divs_sqrt (2120 + k) := by decide
theorem count_eq_all_107 : ∀ k < 20, count_unitary_divs (2140 + k) = count_unitary_divs_sqrt (2140 + k) := by decide
theorem count_eq_all_108 : ∀ k < 20, count_unitary_divs (2160 + k) = count_unitary_divs_sqrt (2160 + k) := by decide
theorem count_eq_all_109 : ∀ k < 20, count_unitary_divs (2180 + k) = count_unitary_divs_sqrt (2180 + k) := by decide
theorem count_eq_all_110 : ∀ k < 20, count_unitary_divs (2200 + k) = count_unitary_divs_sqrt (2200 + k) := by decide
theorem count_eq_all_111 : ∀ k < 20, count_unitary_divs (2220 + k) = count_unitary_divs_sqrt (2220 + k) := by decide
theorem count_eq_all_112 : ∀ k < 20, count_unitary_divs (2240 + k) = count_unitary_divs_sqrt (2240 + k) := by decide
theorem count_eq_all_113 : ∀ k < 20, count_unitary_divs (2260 + k) = count_unitary_divs_sqrt (2260 + k) := by decide
theorem count_eq_all_114 : ∀ k < 20, count_unitary_divs (2280 + k) = count_unitary_divs_sqrt (2280 + k) := by decide
theorem count_eq_all_115 : ∀ k < 10, count_unitary_divs (2300 + k) = count_unitary_divs_sqrt (2300 + k) := by decide

theorem count_eq_all (m : ℕ) (h_lt : m < 2310) : count_unitary_divs m = count_unitary_divs_sqrt m := by
  by_cases h_20 : m < 20
  · exact count_eq_all_0 m h_20
  by_cases h_40 : m < 40
  · have h_k : m - 20 < 20 := by omega
    have h_eq : m = 20 + (m - 20) := by omega
    rw [h_eq]
    exact count_eq_all_1 (m - 20) h_k
  by_cases h_60 : m < 60
  · have h_k : m - 40 < 20 := by omega
    have h_eq : m = 40 + (m - 40) := by omega
    rw [h_eq]
    exact count_eq_all_2 (m - 40) h_k
  by_cases h_80 : m < 80
  · have h_k : m - 60 < 20 := by omega
    have h_eq : m = 60 + (m - 60) := by omega
    rw [h_eq]
    exact count_eq_all_3 (m - 60) h_k
  by_cases h_100 : m < 100
  · have h_k : m - 80 < 20 := by omega
    have h_eq : m = 80 + (m - 80) := by omega
    rw [h_eq]
    exact count_eq_all_4 (m - 80) h_k
  by_cases h_120 : m < 120
  · have h_k : m - 100 < 20 := by omega
    have h_eq : m = 100 + (m - 100) := by omega
    rw [h_eq]
    exact count_eq_all_5 (m - 100) h_k
  by_cases h_140 : m < 140
  · have h_k : m - 120 < 20 := by omega
    have h_eq : m = 120 + (m - 120) := by omega
    rw [h_eq]
    exact count_eq_all_6 (m - 120) h_k
  by_cases h_160 : m < 160
  · have h_k : m - 140 < 20 := by omega
    have h_eq : m = 140 + (m - 140) := by omega
    rw [h_eq]
    exact count_eq_all_7 (m - 140) h_k
  by_cases h_180 : m < 180
  · have h_k : m - 160 < 20 := by omega
    have h_eq : m = 160 + (m - 160) := by omega
    rw [h_eq]
    exact count_eq_all_8 (m - 160) h_k
  by_cases h_200 : m < 200
  · have h_k : m - 180 < 20 := by omega
    have h_eq : m = 180 + (m - 180) := by omega
    rw [h_eq]
    exact count_eq_all_9 (m - 180) h_k
  by_cases h_220 : m < 220
  · have h_k : m - 200 < 20 := by omega
    have h_eq : m = 200 + (m - 200) := by omega
    rw [h_eq]
    exact count_eq_all_10 (m - 200) h_k
  by_cases h_240 : m < 240
  · have h_k : m - 220 < 20 := by omega
    have h_eq : m = 220 + (m - 220) := by omega
    rw [h_eq]
    exact count_eq_all_11 (m - 220) h_k
  by_cases h_260 : m < 260
  · have h_k : m - 240 < 20 := by omega
    have h_eq : m = 240 + (m - 240) := by omega
    rw [h_eq]
    exact count_eq_all_12 (m - 240) h_k
  by_cases h_280 : m < 280
  · have h_k : m - 260 < 20 := by omega
    have h_eq : m = 260 + (m - 260) := by omega
    rw [h_eq]
    exact count_eq_all_13 (m - 260) h_k
  by_cases h_300 : m < 300
  · have h_k : m - 280 < 20 := by omega
    have h_eq : m = 280 + (m - 280) := by omega
    rw [h_eq]
    exact count_eq_all_14 (m - 280) h_k
  by_cases h_320 : m < 320
  · have h_k : m - 300 < 20 := by omega
    have h_eq : m = 300 + (m - 300) := by omega
    rw [h_eq]
    exact count_eq_all_15 (m - 300) h_k
  by_cases h_340 : m < 340
  · have h_k : m - 320 < 20 := by omega
    have h_eq : m = 320 + (m - 320) := by omega
    rw [h_eq]
    exact count_eq_all_16 (m - 320) h_k
  by_cases h_360 : m < 360
  · have h_k : m - 340 < 20 := by omega
    have h_eq : m = 340 + (m - 340) := by omega
    rw [h_eq]
    exact count_eq_all_17 (m - 340) h_k
  by_cases h_380 : m < 380
  · have h_k : m - 360 < 20 := by omega
    have h_eq : m = 360 + (m - 360) := by omega
    rw [h_eq]
    exact count_eq_all_18 (m - 360) h_k
  by_cases h_400 : m < 400
  · have h_k : m - 380 < 20 := by omega
    have h_eq : m = 380 + (m - 380) := by omega
    rw [h_eq]
    exact count_eq_all_19 (m - 380) h_k
  by_cases h_420 : m < 420
  · have h_k : m - 400 < 20 := by omega
    have h_eq : m = 400 + (m - 400) := by omega
    rw [h_eq]
    exact count_eq_all_20 (m - 400) h_k
  by_cases h_440 : m < 440
  · have h_k : m - 420 < 20 := by omega
    have h_eq : m = 420 + (m - 420) := by omega
    rw [h_eq]
    exact count_eq_all_21 (m - 420) h_k
  by_cases h_460 : m < 460
  · have h_k : m - 440 < 20 := by omega
    have h_eq : m = 440 + (m - 440) := by omega
    rw [h_eq]
    exact count_eq_all_22 (m - 440) h_k
  by_cases h_480 : m < 480
  · have h_k : m - 460 < 20 := by omega
    have h_eq : m = 460 + (m - 460) := by omega
    rw [h_eq]
    exact count_eq_all_23 (m - 460) h_k
  by_cases h_500 : m < 500
  · have h_k : m - 480 < 20 := by omega
    have h_eq : m = 480 + (m - 480) := by omega
    rw [h_eq]
    exact count_eq_all_24 (m - 480) h_k
  by_cases h_520 : m < 520
  · have h_k : m - 500 < 20 := by omega
    have h_eq : m = 500 + (m - 500) := by omega
    rw [h_eq]
    exact count_eq_all_25 (m - 500) h_k
  by_cases h_540 : m < 540
  · have h_k : m - 520 < 20 := by omega
    have h_eq : m = 520 + (m - 520) := by omega
    rw [h_eq]
    exact count_eq_all_26 (m - 520) h_k
  by_cases h_560 : m < 560
  · have h_k : m - 540 < 20 := by omega
    have h_eq : m = 540 + (m - 540) := by omega
    rw [h_eq]
    exact count_eq_all_27 (m - 540) h_k
  by_cases h_580 : m < 580
  · have h_k : m - 560 < 20 := by omega
    have h_eq : m = 560 + (m - 560) := by omega
    rw [h_eq]
    exact count_eq_all_28 (m - 560) h_k
  by_cases h_600 : m < 600
  · have h_k : m - 580 < 20 := by omega
    have h_eq : m = 580 + (m - 580) := by omega
    rw [h_eq]
    exact count_eq_all_29 (m - 580) h_k
  by_cases h_620 : m < 620
  · have h_k : m - 600 < 20 := by omega
    have h_eq : m = 600 + (m - 600) := by omega
    rw [h_eq]
    exact count_eq_all_30 (m - 600) h_k
  by_cases h_640 : m < 640
  · have h_k : m - 620 < 20 := by omega
    have h_eq : m = 620 + (m - 620) := by omega
    rw [h_eq]
    exact count_eq_all_31 (m - 620) h_k
  by_cases h_660 : m < 660
  · have h_k : m - 640 < 20 := by omega
    have h_eq : m = 640 + (m - 640) := by omega
    rw [h_eq]
    exact count_eq_all_32 (m - 640) h_k
  by_cases h_680 : m < 680
  · have h_k : m - 660 < 20 := by omega
    have h_eq : m = 660 + (m - 660) := by omega
    rw [h_eq]
    exact count_eq_all_33 (m - 660) h_k
  by_cases h_700 : m < 700
  · have h_k : m - 680 < 20 := by omega
    have h_eq : m = 680 + (m - 680) := by omega
    rw [h_eq]
    exact count_eq_all_34 (m - 680) h_k
  by_cases h_720 : m < 720
  · have h_k : m - 700 < 20 := by omega
    have h_eq : m = 700 + (m - 700) := by omega
    rw [h_eq]
    exact count_eq_all_35 (m - 700) h_k
  by_cases h_740 : m < 740
  · have h_k : m - 720 < 20 := by omega
    have h_eq : m = 720 + (m - 720) := by omega
    rw [h_eq]
    exact count_eq_all_36 (m - 720) h_k
  by_cases h_760 : m < 760
  · have h_k : m - 740 < 20 := by omega
    have h_eq : m = 740 + (m - 740) := by omega
    rw [h_eq]
    exact count_eq_all_37 (m - 740) h_k
  by_cases h_780 : m < 780
  · have h_k : m - 760 < 20 := by omega
    have h_eq : m = 760 + (m - 760) := by omega
    rw [h_eq]
    exact count_eq_all_38 (m - 760) h_k
  by_cases h_800 : m < 800
  · have h_k : m - 780 < 20 := by omega
    have h_eq : m = 780 + (m - 780) := by omega
    rw [h_eq]
    exact count_eq_all_39 (m - 780) h_k
  by_cases h_820 : m < 820
  · have h_k : m - 800 < 20 := by omega
    have h_eq : m = 800 + (m - 800) := by omega
    rw [h_eq]
    exact count_eq_all_40 (m - 800) h_k
  by_cases h_840 : m < 840
  · have h_k : m - 820 < 20 := by omega
    have h_eq : m = 820 + (m - 820) := by omega
    rw [h_eq]
    exact count_eq_all_41 (m - 820) h_k
  by_cases h_860 : m < 860
  · have h_k : m - 840 < 20 := by omega
    have h_eq : m = 840 + (m - 840) := by omega
    rw [h_eq]
    exact count_eq_all_42 (m - 840) h_k
  by_cases h_880 : m < 880
  · have h_k : m - 860 < 20 := by omega
    have h_eq : m = 860 + (m - 860) := by omega
    rw [h_eq]
    exact count_eq_all_43 (m - 860) h_k
  by_cases h_900 : m < 900
  · have h_k : m - 880 < 20 := by omega
    have h_eq : m = 880 + (m - 880) := by omega
    rw [h_eq]
    exact count_eq_all_44 (m - 880) h_k
  by_cases h_920 : m < 920
  · have h_k : m - 900 < 20 := by omega
    have h_eq : m = 900 + (m - 900) := by omega
    rw [h_eq]
    exact count_eq_all_45 (m - 900) h_k
  by_cases h_940 : m < 940
  · have h_k : m - 920 < 20 := by omega
    have h_eq : m = 920 + (m - 920) := by omega
    rw [h_eq]
    exact count_eq_all_46 (m - 920) h_k
  by_cases h_960 : m < 960
  · have h_k : m - 940 < 20 := by omega
    have h_eq : m = 940 + (m - 940) := by omega
    rw [h_eq]
    exact count_eq_all_47 (m - 940) h_k
  by_cases h_980 : m < 980
  · have h_k : m - 960 < 20 := by omega
    have h_eq : m = 960 + (m - 960) := by omega
    rw [h_eq]
    exact count_eq_all_48 (m - 960) h_k
  by_cases h_1000 : m < 1000
  · have h_k : m - 980 < 20 := by omega
    have h_eq : m = 980 + (m - 980) := by omega
    rw [h_eq]
    exact count_eq_all_49 (m - 980) h_k
  by_cases h_1020 : m < 1020
  · have h_k : m - 1000 < 20 := by omega
    have h_eq : m = 1000 + (m - 1000) := by omega
    rw [h_eq]
    exact count_eq_all_50 (m - 1000) h_k
  by_cases h_1040 : m < 1040
  · have h_k : m - 1020 < 20 := by omega
    have h_eq : m = 1020 + (m - 1020) := by omega
    rw [h_eq]
    exact count_eq_all_51 (m - 1020) h_k
  by_cases h_1060 : m < 1060
  · have h_k : m - 1040 < 20 := by omega
    have h_eq : m = 1040 + (m - 1040) := by omega
    rw [h_eq]
    exact count_eq_all_52 (m - 1040) h_k
  by_cases h_1080 : m < 1080
  · have h_k : m - 1060 < 20 := by omega
    have h_eq : m = 1060 + (m - 1060) := by omega
    rw [h_eq]
    exact count_eq_all_53 (m - 1060) h_k
  by_cases h_1100 : m < 1100
  · have h_k : m - 1080 < 20 := by omega
    have h_eq : m = 1080 + (m - 1080) := by omega
    rw [h_eq]
    exact count_eq_all_54 (m - 1080) h_k
  by_cases h_1120 : m < 1120
  · have h_k : m - 1100 < 20 := by omega
    have h_eq : m = 1100 + (m - 1100) := by omega
    rw [h_eq]
    exact count_eq_all_55 (m - 1100) h_k
  by_cases h_1140 : m < 1140
  · have h_k : m - 1120 < 20 := by omega
    have h_eq : m = 1120 + (m - 1120) := by omega
    rw [h_eq]
    exact count_eq_all_56 (m - 1120) h_k
  by_cases h_1160 : m < 1160
  · have h_k : m - 1140 < 20 := by omega
    have h_eq : m = 1140 + (m - 1140) := by omega
    rw [h_eq]
    exact count_eq_all_57 (m - 1140) h_k
  by_cases h_1180 : m < 1180
  · have h_k : m - 1160 < 20 := by omega
    have h_eq : m = 1160 + (m - 1160) := by omega
    rw [h_eq]
    exact count_eq_all_58 (m - 1160) h_k
  by_cases h_1200 : m < 1200
  · have h_k : m - 1180 < 20 := by omega
    have h_eq : m = 1180 + (m - 1180) := by omega
    rw [h_eq]
    exact count_eq_all_59 (m - 1180) h_k
  by_cases h_1220 : m < 1220
  · have h_k : m - 1200 < 20 := by omega
    have h_eq : m = 1200 + (m - 1200) := by omega
    rw [h_eq]
    exact count_eq_all_60 (m - 1200) h_k
  by_cases h_1240 : m < 1240
  · have h_k : m - 1220 < 20 := by omega
    have h_eq : m = 1220 + (m - 1220) := by omega
    rw [h_eq]
    exact count_eq_all_61 (m - 1220) h_k
  by_cases h_1260 : m < 1260
  · have h_k : m - 1240 < 20 := by omega
    have h_eq : m = 1240 + (m - 1240) := by omega
    rw [h_eq]
    exact count_eq_all_62 (m - 1240) h_k
  by_cases h_1280 : m < 1280
  · have h_k : m - 1260 < 20 := by omega
    have h_eq : m = 1260 + (m - 1260) := by omega
    rw [h_eq]
    exact count_eq_all_63 (m - 1260) h_k
  by_cases h_1300 : m < 1300
  · have h_k : m - 1280 < 20 := by omega
    have h_eq : m = 1280 + (m - 1280) := by omega
    rw [h_eq]
    exact count_eq_all_64 (m - 1280) h_k
  by_cases h_1320 : m < 1320
  · have h_k : m - 1300 < 20 := by omega
    have h_eq : m = 1300 + (m - 1300) := by omega
    rw [h_eq]
    exact count_eq_all_65 (m - 1300) h_k
  by_cases h_1340 : m < 1340
  · have h_k : m - 1320 < 20 := by omega
    have h_eq : m = 1320 + (m - 1320) := by omega
    rw [h_eq]
    exact count_eq_all_66 (m - 1320) h_k
  by_cases h_1360 : m < 1360
  · have h_k : m - 1340 < 20 := by omega
    have h_eq : m = 1340 + (m - 1340) := by omega
    rw [h_eq]
    exact count_eq_all_67 (m - 1340) h_k
  by_cases h_1380 : m < 1380
  · have h_k : m - 1360 < 20 := by omega
    have h_eq : m = 1360 + (m - 1360) := by omega
    rw [h_eq]
    exact count_eq_all_68 (m - 1360) h_k
  by_cases h_1400 : m < 1400
  · have h_k : m - 1380 < 20 := by omega
    have h_eq : m = 1380 + (m - 1380) := by omega
    rw [h_eq]
    exact count_eq_all_69 (m - 1380) h_k
  by_cases h_1420 : m < 1420
  · have h_k : m - 1400 < 20 := by omega
    have h_eq : m = 1400 + (m - 1400) := by omega
    rw [h_eq]
    exact count_eq_all_70 (m - 1400) h_k
  by_cases h_1440 : m < 1440
  · have h_k : m - 1420 < 20 := by omega
    have h_eq : m = 1420 + (m - 1420) := by omega
    rw [h_eq]
    exact count_eq_all_71 (m - 1420) h_k
  by_cases h_1460 : m < 1460
  · have h_k : m - 1440 < 20 := by omega
    have h_eq : m = 1440 + (m - 1440) := by omega
    rw [h_eq]
    exact count_eq_all_72 (m - 1440) h_k
  by_cases h_1480 : m < 1480
  · have h_k : m - 1460 < 20 := by omega
    have h_eq : m = 1460 + (m - 1460) := by omega
    rw [h_eq]
    exact count_eq_all_73 (m - 1460) h_k
  by_cases h_1500 : m < 1500
  · have h_k : m - 1480 < 20 := by omega
    have h_eq : m = 1480 + (m - 1480) := by omega
    rw [h_eq]
    exact count_eq_all_74 (m - 1480) h_k
  by_cases h_1520 : m < 1520
  · have h_k : m - 1500 < 20 := by omega
    have h_eq : m = 1500 + (m - 1500) := by omega
    rw [h_eq]
    exact count_eq_all_75 (m - 1500) h_k
  by_cases h_1540 : m < 1540
  · have h_k : m - 1520 < 20 := by omega
    have h_eq : m = 1520 + (m - 1520) := by omega
    rw [h_eq]
    exact count_eq_all_76 (m - 1520) h_k
  by_cases h_1560 : m < 1560
  · have h_k : m - 1540 < 20 := by omega
    have h_eq : m = 1540 + (m - 1540) := by omega
    rw [h_eq]
    exact count_eq_all_77 (m - 1540) h_k
  by_cases h_1580 : m < 1580
  · have h_k : m - 1560 < 20 := by omega
    have h_eq : m = 1560 + (m - 1560) := by omega
    rw [h_eq]
    exact count_eq_all_78 (m - 1560) h_k
  by_cases h_1600 : m < 1600
  · have h_k : m - 1580 < 20 := by omega
    have h_eq : m = 1580 + (m - 1580) := by omega
    rw [h_eq]
    exact count_eq_all_79 (m - 1580) h_k
  by_cases h_1620 : m < 1620
  · have h_k : m - 1600 < 20 := by omega
    have h_eq : m = 1600 + (m - 1600) := by omega
    rw [h_eq]
    exact count_eq_all_80 (m - 1600) h_k
  by_cases h_1640 : m < 1640
  · have h_k : m - 1620 < 20 := by omega
    have h_eq : m = 1620 + (m - 1620) := by omega
    rw [h_eq]
    exact count_eq_all_81 (m - 1620) h_k
  by_cases h_1660 : m < 1660
  · have h_k : m - 1640 < 20 := by omega
    have h_eq : m = 1640 + (m - 1640) := by omega
    rw [h_eq]
    exact count_eq_all_82 (m - 1640) h_k
  by_cases h_1680 : m < 1680
  · have h_k : m - 1660 < 20 := by omega
    have h_eq : m = 1660 + (m - 1660) := by omega
    rw [h_eq]
    exact count_eq_all_83 (m - 1660) h_k
  by_cases h_1700 : m < 1700
  · have h_k : m - 1680 < 20 := by omega
    have h_eq : m = 1680 + (m - 1680) := by omega
    rw [h_eq]
    exact count_eq_all_84 (m - 1680) h_k
  by_cases h_1720 : m < 1720
  · have h_k : m - 1700 < 20 := by omega
    have h_eq : m = 1700 + (m - 1700) := by omega
    rw [h_eq]
    exact count_eq_all_85 (m - 1700) h_k
  by_cases h_1740 : m < 1740
  · have h_k : m - 1720 < 20 := by omega
    have h_eq : m = 1720 + (m - 1720) := by omega
    rw [h_eq]
    exact count_eq_all_86 (m - 1720) h_k
  by_cases h_1760 : m < 1760
  · have h_k : m - 1740 < 20 := by omega
    have h_eq : m = 1740 + (m - 1740) := by omega
    rw [h_eq]
    exact count_eq_all_87 (m - 1740) h_k
  by_cases h_1780 : m < 1780
  · have h_k : m - 1760 < 20 := by omega
    have h_eq : m = 1760 + (m - 1760) := by omega
    rw [h_eq]
    exact count_eq_all_88 (m - 1760) h_k
  by_cases h_1800 : m < 1800
  · have h_k : m - 1780 < 20 := by omega
    have h_eq : m = 1780 + (m - 1780) := by omega
    rw [h_eq]
    exact count_eq_all_89 (m - 1780) h_k
  by_cases h_1820 : m < 1820
  · have h_k : m - 1800 < 20 := by omega
    have h_eq : m = 1800 + (m - 1800) := by omega
    rw [h_eq]
    exact count_eq_all_90 (m - 1800) h_k
  by_cases h_1840 : m < 1840
  · have h_k : m - 1820 < 20 := by omega
    have h_eq : m = 1820 + (m - 1820) := by omega
    rw [h_eq]
    exact count_eq_all_91 (m - 1820) h_k
  by_cases h_1860 : m < 1860
  · have h_k : m - 1840 < 20 := by omega
    have h_eq : m = 1840 + (m - 1840) := by omega
    rw [h_eq]
    exact count_eq_all_92 (m - 1840) h_k
  by_cases h_1880 : m < 1880
  · have h_k : m - 1860 < 20 := by omega
    have h_eq : m = 1860 + (m - 1860) := by omega
    rw [h_eq]
    exact count_eq_all_93 (m - 1860) h_k
  by_cases h_1900 : m < 1900
  · have h_k : m - 1880 < 20 := by omega
    have h_eq : m = 1880 + (m - 1880) := by omega
    rw [h_eq]
    exact count_eq_all_94 (m - 1880) h_k
  by_cases h_1920 : m < 1920
  · have h_k : m - 1900 < 20 := by omega
    have h_eq : m = 1900 + (m - 1900) := by omega
    rw [h_eq]
    exact count_eq_all_95 (m - 1900) h_k
  by_cases h_1940 : m < 1940
  · have h_k : m - 1920 < 20 := by omega
    have h_eq : m = 1920 + (m - 1920) := by omega
    rw [h_eq]
    exact count_eq_all_96 (m - 1920) h_k
  by_cases h_1960 : m < 1960
  · have h_k : m - 1940 < 20 := by omega
    have h_eq : m = 1940 + (m - 1940) := by omega
    rw [h_eq]
    exact count_eq_all_97 (m - 1940) h_k
  by_cases h_1980 : m < 1980
  · have h_k : m - 1960 < 20 := by omega
    have h_eq : m = 1960 + (m - 1960) := by omega
    rw [h_eq]
    exact count_eq_all_98 (m - 1960) h_k
  by_cases h_2000 : m < 2000
  · have h_k : m - 1980 < 20 := by omega
    have h_eq : m = 1980 + (m - 1980) := by omega
    rw [h_eq]
    exact count_eq_all_99 (m - 1980) h_k
  by_cases h_2020 : m < 2020
  · have h_k : m - 2000 < 20 := by omega
    have h_eq : m = 2000 + (m - 2000) := by omega
    rw [h_eq]
    exact count_eq_all_100 (m - 2000) h_k
  by_cases h_2040 : m < 2040
  · have h_k : m - 2020 < 20 := by omega
    have h_eq : m = 2020 + (m - 2020) := by omega
    rw [h_eq]
    exact count_eq_all_101 (m - 2020) h_k
  by_cases h_2060 : m < 2060
  · have h_k : m - 2040 < 20 := by omega
    have h_eq : m = 2040 + (m - 2040) := by omega
    rw [h_eq]
    exact count_eq_all_102 (m - 2040) h_k
  by_cases h_2080 : m < 2080
  · have h_k : m - 2060 < 20 := by omega
    have h_eq : m = 2060 + (m - 2060) := by omega
    rw [h_eq]
    exact count_eq_all_103 (m - 2060) h_k
  by_cases h_2100 : m < 2100
  · have h_k : m - 2080 < 20 := by omega
    have h_eq : m = 2080 + (m - 2080) := by omega
    rw [h_eq]
    exact count_eq_all_104 (m - 2080) h_k
  by_cases h_2120 : m < 2120
  · have h_k : m - 2100 < 20 := by omega
    have h_eq : m = 2100 + (m - 2100) := by omega
    rw [h_eq]
    exact count_eq_all_105 (m - 2100) h_k
  by_cases h_2140 : m < 2140
  · have h_k : m - 2120 < 20 := by omega
    have h_eq : m = 2120 + (m - 2120) := by omega
    rw [h_eq]
    exact count_eq_all_106 (m - 2120) h_k
  by_cases h_2160 : m < 2160
  · have h_k : m - 2140 < 20 := by omega
    have h_eq : m = 2140 + (m - 2140) := by omega
    rw [h_eq]
    exact count_eq_all_107 (m - 2140) h_k
  by_cases h_2180 : m < 2180
  · have h_k : m - 2160 < 20 := by omega
    have h_eq : m = 2160 + (m - 2160) := by omega
    rw [h_eq]
    exact count_eq_all_108 (m - 2160) h_k
  by_cases h_2200 : m < 2200
  · have h_k : m - 2180 < 20 := by omega
    have h_eq : m = 2180 + (m - 2180) := by omega
    rw [h_eq]
    exact count_eq_all_109 (m - 2180) h_k
  by_cases h_2220 : m < 2220
  · have h_k : m - 2200 < 20 := by omega
    have h_eq : m = 2200 + (m - 2200) := by omega
    rw [h_eq]
    exact count_eq_all_110 (m - 2200) h_k
  by_cases h_2240 : m < 2240
  · have h_k : m - 2220 < 20 := by omega
    have h_eq : m = 2220 + (m - 2220) := by omega
    rw [h_eq]
    exact count_eq_all_111 (m - 2220) h_k
  by_cases h_2260 : m < 2260
  · have h_k : m - 2240 < 20 := by omega
    have h_eq : m = 2240 + (m - 2240) := by omega
    rw [h_eq]
    exact count_eq_all_112 (m - 2240) h_k
  by_cases h_2280 : m < 2280
  · have h_k : m - 2260 < 20 := by omega
    have h_eq : m = 2260 + (m - 2260) := by omega
    rw [h_eq]
    exact count_eq_all_113 (m - 2260) h_k
  by_cases h_2300 : m < 2300
  · have h_k : m - 2280 < 20 := by omega
    have h_eq : m = 2280 + (m - 2280) := by omega
    rw [h_eq]
    exact count_eq_all_114 (m - 2280) h_k
  · have h_k : m - 2300 < 10 := by omega
    have h_eq : m = 2300 + (m - 2300) := by omega
    rw [h_eq]
    exact count_eq_all_115 (m - 2300) h_k


theorem A384237_le_unitary_sqrt_all (m : ℕ) (h : m < 2310) : A384237 m ≤ count_unitary_divs_sqrt m := by
  have h_le := A384237_le_unitary_bound m
  rw [count_eq_all m h] at h_le
  exact h_le

theorem ne_ten_of_unitary_sqrt_lt_ten (m : ℕ) (h_lt : m < 2310) (h_ut : count_unitary_divs_sqrt m < 10) : A384237 m ≠ 10 := by
  intro h_eq
  have h_le := A384237_le_unitary_sqrt_all m h_lt
  rw [h_eq] at h_le
  omega

theorem range_direct_0 : ∀ k < 100, k ≠ 0 → (if count_unitary_divs_sqrt k < 10 then true else decide (A384237_direct k ≠ 10)) = true := by decide
theorem range_direct_1 : ∀ k < 100, (if count_unitary_divs_sqrt (100 + k) < 10 then true else decide (A384237_direct (100 + k) ≠ 10)) = true := by decide
theorem range_direct_2 : ∀ k < 100, (if count_unitary_divs_sqrt (200 + k) < 10 then true else decide (A384237_direct (200 + k) ≠ 10)) = true := by decide
theorem range_direct_3 : ∀ k < 100, (if count_unitary_divs_sqrt (300 + k) < 10 then true else decide (A384237_direct (300 + k) ≠ 10)) = true := by decide
theorem range_direct_4 : ∀ k < 100, (if count_unitary_divs_sqrt (400 + k) < 10 then true else decide (A384237_direct (400 + k) ≠ 10)) = true := by decide
theorem range_direct_5 : ∀ k < 100, (if count_unitary_divs_sqrt (500 + k) < 10 then true else decide (A384237_direct (500 + k) ≠ 10)) = true := by decide
theorem range_direct_6 : ∀ k < 100, (if count_unitary_divs_sqrt (600 + k) < 10 then true else decide (A384237_direct (600 + k) ≠ 10)) = true := by decide
theorem range_direct_7 : ∀ k < 100, (if count_unitary_divs_sqrt (700 + k) < 10 then true else decide (A384237_direct (700 + k) ≠ 10)) = true := by decide
theorem range_direct_8 : ∀ k < 100, (if count_unitary_divs_sqrt (800 + k) < 10 then true else decide (A384237_direct (800 + k) ≠ 10)) = true := by decide
theorem range_direct_9 : ∀ k < 100, (if count_unitary_divs_sqrt (900 + k) < 10 then true else decide (A384237_direct (900 + k) ≠ 10)) = true := by decide
theorem range_direct_10 : ∀ k < 100, (if count_unitary_divs_sqrt (1000 + k) < 10 then true else decide (A384237_direct (1000 + k) ≠ 10)) = true := by decide
theorem range_direct_11 : ∀ k < 100, (if count_unitary_divs_sqrt (1100 + k) < 10 then true else decide (A384237_direct (1100 + k) ≠ 10)) = true := by decide
theorem range_direct_12 : ∀ k < 100, (if count_unitary_divs_sqrt (1200 + k) < 10 then true else decide (A384237_direct (1200 + k) ≠ 10)) = true := by decide
theorem range_direct_13 : ∀ k < 100, (if count_unitary_divs_sqrt (1300 + k) < 10 then true else decide (A384237_direct (1300 + k) ≠ 10)) = true := by decide
theorem range_direct_14 : ∀ k < 100, (if count_unitary_divs_sqrt (1400 + k) < 10 then true else decide (A384237_direct (1400 + k) ≠ 10)) = true := by decide
theorem range_direct_15 : ∀ k < 100, (if count_unitary_divs_sqrt (1500 + k) < 10 then true else decide (A384237_direct (1500 + k) ≠ 10)) = true := by decide
theorem range_direct_16 : ∀ k < 100, (if count_unitary_divs_sqrt (1600 + k) < 10 then true else decide (A384237_direct (1600 + k) ≠ 10)) = true := by decide
theorem range_direct_17 : ∀ k < 100, (if count_unitary_divs_sqrt (1700 + k) < 10 then true else decide (A384237_direct (1700 + k) ≠ 10)) = true := by decide
theorem range_direct_18 : ∀ k < 100, (if count_unitary_divs_sqrt (1800 + k) < 10 then true else decide (A384237_direct (1800 + k) ≠ 10)) = true := by decide
theorem range_direct_19 : ∀ k < 100, (if count_unitary_divs_sqrt (1900 + k) < 10 then true else decide (A384237_direct (1900 + k) ≠ 10)) = true := by decide
theorem range_direct_20 : ∀ k < 100, (if count_unitary_divs_sqrt (2000 + k) < 10 then true else decide (A384237_direct (2000 + k) ≠ 10)) = true := by decide
theorem range_direct_21 : ∀ k < 100, (if count_unitary_divs_sqrt (2100 + k) < 10 then true else decide (A384237_direct (2100 + k) ≠ 10)) = true := by decide
theorem range_direct_22 : ∀ k < 100, (if count_unitary_divs_sqrt (2200 + k) < 10 then true else decide (A384237_direct (2200 + k) ≠ 10)) = true := by decide
theorem range_direct_23 : ∀ k < 10, (if count_unitary_divs_sqrt (2300 + k) < 10 then true else decide (A384237_direct (2300 + k) ≠ 10)) = true := by decide

theorem lt_2310_ne_ten (m : ℕ) (h_lt : m < 2310) : A384237 m ≠ 10 := by
  by_cases h_zero : m = 0
  · subst h_zero
    decide
  · by_cases h_ut : count_unitary_divs_sqrt m < 10
    · exact ne_ten_of_unitary_sqrt_lt_ten m h_lt h_ut
    · rw [A384237_eq_fast, ← A384237_direct_eq_fast]
      by_cases h_100 : m < 100
      · have h_helper := range_direct_0 m h_100 h_zero
        rw [if_neg h_ut] at h_helper
        exact decide_eq_true_iff.mp h_helper
      by_cases h_200 : m < 200
      · have h_k : m - 100 < 100 := by omega
        have h_eq : m = 100 + (m - 100) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (100 + (m - 100)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_1 (m - 100) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_300 : m < 300
      · have h_k : m - 200 < 100 := by omega
        have h_eq : m = 200 + (m - 200) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (200 + (m - 200)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_2 (m - 200) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_400 : m < 400
      · have h_k : m - 300 < 100 := by omega
        have h_eq : m = 300 + (m - 300) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (300 + (m - 300)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_3 (m - 300) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_500 : m < 500
      · have h_k : m - 400 < 100 := by omega
        have h_eq : m = 400 + (m - 400) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (400 + (m - 400)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_4 (m - 400) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_600 : m < 600
      · have h_k : m - 500 < 100 := by omega
        have h_eq : m = 500 + (m - 500) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (500 + (m - 500)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_5 (m - 500) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_700 : m < 700
      · have h_k : m - 600 < 100 := by omega
        have h_eq : m = 600 + (m - 600) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (600 + (m - 600)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_6 (m - 600) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_800 : m < 800
      · have h_k : m - 700 < 100 := by omega
        have h_eq : m = 700 + (m - 700) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (700 + (m - 700)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_7 (m - 700) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_900 : m < 900
      · have h_k : m - 800 < 100 := by omega
        have h_eq : m = 800 + (m - 800) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (800 + (m - 800)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_8 (m - 800) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_1000 : m < 1000
      · have h_k : m - 900 < 100 := by omega
        have h_eq : m = 900 + (m - 900) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (900 + (m - 900)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_9 (m - 900) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_1100 : m < 1100
      · have h_k : m - 1000 < 100 := by omega
        have h_eq : m = 1000 + (m - 1000) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (1000 + (m - 1000)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_10 (m - 1000) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_1200 : m < 1200
      · have h_k : m - 1100 < 100 := by omega
        have h_eq : m = 1100 + (m - 1100) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (1100 + (m - 1100)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_11 (m - 1100) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_1300 : m < 1300
      · have h_k : m - 1200 < 100 := by omega
        have h_eq : m = 1200 + (m - 1200) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (1200 + (m - 1200)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_12 (m - 1200) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_1400 : m < 1400
      · have h_k : m - 1300 < 100 := by omega
        have h_eq : m = 1300 + (m - 1300) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (1300 + (m - 1300)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_13 (m - 1300) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_1500 : m < 1500
      · have h_k : m - 1400 < 100 := by omega
        have h_eq : m = 1400 + (m - 1400) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (1400 + (m - 1400)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_14 (m - 1400) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_1600 : m < 1600
      · have h_k : m - 1500 < 100 := by omega
        have h_eq : m = 1500 + (m - 1500) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (1500 + (m - 1500)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_15 (m - 1500) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_1700 : m < 1700
      · have h_k : m - 1600 < 100 := by omega
        have h_eq : m = 1600 + (m - 1600) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (1600 + (m - 1600)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_16 (m - 1600) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_1800 : m < 1800
      · have h_k : m - 1700 < 100 := by omega
        have h_eq : m = 1700 + (m - 1700) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (1700 + (m - 1700)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_17 (m - 1700) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_1900 : m < 1900
      · have h_k : m - 1800 < 100 := by omega
        have h_eq : m = 1800 + (m - 1800) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (1800 + (m - 1800)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_18 (m - 1800) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_2000 : m < 2000
      · have h_k : m - 1900 < 100 := by omega
        have h_eq : m = 1900 + (m - 1900) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (1900 + (m - 1900)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_19 (m - 1900) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_2100 : m < 2100
      · have h_k : m - 2000 < 100 := by omega
        have h_eq : m = 2000 + (m - 2000) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (2000 + (m - 2000)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_20 (m - 2000) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_2200 : m < 2200
      · have h_k : m - 2100 < 100 := by omega
        have h_eq : m = 2100 + (m - 2100) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (2100 + (m - 2100)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_21 (m - 2100) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      by_cases h_2300 : m < 2300
      · have h_k : m - 2200 < 100 := by omega
        have h_eq : m = 2200 + (m - 2200) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (2200 + (m - 2200)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_22 (m - 2200) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper
      · have h_k : m - 2300 < 10 := by omega
        have h_eq : m = 2300 + (m - 2300) := by omega
        have h_ut2 : ¬ count_unitary_divs_sqrt (2300 + (m - 2300)) < 10 := by rwa [← h_eq]
        have h_helper := range_direct_23 (m - 2300) h_k
        rw [if_neg h_ut2] at h_helper
        rw [h_eq]
        exact decide_eq_true_iff.mp h_helper


/--
A385391: (n)$ is the smallest integer $ such that (k) = n$.
This is formalized using the set infimum ($\mathrm{sInf}$) of the preimage of $.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | A384237 k = n}

/-- A002110(n): The primorial \#$. Product of the first $ primes (0-indexed).
  Note: Nat.nth Nat.Prime 0 = 2, Nat.nth Nat.Prime 1 = 3, etc. -/
noncomputable def A002110 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else (Finset.range n).prod fun i => Nat.nth Nat.Prime i

theorem A002110_zero : A002110 0 = 1 := by rfl

theorem A002110_succ (n : ℕ) : A002110 (n + 1) = (Finset.range (n + 1)).prod fun i => Nat.nth Nat.Prime i := by
  unfold A002110
  have h : ¬(n + 1 = 0) := Nat.succ_ne_zero n
  rw [if_neg h]

theorem A002110_one : A002110 1 = 2 := by
  rw [A002110_succ 0]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_zero]
  simp [Nat.nth_prime_zero_eq_two]

theorem A002110_two : A002110 2 = 6 := by
  rw [A002110_succ 1]
  rw [Finset.prod_range_succ]
  have h : (∏ x ∈ range 1, Nat.nth Nat.Prime x) = A002110 1 := (A002110_succ 0).symm
  rw [h, A002110_one, Nat.nth_prime_one_eq_three]
  rfl

theorem A002110_three : A002110 3 = 30 := by
  rw [A002110_succ 2]
  rw [Finset.prod_range_succ]
  have h : (∏ x ∈ range 2, Nat.nth Nat.Prime x) = A002110 2 := (A002110_succ 1).symm
  rw [h, A002110_two, Nat.nth_prime_two_eq_five]
  rfl

theorem A002110_four : A002110 4 = 210 := by
  rw [A002110_succ 3]
  rw [Finset.prod_range_succ]
  have h : (∏ x ∈ range 3, Nat.nth Nat.Prime x) = A002110 3 := (A002110_succ 2).symm
  rw [h, A002110_three, Nat.nth_prime_three_eq_seven]
  rfl

theorem A002110_five : A002110 5 = 2310 := by
  rw [A002110_succ 4]
  rw [Finset.prod_range_succ]
  have h : (∏ x ∈ range 4, Nat.nth Nat.Prime x) = A002110 4 := (A002110_succ 3).symm
  rw [h, A002110_four, Nat.nth_prime_four_eq_eleven]
  rfl

theorem sInf_eq_of_mem_of_forall_lt_not_mem {s : Set ℕ} {val : ℕ} (hmem : val ∈ s) (hlt : ∀ m < val, m ∉ s) : sInf s = val := by
  have hnonempty : s.Nonempty := ⟨val, hmem⟩
  have hle : sInf s ≤ val := Nat.sInf_le hmem
  have hge : val ≤ sInf s := by
    by_contra! h
    have hnot := hlt (sInf s) h
    have hmem_s := Nat.sInf_mem hnonempty
    exact hnot hmem_s
  exact le_antisymm hle hge

theorem a_one : a 1 = A002110 0 := by
  rw [A002110_zero]
  unfold a
  apply sInf_eq_of_mem_of_forall_lt_not_mem
  · simp only [Set.mem_setOf_eq]; decide
  · intro m hm
    simp only [Set.mem_setOf_eq]
    interval_cases m; decide

theorem a_two : a 2 = A002110 1 := by
  rw [A002110_one]
  unfold a
  apply sInf_eq_of_mem_of_forall_lt_not_mem
  · simp only [Set.mem_setOf_eq]; decide
  · intro m hm
    simp only [Set.mem_setOf_eq]
    interval_cases m <;> decide

theorem a_three : a 3 = A002110 2 := by
  rw [A002110_two]
  unfold a
  apply sInf_eq_of_mem_of_forall_lt_not_mem
  · simp only [Set.mem_setOf_eq]; decide
  · intro m hm
    simp only [Set.mem_setOf_eq]
    interval_cases m <;> decide

theorem a_six : a 6 = A002110 3 := by
  rw [A002110_three]
  unfold a
  apply sInf_eq_of_mem_of_forall_lt_not_mem
  · simp only [Set.mem_setOf_eq]; decide
  · intro m hm
    simp only [Set.mem_setOf_eq]
    interval_cases m <;> decide

theorem a_seven : a 7 = A002110 4 := by
  rw [A002110_four]
  unfold a
  apply sInf_eq_of_mem_of_forall_lt_not_mem
  · simp only [Set.mem_setOf_eq]; decide
  · intro m hm
    simp only [Set.mem_setOf_eq]
    interval_cases m <;> decide

theorem a_ten : a 10 = A002110 5 := by
  rw [A002110_five]
  unfold a
  apply sInf_eq_of_mem_of_forall_lt_not_mem
  · simp only [Set.mem_setOf_eq]; decide
  · intro m hm
    simp only [Set.mem_setOf_eq]
    exact lt_2310_ne_ten m hm

/--
oeis_385391_conjecture_0: A385391 a(1) = A002110(0), a(2) = A002110(1), a(3) = A002110(2), a(6) = A002110(3), a(7) = A002110(4), a(10) = A002110(5), ...?
This conjecture is formalized as a conjunction of the listed equalities, implying a general pattern related to A065295.
-/
theorem oeis_385391_conjecture_0 :
  a 1 = A002110 0 ∧
  a 2 = A002110 1 ∧
  a 3 = A002110 2 ∧
  a 6 = A002110 3 ∧
  a 7 = A002110 4 ∧
  a 10 = A002110 5 := by
  refine ⟨a_one, a_two, a_three, a_six, a_seven, a_ten⟩
