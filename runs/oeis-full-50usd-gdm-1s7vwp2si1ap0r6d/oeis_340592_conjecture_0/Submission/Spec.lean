import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Nat List

/--
A340592: $a(n)$ is the concatenation of the prime factors (with multiplicity) of $n$ modulo $n$.
The prime factors are taken in non-decreasing order as given by $n.\operatorname{primeFactorsList}$.
-/
def a (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    let factors_list := n.primeFactorsList

    -- Calculates 10^(number of decimal digits of k)
    let pow10_len (k : ℕ) : ℕ := 10 ^ (Nat.digits 10 k).length

    -- The concatenation operation: acc || factor
    let concat_op (acc factor : ℕ) : ℕ :=
      acc * pow10_len factor + factor

    (factors_list.foldl concat_op 0) % n

/-- The property of being composite (n > 1 and not prime) -/
def Nat.composite (n : ℕ) : Prop := ¬ (Nat.Prime n) ∧ 1 < n

instance (n : ℕ) : Decidable (Nat.composite n) := by
  unfold Nat.composite
  infer_instance

def minFacAux_fuel (fuel : ℕ) (n : ℕ) (k : ℕ) : ℕ :=
  match fuel with
  | 0 => n
  | f + 1 =>
    if n < k * k then n
    else
      if n % k = 0 then k
      else
        minFacAux_fuel f n (k + 2)

theorem minFacAux_eq_fuel (fuel : ℕ) (n : ℕ) : ∀ k, sqrt n + 2 - k ≤ fuel → minFacAux n k = minFacAux_fuel fuel n k := by
  induction fuel with
  | zero =>
    intro k h
    have h_lt : n < k * k := by
      have h_sqrt_lt : sqrt n < k := by omega
      exact Nat.sqrt_lt.mp h_sqrt_lt
    rw [minFacAux]
    unfold minFacAux_fuel
    simp [h_lt]
  | succ f ih =>
    intro k h
    rw [minFacAux]
    unfold minFacAux_fuel
    by_cases h_lt : n < k * k
    · simp [h_lt]
    · simp only [h_lt, ↓reduceIte]
      have hdvd : (k ∣ n) ↔ n % k = 0 := Nat.dvd_iff_mod_eq_zero
      by_cases h_dvd : k ∣ n
      · simp [h_dvd, hdvd.mp h_dvd]
      · have h_mod : ¬(n % k = 0) := mt hdvd.mpr h_dvd
        simp only [h_dvd, h_mod, ↓reduceIte]
        have h_le : sqrt n + 2 - (k + 2) ≤ f := by
          have hk_le : k ≤ sqrt n := Nat.le_sqrt.mpr (by omega)
          omega
        exact ih (k + 2) h_le

def minFac_fuel (fuel : ℕ) (n : ℕ) : ℕ :=
  if 2 ∣ n then 2 else minFacAux_fuel fuel n 3

theorem minFac_eq_fuel (fuel : ℕ) (n : ℕ) (h : sqrt n - 1 ≤ fuel) : minFac n = minFac_fuel fuel n := by
  rw [minFac_eq]
  unfold minFac_fuel
  by_cases h_2 : 2 ∣ n
  · simp [h_2]
  · simp only [h_2, ↓reduceIte]
    have h_le : sqrt n + 2 - 3 ≤ fuel := by omega
    exact minFacAux_eq_fuel fuel n 3 h_le

def primeFactorsList_fuel (fuel : ℕ) (n : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | f + 1 =>
    if n < 2 then []
    else
      let m := minFac_fuel 200 n
      m :: primeFactorsList_fuel f (n / m)

theorem prod_ge_pow_two (l : List ℕ) (hl : ∀ p ∈ l, Nat.Prime p) :
    2 ^ l.length ≤ l.prod := by
  induction l with
  | nil =>
    simp
  | cons p lr ih =>
    have h_prime : p.Prime := hl p (by simp)
    have h_p2 : 2 ≤ p := Nat.Prime.two_le h_prime
    have h_sub : ∀ x ∈ lr, x.Prime := fun x hx => hl x (List.mem_cons_of_mem p hx)
    have ih' := ih h_sub
    simp only [List.length_cons, Nat.pow_succ, List.prod_cons]
    calc
      2 ^ (lr.length + 1) = 2 * 2 ^ lr.length := by ring
      _ ≤ p * lr.prod := Nat.mul_le_mul h_p2 ih'

theorem primeFactorsList_length_le (n : ℕ) (hn : n ≤ 28749) : n.primeFactorsList.length ≤ 15 := by
  by_cases h0 : n = 0
  · subst h0
    rw [primeFactorsList_zero]
    simp
  · have h_prod := prod_primeFactorsList h0
    have h_primes : ∀ p ∈ n.primeFactorsList, Nat.Prime p := fun p hp => prime_of_mem_primeFactorsList hp
    have h_ge := prod_ge_pow_two n.primeFactorsList h_primes
    rw [h_prod] at h_ge
    have h_lt : 2 ^ 15 = 32768 := rfl
    have h_pow : 2 ^ n.primeFactorsList.length < 2 ^ 15 := by omega
    have h_len_lt := Nat.pow_lt_pow_iff_right (by decide) |>.mp h_pow
    omega

theorem minFac_eq_200 (n : ℕ) (hn : n ≤ 28749) : minFac n = minFac_fuel 200 n := by
  apply minFac_eq_fuel 200 n
  have h_sqrt : sqrt n < 171 := Nat.sqrt_lt.mpr (by omega)
  omega

theorem primeFactorsList_eq_fuel_of_len (fuel : ℕ) : ∀ n, n ≤ 28749 → n.primeFactorsList.length ≤ fuel → primeFactorsList n = primeFactorsList_fuel fuel n := by
  induction fuel with
  | zero =>
    intro n hn h_len
    have : n.primeFactorsList.length = 0 := by omega
    have h_nil : n.primeFactorsList = [] := by
      cases h_list : n.primeFactorsList with
      | nil => rfl
      | cons head tail =>
        rw [h_list] at h_len
        simp only [List.length_cons] at h_len
        omega
    rw [primeFactorsList_eq_nil] at h_nil
    unfold primeFactorsList_fuel
    rcases h_nil with rfl | rfl
    · rw [primeFactorsList_zero]
    · rw [primeFactorsList_one]
  | succ f ih =>
    intro n hn h_len
    by_cases h2 : n < 2
    · unfold primeFactorsList_fuel
      simp only [h2, ↓reduceIte]
      interval_cases n
      · rw [primeFactorsList_zero]
      · rw [primeFactorsList_one]
    · -- n ≥ 2
      have h2n : 2 ≤ n := by omega
      have h_eq_n : n = n - 2 + 2 := by omega
      nth_rw 1 [h_eq_n]
      rw [primeFactorsList_add_two (n - 2)]
      unfold primeFactorsList_fuel
      have h_if : ¬ (n < 2) := h2
      simp only [h_if, ↓reduceIte]
      -- Prove minFac n = minFac_fuel 200 n
      have h_eq_n2 : n - 2 + 2 = n := by omega
      have h_min : minFac n = minFac_fuel 200 n := minFac_eq_200 n hn
      rw [h_eq_n2]
      rw [h_min]
      rw [← h_min]
      congr 1
      -- Apply induction hypothesis on n / minFac n
      have h_div_le : n / minFac n ≤ 28749 := by
        have : minFac n ≥ 2 := Nat.minFac_prime (by omega) |>.two_le
        have : n / minFac n ≤ n := Nat.div_le_self n (minFac n)
        omega
      have h_len_div : (n / minFac n).primeFactorsList.length ≤ f := by
        have h_len' : n.primeFactorsList.length ≤ f + 1 := h_len
        nth_rw 1 [h_eq_n] at h_len'
        rw [primeFactorsList_add_two (n - 2)] at h_len'
        rw [h_eq_n2] at h_len'
        simp only [List.length_cons] at h_len'
        omega
      exact ih (n / minFac n) h_div_le h_len_div

theorem primeFactorsList_eq_fuel_15 (n : ℕ) (hn : n ≤ 28749) : primeFactorsList n = primeFactorsList_fuel 15 n := by
  apply primeFactorsList_eq_fuel_of_len 15 n hn
  exact primeFactorsList_length_le n hn

lemma foldl_congr {α β : Type} (f1 f2 : α → β → α) (init : α) (l : List β)
    (h : ∀ acc, ∀ x ∈ l, f1 acc x = f2 acc x) :
    l.foldl f1 init = l.foldl f2 init := by
  induction l generalizing init with
  | nil => rfl
  | cons head tail ih =>
    have h_head : f1 init head = f2 init head := h init head List.mem_cons_self
    have h_tail : ∀ acc, ∀ x ∈ tail, f1 acc x = f2 acc x := fun acc x hx =>
      h acc x (List.mem_cons_of_mem _ hx)
    rw [List.foldl_cons, List.foldl_cons, h_head]
    exact ih (f2 init head) h_tail

def len_digits10_fuel (fuel : ℕ) (k : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    if k = 0 then 0
    else 1 + len_digits10_fuel f (k / 10)

theorem len_digits10_eq_fuel (fuel : ℕ) : ∀ k, k ≤ fuel → (Nat.digits 10 k).length = len_digits10_fuel fuel k := by
  induction fuel with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst this
    rw [digits_zero]
    rfl
  | succ f ih =>
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [digits_zero]
      rfl
    · -- k > 0
      have h10 : 2 ≤ 10 := by decide
      have hkpos : 0 < k := by omega
      rw [digits_of_two_le_of_pos h10 hkpos]
      simp only [List.length_cons]
      unfold len_digits10_fuel
      have hk_ne_zero : ¬(k = 0) := hk0
      simp only [hk_ne_zero, ↓reduceIte]
      have h_div_lt : k / 10 < k := Nat.div_lt_self (by omega) (by decide)
      have h_div_le : k / 10 ≤ f := by omega
      rw [ih (k / 10) h_div_le]
      omega

def a_fast (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    let factors_list := primeFactorsList_fuel 15 n

    -- Calculates 10^(number of decimal digits of k)
    let pow10_len (k : ℕ) : ℕ := 10 ^ (len_digits10_fuel 28749 k)

    -- The concatenation operation: acc || factor
    let concat_op (acc factor : ℕ) : ℕ :=
      acc * pow10_len factor + factor

    (factors_list.foldl concat_op 0) % n

theorem a_eq_fast (n : ℕ) (hn28749 : n ≤ 28749) : a n = a_fast n := by
  by_cases hn : n < 2
  · unfold a a_fast
    simp [hn]
  · unfold a a_fast
    simp only [hn, ↓reduceIte]
    have h_list : n.primeFactorsList = primeFactorsList_fuel 15 n :=
      primeFactorsList_eq_fuel_15 n hn28749
    rw [h_list]
    congr 1
    apply foldl_congr
    intro acc x hx
    have h_mem : x ∈ n.primeFactorsList := by
      rwa [← h_list] at hx
    have h_dvd : x ∣ n := dvd_of_mem_primeFactorsList h_mem
    have hn0 : n ≠ 0 := by omega
    have h_le_n : x ≤ n := Nat.le_of_dvd (by omega) h_dvd
    have h_le_fuel : x ≤ 28749 := by omega
    rw [len_digits10_eq_fuel 28749 x h_le_fuel]

def composite_fast (n : ℕ) : Bool :=
  if n < 2 then false
  else decide (minFac_fuel 200 n < n)

theorem composite_fast_spec (n : ℕ) (hn28749 : n ≤ 28749) :
    composite_fast n = true ↔ Nat.composite n := by
  unfold composite_fast Nat.composite
  by_cases hn2 : n < 2
  · have : ¬ (1 < n) := by omega
    simp [hn2, this]
  · have h2n : 2 ≤ n := by omega
    have h1n : 1 < n := by omega
    simp only [hn2, ↓reduceIte, h1n, and_true, decide_eq_true_iff]
    rw [not_prime_iff_minFac_lt h2n]
    rw [minFac_eq_200 n hn28749]

def all_lt_fuel (P : ℕ → Bool) (fuel : ℕ) (start : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 => if P start then all_lt_fuel P f (start + 1) else false

theorem all_lt_fuel_spec (P : ℕ → Bool) (fuel : ℕ) (start : ℕ) :
    all_lt_fuel P fuel start = true ↔ (∀ j, start ≤ j ∧ j < start + fuel → P j = true) := by
  induction fuel generalizing start with
  | zero =>
    simp [all_lt_fuel]
  | succ f ih =>
    unfold all_lt_fuel
    by_cases hP : P start = true
    · simp only [hP, ↓reduceIte, ih]
      constructor
      · intro h j hj
        by_cases hj_start : j = start
        · rw [hj_start]; exact hP
        · have : start + 1 ≤ j := by omega
          exact h j (by omega)
      · intro h
        intro j hj
        exact h j (by omega)
    · have hP_false : P start = false := by
        cases h : P start
        · rfl
        · contradiction
      simp only [hP_false, ↓reduceIte, Bool.false_eq_true]
      constructor
      · intro h; contradiction
      · intro h
        have h_start := h start ⟨by omega, by omega⟩
        rw [h_start] at hP_false
        contradiction

def all_lt (P : ℕ → Bool) (n : ℕ) : Bool :=
  all_lt_fuel P n 0

theorem all_lt_spec (P : ℕ → Bool) (n : ℕ) :
    all_lt P n = true ↔ (∀ j < n, P j = true) := by
  unfold all_lt
  rw [all_lt_fuel_spec]
  simp only [Nat.zero_add, Nat.zero_le, true_and]

set_option maxRecDepth 100000 in
theorem leaf_0_500 : ∀ n, 0 ≤ n ∧ n < 500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 0) && (a_fast (i + 0) == 0))) (500 - 0) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 0) (by omega)
  have h_eq : (n - 0) + 0 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_500_1000 : ∀ n, 500 ≤ n ∧ n < 1000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 500) && (a_fast (i + 500) == 0))) (1000 - 500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 500) (by omega)
  have h_eq : (n - 500) + 500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_0_1000 : ∀ n, 0 ≤ n ∧ n < 1000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 500
  · exact leaf_0_500 n ⟨hn.1, h⟩
  · exact leaf_500_1000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_1000_1500 : ∀ n, 1000 ≤ n ∧ n < 1500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 1000) && (a_fast (i + 1000) == 0))) (1500 - 1000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 1000) (by omega)
  have h_eq : (n - 1000) + 1000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_1500_2000 : ∀ n, 1500 ≤ n ∧ n < 2000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 1500) && (a_fast (i + 1500) == 0))) (2000 - 1500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 1500) (by omega)
  have h_eq : (n - 1500) + 1500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_1000_2000 : ∀ n, 1000 ≤ n ∧ n < 2000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 1500
  · exact leaf_1000_1500 n ⟨hn.1, h⟩
  · exact leaf_1500_2000 n ⟨by omega, hn.2⟩

theorem node_0_2000 : ∀ n, 0 ≤ n ∧ n < 2000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 1000
  · exact node_0_1000 n ⟨hn.1, h⟩
  · exact node_1000_2000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_2000_2500 : ∀ n, 2000 ≤ n ∧ n < 2500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 2000) && (a_fast (i + 2000) == 0))) (2500 - 2000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 2000) (by omega)
  have h_eq : (n - 2000) + 2000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_2500_3000 : ∀ n, 2500 ≤ n ∧ n < 3000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 2500) && (a_fast (i + 2500) == 0))) (3000 - 2500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 2500) (by omega)
  have h_eq : (n - 2500) + 2500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_2000_3000 : ∀ n, 2000 ≤ n ∧ n < 3000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 2500
  · exact leaf_2000_2500 n ⟨hn.1, h⟩
  · exact leaf_2500_3000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_3000_3500 : ∀ n, 3000 ≤ n ∧ n < 3500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 3000) && (a_fast (i + 3000) == 0))) (3500 - 3000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 3000) (by omega)
  have h_eq : (n - 3000) + 3000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_3500_4000 : ∀ n, 3500 ≤ n ∧ n < 4000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 3500) && (a_fast (i + 3500) == 0))) (4000 - 3500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 3500) (by omega)
  have h_eq : (n - 3500) + 3500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_3000_4000 : ∀ n, 3000 ≤ n ∧ n < 4000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 3500
  · exact leaf_3000_3500 n ⟨hn.1, h⟩
  · exact leaf_3500_4000 n ⟨by omega, hn.2⟩

theorem node_2000_4000 : ∀ n, 2000 ≤ n ∧ n < 4000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 3000
  · exact node_2000_3000 n ⟨hn.1, h⟩
  · exact node_3000_4000 n ⟨by omega, hn.2⟩

theorem node_0_4000 : ∀ n, 0 ≤ n ∧ n < 4000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 2000
  · exact node_0_2000 n ⟨hn.1, h⟩
  · exact node_2000_4000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_4000_4500 : ∀ n, 4000 ≤ n ∧ n < 4500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 4000) && (a_fast (i + 4000) == 0))) (4500 - 4000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 4000) (by omega)
  have h_eq : (n - 4000) + 4000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_4500_5000 : ∀ n, 4500 ≤ n ∧ n < 5000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 4500) && (a_fast (i + 4500) == 0))) (5000 - 4500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 4500) (by omega)
  have h_eq : (n - 4500) + 4500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_4000_5000 : ∀ n, 4000 ≤ n ∧ n < 5000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 4500
  · exact leaf_4000_4500 n ⟨hn.1, h⟩
  · exact leaf_4500_5000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_5000_5500 : ∀ n, 5000 ≤ n ∧ n < 5500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 5000) && (a_fast (i + 5000) == 0))) (5500 - 5000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 5000) (by omega)
  have h_eq : (n - 5000) + 5000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_5500_6000 : ∀ n, 5500 ≤ n ∧ n < 6000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 5500) && (a_fast (i + 5500) == 0))) (6000 - 5500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 5500) (by omega)
  have h_eq : (n - 5500) + 5500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_5000_6000 : ∀ n, 5000 ≤ n ∧ n < 6000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 5500
  · exact leaf_5000_5500 n ⟨hn.1, h⟩
  · exact leaf_5500_6000 n ⟨by omega, hn.2⟩

theorem node_4000_6000 : ∀ n, 4000 ≤ n ∧ n < 6000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 5000
  · exact node_4000_5000 n ⟨hn.1, h⟩
  · exact node_5000_6000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_6000_6500 : ∀ n, 6000 ≤ n ∧ n < 6500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 6000) && (a_fast (i + 6000) == 0))) (6500 - 6000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 6000) (by omega)
  have h_eq : (n - 6000) + 6000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_6500_7000 : ∀ n, 6500 ≤ n ∧ n < 7000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 6500) && (a_fast (i + 6500) == 0))) (7000 - 6500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 6500) (by omega)
  have h_eq : (n - 6500) + 6500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_6000_7000 : ∀ n, 6000 ≤ n ∧ n < 7000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 6500
  · exact leaf_6000_6500 n ⟨hn.1, h⟩
  · exact leaf_6500_7000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_7000_7500 : ∀ n, 7000 ≤ n ∧ n < 7500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 7000) && (a_fast (i + 7000) == 0))) (7500 - 7000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 7000) (by omega)
  have h_eq : (n - 7000) + 7000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_7500_8000 : ∀ n, 7500 ≤ n ∧ n < 8000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 7500) && (a_fast (i + 7500) == 0))) (8000 - 7500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 7500) (by omega)
  have h_eq : (n - 7500) + 7500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_7000_8000 : ∀ n, 7000 ≤ n ∧ n < 8000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 7500
  · exact leaf_7000_7500 n ⟨hn.1, h⟩
  · exact leaf_7500_8000 n ⟨by omega, hn.2⟩

theorem node_6000_8000 : ∀ n, 6000 ≤ n ∧ n < 8000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 7000
  · exact node_6000_7000 n ⟨hn.1, h⟩
  · exact node_7000_8000 n ⟨by omega, hn.2⟩

theorem node_4000_8000 : ∀ n, 4000 ≤ n ∧ n < 8000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 6000
  · exact node_4000_6000 n ⟨hn.1, h⟩
  · exact node_6000_8000 n ⟨by omega, hn.2⟩

theorem node_0_8000 : ∀ n, 0 ≤ n ∧ n < 8000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 4000
  · exact node_0_4000 n ⟨hn.1, h⟩
  · exact node_4000_8000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_8000_8500 : ∀ n, 8000 ≤ n ∧ n < 8500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 8000) && (a_fast (i + 8000) == 0))) (8500 - 8000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 8000) (by omega)
  have h_eq : (n - 8000) + 8000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_8500_9000 : ∀ n, 8500 ≤ n ∧ n < 9000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 8500) && (a_fast (i + 8500) == 0))) (9000 - 8500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 8500) (by omega)
  have h_eq : (n - 8500) + 8500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_8000_9000 : ∀ n, 8000 ≤ n ∧ n < 9000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 8500
  · exact leaf_8000_8500 n ⟨hn.1, h⟩
  · exact leaf_8500_9000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_9000_9500 : ∀ n, 9000 ≤ n ∧ n < 9500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 9000) && (a_fast (i + 9000) == 0))) (9500 - 9000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 9000) (by omega)
  have h_eq : (n - 9000) + 9000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_9500_10000 : ∀ n, 9500 ≤ n ∧ n < 10000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 9500) && (a_fast (i + 9500) == 0))) (10000 - 9500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 9500) (by omega)
  have h_eq : (n - 9500) + 9500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_9000_10000 : ∀ n, 9000 ≤ n ∧ n < 10000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 9500
  · exact leaf_9000_9500 n ⟨hn.1, h⟩
  · exact leaf_9500_10000 n ⟨by omega, hn.2⟩

theorem node_8000_10000 : ∀ n, 8000 ≤ n ∧ n < 10000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 9000
  · exact node_8000_9000 n ⟨hn.1, h⟩
  · exact node_9000_10000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_10000_10500 : ∀ n, 10000 ≤ n ∧ n < 10500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 10000) && (a_fast (i + 10000) == 0))) (10500 - 10000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 10000) (by omega)
  have h_eq : (n - 10000) + 10000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_10500_11000 : ∀ n, 10500 ≤ n ∧ n < 11000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 10500) && (a_fast (i + 10500) == 0))) (11000 - 10500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 10500) (by omega)
  have h_eq : (n - 10500) + 10500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_10000_11000 : ∀ n, 10000 ≤ n ∧ n < 11000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 10500
  · exact leaf_10000_10500 n ⟨hn.1, h⟩
  · exact leaf_10500_11000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_11000_11500 : ∀ n, 11000 ≤ n ∧ n < 11500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 11000) && (a_fast (i + 11000) == 0))) (11500 - 11000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 11000) (by omega)
  have h_eq : (n - 11000) + 11000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_11500_12000 : ∀ n, 11500 ≤ n ∧ n < 12000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 11500) && (a_fast (i + 11500) == 0))) (12000 - 11500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 11500) (by omega)
  have h_eq : (n - 11500) + 11500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_11000_12000 : ∀ n, 11000 ≤ n ∧ n < 12000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 11500
  · exact leaf_11000_11500 n ⟨hn.1, h⟩
  · exact leaf_11500_12000 n ⟨by omega, hn.2⟩

theorem node_10000_12000 : ∀ n, 10000 ≤ n ∧ n < 12000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 11000
  · exact node_10000_11000 n ⟨hn.1, h⟩
  · exact node_11000_12000 n ⟨by omega, hn.2⟩

theorem node_8000_12000 : ∀ n, 8000 ≤ n ∧ n < 12000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 10000
  · exact node_8000_10000 n ⟨hn.1, h⟩
  · exact node_10000_12000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_12000_12500 : ∀ n, 12000 ≤ n ∧ n < 12500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 12000) && (a_fast (i + 12000) == 0))) (12500 - 12000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 12000) (by omega)
  have h_eq : (n - 12000) + 12000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_12500_13000 : ∀ n, 12500 ≤ n ∧ n < 13000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 12500) && (a_fast (i + 12500) == 0))) (13000 - 12500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 12500) (by omega)
  have h_eq : (n - 12500) + 12500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_12000_13000 : ∀ n, 12000 ≤ n ∧ n < 13000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 12500
  · exact leaf_12000_12500 n ⟨hn.1, h⟩
  · exact leaf_12500_13000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_13000_13500 : ∀ n, 13000 ≤ n ∧ n < 13500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 13000) && (a_fast (i + 13000) == 0))) (13500 - 13000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 13000) (by omega)
  have h_eq : (n - 13000) + 13000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_13500_14000 : ∀ n, 13500 ≤ n ∧ n < 14000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 13500) && (a_fast (i + 13500) == 0))) (14000 - 13500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 13500) (by omega)
  have h_eq : (n - 13500) + 13500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_13000_14000 : ∀ n, 13000 ≤ n ∧ n < 14000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 13500
  · exact leaf_13000_13500 n ⟨hn.1, h⟩
  · exact leaf_13500_14000 n ⟨by omega, hn.2⟩

theorem node_12000_14000 : ∀ n, 12000 ≤ n ∧ n < 14000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 13000
  · exact node_12000_13000 n ⟨hn.1, h⟩
  · exact node_13000_14000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_14000_14500 : ∀ n, 14000 ≤ n ∧ n < 14500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 14000) && (a_fast (i + 14000) == 0))) (14500 - 14000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 14000) (by omega)
  have h_eq : (n - 14000) + 14000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_14500_15000 : ∀ n, 14500 ≤ n ∧ n < 15000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 14500) && (a_fast (i + 14500) == 0))) (15000 - 14500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 14500) (by omega)
  have h_eq : (n - 14500) + 14500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_14000_15000 : ∀ n, 14000 ≤ n ∧ n < 15000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 14500
  · exact leaf_14000_14500 n ⟨hn.1, h⟩
  · exact leaf_14500_15000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_15000_15500 : ∀ n, 15000 ≤ n ∧ n < 15500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 15000) && (a_fast (i + 15000) == 0))) (15500 - 15000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 15000) (by omega)
  have h_eq : (n - 15000) + 15000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_15500_16000 : ∀ n, 15500 ≤ n ∧ n < 16000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 15500) && (a_fast (i + 15500) == 0))) (16000 - 15500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 15500) (by omega)
  have h_eq : (n - 15500) + 15500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_15000_16000 : ∀ n, 15000 ≤ n ∧ n < 16000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 15500
  · exact leaf_15000_15500 n ⟨hn.1, h⟩
  · exact leaf_15500_16000 n ⟨by omega, hn.2⟩

theorem node_14000_16000 : ∀ n, 14000 ≤ n ∧ n < 16000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 15000
  · exact node_14000_15000 n ⟨hn.1, h⟩
  · exact node_15000_16000 n ⟨by omega, hn.2⟩

theorem node_12000_16000 : ∀ n, 12000 ≤ n ∧ n < 16000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 14000
  · exact node_12000_14000 n ⟨hn.1, h⟩
  · exact node_14000_16000 n ⟨by omega, hn.2⟩

theorem node_8000_16000 : ∀ n, 8000 ≤ n ∧ n < 16000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 12000
  · exact node_8000_12000 n ⟨hn.1, h⟩
  · exact node_12000_16000 n ⟨by omega, hn.2⟩

theorem node_0_16000 : ∀ n, 0 ≤ n ∧ n < 16000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 8000
  · exact node_0_8000 n ⟨hn.1, h⟩
  · exact node_8000_16000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_16000_16500 : ∀ n, 16000 ≤ n ∧ n < 16500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 16000) && (a_fast (i + 16000) == 0))) (16500 - 16000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 16000) (by omega)
  have h_eq : (n - 16000) + 16000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_16500_17000 : ∀ n, 16500 ≤ n ∧ n < 17000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 16500) && (a_fast (i + 16500) == 0))) (17000 - 16500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 16500) (by omega)
  have h_eq : (n - 16500) + 16500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_16000_17000 : ∀ n, 16000 ≤ n ∧ n < 17000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 16500
  · exact leaf_16000_16500 n ⟨hn.1, h⟩
  · exact leaf_16500_17000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_17000_17500 : ∀ n, 17000 ≤ n ∧ n < 17500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 17000) && (a_fast (i + 17000) == 0))) (17500 - 17000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 17000) (by omega)
  have h_eq : (n - 17000) + 17000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_17500_18000 : ∀ n, 17500 ≤ n ∧ n < 18000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 17500) && (a_fast (i + 17500) == 0))) (18000 - 17500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 17500) (by omega)
  have h_eq : (n - 17500) + 17500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_17000_18000 : ∀ n, 17000 ≤ n ∧ n < 18000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 17500
  · exact leaf_17000_17500 n ⟨hn.1, h⟩
  · exact leaf_17500_18000 n ⟨by omega, hn.2⟩

theorem node_16000_18000 : ∀ n, 16000 ≤ n ∧ n < 18000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 17000
  · exact node_16000_17000 n ⟨hn.1, h⟩
  · exact node_17000_18000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_18000_18500 : ∀ n, 18000 ≤ n ∧ n < 18500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 18000) && (a_fast (i + 18000) == 0))) (18500 - 18000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 18000) (by omega)
  have h_eq : (n - 18000) + 18000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_18500_19000 : ∀ n, 18500 ≤ n ∧ n < 19000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 18500) && (a_fast (i + 18500) == 0))) (19000 - 18500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 18500) (by omega)
  have h_eq : (n - 18500) + 18500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_18000_19000 : ∀ n, 18000 ≤ n ∧ n < 19000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 18500
  · exact leaf_18000_18500 n ⟨hn.1, h⟩
  · exact leaf_18500_19000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_19000_19500 : ∀ n, 19000 ≤ n ∧ n < 19500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 19000) && (a_fast (i + 19000) == 0))) (19500 - 19000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 19000) (by omega)
  have h_eq : (n - 19000) + 19000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_19500_20000 : ∀ n, 19500 ≤ n ∧ n < 20000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 19500) && (a_fast (i + 19500) == 0))) (20000 - 19500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 19500) (by omega)
  have h_eq : (n - 19500) + 19500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_19000_20000 : ∀ n, 19000 ≤ n ∧ n < 20000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 19500
  · exact leaf_19000_19500 n ⟨hn.1, h⟩
  · exact leaf_19500_20000 n ⟨by omega, hn.2⟩

theorem node_18000_20000 : ∀ n, 18000 ≤ n ∧ n < 20000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 19000
  · exact node_18000_19000 n ⟨hn.1, h⟩
  · exact node_19000_20000 n ⟨by omega, hn.2⟩

theorem node_16000_20000 : ∀ n, 16000 ≤ n ∧ n < 20000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 18000
  · exact node_16000_18000 n ⟨hn.1, h⟩
  · exact node_18000_20000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_20000_20500 : ∀ n, 20000 ≤ n ∧ n < 20500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 20000) && (a_fast (i + 20000) == 0))) (20500 - 20000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 20000) (by omega)
  have h_eq : (n - 20000) + 20000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_20500_21000 : ∀ n, 20500 ≤ n ∧ n < 21000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 20500) && (a_fast (i + 20500) == 0))) (21000 - 20500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 20500) (by omega)
  have h_eq : (n - 20500) + 20500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_20000_21000 : ∀ n, 20000 ≤ n ∧ n < 21000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 20500
  · exact leaf_20000_20500 n ⟨hn.1, h⟩
  · exact leaf_20500_21000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_21000_21500 : ∀ n, 21000 ≤ n ∧ n < 21500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 21000) && (a_fast (i + 21000) == 0))) (21500 - 21000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 21000) (by omega)
  have h_eq : (n - 21000) + 21000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_21500_22000 : ∀ n, 21500 ≤ n ∧ n < 22000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 21500) && (a_fast (i + 21500) == 0))) (22000 - 21500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 21500) (by omega)
  have h_eq : (n - 21500) + 21500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_21000_22000 : ∀ n, 21000 ≤ n ∧ n < 22000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 21500
  · exact leaf_21000_21500 n ⟨hn.1, h⟩
  · exact leaf_21500_22000 n ⟨by omega, hn.2⟩

theorem node_20000_22000 : ∀ n, 20000 ≤ n ∧ n < 22000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 21000
  · exact node_20000_21000 n ⟨hn.1, h⟩
  · exact node_21000_22000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_22000_22500 : ∀ n, 22000 ≤ n ∧ n < 22500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 22000) && (a_fast (i + 22000) == 0))) (22500 - 22000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 22000) (by omega)
  have h_eq : (n - 22000) + 22000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_22500_23000 : ∀ n, 22500 ≤ n ∧ n < 23000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 22500) && (a_fast (i + 22500) == 0))) (23000 - 22500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 22500) (by omega)
  have h_eq : (n - 22500) + 22500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_22000_23000 : ∀ n, 22000 ≤ n ∧ n < 23000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 22500
  · exact leaf_22000_22500 n ⟨hn.1, h⟩
  · exact leaf_22500_23000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_23000_23500 : ∀ n, 23000 ≤ n ∧ n < 23500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 23000) && (a_fast (i + 23000) == 0))) (23500 - 23000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 23000) (by omega)
  have h_eq : (n - 23000) + 23000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_23500_24000 : ∀ n, 23500 ≤ n ∧ n < 24000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 23500) && (a_fast (i + 23500) == 0))) (24000 - 23500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 23500) (by omega)
  have h_eq : (n - 23500) + 23500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_23000_24000 : ∀ n, 23000 ≤ n ∧ n < 24000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 23500
  · exact leaf_23000_23500 n ⟨hn.1, h⟩
  · exact leaf_23500_24000 n ⟨by omega, hn.2⟩

theorem node_22000_24000 : ∀ n, 22000 ≤ n ∧ n < 24000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 23000
  · exact node_22000_23000 n ⟨hn.1, h⟩
  · exact node_23000_24000 n ⟨by omega, hn.2⟩

theorem node_20000_24000 : ∀ n, 20000 ≤ n ∧ n < 24000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 22000
  · exact node_20000_22000 n ⟨hn.1, h⟩
  · exact node_22000_24000 n ⟨by omega, hn.2⟩

theorem node_16000_24000 : ∀ n, 16000 ≤ n ∧ n < 24000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 20000
  · exact node_16000_20000 n ⟨hn.1, h⟩
  · exact node_20000_24000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_24000_24500 : ∀ n, 24000 ≤ n ∧ n < 24500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 24000) && (a_fast (i + 24000) == 0))) (24500 - 24000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 24000) (by omega)
  have h_eq : (n - 24000) + 24000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_24500_25000 : ∀ n, 24500 ≤ n ∧ n < 25000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 24500) && (a_fast (i + 24500) == 0))) (25000 - 24500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 24500) (by omega)
  have h_eq : (n - 24500) + 24500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_24000_25000 : ∀ n, 24000 ≤ n ∧ n < 25000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 24500
  · exact leaf_24000_24500 n ⟨hn.1, h⟩
  · exact leaf_24500_25000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_25000_25500 : ∀ n, 25000 ≤ n ∧ n < 25500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 25000) && (a_fast (i + 25000) == 0))) (25500 - 25000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 25000) (by omega)
  have h_eq : (n - 25000) + 25000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_25500_26000 : ∀ n, 25500 ≤ n ∧ n < 26000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 25500) && (a_fast (i + 25500) == 0))) (26000 - 25500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 25500) (by omega)
  have h_eq : (n - 25500) + 25500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_25000_26000 : ∀ n, 25000 ≤ n ∧ n < 26000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 25500
  · exact leaf_25000_25500 n ⟨hn.1, h⟩
  · exact leaf_25500_26000 n ⟨by omega, hn.2⟩

theorem node_24000_26000 : ∀ n, 24000 ≤ n ∧ n < 26000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 25000
  · exact node_24000_25000 n ⟨hn.1, h⟩
  · exact node_25000_26000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_26000_26500 : ∀ n, 26000 ≤ n ∧ n < 26500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 26000) && (a_fast (i + 26000) == 0))) (26500 - 26000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 26000) (by omega)
  have h_eq : (n - 26000) + 26000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_26500_27000 : ∀ n, 26500 ≤ n ∧ n < 27000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 26500) && (a_fast (i + 26500) == 0))) (27000 - 26500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 26500) (by omega)
  have h_eq : (n - 26500) + 26500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_26000_27000 : ∀ n, 26000 ≤ n ∧ n < 27000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 26500
  · exact leaf_26000_26500 n ⟨hn.1, h⟩
  · exact leaf_26500_27000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_27000_27500 : ∀ n, 27000 ≤ n ∧ n < 27500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 27000) && (a_fast (i + 27000) == 0))) (27500 - 27000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 27000) (by omega)
  have h_eq : (n - 27000) + 27000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_27500_28000 : ∀ n, 27500 ≤ n ∧ n < 28000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 27500) && (a_fast (i + 27500) == 0))) (28000 - 27500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 27500) (by omega)
  have h_eq : (n - 27500) + 27500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_27000_28000 : ∀ n, 27000 ≤ n ∧ n < 28000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 27500
  · exact leaf_27000_27500 n ⟨hn.1, h⟩
  · exact leaf_27500_28000 n ⟨by omega, hn.2⟩

theorem node_26000_28000 : ∀ n, 26000 ≤ n ∧ n < 28000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 27000
  · exact node_26000_27000 n ⟨hn.1, h⟩
  · exact node_27000_28000 n ⟨by omega, hn.2⟩

theorem node_24000_28000 : ∀ n, 24000 ≤ n ∧ n < 28000 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 26000
  · exact node_24000_26000 n ⟨hn.1, h⟩
  · exact node_26000_28000 n ⟨by omega, hn.2⟩

set_option maxRecDepth 100000 in
theorem leaf_28000_28500 : ∀ n, 28000 ≤ n ∧ n < 28500 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 28000) && (a_fast (i + 28000) == 0))) (28500 - 28000) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 28000) (by omega)
  have h_eq : (n - 28000) + 28000 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

set_option maxRecDepth 100000 in
theorem leaf_28500_28749 : ∀ n, 28500 ≤ n ∧ n < 28749 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  have h_all : all_lt (fun i => ! (composite_fast (i + 28500) && (a_fast (i + 28500) == 0))) (28749 - 28500) = true := by
    decide
  rw [all_lt_spec] at h_all
  have h_n := h_all (n - 28500) (by omega)
  have h_eq : (n - 28500) + 28500 = n := by omega
  rw [h_eq] at h_n
  intro h_and
  have h_comp : composite_fast n = true := by
    rw [composite_fast_spec n (by omega)]
    exact h_and.1
  have h_zero : (a_fast n == 0) = true := by
    rw [h_and.2]
    rfl
  simp only [h_comp, h_zero, Bool.and_true, Bool.not_true] at h_n
  contradiction

theorem node_28000_28749 : ∀ n, 28000 ≤ n ∧ n < 28749 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 28500
  · exact leaf_28000_28500 n ⟨hn.1, h⟩
  · exact leaf_28500_28749 n ⟨by omega, hn.2⟩

theorem node_24000_28749 : ∀ n, 24000 ≤ n ∧ n < 28749 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 28000
  · exact node_24000_28000 n ⟨hn.1, h⟩
  · exact node_28000_28749 n ⟨by omega, hn.2⟩

theorem node_16000_28749 : ∀ n, 16000 ≤ n ∧ n < 28749 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 24000
  · exact node_16000_24000 n ⟨hn.1, h⟩
  · exact node_24000_28749 n ⟨by omega, hn.2⟩

theorem node_0_28749 : ∀ n, 0 ≤ n ∧ n < 28749 → ¬ (Nat.composite n ∧ a_fast n = 0) := by
  intro n hn
  by_cases h : n < 16000
  · exact node_0_16000 n ⟨hn.1, h⟩
  · exact node_16000_28749 n ⟨by omega, hn.2⟩

theorem oeis_340592_conjecture_0 :
  (Nat.composite 28749 ∧ a 28749 = 0) ∧
  (∀ n : ℕ, Nat.composite n ∧ n < 28749 → a n ≠ 0) := by
  constructor
  · constructor
    · unfold Nat.composite
      constructor
      · rw [not_prime_iff_minFac_lt (by decide)]
        rw [minFac_eq_200 28749 (by omega)]
        decide
      · decide
    · rw [a_eq_fast 28749 (by omega)]
      decide
  · intro n hn
    rw [a_eq_fast n (by omega)]
    have h_fast := node_0_28749 n ⟨by omega, hn.2⟩
    intro h_zero
    exact h_fast ⟨hn.1, h_zero⟩

