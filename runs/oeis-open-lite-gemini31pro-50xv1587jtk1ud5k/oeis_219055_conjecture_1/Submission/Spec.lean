import FormalConjectures.Util.ProblemImports
open Nat Finset

def A219055 (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun q : ℕ =>
    ((1 + n % 2) + 1) * q < n ∧
    q.Prime ∧
    (q + 6).Prime ∧
    (n - (1 + n % 2) * q).Prime ∧
    (n - (1 + n % 2) * q - 6).Prime
  ) (Finset.range n)

def goldbach_conjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q

def lemoine_conjecture : Prop :=
  ∀ n : ℕ, 7 ≤ n → Odd n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q

def six_prime_gap_conjecture : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ (p + 6).Prime}

def a219055_core_conjecture : Prop :=
  ∀ n : ℕ,
    (Even n ∧ 8012 < n) ∨ (Odd n ∧ 15727 < n)
      → A219055 n > 0

lemma prime_not_dvd_of_gt_of_dvd {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q) (hq_lt : q < p) (h_dvd : q ∣ p) : False := by
  have : q = 1 ∨ q = p := hp.eq_one_or_self_of_dvd q h_dvd
  rcases this with rfl | rfl
  · omega
  · omega

lemma factorial_ge_self {M q : ℕ} (hq : q ≤ M) (hq_pos : 0 < q) : q ≤ M.factorial := by
  have : q ∣ M.factorial := Nat.dvd_factorial hq_pos hq
  exact Nat.le_of_dvd (Nat.factorial_pos M) this

lemma sexy_primes_infinite (hCore : a219055_core_conjecture) : six_prime_gap_conjecture := by
  intro hFin
  rcases hFin.bddAbove with ⟨M, hM⟩
  let n := 16028 * M.factorial
  have hn_even : Even n := by
    unfold n
    exact even_iff_two_dvd.mpr ⟨8014 * M.factorial, by omega⟩
  have hn_gt : 8012 < n := by
    unfold n
    have : 1 ≤ M.factorial := Nat.factorial_pos M
    omega
  have hA := hCore n (Or.inl ⟨hn_even, hn_gt⟩)
  unfold A219055 at hA
  have h_pos : 0 < Finset.card (Finset.filter _ _) := hA
  obtain ⟨q, hq⟩ := Finset.card_pos.mp h_pos
  rw [Finset.mem_filter, Finset.mem_range] at hq
  rcases hq with ⟨hq_range, hq_lt, hq_prime, hq6_prime, hp_prime, _⟩
  have hn_mod2 : n % 2 = 0 := Nat.even_iff.mp hn_even
  have h_sub : n - (1 + n % 2) * q = n - q := by
    rw [hn_mod2]
    omega
  rw [h_sub] at hp_prime
  have hq_in_S : q ∈ {p : ℕ | p.Prime ∧ (p + 6).Prime} := ⟨hq_prime, hq6_prime⟩
  have hq_le_M : q ≤ M := hM hq_in_S
  have hq_dvd_Mfac : q ∣ M.factorial := Nat.dvd_factorial (Nat.Prime.pos hq_prime) hq_le_M
  have hq_dvd_n : q ∣ n := dvd_trans hq_dvd_Mfac (dvd_mul_left _ _)
  have hq_dvd_p : q ∣ (n - q) := Nat.dvd_sub hq_dvd_n dvd_rfl
  have hq_ge2 : 2 ≤ q := hq_prime.two_le
  have hq_lt_p : q < n - q := by
    have h1 : q ≤ M.factorial := factorial_ge_self hq_le_M (Nat.Prime.pos hq_prime)
    have h2 : 16028 * q ≤ n := by
      unfold n
      gcongr
    omega
  exact prime_not_dvd_of_gt_of_dvd hp_prime hq_ge2 hq_lt_p hq_dvd_p

def minFacAux_fuel (n fuel k : ℕ) : ℕ :=
  match fuel with
  | 0 => n
  | f + 1 =>
    if n < k * k then n
    else if k ∣ n then k
    else minFacAux_fuel n f (k + 2)

lemma n_lt_k_sq {n k : ℕ} (h : n.sqrt + 2 - k ≤ 0) : n < k * k := by
  have h1 : n.sqrt < k := by omega
  have h2 : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
  nlinarith

lemma minFacAux_fuel_eq (n : ℕ) : ∀ f k, n.sqrt + 2 - k ≤ f → minFacAux_fuel n f k = n.minFacAux k := by
  intro f
  induction f with
  | zero =>
    intro k h
    have h_lt : n < k * k := n_lt_k_sq h
    rw [minFacAux_fuel, Nat.minFacAux, if_pos h_lt]
  | succ f ih =>
    intro k h
    rw [minFacAux_fuel, Nat.minFacAux]
    split_ifs with h1 h2
    · rfl
    · rfl
    · apply ih
      omega

def check_prime (n : ℕ) : Bool :=
  if n < 2 then false
  else if n % 2 = 0 then n == 2
  else minFacAux_fuel n n 3 == n

lemma check_prime_eq_prime (n : ℕ) : check_prime n = true ↔ n.Prime := by
  rw [check_prime]
  split_ifs with h1 h2
  · exact iff_of_false (by simp) (by intro hp; have := hp.two_le; omega)
  · constructor
    · intro h
      have h_eq : n = 2 := beq_iff_eq.mp h
      rw [h_eq]
      exact Nat.prime_two
    · intro h
      have h_dvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero h2
      have h_eq2 : n = 2 := (Nat.Prime.eq_two_or_odd h).resolve_right (by omega)
      exact beq_iff_eq.mpr h_eq2
  · have h_fuel : n.sqrt + 2 - 3 ≤ n := by
      have : n.sqrt ≤ n := Nat.sqrt_le_self n
      omega
    have h_minFac : minFacAux_fuel n n 3 = n.minFacAux 3 := minFacAux_fuel_eq n n 3 h_fuel
    have hn2 : 2 ≤ n := by omega
    have hnd2 : ¬(2 ∣ n) := by
      intro h_dvd
      have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
      omega
    have h_minFac_eq : n.minFac = n.minFacAux 3 := by
      rw [Nat.minFac_eq]
      rw [if_neg hnd2]
    rw [h_minFac, ← h_minFac_eq]
    constructor
    · intro h
      have h_eq : n.minFac = n := beq_iff_eq.mp h
      exact Nat.prime_def_minFac.mpr ⟨hn2, h_eq⟩
    · intro h
      exact beq_iff_eq.mpr h.minFac_eq

def check_goldbach_for (n fuel q : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if q ≥ n then false
    else if check_prime q ∧ check_prime (n - q) then true
    else check_goldbach_for n f (q + 1)

lemma check_goldbach_for_imp (n : ℕ) : ∀ fuel q, check_goldbach_for n fuel q = true → ∃ p q', p.Prime ∧ q'.Prime ∧ n = p + q' := by
  intro fuel
  induction fuel with
  | zero =>
    intro q h; contradiction
  | succ f ih =>
    intro q
    unfold check_goldbach_for
    split_ifs with h1 h2
    · intro h; contradiction
    · intro h
      have hp : q.Prime := (check_prime_eq_prime q).mp h2.1
      have hq : (n - q).Prime := (check_prime_eq_prime (n - q)).mp h2.2
      use (n - q), q
      have : n = (n - q) + q := by omega
      exact ⟨hq, hp, this⟩
    · intro h; exact ih (q + 1) h

def check_goldbach_range (start : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 =>
    let n := start + len
    if n % 2 = 0 ∧ n ≥ 4 then
      if check_goldbach_for n n 2 then check_goldbach_range start len else false
    else check_goldbach_range start len

lemma check_goldbach_range_imp : ∀ len start, check_goldbach_range start len = true → ∀ m, start ≤ m → m < start + len → m ≥ 4 → Even m → ∃ p q, p.Prime ∧ q.Prime ∧ m = p + q := by
  intro len
  induction len with
  | zero =>
    intro start h m hs hl h4 hodd
    omega
  | succ len ih =>
    intro start h m hs hl h4 hodd
    unfold check_goldbach_range at h
    dsimp at h
    split_ifs at h with h1 h2
    · have hm_le : m ≤ start + len := by omega
      rcases eq_or_lt_of_le hm_le with rfl | hmlt
      · exact check_goldbach_for_imp (start + len) (start + len) 2 h2
      · exact ih start h m hs hmlt h4 hodd
    · have hm_le : m ≤ start + len := by omega
      rcases eq_or_lt_of_le hm_le with rfl | hmlt
      · have : (start + len) % 2 = 0 := Nat.even_iff.mp hodd
        omega
      · exact ih start h m hs hmlt h4 hodd

def check_lemoine_for (n fuel q : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if 2 * q ≥ n then false
    else if check_prime q ∧ check_prime (n - 2 * q) then true
    else check_lemoine_for n f (q + 1)

lemma check_lemoine_for_imp (n : ℕ) : ∀ fuel q, check_lemoine_for n fuel q = true → ∃ p q', p.Prime ∧ q'.Prime ∧ n = p + 2 * q' := by
  intro fuel
  induction fuel with
  | zero =>
    intro q h; contradiction
  | succ f ih =>
    intro q
    unfold check_lemoine_for
    split_ifs with h1 h2
    · intro h; contradiction
    · intro h
      have hp : q.Prime := (check_prime_eq_prime q).mp h2.1
      have hq : (n - 2 * q).Prime := (check_prime_eq_prime (n - 2 * q)).mp h2.2
      use (n - 2 * q), q
      have : n = (n - 2 * q) + 2 * q := by omega
      exact ⟨hq, hp, this⟩
    · intro h; exact ih (q + 1) h

def check_lemoine_range (start : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 =>
    let n := start + len
    if n % 2 = 1 ∧ n ≥ 7 then
      if check_lemoine_for n (n / 2) 2 then check_lemoine_range start len else false
    else check_lemoine_range start len

lemma check_lemoine_range_imp : ∀ len start, check_lemoine_range start len = true → ∀ m, start ≤ m → m < start + len → m ≥ 7 → Odd m → ∃ p q, p.Prime ∧ q.Prime ∧ m = p + 2 * q := by
  intro len
  induction len with
  | zero =>
    intro start h m hs hl h7 hodd
    omega
  | succ len ih =>
    intro start h m hs hl h7 hodd
    unfold check_lemoine_range at h
    dsimp at h
    split_ifs at h with h1 h2
    · have hm_le : m ≤ start + len := by omega
      rcases eq_or_lt_of_le hm_le with rfl | hmlt
      · exact check_lemoine_for_imp (start + len) ((start + len) / 2) 2 h2
      · exact ih start h m hs hmlt h7 hodd
    · have hm_le : m ≤ start + len := by omega
      rcases eq_or_lt_of_le hm_le with rfl | hmlt
      · have : (start + len) % 2 = 1 := Nat.odd_iff.mp hodd
        omega
      · exact ih start h m hs hmlt h7 hodd

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

theorem goldbach_chunk : check_goldbach_range 0 8013 = true := by decide
theorem lemoine_chunk_1 : check_lemoine_range 0 4000 = true := by decide
theorem lemoine_chunk_2 : check_lemoine_range 4000 4000 = true := by decide
theorem lemoine_chunk_3 : check_lemoine_range 8000 4000 = true := by decide
theorem lemoine_chunk_4 : check_lemoine_range 12000 3728 = true := by decide

theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture := by
  intro hCore
  refine ⟨?_, ?_, ?_⟩
  · intro n h4 heven
    by_cases hn : n > 8012
    · have hA := hCore n (Or.inl ⟨heven, hn⟩)
      unfold A219055 at hA
      have h_pos : 0 < Finset.card (Finset.filter _ _) := hA
      obtain ⟨q, hq⟩ := Finset.card_pos.mp h_pos
      rw [Finset.mem_filter, Finset.mem_range] at hq
      rcases hq with ⟨hq_range, hq_lt, hq_prime, _, hp_prime, _⟩
      have hn_mod2 : n % 2 = 0 := Nat.even_iff.mp heven
      have h_sub : n - (1 + n % 2) * q = n - q := by rw [hn_mod2]; omega
      rw [h_sub] at hp_prime
      use n - q, q
      have : n = (n - q) + q := by rw [hn_mod2] at hq_lt; omega
      exact ⟨hp_prime, hq_prime, this⟩
    · have hle : n < 8013 := by omega
      exact check_goldbach_range_imp 8013 0 goldbach_chunk n (by omega) hle h4 heven
  · intro n h7 hodd
    by_cases hn : n > 15727
    · have hA := hCore n (Or.inr ⟨hodd, hn⟩)
      unfold A219055 at hA
      have h_pos : 0 < Finset.card (Finset.filter _ _) := hA
      obtain ⟨q, hq⟩ := Finset.card_pos.mp h_pos
      rw [Finset.mem_filter, Finset.mem_range] at hq
      rcases hq with ⟨hq_range, hq_lt, hq_prime, _, hp_prime, _⟩
      have hn_mod2 : n % 2 = 1 := Nat.odd_iff.mp hodd
      have h_sub : n - (1 + n % 2) * q = n - 2 * q := by rw [hn_mod2]
      rw [h_sub] at hp_prime
      use n - 2 * q, q
      have : n = (n - 2 * q) + 2 * q := by rw [hn_mod2] at hq_lt; omega
      exact ⟨hp_prime, hq_prime, this⟩
    · have h_cases : n < 4000 ∨ (4000 ≤ n ∧ n < 8000) ∨ (8000 ≤ n ∧ n < 12000) ∨ (12000 ≤ n ∧ n < 15728) := by omega
      rcases h_cases with h1 | h2 | h3 | h4
      · exact check_lemoine_range_imp 4000 0 lemoine_chunk_1 n (by omega) h1 h7 hodd
      · exact check_lemoine_range_imp 4000 4000 lemoine_chunk_2 n h2.1 h2.2 h7 hodd
      · exact check_lemoine_range_imp 4000 8000 lemoine_chunk_3 n h3.1 h3.2 h7 hodd
      · exact check_lemoine_range_imp 3728 12000 lemoine_chunk_4 n h4.1 h4.2 h7 hodd
  · exact sexy_primes_infinite hCore

theorem oeis_219055_conjecture_1.disproof : ¬ (type_of% @oeis_219055_conjecture_1) := sorry
