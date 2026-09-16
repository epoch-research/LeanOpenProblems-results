import FormalConjectures.Util.ProblemImports
open Nat Finset

def A338777 (n : ℕ) : ℕ :=
  let m := 2 * n
  if m = 0 then 1 else
  let r := Nat.sqrt m
  let small_primes : Finset ℕ := (Finset.range (r + 1)).filter Nat.Prime
  let is_gb_associated (p : ℕ) : Prop :=
    Nat.Prime p ∧ r < p ∧ p ≤ m / 2 ∧ (∀ q ∈ small_primes, p % q ≠ m % q)
  let GB_2n : Finset ℕ := (Finset.range (m / 2 + 1)).filter is_gb_associated
  GB_2n.prod id

def GB_set (m : ℕ) : Finset ℕ :=
  if m = 0 then ∅ else
  let r := Nat.sqrt m
  let small_primes : Finset ℕ := (Finset.range (r + 1)).filter Nat.Prime
  let is_gb_associated (p : ℕ) : Prop :=
    Nat.Prime p ∧ r < p ∧ p ≤ m / 2 ∧ (∀ q ∈ small_primes, p % q ≠ m % q)
  (Finset.range (m / 2 + 1)).filter is_gb_associated

def goldbach_conjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ p1 p2 : ℕ, Nat.Prime p1 ∧ Nat.Prime p2 ∧ 2 * n = p1 + p2

lemma A338777_eq_prod (n : ℕ) (hn : n > 0) : A338777 n = (GB_set (2 * n)).prod id := by
  dsimp [A338777, GB_set]
  have hm : 2 * n ≠ 0 := by omega
  rw [if_neg hm, if_neg hm]

lemma prod_id_eq_one {s : Finset ℕ} (h : ∀ x ∈ s, x ≥ 2) : s.prod id = 1 ↔ s = ∅ := by
  constructor
  · intro h1
    by_contra h2
    have ⟨x, hx⟩ : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr h2
    have hx2 : x ≥ 2 := h x hx
    have h_prod : x ∣ s.prod id := dvd_prod_of_mem id hx
    rw [h1] at h_prod
    have h_le : x ≤ 1 := Nat.le_of_dvd zero_lt_one h_prod
    omega
  · intro h1
    rw [h1, prod_empty]

lemma gb_prop (m : ℕ) (p : ℕ) (hp : p ∈ GB_set m) :
    m ≠ 0 ∧ Nat.Prime p ∧ Nat.sqrt m < p ∧ p ≤ m / 2 ∧
    ∀ q, Nat.Prime q → q ≤ Nat.sqrt m → p % q ≠ m % q := by
  dsimp [GB_set] at hp
  split_ifs at hp with h0
  · simp at hp
  · rw [mem_filter, mem_range] at hp
    rcases hp with ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h0, h2, h3, h4, fun q hq hq2 => ?_⟩
    apply h5
    rw [mem_filter, mem_range]
    exact ⟨Nat.lt_succ_of_le hq2, hq⟩

lemma prime_sub (m p : ℕ) (hp : p ∈ GB_set m) : Nat.Prime (m - p) := by
  rcases gb_prop m p hp with ⟨hm0, hp_prime, hp_gt, hp_le, hp_mod⟩
  have hp2 : p ≥ 2 := hp_prime.two_le
  have h_sub_ge_2 : 2 ≤ m - p := by omega
  have h_le : p ≤ m := by omega
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h_sub_ge_2, fun d hd_ge2 hd_le hd_div => ?_⟩
  set q := minFac d
  have hq_prime : Nat.Prime q := minFac_prime (by omega)
  have hq_dvd_d : q ∣ d := minFac_dvd d
  have hq_dvd_sub : q ∣ m - p := dvd_trans hq_dvd_d hd_div
  have hq_le_d : q ≤ d := minFac_le (by omega)
  have hq_le_sqrt : q ≤ Nat.sqrt m := by
    calc
      q ≤ d := hq_le_d
      _ ≤ Nat.sqrt (m - p) := hd_le
      _ ≤ Nat.sqrt m := Nat.sqrt_le_sqrt (by omega)
  have h_mod := hp_mod q hq_prime hq_le_sqrt
  have h_mod2 : (m - p) % q = 0 := Nat.mod_eq_zero_of_dvd hq_dvd_sub
  have hm_eq : m = (m - p) + p := by omega
  have hm_mod : m % q = p % q := by
    rw [hm_eq, Nat.add_mod, h_mod2, zero_add, Nat.mod_mod]
  exact h_mod hm_mod.symm

lemma part2 (n : ℕ) (hn : 3 ≤ n) (ha : A338777 n ≠ 1) :
    let m2n := 2 * n
    let GB_2n := GB_set m2n
    GB_2n.Nonempty ∧
    ∃ m : ℕ, m ∈ GB_2n ∧ (∀ k ∈ GB_2n, k ≤ m) ∧ Nat.Prime (m2n - m) := by
  intro m2n GB_2n
  have h_pos : n > 0 := by omega
  have e1 : A338777 n = GB_2n.prod id := A338777_eq_prod n h_pos
  rw [e1] at ha
  have h_ge2 : ∀ x ∈ GB_2n, x ≥ 2 := fun x hx => (gb_prop m2n x hx).2.1.two_le
  have h_not_empty : GB_2n ≠ ∅ := by
    intro h_emp
    have e2 := (prod_id_eq_one h_ge2).mpr h_emp
    contradiction
  have h_nonempty : GB_2n.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_not_empty
  refine ⟨h_nonempty, ?_⟩
  set max_val := GB_2n.max' h_nonempty
  have h_max_mem : max_val ∈ GB_2n := Finset.max'_mem GB_2n h_nonempty
  have h_max_le : ∀ k ∈ GB_2n, k ≤ max_val := fun k hk => Finset.le_max' GB_2n k hk
  have h_prime_sub : Nat.Prime (m2n - max_val) := prime_sub m2n max_val h_max_mem
  exact ⟨max_val, h_max_mem, h_max_le, h_prime_sub⟩

lemma part1 (h : ∀ k : ℕ, 3 ≤ k → A338777 k ≠ 1) : goldbach_conjecture := by
  intro n hn
  have ha := h n hn
  have ⟨h_nonempty, m, hm, _, hm_prime⟩ := part2 n hn ha
  have h_m_prime : Nat.Prime m := (gb_prop (2 * n) m hm).2.1
  have hm_le : m ≤ 2 * n := by
    have h_le := (gb_prop (2 * n) m hm).2.2.2.1
    omega
  refine ⟨2 * n - m, m, hm_prime, h_m_prime, ?_⟩
  omega

