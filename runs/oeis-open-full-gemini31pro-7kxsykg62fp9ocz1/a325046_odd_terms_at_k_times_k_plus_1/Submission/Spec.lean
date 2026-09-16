import FormalConjectures.Util.ProblemImports
import Mathlib

open Nat
open Finset

def a (N : ℕ) : ℕ :=
  (range (N + 1)).sum (fun n =>
    (range (n + 1)).sum (fun k =>
      let R : ℕ := N - n * (k + 1)
      let m : ℕ := n + 1
      if n * (k + 1) ≤ N ∧ R % m = 0 then
        let j : ℕ := R / m
        n.choose k * (n + j).choose j
      else
        0
    )
  )

def a_inner (N n : ℕ) : ℕ :=
  (range (n + 1)).sum (fun k =>
    if h : n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0 then
      let j : ℕ := (N - n * (k + 1)) / (n + 1)
      n.choose k * (n + j).choose j
    else
      0
  )

def fast_inner (N n : ℕ) : ℕ :=
  let r := N % (n + 1)
  let s := N / (n + 1)
  if s + r ≥ n then
    n.choose (n - r) * (s + r).choose n
  else
    0

lemma k_unique (N n k : ℕ) (hk : k ≤ n) (h1 : n * (k + 1) ≤ N) (h2 : (N - n * (k + 1)) % (n + 1) = 0) :
  k = n - (N % (n + 1)) := by
  have hdvd : (n + 1) ∣ N - n * (k + 1) := Nat.dvd_of_mod_eq_zero h2
  rcases hdvd with ⟨c, hc⟩
  have eq1 : N = (n + 1) * c + n * (k + 1) := by omega
  have eq2 : N = (n + 1) * (c + k) + (n - k) := by
    zify [hk] at eq1 ⊢
    linear_combination eq1
  have eq3 : N % (n + 1) = n - k := by
    rw [eq2, add_comm]
    have : (n - k + (n + 1) * (c + k)) % (n + 1) = (n - k) % (n + 1) := Nat.add_mul_mod_self_left (n - k) (n + 1) (c + k)
    rw [this, Nat.mod_eq_of_lt (by omega)]
  omega

lemma j_val_proof (N n k s r c : ℕ) (hk : k = n - r) (hr : r ≤ n) (h1 : N = (n + 1) * s + r) (h2 : N = (n + 1) * c + n * (k + 1)) :
  c = s + r - n ∧ c = s - k ∧ n + c = s + r := by
  have H1 : (N : ℤ) = (n + 1 : ℤ) * s + r := by exact_mod_cast h1
  have H2 : (N : ℤ) = (n + 1 : ℤ) * c + n * (k + 1 : ℤ) := by exact_mod_cast h2
  have H3 : (k : ℤ) = n - r := by omega
  have H4 : (c : ℤ) = s + r - n := by nlinarith
  omega

lemma condition_false (N n k : ℕ) (hk : k ≤ n) (h_sr : N / (n + 1) + (N % (n + 1)) < n) :
  ¬ (n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0) := by
  intro h
  have h1 := k_unique N n k hk h.1 h.2
  have hr_le : N % (n + 1) ≤ n := by
    have : N % (n + 1) < n + 1 := Nat.mod_lt N (by omega)
    omega
  have H1 : N = (n + 1) * (N / (n + 1)) + N % (n + 1) := (Nat.div_add_mod N (n + 1)).symm
  have H2 : N - n * (k + 1) = (n + 1) * ((N - n * (k + 1)) / (n + 1)) := Nat.div_add_mod (N - n * (k + 1)) (n + 1) |>.symm |> (fun h_eq => by rw [h.2, add_zero] at h_eq; exact h_eq)
  have H3 : N = (n + 1) * ((N - n * (k + 1)) / (n + 1)) + n * (k + 1) := by omega
  have H4 := j_val_proof N n k (N / (n + 1)) (N % (n + 1)) ((N - n * (k + 1)) / (n + 1)) h1 hr_le H1 H3
  omega

lemma condition_true (N n k s r : ℕ) (hr : r = N % (n + 1)) (hs : s = N / (n + 1))
    (hk : k = n - r) (h_sr : s + r ≥ n) (hr_le : r ≤ n) :
  n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0 ∧ (N - n * (k + 1)) / (n + 1) = s - k := by
  have hN : (N : ℤ) = (n + 1 : ℤ) * s + r := by
    have : N = (n + 1) * s + r := by
      rw [hs, hr]
      exact (Nat.div_add_mod N (n + 1)).symm
    exact_mod_cast this
  have h_le : n * (k + 1) ≤ N := by
    have : (n * (k + 1) : ℤ) ≤ N := by
      have : (k : ℤ) = n - r := by omega
      nlinarith
    exact_mod_cast this
  refine ⟨h_le, ?_, ?_⟩
  · have H2 : ((N - n * (k + 1) : ℕ) : ℤ) = (n + 1 : ℤ) * (s + r - n : ℤ) := by
      have h1 : ((N - n * (k + 1) : ℕ) : ℤ) = (N : ℤ) - (n * (k + 1) : ℕ) := Nat.cast_sub h_le
      have h2 : ((n * (k + 1) : ℕ) : ℤ) = (n : ℤ) * (k + 1 : ℤ) := by push_cast; rfl
      have h3 : (k : ℤ) = n - r := by omega
      rw [h1, h2, h3]
      nlinarith
    have H3 : N - n * (k + 1) = (n + 1) * (s + r - n) := by exact_mod_cast H2
    rw [H3]
    exact Nat.mul_mod_right _ _
  · have H2 : ((N - n * (k + 1) : ℕ) : ℤ) = (n + 1 : ℤ) * (s + r - n : ℤ) := by
      have h1 : ((N - n * (k + 1) : ℕ) : ℤ) = (N : ℤ) - (n * (k + 1) : ℕ) := Nat.cast_sub h_le
      have h2 : ((n * (k + 1) : ℕ) : ℤ) = (n : ℤ) * (k + 1 : ℤ) := by push_cast; rfl
      have h3 : (k : ℤ) = n - r := by omega
      rw [h1, h2, h3]
      nlinarith
    have H3 : N - n * (k + 1) = (n + 1) * (s + r - n) := by exact_mod_cast H2
    rw [H3]
    have : (n + 1) * (s + r - n) / (n + 1) = s + r - n := Nat.mul_div_cancel_left _ (by omega)
    rw [this]
    omega

lemma sum_eq (n k_val : ℕ) (hk : k_val ∈ range (n + 1)) (f : ℕ → ℕ)
  (h_other : ∀ k ∈ range (n + 1), k ≠ k_val → f k = 0) :
  (range (n + 1)).sum f = f k_val := by
  apply sum_eq_single k_val h_other
  intro h
  contradiction

lemma a_inner_eq_fast_inner (N n : ℕ) : a_inner N n = fast_inner N n := by
  let r := N % (n + 1)
  let s := N / (n + 1)
  have hr_le : r ≤ n := by
    have : r < n + 1 := Nat.mod_lt N (by omega)
    omega
  unfold a_inner
  by_cases h_sr : s + r ≥ n
  · have h_fast : fast_inner N n = n.choose (n - r) * (s + r).choose n := by
      unfold fast_inner
      exact if_pos h_sr
    rw [h_fast]
    let k_val := n - r
    have hk_mem : k_val ∈ range (n + 1) := mem_range.mpr (by omega)
    have H_sum := sum_eq n k_val hk_mem (fun k => if h : n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0 then n.choose k * (n + (N - n * (k + 1)) / (n + 1)).choose ((N - n * (k + 1)) / (n + 1)) else 0)
    have H_cond : ∀ k ∈ range (n + 1), k ≠ k_val → (if h : n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0 then n.choose k * (n + (N - n * (k + 1)) / (n + 1)).choose ((N - n * (k + 1)) / (n + 1)) else 0) = 0 := by
      intro k hk hneq
      have h_k_le : k ≤ n := by
        have : k < n + 1 := mem_range.mp hk
        omega
      have : ¬ (n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0) := by
        intro H_cond
        have : k = k_val := k_unique N n k h_k_le H_cond.1 H_cond.2
        exact hneq this
      exact dif_neg this
    have H := H_sum H_cond
    rw [H]
    have cond := condition_true N n k_val s r rfl rfl rfl h_sr hr_le
    rw [dif_pos ⟨cond.1, cond.2.1⟩]
    have hj : (N - n * (k_val + 1)) / (n + 1) = s - k_val := cond.2.2
    have hj2 : n + (s - k_val) = s + r := by omega
    rw [hj, hj2]
    congr 1
    have h_symm : s - k_val = s + r - n := by omega
    rw [h_symm]
    exact choose_symm (by omega)
  · have h_fast : fast_inner N n = 0 := by
      unfold fast_inner
      exact if_neg h_sr
    rw [h_fast]
    apply sum_eq_zero
    intro k hk
    have h_k_le : k ≤ n := by
      have : k < n + 1 := mem_range.mp hk
      omega
    have h_sr_lt : N / (n + 1) + (N % (n + 1)) < n := by omega
    have : ¬ (n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0) := condition_false N n k h_k_le h_sr_lt
    exact dif_neg this

def f (N n : ℕ) : ZMod 2 :=
  let r := N % (n + 1)
  let s := N / (n + 1)
  if s + r ≥ n then
    (n.choose (n - r) : ZMod 2) * ((s + r).choose n : ZMod 2)
  else
    0

def g (N n : ℕ) : ℕ :=
  if f N n ≠ 0 then N / (n + 1) else n

lemma f_val_comm (n s r : ℕ) (h1 : r ≤ n) :
  n.choose (n - r) * (s + r).choose n = s.choose (n - r) * (s + r).choose s := by
  have h3 : n.choose (n - r) = n.choose r := Nat.choose_symm h1
  have h4 : (s + r).choose (s + r - s) = (s + r).choose s := Nat.choose_symm (by omega)
  have h5 : s + r - s = r := by omega
  rw [h5] at h4
  rw [h3, mul_comm, ← h4]
  have H1 : (s + r).choose n * n.choose r = (s + r).choose r * (s + r - r).choose (n - r) :=
    Nat.choose_mul (by omega)
  have H2 : s + r - r = s := by omega
  rw [H2] at H1
  rw [H1]
  ring

lemma div_mod_eq (N n s r : ℕ) (h_r : r = N % (n + 1)) (h_s : s = N / (n + 1))
    (h_sr : s + r ≥ n) :
  N / (s + 1) = n ∧ N % (s + 1) = s + r - n := by
  have H1 : N = (n + 1) * s + r := by
    rw [h_s, h_r]
    exact (Nat.div_add_mod N (n + 1)).symm
  have H2 : N = (s + 1) * n + (s + r - n) := by
    have : r ≤ n := by
      have : r < n + 1 := by
        rw [h_r]
        exact Nat.mod_lt N (by omega)
      omega
    zify [h_sr, this] at H1 ⊢
    linear_combination H1
  have H3 : s + r - n < s + 1 := by
    have : r < n + 1 := by
      rw [h_r]
      exact Nat.mod_lt N (by omega)
    omega
  refine ⟨?_, ?_⟩
  · rw [H2]
    rw [add_comm]
    have : (s + r - n + (s + 1) * n) / (s + 1) = (s + r - n) / (s + 1) + n :=
      Nat.add_mul_div_left (s + r - n) n (by omega)
    rw [this]
    have : (s + r - n) / (s + 1) = 0 := Nat.div_eq_of_lt H3
    rw [this, zero_add]
  · rw [H2]
    rw [add_comm]
    have : (s + r - n + (s + 1) * n) % (s + 1) = (s + r - n) % (s + 1) :=
      Nat.add_mul_mod_self_left (s + r - n) (s + 1) n
    rw [this]
    exact Nat.mod_eq_of_lt H3

lemma f_val_eq (N n : ℕ) (h_not_zero : f N n ≠ 0) : N / (n + 1) + (N % (n + 1)) ≥ n := by
  dsimp [f] at h_not_zero
  split_ifs at h_not_zero with h
  · exact h
  · contradiction

lemma f_g (N n : ℕ) : f N (g N n) = f N n := by
  dsimp [g]
  by_cases h_not_zero : f N n ≠ 0
  · rw [if_pos h_not_zero]
    dsimp [f] at h_not_zero ⊢
    let r := N % (n + 1)
    let s := N / (n + 1)
    have h_sr : s + r ≥ n := by
      split_ifs at h_not_zero with hc
      · exact hc
      · contradiction
    have hr_le : r ≤ n := by
      have : r < n + 1 := Nat.mod_lt N (by omega)
      omega
    have H_div_mod := div_mod_eq N n s r rfl rfl h_sr
    have H1 : N / (s + 1) = n := H_div_mod.1
    have H2 : N % (s + 1) = s + r - n := H_div_mod.2
    have H3 : n + (s + r - n) ≥ s := by omega
    have H4 : s - (s + r - n) = n - r := by omega
    have H5 : n + (s + r - n) = s + r := by omega
    have h_f : (if N / (s + 1) + N % (s + 1) ≥ s then
        (s.choose (s - N % (s + 1)) : ZMod 2) * ((N / (s + 1) + N % (s + 1)).choose s : ZMod 2)
      else 0) =
      (s.choose (n - r) : ZMod 2) * ((s + r).choose s : ZMod 2) := by
      rw [H1, H2]
      have H_if : (if n + (s + r - n) ≥ s then
          ((s.choose (s - (s + r - n)) : ZMod 2) * (n + (s + r - n)).choose s : ZMod 2)
        else 0) =
        (s.choose (n - r) : ZMod 2) * ((s + r).choose s : ZMod 2) := by
        rw [if_pos H3, H4, H5]
      exact H_if
    have eq := f_val_comm n s r hr_le
    have eq_cast : (n.choose (n - r) : ZMod 2) * ((s + r).choose n : ZMod 2) = (s.choose (n - r) : ZMod 2) * ((s + r).choose s : ZMod 2) := by
      have : ((n.choose (n - r) * (s + r).choose n : ℕ) : ZMod 2) = ((s.choose (n - r) * (s + r).choose s : ℕ) : ZMod 2) := by rw [eq]
      push_cast at this
      exact this
    have h_f_n : (if s + r ≥ n then
        (n.choose (n - r) : ZMod 2) * ((s + r).choose n : ZMod 2)
      else 0) = (n.choose (n - r) : ZMod 2) * ((s + r).choose n : ZMod 2) := by
      rw [if_pos h_sr]
    change _ = (if s + r ≥ n then _ else 0)
    rw [h_f, h_f_n, eq_cast]
  · rw [if_neg h_not_zero]

lemma g_involution (N n : ℕ) : g N (g N n) = n := by
  dsimp [g]
  by_cases h : f N n ≠ 0
  · rw [if_pos h]
    have h_f : f N (N / (n + 1)) ≠ 0 := by
      have h_fg := f_g N n
      dsimp [g] at h_fg
      rw [if_pos h] at h_fg
      rw [h_fg]
      exact h
    rw [if_pos h_f]
    let r := N % (n + 1)
    let s := N / (n + 1)
    have h_sr : s + r ≥ n := f_val_eq N n h
    have H_div_mod := div_mod_eq N n s r rfl rfl h_sr
    exact H_div_mod.1
  · rw [if_neg h]
    rw [if_neg h]

lemma choose_mul_eq (n r : ℕ) (h : r ≤ n) :
  n.choose r * (n + r).choose n = (n + r).choose (2 * r) * (2 * r).choose r := by
  have H1 : (n + r).choose (2 * r) * (2 * r).choose r = (n + r).choose r * (n + r - r).choose (2 * r - r) :=
    Nat.choose_mul (by omega)
  have H2 : n + r - r = n := by omega
  have H3 : 2 * r - r = r := by omega
  rw [H2, H3] at H1
  have H4 : (n + r).choose (n + r - n) = (n + r).choose n := Nat.choose_symm (by omega)
  have H5 : n + r - n = r := by omega
  rw [H5] at H4
  rw [H4] at H1
  rw [mul_comm]
  exact H1.symm

lemma choose_even (r : ℕ) (h : r > 0) : 2 ∣ (2 * r).choose r := by
  have H1 := Nat.add_one_mul_choose_eq (2 * r - 1) (r - 1)
  have H2 : 2 * r - 1 + 1 = 2 * r := by omega
  have H3 : r - 1 + 1 = r := by omega
  rw [H2, H3] at H1
  have H4 : 2 * (2 * r - 1).choose (r - 1) * r = (2 * r).choose r * r := by
    calc 2 * (2 * r - 1).choose (r - 1) * r = 2 * r * (2 * r - 1).choose (r - 1) := by ring
      _ = (2 * r).choose r * r := H1
  have H5 : 2 * (2 * r - 1).choose (r - 1) = (2 * r).choose r := by
    apply Nat.eq_of_mul_eq_mul_right h H4
  rw [H5.symm]
  exact dvd_mul_right 2 _

lemma binom_n_r_odd_implies_r_zero (n r : ℕ) (hr : r ≤ n) :
  (n.choose r : ZMod 2) * ((n + r).choose n : ZMod 2) ≠ 0 → r = 0 := by
  intro h
  by_cases h_r : r = 0
  · exact h_r
  · have h_pos : r > 0 := by omega
    have H1 := choose_even r h_pos
    have H2 := choose_mul_eq n r hr
    have H3 : 2 ∣ n.choose r * (n + r).choose n := by
      rw [H2]
      exact dvd_mul_of_dvd_right H1 _
    have H4 : ((n.choose r * (n + r).choose n : ℕ) : ZMod 2) = 0 := by
      rw [CharP.cast_eq_zero_iff (ZMod 2) 2]
      exact H3
    push_cast at H4
    contradiction

lemma sum_f_eq_sum_fixed (N : ℕ) : 
  (∑ n ∈ range (N + 1), f N n) = ∑ n ∈ (range (N + 1)).filter (fun n => f N n ≠ 0 ∧ N / (n + 1) = n), f N n := by
  have h_split1 : (∑ n ∈ range (N + 1), f N n) = 
    (∑ n ∈ (range (N + 1)).filter (fun n => f N n ≠ 0), f N n) + 
    ∑ n ∈ (range (N + 1)).filter (fun n => ¬(f N n ≠ 0)), f N n := by
    exact (sum_filter_add_sum_filter_not (range (N + 1)) (fun n => f N n ≠ 0) (fun n => f N n)).symm
  have h_zero : ∑ n ∈ (range (N + 1)).filter (fun n => ¬(f N n ≠ 0)), f N n = 0 := by
    apply sum_eq_zero
    intro n hn
    have h1 := mem_filter.mp hn
    exact Decidable.of_not_not h1.2
  rw [h_zero, add_zero] at h_split1
  have h_split2 : (∑ n ∈ (range (N + 1)).filter (fun n => f N n ≠ 0), f N n) =
    (∑ n ∈ ((range (N + 1)).filter (fun n => f N n ≠ 0)).filter (fun n => N / (n + 1) = n), f N n) +
    ∑ n ∈ ((range (N + 1)).filter (fun n => f N n ≠ 0)).filter (fun n => N / (n + 1) ≠ n), f N n := by
    exact (sum_filter_add_sum_filter_not ((range (N + 1)).filter (fun n => f N n ≠ 0)) (fun n => N / (n + 1) = n) (fun n => f N n)).symm
  
  have h_inv : ∑ n ∈ ((range (N + 1)).filter (fun n => f N n ≠ 0)).filter (fun n => ¬ (N / (n + 1) = n)), f N n = 0 := by
    apply sum_involution (g := fun n _ => g N n)
    · intro n hn
      have H : f N n + f N (g N n) = f N n + f N n := by rw [f_g N n]
      rw [H]
      exact CharTwo.add_self_eq_zero (f N n)
    · intro n hn _
      have h1 := mem_filter.mp hn
      have h2 := mem_filter.mp h1.1
      have h_neq := h1.2
      dsimp [g]
      rw [if_pos h2.2]
      exact h_neq
    · intro n hn
      have h1 := mem_filter.mp hn
      have h2 := mem_filter.mp h1.1
      have h_neq := h1.2
      have H_g_val : g N n = N / (n + 1) := by
        dsimp [g]
        rw [if_pos h2.2]
      rw [H_g_val]
      rw [mem_filter]
      refine ⟨?_, ?_⟩
      · rw [mem_filter]
        refine ⟨?_, ?_⟩
        · rw [mem_range]
          let q := N / (n + 1)
          let r := N % (n + 1)
          have h_div : (n + 1) * q + r = N := Nat.div_add_mod N (n + 1)
          have H_q_lt : q < N + 1 := by
            have := Nat.div_le_self N (n + 1)
            omega
          exact H_q_lt
        · have eq : f N (N / (n + 1)) = f N n := by
            have eq_g := f_g N n
            rw [H_g_val] at eq_g
            exact eq_g
          rw [eq]
          exact h2.2
      · have : N / (N / (n + 1) + 1) = n := by
          have H_sr : N / (n + 1) + N % (n + 1) ≥ n := f_val_eq N n h2.2
          have H_div_mod := div_mod_eq N n (N / (n + 1)) (N % (n + 1)) rfl rfl H_sr
          exact H_div_mod.1
        rw [this]
        intro h
        exact h_neq h.symm
    · intro n hn
      have h1 := mem_filter.mp hn
      have h2 := mem_filter.mp h1.1
      have H_g_g_val : g N (g N n) = n := by
        exact g_involution N n
      exact H_g_g_val
  
  have H_eq_filter : ((range (N + 1)).filter (fun n => f N n ≠ 0)).filter (fun n => N / (n + 1) ≠ n) =
    ((range (N + 1)).filter (fun n => f N n ≠ 0)).filter (fun n => ¬ (N / (n + 1) = n)) := by rfl
  rw [H_eq_filter] at h_split2
  rw [h_inv, add_zero] at h_split2
  rw [h_split1, h_split2]
  have eq_filters : ((range (N + 1)).filter (fun n => f N n ≠ 0)).filter (fun n => N / (n + 1) = n) =
    (range (N + 1)).filter (fun n => f N n ≠ 0 ∧ N / (n + 1) = n) := by
    ext a
    rw [mem_filter, mem_filter, mem_filter]
    tauto
  rw [eq_filters]

lemma sum_fixed_implies (N n : ℕ) (h1 : f N n ≠ 0) (h2 : N / (n + 1) = n) : N = n * (n + 1) := by
  have H_f : f N n = 
    if N / (n + 1) + N % (n + 1) ≥ n then
      (n.choose (n - N % (n + 1)) : ZMod 2) * ((N / (n + 1) + N % (n + 1)).choose n : ZMod 2)
    else 0 := rfl
  have H_sr : N / (n + 1) + N % (n + 1) ≥ n := f_val_eq N n h1
  rw [if_pos H_sr] at H_f
  have H_sub : n.choose (n - N % (n + 1)) = n.choose (N % (n + 1)) := by
    apply Nat.choose_symm
    have : N % (n + 1) < n + 1 := Nat.mod_lt N (by omega)
    omega
  have H_f2 : f N n = (n.choose (N % (n + 1)) : ZMod 2) * ((n + N % (n + 1)).choose n : ZMod 2) := by
    rw [H_sub, h2] at H_f
    exact H_f
  have H_neq : (n.choose (N % (n + 1)) : ZMod 2) * ((n + N % (n + 1)).choose n : ZMod 2) ≠ 0 := by
    rw [← H_f2]
    exact h1
  have H_r_le : N % (n + 1) ≤ n := by
    have : N % (n + 1) < n + 1 := Nat.mod_lt N (by omega)
    omega
  have H_r_zero : N % (n + 1) = 0 := binom_n_r_odd_implies_r_zero n (N % (n + 1)) H_r_le H_neq
  have H_N : (n + 1) * (N / (n + 1)) + N % (n + 1) = N := Nat.div_add_mod N (n + 1)
  rw [h2, H_r_zero] at H_N
  rw [add_zero, mul_comm] at H_N
  exact H_N.symm

lemma a_eq_sum_inner (N : ℕ) : a N = (range (N + 1)).sum (fun n => a_inner N n) := by
  rfl

lemma fast_inner_zmod (N n : ℕ) : (fast_inner N n : ZMod 2) = f N n := by
  dsimp [fast_inner, f]
  by_cases h : N / (n + 1) + N % (n + 1) ≥ n
  · rw [if_pos h, if_pos h]
    push_cast
    rfl
  · rw [if_neg h, if_neg h]
    push_cast
    rfl

lemma a_zmod_eq (N : ℕ) : (a N : ZMod 2) = ∑ n ∈ range (N + 1), f N n := by
  rw [a_eq_sum_inner]
  push_cast
  apply sum_congr rfl
  intro n hn
  rw [a_inner_eq_fast_inner]
  exact fast_inner_zmod N n

lemma filter_nonempty_of_sum_eq_one {s : Finset ℕ} {f : ℕ → ZMod 2} (h : ∑ n ∈ s, f n = 1) :
  ∃ n ∈ s, f n ≠ 0 := by
  by_contra hc
  push_neg at hc
  have : ∑ n ∈ s, f n = 0 := by
    apply sum_eq_zero
    intro n hn
    exact hc n hn
  rw [this] at h
  revert h
  decide

theorem a325046_odd_terms_at_k_times_k_plus_1 (N : ℕ) :
  a N % 2 = 1 → ∃ k : ℕ, N = k * (k + 1) := by
  intro h_odd
  have h_zmod : (a N : ZMod 2) = 1 := by
    have : ((a N % 2 : ℕ) : ZMod 2) = (1 : ZMod 2) := by
      rw [h_odd]
      rfl
    have H : ↑(a N % 2) = (↑(a N) : ZMod 2) := ZMod.natCast_mod (a N) 2
    rw [← H]
    exact this
  rw [a_zmod_eq N, sum_f_eq_sum_fixed N] at h_zmod
  have h_exists := filter_nonempty_of_sum_eq_one h_zmod
  rcases h_exists with ⟨n, hn, _⟩
  have h_mem := mem_filter.mp hn
  have h_f_neq_zero : f N n ≠ 0 := h_mem.2.1
  have h_div_eq : N / (n + 1) = n := h_mem.2.2
  have h_fixed := sum_fixed_implies N n h_f_neq_zero h_div_eq
  use n

theorem a325046_odd_terms_at_k_times_k_plus_1.disproof : ¬ (type_of% @a325046_odd_terms_at_k_times_k_plus_1) := sorry
