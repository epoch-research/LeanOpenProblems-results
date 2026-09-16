import Mathlib
import Submission.Spec

open Nat Finset Classical

lemma central_binom_even (A : ℕ) (hA : 0 < A) : Even ((2 * A).choose A) := by
  have H1 : 2 * A = 2 * A - 1 + 1 := by omega
  have H2 : A = A - 1 + 1 := by omega
  nth_rw 1 [H1]
  nth_rw 2 [H2]
  rw [choose_succ_succ]
  have H3 : (2 * A - 1).choose (A - 1).succ = (2 * A - 1).choose (A - 1) := by
    have hA' : (A - 1).succ = A := by omega
    rw [hA']
    have H3' := choose_symm (n := 2 * A - 1) (k := A) (by omega)
    have hr : 2 * A - 1 - A = A - 1 := by omega
    rw [hr] at H3'
    exact H3'.symm
  rw [H3]
  use (2 * A - 1).choose (A - 1)

lemma term_eq (n k j : ℕ) (hk : k ≤ n) :
  n.choose k * (n + j).choose j = (j + k).choose k * (n + j).choose (n - k) := by
  have h1 : (n + j).choose j = (n + j).choose n := by
    have h1' := choose_symm (n := n + j) (k := n) (by omega)
    have hr : n + j - n = j := by omega
    rw [hr] at h1'
    exact h1'
  have h2 : (n + j).choose (n - k) = (n + j).choose (j + k) := by
    have h2' := choose_symm (n := n + j) (k := j + k) (by omega)
    have hr : n + j - (j + k) = n - k := by omega
    rw [hr] at h2'
    exact h2'
  rw [mul_comm (n.choose k), h1]
  rw [mul_comm ((j + k).choose k), h2]
  have L := choose_mul (n := n + j) (k := n) (s := k) (by omega)
  have R := choose_mul (n := n + j) (k := j + k) (s := k) (by omega)
  rw [L, R]
  have h3 : (n + j - k).choose (n - k) = (n + j - k).choose j := by
    have h3' := choose_symm (n := n + j - k) (k := j) (by omega)
    have hr : n + j - k - j = n - k := by omega
    rw [hr] at h3'
    exact h3'
  rw [h3]
  congr 2
  omega

lemma term_eq2 (k A : ℕ) :
  (k + A).choose k * (k + 2 * A).choose A = (2 * A).choose A * (k + 2 * A).choose (2 * A) := by
  have h1 := choose_mul (n := k + 2 * A) (k := 2 * A) (s := A) (by omega)
  have h2 : (k + 2 * A - A).choose (2 * A - A) = (k + A).choose A := by
    congr 2
    · omega
    · omega
  have h3 : (k + A).choose A = (k + A).choose k := by
    have h3' := choose_symm (n := k + A) (k := k) (by omega)
    have hr : k + A - k = A := by omega
    rw [hr] at h3'
    exact h3'
  rw [h2, h3] at h1
  rw [mul_comm ((k + A).choose k)]
  rw [mul_comm ((2 * A).choose A)]
  exact h1.symm

lemma term2_eq_zero_of_lt (n k : ℕ) (hk : k < n) :
  ((n.choose k : ZMod 2) * ((2 * n - k).choose (n - k) : ZMod 2)) = 0 := by
  set A := n - k
  have hA : 0 < A := by omega
  have h_term : n.choose k * (2 * n - k).choose (n - k) = (2 * A).choose A * (k + 2 * A).choose (2 * A) := by
    have h1 : n = k + A := by omega
    have h2 : 2 * n - k = k + 2 * A := by omega
    have h3 : n - k = A := by omega
    nth_rw 1 [h1, h2, h3]
    exact term_eq2 k A
  have h_even := central_binom_even A hA
  rcases h_even with ⟨r, hr⟩
  have h_term_zmod : ((n.choose k * (2 * n - k).choose (n - k) : ℕ) : ZMod 2) = 0 := by
    rw [h_term]
    push_cast
    have : ((2 * A).choose A : ZMod 2) = 0 := by
      rw [hr]
      push_cast
      exact CharTwo.add_self_eq_zero _
    rw [this, zero_mul]
  push_cast at h_term_zmod
  exact h_term_zmod

lemma zmod2_sum_involution {ι : Type*} (s : Finset ι) (f : ι → ZMod 2)
  (g : ι → ι)
  (hg_mem : ∀ a ∈ s, g a ∈ s)
  (hg_eq : ∀ a ∈ s, f a = f (g a))
  (hg_inv : ∀ a ∈ s, g (g a) = a) :
  ∑ x ∈ s, f x = ∑ x ∈ s.filter (fun a => g a = a), f x := by
  calc
    ∑ x ∈ s, f x = ∑ x ∈ s.filter (fun a => g a = a) ∪ s.filter (fun a => g a ≠ a), f x := by
      congr 1
      ext x
      simp
      tauto
    _ = ∑ x ∈ s.filter (fun a => g a = a), f x + ∑ x ∈ s.filter (fun a => g a ≠ a), f x := by
      apply sum_union
      rw [disjoint_filter]
      intro x _ h2 h3
      exact h3 h2
    _ = ∑ x ∈ s.filter (fun a => g a = a), f x + 0 := by
      congr 1
      apply sum_involution (g := fun a _ => g a)
      · intro a ha
        rw [mem_filter] at ha
        have : f a = f (g a) := hg_eq a ha.1
        rw [this]
        exact CharTwo.add_self_eq_zero _
      · intro a ha _
        rw [mem_filter] at ha
        exact ha.2
      · intro a ha
        rw [mem_filter] at ha ⊢
        exact ⟨hg_mem a ha.1, by rw [hg_inv a ha.1]; exact ha.2.symm⟩
      · intro a ha
        rw [mem_filter] at ha
        exact hg_inv a ha.1
    _ = _ := add_zero _

lemma a_mod2_eq_interm (m : ℕ) :
  (a m : ZMod 2) = ∑ n ∈ range (m + 1), ∑ k ∈ range (n + 1),
    if n * (k + 1) ≤ m ∧ (n + 1) ∣ (m - n * (k + 1)) then
      (n.choose k : ZMod 2) * ((n + (m - n * (k + 1)) / (n + 1)).choose ((m - n * (k + 1)) / (n + 1)) : ZMod 2)
    else 0 := by
  dsimp [a]
  push_cast
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro k _
  by_cases h : n * (k + 1) ≤ m ∧ (n + 1) ∣ (m - n * (k + 1))
  · rw [if_pos h, if_pos h.1, if_pos h.2]
    by_cases h_even : Even ((m - n * (k + 1)) / (n + 1))
    · rw [if_pos h_even]
      ring
    · rw [if_neg h_even]
      have : (-1 : ZMod 2) = 1 := rfl
      rw [this, one_mul]
  · rw [if_neg h]
    by_cases h1 : n * (k + 1) ≤ m
    · rw [if_pos h1]
      have h2 : ¬ (n + 1) ∣ (m - n * (k + 1)) := by tauto
      rw [if_neg h2]
    · rw [if_neg h1]

def isValid (m n k : ℕ) : Prop :=
  n * (k + 1) ≤ m ∧ (n + 1) ∣ (m - n * (k + 1)) ∧ k ≤ n

def j_val (m n k : ℕ) : ℕ := (m - n * (k + 1)) / (n + 1)

noncomputable def term2 (m : ℕ) (p : ℕ × ℕ) : ZMod 2 :=
  (p.1.choose p.2 : ZMod 2) * ((p.1 + j_val m p.1 p.2).choose (j_val m p.1 p.2) : ZMod 2)

lemma m_eq_of_isValid (m n k : ℕ) (h : isValid m n k) :
  m = n * (k + 1) + j_val m n k * (n + 1) := by
  dsimp [isValid, j_val] at h ⊢
  rcases h with ⟨h1, ⟨c, hc⟩, h3⟩
  rw [hc]
  rw [Nat.mul_div_cancel_left _ (by omega)]
  rw [mul_comm c (n+1), ← hc]
  exact Nat.add_sub_of_le h1 |>.symm

noncomputable def g_val (m : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let n := p.1
  let k := p.2
  let j := j_val m n k
  (j + k, k)

noncomputable def S (m : ℕ) : Finset (ℕ × ℕ) :=
  ((range (m + 1)) ×ˢ (range (m + 1))).filter (fun p => isValid m p.1 p.2)

lemma a_mod2_eq (m : ℕ) :
  (a m : ZMod 2) = ∑ x ∈ S m, term2 m x := by
  rw [a_mod2_eq_interm]
  have h_rhs : ∑ x ∈ S m, term2 m x = ∑ n ∈ range (m + 1), ∑ k ∈ range (m + 1), if isValid m n k then term2 m (n, k) else 0 := by
    dsimp [S]
    rw [sum_filter]
    have := sum_product (s := range (m + 1)) (t := range (m + 1)) (f := fun p : ℕ × ℕ => if isValid m p.1 p.2 then term2 m p else 0)
    exact this
  rw [show (∑ x ∈ S m, term2 m x) = ∑ p ∈ S m, term2 m p from rfl, h_rhs]
  apply sum_congr rfl
  intro n hn
  rw [mem_range] at hn
  have H_sum : ∑ k ∈ range (m + 1), (if isValid m n k then term2 m (n, k) else 0) = ∑ k ∈ range (n + 1), (if isValid m n k then term2 m (n, k) else 0) + ∑ k ∈ Ico (n + 1) (m + 1), (if isValid m n k then term2 m (n, k) else 0) := by
    exact (sum_range_add_sum_Ico _ (by omega)).symm
  rw [H_sum]
  have H_zero : ∑ k ∈ Ico (n + 1) (m + 1), (if isValid m n k then term2 m (n, k) else 0) = 0 := by
    apply sum_eq_zero
    intro k hk
    rw [mem_Ico] at hk
    have h_not : ¬ isValid m n k := by
      intro h_v
      have : k ≤ n := h_v.2.2
      omega
    rw [if_neg h_not]
  rw [H_zero, add_zero]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  dsimp [isValid, term2]
  by_cases h : n * (k + 1) ≤ m ∧ n + 1 ∣ m - n * (k + 1)
  · rw [if_pos h]
    have h_valid : n * (k + 1) ≤ m ∧ n + 1 ∣ m - n * (k + 1) ∧ k ≤ n := ⟨h.1, h.2, by omega⟩
    rw [if_pos h_valid]
    rfl
  · rw [if_neg h]
    have h_not : ¬ (n * (k + 1) ≤ m ∧ n + 1 ∣ m - n * (k + 1) ∧ k ≤ n) := by tauto
    rw [if_neg h_not]

lemma g_val_isValid (m : ℕ) (p : ℕ × ℕ) (hp : p ∈ S m) :
  g_val m p ∈ S m := by
  dsimp [S] at hp ⊢
  rw [mem_filter] at hp ⊢
  rcases hp with ⟨hp1, hp2⟩
  set n := p.1
  set k := p.2
  set j := j_val m n k
  have h_m : m = n * (k + 1) + j * (n + 1) := m_eq_of_isValid m n k hp2
  have hk : k ≤ n := hp2.2.2
  dsimp [g_val, isValid]
  have H1 : (j + k) * (k + 1) ≤ m := by
    rw [h_m]
    nlinarith
  have H2 : (j + k + 1) ∣ m - (j + k) * (k + 1) := by
    use n - k
    have h_sub : m - (j + k) * (k + 1) = (j + k + 1) * (n - k) := by
      have h1 : ((n - k : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) := by omega
      have h2 : ((j + k + 1 : ℕ) : ℤ) * ((n - k : ℕ) : ℤ) + (((j + k) * (k + 1) : ℕ) : ℤ) = ((n * (k + 1) + j * (n + 1) : ℕ) : ℤ) := by
        push_cast
        rw [h1]
        ring
      have h3 : n * (k + 1) + j * (n + 1) = (j + k + 1) * (n - k) + (j + k) * (k + 1) := by
        exact_mod_cast h2.symm
      rw [h_m, h3, Nat.add_sub_cancel]
    rw [h_sub, mul_comm]
  have H3 : k ≤ j + k := by omega
  refine ⟨?_, H1, H2, H3⟩
  rw [mem_product]
  constructor
  · rw [mem_range]
    nlinarith
  · rw [mem_product] at hp1
    exact hp1.2

lemma term2_eq_g_val (m : ℕ) (p : ℕ × ℕ) (hp : p ∈ S m) :
  term2 m p = term2 m (g_val m p) := by
  dsimp [term2, g_val]
  dsimp [S] at hp
  rw [mem_filter] at hp
  set n := p.1
  set k := p.2
  set j := j_val m n k
  have h_m : m = n * (k + 1) + j * (n + 1) := m_eq_of_isValid m n k hp.2
  have hk : k ≤ n := hp.2.2.2
  have h_j_prime : j_val m (j + k) k = n - k := by
    dsimp [j_val]
    have h_sub : m - (j + k) * (k + 1) = (j + k + 1) * (n - k) := by
      have h1 : ((n - k : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) := by omega
      have h2 : ((j + k + 1 : ℕ) : ℤ) * ((n - k : ℕ) : ℤ) + (((j + k) * (k + 1) : ℕ) : ℤ) = ((n * (k + 1) + j * (n + 1) : ℕ) : ℤ) := by
        push_cast
        rw [h1]
        ring
      have h3 : n * (k + 1) + j * (n + 1) = (j + k + 1) * (n - k) + (j + k) * (k + 1) := by
        exact_mod_cast h2.symm
      rw [h_m, h3, Nat.add_sub_cancel]
    rw [h_sub]
    exact Nat.mul_div_cancel_left _ (by omega)
  rw [h_j_prime]
  have h_n_prime_add_j_prime : j + k + (n - k) = n + j := by omega
  rw [h_n_prime_add_j_prime]
  push_cast
  have h_term := term_eq n k j hk
  have h_term_zmod : ((n.choose k * (n + j).choose j : ℕ) : ZMod 2) = (((j + k).choose k * (n + j).choose (n - k) : ℕ) : ZMod 2) := by
    rw [h_term]
  push_cast at h_term_zmod
  exact h_term_zmod

lemma g_val_involution (m : ℕ) (p : ℕ × ℕ) (hp : p ∈ S m) :
  g_val m (g_val m p) = p := by
  dsimp [g_val]
  dsimp [S] at hp
  rw [mem_filter] at hp
  set n := p.1
  set k := p.2
  set j := j_val m n k
  have h_m : m = n * (k + 1) + j * (n + 1) := m_eq_of_isValid m n k hp.2
  have hk : k ≤ n := hp.2.2.2
  have h_j_prime : j_val m (j + k) k = n - k := by
    dsimp [j_val]
    have h_sub : m - (j + k) * (k + 1) = (j + k + 1) * (n - k) := by
      have h1 : ((n - k : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) := by omega
      have h2 : ((j + k + 1 : ℕ) : ℤ) * ((n - k : ℕ) : ℤ) + (((j + k) * (k + 1) : ℕ) : ℤ) = ((n * (k + 1) + j * (n + 1) : ℕ) : ℤ) := by
        push_cast
        rw [h1]
        ring
      have h3 : n * (k + 1) + j * (n + 1) = (j + k + 1) * (n - k) + (j + k) * (k + 1) := by
        exact_mod_cast h2.symm
      rw [h_m, h3, Nat.add_sub_cancel]
    rw [h_sub]
    exact Nat.mul_div_cancel_left _ (by omega)
  ext
  · dsimp
    rw [h_j_prime]
    omega
  · rfl

lemma a_mod2_final (m : ℕ) :
  (a m : ZMod 2) = ∑ x ∈ (S m).filter (fun a => g_val m a = a), term2 m x := by
  rw [a_mod2_eq]
  have H := zmod2_sum_involution (S m) (term2 m) (g_val m) (g_val_isValid m) (term2_eq_g_val m) (g_val_involution m)
  convert H

lemma odd_iff_zmod2_eq_one (x : ℤ) : Odd x ↔ (x : ZMod 2) = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [hk]
    push_cast
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_mul, zero_add]
  · intro h
    have h_mod : ((x % 2 : ℤ) : ZMod 2) = (x : ZMod 2) := by
      have h1 : x = 2 * (x / 2) + x % 2 := Int.mul_ediv_add_emod x 2 |>.symm
      have h2 : ((x % 2 : ℤ) : ℤ) = x - 2 * (x / 2) := by omega
      have h3 : (((x % 2 : ℤ) : ℤ) : ZMod 2) = ((x - 2 * (x / 2) : ℤ) : ZMod 2) := by rw [h2]
      push_cast at h3
      have h4 : (2 : ZMod 2) = 0 := rfl
      rw [h4, zero_mul, sub_zero] at h3
      exact h3
    have h_mod2 : ((x % 2 : ℤ) : ZMod 2) = 1 := by
      rw [h_mod, h]
    have H : (x % 2 : ℤ) = 1 := by
      have hy : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hy with h1 | h1
      · rw [h1] at h_mod2
        have h_abs : (0 : ZMod 2) ≠ 1 := by decide
        exact False.elim (h_abs h_mod2)
      · exact h1
    use x / 2
    have : x = 2 * (x / 2) + x % 2 := Int.mul_ediv_add_emod x 2 |>.symm
    omega

lemma term2_fixed_point_zero (m : ℕ) (p : ℕ × ℕ) (hp1 : p ∈ S m) (hp2 : g_val m p = p) (hp3 : p.2 < p.1) :
  term2 m p = 0 := by
  dsimp [term2]
  have h_n : p.1 = j_val m p.1 p.2 + p.2 := by
    have : (g_val m p).1 = p.1 := by rw [hp2]
    exact this.symm
  have h_j : j_val m p.1 p.2 = p.1 - p.2 := by omega
  rw [h_j]
  have h_eq : p.1 + (p.1 - p.2) = 2 * p.1 - p.2 := by omega
  rw [h_eq]
  exact term2_eq_zero_of_lt p.1 p.2 hp3

