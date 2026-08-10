import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A357960: $a(n) = A005259(n-1)^5 \cdot A005258(n)^6$.
The sequence is defined by the combinatorial formula:
$$a(n) = \left( \sum_{k = 0}^{n-1} \binom{n-1}{k}^2 \binom{n+k-1}{k}^2 \right)^5 \cdot \left( \sum_{k = 0}^{n} \binom{n}{k}^2 \binom{n+k}{k} \right)^6$$
-/
def a (n : ℕ) : ℕ :=
  let N := n - 1
  ( (range n).sum fun k => (N.choose k) ^ 2 * ((N + k).choose k) ^ 2 ) ^ 5 *
  ( (range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k) ) ^ 6

lemma prime_cases (p : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) : p = 3 ∨ 5 ≤ p := by
  rcases hp_ge_3.eq_or_lt with rfl | hp_gt_3
  · left; rfl
  · right
    have h4 : 4 ≤ p := hp_gt_3
    rcases h4.eq_or_lt with rfl | hp_gt_4
    · exfalso
      have hnot : ¬ (4).Prime := by decide
      exact hnot hp
    · exact hp_gt_4

lemma dvd_choose_helper (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k < p) :
    p ∣ (p - 1 + k).choose k := by
  have h1 : k < p := hk2
  have h2 : p - 1 + k - k < p := by
    rw [Nat.add_sub_cancel]
    exact Nat.sub_lt hp.pos Nat.one_pos
  have h3 : p ≤ p - 1 + k := by
    omega
  exact hp.dvd_choose h1 h2 h3

lemma sq_dvd_sq_helper (p x : ℕ) (h : p ∣ x) : p ^ 2 ∣ x ^ 2 := by
  have h2 : p * p ∣ x * x := mul_dvd_mul h h
  rw [← sq, ← sq] at h2
  exact h2


lemma sq_div_sq_eq (p x : ℕ) (hp : p.Prime) (h : p ∣ x) : x ^ 2 / p ^ 2 = (x / p) ^ 2 := by
  have hp_pos : 0 < p := hp.pos
  have hp2_pos : 0 < p ^ 2 := Nat.pow_pos hp_pos
  rcases h with ⟨y, rfl⟩
  have h1 : p * y / p = y := Nat.mul_div_cancel_left y hp_pos
  have h2 : (p * y) ^ 2 = p ^ 2 * y ^ 2 := by ring
  rw [h2]
  rw [Nat.mul_div_cancel_left (y ^ 2) hp2_pos]
  rw [h1]

lemma term_dvd_helper (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k < p) :
    p ^ 2 ∣ ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2 := by
  have h_dvd : p ∣ (p - 1 + k).choose k := dvd_choose_helper p k hp hk1 hk2
  have h_sq : p ^ 2 ∣ ((p - 1 + k).choose k) ^ 2 := sq_dvd_sq_helper p _ h_dvd
  exact dvd_mul_of_dvd_right h_sq _


lemma sum_range_succ_split (n : ℕ) (f : ℕ → ℕ) :
    (range (n + 1)).sum f = f 0 + (range n).sum (fun k => f (k + 1)) := by
  rw [sum_range_succ', add_comm]


lemma S1_sub_one_eq_sum (p : ℕ) (hp : 1 ≤ p) :
    (range p).sum (fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2) - 1 =
    (range (p - 1)).sum (fun k => ((p - 1).choose (k + 1)) ^ 2 * ((p - 1 + k + 1).choose (k + 1)) ^ 2) := by
  let f := fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2
  have h_p : p = (p - 1) + 1 := by omega
  have h_split := sum_range_succ_split (p - 1) f
  rw [← h_p] at h_split
  have h_f0 : f 0 = 1 := by
    change ((p - 1).choose 0) ^ 2 * ((p - 1 + 0).choose 0) ^ 2 = 1
    simp
  rw [h_f0] at h_split
  change (range p).sum f - 1 = (range (p - 1)).sum (fun k => f (k + 1))
  rw [h_split]
  simp

lemma S1_ge_one (p : ℕ) (hp : 1 ≤ p) :
    1 ≤ (range p).sum (fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2) := by
  have h0 : 0 ∈ range p := mem_range.2 hp
  have h_le : ((p - 1).choose 0) ^ 2 * ((p - 1 + 0).choose 0) ^ 2 ≤ (range p).sum (fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2) :=
    single_le_sum (f := fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2) (fun _ _ => Nat.zero_le _) h0
  have h_term0 : ((p - 1).choose 0) ^ 2 * ((p - 1 + 0).choose 0) ^ 2 = 1 := by
    simp
  rw [h_term0] at h_le
  exact h_le


lemma dvd_sum_range (p : ℕ) (n : ℕ) (f : ℕ → ℕ) (h : ∀ k < n, p ^ 2 ∣ f (k + 1)) :
    p ^ 2 ∣ (range n).sum (fun k => f (k + 1)) := by
  apply dvd_sum
  intro k hk
  rw [mem_range] at hk
  exact h k hk

lemma sum_term_dvd_helper (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    let N := p - 1
    p ^ 2 ∣ (range N).sum (fun k => (N.choose (k + 1)) ^ 2 * ((N + k + 1).choose (k + 1)) ^ 2) := by
  let N := p - 1
  let f := fun k => (N.choose k) ^ 2 * ((N + k).choose k) ^ 2
  have h_dvd : ∀ k < N, p ^ 2 ∣ f (k + 1) := by
    intro k hk
    have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hk2 : k + 1 < p := by
      have hN : N = p - 1 := rfl
      omega
    exact term_dvd_helper p (k + 1) hp hk1 hk2
  exact dvd_sum_range p N f h_dvd

lemma modeq_helper (a b m x : ℕ) (h1 : a = b + x) (h2 : m ∣ x) : a ≡ b [MOD m] := by
  rw [h1]
  exact Nat.add_modEq_left_iff.2 h2


lemma Apery_mod_p_sq (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    let N := p - 1
    (range p).sum (fun k => (N.choose k) ^ 2 * ((N + k).choose k) ^ 2) ≡ 1 [MOD p ^ 2] := by
  let N := p - 1
  let f := fun k => (N.choose k) ^ 2 * ((N + k).choose k) ^ 2
  have h_split : (range (N + 1)).sum f = f 0 + (range N).sum (fun k => f (k + 1)) := sum_range_succ_split N f
  have h_p : p = N + 1 := by
    have : N = p - 1 := rfl
    omega
  have h_S : (range p).sum f = (range (N + 1)).sum f := by rw [← h_p]
  have h_f0 : f 0 = 1 := by
    change (N.choose 0) ^ 2 * ((N + 0).choose 0) ^ 2 = 1
    simp
  have h_sum : (range p).sum f = 1 + (range N).sum (fun k => f (k + 1)) := by
    rw [h_S, h_split, h_f0]
  exact modeq_helper ((range p).sum f) 1 (p ^ 2) _ h_sum (sum_term_dvd_helper p hp hp3)


lemma sum_range_succ_split_both (n : ℕ) (hn : 1 ≤ n) (f : ℕ → ℕ) :
    (range (n + 1)).sum f = f 0 + (range (n - 1)).sum (fun k => f (k + 1)) + f n := by
  have h_split : (range (n + 1)).sum f = (range n).sum f + f n := sum_range_succ f n
  have h_split2 : (range n).sum f = f 0 + (range (n - 1)).sum (fun k => f (k + 1)) := by
    have hn1 : n = (n - 1) + 1 := by omega
    nth_rw 1 [hn1]
    rw [sum_range_succ_split]
  rw [h_split, h_split2]


lemma s_term_dvd_helper (p k : ℕ) (hp : p.Prime) (hk2 : k + 1 < p) :
    p ^ 2 ∣ (p.choose (k + 1)) ^ 2 * ((p + k + 1).choose (k + 1)) := by
  have hk_ne_zero : k + 1 ≠ 0 := Nat.succ_ne_zero k
  have hdvd : p ∣ p.choose (k + 1) := hp.dvd_choose_self hk_ne_zero hk2
  have h_sq : p ^ 2 ∣ (p.choose (k + 1)) ^ 2 := sq_dvd_sq_helper p _ hdvd
  exact dvd_mul_of_dvd_left h_sq _


lemma s_sum_term_dvd_helper (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    let N := p - 1
    p ^ 2 ∣ (range N).sum (fun k => (p.choose (k + 1)) ^ 2 * ((p + k + 1).choose (k + 1))) := by
  let N := p - 1
  let f := fun k => (p.choose k) ^ 2 * ((p + k).choose k)
  have h_dvd : ∀ k < N, p ^ 2 ∣ f (k + 1) := by
    intro k hk
    have hk2 : k + 1 < p := by
      have hN : N = p - 1 := rfl
      omega
    exact s_term_dvd_helper p k hp hk2
  exact dvd_sum_range p N f h_dvd


lemma s_mod_split_helper (p : ℕ) (_hp : p.Prime) (hp3 : 3 ≤ p) :
    (range (p + 1)).sum (fun k => (p.choose k) ^ 2 * ((p + k).choose k)) =
    1 + (2 * p).choose p + (range (p - 1)).sum (fun k => (p.choose (k + 1)) ^ 2 * ((p + k + 1).choose (k + 1))) := by
  let f := fun k => (p.choose k) ^ 2 * ((p + k).choose k)
  have hn : 1 ≤ p := by omega
  have h_split := sum_range_succ_split_both p hn f
  have h_f0 : f 0 = 1 := by
    change (p.choose 0) ^ 2 * ((p + 0).choose 0) = 1
    simp
  have h_fp : f p = (2 * p).choose p := by
    change (p.choose p) ^ 2 * ((p + p).choose p) = (2 * p).choose p
    have : p.choose p = 1 := choose_self p
    have hpp : p + p = 2 * p := by omega
    rw [hpp, this]
    simp
  change (range (p + 1)).sum f = 1 + (2 * p).choose p + (range (p - 1)).sum (fun k => f (k + 1))
  rw [h_split, h_f0, h_fp]
  omega

lemma s_mod_p_sq_helper (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (range (p + 1)).sum (fun k => (p.choose k) ^ 2 * ((p + k).choose k)) ≡
    1 + (2 * p).choose p [MOD p ^ 2] := by
  have h_sum := s_mod_split_helper p hp hp3
  exact modeq_helper _ (1 + (2 * p).choose p) (p ^ 2) _ h_sum (s_sum_term_dvd_helper p hp hp3)


lemma choose_relation_helper (p : ℕ) (hp : p.Prime) :
    (2 * p).choose p = 2 * (2 * p - 1).choose (p - 1) := by
  have h_prime_pos : 0 < p := hp.pos
  have h_eq : (2 * p - 1 + 1) * (2 * p - 1).choose (p - 1) = (2 * p - 1 + 1).choose (p - 1 + 1) * (p - 1 + 1) :=
    add_one_mul_choose_eq (2 * p - 1) (p - 1)
  have h_p2 : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  have h_2p : 2 * p - 1 + 1 = 2 * p := Nat.sub_add_cancel (by omega)
  rw [h_p2, h_2p] at h_eq
  have h_eq2 : p * (2 * (2 * p - 1).choose (p - 1)) = p * (2 * p).choose p := by
    calc
      p * (2 * (2 * p - 1).choose (p - 1)) = (2 * p) * (2 * p - 1).choose (p - 1) := by ring
      _ = (2 * p).choose p * p := h_eq
      _ = p * (2 * p).choose p := by ring
  exact Nat.eq_of_mul_eq_mul_left hp.pos h_eq2.symm

lemma choose_p_ge_two (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    2 ≤ (2 * p).choose p := by
  rw [choose_relation_helper p hp]
  have h_ge : 1 ≤ (2 * p - 1).choose (p - 1) := by
    apply Nat.choose_pos
    omega
  omega


lemma S2_ge_three (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    3 ≤ (range (p + 1)).sum (fun k => (p.choose k) ^ 2 * ((p + k).choose k)) := by
  have h_split := s_mod_split_helper p hp hp3
  rw [h_split]
  have h_ge : 2 ≤ (2 * p).choose p := choose_p_ge_two p hp hp3
  omega

lemma sq_sub_self_modeq (p y : ℕ) (hy : y ≤ p) :
    (p - y) ^ 2 ≡ y ^ 2 [MOD p] := by
  have h_eq : (p - y) ^ 2 + 2 * p * y = p ^ 2 + y ^ 2 := by
    have h_p : p = (p - y) + y := (Nat.sub_add_cancel hy).symm
    nth_rw 2 [h_p]
    nth_rw 3 [h_p]
    ring
  have h_mod : (p - y) ^ 2 ≡ (p - y) ^ 2 + 2 * p * y [MOD p] := by
    have h_div : p ∣ 2 * p * y := by
      use 2 * y
      ring
    exact ((@Nat.add_modEq_left_iff p ((p - y) ^ 2) (2 * p * y)).2 h_div).symm
  have h_mod2 : p ^ 2 + y ^ 2 ≡ y ^ 2 [MOD p] := by
    have h_div : p ∣ p ^ 2 := by
      use p
      ring
    have h_add := (@Nat.add_modEq_left_iff p (y ^ 2) (p ^ 2)).2 h_div
    rw [add_comm (p ^ 2) (y ^ 2)]
    exact h_add
  have h_eq_modEq : (p - y) ^ 2 + 2 * p * y ≡ p ^ 2 + y ^ 2 [MOD p] := by
    rw [h_eq]
  exact h_mod.trans (h_eq_modEq.trans h_mod2)

lemma descFactorial_sq_modeq (p : ℕ) (_hp : p.Prime) (k : ℕ) (hk : k < p) :
    ((p - 1).descFactorial k) ^ 2 ≡ k.factorial ^ 2 [MOD p] := by
  induction k with
  | zero =>
    simp [Nat.descFactorial, Nat.factorial]
    rfl
  | succ k ih =>
    have hk_succ : k < p := by omega
    have h_ih := ih hk_succ
    rw [Nat.descFactorial_succ, Nat.factorial_succ]
    rw [mul_pow, mul_pow]
    have h_sub : p - 1 - k = p - (k + 1) := by omega
    rw [h_sub]
    have h_sq := sq_sub_self_modeq p (k + 1) (by omega)
    exact Nat.ModEq.mul h_sq h_ih

lemma choose_sq_sub_one_dvd (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k < p) :
    p ∣ ((p - 1).choose k) ^ 2 - 1 := by
  have h_desc := descFactorial_sq_modeq p hp k hk
  have h_eq : (p - 1).descFactorial k = k.factorial * (p - 1).choose k := descFactorial_eq_factorial_mul_choose (p - 1) k
  rw [h_eq] at h_desc
  rw [mul_pow] at h_desc
  have h_le : k.factorial ^ 2 ≤ k.factorial ^ 2 * ((p - 1).choose k) ^ 2 := by
    have h_choose : 1 ≤ (p - 1).choose k := Nat.choose_pos (by omega)
    have h_choose_sq : 1 ≤ ((p - 1).choose k) ^ 2 := by nlinarith [h_choose]
    have h_mul := Nat.mul_le_mul_left (k.factorial ^ 2) h_choose_sq
    rw [mul_one] at h_mul
    exact h_mul
  have h_dvd : p ∣ k.factorial ^ 2 * ((p - 1).choose k) ^ 2 - k.factorial ^ 2 := (Nat.modEq_iff_dvd' h_le).1 h_desc.symm
  have h_factor : k.factorial ^ 2 * ((p - 1).choose k) ^ 2 - k.factorial ^ 2 = k.factorial ^ 2 * (((p - 1).choose k) ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
  rw [h_factor] at h_dvd
  have h_not_dvd : ¬ p ∣ k.factorial ^ 2 := by
    intro h_dvd2
    have h_p_dvd_k : p ∣ k.factorial := hp.dvd_of_dvd_pow h_dvd2
    have h_le_k : p ≤ k := (hp.dvd_factorial).1 h_p_dvd_k
    omega
  exact (hp.dvd_mul.1 h_dvd).resolve_left h_not_dvd

lemma T_k_sub_sq_dvd (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k < p) :
    p ^ 3 ∣ ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2 - p ^ 2 * (((p - 1 + k).choose k) / p) ^ 2 := by
  let N := p - 1
  let A := (N + k).choose k / p
  let T := (N.choose k) ^ 2 * ((N + k).choose k) ^ 2
  have h_dvd : p ∣ (N.choose k) ^ 2 - 1 := choose_sq_sub_one_dvd p hp k hk2
  rcases h_dvd with ⟨D, hD⟩
  have h_choose_sq : (N.choose k) ^ 2 = 1 + p * D := by
    have h_le : 1 ≤ (N.choose k) ^ 2 := by
      have h_pos : 1 ≤ N.choose k := Nat.choose_pos (by omega)
      nlinarith [h_pos]
    omega
  have h_pA : (N + k).choose k = p * A := by
    have h_dvd_Ak : p ∣ (N + k).choose k := dvd_choose_helper p k hp hk1 hk2
    exact (Nat.mul_div_cancel' h_dvd_Ak).symm
  have h_T_eq : T - p ^ 2 * A ^ 2 = p ^ 3 * A ^ 2 * D := by
    change (N.choose k) ^ 2 * ((N + k).choose k) ^ 2 - p ^ 2 * A ^ 2 = p ^ 3 * A ^ 2 * D
    rw [h_pA]
    rw [h_choose_sq]
    have h_ring : (1 + p * D) * (p * A) ^ 2 = p ^ 2 * A ^ 2 + p ^ 3 * A ^ 2 * D := by ring
    rw [h_ring]
    rw [Nat.add_sub_cancel_left]
  change p ^ 3 ∣ T - p ^ 2 * A ^ 2
  rw [h_T_eq]
  have h_dvd3 : p ^ 3 ∣ p ^ 3 * A ^ 2 * D := by
    use A ^ 2 * D
    ring
  exact h_dvd3

lemma sum_sub_helper {α : Type*} (s : Finset α) (f g : α → ℕ) (h_le : ∀ x ∈ s, g x ≤ f x) :
    s.sum (fun x => f x) - s.sum (fun x => g x) = s.sum (fun x => f x - g x) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp only [mem_cons, forall_eq_or_imp] at h_le
    have h_le_a := h_le.1
    have h_le_s := h_le.2
    rw [sum_cons, sum_cons, sum_cons]
    have h_ih := ih h_le_s
    have h_sum_le : s.sum (fun x => g x) ≤ s.sum (fun x => f x) := sum_le_sum h_le_s
    omega

lemma dvd_sum_sub {α : Type*} (s : Finset α) (f g : α → ℕ) (m : ℕ) (h_le : ∀ x ∈ s, g x ≤ f x) (h_dvd : ∀ x ∈ s, m ∣ f x - g x) :
    m ∣ s.sum (fun x => f x) - s.sum (fun x => g x) := by
  rw [sum_sub_helper s f g h_le]
  apply dvd_sum
  intro x hx
  exact h_dvd x hx

lemma T_ge_sq (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k < p) :
    p ^ 2 * (((p - 1 + k).choose k) / p) ^ 2 ≤ ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2 := by
  let N := p - 1
  have h_dvd : p ∣ (N + k).choose k := dvd_choose_helper p k hp hk1 hk2
  have h_choose : 1 ≤ N.choose k := Nat.choose_pos (by omega)
  have h_choose_sq : 1 ≤ (N.choose k) ^ 2 := by nlinarith
  rcases h_dvd with ⟨A, h_pA⟩
  have h_div : (N + k).choose k / p = A := by
    rw [h_pA]
    exact Nat.mul_div_cancel_left A hp.pos
  rw [h_div, h_pA]
  calc
    p ^ 2 * A ^ 2 = (p * A) ^ 2 := by ring
    _ = 1 * (p * A) ^ 2 := by rw [one_mul]
    _ ≤ (N.choose k) ^ 2 * (p * A) ^ 2 := Nat.mul_le_mul_right ((p * A) ^ 2) h_choose_sq


lemma div_sq_sub_sq_dvd (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k < p) :
    p ∣ (((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2) / p ^ 2 - (((p - 1 + k).choose k) / p) ^ 2 := by
  let T := ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2
  let A := ((p - 1 + k).choose k) / p
  have h_dvd : p ^ 3 ∣ T - p ^ 2 * A ^ 2 := T_k_sub_sq_dvd p k hp hk1 hk2
  have h_le : p ^ 2 * A ^ 2 ≤ T := T_ge_sq p k hp hk1 hk2
  rcases h_dvd with ⟨K, hK⟩
  have h_eq : T = p ^ 2 * A ^ 2 + p ^ 3 * K := by omega
  have h_eq2 : T = p ^ 2 * (A ^ 2 + p * K) := by
    calc
      T = p ^ 2 * A ^ 2 + p ^ 3 * K := h_eq
      _ = p ^ 2 * A ^ 2 + p ^ 2 * (p * K) := by ring
      _ = p ^ 2 * (A ^ 2 + p * K) := by ring
  have h_div : T / p ^ 2 = A ^ 2 + p * K := by
    rw [h_eq2]
    exact Nat.mul_div_cancel_left _ (Nat.pow_pos hp.pos)
  have h_sub : T / p ^ 2 - A ^ 2 = p * K := by omega
  rw [h_sub]
  exact dvd_mul_right p K













lemma sum_div_helper (p : ℕ) (n : ℕ) (f : ℕ → ℕ) (h : ∀ k < n, p ∣ f k) :
    (range n).sum f = p * (range n).sum (fun k => f k / p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    have h_dvd : p ∣ f n := h n (Nat.lt_succ_self n)
    have h_ih : (range n).sum f = p * (range n).sum (fun k => f k / p) := by
      apply ih
      intro k hk
      exact h k (Nat.lt_succ_of_lt hk)
    have h_cancel : f n = p * (f n / p) := (Nat.mul_div_cancel' h_dvd).symm
    rw [h_ih]
    nth_rw 1 [h_cancel]
    ring

lemma algebra_step_nat (p u v w S1 S2 : ℕ)
    (h1 : S1 = 1 + p ^ 3 * u)
    (h2 : S2 = 3 + p ^ 3 * v)
    (h_eq : 5 * u + 2 * v = p ^ 2 * w) :
    S1 ^ 5 * S2 ^ 6 ≡ 729 [MOD p ^ 5] := by
  have hX : (1 + p ^ 3 * u) ^ 5 = 1 + 5 * (p ^ 3 * u) + (p ^ 3 * u) ^ 2 * (10 + 10 * (p ^ 3 * u) + 5 * (p ^ 3 * u) ^ 2 + (p ^ 3 * u) ^ 3) := by ring
  have hY : (3 + p ^ 3 * v) ^ 6 = 729 + 1458 * (p ^ 3 * v) + (p ^ 3 * v) ^ 2 * (1215 + 540 * (p ^ 3 * v) + 135 * (p ^ 3 * v) ^ 2 + 18 * (p ^ 3 * v) ^ 3 + (p ^ 3 * v) ^ 4) := by ring
  let B_quot := p * u ^ 2 * (10 + 10 * (p ^ 3 * u) + 5 * (p ^ 3 * u) ^ 2 + (p ^ 3 * u) ^ 3)
  let D_quot := p * v ^ 2 * (1215 + 540 * (p ^ 3 * v) + 135 * (p ^ 3 * v) ^ 2 + 18 * (p ^ 3 * v) ^ 3 + (p ^ 3 * v) ^ 4)
  have hB : (p ^ 3 * u) ^ 2 * (10 + 10 * (p ^ 3 * u) + 5 * (p ^ 3 * u) ^ 2 + (p ^ 3 * u) ^ 3) = p ^ 5 * B_quot := by
    dsimp [B_quot]
    ring
  have hD : (p ^ 3 * v) ^ 2 * (1215 + 540 * (p ^ 3 * v) + 135 * (p ^ 3 * v) ^ 2 + 18 * (p ^ 3 * v) ^ 3 + (p ^ 3 * v) ^ 4) = p ^ 5 * D_quot := by
    dsimp [D_quot]
    ring
  let A := 1 + 5 * (p ^ 3 * u)
  let C := 729 + 1458 * (p ^ 3 * v)
  have h_prod : (A + p ^ 5 * B_quot) * (C + p ^ 5 * D_quot) = A * C + p ^ 5 * (A * D_quot + B_quot * C + p ^ 5 * B_quot * D_quot) := by ring
  have h_AC : A * C = 729 + p ^ 5 * (729 * w + p * 7290 * u * v) := by
    dsimp [A, C]
    have h_ac_exp : (1 + 5 * (p ^ 3 * u)) * (729 + 1458 * (p ^ 3 * v)) = 729 + (1458 * (p ^ 3 * v) + 5 * (p ^ 3 * u) * 729) + 5 * (p ^ 3 * u) * (1458 * (p ^ 3 * v)) := by ring
    have h_rew : 1458 * (p ^ 3 * v) + 5 * (p ^ 3 * u) * 729 = p ^ 3 * 729 * (5 * u + 2 * v) := by ring
    have h_rew2 : 5 * (p ^ 3 * u) * (1458 * (p ^ 3 * v)) = p ^ 5 * (p * 7290 * u * v) := by ring
    rw [h_ac_exp, h_rew, h_rew2, h_eq]
    ring
  have h_sum : S1 ^ 5 * S2 ^ 6 = 729 + p ^ 5 * ((729 * w + p * 7290 * u * v) + (A * D_quot + B_quot * C + p ^ 5 * B_quot * D_quot)) := by
    rw [h1, h2, hX, hY, hB, hD, h_prod, h_AC]
    ring
  exact modeq_helper _ 729 (p ^ 5) _ h_sum (dvd_mul_of_dvd_left dvd_rfl _)


lemma glue_step (p S1 S2 : ℕ) (_hp : 3 ≤ p) (h_S1_ge : 1 ≤ S1) (h_S2_ge : 3 ≤ S2)
    (h_div1 : p ^ 3 ∣ S1 - 1)
    (h_div2 : p ^ 3 ∣ S2 - 3)
    (h_div3 : p ^ 2 ∣ 5 * ((S1 - 1) / p ^ 3) + 2 * ((S2 - 3) / p ^ 3)) :
    S1 ^ 5 * S2 ^ 6 ≡ 729 [MOD p ^ 5] := by
  let u := (S1 - 1) / p ^ 3
  let v := (S2 - 3) / p ^ 3
  let w := (5 * u + 2 * v) / p ^ 2
  have h1 : S1 = 1 + p ^ 3 * u := by
    have : S1 - 1 = p ^ 3 * u := (Nat.mul_div_cancel' h_div1).symm
    omega
  have h2 : S2 = 3 + p ^ 3 * v := by
    have : S2 - 3 = p ^ 3 * v := (Nat.mul_div_cancel' h_div2).symm
    omega
  have h_eq : 5 * u + 2 * v = p ^ 2 * w := (Nat.mul_div_cancel' h_div3).symm
  exact algebra_step_nat p u v w S1 S2 h1 h2 h_eq


lemma dvd_div_of_dvd_sq (p x : ℕ) (hp : 0 < p) (h : p ^ 2 ∣ x) : p ∣ x / p := by
  rcases h with ⟨y, rfl⟩
  have h_eq : p ^ 2 * y = p * (p * y) := by ring
  rw [h_eq, Nat.mul_div_cancel_left _ hp]
  exact dvd_mul_right p y

lemma sum_div_sq_helper (p : ℕ) (n : ℕ) (f : ℕ → ℕ) (hp : 0 < p) (h : ∀ k < n, p ^ 2 ∣ f k) :
    (range n).sum f / p ^ 2 = (range n).sum (fun k => f k / p ^ 2) := by
  have h_eq : (range n).sum f = p ^ 2 * (range n).sum (fun k => f k / p ^ 2) := by
    rw [mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have h_dvd := h k hk
    exact (Nat.mul_div_cancel' h_dvd).symm
  rw [h_eq]
  apply Nat.mul_div_cancel_left
  exact Nat.pow_pos hp


lemma S1_sub_one_div_p_sq (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ((range p).sum (fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2) - 1) / p ^ 2 =
    (range (p - 1)).sum (fun k => ((p - 1).choose (k + 1)) ^ 2 * ((p - 1 + k + 1).choose (k + 1)) ^ 2 / p ^ 2) := by
  let f := fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2
  have h_S1 : (range p).sum f - 1 = (range (p - 1)).sum (fun k => f (k + 1)) := by
    apply S1_sub_one_eq_sum p (by omega)
  rw [h_S1]
  have h_dvd : ∀ k < p - 1, p ^ 2 ∣ f (k + 1) := by
    intro k hk
    have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hk2 : k + 1 < p := by omega
    exact term_dvd_helper p (k + 1) hp hk1 hk2
  have h_sum := sum_div_sq_helper p (p - 1) (fun k => f (k + 1)) hp.pos h_dvd
  exact h_sum

lemma S1_sub_one_div_p_sq_modeq_sum_sq (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    p ∣ ((range p).sum (fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2) - 1) / p ^ 2 -
    (range (p - 1)).sum (fun k => (((p - 1 + k + 1).choose (k + 1)) / p) ^ 2) := by
  let f_sum := fun k => ((p - 1).choose (k + 1)) ^ 2 * ((p - 1 + k + 1).choose (k + 1)) ^ 2 / p ^ 2
  let g_sum := fun k => (((p - 1 + k + 1).choose (k + 1)) / p) ^ 2
  have h_eq : ((range p).sum (fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2) - 1) / p ^ 2 =
              (range (p - 1)).sum f_sum := by
    apply S1_sub_one_div_p_sq p hp hp3
  rw [h_eq]
  apply dvd_sum_sub (range (p - 1)) f_sum g_sum p
  · intro k hk
    rw [mem_range] at hk
    have h_le : p ^ 2 * g_sum k ≤ ((p - 1).choose (k + 1)) ^ 2 * ((p - 1 + k + 1).choose (k + 1)) ^ 2 := by
      exact T_ge_sq p (k + 1) hp (by omega) (by omega)
    have h_div_le : p ^ 2 * g_sum k / p ^ 2 ≤ ((p - 1).choose (k + 1)) ^ 2 * ((p - 1 + k + 1).choose (k + 1)) ^ 2 / p ^ 2 := Nat.div_le_div_right h_le
    have h_LHS : p ^ 2 * g_sum k / p ^ 2 = g_sum k := by
      exact Nat.mul_div_cancel_left _ (Nat.pow_pos hp.pos)
    rw [h_LHS] at h_div_le
    exact h_div_le
  · intro k hk
    rw [mem_range] at hk
    exact div_sq_sub_sq_dvd p (k + 1) hp (by omega) (by omega)




lemma dvd_choose_step (p k : ℕ) (hp : p.Prime) (hk : k ≤ p - 2) :
    p ∣ (p + k).choose (k + 1) := by
  have hp2 := hp.two_le
  have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hk2 : k + 1 < p := by omega
  have h_eq : p - 1 + (k + 1) = p + k := by omega
  have h_dvd := dvd_choose_helper p (k + 1) hp hk1 hk2
  rw [h_eq] at h_dvd
  exact h_dvd

lemma choose_relation (p k : ℕ) (hk : 1 ≤ k) (hkp : k < p) :
    k * (p - 1 + k).choose k = p * (p - 1 + k).choose (k - 1) := by
  have hn : p - 1 + k = p - 2 + k + 1 := by omega
  have h1 : (p - 2 + k + 1) * (p - 2 + k).choose (k - 1) = (p - 2 + k + 1).choose k * k := by
    have h_add := add_one_mul_choose_eq (p - 2 + k) (k - 1)
    have hk_rew : k - 1 + 1 = k := Nat.sub_add_cancel hk
    rw [hk_rew] at h_add
    exact h_add
  have h2 : (p - 2 + k).choose (k - 1) * (p - 2 + k + 1) = (p - 2 + k + 1).choose (k - 1) * (p - 2 + k + 1 - (k - 1)) := by
    apply choose_mul_succ_eq (p - 2 + k) (k - 1)
  have h_sub : p - 2 + k + 1 - (k - 1) = p := by omega
  rw [h_sub] at h2
  rw [← hn] at h1 h2
  calc
    k * (p - 1 + k).choose k = (p - 1 + k).choose k * k := mul_comm _ _
    _ = (p - 1 + k) * (p - 2 + k).choose (k - 1) := h1.symm
    _ = (p - 2 + k).choose (k - 1) * (p - 1 + k) := mul_comm _ _
    _ = (p - 1 + k).choose (k - 1) * p := h2
    _ = p * (p - 1 + k).choose (k - 1) := mul_comm _ _


lemma A_relation (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k < p) :
    let A := (p-1+k).choose k / p
    k * A = (p-1+k).choose (k-1) := by
  let A := (p-1+k).choose k / p
  have h_dvd : p ∣ (p-1+k).choose k := dvd_choose_helper p k hp hk1 hk2
  have h_cancel : (p-1+k).choose k = p * A := (Nat.mul_div_cancel' h_dvd).symm
  have h_rel := choose_relation p k hk1 hk2
  rw [h_cancel] at h_rel
  have h_eq : p * (k * A) = p * (p-1+k).choose (k-1) := by
    calc
      p * (k * A) = k * (p * A) := by ring
      _ = p * (p-1+k).choose (k-1) := h_rel
  exact Nat.eq_of_mul_eq_mul_left hp.pos h_eq


lemma coprime_helper (p k : ℕ) (hp : p.Prime) (hk : k + 1 < p) : (k + 1).Coprime p := by
  have h1 : p.Coprime (k + 1) := by
    apply hp.coprime_iff_not_dvd.2
    apply Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  exact h1.symm

lemma sum_pow_sub_three_zmod_eq_zero (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (range (p - 1)).sum (fun k => ((k + 1 : ZMod p)) ^ (p - 3)) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  generalize hd : p - 1 = d
  have hp_eq : p = d + 1 := by omega
  subst hp_eq
  have h_card : Fintype.card (ZMod (d + 1)) = d + 1 := ZMod.card (d + 1)
  have h_pow_lt : d + 1 - 3 < Fintype.card (ZMod (d + 1)) - 1 := by
    rw [h_card]
    omega
  have h_sum := FiniteField.sum_pow_lt_card_sub_one (K := ZMod (d + 1)) (d + 1 - 3) h_pow_lt
  have h_eq : ∑ x : ZMod (d + 1), x ^ (d + 1 - 3) = ∑ x : Fin (d + 1), (↑(x.val) : ZMod (d + 1)) ^ (d + 1 - 3) := by
    have hd_sub : d + 1 - 3 = d - 2 := by omega
    rw [hd_sub]
    congr 1
    ext x
    change x ^ (d - 2) = (↑x.val : ZMod (d + 1)) ^ (d - 2)
    have hx : (↑x.val : ZMod (d + 1)) = x := ZMod.natCast_zmod_val x
    rw [hx]
  have h_range := Fin.sum_univ_eq_sum_range (fun (i : ℕ) => (i : ZMod (d + 1)) ^ (d + 1 - 3)) (d + 1)
  rw [h_eq, h_range] at h_sum
  rw [sum_range_succ'] at h_sum
  have h_ne : d + 1 - 3 ≠ 0 := by omega
  simp only [Nat.cast_zero, zero_pow h_ne, add_zero, Nat.cast_add_one] at h_sum
  exact h_sum

lemma sum_pow_sub_three_modeq_zero (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (range (p - 1)).sum (fun k => (k + 1) ^ (p - 3)) ≡ 0 [MOD p] := by
  have h_zmod := sum_pow_sub_three_zmod_eq_zero p hp hp5
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact h_zmod

lemma choose_mod_p_eq_one (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k < p) :
    (p - 1 + k).choose (k - 1) ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h_lucas : (p - 1 + k).choose (k - 1) ≡ ((p - 1 + k) % p).choose ((k - 1) % p) * ((p - 1 + k) / p).choose ((k - 1) / p) [MOD p] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h_mod1 : (p - 1 + k) % p = k - 1 := by
    have h1 : p - 1 + k = (k - 1) + p := by omega
    rw [h1, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have h_mod2 : (k - 1) % p = k - 1 := Nat.mod_eq_of_lt (by omega)
  have h_div1 : (p - 1 + k) / p = 1 := by
    have h1 : p - 1 + k = (k - 1) + p := by omega
    rw [h1, Nat.add_div_right _ hp.pos]
    have h2 : (k - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [h2]
  have h_div2 : (k - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [h_mod1, h_mod2, h_div1, h_div2] at h_lucas
  simp at h_lucas
  exact h_lucas

lemma k_mul_A_mod_p_eq_one (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k < p) :
    k * ((p - 1 + k).choose k / p) ≡ 1 [MOD p] := by
  have h_rel := A_relation p k hp hk1 hk2
  have h_choose := choose_mod_p_eq_one p k hp hk1 hk2
  rw [← h_rel] at h_choose
  exact h_choose

lemma k_sq_mul_A_sq_mod_p_eq_one (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k < p) :
    k ^ 2 * ((p - 1 + k).choose k / p) ^ 2 ≡ 1 [MOD p] := by
  have h := k_mul_A_mod_p_eq_one p k hp hk1 hk2
  have h_sq := Nat.ModEq.mul h h
  have h_ring : (k * ((p - 1 + k).choose k / p)) * (k * ((p - 1 + k).choose k / p)) = k ^ 2 * ((p - 1 + k).choose k / p) ^ 2 := by ring
  rw [h_ring] at h_sq
  exact h_sq

lemma A_sq_modeq_pow_sub_three (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : k < p - 1) :
    (((p - 1 + k + 1).choose (k + 1)) / p) ^ 2 ≡ (k + 1) ^ (p - 3) [MOD p] := by
  let A := ((p - 1 + k + 1).choose (k + 1)) / p
  have h_fermat : (k + 1) ^ (p - 1) ≡ 1 [MOD p] := Nat.ModEq.pow_card_sub_one_eq_one hp (coprime_helper p k hp (by omega))
  have h_rel : (k + 1) ^ 2 * A ^ 2 ≡ 1 [MOD p] := k_sq_mul_A_sq_mod_p_eq_one p (k + 1) hp (by omega) (by omega)
  have h_mul := Nat.ModEq.mul (Nat.ModEq.refl ((k + 1) ^ (p - 3))) h_rel
  have h_eq1 : (k + 1) ^ (p - 3) * ((k + 1) ^ 2 * A ^ 2) = ((k + 1) ^ (p - 3) * (k + 1) ^ 2) * A ^ 2 := by ring
  have h_pow : (k + 1) ^ (p - 3) * (k + 1) ^ 2 = (k + 1) ^ (p - 1) := by
    rw [← pow_add]
    have : p - 3 + 2 = p - 1 := by omega
    rw [this]
  rw [h_eq1, h_pow] at h_mul
  have h_LHS : (k + 1) ^ (p - 1) * A ^ 2 ≡ 1 * A ^ 2 [MOD p] := Nat.ModEq.mul h_fermat (Nat.ModEq.refl (A ^ 2))
  rw [one_mul] at h_LHS
  have h_RHS : (k + 1) ^ (p - 3) * 1 = (k + 1) ^ (p - 3) := mul_one _
  rw [h_RHS] at h_mul
  exact h_LHS.symm.trans h_mul

lemma sum_modeq {α : Type*} (s : Finset α) (f g : α → ℕ) (m : ℕ) (h : ∀ x ∈ s, f x ≡ g x [MOD m]) :
    s.sum f ≡ s.sum g [MOD m] := by
  induction s using Finset.cons_induction with
  | empty =>
    simp
    rfl
  | cons a s ha ih =>
    simp only [mem_cons, forall_eq_or_imp] at h
    rw [sum_cons, sum_cons]
    exact Nat.ModEq.add h.1 (ih h.2)

lemma sum_A_sq_modeq_sum_pow_sub_three (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (range (p - 1)).sum (fun k => (((p - 1 + k + 1).choose (k + 1)) / p) ^ 2) ≡
    (range (p - 1)).sum (fun k => (k + 1) ^ (p - 3)) [MOD p] := by
  apply sum_modeq
  intro k hk
  rw [mem_range] at hk
  exact A_sq_modeq_pow_sub_three p k hp hp5 hk


lemma sum_sq_le_S1_sub_one_div_p_sq (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (range (p - 1)).sum (fun k => (((p - 1 + k + 1).choose (k + 1)) / p) ^ 2) ≤
    ((range p).sum (fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2) - 1) / p ^ 2 := by
  let f_sum := fun k => ((p - 1).choose (k + 1)) ^ 2 * ((p - 1 + k + 1).choose (k + 1)) ^ 2 / p ^ 2
  let g_sum := fun k => (((p - 1 + k + 1).choose (k + 1)) / p) ^ 2
  have h_eq : ((range p).sum (fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2) - 1) / p ^ 2 =
              (range (p - 1)).sum f_sum := by
    apply S1_sub_one_div_p_sq p hp hp3
  rw [h_eq]
  apply sum_le_sum
  intro k hk
  rw [mem_range] at hk
  have h_le : p ^ 2 * g_sum k ≤ ((p - 1).choose (k + 1)) ^ 2 * ((p - 1 + k + 1).choose (k + 1)) ^ 2 := by
    exact T_ge_sq p (k + 1) hp (by omega) (by omega)
  have h_div_le : p ^ 2 * g_sum k / p ^ 2 ≤ ((p - 1).choose (k + 1)) ^ 2 * ((p - 1 + k + 1).choose (k + 1)) ^ 2 / p ^ 2 := Nat.div_le_div_right h_le
  have h_LHS : p ^ 2 * g_sum k / p ^ 2 = g_sum k := by
    exact Nat.mul_div_cancel_left _ (Nat.pow_pos hp.pos)
  rw [h_LHS] at h_div_le
  exact h_div_le

lemma dvd_sum_A_sq (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ (range (p - 1)).sum (fun k => (((p - 1 + k + 1).choose (k + 1)) / p) ^ 2) := by
  have h1 := sum_A_sq_modeq_sum_pow_sub_three p hp hp5
  have h2 := sum_pow_sub_three_modeq_zero p hp hp5
  have h3 := h1.trans h2
  exact Nat.modEq_zero_iff_dvd.1 h3


lemma choose_mod_p_eq_one_B (p k : ℕ) (hp : p.Prime) (hk : k < p - 1) :
    (p + k + 1).choose (k + 1) ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h_lucas : (p + k + 1).choose (k + 1) ≡ ((p + k + 1) % p).choose ((k + 1) % p) * ((p + k + 1) / p).choose ((k + 1) / p) [MOD p] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h_mod1 : (p + k + 1) % p = k + 1 := by
    have h1 : p + k + 1 = (k + 1) + p := by omega
    rw [h1, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have h_mod2 : (k + 1) % p = k + 1 := Nat.mod_eq_of_lt (by omega)
  have h_div1 : (p + k + 1) / p = 1 := by
    have h1 : p + k + 1 = (k + 1) + p := by omega
    rw [h1, Nat.add_div_right _ hp.pos]
    have h2 : (k + 1) / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [h2]
  have h_div2 : (k + 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [h_mod1, h_mod2, h_div1, h_div2] at h_lucas
  simp at h_lucas
  exact h_lucas

lemma B_relation (p k : ℕ) (hp : p.Prime) (hk : k < p - 1) :
    let B := p.choose (k + 1) / p
    B * (k + 1) = (p - 1).choose k := by
  let B := p.choose (k + 1) / p
  have hk2 : k + 1 < p := by omega
  have hk_nz : k + 1 ≠ 0 := by omega
  have h_dvd : p ∣ p.choose (k + 1) := hp.dvd_choose_self hk_nz hk2
  have h_cancel : p.choose (k + 1) = p * B := (Nat.mul_div_cancel' h_dvd).symm
  have h_id := add_one_mul_choose_eq (p - 1) k
  have h_p : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  rw [h_p] at h_id
  have h_mul : p * (p - 1).choose k = p * (B * (k + 1)) := by
    calc
      p * (p - 1).choose k = p.choose (k + 1) * (k + 1) := h_id
      _ = (p * B) * (k + 1) := by rw [h_cancel]
      _ = p * (B * (k + 1)) := by ring
  exact Nat.eq_of_mul_eq_mul_left hp.pos h_mul.symm

lemma k_sq_mul_B_sq_mod_p_eq_one (p k : ℕ) (hp : p.Prime) (hk : k < p - 1) :
    (k + 1) ^ 2 * (p.choose (k + 1) / p) ^ 2 ≡ 1 [MOD p] := by
  have h_rel := B_relation p k hp hk
  have h_choose : ((p - 1).choose k) ^ 2 ≡ 1 [MOD p] := by
    have h_le : 1 ≤ ((p - 1).choose k) ^ 2 := by
      have h_pos : 1 ≤ (p-1).choose k := Nat.choose_pos (by omega)
      nlinarith
    exact ((Nat.modEq_iff_dvd' h_le).2 (choose_sq_sub_one_dvd p hp k (by omega))).symm
  rw [← h_rel] at h_choose
  have h_ring : (p.choose (k + 1) / p * (k + 1)) ^ 2 = (k + 1) ^ 2 * (p.choose (k + 1) / p) ^ 2 := by ring
  rw [h_ring] at h_choose
  exact h_choose

lemma B_sq_modeq_pow_sub_three (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : k < p - 1) :
    (p.choose (k + 1) / p) ^ 2 * (p + k + 1).choose (k + 1) ≡ (k + 1) ^ (p - 3) [MOD p] := by
  let B := p.choose (k + 1) / p
  have h_fermat : (k + 1) ^ (p - 1) ≡ 1 [MOD p] := Nat.ModEq.pow_card_sub_one_eq_one hp (coprime_helper p k hp (by omega))
  have h_rel : (k + 1) ^ 2 * B ^ 2 ≡ 1 [MOD p] := k_sq_mul_B_sq_mod_p_eq_one p k hp hk
  have h_choose_one : (p + k + 1).choose (k + 1) ≡ 1 [MOD p] := choose_mod_p_eq_one_B p k hp hk
  have h_rel_mul : (k + 1) ^ 2 * B ^ 2 * (p + k + 1).choose (k + 1) ≡ 1 * 1 [MOD p] := Nat.ModEq.mul h_rel h_choose_one
  rw [mul_one] at h_rel_mul
  have h_mul := Nat.ModEq.mul (Nat.ModEq.refl ((k + 1) ^ (p - 3))) h_rel_mul
  have h_eq1 : (k + 1) ^ (p - 3) * ((k + 1) ^ 2 * B ^ 2 * (p + k + 1).choose (k + 1)) = ((k + 1) ^ (p - 3) * (k + 1) ^ 2) * B ^ 2 * (p + k + 1).choose (k + 1) := by ring
  have h_pow : (k + 1) ^ (p - 3) * (k + 1) ^ 2 = (k + 1) ^ (p - 1) := by
    rw [← pow_add]
    have : p - 3 + 2 = p - 1 := by omega
    rw [this]
  rw [h_eq1, h_pow] at h_mul
  have h_LHS : (k + 1) ^ (p - 1) * B ^ 2 * (p + k + 1).choose (k + 1) ≡ 1 * B ^ 2 * (p + k + 1).choose (k + 1) [MOD p] := by
    apply Nat.ModEq.mul
    · exact Nat.ModEq.mul h_fermat (Nat.ModEq.refl (B ^ 2))
    · exact Nat.ModEq.refl _
  rw [one_mul] at h_LHS
  have h_RHS : (k + 1) ^ (p - 3) * 1 = (k + 1) ^ (p - 3) := mul_one _
  rw [h_RHS] at h_mul
  exact h_LHS.symm.trans h_mul

lemma sum_B_sq_modeq_sum_pow_sub_three (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (range (p - 1)).sum (fun k => (p.choose (k + 1) / p) ^ 2 * (p + k + 1).choose (k + 1)) ≡
    (range (p - 1)).sum (fun k => (k + 1) ^ (p - 3)) [MOD p] := by
  apply sum_modeq
  intro k hk
  rw [mem_range] at hk
  exact B_sq_modeq_pow_sub_three p k hp hp5 hk

lemma dvd_sum_B_sq (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ (range (p - 1)).sum (fun k => (p.choose (k + 1) / p) ^ 2 * (p + k + 1).choose (k + 1)) := by
  have h1 := sum_B_sq_modeq_sum_pow_sub_three p hp hp5
  have h2 := sum_pow_sub_three_modeq_zero p hp hp5
  have h3 := h1.trans h2
  exact Nat.modEq_zero_iff_dvd.1 h3

lemma dvd_middle_sum_p_cubed (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    let S2 := (range (p + 1)).sum (fun k => (p.choose k) ^ 2 * ((p + k).choose k))
    p ^ 3 ∣ S2 - 1 - (2 * p).choose p := by
  intro S2
  have hp3 : 3 ≤ p := by omega
  have h_split := s_mod_split_helper p hp hp3
  have h_eq : S2 - 1 - (2 * p).choose p = (range (p - 1)).sum (fun k => (p.choose (k + 1)) ^ 2 * ((p + k + 1).choose (k + 1))) := by
    change (range (p + 1)).sum (fun k => (p.choose k) ^ 2 * ((p + k).choose k)) - 1 - (2 * p).choose p = _
    rw [h_split]
    omega
  rw [h_eq]
  have h_dvd : ∀ k < p - 1, p ^ 2 ∣ (p.choose (k + 1)) ^ 2 * ((p + k + 1).choose (k + 1)) := by
    intro k hk
    exact s_term_dvd_helper p k hp (by omega)
  have h_sum_eq := sum_div_sq_helper p (p - 1) (fun k => (p.choose (k + 1)) ^ 2 * ((p + k + 1).choose (k + 1))) hp.pos h_dvd
  have h_eq2 : (range (p - 1)).sum (fun k => (p.choose (k + 1)) ^ 2 * ((p + k + 1).choose (k + 1))) =
               p ^ 2 * (range (p - 1)).sum (fun k => (p.choose (k + 1) / p) ^ 2 * ((p + k + 1).choose (k + 1))) := by
    rw [mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have hk_nz : k + 1 ≠ 0 := by omega
    have hk_lt : k + 1 < p := by omega
    have h_pdvd : p ∣ p.choose (k + 1) := hp.dvd_choose_self hk_nz hk_lt
    have h_cancel : p.choose (k + 1) = p * (p.choose (k + 1) / p) := (Nat.mul_div_cancel' h_pdvd).symm
    nth_rw 1 [h_cancel]
    ring
  rw [h_eq2]
  rcases dvd_sum_B_sq p hp hp5 with ⟨K, hK⟩
  rw [hK]
  use K
  ring

lemma central_choose_eq_sum_choose_sq (p : ℕ) :
    (2 * p).choose p = (range (p + 1)).sum (fun k => (p.choose k) ^ 2) := by
  have h_add : (2 * p).choose p = (p + p).choose p := by
    congr 1
    ring
  rw [h_add]
  rw [Nat.add_choose_eq p p p]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.choose i * p.choose j) p]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have hk_le : k ≤ p := by omega
  have h_symm : p.choose (p - k) = p.choose k := Nat.choose_symm hk_le
  rw [h_symm]
  ring

lemma B_sq_only_modeq_pow_sub_three (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : k < p - 1) :
    (p.choose (k + 1) / p) ^ 2 ≡ (k + 1) ^ (p - 3) [MOD p] := by
  let B := p.choose (k + 1) / p
  have h_choose_one : (p + k + 1).choose (k + 1) ≡ 1 [MOD p] := choose_mod_p_eq_one_B p k hp hk
  have h1 : B ^ 2 * 1 ≡ B ^ 2 * (p + k + 1).choose (k + 1) [MOD p] := by
    apply Nat.ModEq.mul (Nat.ModEq.refl _) h_choose_one.symm
  rw [mul_one] at h1
  have h2 : B ^ 2 * (p + k + 1).choose (k + 1) ≡ (k + 1) ^ (p - 3) [MOD p] := B_sq_modeq_pow_sub_three p k hp hp5 hk
  exact h1.trans h2

lemma sum_B_sq_only_modeq_sum_pow_sub_three (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (range (p - 1)).sum (fun k => (p.choose (k + 1) / p) ^ 2) ≡
    (range (p - 1)).sum (fun k => (k + 1) ^ (p - 3)) [MOD p] := by
  apply sum_modeq
  intro k hk
  rw [mem_range] at hk
  exact B_sq_only_modeq_pow_sub_three p k hp hp5 hk

lemma dvd_sum_B_sq_only (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ (range (p - 1)).sum (fun k => (p.choose (k + 1) / p) ^ 2) := by
  have h1 := sum_B_sq_only_modeq_sum_pow_sub_three p hp hp5
  have h2 := sum_pow_sub_three_modeq_zero p hp hp5
  have h3 := h1.trans h2
  exact Nat.modEq_zero_iff_dvd.1 h3

lemma central_choose_mod_p_cubed (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : p ^ 3 ∣ (2 * p).choose p - 2 := by
  have h_sum := central_choose_eq_sum_choose_sq p
  have h_p_pos : 1 ≤ p := by omega
  have h_split := sum_range_succ_split_both p h_p_pos (fun k => (p.choose k) ^ 2)
  have h_term0 : (p.choose 0) ^ 2 = 1 := by simp
  have h_termp : (p.choose p) ^ 2 = 1 := by simp
  rw [h_term0, h_termp] at h_split
  have h_sum_eq : (range (p + 1)).sum (fun k => (p.choose k) ^ 2) = 2 + (range (p - 1)).sum (fun k => (p.choose (k + 1)) ^ 2) := by
    omega
  have h_eq : (2 * p).choose p - 2 = (range (p - 1)).sum (fun k => (p.choose (k + 1)) ^ 2) := by
    rw [h_sum, h_sum_eq]
    omega
  rw [h_eq]
  have h_eq2 : (range (p - 1)).sum (fun k => (p.choose (k + 1)) ^ 2) =
               p ^ 2 * (range (p - 1)).sum (fun k => (p.choose (k + 1) / p) ^ 2) := by
    rw [mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have hk_nz : k + 1 ≠ 0 := by omega
    have hk_lt : k + 1 < p := by omega
    have h_pdvd : p ∣ p.choose (k + 1) := hp.dvd_choose_self hk_nz hk_lt
    have h_cancel : p.choose (k + 1) = p * (p.choose (k + 1) / p) := (Nat.mul_div_cancel' h_pdvd).symm
    nth_rw 1 [h_cancel]
    ring
  rw [h_eq2]
  rcases dvd_sum_B_sq_only p hp hp5 with ⟨K, hK⟩
  rw [hK]
  use K
  ring

lemma dvd_of_dvd_sub_of_dvd {A B p : ℕ} (h1 : p ∣ A - B) (h2 : p ∣ B) (h_le : B ≤ A) : p ∣ A := by
  have h_eq : A = (A - B) + B := (Nat.sub_add_cancel h_le).symm
  rw [h_eq]
  exact dvd_add h1 h2

lemma dvd_mul_of_div_dvd (p x : ℕ) (_hp : p.Prime) (h_div : p ^ 2 ∣ x) (h_dvd : p ∣ x / p ^ 2) :
    p ^ 3 ∣ x := by
  have h_eq : x = p ^ 2 * (x / p ^ 2) := (Nat.mul_div_cancel' h_div).symm
  rcases h_dvd with ⟨k, hk⟩
  rw [hk] at h_eq
  have h_eq2 : x = p ^ 3 * k := by
    calc
      x = p ^ 2 * (p * k) := h_eq
      _ = p ^ 3 * k := by ring
  rw [h_eq2]
  exact dvd_mul_right (p ^ 3) k


lemma sorry_conjecture (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (S1 S2 : ℕ) (h_div1 : p ^ 3 ∣ S1 - 1) (h_div2 : p ^ 3 ∣ S2 - 3) (h_S1_ge : 1 ≤ S1) (h_S2_ge : 3 ≤ S2) :
    p ^ 2 ∣ 5 * ((S1 - 1) / p ^ 3) + 2 * ((S2 - 3) / p ^ 3) := sorry







/--
Conjecture 1 from OEIS A357960:
$a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem oeis_A357960_conjecture_1 (p : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) :
    a p ≡ a 1 [MOD p ^ 5] := by
  rcases prime_cases p hp hp_ge_3 with rfl | hp_ge_5
  · decide
  · let S1 := (range p).sum (fun k => ((p - 1).choose k) ^ 2 * ((p - 1 + k).choose k) ^ 2)
    let S2 := (range (p + 1)).sum (fun k => (p.choose k) ^ 2 * ((p + k).choose k))
    have hp3 : 3 ≤ p := by omega
    have h_S1_ge : 1 ≤ S1 := S1_ge_one p (by omega)
    have h_S2_ge : 3 ≤ S2 := S2_ge_three p hp (by omega)
    have h_S1_sub_one_eq : S1 - 1 = (range (p - 1)).sum (fun k => ((p - 1).choose (k + 1)) ^ 2 * ((p - 1 + k + 1).choose (k + 1)) ^ 2) :=
      S1_sub_one_eq_sum p (by omega)
    have h_S1_div_p_sq : p ^ 2 ∣ S1 - 1 := by
      rw [h_S1_sub_one_eq]
      exact sum_term_dvd_helper p hp hp3
    have h_dvd_sub : p ∣ (S1 - 1) / p ^ 2 - (range (p - 1)).sum (fun k => (((p - 1 + k + 1).choose (k + 1)) / p) ^ 2) :=
      S1_sub_one_div_p_sq_modeq_sum_sq p hp hp3
    have h_dvd_sum : p ∣ (range (p - 1)).sum (fun k => (((p - 1 + k + 1).choose (k + 1)) / p) ^ 2) :=
      dvd_sum_A_sq p hp hp_ge_5
    have h_le_sum : (range (p - 1)).sum (fun k => (((p - 1 + k + 1).choose (k + 1)) / p) ^ 2) ≤ (S1 - 1) / p ^ 2 :=
      sum_sq_le_S1_sub_one_div_p_sq p hp hp3
    have h_dvd_div : p ∣ (S1 - 1) / p ^ 2 :=
      dvd_of_dvd_sub_of_dvd h_dvd_sub h_dvd_sum h_le_sum
    have h_div1 : p ^ 3 ∣ S1 - 1 :=
      dvd_mul_of_div_dvd p (S1 - 1) hp h_S1_div_p_sq h_dvd_div
    have h_div2 : p ^ 3 ∣ S2 - 3 := by
      have h_sum_split := s_mod_split_helper p hp (by omega)
      have h_ge_sum : 1 + (2 * p).choose p ≤ S2 := by
        change 1 + (2 * p).choose p ≤ (range (p + 1)).sum (fun k => (p.choose k) ^ 2 * ((p + k).choose k))
        rw [h_sum_split]
        omega
      have h1 : S2 - 3 = (S2 - 1 - (2 * p).choose p) + ((2 * p).choose p - 2) := by
        have h_choose : 2 ≤ (2 * p).choose p := choose_p_ge_two p hp (by omega)
        omega
      rw [h1]
      apply dvd_add
      · exact dvd_middle_sum_p_cubed p hp hp_ge_5
      · exact central_choose_mod_p_cubed p hp hp_ge_5
    have h_div3 : p ^ 2 ∣ 5 * ((S1 - 1) / p ^ 3) + 2 * ((S2 - 3) / p ^ 3) := sorry_conjecture p hp hp_ge_5 S1 S2 h_div1 h_div2 h_S1_ge h_S2_ge
    have h_glue := glue_step p S1 S2 hp3 h_S1_ge h_S2_ge h_div1 h_div2 h_div3
    change S1 ^ 5 * S2 ^ 6 ≡ a 1 [MOD p ^ 5]
    have h_a1 : a 1 = 729 := rfl
    rw [h_a1]
    exact h_glue


#print axioms oeis_A357960_conjecture_1
