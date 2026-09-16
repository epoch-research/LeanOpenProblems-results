import FormalConjectures.Util.ProblemImports

open Nat BigOperators

noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_pred : ℕ := n.pred
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)
    let denominator : ℕ := n.factorial
    numerator / denominator

-- Proof8.lean

open Nat BigOperators

lemma dvd_prod_of_dvd {α β : Type} [CommMonoid α] {s : Finset β} {f : β → α} {p : α} (h : ∀ x ∈ s, p ∣ f x) :
  p ^ s.card ∣ s.prod f := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp
  · rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_add, pow_one, mul_comm]
    apply mul_dvd_mul
    · exact h a (Finset.mem_insert_self a s)
    · apply ih
      intro x hx
      exact h x (Finset.mem_insert_of_mem hx)

-- Proof10.lean

lemma fermat (p : ℕ) [hp : Fact p.Prime] (hodd : p > 2) (j : ℕ) :
  p ∣ 2 ^ (j * (p - 1)) - 1 := by
  have h_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
      calc ((2 : ℕ) : ZMod p) = (2 : ZMod p) := by rfl
        _ = (0 : ZMod p) := h
        _ = ((0 : ℕ) : ZMod p) := Nat.cast_zero.symm
    have h2 : 2 ≡ 0 [MOD p] := (ZMod.natCast_eq_natCast_iff 2 0 p).mp h1
    have h3 : p ∣ 2 := Nat.modEq_zero_iff_dvd.mp h2
    have : p ≤ 2 := Nat.le_of_dvd (by decide) h3
    omega
  have h1 : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h_ne
  have h2 : (2 : ZMod p) ^ (j * (p - 1)) = 1 := by
    rw [mul_comm, pow_mul, h1, one_pow]
  have h3 : ((2 ^ (j * (p - 1)) : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_pow]
    exact h2
  have h4 : ((2 ^ (j * (p - 1)) - 1 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
    have h_pow : 2 ^ (j * (p - 1)) ≥ 1 := Nat.one_le_two_pow
    rw [Nat.cast_sub h_pow, h3, Nat.cast_one, sub_self, Nat.cast_zero]
  have h5 : 2 ^ (j * (p - 1)) - 1 ≡ 0 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp h4
  exact Nat.modEq_zero_iff_dvd.mp h5

-- Proof11.lean

open Nat BigOperators

lemma p_pow_dvd_P (n p : ℕ) [Fact p.Prime] (hn2 : n > 2) (hodd : p > 2) :
  p ^ ((n - 2) / (p - 1)) ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  let k := (n - 2) / (p - 1)
  let S := (Finset.Ico 1 (k + 1)).image (fun j => j * (p - 1))
  have h_sub : S ⊆ Finset.Ico 1 (n - 1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨j, hj, rfl⟩
    rw [Finset.mem_Ico] at hj ⊢
    constructor
    · have : p - 1 ≥ 2 := by omega
      have : j ≥ 1 := hj.1
      nlinarith
    · have h_k_def : k = (n - 2) / (p - 1) := rfl
      have hj_le_k : j ≤ k := by omega
      have h1 : j * (p - 1) ≤ k * (p - 1) := Nat.mul_le_mul_right (p - 1) hj_le_k
      have h2 : k * (p - 1) ≤ n - 2 := by
        rw [h_k_def]
        exact Nat.div_mul_le_self (n - 2) (p - 1)
      have h3 : j * (p - 1) ≤ n - 2 := le_trans h1 h2
      have : n ≥ 3 := hn2
      omega
  have h_dvd : ∀ x ∈ S, p ∣ 2 ^ x - 1 := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨j, _, rfl⟩
    exact fermat p hodd j
  have h_prod : p ^ S.card ∣ S.prod (fun k => 2 ^ k - 1) := dvd_prod_of_dvd h_dvd
  have h_card : S.card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have : p - 1 > 0 := by omega
      exact Nat.eq_of_mul_eq_mul_right this hab
  rw [h_card] at h_prod
  have h_dvd_prod : S.prod (fun k => 2 ^ k - 1) ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
    exact Finset.prod_dvd_prod_of_subset S (Finset.Ico 1 (n - 1)) (fun k => 2^k - 1) h_sub
  exact dvd_trans h_prod h_dvd_prod

-- Proof5.lean

open Nat BigOperators

lemma mod_div_trick (p k : ℕ) (hp : p ≥ 2) (hk : k ≥ 2) :
  (p * k - 1) % p = p - 1 ∧ (p * k - 1) / p = k - 1 := by
  have h1 : p * k - 1 = (p - 1) + p * (k - 1) := by
    zify [show p * k ≥ 1 by nlinarith, show k ≥ 1 by omega, show p ≥ 1 by omega]
    ring
  have hl : p - 1 < p := by omega
  constructor
  · rw [h1]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  · rw [h1]
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hl]
    omega

-- Proof6.lean

open Nat BigOperators

lemma digits_sum_pos (p n : ℕ) (hp : p > 1) (hn : n > 0) :
  (p.digits n).sum ≥ 1 := by
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.digits_def' hp hn]
  simp only [List.sum_cons]
  by_cases h0 : n / p = 0
  · have h_mod : n % p = n := by
      have : n < p := by
        by_contra h
        have : 0 < n / p := Nat.div_pos (by omega) (by omega)
        omega
      exact Nat.mod_eq_of_lt this
    omega
  · have h_div_pos : n / p > 0 := Nat.pos_of_ne_zero h0
    have h_lt : n / p < n := Nat.div_lt_self hn hp
    have := ih (n / p) h_lt h_div_pos
    omega

lemma digits_sum_ge_p (n p : ℕ) [hp : Fact p.Prime] (hn2 : n > 2) (hcomp : ¬ n.Prime) (hdvd : p ∣ n) :
  (p.digits (n - 1)).sum ≥ p := by
  have hk : ∃ k, n = p * k := exists_eq_mul_right_of_dvd hdvd
  rcases hk with ⟨k, rfl⟩
  have hk2 : k ≥ 2 := by
    by_contra h
    have h1 : k < 2 := by omega
    rcases k with _ | _ | _
    · omega
    · have : p * 1 = p := mul_one p
      rw [this] at hcomp
      exact hcomp hp.out
    · omega
  have h_p2 : p ≥ 2 := hp.out.two_le
  have mod_div := mod_div_trick p k h_p2 hk2
  have h_n1_pos : p * k - 1 > 0 := by
    have : p * k ≥ 4 := by nlinarith
    omega
  rw [Nat.digits_def' (by omega) h_n1_pos]
  simp only [List.sum_cons]
  rw [mod_div.1, mod_div.2]
  have h_k_1_pos : k - 1 > 0 := by omega
  have := digits_sum_pos p (k - 1) (by omega) h_k_1_pos
  omega

-- Proof7.lean

open Nat BigOperators

lemma vp_fact_upper_bound (n p : ℕ) [Fact p.Prime] (hn2 : n > 2) (hodd : p > 2) (hcomp : ¬ n.Prime) (hdvd : p ∣ n) :
  padicValNat p (n - 1).factorial < (n - 2) / (p - 1) := by
  have h1 : (p - 1) * padicValNat p (n - 1).factorial = (n - 1) - (p.digits (n - 1)).sum := by
    exact sub_one_mul_padicValNat_factorial (n - 1)
  have h2 : (p.digits (n - 1)).sum ≥ p := digits_sum_ge_p n p hn2 hcomp hdvd
  have hk : ∃ k, n = k * p := exists_eq_mul_left_of_dvd hdvd
  rcases hk with ⟨k, rfl⟩
  have hk2 : k ≥ 2 := by
    by_contra h
    have h1 : k < 2 := by omega
    rcases k with _ | _ | _
    · omega
    · have : 1 * p = p := one_mul p
      rw [this] at hcomp
      exact hcomp (Fact.out)
    · omega
  have hp2 : p ≥ 3 := by omega
  have h3 : (p - 1) * padicValNat p (k * p - 1).factorial ≤ k * p - 1 - p := by omega
  have h6 : (padicValNat p (k * p - 1).factorial + 1) * (p - 1) ≤ k * p - 2 := by
    have eq1 : (padicValNat p (k * p - 1).factorial + 1) * (p - 1) = (p - 1) * padicValNat p (k * p - 1).factorial + (p - 1) := by ring
    rw [eq1]
    have eq2 : k * p - 1 - p + (p - 1) = k * p - 2 := by
      have h_k_p : k * p ≥ 2 * p := by nlinarith
      have h_sub : k * p - 1 ≥ p := by omega
      have h_kp_pos : k * p ≥ 1 := by omega
      have h_kp_2 : k * p ≥ 2 := by omega
      zify [h_k_p, h_sub, h_kp_pos, h_kp_2, show p ≥ 1 by omega]
      ring
    omega
  have h7 : padicValNat p (k * p - 1).factorial + 1 ≤ (k * p - 2) / (p - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    exact h6
  omega

-- Proof12.lean

open Nat BigOperators

lemma P_pos (n : ℕ) (hn2 : n > 2) :
  (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) > 0 := by
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Ico] at hk
  have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk.1
  have h2 : 2 ^ 1 = 2 := rfl
  omega

-- Proof13.lean

open Nat BigOperators

lemma vp_P_lower_bound (n p : ℕ) [Fact p.Prime] (hn2 : n > 2) (hodd : p > 2) :
  (n - 2) / (p - 1) ≤ padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
  have hdvd := p_pow_dvd_P n p hn2 hodd
  have hpos := P_pos n hn2
  have hne : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by omega
  exact (padicValNat_dvd_iff_le hne).mp hdvd

-- Proof17.lean

open Nat BigOperators

lemma vp_fact_le (n p : ℕ) [Fact p.Prime] (hn : n > 2) :
  padicValNat p (n - 1).factorial ≤ (n - 2) / (p - 1) := by
  have h1 : (p - 1) * padicValNat p (n - 1).factorial = (n - 1) - (p.digits (n - 1)).sum := by
    exact sub_one_mul_padicValNat_factorial (n - 1)
  have hp_pos : p > 1 := (Fact.out : p.Prime).one_lt
  have hn1_pos : n - 1 > 0 := by omega
  have h2 : (p.digits (n - 1)).sum ≥ 1 := digits_sum_pos p (n - 1) hp_pos hn1_pos
  have h3 : padicValNat p (n - 1).factorial * (p - 1) ≤ n - 2 := by
    calc padicValNat p (n - 1).factorial * (p - 1) = (p - 1) * padicValNat p (n - 1).factorial := by ring
      _ = (n - 1) - (p.digits (n - 1)).sum := h1
      _ ≤ (n - 1) - 1 := by omega
      _ = n - 2 := by omega
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact h3

-- Proof19.lean

open Nat BigOperators

lemma prod_pos (n : ℕ) : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) > 0 := by
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Ico] at hk
  have h1 : 2 ^ k > 1 := by
    calc 2 ^ k ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hk.1
      _ = 2 := by decide
      _ > 1 := by decide
  omega

-- Proof18.lean

open Nat BigOperators

lemma exact_div (n : ℕ) (hn : n > 2) :
  (n - 1).factorial ∣ 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p m hp hpm
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hodd : p > 2
  · have h_fact_pos : (n - 1).factorial ≠ 0 := by
      exact Nat.ne_of_gt (Nat.factorial_pos (n - 1))
    have h1 : m ≤ padicValNat p (n - 1).factorial := (padicValNat_dvd_iff_le h_fact_pos).mp hpm
    have h2 : padicValNat p (n - 1).factorial ≤ (n - 2) / (p - 1) := vp_fact_le n p hn
    have h3 : (n - 2) / (p - 1) ≤ padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := vp_P_lower_bound n p hn hodd
    have h4 : m ≤ padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by omega
    have hprod_pos : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
      exact Nat.ne_of_gt (prod_pos n)
    have h5 : p ^ m ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := (padicValNat_dvd_iff_le hprod_pos).mpr h4
    exact dvd_mul_of_dvd_right h5 _
  · have hp_ge2 : p ≥ 2 := hp.two_le
    have p2 : p = 2 := by omega
    subst p2
    have h_fact_pos : (n - 1).factorial ≠ 0 := by
      exact Nat.ne_of_gt (Nat.factorial_pos (n - 1))
    have h1 : m ≤ padicValNat 2 (n - 1).factorial := (padicValNat_dvd_iff_le h_fact_pos).mp hpm
    have h2 : padicValNat 2 (n - 1).factorial ≤ n - 2 := by
      have hle : padicValNat 2 (n - 1).factorial ≤ (n - 2) / (2 - 1) := vp_fact_le n 2 hn
      omega
    have h3 : m ≤ n - 2 := by omega
    have h4 : 2 ^ m ∣ 2 ^ (n - 2) := Nat.pow_dvd_pow 2 h3
    exact dvd_mul_of_dvd_left h4 _

-- Proof20.lean

open Nat BigOperators

lemma a_mul_fact (n : ℕ) (hn : n > 2) :
  a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  have hn1 : n - 1 ≠ 0 := by omega
  unfold a
  rw [dif_neg hn1]
  have h_div : (n - 1).factorial ∣ 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := exact_div n hn
  exact Nat.div_mul_cancel h_div

-- Proof22.lean

open Nat BigOperators

lemma odd_pow_minus_one (k : ℕ) (hk : k ≥ 1) : Odd (2 ^ k - 1) := by
  have : 2 ^ k = 2 * 2 ^ (k - 1) := by
    calc 2 ^ k = 2 ^ (1 + (k - 1)) := by rw [add_tsub_cancel_of_le hk]
      _ = 2 ^ 1 * 2 ^ (k - 1) := pow_add 2 1 (k - 1)
      _ = 2 * 2 ^ (k - 1) := by ring
  rw [this]
  have hpos : 2 ^ (k - 1) ≥ 1 := by
    have h1 : 2 ≥ 1 := by omega
    exact Nat.one_le_pow (k - 1) 2 h1
  have h2 : 2 * 2 ^ (k - 1) ≥ 2 := by nlinarith
  have h3 : 2 * 2 ^ (k - 1) - 1 = 2 * (2 ^ (k - 1) - 1) + 1 := by omega
  rw [h3]
  use 2 ^ (k - 1) - 1

lemma P_odd (n : ℕ) (hn2 : n > 2) :
  ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) % 2 = 1 := by
  have h_odd : Odd ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
    apply Finset.prod_induction (s := Finset.Ico 1 (n - 1)) (p := Odd)
    · intro a b ha hb
      exact Odd.mul ha hb
    · exact odd_one
    · intro x hx
      rw [Finset.mem_Ico] at hx
      exact odd_pow_minus_one x hx.1
  rcases h_odd with ⟨m, hm⟩
  rw [hm]
  omega

lemma padicValNat_P_two (n : ℕ) (hn2 : n > 2) :
  padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = 0 := by
  have H : ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) % 2 = 1 := P_odd n hn2
  have h_prod_pos : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
    intro h
    rw [h] at H
    omega
  by_contra h_neq
  have h_pos : padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) ≥ 1 := by omega
  have h_dvd : 2 ^ 1 ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := (padicValNat_dvd_iff_le h_prod_pos).mpr h_pos
  have h2 : 2 ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
    have : 2 ^ 1 = 2 := by rfl
    rw [← this]
    exact h_dvd
  have hm : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  omega

-- Proof21.lean

open Nat

lemma vp_fact_upper_bound_2 (n : ℕ) (hn2 : n > 2) (heven : 2 ∣ n) :
  padicValNat 2 (n - 1).factorial < n - 2 := by
  have h1 : padicValNat 2 (n - 1).factorial = (n - 1) - (Nat.digits 2 (n - 1)).sum := by
    have h_sub : (2 - 1) * padicValNat 2 (n - 1).factorial = (n - 1) - (Nat.digits 2 (n - 1)).sum := by
      exact sub_one_mul_padicValNat_factorial (n - 1)
    have h_sub2 : 2 - 1 = 1 := rfl
    rw [h_sub2, one_mul] at h_sub
    exact h_sub
  have h2 : (Nat.digits 2 (n - 1)).sum ≥ 2 := by
    rcases heven with ⟨m, hm⟩
    have hm2 : m ≥ 2 := by omega
    have hn1 : n - 1 = 1 + 2 * (m - 1) := by omega
    have hb : 1 < 2 := by omega
    have hxb : 1 < 2 := by omega
    have hxy : 1 ≠ 0 ∨ m - 1 ≠ 0 := Or.inl (by omega)
    have h_digits : Nat.digits 2 (n - 1) = 1 :: Nat.digits 2 (m - 1) := by
      rw [hn1]
      exact Nat.digits_add 2 hb 1 (m - 1) hxb hxy
    have h_sum : (Nat.digits 2 (n - 1)).sum = 1 + (Nat.digits 2 (m - 1)).sum := by
      rw [h_digits, List.sum_cons]
    have hm1_pos : m - 1 > 0 := by omega
    have h_sum_m1 : (Nat.digits 2 (m - 1)).sum ≥ 1 := digits_sum_pos 2 (m - 1) hb hm1_pos
    omega
  omega

-- Proof23.lean

open Nat BigOperators

lemma odd_prime_factor_contradiction (n p : ℕ) (hn2 : n > 2) (hcomp : ¬ n.Prime)
  (hp_prime : p.Prime) (hp_odd : p > 2) (hp_dvd_n : p ∣ n)
  (h_dvd : n ∣ a (n - 1) + 2 ^ (n - 2)) : False := by
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have h_fact_pos : (n - 1).factorial ≠ 0 := Nat.ne_of_gt (Nat.factorial_pos (n - 1))
  have h_mul : a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := a_mul_fact n hn2
  have h_vp_fact : padicValNat p (n - 1).factorial < (n - 2) / (p - 1) := vp_fact_upper_bound n p hn2 hp_odd hcomp hp_dvd_n
  have h_vp_P : (n - 2) / (p - 1) ≤ padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := vp_P_lower_bound n p hn2 hp_odd
  have h_vp_P_gt : padicValNat p (n - 1).factorial < padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by omega
  have h_P_pos : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := Nat.ne_of_gt (prod_pos n)
  have h_2_pos : 2 ^ (n - 2) ≠ 0 := by
    have h1 : 2 ^ (n - 2) > 0 := by positivity
    omega
  have h_a_pos : a (n - 1) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h_mul
    have hp2 : 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) = 0 := h_mul.symm
    cases Nat.mul_eq_zero.mp hp2 with
    | inl h => exact h_2_pos h
    | inr h => exact h_P_pos h
  have h_vp_mul : padicValNat p (a (n - 1) * (n - 1).factorial) = padicValNat p (a (n - 1)) + padicValNat p (n - 1).factorial := padicValNat.mul h_a_pos h_fact_pos
  have h_vp_RHS : padicValNat p (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = padicValNat p (2 ^ (n - 2)) + padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := padicValNat.mul h_2_pos h_P_pos
  have h_vp_2 : padicValNat p (2 ^ (n - 2)) = 0 := by
    by_contra hz
    have h1 : padicValNat p (2 ^ (n - 2)) ≥ 1 := by omega
    have h2 : p ^ 1 ∣ 2 ^ (n - 2) := (padicValNat_dvd_iff_le h_2_pos).mpr h1
    have h3 : p ∣ 2 ^ (n - 2) := by
      have : p ^ 1 = p := pow_one p
      rw [← this]
      exact h2
    have h4 : p ∣ 2 := hp_prime.dvd_of_dvd_pow h3
    have h5 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp h4
    omega
  have h_eq : padicValNat p (a (n - 1)) + padicValNat p (n - 1).factorial = padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
    rw [← h_vp_mul, h_mul, h_vp_RHS, h_vp_2, zero_add]
  have h_vp_a : padicValNat p (a (n - 1)) ≥ 1 := by omega
  have h_dvd_a : p ∣ a (n - 1) := by
    have hdvd1 : p ^ 1 ∣ a (n - 1) := (padicValNat_dvd_iff_le h_a_pos).mpr h_vp_a
    have hpow : p ^ 1 = p := pow_one p
    rw [← hpow]
    exact hdvd1
  have h_p_dvd_sum : p ∣ a (n - 1) + 2 ^ (n - 2) := Nat.dvd_trans hp_dvd_n h_dvd
  have h_p_dvd_2 : p ∣ 2 ^ (n - 2) := (Nat.dvd_add_right h_dvd_a).mp h_p_dvd_sum
  have h_p_dvd_2' : p ∣ 2 := hp_prime.dvd_of_dvd_pow h_p_dvd_2
  have h_p_eq_2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp h_p_dvd_2'
  omega

-- Proof24.lean

open Nat

lemma digits_two_pow_sub_one (m : ℕ) : (Nat.digits 2 (2 ^ m - 1)).sum = m := by
  induction m with
  | zero =>
    have : 2 ^ 0 - 1 = 0 := rfl
    rw [this, Nat.digits_zero, List.sum_nil]
  | succ m ih =>
    have h1 : 2 ^ (m + 1) - 1 = 1 + 2 * (2 ^ m - 1) := by
      have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      have hpos : 2 ^ m ≥ 1 := by
        have hd : 2 ≥ 1 := by omega
        exact Nat.one_le_pow m 2 hd
      omega
    rw [h1]
    have h_digits : Nat.digits 2 (1 + 2 * (2 ^ m - 1)) = 1 :: Nat.digits 2 (2 ^ m - 1) := by
      exact Nat.digits_add 2 (by decide) 1 (2 ^ m - 1) (by decide) (Or.inl (by decide))
    rw [h_digits, List.sum_cons, ih]
    omega

-- Proof25.lean

open Nat BigOperators

lemma padicValNat_two_pow (k : ℕ) : padicValNat 2 (2 ^ k) = k := by
  have hpos : 2 ^ k ≠ 0 := by
    have : 2 ^ k > 0 := by positivity
    omega
  have h1 : k ≤ padicValNat 2 (2 ^ k) := (padicValNat_dvd_iff_le hpos).mp (dvd_rfl)
  have h2 : padicValNat 2 (2 ^ k) ≤ k := by
    by_contra hc
    have : padicValNat 2 (2 ^ k) ≥ k + 1 := by omega
    have : 2 ^ (k + 1) ∣ 2 ^ k := (padicValNat_dvd_iff_le hpos).mpr this
    have : 2 ^ (k + 1) ≤ 2 ^ k := Nat.le_of_dvd (by positivity) this
    have : 2 ^ (k + 1) > 2 ^ k := by
      have h2 : 2 > 1 := by omega
      exact Nat.pow_lt_pow_right h2 (by omega)
    omega
  omega

lemma pow_two_ge_add_two (m : ℕ) (hm2 : m ≥ 2) : 2 ^ m ≥ m + 2 := by
  induction m, hm2 using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have : 2 * 2 ^ k ≥ 2 * (k + 2) := Nat.mul_le_mul_left 2 ih
    omega

lemma power_of_two_contradiction (n m : ℕ) (hn2 : n > 2) (hcomp : ¬ n.Prime)
  (hn_eq : n = 2 ^ m)
  (h_dvd : n ∣ a (n - 1) + 2 ^ (n - 2)) : False := by
  have hm2 : m ≥ 2 := by
    by_contra h
    have : m < 2 := by omega
    rcases m with _ | _ | _
    · have : n = 1 := by omega
      omega
    · have : n = 2 := by omega
      omega
    · omega
  have h_pow_m : 2 ^ m ≥ m + 2 := pow_two_ge_add_two m hm2
  have hn1 : n - 1 = 2 ^ m - 1 := by omega
  have h_fact_pos : (n - 1).factorial ≠ 0 := Nat.ne_of_gt (Nat.factorial_pos (n - 1))
  have h_P_pos : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := Nat.ne_of_gt (prod_pos n)
  have h_2_pos : 2 ^ (n - 2) ≠ 0 := by
    have h1 : 2 ^ (n - 2) > 0 := by positivity
    omega
  have h_mul : a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := a_mul_fact n hn2
  have h_a_pos : a (n - 1) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h_mul
    have hp2 : 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) = 0 := h_mul.symm
    cases Nat.mul_eq_zero.mp hp2 with
    | inl h => exact h_2_pos h
    | inr h => exact h_P_pos h
  have h_vp_mul : padicValNat 2 (a (n - 1) * (n - 1).factorial) = padicValNat 2 (a (n - 1)) + padicValNat 2 (n - 1).factorial := padicValNat.mul h_a_pos h_fact_pos
  have h_vp_RHS : padicValNat 2 (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = padicValNat 2 (2 ^ (n - 2)) + padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := padicValNat.mul h_2_pos h_P_pos
  have h_vp_P : padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = 0 := padicValNat_P_two n hn2
  have h_vp_2 : padicValNat 2 (2 ^ (n - 2)) = n - 2 := padicValNat_two_pow (n - 2)
  have h_vp_fact : padicValNat 2 (n - 1).factorial = n - 1 - m := by
    have h1 : padicValNat 2 (n - 1).factorial = (n - 1) - (Nat.digits 2 (n - 1)).sum := by
      have h_sub : (2 - 1) * padicValNat 2 (n - 1).factorial = (n - 1) - (Nat.digits 2 (n - 1)).sum := sub_one_mul_padicValNat_factorial (n - 1)
      have h_sub2 : 2 - 1 = 1 := rfl
      rw [h_sub2, one_mul] at h_sub
      exact h_sub
    have h2 : (Nat.digits 2 (n - 1)).sum = m := by
      rw [hn1]
      exact digits_two_pow_sub_one m
    rw [h2] at h1
    exact h1
  have h_vp_a : padicValNat 2 (a (n - 1)) = m - 1 := by
    have h_eq1 : padicValNat 2 (a (n - 1)) + padicValNat 2 (n - 1).factorial = padicValNat 2 (2 ^ (n - 2)) + padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
      rw [← h_vp_mul, h_mul, h_vp_RHS]
    rw [h_vp_fact, h_vp_P, h_vp_2, add_zero] at h_eq1
    have : n ≥ m + 2 := by
      have : n = 2 ^ m := hn_eq
      omega
    omega
  have h_n_dvd_sum : 2 ^ m ∣ 2 ^ (n - 2) + a (n - 1) := by
    have : 2 ^ m ∣ a (n - 1) + 2 ^ (n - 2) := by
      rw [← hn_eq]
      exact h_dvd
    rw [add_comm] at this
    exact this
  have h_n_dvd_2 : 2 ^ m ∣ 2 ^ (n - 2) := by
    have hpow : m ≤ n - 2 := by
      have : n ≥ m + 2 := by
        have : n = 2 ^ m := hn_eq
        omega
      omega
    exact Nat.pow_dvd_pow 2 hpow
  have h_n_dvd_a : 2 ^ m ∣ a (n - 1) := (Nat.dvd_add_right h_n_dvd_2).mp h_n_dvd_sum
  have h_dvd_a : m ≤ padicValNat 2 (a (n - 1)) := (padicValNat_dvd_iff_le h_a_pos).mp h_n_dvd_a
  omega

-- Proof26.lean

open Nat BigOperators

lemma eq_two_pow_of_no_odd_prime_factor (n : ℕ) (hn0 : n > 0)
  (h_no_odd : ¬ ∃ q, q.Prime ∧ q > 2 ∧ q ∣ n) : ∃ m, n = 2 ^ m := by
  let k := padicValNat 2 n
  have h2 : 2 ^ k ∣ n := (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
  rcases h2 with ⟨c, hc⟩
  have hc_pos : c > 0 := by
    by_contra hc0
    have : c = 0 := by omega
    subst this
    have : n = 0 := by omega
    omega
  by_cases hc1 : c = 1
  · subst hc1
    use k
    rw [hc, mul_one]
  · have hc_neq_1 : c ≠ 1 := by omega
    have h_q : ∃ q, q.Prime ∧ q ∣ c := Nat.exists_prime_and_dvd hc_neq_1
    rcases h_q with ⟨q, hq_prime, hq_dvd⟩
    have hq_n : q ∣ n := by
      rw [hc]
      exact dvd_mul_of_dvd_right hq_dvd _
    by_cases hq2 : q = 2
    · subst hq2
      have h2_c : 2 ∣ c := hq_dvd
      rcases h2_c with ⟨d, hd⟩
      have hn_new : n = 2 ^ (k + 1) * d := by
        calc n = 2 ^ k * c := hc
          _ = 2 ^ k * (2 * d) := by rw [hd]
          _ = 2 ^ k * 2 * d := by ring
          _ = 2 ^ (k + 1) * d := by ring
      have h_dvd_n : 2 ^ (k + 1) ∣ n := ⟨d, hn_new⟩
      have hk_lt : k + 1 ≤ k := (padicValNat_dvd_iff_le (by omega)).mp h_dvd_n
      omega
    · have hq_gt2 : q > 2 := by
        have : q ≥ 2 := hq_prime.two_le
        omega
      have h_contra : ∃ q, q.Prime ∧ q > 2 ∧ q ∣ n := ⟨q, hq_prime, hq_gt2, hq_n⟩
      contradiction

lemma composite_contradiction (n : ℕ) (hn2 : n > 2) (hcomp : ¬ n.Prime)
  (h_dvd : n ∣ a (n - 1) + 2 ^ (n - 2)) : False := by
  have hc_neq_1 : n ≠ 1 := by omega
  have h_has_prime : ∃ p, p.Prime ∧ p ∣ n := Nat.exists_prime_and_dvd hc_neq_1
  rcases h_has_prime with ⟨p, hp_prime, hp_dvd⟩
  by_cases hodd : p > 2
  · exact odd_prime_factor_contradiction n p hn2 hcomp hp_prime hodd hp_dvd h_dvd
  · have hp_eq_2 : p = 2 := by
      have hp2 : p ≥ 2 := hp_prime.two_le
      omega
    subst hp_eq_2
    by_cases h_odd_prime : ∃ q, q.Prime ∧ q > 2 ∧ q ∣ n
    · rcases h_odd_prime with ⟨q, hq_prime, hq_odd, hq_dvd⟩
      exact odd_prime_factor_contradiction n q hn2 hcomp hq_prime hq_odd hq_dvd h_dvd
    · have h_pow2 : ∃ m, n = 2 ^ m := eq_two_pow_of_no_odd_prime_factor n (by omega) h_odd_prime
      rcases h_pow2 with ⟨m, hm_eq⟩
      exact power_of_two_contradiction n m hn2 hcomp hm_eq h_dvd

-- Proof27.lean

open Nat BigOperators

lemma P_mod_n_eq_one (n : ℕ) (hn_prime : n.Prime) (hn2 : n > 2)
  (h_dvd : n ∣ a (n - 1) + 2 ^ (n - 2)) :
  (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) = 1 := by
  haveI : Fact n.Prime := ⟨hn_prime⟩
  have h_mul : a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := a_mul_fact n hn2
  have h_mul_zmod : ((a (n - 1) * (n - 1).factorial : ℕ) : ZMod n) = (((2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n)) := by
    rw [h_mul]
  have h_wilson : ((n - 1).factorial : ZMod n) = -1 := ZMod.wilsons_lemma n
  have h_dvd_zmod : (a (n - 1) : ZMod n) + ((2 ^ (n - 2) : ℕ) : ZMod n) = 0 := by
    have h1 : ((a (n - 1) + 2 ^ (n - 2) : ℕ) : ZMod n) = 0 := by
      exact (CharP.cast_eq_zero_iff (ZMod n) n (a (n - 1) + 2 ^ (n - 2))).mpr h_dvd
    have h2 : ((a (n - 1) + 2 ^ (n - 2) : ℕ) : ZMod n) = (a (n - 1) : ZMod n) + ((2 ^ (n - 2) : ℕ) : ZMod n) := Nat.cast_add _ _
    rw [h2] at h1
    exact h1
  have h_a_eq : (a (n - 1) : ZMod n) = - ((2 ^ (n - 2) : ℕ) : ZMod n) := by
    calc (a (n - 1) : ZMod n) = (a (n - 1) : ZMod n) + ((2 ^ (n - 2) : ℕ) : ZMod n) - ((2 ^ (n - 2) : ℕ) : ZMod n) := by ring
      _ = 0 - ((2 ^ (n - 2) : ℕ) : ZMod n) := by rw [h_dvd_zmod]
      _ = - ((2 ^ (n - 2) : ℕ) : ZMod n) := by ring
  have h_RHS_zmod : (((2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n)) = ((2 ^ (n - 2) : ℕ) : ZMod n) * (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) := Nat.cast_mul _ _
  have h_LHS_zmod : ((a (n - 1) * (n - 1).factorial : ℕ) : ZMod n) = ((2 ^ (n - 2) : ℕ) : ZMod n) := by
    calc ((a (n - 1) * (n - 1).factorial : ℕ) : ZMod n) = (a (n - 1) : ZMod n) * ((n - 1).factorial : ZMod n) := Nat.cast_mul _ _
      _ = - ((2 ^ (n - 2) : ℕ) : ZMod n) * -1 := by rw [h_wilson, h_a_eq]
      _ = ((2 ^ (n - 2) : ℕ) : ZMod n) := by ring
  rw [h_LHS_zmod, h_RHS_zmod] at h_mul_zmod
  have h_inv : IsUnit ((2 ^ (n - 2) : ℕ) : ZMod n) := by
    have h2 : (2 : ZMod n) ≠ 0 := by
      intro h
      have : n ∣ 2 := (CharP.cast_eq_zero_iff (ZMod n) n 2).mp h
      have : n = 2 := (Nat.prime_dvd_prime_iff_eq hn_prime Nat.prime_two).mp this
      omega
    have h2_unit : IsUnit (2 : ZMod n) := isUnit_iff_ne_zero.mpr h2
    have h2_pow_unit : IsUnit ((2 : ZMod n) ^ (n - 2)) := IsUnit.pow (n - 2) h2_unit
    have h_pow_eq : ((2 ^ (n - 2) : ℕ) : ZMod n) = (2 : ZMod n) ^ (n - 2) := by push_cast; rfl
    rw [h_pow_eq]
    exact h2_pow_unit
  have h_cancel : ((2 ^ (n - 2) : ℕ) : ZMod n) * 1 = ((2 ^ (n - 2) : ℕ) : ZMod n) * (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) := by
    calc ((2 ^ (n - 2) : ℕ) : ZMod n) * 1 = ((2 ^ (n - 2) : ℕ) : ZMod n) := by ring
      _ = ((2 ^ (n - 2) : ℕ) : ZMod n) * (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) := h_mul_zmod
  have h_cancel2 : 1 = (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) := h_inv.mul_left_cancel h_cancel
  exact h_cancel2.symm

-- Proof28.lean

open Nat BigOperators

lemma is_primitive_root_of_P_mod_n_eq_one (n : ℕ) (hn_prime : n.Prime) (hn2 : n > 2)
  (hP : (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) = 1) :
  IsPrimitiveRoot (2 : ZMod n) (n - 1) := by
  haveI : Fact n.Prime := ⟨hn_prime⟩
  have h_unit : (2 : ZMod n) ≠ 0 := by
    intro h
    have : n ∣ 2 := (CharP.cast_eq_zero_iff (ZMod n) n 2).mp h
    have : n = 2 := (Nat.prime_dvd_prime_iff_eq hn_prime Nat.prime_two).mp this
    omega
  have h_order_dvd : orderOf (2 : ZMod n) ∣ n - 1 := ZMod.orderOf_dvd_card_sub_one h_unit
  by_contra h_not_prim
  rw [IsPrimitiveRoot.iff_orderOf] at h_not_prim
  have h_order_lt : orderOf (2 : ZMod n) < n - 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) h_order_dvd) h_not_prim
  let d : ℕ := orderOf (2 : ZMod n)
  have hd_pos : d ≥ 1 := by
    have hd_zero : d = 0 → n - 1 = 0 := by
      intro h
      have : 0 ∣ n - 1 := by
        rw [← h]
        exact h_order_dvd
      exact eq_zero_of_zero_dvd this
    omega
  have hd_le : d ≤ n - 2 := by omega
  have h_d_in : d ∈ Finset.Ico 1 (n - 1) := by
    rw [Finset.mem_Ico]
    exact ⟨hd_pos, h_order_lt⟩
  have h_dvd_prod : (2 ^ d - 1) ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
    exact Finset.dvd_prod_of_mem (fun k => 2 ^ k - 1) h_d_in
  have h_2d_mod : ((2 ^ d - 1 : ℕ) : ZMod n) = 0 := by
    have h_pow : (2 : ZMod n) ^ d = 1 := pow_orderOf_eq_one (2 : ZMod n)
    have h_pow_nat : ((2 ^ d : ℕ) : ZMod n) = 1 := by
      calc ((2 ^ d : ℕ) : ZMod n) = (2 : ZMod n) ^ d := by push_cast; rfl
        _ = 1 := h_pow
    have h_sub : 2 ^ d - 1 + 1 = 2 ^ d := by
      have hd_pos_pow : 2 ^ d ≥ 1 := Nat.one_le_pow d 2 (by omega)
      omega
    have h_sub_zmod : (((2 ^ d - 1 : ℕ) : ZMod n) + 1) = ((2 ^ d : ℕ) : ZMod n) := by
      calc (((2 ^ d - 1 : ℕ) : ZMod n) + 1) = (((2 ^ d - 1 : ℕ) : ZMod n) + (1 : ℕ) : ZMod n) := by push_cast; rfl
        _ = (((2 ^ d - 1 + 1 : ℕ) : ZMod n)) := by rw [Nat.cast_add]
        _ = ((2 ^ d : ℕ) : ZMod n) := by rw [h_sub]
    rw [h_pow_nat] at h_sub_zmod
    calc ((2 ^ d - 1 : ℕ) : ZMod n) = ((2 ^ d - 1 : ℕ) : ZMod n) + 1 - 1 := by ring
      _ = 1 - 1 := by rw [h_sub_zmod]
      _ = 0 := by ring
  have h_prod_zero : (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) = 0 := by
    rcases h_dvd_prod with ⟨c, hc⟩
    rw [hc, Nat.cast_mul, h_2d_mod, zero_mul]
  rw [hP] at h_prod_zero
  have : (1 : ZMod n) ≠ 0 := by
    exact one_ne_zero
  exact this h_prod_zero

-- Proof29.lean

open Nat BigOperators

lemma a091669_conjecture_primitive_root_proof (n : ℕ) (hn : n > 2) :
  n ∣ a (n - 1) + 2 ^ (n - 2) →
  n.Prime ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro h_dvd
  have hn_prime : n.Prime := by
    by_contra hcomp
    exact composite_contradiction n hn hcomp h_dvd
  have h_totient : Nat.totient n = n - 1 := Nat.totient_prime hn_prime
  rw [h_totient]
  have hP : (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) = 1 := P_mod_n_eq_one n hn_prime hn h_dvd
  exact ⟨hn_prime, is_primitive_root_of_P_mod_n_eq_one n hn_prime hn hP⟩


theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) :=
by exact a091669_conjecture_primitive_root_proof n hn

theorem a091669_conjecture_primitive_root.disproof : ¬ (type_of% @a091669_conjecture_primitive_root) := by
  sorry
