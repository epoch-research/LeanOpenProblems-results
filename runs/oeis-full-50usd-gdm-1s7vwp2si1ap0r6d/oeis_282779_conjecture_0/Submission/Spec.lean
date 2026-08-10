import FormalConjectures.Util.ProblemImports

open Nat Set Classical

/--
A282779: Period of cubes mod $n$.
The $n$-th term $a(n)$ is the smallest positive integer $T$ such that $\forall k \in \mathbb{N}$, $(k+T)^3 \equiv k^3 \pmod n$.
-/
noncomputable def A282779 (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Handle the non-sequence index n=0
  else
    -- sInf computes the infimum of the set, which is the minimum since ℕ is well-ordered.
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ 3 % n = k ^ 3 % n }

/--
The length of the minimal positive period of the sequence $k^p \pmod n$.
$a_p(n) = \min \{ T \in \mathbb{N}^+ \mid \forall k \in \mathbb{N}, (k+T)^p \equiv k^p \pmod n \}$.
-/
noncomputable def period_of_power_mod (p n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n }

/--
oeis_282779_conjecture_0: Conjecture: let a_p(n) be the length of the period of the sequence k^p mod n where p is a prime,
then a_p(n) = n/p if n == 0 (mod p^2) else a_p(n) = n.
-/
def S (p n : ℕ) : Set ℕ := { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n }

theorem test_mod_eq (k n p : ℕ) : (k + n) ^ p % n = k ^ p % n := by
  have h1 : (k + n) % n = k % n := by
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  have h2 : (k + n) ^ p % n = k ^ p % n := Nat.ModEq.pow p h1
  exact h2

theorem period_of_power_mod_def (p n : ℕ) (hn : n > 0) :
    period_of_power_mod p n = sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n } := by
  unfold period_of_power_mod
  have hne : n ≠ 0 := by omega
  rw [if_neg hne]

theorem sum_split (p : ℕ) (hp : p ≥ 2) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (p + 1), f i = f 0 + f 1 + (∑ i ∈ Finset.range (p - 2), f (i + 2)) + f p := by
  rw [Finset.sum_range_succ f p]
  have hp1 : p = (p - 1) + 1 := by omega
  have hp2 : p - 1 = (p - 2) + 1 := by omega
  nth_rw 1 [hp1]
  rw [Finset.sum_range_succ' f (p - 1)]
  nth_rw 1 [hp2]
  rw [Finset.sum_range_succ' (fun i => f (i + 1)) (p - 2)]
  simp only [Nat.reduceAdd]
  ac_rfl

theorem T_add_one_pow (p T : ℕ) :
    (T + 1)^p = ∑ i ∈ Finset.range (p + 1), p.choose i * T^i := by
  have h := add_pow T 1 p
  simp only [one_pow, mul_one] at h
  rw [h]
  congr 1
  ext i
  simp only [Nat.cast_id]
  ring

theorem T_add_one_pow_split (p T : ℕ) (hp : p ≥ 2) :
    (T + 1)^p = 1 + p * T + (∑ i ∈ Finset.range (p - 2), p.choose (i + 2) * T^(i+2)) + T^p := by
  rw [T_add_one_pow p T]
  rw [sum_split p hp (fun i => p.choose i * T^i)]
  simp only [Nat.choose_zero_right, pow_zero, mul_one, Nat.choose_one_right, pow_one, Nat.choose_self, one_mul]

theorem dvd_choose_of_range (p i : ℕ) (hp : Nat.Prime p) (hi : i ∈ Finset.range (p - 2)) :
    p ∣ p.choose (i + 2) := by
  have hi_lt : i < p - 2 := Finset.mem_range.mp hi
  have ha : i + 2 < p := by omega
  have hab : p - (i + 2) < p := by omega
  have h_le : p ≤ p := by rfl
  exact Nat.Prime.dvd_choose hp ha hab h_le

theorem h_sum_test (p T : ℕ) (hp : Nat.Prime p) :
    (∑ i ∈ Finset.range (p - 2), p.choose (i + 2) * T^(i+2)) = p * T * (∑ i ∈ Finset.range (p - 2), (p.choose (i + 2) / p) * T^(i+1)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h_dvd : p ∣ p.choose (i + 2) := dvd_choose_of_range p i hp hi
  have h_cancel : p * (p.choose (i + 2) / p) = p.choose (i + 2) := Nat.mul_div_cancel' h_dvd
  have h_pow : T^(i+2) = T * T^(i+1) := by
    have : i + 2 = 1 + (i + 1) := by omega
    rw [this, pow_add, pow_one]
  rw [h_pow]
  nth_rw 1 [← h_cancel]
  ring

theorem mod_eq_cancel (a b n : ℕ) (h : (a + b) % n = a % n) : b % n = 0 := by
  have h1 : a ≡ a [MOD n] := rfl
  have h2 : a + b ≡ a + 0 [MOD n] := by
    rw [add_zero]
    exact h
  exact Nat.ModEq.add_left_cancel h1 h2

theorem T_pow_mod_zero' (p n T : ℕ) (hp : Nat.Prime p) (hT : T ∈ S p n) : T^p % n = 0 := by
  have hT2 := hT.2 0
  have hz : 0 + T = T := Nat.zero_add T
  rw [hz] at hT2
  have hp_pos : p > 0 := hp.pos
  have hz2 : 0 ^ p = 0 := Nat.zero_pow hp_pos
  rw [hz2, Nat.zero_mod] at hT2
  exact hT2

theorem p_T_U_mod_zero (p n T : ℕ) (hp : Nat.Prime p) (hT : T ∈ S p n) :
    let U := 1 + ∑ i ∈ Finset.range (p - 2), (p.choose (i + 2) / p) * T^(i+1)
    (p * T * U) % n = 0 := by
  intro U
  have hT1 := hT.2 1
  have h_add : 1 + T = T + 1 := by ring
  rw [h_add] at hT1
  have hp_pos : p > 0 := hp.pos
  have hz1 : 1 ^ p = 1 := Nat.one_pow p
  rw [hz1] at hT1
  have hp2 : p ≥ 2 := hp.two_le
  have h_eq : (T + 1)^p = 1 + T^p + p * T * U := by
    rw [T_add_one_pow_split p T hp2]
    rw [h_sum_test p T hp]
    ring
  rw [h_eq] at hT1
  have h_tp : T^p % n = 0 := T_pow_mod_zero' p n T hp hT
  have h_eq2 : (1 + T^p + p * T * U) % n = (1 + p * T * U) % n := by
    have h_assoc : 1 + T^p + p * T * U = (1 + p * T * U) + T^p := by ring
    rw [h_assoc]
    rw [Nat.add_mod, h_tp, Nat.add_zero, Nat.mod_mod]
  rw [h_eq2] at hT1
  have h_eq3 : (1 + p * T * U) % n = (1 + p * T * U) % n := rfl
  exact mod_eq_cancel 1 (p * T * U) n hT1

theorem coprime_n_U (p n T : ℕ) (hp : Nat.Prime p) (hT : T ∈ S p n) :
    let U := 1 + ∑ i ∈ Finset.range (p - 2), (p.choose (i + 2) / p) * T^(i+1)
    Nat.Coprime n U := by
  intro U
  by_contra hc
  rw [Nat.coprime_iff_gcd_eq_one] at hc
  rcases Nat.exists_prime_and_dvd hc with ⟨q, hq_prime, hq_dvd⟩
  have hq_n : q ∣ n := dvd_trans hq_dvd (Nat.gcd_dvd_left n U)
  have hq_U : q ∣ U := dvd_trans hq_dvd (Nat.gcd_dvd_right n U)
  have h_tp : T^p % n = 0 := T_pow_mod_zero' p n T hp hT
  have h_n_dvd_tp : n ∣ T^p := Nat.dvd_of_mod_eq_zero h_tp
  have hq_tp : q ∣ T^p := dvd_trans hq_n h_n_dvd_tp
  have hq_T : q ∣ T := Nat.Prime.dvd_of_dvd_pow hq_prime hq_tp
  have hq_sum : q ∣ ∑ i ∈ Finset.range (p - 2), (p.choose (i + 2) / p) * T^(i+1) := by
    apply Finset.dvd_sum
    intro i hi
    have h_pow : T^(i+1) = T * T^i := by
      have : i + 1 = 1 + i := by omega
      rw [this, pow_add, pow_one]
    rw [h_pow]
    rw [show (p.choose (i + 2) / p) * (T * T^i) = ((p.choose (i + 2) / p) * T^i) * T by ring]
    exact dvd_mul_of_dvd_right hq_T _
  have h_one : q ∣ 1 := by
    have h_sub : 1 = (1 + ∑ i ∈ Finset.range (p - 2), (p.choose (i + 2) / p) * T^(i+1)) - ∑ i ∈ Finset.range (p - 2), (p.choose (i + 2) / p) * T^(i+1) := by omega
    nth_rw 1 [h_sub]
    exact Nat.dvd_sub hq_U hq_sum
  have hq_le : q ≤ 1 := Nat.le_of_dvd (by omega) h_one
  have hq_ge : q ≥ 2 := hq_prime.two_le
  omega

theorem n_dvd_p_T (p n T : ℕ) (hp : Nat.Prime p) (hT : T ∈ S p n) : n ∣ p * T := by
  let U := 1 + ∑ i ∈ Finset.range (p - 2), (p.choose (i + 2) / p) * T^(i+1)
  have h_coprime : n.Coprime U := coprime_n_U p n T hp hT
  have h_mod : (p * T * U) % n = 0 := p_T_U_mod_zero p n T hp hT
  have h_dvd : n ∣ p * T * U := Nat.dvd_of_mod_eq_zero h_mod
  exact Nat.Coprime.dvd_of_dvd_mul_right h_coprime h_dvd

theorem Case_B_dvd (p n T : ℕ) (hp : Nat.Prime p) (h_np2 : ¬ p^2 ∣ n) (hT : T ∈ S p n) : n ∣ T := by
  have h_dvd_pt : n ∣ p * T := n_dvd_p_T p n T hp hT
  by_cases h_pn : p ∣ n
  · have h_div_mul : p * (n / p) = n := Nat.mul_div_cancel' h_pn
    have h_p_pos : p > 0 := hp.pos
    let d := n / p
    have h_nd : n = p * d := h_div_mul.symm
    have h_np2_rew : ¬ p * p ∣ p * d := by
      rw [h_nd] at h_np2
      have hp2_eq : p^2 = p * p := by ring
      rw [hp2_eq] at h_np2
      exact h_np2
    have h_p_not_dvd_d : ¬ p ∣ d := by
      intro h_pd
      apply h_np2_rew
      exact Nat.mul_dvd_mul_left p h_pd
    have h_coprime : d.Coprime p := by
      have h_cop_pd := (Nat.Prime.coprime_iff_not_dvd hp).mpr h_p_not_dvd_d
      exact h_cop_pd.symm
    rw [h_nd] at h_dvd_pt
    have h_d_dvd_T : d ∣ T := (Nat.mul_dvd_mul_iff_left h_p_pos).mp h_dvd_pt
    have h_tp : T^p % n = 0 := T_pow_mod_zero' p n T hp hT
    have h_n_dvd_tp : n ∣ T^p := Nat.dvd_of_mod_eq_zero h_tp
    have h_p_dvd_n : p ∣ n := h_pn
    have h_p_dvd_tp : p ∣ T^p := dvd_trans h_p_dvd_n h_n_dvd_tp
    have h_p_dvd_T : p ∣ T := Nat.Prime.dvd_of_dvd_pow hp h_p_dvd_tp
    have h_dp_dvd_T : d * p ∣ T := Nat.Coprime.mul_dvd_of_dvd_of_dvd h_coprime h_d_dvd_T h_p_dvd_T
    have h_dp_eq : d * p = n := by
      rw [mul_comm]
      exact h_nd.symm
    rw [h_dp_eq] at h_dp_dvd_T
    exact h_dp_dvd_T
  · have h_coprime : n.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h_pn).symm
    exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_dvd_pt

theorem Case_A_le (p n T : ℕ) (hp : Nat.Prime p) (h_np2 : p^2 ∣ n) (hT : T ∈ S p n) : n / p ≤ T := by
  have hp2_eq : p^2 = p * p := by ring
  rw [hp2_eq] at h_np2
  have h_p_dvd_n : p ∣ n := dvd_trans (dvd_mul_right p p) h_np2
  have h_div_mul : p * (n / p) = n := Nat.mul_div_cancel' h_p_dvd_n
  have h_p_pos : p > 0 := hp.pos
  have h_dvd_pt : n ∣ p * T := n_dvd_p_T p n T hp hT
  rw [← h_div_mul] at h_dvd_pt
  have h_nd_dvd_T : n / p ∣ T := (Nat.mul_dvd_mul_iff_left h_p_pos).mp h_dvd_pt
  have h_T_pos : T > 0 := hT.1
  exact Nat.le_of_dvd h_T_pos h_nd_dvd_T

theorem sum_split2 (p : ℕ) (hp : p ≥ 1) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (p + 1), f i = f 0 + f 1 + ∑ i ∈ Finset.range (p - 1), f (i + 2) := by
  rw [Finset.sum_range_succ' f p]
  have hp1 : p = (p - 1) + 1 := by omega
  nth_rw 1 [hp1]
  rw [Finset.sum_range_succ' (fun i => f (i + 1)) (p - 1)]
  simp only [Nat.reduceAdd]
  ac_rfl

theorem Case_A_in (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) (h_np2 : p^2 ∣ n) :
    let T := n / p
    T ∈ S p n := by
  intro T
  have hp2_eq : p^2 = p * p := by ring
  have h_np2' : p * p ∣ n := by
    rw [hp2_eq] at h_np2
    exact h_np2
  have h_p_dvd_n : p ∣ n := dvd_trans (dvd_mul_right p p) h_np2'
  have h_p_pos : p > 0 := hp.pos
  have h_div_mul : p * (n / p) = n := Nat.mul_div_cancel' h_p_dvd_n
  have h_nd_eq : p * T = n := h_div_mul
  have hp2_le_n : p * p ≤ n := Nat.le_of_dvd hn h_np2'
  have hp_ge : p ≥ 2 := hp.two_le
  have hp_le_T : p ≤ T := Nat.le_of_mul_le_mul_left (by rw [h_nd_eq]; exact hp2_le_n) h_p_pos
  have h_T_pos : T > 0 := by omega
  refine ⟨h_T_pos, fun k => ?_⟩
  have h_add : k + T = T + k := add_comm k T
  rw [h_add]
  have h_pow := add_pow T k p
  simp only [Nat.cast_id] at h_pow
  rw [h_pow]
  let f := fun m => T^m * k^(p-m) * p.choose m
  have h_split : ∑ m ∈ Finset.range (p + 1), T^m * k^(p-m) * p.choose m = f 0 + f 1 + ∑ i ∈ Finset.range (p - 1), f (i + 2) := by
    exact sum_split2 p (by omega) f
  rw [h_split]
  have h_f0 : f 0 = k^p := by
    dsimp [f]
    simp
  have h_f1 : f 1 = n * k^(p-1) := by
    dsimp [f]
    rw [pow_one, Nat.choose_one_right]
    have : T * k^(p-1) * p = (p * T) * k^(p-1) := by ring
    rw [this, h_nd_eq]
  rw [h_f0, h_f1]
  have h_mod_zero : (n * k^(p-1) + ∑ i ∈ Finset.range (p - 1), f (i + 2)) % n = 0 := by
    rw [Nat.add_mod]
    have h1 : n * k^(p-1) % n = 0 := by
      rw [Nat.mul_mod_right]
    rw [h1, Nat.zero_add, Nat.mod_mod]
    have h_dvd_sum : n ∣ ∑ i ∈ Finset.range (p - 1), f (i + 2) := by
      apply Finset.dvd_sum
      intro i hi
      dsimp [f]
      have h_p_dvd_T : p ∣ T := by
        have : p * p ∣ p * T := by
          rw [h_nd_eq]
          exact h_np2'
        exact (Nat.mul_dvd_mul_iff_left h_p_pos).mp this
      rcases h_p_dvd_T with ⟨e, he⟩
      have h_T_pow : T^(i+2) = n * (e * T^i) := by
        have : i + 2 = 2 + i := by omega
        rw [this, pow_add]
        have h_T2 : T^2 = (p * T) * e := by
          rw [he]
          ring
        rw [h_T2, h_nd_eq]
        ring
      have h_dvd_T_pow : n ∣ T^(i+2) := by
        rw [h_T_pow]
        exact dvd_mul_right n _
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h_dvd_T_pow _) _
    exact Nat.mod_eq_zero_of_dvd h_dvd_sum
  have h_assoc : k^p + n * k^(p-1) + ∑ i ∈ Finset.range (p - 1), f (i + 2) = k^p + (n * k^(p-1) + ∑ i ∈ Finset.range (p - 1), f (i + 2)) := by ring
  rw [h_assoc]
  rw [Nat.add_mod, h_mod_zero, Nat.add_zero, Nat.mod_mod]

theorem oeis_282779_conjecture_0 (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) :
    period_of_power_mod p n = if p ^ 2 ∣ n then n / p else n := by
  rw [period_of_power_mod_def p n hn]
  have hS : { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n } = S p n := rfl
  rw [hS]
  by_cases h_np2 : p^2 ∣ n
  · rw [if_pos h_np2]
    have h_in : n / p ∈ S p n := Case_A_in p n hp hn h_np2
    have h_le : sInf (S p n) ≤ n / p := Nat.sInf_le h_in
    have h_ge : n / p ≤ sInf (S p n) := by
      have h_nonempty : (S p n).Nonempty := ⟨n / p, h_in⟩
      have h_mem : sInf (S p n) ∈ S p n := Nat.sInf_mem h_nonempty
      exact Case_A_le p n (sInf (S p n)) hp h_np2 h_mem
    omega
  · rw [if_neg h_np2]
    have h_n_in : n ∈ S p n := by
      refine ⟨hn, fun k => test_mod_eq k n p⟩
    have h_le : sInf (S p n) ≤ n := Nat.sInf_le h_n_in
    have h_ge : n ≤ sInf (S p n) := by
      have h_nonempty : (S p n).Nonempty := ⟨n, h_n_in⟩
      have h_mem : sInf (S p n) ∈ S p n := Nat.sInf_mem h_nonempty
      have h_dvd : n ∣ sInf (S p n) := Case_B_dvd p n (sInf (S p n)) hp h_np2 h_mem
      have h_pos : sInf (S p n) > 0 := h_mem.1
      exact Nat.le_of_dvd h_pos h_dvd
    omega


