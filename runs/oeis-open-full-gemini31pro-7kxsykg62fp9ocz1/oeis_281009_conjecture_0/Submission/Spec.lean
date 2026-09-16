import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A281009: Number of odd divisors of $n$ minus the number of middle divisors of $n$.
A divisor $d$ of $n$ is a "middle divisor" if $\sqrt{n/2} \le d < \sqrt{2n}$,
which is equivalent to $n \le 2d^2$ and $d^2 < 2n$ for $d \in \mathbb{N}$.
-/
def A281009 (n : ℕ) : ℤ :=
  if h : n = 0 then
    0
  else
    let odd_div_count : ℕ := (divisors n).filter (fun d => d % 2 = 1) |>.card
    let middle_div_condition (d : ℕ) : Prop := n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n
    let middle_div_count : ℕ := (divisors n).filter middle_div_condition |>.card
    (odd_div_count : ℤ) - (middle_div_count : ℤ)

def odd_part (d : ℕ) : ℕ := d / 2^(padicValNat 2 d)
lemma odd_part_mul (d : ℕ) : 2^(padicValNat 2 d) * odd_part d = d := by
  if h : d = 0 then simp [h, odd_part] else exact Nat.mul_div_cancel' pow_padicValNat_dvd
lemma odd_part_odd (d : ℕ) (hd : d ≠ 0) : odd_part d % 2 = 1 := by
  have hp : Fact (Nat.Prime 2) := fact_iff.mpr (by decide)
  have h_ndvd : ¬ (2^(padicValNat 2 d + 1) ∣ d) := by
    rw [padicValNat_dvd_iff]
    push_neg
    exact ⟨hd, Nat.lt_succ_self _⟩
  by_contra h_even
  have h_zero : odd_part d % 2 = 0 := by omega
  have h_dvd : 2 ∣ odd_part d := dvd_of_mod_eq_zero h_zero
  rcases h_dvd with ⟨c, hc⟩
  have h_d : d = 2^(padicValNat 2 d + 1) * c := by
    calc d = 2^(padicValNat 2 d) * odd_part d := (odd_part_mul d).symm
         _ = 2^(padicValNat 2 d) * (c * 2) := by rw [hc]; ring
         _ = 2^(padicValNat 2 d + 1) * c := by rw [pow_succ]; ring
  have h_contra : 2^(padicValNat 2 d + 1) ∣ d := ⟨c, h_d⟩
  exact h_ndvd h_contra
lemma odd_part_dvd_self (d : ℕ) : odd_part d ∣ d := by
  use 2^(padicValNat 2 d)
  rw [mul_comm]
  exact (odd_part_mul d).symm
lemma odd_part_dvd (d n : ℕ) (h : d ∣ n) : odd_part d ∣ n := dvd_trans (odd_part_dvd_self d) h

lemma two_pow_inj (x y : ℕ) (h : 2^x = 2^y) : x = y := by
  have hp : Fact (Nat.Prime 2) := fact_iff.mpr (by decide)
  have h1 : padicValNat 2 (2^x) = x * padicValNat 2 2 := padicValNat.pow x (by decide)
  have h2 : padicValNat 2 (2^y) = y * padicValNat 2 2 := padicValNat.pow y (by decide)
  rw [h] at h1
  rw [padicValNat_self, mul_one] at h1 h2
  exact h1.symm.trans h2

lemma padic_mul_odd (n u : ℕ) (hn : n ≠ 0) (hu : u ∣ n) (hu_odd : u % 2 = 1) :
    padicValNat 2 (n / u) = padicValNat 2 n := by
  have hp : Fact (Nat.Prime 2) := fact_iff.mpr (by decide)
  have hu_ne : u ≠ 0 := by rintro rfl; contradiction
  have hnu_ne : n / u ≠ 0 := by rintro h; exact hn (Nat.eq_zero_of_dvd_of_div_eq_zero hu h)
  have h_eq : n = u * (n / u) := (Nat.mul_div_cancel' hu).symm
  have h_val := padicValNat.mul hu_ne hnu_ne (p := 2)
  have h_u_val : padicValNat 2 u = 0 := by
    by_contra h_pos
    have hdvd : 2^1 ∣ u := pow_dvd_of_le_of_pow_dvd (Nat.pos_of_ne_zero h_pos) pow_padicValNat_dvd
    have : u % 2 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using hdvd)
    omega
  rw [← h_eq] at h_val
  rw [h_u_val, zero_add] at h_val
  exact h_val.symm

lemma odd_part_pow_two_mul (a u : ℕ) (hu_odd : u % 2 = 1) : odd_part (2^a * u) = u := by
  have hp : Fact (Nat.Prime 2) := fact_iff.mpr (by decide)
  have hu_ne : u ≠ 0 := by rintro rfl; contradiction
  have h_pow_ne : 2^a ≠ 0 := by positivity
  have h_val1 : padicValNat 2 (2^a * u) = padicValNat 2 (2^a) + padicValNat 2 u := padicValNat.mul h_pow_ne hu_ne (p := 2)
  have h_u_val : padicValNat 2 u = 0 := by
    by_contra h_pos
    have hdvd : 2^1 ∣ u := pow_dvd_of_le_of_pow_dvd (Nat.pos_of_ne_zero h_pos) pow_padicValNat_dvd
    have : u % 2 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using hdvd)
    omega
  have ha_ne : 2 ≠ 0 := by decide
  have h_pow_val : padicValNat 2 (2^a) = a * padicValNat 2 2 := padicValNat.pow a ha_ne
  rw [padicValNat_self, mul_one] at h_pow_val
  rw [h_u_val, h_pow_val, add_zero] at h_val1
  rw [odd_part, h_val1, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h_pow_ne)]

lemma padic_le_padic (d n : ℕ) (hd : d ∣ n) (hn : n ≠ 0) : padicValNat 2 d ≤ padicValNat 2 n := by
  have hp : Fact (Nat.Prime 2) := fact_iff.mpr (by decide)
  have h_dvd : 2^(padicValNat 2 d) ∣ n := dvd_trans pow_padicValNat_dvd hd
  have h_iff := padicValNat_dvd_iff (padicValNat 2 d) n (p := 2)
  rw [iff_true_left h_dvd] at h_iff
  exact h_iff.resolve_left hn

def O (n : ℕ) : Finset ℕ := (divisors n).filter (fun d => d % 2 = 1)
def M (n : ℕ) : Finset ℕ := (divisors n).filter (fun d => n ≤ 2 * d^2 ∧ d^2 < 2 * n)
def chain_M (n u : ℕ) : ℕ := ((range (padicValNat 2 n + 1)).filter (fun k => n ≤ 2 * (2^k * u)^2 ∧ 2 * (2^k * u)^2 < 4 * n)).card

lemma sum_chain_M (n : ℕ) (hn : n ≠ 0) : ∑ u ∈ O n, chain_M n u = (M n).card := by
  have H : Set.MapsTo odd_part (M n) (O n) := by
    intro d hd
    rw [mem_coe, M, mem_filter, mem_divisors] at hd
    rcases hd with ⟨⟨hd_dvd, _⟩, _⟩
    have h_d_ne : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hd_dvd)
    rw [mem_coe, O, mem_filter, mem_divisors]
    exact ⟨⟨odd_part_dvd d n hd_dvd, hn⟩, odd_part_odd d h_d_ne⟩
  have h_sum := Finset.card_eq_sum_card_fiberwise H
  rw [h_sum]
  apply sum_congr rfl
  intro u hu
  rw [chain_M]
  have h_u_ne : u ≠ 0 := by
    rw [O, mem_filter, mem_divisors] at hu
    rcases hu with ⟨⟨_, hn_ne⟩, _⟩
    rintro rfl
    omega
  have h_u_odd : u % 2 = 1 := by
    rw [O, mem_filter, mem_divisors] at hu
    exact hu.2
  have h_u_dvd : u ∣ n := by
    rw [O, mem_filter, mem_divisors] at hu
    exact hu.1.1
  let s := (range (padicValNat 2 n + 1)).filter (fun k => n ≤ 2 * (2^k * u)^2 ∧ 2 * (2^k * u)^2 < 4 * n)
  let f := fun k => 2^k * u
  have h_inj : Function.Injective f := by
    intro x y hxy
    have h_eq : 2^x = 2^y := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h_u_ne) hxy
    exact two_pow_inj x y h_eq
  have h_card := Finset.card_image_of_injective s h_inj
  rw [← h_card]
  congr 1
  ext d
  rw [mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [mem_filter, mem_range] at hk
    rcases hk with ⟨hk_lt, hk_mid⟩
    rw [mem_filter, M, mem_filter, mem_divisors]
    have h_odd_part : odd_part (2^k * u) = u := odd_part_pow_two_mul k u h_u_odd
    have h_dvd : 2^k * u ∣ n := by
      have hk_le : k ≤ padicValNat 2 n := Nat.lt_succ_iff.mp hk_lt
      have hp : Fact (Nat.Prime 2) := fact_iff.mpr (by decide)
      have h_padic_eq : padicValNat 2 (n / u) = padicValNat 2 n := padic_mul_odd n u hn h_u_dvd h_u_odd
      rw [← h_padic_eq] at hk_le
      have hdvd1 : 2^k ∣ n / u := by
        have : 2^k ∣ 2^(padicValNat 2 (n / u)) := pow_dvd_of_le_of_pow_dvd hk_le (dvd_refl _)
        exact dvd_trans this pow_padicValNat_dvd
      have h_n_eq : n = (n / u) * u := (Nat.div_mul_cancel h_u_dvd).symm
      rw [h_n_eq]
      exact mul_dvd_mul hdvd1 (dvd_refl u)
    have hd_mid_M : n ≤ 2 * (2^k * u)^2 ∧ (2^k * u)^2 < 2 * n := by omega
    exact ⟨⟨⟨h_dvd, hn⟩, hd_mid_M⟩, h_odd_part⟩
  · intro hd
    rw [mem_filter, M, mem_filter, mem_divisors] at hd
    rcases hd with ⟨⟨⟨hd_dvd, _⟩, hd_mid⟩, hd_odd⟩
    use padicValNat 2 d
    rw [mem_filter, mem_range]
    have hd_ne : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hd_dvd)
    have hd_eq : d = 2^(padicValNat 2 d) * u := by
      calc d = 2^(padicValNat 2 d) * odd_part d := (odd_part_mul d).symm
           _ = 2^(padicValNat 2 d) * u := by rw [hd_odd]
    have hk_lt : padicValNat 2 d < padicValNat 2 n + 1 := by
      have h_le := padic_le_padic d n hd_dvd hn
      exact Nat.lt_succ_iff.mpr h_le
    have hk_mid : n ≤ 2 * (2^(padicValNat 2 d) * u)^2 ∧ 2 * (2^(padicValNat 2 d) * u)^2 < 4 * n := by
      rw [← hd_eq]
      omega
    exact ⟨⟨hk_lt, hk_mid⟩, hd_eq.symm⟩

lemma involution_O (n : ℕ) (hn : n ≠ 0) :
    ∀ u ∈ O n, odd_part (n / u) ∈ O n ∧ odd_part (n / odd_part (n / u)) = u := by
  intro u hu
  rw [O, mem_filter, mem_divisors] at hu
  rcases hu with ⟨⟨hu_dvd, _⟩, hu_odd⟩
  have hu_ne : u ≠ 0 := by rintro rfl; contradiction
  have hnu_ne : n / u ≠ 0 := by rintro h; exact hn (Nat.eq_zero_of_dvd_of_div_eq_zero hu_dvd h)
  have h_v_dvd : odd_part (n / u) ∣ n := odd_part_dvd _ _ (Nat.div_dvd_of_dvd hu_dvd)
  have h_v_odd : odd_part (n / u) % 2 = 1 := odd_part_odd _ hnu_ne
  have h_v_in_O : odd_part (n / u) ∈ O n := by
    rw [O, mem_filter, mem_divisors]
    exact ⟨⟨h_v_dvd, hn⟩, h_v_odd⟩
  refine ⟨h_v_in_O, ?_⟩
  let a := padicValNat 2 n
  let v := odd_part (n / u)
  have h_nu : n / u = 2^a * v := by
    calc n / u = 2^(padicValNat 2 (n / u)) * v := (odd_part_mul (n / u)).symm
         _ = 2^a * v := by rw [padic_mul_odd n u hn hu_dvd hu_odd]
  have h_n_eq : n = (2^a * u) * v := by
    calc n = (n / u) * u := (Nat.div_mul_cancel hu_dvd).symm
         _ = (2^a * v) * u := by rw [h_nu]
         _ = (2^a * u) * v := by ring
  have h_v_ne : v ≠ 0 := by
    intro h_v_zero
    have : n / u = 0 := by
      calc n / u = 2^a * v := h_nu
           _ = 2^a * 0 := by rw [h_v_zero]
           _ = 0 := by ring
    exact hnu_ne this
  have h_nv : n / v = 2^a * u := by
    have : n / v = (2^a * u) * v / v := by congr 1
    rw [this, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero h_v_ne)]
  have h_odd_part : odd_part (n / v) = u := by
    rw [h_nv]
    exact odd_part_pow_two_mul a u hu_odd
  exact h_odd_part

lemma odd_sq_ne_even (u n : ℕ) (hn : n ≠ 0) (hu_odd : u % 2 = 1) : u^2 ≠ 2 * n := by
  intro h
  have hp : Fact (Nat.Prime 2) := fact_iff.mpr (by decide)
  have h1 : padicValNat 2 (u^2) = 0 := by
    have : u^2 % 2 = 1 := by
      calc u^2 % 2 = (u * u) % 2 := by rw [sq]
           _ = ((u % 2) * (u % 2)) % 2 := by rw [Nat.mul_mod]
           _ = (1 * 1) % 2 := by rw [hu_odd]
           _ = 1 := by decide
    by_contra h_pos
    have hdvd : 2^1 ∣ u^2 := pow_dvd_of_le_of_pow_dvd (Nat.pos_of_ne_zero h_pos) pow_padicValNat_dvd
    have : u^2 % 2 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using hdvd)
    omega
  have h2 : padicValNat 2 (2 * n) = padicValNat 2 2 + padicValNat 2 n := by
    exact padicValNat.mul (by decide) hn (p := 2)
  have h3 : padicValNat 2 2 = 1 := padicValNat_self
  rw [h3] at h2
  rw [h] at h1
  omega

lemma u_pow_two_mul (u k : ℕ) : 2 * (2^k * u)^2 = 2 * 4^k * u^2 := by
  calc 2 * (2^k * u)^2 = 2 * ((2^k)^2 * u^2) := by rw [mul_pow]
       _ = 2 * (2^k)^2 * u^2 := by rw [mul_assoc]
       _ = 2 * (2^2)^k * u^2 := by rw [← pow_mul, mul_comm k 2, pow_mul]
       _ = 2 * 4^k * u^2 := by rfl

lemma two_mul_four_pow (a : ℕ) : 2 * 4^a = 2^(a + 1) * 2^a := by
  calc 2 * 4^a = 2 * (2^2)^a := by rfl
       _ = 2 * 2^(2 * a) := by rw [← pow_mul]
       _ = 2^(2 * a + 1) := by rw [pow_succ']
       _ = 2^(a + 1 + a) := by congr 1; omega
       _ = 2^(a + 1) * 2^a := by rw [pow_add]

lemma le_pow_four (n : ℕ) : n ≤ 4^n := by
  induction n with
  | zero => exact Nat.zero_le 1
  | succ n ih =>
    have : 1 ≤ 4^n := Nat.one_le_pow _ _ (by decide)
    calc n + 1 ≤ 4^n + 1 := Nat.add_le_add_right ih 1
         _ ≤ 4^n + 4^n + 4^n + 4^n := by omega
         _ = 4^(n + 1) := by ring

lemma exists_power_four_in_interval (n X : ℕ) (hX0 : 0 < X) (hX : X < 4 * n) :
    ∃ k : ℕ, n ≤ 4^k * X ∧ 4^k * X < 4 * n := by
  have h_ex : ∃ j, n ≤ 4^j * X := by
    use n
    have h1 : n ≤ n * X := Nat.le_mul_of_pos_right _ hX0
    have h2 : n ≤ 4^n := le_pow_four n
    have h3 : n * X ≤ 4^n * X := Nat.mul_le_mul_right X h2
    omega
  let k := Nat.find h_ex
  have hk : n ≤ 4^k * X := Nat.find_spec h_ex
  use k
  refine ⟨hk, ?_⟩
  have hk0 : k = 0 ∨ 0 < k := Nat.eq_zero_or_pos k
  cases hk0 with
  | inl h0 =>
    rw [h0]
    simp only [pow_zero, one_mul]
    exact hX
  | inr hpos =>
    have hk' : ¬ (n ≤ 4^(k - 1) * X) := Nat.find_min h_ex (Nat.pred_lt hpos.ne.symm)
    push_neg at hk'
    have h_eq : 4^k * X = 4 * (4^(k - 1) * X) := by
      calc 4^k * X = 4^(k - 1 + 1) * X := by congr 2; omega
           _ = (4^(k - 1) * 4) * X := by rw [pow_succ]
           _ = 4 * (4^(k - 1) * X) := by ring
    rw [h_eq]
    exact Nat.mul_lt_mul_of_pos_left hk' (by decide)

lemma lt_of_mul_lt_mul_right_of_pos {a b c : ℕ} (h : a * c < b * c) : a < b := by
  cases c with
  | zero => simp at h
  | succ c => exact Nat.lt_of_mul_lt_mul_right h

lemma contra_helper (a u v : ℕ) (h_pos : 0 < 2^a * u) (h : 2 * 4^(a+1) * u^2 < 4 * (2^a * u * v)) : 2 * (2^a * u * v) < v^2 := by
  have h1 : (2 * 2^a * u) * (4 * 2^a * u) = 2 * 4^(a+1) * u^2 := by
    calc (2 * 2^a * u) * (4 * 2^a * u) = 8 * (2^a * 2^a) * u^2 := by ring
         _ = 8 * (2^a)^2 * u^2 := by ring
         _ = 8 * (2^2)^a * u^2 := by rw [← pow_mul, mul_comm a 2, pow_mul]
         _ = 2 * 4 * 4^a * u^2 := by rfl
         _ = 2 * (4 * 4^a) * u^2 := by ring
         _ = 2 * 4^(a+1) * u^2 := by rw [← pow_succ']
  have h2 : (2 * 2^a * u) * (4 * 2^a * u) < v * (4 * 2^a * u) := by
    calc (2 * 2^a * u) * (4 * 2^a * u) = 2 * 4^(a+1) * u^2 := h1
         _ < 4 * (2^a * u * v) := h
         _ = v * (4 * 2^a * u) := by ring
  have h3 : 2 * 2^a * u < v := Nat.lt_of_mul_lt_mul_right h2
  have hv : 0 < v := by linarith
  calc 2 * (2^a * u * v) = (2 * 2^a * u) * v := by ring
       _ < v * v := Nat.mul_lt_mul_of_pos_right h3 hv
       _ = v^2 := by ring

lemma chain_M_eq_zero_of_O_L (n u : ℕ) (hu : 2 * n < u^2) : chain_M n u = 0 := by
  rw [chain_M]
  apply Finset.card_eq_zero.mpr
  by_contra h
  obtain ⟨k, hk⟩ := Finset.nonempty_of_ne_empty h
  rw [mem_filter] at hk
  rcases hk with ⟨_, hk1, hk2⟩
  have h_pow_eq : 4^k * (2 * u^2) = 2 * 4^k * u^2 := by ring
  have h_pow2 : 2 * 4^k * u^2 = 2 * (2^k * u)^2 := (u_pow_two_mul u k).symm
  have h1 : 4 * n < 2 * u^2 := by omega
  have h2 : 2 * u^2 ≤ 4^k * (2 * u^2) := by
    have : 1 ≤ 4^k := Nat.one_le_pow _ _ (by decide)
    nlinarith
  omega

lemma chain_M_eq_zero_of_O_L_star (n u : ℕ) (hn : n ≠ 0) (hu : u ∣ n) (hu_odd : u % 2 = 1)
    (h_star : 2 * n < (odd_part (n / u))^2) : chain_M n u = 0 := by
  rw [chain_M]
  apply Finset.card_eq_zero.mpr
  by_contra h
  obtain ⟨k, hk⟩ := Finset.nonempty_of_ne_empty h
  rw [mem_filter, mem_range] at hk
  rcases hk with ⟨hk_range, hk1, hk2⟩
  let a := padicValNat 2 n
  let v := odd_part (n / u)
  have h_nu : n / u = 2^a * v := by
    calc n / u = 2^(padicValNat 2 (n / u)) * v := (odd_part_mul (n / u)).symm
         _ = 2^a * v := by rw [padic_mul_odd n u hn hu hu_odd]
  have h_n_eq : n = 2^a * u * v := by
    calc n = u * (n / u) := (Nat.mul_div_cancel' hu).symm
         _ = u * (2^a * v) := by rw [h_nu]
         _ = 2^a * u * v := by ring
  have h_star' : 2 * (2^a * u * v) < v^2 := by
    calc 2 * (2^a * u * v) = 2 * n := by rw [← h_n_eq]
         _ < v^2 := h_star
  have h_v_gt : 2^(a + 1) * u < v := by
    have h : 2^(a+1) * u * v < v * v := by
      calc 2^(a+1) * u * v = 2 * (2^a * u * v) := by ring
           _ < v^2 := h_star'
           _ = v * v := by ring
    exact lt_of_mul_lt_mul_right_of_pos h
  have hu_ne : u ≠ 0 := by rintro rfl; contradiction
  have h_pos : 0 < 2^a * u := by
    have h1 : 0 < u := Nat.pos_of_ne_zero hu_ne
    have h2 : 0 < 2^a := by positivity
    exact Nat.mul_pos h2 h1
  have h_contra : 2 * (2^k * u)^2 < n := by
    calc 2 * (2^k * u)^2 = 2 * 4^k * u^2 := u_pow_two_mul u k
         _ ≤ 2 * 4^a * u^2 := by
           have hk_le : k ≤ a := Nat.lt_succ_iff.mp hk_range
           have : 4^k ≤ 4^a := Nat.pow_le_pow_right (by decide) hk_le
           nlinarith
         _ = 2^(a + 1) * 2^a * u^2 := by rw [two_mul_four_pow a, mul_assoc]
         _ = (2^(a+1) * u) * (2^a * u) := by ring
         _ < v * (2^a * u) := Nat.mul_lt_mul_of_pos_right h_v_gt h_pos
         _ = v * 2^a * u := by ring
         _ = n := by rw [h_n_eq]; ring
  omega

lemma chain_M_eq_one_of_not_O_L_and_not_O_L_star (n u : ℕ) (hn : n ≠ 0) (hu : u ∣ n) (hu_odd : u % 2 = 1)
    (h_not_L : u^2 ≤ 2 * n) (h_not_L_star : (odd_part (n / u))^2 ≤ 2 * n) :
    chain_M n u ≥ 1 := by
  have hu_ne : u ≠ 0 := by rintro rfl; contradiction
  have hX0 : 0 < 2 * u^2 := by positivity
  have hX : 2 * u^2 < 4 * n := by
    have h_ne : u^2 ≠ 2 * n := odd_sq_ne_even u n hn hu_odd
    have h_lt : u^2 < 2 * n := Nat.lt_of_le_of_ne h_not_L h_ne
    omega
  have ⟨k, hk1, hk2⟩ := exists_power_four_in_interval n (2 * u^2) hX0 hX
  have h_k_in : k ∈ (range (padicValNat 2 n + 1)).filter (fun k => n ≤ 2 * (2^k * u)^2 ∧ 2 * (2^k * u)^2 < 4 * n) := by
    rw [mem_filter, mem_range]
    have h_pow_eq : 4^k * (2 * u^2) = 2 * 4^k * u^2 := by ring
    have h_symm : 2 * 4^k * u^2 = 2 * (2^k * u)^2 := (u_pow_two_mul u k).symm
    have hk1' : n ≤ 2 * (2^k * u)^2 := by
      rw [h_pow_eq] at hk1
      rw [h_symm] at hk1
      exact hk1
    have hk2' : 2 * (2^k * u)^2 < 4 * n := by
      rw [h_pow_eq] at hk2
      rw [h_symm] at hk2
      exact hk2
    refine ⟨?_, hk1', hk2'⟩
    by_contra h_ge
    push_neg at h_ge
    have h_k_gt_a : padicValNat 2 n + 1 ≤ k := h_ge
    let a := padicValNat 2 n
    let v := odd_part (n / u)
    have h_nu : n / u = 2^a * v := by
      calc n / u = 2^(padicValNat 2 (n / u)) * v := (odd_part_mul (n / u)).symm
           _ = 2^a * v := by rw [padic_mul_odd n u hn hu hu_odd]
    have h_n_eq : n = 2^a * u * v := by
      calc n = u * (n / u) := (Nat.mul_div_cancel' hu).symm
           _ = u * (2^a * v) := by rw [h_nu]
           _ = 2^a * u * v := by ring
    have h_contra1 : 2 * 4^(a+1) * u^2 ≤ 4^k * (2 * u^2) := by
      calc 2 * 4^(a+1) * u^2 = 4^(a+1) * (2 * u^2) := by ring
           _ ≤ 4^k * (2 * u^2) := by
             have : 4^(a+1) ≤ 4^k := Nat.pow_le_pow_right (by decide) h_k_gt_a
             nlinarith
    have h_contra2 : 2 * 4^(a+1) * u^2 < 4 * (2^a * u * v) := by
      calc 2 * 4^(a+1) * u^2 ≤ 4^k * (2 * u^2) := h_contra1
           _ < 4 * n := hk2
           _ = 4 * (2^a * u * v) := by rw [h_n_eq]
    have h_pos : 0 < 2^a * u := by
      have h1 : 0 < u := Nat.pos_of_ne_zero hu_ne
      have h2 : 0 < 2^a := by positivity
      exact Nat.mul_pos h2 h1
    have h_v_gt : 2 * n < v^2 := by
      have : 2 * (2^a * u * v) < v^2 := contra_helper a u v h_pos h_contra2
      rwa [← h_n_eq] at this
    have h_v_le : v^2 ≤ 2 * n := h_not_L_star
    omega
  rw [chain_M]
  exact card_pos.mpr ⟨k, h_k_in⟩

lemma chain_M_le_one (n u : ℕ) : chain_M n u ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  rw [mem_filter] at hx hy
  rcases hx with ⟨_, hx1, hx2⟩
  rcases hy with ⟨_, hy1, hy2⟩
  rw [u_pow_two_mul] at hx1 hx2 hy1 hy2
  by_contra hxy
  obtain h | h := lt_or_gt_of_ne hxy
  · have h_le : x + 1 ≤ y := h
    have : 4^(x + 1) * (2 * u^2) ≤ 4^y * (2 * u^2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h_le)
    have : 4 * (4^x * (2 * u^2)) ≤ 4^y * (2 * u^2) := by
      calc 4 * (4^x * (2 * u^2)) = 4^(x + 1) * (2 * u^2) := by ring
           _ ≤ 4^y * (2 * u^2) := this
    have h_contra : 4 * n ≤ 4^y * (2 * u^2) := by
      calc 4 * n ≤ 4 * (4^x * (2 * u^2)) := Nat.mul_le_mul_left 4 (by nlinarith)
           _ ≤ 4^y * (2 * u^2) := this
    nlinarith
  · have h_le : y + 1 ≤ x := h
    have : 4^(y + 1) * (2 * u^2) ≤ 4^x * (2 * u^2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h_le)
    have : 4 * (4^y * (2 * u^2)) ≤ 4^x * (2 * u^2) := by
      calc 4 * (4^y * (2 * u^2)) = 4^(y + 1) * (2 * u^2) := by ring
           _ ≤ 4^x * (2 * u^2) := this
    have h_contra : 4 * n ≤ 4^x * (2 * u^2) := by
      calc 4 * n ≤ 4 * (4^y * (2 * u^2)) := Nat.mul_le_mul_left 4 (by nlinarith)
           _ ≤ 4^x * (2 * u^2) := this
    nlinarith

lemma chain_M_eq_one (n u : ℕ) (hn : n ≠ 0) (hu : u ∣ n) (hu_odd : u % 2 = 1)
    (h_not_L : u^2 ≤ 2 * n) (h_not_L_star : (odd_part (n / u))^2 ≤ 2 * n) : chain_M n u = 1 := by
  have h1 := chain_M_eq_one_of_not_O_L_and_not_O_L_star n u hn hu hu_odd h_not_L h_not_L_star
  have h2 := chain_M_le_one n u
  omega

def O_L (n : ℕ) : Finset ℕ := (divisors n).filter (fun d => d % 2 = 1 ∧ 2 * n < d^2)

lemma O_L_subset_O (n : ℕ) : O_L n ⊆ O n := by
  intro x hx
  rw [O_L, mem_filter] at hx
  rw [O, mem_filter]
  exact ⟨hx.1, hx.2.1⟩

lemma odd_part_le (d : ℕ) : odd_part d ≤ d := by
  rw [odd_part]
  exact Nat.div_le_self d _

lemma odd_part_mul_le (n u : ℕ) (hu : u ∣ n) : u * odd_part (n / u) ≤ n := by
  calc u * odd_part (n / u) ≤ u * (n / u) := Nat.mul_le_mul_left u (odd_part_le _)
       _ = n := (Nat.mul_div_cancel' hu)

lemma O_L_disj_O_L_star (n u v : ℕ) (h_u : u ∈ O_L n) (h_v : v ∈ O_L n) (h_mul : u * v ≤ n) : False := by
  rw [O_L, mem_filter] at h_u h_v
  have h1 : 2 * n < u^2 := h_u.2.2
  have h2 : 2 * n < v^2 := h_v.2.2
  have h_pos : 0 < v^2 := by omega
  have h_mul_lt : 4 * n^2 < u^2 * v^2 := by
    calc 4 * n^2 = (2 * n) * (2 * n) := by ring
         _ ≤ (2 * n) * v^2 := Nat.mul_le_mul_left _ (by omega)
         _ < u^2 * v^2 := Nat.mul_lt_mul_of_pos_right h1 h_pos
  have h_sq : u^2 * v^2 = (u * v)^2 := by ring
  have h_bound : (u * v)^2 ≤ n^2 := by
    calc (u * v)^2 = (u * v) * (u * v) := by ring
         _ ≤ n * (u * v) := Nat.mul_le_mul_right _ h_mul
         _ ≤ n * n := Nat.mul_le_mul_left _ h_mul
         _ = n^2 := by ring
  omega

lemma disjoint_O_L_image (n : ℕ) (hn : n ≠ 0) :
    Disjoint (O_L n) ((O_L n).image (fun u => odd_part (n / u))) := by
  rw [Finset.disjoint_left]
  intro x hx h_img
  rw [mem_image] at h_img
  rcases h_img with ⟨u, hu_in, rfl⟩
  have hu_dvd : u ∣ n := by
    have h_sub := O_L_subset_O n hu_in
    rw [O, mem_filter, mem_divisors] at h_sub
    exact h_sub.1.1
  have h_mul := odd_part_mul_le n u hu_dvd
  exact O_L_disj_O_L_star n u (odd_part (n / u)) hu_in hx h_mul

lemma O_L_image_card (n : ℕ) (hn : n ≠ 0) :
    ((O_L n).image (fun u => odd_part (n / u))).card = (O_L n).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hxy' : odd_part (n / x) = odd_part (n / y) := by exact hxy
  have hx_sub := O_L_subset_O n hx
  have hy_sub := O_L_subset_O n hy
  have h_inv_x := (involution_O n hn x hx_sub).2
  have h_inv_y := (involution_O n hn y hy_sub).2
  rw [hxy'] at h_inv_x
  exact h_inv_x.symm.trans h_inv_y

lemma S_bad_sub (n : ℕ) (hn : n ≠ 0) : O_L n ∪ (O_L n).image (fun u => odd_part (n / u)) ⊆ O n := by
  intro x hx
  rw [mem_union] at hx
  cases hx with
  | inl h => exact O_L_subset_O n h
  | inr h =>
    rw [mem_image] at h
    rcases h with ⟨u, hu, rfl⟩
    have hu_O := O_L_subset_O n hu
    exact (involution_O n hn u hu_O).1

lemma card_S3 (n : ℕ) (hn : n ≠ 0) :
    (O n \ (O_L n ∪ (O_L n).image (fun u => odd_part (n / u)))).card = (O n).card - 2 * (O_L n).card := by
  have h_disj := disjoint_O_L_image n hn
  have h_card1 := Finset.card_union_of_disjoint h_disj
  rw [O_L_image_card n hn] at h_card1
  have h_sub := S_bad_sub n hn
  rw [card_sdiff, inter_eq_left.mpr h_sub, h_card1]
  omega

lemma final_equality (n : ℕ) (hn : n ≠ 0) : (M n).card = (O n).card - 2 * (O_L n).card := by
  have h_sum := sum_chain_M n hn
  rw [← h_sum]
  let S_bad := O_L n ∪ (O_L n).image (fun u => odd_part (n / u))
  have h_sub : S_bad ⊆ O n := S_bad_sub n hn
  have h_sum_split : ∑ u ∈ O n, chain_M n u = ∑ u ∈ S_bad, chain_M n u + ∑ u ∈ O n \ S_bad, chain_M n u := by
    rw [← sum_union disjoint_sdiff]
    congr 1
    exact (Finset.union_sdiff_of_subset h_sub).symm
  have h_sum_bad : ∑ u ∈ S_bad, chain_M n u = 0 := by
    apply sum_eq_zero
    intro u hu
    have hu_O : u ∈ O n := h_sub hu
    have hu_dvd : u ∣ n := by
      rw [O, mem_filter, mem_divisors] at hu_O
      exact hu_O.1.1
    have hu_odd : u % 2 = 1 := by
      rw [O, mem_filter, mem_divisors] at hu_O
      exact hu_O.2
    rw [mem_union] at hu
    cases hu with
    | inl h =>
      rw [O_L, mem_filter] at h
      exact chain_M_eq_zero_of_O_L n u h.2.2
    | inr h =>
      rw [mem_image] at h
      rcases h with ⟨v, hv_in, rfl⟩
      have hv_O : v ∈ O n := S_bad_sub n hn (mem_union_left _ hv_in)
      have h_v_eq : odd_part (n / odd_part (n / v)) = v := (involution_O n hn v hv_O).2
      have h_star : 2 * n < (odd_part (n / odd_part (n / v)))^2 := by
        rw [h_v_eq]
        rw [O_L, mem_filter] at hv_in
        exact hv_in.2.2
      exact chain_M_eq_zero_of_O_L_star n (odd_part (n / v)) hn hu_dvd hu_odd h_star
  have h_sum_good : ∑ u ∈ O n \ S_bad, chain_M n u = (O n \ S_bad).card := by
    calc ∑ u ∈ O n \ S_bad, chain_M n u = ∑ u ∈ O n \ S_bad, 1 := by
           apply sum_congr rfl
           intro u hu
           rw [mem_sdiff, mem_union, not_or] at hu
           have hu_in_O := hu.1
           have hu_not_L := hu.2.1
           have hu_not_L_star := hu.2.2
           have hu_in_O_copy := hu_in_O
           rw [O, mem_filter, mem_divisors] at hu_in_O
           have hu_dvd := hu_in_O.1.1
           have hu_odd := hu_in_O.2
           have h1 : u^2 ≤ 2 * n := by
             rw [O_L, mem_filter, not_and] at hu_not_L
             have h_in : u ∈ divisors n := by
               have h_tmp := hu_in_O_copy
               rw [O, mem_filter] at h_tmp
               exact h_tmp.1
             have : ¬(2 * n < u^2) := by
               intro h_lt
               exact hu_not_L h_in ⟨hu_odd, h_lt⟩
             omega
           have h2 : (odd_part (n / u))^2 ≤ 2 * n := by
             by_contra h_gt
             push_neg at h_gt
             have h_v_O : odd_part (n / u) ∈ O n := (involution_O n hn u hu_in_O_copy).1
             have h_v_L : odd_part (n / u) ∈ O_L n := by
               rw [O_L, mem_filter]
               rw [O, mem_filter] at h_v_O
               exact ⟨h_v_O.1, h_v_O.2, h_gt⟩
             have h_u_img : u ∈ (O_L n).image (fun u => odd_part (n / u)) := by
               rw [mem_image]
               use odd_part (n / u)
               refine ⟨h_v_L, ?_⟩
               exact (involution_O n hn u hu_in_O_copy).2
             exact hu_not_L_star h_u_img
           exact chain_M_eq_one n u hn hu_dvd hu_odd h1 h2
         _ = (O n \ S_bad).card := by simp
  rw [h_sum_split, h_sum_bad, zero_add, h_sum_good]
  exact card_S3 n hn

lemma oeis_281009_conjecture_proof (n : ℕ) (hn : n ≠ 0) : (A281009 n : ℤ) = 2 * (O_L n).card := by
  have h_eq := final_equality n hn
  rw [A281009, dif_neg hn]
  have h_odd_count : ((divisors n).filter (fun d => d % 2 = 1)).card = (O n).card := rfl
  have h_mid_count : ((divisors n).filter (fun d => n ≤ 2 * d^2 ∧ d^2 < 2 * n)).card = (M n).card := rfl
  dsimp
  rw [h_odd_count, h_mid_count]
  have h_le : 2 * (O_L n).card ≤ (O n).card := by
    have h_sub := S_bad_sub n hn
    have h_card := card_le_card h_sub
    have h_disj := disjoint_O_L_image n hn
    have h_card1 := Finset.card_union_of_disjoint h_disj
    rw [O_L_image_card n hn] at h_card1
    omega
  rw [h_eq, Nat.cast_sub (by omega)]
  push_cast
  ring

/--
Conjecture 1: a(n) is also twice the number of odd divisors of n greater than sqrt(2*n).
-/
theorem oeis_281009_conjecture_0 (n : ℕ) (hn : n ≠ 0) :
    (A281009 n : ℤ) = 2 * (↑(((divisors n).filter (fun d => d % 2 = 1 ∧ 2 * n < d ^ 2)).card) : ℤ) :=
  oeis_281009_conjecture_proof n hn

theorem oeis_281009_conjecture_0.disproof : ¬ (type_of% @oeis_281009_conjecture_0) := sorry
