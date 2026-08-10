import FormalConjectures.Util.ProblemImports

open Finset
open ZMod

noncomputable def A000224 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

theorem A000224_of_ne_zero {n : ℕ} (h_ne : n ≠ 0) :
    A000224 n = Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n)) := by
  unfold A000224
  split_ifs with h
  · exact False.elim (h_ne h)
  · rfl

theorem A000224_ge_two {n : ℕ} (hn : 1 < n) : A000224 n ≥ 2 := by
  have h_ne : n ≠ 0 := by omega
  rw [A000224_of_ne_zero h_ne]
  have h0 : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have h1 : 1 ∈ Finset.range n := Finset.mem_range.mpr hn
  have h0_img : 0 ∈ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) := by
    simp only [Finset.mem_image]
    refine ⟨0, h0, by simp⟩
  have h1_img : 1 ∈ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) := by
    simp only [Finset.mem_image]
    refine ⟨1, h1, by simp [Nat.mod_eq_of_lt hn]⟩
  have h_sub : {0, 1} ⊆ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0_img
    · exact h1_img
  have h_card_pair : Finset.card ({0, 1} : Finset ℕ) = 2 := by
    rw [Finset.card_pair (by decide)]
  have h_le := Finset.card_le_card h_sub
  rw [h_card_pair] at h_le
  exact h_le

theorem even_case {n : ℕ} (hn : Even n) (h_n : 1 < n) :
    ¬ (n * n ≡ 1 [MOD (A000224 n) * (A000224 n - 1)]) := by
  intro h
  set A := A000224 n
  have h_ge : A ≥ 2 := A000224_ge_two h_n
  have h_prod_even : Even (A * (A - 1)) := by
    rcases Nat.even_or_odd A with ⟨k, hk⟩ | ⟨k, hk⟩
    · use k * (A - 1)
      nth_rw 1 [hk]
      ring
    · use A * k
      have : A - 1 = 2 * k := by omega
      rw [this]
      rw [hk]
      ring
  rcases h_prod_even with ⟨m, hm⟩
  set M := A * (A - 1)
  have h_mod_ge : M ≥ 2 := by
    change A * (A - 1) ≥ 2
    have h1 : A ≥ 2 := h_ge
    have h2 : A - 1 ≥ 1 := by omega
    nlinarith
  have h_lt : 1 < M := by omega
  have h_mod : (n * n) % M = 1 := by
    rw [Nat.ModEq] at h
    rw [Nat.mod_eq_of_lt h_lt] at h
    exact h
  have hm' : M = 2 * m := by omega
  rw [hm'] at h_mod
  have h_odd : ¬ Even (n * n) := by
    intro h_even
    rcases h_even with ⟨r, hr⟩
    have hr' : n * n = 2 * r := by omega
    have h_mod2 : (2 * r) % (2 * m) = 1 := by
      rw [← hr']
      exact h_mod
    have h_div_mod : (2 * r) % (2 * m) % 2 = 1 % 2 := congr_arg (· % 2) h_mod2
    rw [Nat.mul_mod_mul_left] at h_div_mod
    simp at h_div_mod
  have h_even_nn : Even (n * n) := Even.mul_right hn n
  exact h_odd h_even_nn

theorem range_image_eq_range_half {n : ℕ} (h_odd : Odd n) (hn : 1 < n) :
    (Finset.range n).image (fun k : ℕ => k ^ 2 % n) =
    (Finset.range ((n + 1) / 2)).image (fun k : ℕ => k ^ 2 % n) := by
  rcases h_odd with ⟨m, hm⟩
  have h_div : (n + 1) / 2 = m + 1 := by
    rw [hm]
    omega
  ext y
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    by_cases h_lt : k < (n + 1) / 2
    · exact ⟨k, h_lt, rfl⟩
    · -- k ≥ (n+1)/2
      have hk2 : m + 1 ≤ k := by omega
      use n - k
      have hk_lt : n - k < m + 1 := by omega
      have hk_lt_half : n - k < (n + 1) / 2 := by omega
      refine ⟨hk_lt_half, ?_⟩
      -- k^2 % n = (n-k)^2 % n
      have h1 : 2 * k ≥ n := by omega
      have h2 : n ≥ k := by omega
      have h_eq : n * (2 * k - n) + (n - k) ^ 2 = k ^ 2 := by
        zify [h1, h2]
        ring
      rw [← h_eq]
      rw [add_comm]
      rw [Nat.add_mul_mod_self_left]
  · rintro ⟨k, hk, rfl⟩
    use k
    have h_lt : k < n := by omega
    exact ⟨h_lt, rfl⟩

theorem exists_factorization_of_odd_composite {n : ℕ} (h_odd : Odd n) (h_comp : ¬ n.Prime) (h_n : 1 < n) :
    ∃ p m, n = p * m ∧ 3 ≤ p ∧ p ≤ m := by
  have h2n : 2 ≤ n := by omega
  rcases Nat.exists_dvd_of_not_prime2 h2n h_comp with ⟨p, hp_dvd, hp1, hp_lt⟩
  set m := n / p
  have h_eq : n = p * m := (Nat.mul_div_cancel' hp_dvd).symm
  have hp_m_odd : Odd p ∧ Odd m := by
    have h_pm_odd : Odd (p * m) := by
      rw [← h_eq]
      exact h_odd
    exact Nat.odd_mul.mp h_pm_odd
  rcases hp_m_odd with ⟨⟨kp, hkp⟩, ⟨km, hkm⟩⟩
  have hp3 : 3 ≤ p := by omega
  have hm_ne1 : m ≠ 1 := by
    intro hm1
    rw [hm1] at h_eq
    rw [mul_one] at h_eq
    omega
  have hm3 : 3 ≤ m := by omega
  by_cases h_le : p ≤ m
  · exact ⟨p, m, h_eq, hp3, h_le⟩
  · have h_le2 : m ≤ p := by omega
    exact ⟨m, p, by rw [h_eq, mul_comm], hm3, h_le2⟩

theorem card_image_le_of_collision {α β : Type*} [DecidableEq α] [DecidableEq β] {s : Finset α} {f : α → β} {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) (h_eq : f x = f y) :
    (s.image f).card ≤ s.card - 1 := by
  have h_eq_set : s.image f = (s.erase y).image f := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases h_wy : w = y
      · subst h_wy
        exact ⟨x, Finset.mem_erase.mpr ⟨hne, hx⟩, h_eq⟩
      · exact ⟨w, Finset.mem_erase.mpr ⟨h_wy, hw⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, Finset.mem_of_mem_erase hw, rfl⟩
  rw [h_eq_set]
  have h_card := Finset.card_image_le (f := f) (s := s.erase y)
  have h_erase : (s.erase y).card = s.card - 1 := Finset.card_erase_of_mem hy
  rw [h_erase] at h_card
  exact h_card

theorem A000224_le_half_of_odd_composite {n : ℕ} (h_odd : Odd n) (h_comp : ¬ n.Prime) (h_n : 1 < n) :
    A000224 n ≤ (n - 1) / 2 := by
  rcases exists_factorization_of_odd_composite h_odd h_comp h_n with ⟨p, m, rfl, hp3, h_le⟩
  have hp_m_odd : Odd p ∧ Odd m := by
    have h_pm_odd : Odd (p * m) := h_odd
    exact Nat.odd_mul.mp h_pm_odd
  rcases hp_m_odd with ⟨⟨kp, rfl⟩, ⟨km, rfl⟩⟩
  have h_kp_le : kp ≤ km := by omega
  set x := (2 * km + 1 - (2 * kp + 1)) / 2
  set y := (2 * km + 1 + (2 * kp + 1)) / 2
  have hx : x = km - kp := by omega
  have hy : y = km + kp + 1 := by omega
  have hkp_pos : kp ≥ 1 := by omega
  have hkm_pos : km ≥ 1 := by omega
  have h_xy_lt : y < ((2 * kp + 1) * (2 * km + 1) + 1) / 2 := by
    have : (2 * kp + 1) * (2 * km + 1) + 1 = 2 * (2 * km * kp + km + kp + 1) := by ring
    rw [this]
    rw [Nat.mul_div_cancel_left]
    · nlinarith
    · omega
  have h_x_lt_y : x < y := by omega
  have h_x_ne_y : x ≠ y := by omega
  have h_sq_eq : y ^ 2 = x ^ 2 + (2 * kp + 1) * (2 * km + 1) := by
    rw [hx, hy]
    zify [h_kp_le]
    ring
  have h_mod_eq : y ^ 2 % ((2 * kp + 1) * (2 * km + 1)) = x ^ 2 % ((2 * kp + 1) * (2 * km + 1)) := by
    rw [h_sq_eq]
    have h_rw : x ^ 2 + (2 * kp + 1) * (2 * km + 1) = (2 * kp + 1) * (2 * km + 1) * 1 + x ^ 2 := by ring
    rw [h_rw]
    exact Nat.mul_add_mod_self_left ((2 * kp + 1) * (2 * km + 1)) 1 (x ^ 2)
  have h_ne : (2 * kp + 1) * (2 * km + 1) ≠ 0 := by omega
  rw [A000224_of_ne_zero h_ne]
  rw [range_image_eq_range_half h_odd (by omega)]
  have h_x_mem : x ∈ Finset.range (((2 * kp + 1) * (2 * km + 1) + 1) / 2) := Finset.mem_range.mpr (by omega)
  have h_y_mem : y ∈ Finset.range (((2 * kp + 1) * (2 * km + 1) + 1) / 2) := Finset.mem_range.mpr h_xy_lt
  have h_le_card := card_image_le_of_collision (f := fun k : ℕ => k ^ 2 % ((2 * kp + 1) * (2 * km + 1))) h_x_mem h_y_mem h_x_ne_y h_mod_eq.symm
  rw [Finset.card_range] at h_le_card
  have h_goal : ((2 * kp + 1) * (2 * km + 1) + 1) / 2 - 1 = ((2 * kp + 1) * (2 * km + 1) - 1) / 2 := by omega
  rw [h_goal] at h_le_card
  exact h_le_card

theorem card_squares_eq_zmod_card (n : ℕ) [NeZero n] :
    Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n)) =
    Finset.card (Finset.univ.image (fun x : ZMod n => x ^ 2)) := by
  set s := (Finset.range n).image (fun k : ℕ => k ^ 2 % n)
  set t := Finset.univ.image (fun x : ZMod n => x ^ 2)
  apply @Finset.card_bij' ℕ (ZMod n) s t (fun a _ => (a : ZMod n)) (fun b _ => b.val)
  · intro a ha
    dsimp [s, t] at ha ⊢
    simp only [Finset.mem_image, Finset.mem_range] at ha ⊢
    rcases ha with ⟨k, _, rfl⟩
    use (k : ZMod n)
    simp only [Finset.mem_univ, true_and]
    rw [ZMod.natCast_mod]
    push_cast
    rfl
  · intro b hb
    dsimp [s, t] at hb ⊢
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hb ⊢
    rcases hb with ⟨x, rfl⟩
    use x.val
    have hx_lt : x.val < n := ZMod.val_lt x
    refine ⟨by simpa using hx_lt, ?_⟩
    rw [pow_two (x.val), pow_two x, ZMod.val_mul]
  · intro a ha
    dsimp [s] at ha
    simp only [Finset.mem_image, Finset.mem_range] at ha
    rcases ha with ⟨k, _, rfl⟩
    rw [ZMod.val_natCast, Nat.mod_mod]
  · intro b hb
    exact ZMod.natCast_zmod_val b

theorem card_univ_image_sq {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Finset.card (Finset.univ.image (fun x : ZMod p => x ^ 2)) = (p + 1) / 2 := by
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have h_div : (p + 1) % 2 = 0 := by omega
  have h_mul_div : 2 * ((p + 1) / 2) = p + 1 := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h_div)
  set m := (p + 1) / 2
  have h_eq : Finset.univ.image (fun x : ZMod p => x ^ 2) =
              (Finset.range m).image (fun (k : ℕ) => (k : ZMod p) ^ 2) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases h_lt : x.val < m
      · use x.val
        simp only [Finset.mem_range]
        refine ⟨h_lt, ?_⟩
        rw [ZMod.natCast_zmod_val]
      · have h_ge : x.val ≥ m := by omega
        have hx_lt : x.val < p := ZMod.val_lt x
        set k := p - x.val
        use k
        simp only [Finset.mem_range]
        have hk_lt : k < m := by omega
        refine ⟨hk_lt, ?_⟩
        have hk_eq : (k : ZMod p) = -x := by
          have h_sub : ((p - x.val : ℕ) : ZMod p) = (p : ZMod p) - (x.val : ZMod p) := Nat.cast_sub hx_lt.le
          rw [h_sub, ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val]
        rw [hk_eq]
        ring
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(k : ZMod p), rfl⟩
  rw [h_eq]
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_range]
  · intro k1 hk1 k2 hk2 hsq
    haveI : Fact p.Prime := ⟨hp⟩
    have hk1_lt : k1 < m := Finset.mem_range.mp hk1
    have hk2_lt : k2 < m := Finset.mem_range.mp hk2
    have hm_le_p : m ≤ p := by omega
    have hk1_lt_p : k1 < p := hk1_lt.trans_le hm_le_p
    have hk2_lt_p : k2 < p := hk2_lt.trans_le hm_le_p
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hsq
    rcases hsq with h1 | h2
    · -- k1 = k2 in ZMod p
      have h_val := congr_arg ZMod.val h1
      rw [ZMod.val_natCast_of_lt hk1_lt_p, ZMod.val_natCast_of_lt hk2_lt_p] at h_val
      exact h_val
    · -- k1 = -k2 in ZMod p => k1 + k2 = 0
      have h_add : ((k1 + k2 : ℕ) : ZMod p) = 0 := by
        push_cast
        rw [h2]
        ring
      rw [ZMod.natCast_eq_zero_iff] at h_add
      -- since k1, k2 < m:
      have hk1_le : k1 ≤ (p - 1) / 2 := by omega
      have hk2_le : k2 ≤ (p - 1) / 2 := by omega
      have h_sum_le : k1 + k2 ≤ p - 1 := by omega
      rcases h_add with ⟨c, hc⟩
      -- k1 + k2 = c * p
      -- since k1 + k2 <= p - 1, we must have c = 0
      have hc0 : c = 0 := by
        by_contra h_ne
        have hc_ge : c ≥ 1 := by omega
        have h_mul : c * p ≥ 1 * p := Nat.mul_le_mul_right p hc_ge
        simp only [one_mul] at h_mul
        rw [mul_comm] at hc
        rw [← hc] at h_mul
        omega
      subst hc0
      simp only [mul_zero, add_eq_zero] at hc
      omega

theorem A000224_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    A000224 p = (p + 1) / 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp1 : 1 < p := hp.one_lt
  rw [A000224_of_ne_zero (by omega)]
  rw [card_squares_eq_zmod_card p]
  exact card_univ_image_sq hp hp2

theorem forward_direction {n : ℕ} (h_n : 1 < n) (hp : n.Prime) (hp2 : n ≠ 2) :
    (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  have hp_odd : n % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have h_div : (n + 1) % 2 = 0 := by omega
  have h_A : A000224 n = (n + 1) / 2 := A000224_of_odd_prime hp hp2
  set A := A000224 n
  have h_A_val : A = (n + 1) / 2 := h_A
  have h2A : 2 * A = n + 1 := by
    rw [h_A_val]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h_div)
  have h_A_ge : A ≥ 2 := by omega
  have h_A_sub : 2 * (A - 1) = n - 1 := by omega
  have h_prod_eq : (n + 1) * (n - 1) + 1 = n * n := by
    have h1 : 1 ≤ n := by omega
    have h2 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub h1
    have h_int : ((n + 1) * (n - 1) + 1 : ℤ) = (n * n : ℤ) := by
      ring
    exact_mod_cast h_int
  have h_eq : n * n = 4 * (A * (A - 1)) + 1 := by
    calc
      n * n = (n + 1) * (n - 1) + 1 := h_prod_eq.symm
      _ = (2 * A) * (2 * (A - 1)) + 1 := by rw [h2A, h_A_sub]
      _ = 4 * (A * (A - 1)) + 1 := by ring
  rw [Nat.ModEq]
  rw [h_eq]
  rw [add_comm]
  rw [Nat.add_mul_mod_self_right]

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable def check_ordowski (n : ℕ) : Bool :=
  if n % 2 == 0 then true
  else if decide (Nat.Prime n) then true
  else
    let A := A000224 n
    let M := A * (A - 1)
    if M == 0 then true
    else (n * n) % M != 1

noncomputable def check_up_to : ℕ → Bool
  | 0 => true
  | n + 1 => check_ordowski n && check_up_to n

theorem check_up_to_implies_no_solution (limit : ℕ) :
    check_up_to limit = true → ∀ n, n < limit → 1 < n → ¬ n.Prime → Odd n → ¬ ((n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)]) := by
  induction limit with
  | zero =>
    intro _ n hn
    omega
  | succ limit ih =>
    intro h_check n hn h_n hp hn_odd h_congr
    unfold check_up_to at h_check
    rw [Bool.and_eq_true] at h_check
    rcases h_check with ⟨h_limit, h_prev⟩
    by_cases hn_limit : n < limit
    · exact ih h_prev n hn_limit h_n hp hn_odd h_congr
    · have hn_eq : n = limit := by omega
      subst hn_eq
      unfold check_ordowski at h_limit
      have h_mod2 : n % 2 ≠ 0 := by
        intro h_even
        have : Even n := Nat.even_iff.mpr h_even
        have h_not_odd := Nat.not_even_iff_odd.mpr hn_odd
        exact h_not_odd this
      have h_prime_dec : decide (Nat.Prime n) = false := by
        simp [hp]
      simp [h_mod2, h_prime_dec] at h_limit
      have h_mod_eq : (n * n) % (A000224 n * (A000224 n - 1)) = 1 := by
        have h_M_gt : 1 < A000224 n * (A000224 n - 1) := by
          have h_A_ge : A000224 n ≥ 2 := A000224_ge_two h_n
          have h_A_sub : A000224 n - 1 ≥ 1 := by omega
          have : 2 * 1 ≤ A000224 n * (A000224 n - 1) := Nat.mul_le_mul h_A_ge h_A_sub
          omega
        rw [h_congr]
        exact Nat.mod_eq_of_lt h_M_gt
      have h_A_ge : A000224 n ≥ 2 := A000224_ge_two h_n
      omega

theorem check_up_to_250_true : check_up_to 350 = true := by
  decide

/--
Conjecture: n^2 == 1 (mod a(n)*(a(n)-1)) if and only if n is an odd prime.
-/
lemma no_solution_small :
    ∀ n < 350, 1 < n → ¬ n.Prime → Odd n → ¬ ((n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)]) :=
  check_up_to_implies_no_solution 350 check_up_to_250_true
theorem oeis_a000224_conjecture_ordowski {n : ℕ} (h_n : 1 < n) :
    (n.Prime ∧ n ≠ 2) ↔ (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  constructor
  · rintro ⟨hp, hp2⟩
    exact forward_direction h_n hp hp2
  · intro h
    by_cases hp : n.Prime
    · refine ⟨hp, ?_⟩
      rintro rfl
      have hA : A000224 2 = 2 := by decide
      rw [hA] at h
      have h_not : ¬((2 * 2) ≡ 1 [MOD 2 * (2 - 1)]) := by decide
      exact (h_not h).elim
    · by_cases hn_even : Even n
      · exact (even_case hn_even h_n h).elim
      · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
        set p := n.minFac
        have hp_prime : p.Prime := Nat.minFac_prime (by omega)
        have h_p_dvd : p ∣ n := n.minFac_dvd
        have hp3 : 3 ≤ p := by
          have hp_ge : p ≥ 2 := hp_prime.two_le
          by_contra hp_lt
          have hp2 : p = 2 := by omega
          rcases h_p_dvd with ⟨k, hk⟩
          have h_even_n : Even n := by
            use k
            rw [hk, hp2]
            omega
          exact hn_even h_even_n
        set A := A000224 n
        set M := A * (A - 1)
        have h_M_ge_two : M ≥ 2 := by
          have h_A_ge_two : A ≥ 2 := A000224_ge_two h_n
          have h_A_sub_one : A - 1 ≥ 1 := by omega
          calc
            A * (A - 1) ≥ 2 * (A - 1) := Nat.mul_le_mul_right (A - 1) h_A_ge_two
            _ ≥ 2 * 1 := Nat.mul_le_mul_left 2 h_A_sub_one
            _ = 2 := by rfl
        have h_mod : (n * n) % M = 1 := by
          have h_lt : 1 < M := by omega
          have h_mod_eq : (n * n) % M = 1 % M := h
          rw [Nat.mod_eq_of_lt h_lt] at h_mod_eq
          exact h_mod_eq
        have h_eq_div : n * n = M * (n * n / M) + (n * n) % M := (Nat.div_add_mod (n * n) M).symm
        have h_sub : n * n - 1 = M * (n * n / M) := by omega
        have h_dvd_M : M ∣ n * n - 1 := ⟨n * n / M, h_sub⟩
        have hp_ndvd_M : ¬ (p ∣ M) := by
          intro hp_dvd_M
          have hp_dvd_nn_sub_one : p ∣ n * n - 1 := hp_dvd_M.trans h_dvd_M
          have hp_dvd_nn : p ∣ n * n := by
            rcases h_p_dvd with ⟨r, hr⟩
            use r * n
            rw [hr]
            ring
          rcases hp_dvd_nn with ⟨d, hd⟩
          rcases hp_dvd_nn_sub_one with ⟨c, hc⟩
          have h_eq : p * d = p * c + 1 := by omega
          have hp_le_one : p ≤ 1 := by
            by_contra hp_gt
            have h_p_ge2 : p ≥ 2 := by omega
            have h_d_gt_c : d > c := by
              by_contra h_le
              have : p * d ≤ p * c := Nat.mul_le_mul_left p (by omega)
              omega
            have h_d_minus_c_ge1 : d - c ≥ 1 := by omega
            have h_prod : p * (d - c) ≥ 2 := by
              calc
                p * (d - c) ≥ p * 1 := Nat.mul_le_mul_left p h_d_minus_c_ge1
                _ ≥ 2 * 1 := Nat.mul_le_mul_right 1 h_p_ge2
                _ = 2 := by rfl
            have h_prod_eq : p * (d - c) = 1 := by
              zify [h_d_minus_c_ge1, h_d_gt_c.le] at *
              linarith
            omega
          omega
        by_cases hn1000 : n < 1000
        · have h_not := no_solution_small n hn1000 h_n hp hn_odd
          exact False.elim (h_not h)
        · have h_A_le : A ≤ (n - 1) / 2 := A000224_le_half_of_odd_composite hn_odd hp h_n
          have h_M_le : 4 * M ≤ n * n - 4 * n + 3 := by
            have h1 : 2 * A ≤ n - 1 := by omega
            have h2 : 2 * A - 2 ≤ n - 3 := by omega
            have h3 : (2 * A) * (2 * A - 2) ≤ (n - 1) * (n - 3) := Nat.mul_le_mul h1 h2
            have h_eq1 : (2 * A) * (2 * A - 2) = 4 * M := by
              have : 2 * A - 2 = 2 * (A - 1) := by omega
              rw [this]
              ring
            have h_eq2 : (n - 1) * (n - 3) = n * n - 4 * n + 3 := by
              have hn4 : n ≥ 4 := by omega
              have h_sub1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
              have h_sub2 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
              have h_sub3 : ((n * n - 4 * n : ℕ) : ℤ) = (n : ℤ) * (n : ℤ) - 4 * (n : ℤ) := by
                have : n * n ≥ 4 * n := by nlinarith
                omega
              have h_int : (((n - 1) * (n - 3) : ℕ) : ℤ) = ((n * n - 4 * n + 3 : ℕ) : ℤ) := by
                push_cast
                rw [h_sub1, h_sub2, h_sub3]
                ring
              exact_mod_cast h_int
            omega
          have h_5M_le : 5 * M ≤ n * n - 1 := by
            have h_eq : n * n - 1 = (n * n - 1) / M * M := by
              have h_eq_lhs := (Nat.mul_div_cancel' h_dvd_M).symm
              rw [Nat.mul_comm M] at h_eq_lhs
              exact h_eq_lhs
            have h_4M_lt : 4 * M < n * n - 1 := by omega
            have h_k_ge : (n * n - 1) / M ≥ 5 := by
              by_contra h_lt
              have : (n * n - 1) / M ≤ 4 := by omega
              have : (n * n - 1) / M * M ≤ 4 * M := Nat.mul_le_mul_right M this
              omega
            have : 5 * M ≤ (n * n - 1) / M * M := Nat.mul_le_mul_right M h_k_ge
            omega
          sorry
