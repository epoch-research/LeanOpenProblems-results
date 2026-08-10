import FormalConjectures.Util.ProblemImports
open Finset BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- ===== copied digit machinery from TestPoC =====
lemma low_bound (W : ℕ) (c : ℕ → ℕ) (hc : ∀ i, c i < 2^W) (k : ℕ) :
    (∑ i ∈ range k, c i * 2^(W*i)) < 2^(W*k) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hexp : 2^(W*(n+1)) = 2^W * 2^(W*n) := by rw [← pow_add]; congr 1; ring
    rw [hexp]
    have h1 : c n + 1 ≤ 2^W := hc n
    calc (∑ i ∈ range n, c i * 2^(W*i)) + c n * 2^(W*n)
        < 2^(W*n) + c n * 2^(W*n) := by exact Nat.add_lt_add_right ih _
      _ = (c n + 1) * 2^(W*n) := by ring
      _ ≤ 2^W * 2^(W*n) := by exact Nat.mul_le_mul_right _ h1

lemma upper_dvd (W : ℕ) (c : ℕ → ℕ) (k M : ℕ) :
    2^(W*(k+1)) ∣ (∑ i ∈ Ico (k+1) M, c i * 2^(W*i)) := by
  apply Finset.dvd_sum
  intro i hi
  rw [Finset.mem_Ico] at hi
  have : 2^(W*(k+1)) ∣ 2^(W*i) := by
    apply pow_dvd_pow
    exact Nat.mul_le_mul_left W hi.1
  exact Dvd.dvd.mul_left this _

lemma digit_extract (W : ℕ) (c : ℕ → ℕ) (hc : ∀ i, c i < 2^W) (M k : ℕ) (hk : k < M) :
    ((∑ i ∈ range M, c i * 2^(W*i)) / 2^(W*k)) % 2^W = c k := by
  have hsplit : (∑ i ∈ range M, c i * 2^(W*i))
      = (∑ i ∈ range k, c i * 2^(W*i)) + (∑ i ∈ Ico k M, c i * 2^(W*i)) := by
    rw [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (le_of_lt hk)]
  have hpeel : (∑ i ∈ Ico k M, c i * 2^(W*i))
      = c k * 2^(W*k) + (∑ i ∈ Ico (k+1) M, c i * 2^(W*i)) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot hk]
  obtain ⟨U', hU'⟩ := upper_dvd W c k M
  set L := ∑ i ∈ range k, c i * 2^(W*i) with hLdef
  have hLlt : L < 2^(W*k) := low_bound W c hc k
  have hexp : 2^(W*(k+1)) = 2^(W*k) * 2^W := by rw [← pow_add, show W*k+W = W*(k+1) from by ring]
  have hN : (∑ i ∈ range M, c i * 2^(W*i)) = L + (c k + 2^W * U') * 2^(W*k) := by
    rw [hsplit, hpeel, hU', hexp]; ring
  rw [hN]
  rw [Nat.add_mul_div_right _ _ (by positivity)]
  rw [Nat.div_eq_of_lt hLlt]
  simp only [Nat.zero_add]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (hc k)

-- ===== card machinery; W kept symbolic to avoid elaborator reducing 2^(W k²) =====
noncomputable def Ftheta (W : ℕ) : ℕ := ∑ k ∈ range 264, 2^(W*k^2)
noncomputable def Gtheta (W : ℕ) : ℕ := ∑ k ∈ Ico 1 264, 2^(W*k^2)

-- count function over nested ranges (z ∈ Ico 1 264 so z ≥ 1)
noncomputable def cntN (m : ℕ) : ℕ :=
  ∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ Ico 1 264, ∑ w ∈ range 264,
    (if x^2+y^2+z^2+w^2 = m then 1 else 0)

-- F - 1 = G
lemma F_sub_one (W : ℕ) : Ftheta W - 1 = Gtheta W := by
  unfold Ftheta Gtheta
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (0:ℕ) < 264)]
  simp

-- key: 2^(W s) expands over the digit indicator, for s < M
lemma pow_eq_sum_ind (W s : ℕ) (hs : s < 276677) :
    (2:ℕ)^(W*s) = ∑ m ∈ range 276677, (if s = m then 1 else 0) * 2^(W*m) := by
  rw [Finset.sum_eq_single_of_mem s (Finset.mem_range.mpr hs)]
  · simp
  · intro m _ hm
    rw [if_neg (by omega), zero_mul]

-- expand: F*F*G*F = nested theta sum
lemma expand_FFGF (W : ℕ) :
    Ftheta W * Ftheta W * Gtheta W * Ftheta W
      = ∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ Ico 1 264, ∑ w ∈ range 264,
          2^(W*(x^2+y^2+z^2+w^2)) := by
  have hFF : Ftheta W * Ftheta W = ∑ x ∈ range 264, ∑ y ∈ range 264, 2^(W*(x^2+y^2)) := by
    unfold Ftheta; rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _
    rw [← pow_add, show W*x^2+W*y^2 = W*(x^2+y^2) from by ring]
  have hGF : Gtheta W * Ftheta W = ∑ z ∈ Ico 1 264, ∑ w ∈ range 264, 2^(W*(z^2+w^2)) := by
    unfold Gtheta Ftheta; rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro w _
    rw [← pow_add, show W*z^2+W*w^2 = W*(z^2+w^2) from by ring]
  rw [mul_assoc (Ftheta W*Ftheta W) (Gtheta W) (Ftheta W), hFF, hGF, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w _
  rw [← pow_add, show W*(x^2+y^2)+W*(z^2+w^2) = W*(x^2+y^2+z^2+w^2) from by ring]

lemma step1_lemma (W : ℕ) :
    (∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ Ico 1 264, ∑ w ∈ range 264,
        (2:ℕ)^(W*(x^2+y^2+z^2+w^2)))
      = ∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ Ico 1 264, ∑ w ∈ range 264,
          ∑ m ∈ range 276677, (if x^2+y^2+z^2+w^2 = m then 1 else 0) * 2^(W*m) := by
  apply Finset.sum_congr rfl; intro x hx
  apply Finset.sum_congr rfl; intro y hy
  apply Finset.sum_congr rfl; intro z hz
  apply Finset.sum_congr rfl; intro w hw
  rw [Finset.mem_range] at hx hy hw
  rw [Finset.mem_Ico] at hz
  apply pow_eq_sum_ind
  have h1 : x^2 ≤ 69169 := by calc x^2 ≤ 263^2 := Nat.pow_le_pow_left (by omega) 2
                                  _ = 69169 := by norm_num
  have h2 : y^2 ≤ 69169 := by calc y^2 ≤ 263^2 := Nat.pow_le_pow_left (by omega) 2
                                  _ = 69169 := by norm_num
  have h3 : z^2 ≤ 69169 := by calc z^2 ≤ 263^2 := Nat.pow_le_pow_left (by omega) 2
                                  _ = 69169 := by norm_num
  have h4 : w^2 ≤ 69169 := by calc w^2 ≤ 263^2 := Nat.pow_le_pow_left (by omega) 2
                                  _ = 69169 := by norm_num
  omega

-- regroup nested sum by value m
lemma regroup (W : ℕ) :
    (∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ Ico 1 264, ∑ w ∈ range 264,
        (2:ℕ)^(W*(x^2+y^2+z^2+w^2)))
      = ∑ m ∈ range 276677, cntN m * 2^(W*m) := by
  rw [step1_lemma W]
  symm
  simp only [cntN, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro z _
  rw [Finset.sum_comm]

-- bound: cntN m < 2^33
lemma cntN_lt (m : ℕ) : cntN m < 2^33 := by
  have h : cntN m ≤ ∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ Ico 1 264, ∑ w ∈ range 264, 1 := by
    unfold cntN
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro y _
    apply Finset.sum_le_sum; intro z _
    apply Finset.sum_le_sum; intro w _
    split <;> norm_num
  simp only [Finset.sum_const, Finset.card_range, Nat.card_Ico, smul_eq_mul, mul_one] at h
  norm_num at h
  omega

lemma theta_eq_cnt (W : ℕ) :
    Ftheta W * Ftheta W * Gtheta W * Ftheta W = ∑ m ∈ range 276677, cntN m * 2^(W*m) := by
  rw [expand_FFGF W, regroup W]

lemma cnt_digit :
    ((Ftheta 33 * Ftheta 33 * Gtheta 33 * Ftheta 33) / 2^(33*69383)) % 2^33 = cntN 69383 := by
  rw [theta_eq_cnt 33]
  exact digit_extract 33 cntN cntN_lt 276677 69383 (by norm_num)

set_option maxHeartbeats 0 in
lemma cnt_val :
    ((Ftheta 33 * Ftheta 33 * Gtheta 33 * Ftheta 33) / 2^(33*69383)) % 2^33 = 34692 := by
  unfold Ftheta Gtheta
  decide +kernel

lemma cntN_69383 : cntN 69383 = 34692 := by rw [← cnt_digit, cnt_val]

-- w-uniqueness: counting w with x²+y²+z²+w²=n equals the IsSquare indicator
lemma w_uniq (x y z : ℕ) :
    (∑ w ∈ range 264, (if x^2+y^2+z^2+w^2 = 69383 then (1:ℕ) else 0))
      = (if (x^2+y^2+z^2 ≤ 69383 ∧ IsSquare (69383 - (x^2+y^2+z^2))) then 1 else 0) := by
  set s := x^2+y^2+z^2 with hs_def
  by_cases hs : s ≤ 69383
  · by_cases hsq : IsSquare (69383 - s)
    · rw [if_pos ⟨hs, hsq⟩]
      obtain ⟨w0, hw0⟩ := hsq
      have hw0n : s + w0 * w0 = 69383 := by omega
      have hw0lt : w0 < 264 := by nlinarith [hw0n]
      rw [Finset.sum_eq_single_of_mem w0 (Finset.mem_range.mpr hw0lt)]
      · rw [if_pos]; rw [sq]; omega
      · intro w _ hw
        rw [if_neg]
        intro hcon
        rw [sq] at hcon
        have : w * w = w0 * w0 := by omega
        exact (hw (Nat.mul_self_inj.mp this)).elim
    · rw [if_neg (by tauto)]
      apply Finset.sum_eq_zero
      intro w _
      rw [if_neg]
      intro hcon
      apply hsq
      exact ⟨w, by rw [sq] at hcon; omega⟩
  · rw [if_neg (by tauto)]
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    intro hcon
    rw [sq] at hcon; omega

-- full-qualifier count (= a 69383)
def cond3 (x y z : ℕ) : ℕ := if IsSquare ((5*x^2+7*y^2+9*z^2)*y*z) then 1 else 0

noncomputable def FQ : ℕ :=
  ∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ range 264,
    (if (0 < z ∧ x^2+y^2+z^2 ≤ 69383 ∧ IsSquare (69383-(x^2+y^2+z^2)) ∧
        IsSquare ((5*x^2+7*y^2+9*z^2)*y*z)) then (1:ℕ) else 0)

noncomputable def S3 : Finset (ℕ×ℕ×ℕ) :=
  (range 264 ×ˢ range 264 ×ˢ range 264).filter
    (fun p => 0 < p.2.2 ∧ p.1^2+p.2.1^2+p.2.2^2 ≤ 69383 ∧
              IsSquare (69383 - (p.1^2+p.2.1^2+p.2.2^2)))

-- helper: range→Ico for z>0
lemma sum_pos_z (g : ℕ → ℕ) :
    (∑ z ∈ range 264, (if 0 < z then g z else 0)) = ∑ z ∈ Ico 1 264, g z := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (0:ℕ) < 264)]
  simp only [lt_irrefl, if_false, zero_add]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mem_Ico] at hz
  rw [if_pos (by omega)]

lemma card_S3 : S3.card = 34692 := by
  rw [← cntN_69383]
  unfold S3
  rw [Finset.card_filter, Finset.sum_product, cntN]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl; intro y _
  simp only
  rw [← sum_pos_z]
  apply Finset.sum_congr rfl; intro z _
  by_cases hz : 0 < z
  · rw [if_pos hz, w_uniq x y z]
    simp only [hz, true_and]
  · rw [if_neg hz, if_neg (fun h => hz h.1)]

lemma FQ_eq : FQ = ∑ p ∈ S3, cond3 p.1 p.2.1 p.2.2 := by
  rw [S3, Finset.sum_filter, Finset.sum_product]
  unfold FQ
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl; intro y _
  simp only
  apply Finset.sum_congr rfl; intro z _
  unfold cond3
  by_cases h3 : (0 < z ∧ x^2+y^2+z^2 ≤ 69383 ∧ IsSquare (69383-(x^2+y^2+z^2)))
  · rw [if_pos h3]
    by_cases hcc : IsSquare ((5*x^2+7*y^2+9*z^2)*y*z)
    · rw [if_pos hcc, if_pos ⟨h3.1, h3.2.1, h3.2.2, hcc⟩]
    · rw [if_neg hcc, if_neg (fun h => hcc h.2.2.2)]
  · rw [if_neg h3, if_neg (fun h => h3 ⟨h.1, h.2.1, h.2.2.1⟩)]
