import FormalConjectures.Util.ProblemImports
open BigOperators Nat Finset
set_option maxHeartbeats 0

def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

def T (n k : ℕ) : ℕ := (n.choose k)^2 * ((Nat.choose (n+k) k))^2

lemma choose_mod3_lucas1 (n k : ℕ) :
    n.choose k ≡ (n % 3).choose (k % 3) * (n / 3).choose (k / 3) [MOD 3] := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 3)

lemma zmod_choose_3m_k (m k : ℕ) :
    ((3*m).choose k : ZMod 3) = (if k % 3 = 0 then (m.choose (k/3) : ZMod 3) else 0) := by
  have h := choose_mod3_lucas1 (3*m) k
  have hm : (3*m) % 3 = 0 := by simp [Nat.mul_mod_right]
  have hdivm : (3*m) / 3 = m := by omega
  rw [hm, hdivm] at h
  by_cases hk : k % 3 = 0
  · have h0 : Nat.choose 0 (k % 3) = 1 := by simp [hk]
    rw [h0, one_mul] at h
    rw [if_pos hk]
    exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h
  · have h0 : Nat.choose 0 (k % 3) = 0 := by
      cases hmod : k % 3 with
      | zero => exact False.elim (hk hmod)
      | succ r => simp
    rw [h0, zero_mul] at h
    rw [if_neg hk]
    exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h

lemma zmod_choose_3m_plus_3q (m q : ℕ) :
    ((3*m + 3*q).choose (3*q) : ZMod 3) = ((m+q).choose q : ZMod 3) := by
  have h := choose_mod3_lucas1 (3*m+3*q) (3*q)
  have hmodtop : (3*m+3*q) % 3 = 0 := by omega
  have hdivtop : (3*m+3*q) / 3 = m+q := by omega
  have hmodbot : (3*q) % 3 = 0 := by simp [Nat.mul_mod_right]
  have hdivbot : (3*q) / 3 = q := by omega
  rw [hmodtop, hdivtop, hmodbot, hdivbot] at h
  simp at h
  exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h

lemma zmod_T_3m_k (m k : ℕ) :
    (T (3*m) k : ZMod 3) = (if k % 3 = 0 then (T m (k/3) : ZMod 3) else 0) := by
  unfold T
  have h1 := zmod_choose_3m_k m k
  by_cases hk : k % 3 = 0
  · rw [if_pos hk] at h1 ⊢
    let q := k/3
    have hkdecomp : k = 3*q := by
      dsimp [q]
      conv_lhs => rw [← Nat.mod_add_div k 3]
      rw [hk]
      omega
    have hqdiv : (3*q)/3 = q := by omega
    rw [hkdecomp] at h1 ⊢
    simp only [hqdiv] at h1 ⊢
    have h2 := zmod_choose_3m_plus_3q m q
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [h1, h2]
  · rw [if_neg hk] at h1 ⊢
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [h1]
    ring

lemma sum_filter_triples (m : ℕ) (f : ℕ → ZMod 3) :
    (∑ k ∈ Finset.range (3*m + 1), if k % 3 = 0 then f (k/3) else 0)
      = ∑ q ∈ Finset.range (m+1), f q := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun q _ => 3*q) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_range, mem_filter]
    simp only [mem_range] at hq
    constructor
    · omega
    · simp [Nat.mul_mod_right]
  · intro a ha b hb h
    have hv : 3 * a = 3 * b := h
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    have hkdecomp : 3 * (k/3) = k := by
      conv_rhs => rw [← Nat.mod_add_div k 3]
      rw [hk.2]
      omega
    refine ⟨k/3, ?_, ?_⟩
    · have hbound : 3 * (k/3) < 3 * m + 1 := by
        rw [hkdecomp]
        exact hk.1
      simp only [mem_range]
      omega
    · exact hkdecomp
  · intro q hq
    have hdiv : (3*q)/3 = q := by omega
    simp [hdiv]

lemma A3_eq_A_zmod (m : ℕ) : (A005259' (3*m) : ZMod 3) = (A005259' m : ZMod 3) := by
  unfold A005259'
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  have hterm : ∀ k, ((↑((3 * m).choose k) : ZMod 3) ^ 2 * (↑((3 * m + k).choose k) : ZMod 3) ^ 2)
      = if k % 3 = 0 then ((T m (k/3) : ℕ) : ZMod 3) else 0 := by
    intro k
    simpa [T, Nat.cast_mul, Nat.cast_pow] using zmod_T_3m_k m k
  rw [Finset.sum_congr rfl (fun k hk => hterm k)]
  simpa [T, Nat.cast_mul, Nat.cast_pow] using sum_filter_triples m (fun q => (T m q : ZMod 3))

lemma zmod_choose_3m_r_k (m r k : ℕ) (hr : r < 3) :
    ((3*m+r).choose k : ZMod 3) = ((r.choose (k%3) : ZMod 3) * (m.choose (k/3) : ZMod 3)) := by
  have h := choose_mod3_lucas1 (3*m+r) k
  have hmod : (3*m+r) % 3 = r := by omega
  have hdiv : (3*m+r) / 3 = m := by omega
  rw [hmod, hdiv] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h

lemma zmod_choose_no_carry (m q r s : ℕ) (h : r + s < 3) :
    ((3*m+r + (3*q+s)).choose (3*q+s) : ZMod 3)
      = (((r+s).choose s : ZMod 3) * ((m+q).choose q : ZMod 3)) := by
  have hl := choose_mod3_lucas1 (3*m+r + (3*q+s)) (3*q+s)
  have hmodtop : (3*m+r + (3*q+s)) % 3 = r+s := by omega
  have hdivtop : (3*m+r + (3*q+s)) / 3 = m+q := by omega
  have hmodbot : (3*q+s) % 3 = s := by omega
  have hdivbot : (3*q+s) / 3 = q := by omega
  rw [hmodtop, hdivtop, hmodbot, hdivbot] at hl
  exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 hl

lemma zmod_T_3m1_k (m k : ℕ) :
    (T (3*m+1) k : ZMod 3) = (if k % 3 = 2 then 0 else (T m (k/3) : ZMod 3)) := by
  unfold T
  have h1 := zmod_choose_3m_r_k m 1 k (by norm_num)
  rcases Nat.mod_lt k (by norm_num : 0 < 3) with hlt
  interval_cases hs : k % 3
  · let q := k/3
    have hk : k = 3*q+0 := by dsimp [q]; conv_lhs => rw [← Nat.mod_add_div k 3]; rw [hs]; omega
    rw [hk] at h1 ⊢
    have hdiv : (3*q+0)/3 = q := by omega
    simp only [hdiv] at h1 ⊢
    have h2 := zmod_choose_no_carry m q 1 0 (by norm_num)
    simp only [Nat.cast_mul, Nat.cast_pow]
    simp at h1 h2
    rw [h1, h2]
    ring
  · let q := k/3
    have hk : k = 3*q+1 := by dsimp [q]; conv_lhs => rw [← Nat.mod_add_div k 3]; rw [hs]; omega
    rw [hk] at h1 ⊢
    have hdiv : (3*q+1)/3 = q := by omega
    simp only [hdiv] at h1 ⊢
    have h2 := zmod_choose_no_carry m q 1 1 (by norm_num)
    simp only [Nat.cast_mul, Nat.cast_pow]
    simp at h1 h2
    rw [h1, h2]
    ring
  · rw [if_pos hs]
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [h1]
    norm_num

lemma zmod_T_3m2_k (m k : ℕ) :
    (T (3*m+2) k : ZMod 3) = (if k % 3 = 0 then (T m (k/3) : ZMod 3) else 0) := by
  unfold T
  have h1 := zmod_choose_3m_r_k m 2 k (by norm_num)
  rcases Nat.mod_lt k (by norm_num : 0 < 3) with hlt
  interval_cases hs : k % 3
  · let q := k/3
    have hk : k = 3*q+0 := by dsimp [q]; conv_lhs => rw [← Nat.mod_add_div k 3]; rw [hs]; omega
    rw [hk] at h1 ⊢
    have hdiv : (3*q+0)/3 = q := by omega
    simp only [hdiv] at h1 ⊢
    have h2 := zmod_choose_no_carry m q 2 0 (by norm_num)
    simp only [Nat.cast_mul, Nat.cast_pow]
    simp at h1 h2
    rw [h1, h2]
    ring
  · rw [if_neg (by omega : ¬ k % 3 = 0)]
    -- second binomial is zero mod 3 because of carry in unit digit
    simp only [Nat.cast_mul, Nat.cast_pow]
    -- prove via Lucas directly
    have h2 := choose_mod3_lucas1 (3*m+2+k) k
    have hkmod : k % 3 = 1 := hs
    have htopmod : (3*m+2+k) % 3 = 0 := by omega
    have hbotmod : k % 3 = 1 := hs
    rw [htopmod, hbotmod] at h2
    have hz : Nat.choose 0 1 = 0 := by simp
    rw [hz, zero_mul] at h2
    have h2z : (((3*m+2+k).choose k : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_natCast_iff _ _ 3).2 h2
    rw [h2z]
    ring
  · rw [if_neg (by omega : ¬ k % 3 = 0)]
    simp only [Nat.cast_mul, Nat.cast_pow]
    have h2 := choose_mod3_lucas1 (3*m+2+k) k
    have htopmod : (3*m+2+k) % 3 = 1 := by omega
    have hbotmod : k % 3 = 2 := hs
    rw [htopmod, hbotmod] at h2
    have hz : Nat.choose 1 2 = 0 := by simp
    rw [hz, zero_mul] at h2
    have h2z : (((3*m+2+k).choose k : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_natCast_iff _ _ 3).2 h2
    rw [h2z]
    ring
