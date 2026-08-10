import FormalConjectures.Util.ProblemImports
open BigOperators Nat Finset
set_option maxHeartbeats 0

def T (n k : ℕ) : ℕ := (n.choose k)^2 * ((Nat.choose (n+k) k))^2

lemma choose_mod3_lucas1 (n k : ℕ) :
    n.choose k ≡ (n % 3).choose (k % 3) * (n / 3).choose (k / 3) [MOD 3] := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 3)

lemma zmod_choose_3m_r_k (m r k : ℕ) (hr : r < 3) :
    ((3*m+r).choose k : ZMod 3) = ((r.choose (k%3) : ZMod 3) * (m.choose (k/3) : ZMod 3)) := by
  have h := choose_mod3_lucas1 (3*m+r) k
  have hmod : (3*m+r) % 3 = r := by omega
  have hdiv : (3*m+r) / 3 = m := by omega
  rw [hmod, hdiv] at h
  have hz : ((3*m+r).choose k : ZMod 3) = (((r.choose (k%3) * m.choose (k/3) : ℕ) : ZMod 3)) :=
    (ZMod.natCast_eq_natCast_iff _ _ 3).2 h
  simpa [Nat.cast_mul] using hz

lemma zmod_choose_second_3m1_s0 (m q : ℕ) :
    ((3*m+1 + (3*q+0)).choose (3*q+0) : ZMod 3) = ((m+q).choose q : ZMod 3) := by
  have h := choose_mod3_lucas1 (3*m+1 + (3*q+0)) (3*q+0)
  have htmod : (3*m+1 + (3*q+0)) % 3 = 1 := by omega
  have htdiv : (3*m+1 + (3*q+0)) / 3 = m+q := by omega
  have hbmod : (3*q+0) % 3 = 0 := by omega
  have hbdiv : (3*q+0) / 3 = q := by omega
  rw [htmod, htdiv, hbmod, hbdiv] at h
  norm_num at h
  exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h

lemma zmod_choose_second_3m1_s1 (m q : ℕ) :
    ((3*m+1 + (3*q+1)).choose (3*q+1) : ZMod 3) = (2 : ZMod 3) * ((m+q).choose q : ZMod 3) := by
  have h := choose_mod3_lucas1 (3*m+1 + (3*q+1)) (3*q+1)
  have htmod : (3*m+1 + (3*q+1)) % 3 = 2 := by omega
  have htdiv : (3*m+1 + (3*q+1)) / 3 = m+q := by omega
  have hbmod : (3*q+1) % 3 = 1 := by omega
  have hbdiv : (3*q+1) / 3 = q := by omega
  rw [htmod, htdiv, hbmod, hbdiv] at h
  norm_num at h
  have hz : ((3*m+1 + (3*q+1)).choose (3*q+1) : ZMod 3) = (((2 * (m+q).choose q : ℕ) : ZMod 3)) :=
    (ZMod.natCast_eq_natCast_iff _ _ 3).2 h
  simpa [Nat.cast_mul] using hz

lemma zmod_choose_second_3m1_s2 (m q : ℕ) :
    ((3*m+1 + (3*q+2)).choose (3*q+2) : ZMod 3) = 0 := by
  have h := choose_mod3_lucas1 (3*m+1 + (3*q+2)) (3*q+2)
  have htmod : (3*m+1 + (3*q+2)) % 3 = 0 := by omega
  have hbmod : (3*q+2) % 3 = 2 := by omega
  rw [htmod, hbmod] at h
  norm_num at h
  exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h

lemma k_decomp_mod3 (k s : ℕ) (hs : k % 3 = s) : k = 3*(k/3)+s := by
  calc
    k = k % 3 + 3*(k/3) := (Nat.mod_add_div k 3).symm
    _ = 3*(k/3)+s := by rw [hs]; omega

lemma zmod_T_3m1_k (m k : ℕ) :
    (T (3*m+1) k : ZMod 3) = (if k % 3 = 2 then 0 else (T m (k/3) : ZMod 3)) := by
  unfold T
  have h1 := zmod_choose_3m_r_k m 1 k (by norm_num)
  have hlt := Nat.mod_lt k (by norm_num : 0 < 3)
  interval_cases hs : k % 3
  · let q := k/3
    have hk : k = 3*q+0 := by dsimp [q]; simpa [add_comm] using k_decomp_mod3 k 0 hs
    rw [hk] at h1 ⊢
    have hdiv : (3*q+0)/3 = q := by omega
    simp only [hdiv] at h1 ⊢
    have h2 := zmod_choose_second_3m1_s0 m q
    simp only [Nat.cast_mul, Nat.cast_pow]
    simp at h1
    have h1' : (↑((3 * m + 1).choose (3*q+0)) : ZMod 3) = ↑(m.choose q) := by simpa using h1
    rw [h1', h2]
    simp
  · let q := k/3
    have hk : k = 3*q+1 := by dsimp [q]; exact k_decomp_mod3 k 1 hs
    rw [hk] at h1 ⊢
    have hdiv : (3*q+1)/3 = q := by omega
    simp only [hdiv] at h1 ⊢
    have h2 := zmod_choose_second_3m1_s1 m q
    simp only [Nat.cast_mul, Nat.cast_pow]
    simp at h1
    rw [h1, h2]
    rw [if_neg (by norm_num : (1:ℕ) ≠ 2)]
    ring_nf
    have h4 : (4 : ZMod 3) = 1 := by native_decide
    rw [h4]
    ring
  · simp only [Nat.cast_mul, Nat.cast_pow]
    simp [hs] at h1 ⊢
    rw [h1]
    norm_num

lemma zmod_choose_second_3m2_s0 (m q : ℕ) :
    ((3*m+2 + (3*q+0)).choose (3*q+0) : ZMod 3) = ((m+q).choose q : ZMod 3) := by
  have h := choose_mod3_lucas1 (3*m+2 + (3*q+0)) (3*q+0)
  have htmod : (3*m+2 + (3*q+0)) % 3 = 2 := by omega
  have htdiv : (3*m+2 + (3*q+0)) / 3 = m+q := by omega
  have hbmod : (3*q+0) % 3 = 0 := by omega
  have hbdiv : (3*q+0) / 3 = q := by omega
  rw [htmod, htdiv, hbmod, hbdiv] at h
  norm_num at h
  exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h

lemma zmod_second_zero_3m2_s1 (m q : ℕ) :
    ((3*m+2 + (3*q+1)).choose (3*q+1) : ZMod 3) = 0 := by
  have h := choose_mod3_lucas1 (3*m+2 + (3*q+1)) (3*q+1)
  have htmod : (3*m+2 + (3*q+1)) % 3 = 0 := by omega
  have hbmod : (3*q+1) % 3 = 1 := by omega
  rw [htmod, hbmod] at h
  norm_num at h
  exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h

lemma zmod_second_zero_3m2_s2 (m q : ℕ) :
    ((3*m+2 + (3*q+2)).choose (3*q+2) : ZMod 3) = 0 := by
  have h := choose_mod3_lucas1 (3*m+2 + (3*q+2)) (3*q+2)
  have htmod : (3*m+2 + (3*q+2)) % 3 = 1 := by omega
  have hbmod : (3*q+2) % 3 = 2 := by omega
  rw [htmod, hbmod] at h
  norm_num at h
  exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h

lemma zmod_T_3m2_k (m k : ℕ) :
    (T (3*m+2) k : ZMod 3) = (if k % 3 = 0 then (T m (k/3) : ZMod 3) else 0) := by
  unfold T
  have h1 := zmod_choose_3m_r_k m 2 k (by norm_num)
  have hlt := Nat.mod_lt k (by norm_num : 0 < 3)
  interval_cases hs : k % 3
  · let q := k/3
    have hk : k = 3*q+0 := by dsimp [q]; simpa [add_comm] using k_decomp_mod3 k 0 hs
    rw [hk] at h1 ⊢
    have hdiv : (3*q+0)/3 = q := by omega
    simp only [hdiv] at h1 ⊢
    have h2 := zmod_choose_second_3m2_s0 m q
    simp only [Nat.cast_mul, Nat.cast_pow]
    simp at h1
    have h1' : (↑((3 * m + 2).choose (3*q+0)) : ZMod 3) = ↑(m.choose q) := by simpa using h1
    rw [h1', h2]
    simp
  · let q := k/3
    have hk : k = 3*q+1 := by dsimp [q]; exact k_decomp_mod3 k 1 hs
    rw [hk] at h1 ⊢
    have h2 := zmod_second_zero_3m2_s1 m q
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [h2]
    simp
  · let q := k/3
    have hk : k = 3*q+2 := by dsimp [q]; exact k_decomp_mod3 k 2 hs
    rw [hk] at h1 ⊢
    have h2 := zmod_second_zero_3m2_s2 m q
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [h2]
    simp

def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => T n k

lemma sum_filter_residue_b2 (m s : ℕ) (hslt : s < 2) (f : ℕ → ZMod 3) :
    (∑ k ∈ Finset.range (3*m + 2), if k % 3 = s then f (k/3) else 0)
      = ∑ q ∈ Finset.range (m+1), f q := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun q _ => 3*q+s) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, mem_range]
    simp only [mem_range] at hq
    constructor
    · omega
    · omega
  · intro a ha b hb h
    have hv : 3 * a + s = 3 * b + s := h
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    have hkdecomp : 3 * (k/3) + s = k := by
      conv_rhs => rw [← Nat.mod_add_div k 3]
      rw [hk.2]
      omega
    refine ⟨k/3, ?_, ?_⟩
    · have hbound : 3 * (k/3) + s < 3*m + 2 := by
        rw [hkdecomp]
        exact hk.1
      simp only [mem_range]
      omega
    · exact hkdecomp
  · intro q hq
    have hmod : (3*q+s) % 3 = s := by omega
    have hdiv : (3*q+s) / 3 = q := by omega
    simp [hdiv]

lemma A3m1_eq_neg (m : ℕ) : (A005259' (3*m+1) : ZMod 3) = - (A005259' m : ZMod 3) := by
  unfold A005259'
  simp only [Nat.cast_sum]
  have hterm : ∀ k, ((T (3*m+1) k : ℕ) : ZMod 3) = if k % 3 = 2 then 0 else ((T m (k/3) : ℕ) : ZMod 3) := zmod_T_3m1_k m
  rw [Finset.sum_congr rfl (fun k hk => hterm k)]
  have hsplit : (∑ k ∈ range (3*m+2), (if k % 3 = 2 then 0 else ((T m (k/3) : ℕ) : ZMod 3)))
      = (∑ k ∈ range (3*m+2), if k % 3 = 0 then ((T m (k/3) : ℕ) : ZMod 3) else 0)
        + (∑ k ∈ range (3*m+2), if k % 3 = 1 then ((T m (k/3) : ℕ) : ZMod 3) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hlt := Nat.mod_lt k (by norm_num : 0 < 3)
    interval_cases k % 3 <;> simp
  rw [hsplit]
  rw [sum_filter_residue_b2 m 0 (by norm_num) (fun q => ((T m q : ℕ) : ZMod 3))]
  rw [sum_filter_residue_b2 m 1 (by norm_num) (fun q => ((T m q : ℕ) : ZMod 3))]
  let S : ZMod 3 := ∑ q ∈ range (m + 1), ((T m q : ℕ) : ZMod 3)
  change S + S = -S
  have h2 : (2 : ZMod 3) = -1 := by native_decide
  calc
    S + S = (2 : ZMod 3) * S := by ring
    _ = -S := by rw [h2]; ring

lemma sum_filter_residue0_b3 (m : ℕ) (f : ℕ → ZMod 3) :
    (∑ k ∈ Finset.range (3*m + 3), if k % 3 = 0 then f (k/3) else 0)
      = ∑ q ∈ Finset.range (m+1), f q := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun q _ => 3*q) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, mem_range]
    simp only [mem_range] at hq
    constructor
    · omega
    · simp [Nat.mul_mod_right]
  · intro a ha b hb h
    have hv : 3*a = 3*b := h
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    have hkdecomp : 3 * (k/3) = k := by
      conv_rhs => rw [← Nat.mod_add_div k 3]
      rw [hk.2]
      omega
    refine ⟨k/3, ?_, ?_⟩
    · have hbound : 3 * (k/3) < 3*m + 3 := by
        rw [hkdecomp]
        exact hk.1
      simp only [mem_range]
      omega
    · exact hkdecomp
  · intro q hq
    have hdiv : (3*q)/3 = q := by omega
    simp [hdiv]

lemma A3m2_eq (m : ℕ) : (A005259' (3*m+2) : ZMod 3) = (A005259' m : ZMod 3) := by
  unfold A005259'
  simp only [Nat.cast_sum]
  have hterm : ∀ k, ((T (3*m+2) k : ℕ) : ZMod 3) = if k % 3 = 0 then ((T m (k/3) : ℕ) : ZMod 3) else 0 := zmod_T_3m2_k m
  rw [Finset.sum_congr rfl (fun k hk => hterm k)]
  exact sum_filter_residue0_b3 m (fun q => ((T m q : ℕ) : ZMod 3))

lemma zmod_choose_3m_k0 (m k : ℕ) :
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

lemma zmod_choose_second_3m_s0 (m q : ℕ) :
    ((3*m + 3*q).choose (3*q) : ZMod 3) = ((m+q).choose q : ZMod 3) := by
  have h := choose_mod3_lucas1 (3*m+3*q) (3*q)
  have htmod : (3*m+3*q) % 3 = 0 := by omega
  have htdiv : (3*m+3*q) / 3 = m+q := by omega
  have hbmod : (3*q) % 3 = 0 := by simp [Nat.mul_mod_right]
  have hbdiv : (3*q) / 3 = q := by omega
  rw [htmod, htdiv, hbmod, hbdiv] at h
  norm_num at h
  exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 h

lemma zmod_T_3m_k0 (m k : ℕ) :
    (T (3*m) k : ZMod 3) = (if k % 3 = 0 then (T m (k/3) : ZMod 3) else 0) := by
  unfold T
  have h1 := zmod_choose_3m_k0 m k
  by_cases hk : k % 3 = 0
  · rw [if_pos hk] at h1 ⊢
    let q := k/3
    have hkdecomp : k = 3*q := by
      dsimp [q]
      conv_lhs => rw [← Nat.mod_add_div k 3]
      rw [hk]
      omega
    rw [hkdecomp] at h1 ⊢
    have hdiv : (3*q)/3 = q := by omega
    simp only [hdiv] at h1 ⊢
    have h2 := zmod_choose_second_3m_s0 m q
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [h1, h2]
  · rw [if_neg hk] at h1 ⊢
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [h1]
    ring

lemma sum_filter_residue0_b1 (m : ℕ) (f : ℕ → ZMod 3) :
    (∑ k ∈ Finset.range (3*m + 1), if k % 3 = 0 then f (k/3) else 0)
      = ∑ q ∈ Finset.range (m+1), f q := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun q _ => 3*q) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, mem_range]
    simp only [mem_range] at hq
    constructor
    · omega
    · simp [Nat.mul_mod_right]
  · intro a ha b hb h
    have hv : 3*a = 3*b := h
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    have hkdecomp : 3 * (k/3) = k := by
      conv_rhs => rw [← Nat.mod_add_div k 3]
      rw [hk.2]
      omega
    refine ⟨k/3, ?_, ?_⟩
    · have hbound : 3 * (k/3) < 3*m + 1 := by
        rw [hkdecomp]
        exact hk.1
      simp only [mem_range]
      omega
    · exact hkdecomp
  · intro q hq
    have hdiv : (3*q)/3 = q := by omega
    simp [hdiv]

lemma A3m0_eq (m : ℕ) : (A005259' (3*m) : ZMod 3) = (A005259' m : ZMod 3) := by
  unfold A005259'
  simp only [Nat.cast_sum]
  have hterm : ∀ k, ((T (3*m) k : ℕ) : ZMod 3) = if k % 3 = 0 then ((T m (k/3) : ℕ) : ZMod 3) else 0 := zmod_T_3m_k0 m
  rw [Finset.sum_congr rfl (fun k hk => hterm k)]
  exact sum_filter_residue0_b1 m (fun q => ((T m q : ℕ) : ZMod 3))

lemma A_adjacent_zmod_zero : ∀ n : ℕ, (A005259' n : ZMod 3) + (A005259' (n+1) : ZMod 3) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let m := n / 3
    have hlt := Nat.mod_lt n (by norm_num : 0 < 3)
    interval_cases hmod : n % 3
    · have hn : n = 3*m := by
        dsimp [m]
        conv_lhs => rw [← Nat.mod_add_div n 3]
        rw [hmod]
        omega
      rw [hn]
      rw [show 3*m + 1 = 3*m+1 by rfl]
      rw [A3m0_eq m, A3m1_eq_neg m]
      ring
    · have hn : n = 3*m+1 := by
        dsimp [m]
        conv_lhs => rw [← Nat.mod_add_div n 3]
        rw [hmod]
        omega
      rw [hn]
      rw [show 3*m+1+1 = 3*m+2 by omega]
      rw [A3m1_eq_neg m, A3m2_eq m]
      ring
    · have hn : n = 3*m+2 := by
        dsimp [m]
        conv_lhs => rw [← Nat.mod_add_div n 3]
        rw [hmod]
        omega
      have hm_lt : m < n := by
        rw [hn]
        omega
      have ih' := ih m hm_lt
      rw [hn]
      rw [show 3*m+2+1 = 3*(m+1) by omega]
      rw [A3m2_eq m, A3m0_eq (m+1)]
      exact ih'

lemma three_dvd_adjacent (n : ℕ) : 3 ∣ A005259' n + A005259' (n+1) := by
  have h := A_adjacent_zmod_zero n
  rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff] at h
  exact h
