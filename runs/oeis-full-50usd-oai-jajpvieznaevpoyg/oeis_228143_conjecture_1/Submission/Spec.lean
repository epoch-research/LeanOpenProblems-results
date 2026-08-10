import FormalConjectures.Util.ProblemImports

open BigOperators Matrix Nat

/--
A005259: The auxiliary sequence used for the Hankel matrix, defined as
$$\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$$
-/
def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

/--
A228143: Determinant of the $(n+1) \times (n+1)$ Hankel-type matrix with $(i,j)$-entry equal to A005259$(i+j)$ for all $i,j = 0,\dots,n$.
The entry function A005259 is taken to be $\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dim : Type := Fin (n + 1)
  -- Matrix entries are lifted to ℤ for determinant calculation
  let M : Matrix dim dim ℤ :=
    Matrix.of fun i j => (A005259' (i.val + j.val) : ℤ)
  -- The sequence is known to be non-negative integers (nonn).
  M.det.natAbs

open PowerSeries

/-- The power series $A(x/3) = \sum_{n=0}^\infty \frac{a(n)}{3^n} x^n$ over ℚ. -/
noncomputable def OGF_A_scaled : PowerSeries ℚ :=
  PowerSeries.mk fun n => (a n : ℚ) / (3 ^ n : ℚ)


set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open Finset


lemma central_choose_even (k : ℕ) (hk : 0 < k) : Even ((2*k).choose k) := by
  cases k with
  | zero => omega
  | succ t =>
    use (2*t+1).choose t
    have hsym : (2*t+1).choose (t+1) = (2*t+1).choose t := by
      apply Nat.choose_symm_of_eq_add
      omega
    have htwo : 2 * (t+1) = (2*t+1).succ := by omega
    calc
      (2*(t+1)).choose (t+1) = ((2*t+1).succ).choose (t+1) := by rw [htwo]
      _ = (2*t+1).choose t + (2*t+1).choose (t+1) := Nat.choose_succ_succ (2*t+1) t
      _ = (2*t+1).choose t + (2*t+1).choose t := by rw [hsym]

lemma choose_prod_even {n k : ℕ} (hk : 0 < k) : Even (n.choose k * (n+k).choose k) := by
  by_cases hkn : k ≤ n
  · have hident : n.choose k * (n+k).choose k = (n+k).choose (2*k) * (2*k).choose k := by
      have h := Nat.choose_mul (n := n+k) (k := 2*k) (s := k) (by omega : k ≤ 2*k)
      have hsub1 : n + k - k = n := by omega
      have hsub2 : 2 * k - k = k := by omega
      calc
        n.choose k * (n+k).choose k = (n+k).choose k * n.choose k := by ring
        _ = (n+k).choose k * ((n+k)-k).choose ((2*k)-k) := by rw [hsub1, hsub2]
        _ = (n+k).choose (2*k) * (2*k).choose k := h.symm
    rw [hident]
    exact Even.mul_left (central_choose_even k hk) ((n+k).choose (2*k))
  · have hkgt : n < k := by omega
    rw [Nat.choose_eq_zero_of_lt hkgt]
    simp

lemma apery_term_even {n k : ℕ} (hk : 0 < k) :
    Even ((n.choose k)^2 * ((Nat.choose (n + k) k))^2) := by
  have hp : Even (n.choose k * (n+k).choose k) := choose_prod_even hk
  rcases hp with ⟨z, hz⟩
  use 2 * z^2
  calc
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2 = (n.choose k * (n+k).choose k)^2 := by ring
    _ = (z+z)^2 := by rw [hz]
    _ = (2 * z^2) + (2 * z^2) := by ring

lemma A005259_odd (n : ℕ) : Odd (A005259' n) := by
  unfold A005259'
  rw [Finset.sum_eq_add_sum_diff_singleton (show (0:ℕ) ∈ Finset.range (n+1) by simp)]
  simp
  have heven : Even (∑ x ∈ Finset.range (n + 1) \ {0}, (n.choose x)^2 * ((n + x).choose x)^2) := by
    apply Finset.even_sum
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hk
    exact apery_term_even (Nat.pos_of_ne_zero hk.2)
  rcases heven with ⟨z, hz⟩
  use z
  rw [hz]
  omega


def T (n k : ℕ) : ℕ := (n.choose k)^2 * ((Nat.choose (n+k) k))^2

lemma A005259'_eq_sum_T (n : ℕ) : A005259' n = Finset.sum (Finset.range (n+1)) (fun k => T n k) := by rfl

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
    have h4 : (4 : ZMod 3) = 1 := by decide
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
  rw [A005259'_eq_sum_T]
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
  rw [A005259'_eq_sum_T]
  simp only [Nat.cast_sum]
  let S : ZMod 3 := ∑ q ∈ range (m + 1), ((T m q : ℕ) : ZMod 3)
  change S + S = -S
  have h2 : (2 : ZMod 3) = -1 := by decide
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
  rw [A005259'_eq_sum_T]
  simp only [Nat.cast_sum]
  have hterm : ∀ k, ((T (3*m+2) k : ℕ) : ZMod 3) = if k % 3 = 0 then ((T m (k/3) : ℕ) : ZMod 3) else 0 := zmod_T_3m2_k m
  rw [Finset.sum_congr rfl (fun k hk => hterm k)]
  rw [A005259'_eq_sum_T]
  simp only [Nat.cast_sum]
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
  rw [A005259'_eq_sum_T]
  simp only [Nat.cast_sum]
  have hterm : ∀ k, ((T (3*m) k : ℕ) : ZMod 3) = if k % 3 = 0 then ((T m (k/3) : ℕ) : ZMod 3) else 0 := zmod_T_3m_k0 m
  rw [Finset.sum_congr rfl (fun k hk => hterm k)]
  rw [A005259'_eq_sum_T]
  simp only [Nat.cast_sum]
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


-- reuse definitions from scratch by copying minimal rowOp and determinant-divisibility lemmas
noncomputable def rowOp (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℤ :=
  Matrix.of fun i k => if k = i then (1:ℤ) else if (0 < i.val ∧ k.val + 1 = i.val) then 1 else 0

lemma rowOp_lower (N : ℕ) : (rowOp N).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hlt : i < j := by simpa using hij
  have hne : ¬ j = i := by exact ne_of_gt hlt
  simp only [rowOp, Matrix.of_apply, if_neg hne]
  by_cases hpos : 0 < i.val
  · rw [if_neg]
    intro hk
    have hv : i.val < j.val := by exact hlt
    omega
  · rw [if_neg]
    intro h
    exact hpos h.1

lemma det_rowOp (N : ℕ) : (rowOp N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [rowOp]
  · exact rowOp_lower N

lemma rowOp_mul_apply_pos {N : ℕ} (M : Matrix (Fin (N+1)) (Fin (N+1)) ℤ)
    {i : Fin (N+1)} (hi : 0 < i.val) (j : Fin (N+1)) :
    (rowOp N * M) i j = M i j + M ⟨i.val - 1, by omega⟩ j := by
  rw [Matrix.mul_apply]
  let p : Fin (N+1) := ⟨i.val - 1, by omega⟩
  have hp_ne : p ≠ i := by
    intro h
    have : p.val = i.val := congrArg Fin.val h
    dsimp [p] at this
    omega
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
  rw [show rowOp N i i = 1 by simp [rowOp]]
  simp only [one_mul]
  rw [Finset.sum_eq_single p]
  · have hpval : rowOp N i p = 1 := by
      have hne : ¬ p = i := hp_ne
      have hp : 0 < i.val ∧ p.val + 1 = i.val := by
        constructor
        · exact hi
        · dsimp [p]; omega
      change (if p = i then (1 : ℤ) else if (0 < i.val ∧ p.val + 1 = i.val) then 1 else 0) = 1
      rw [if_neg hne, if_pos hp]
    rw [hpval]
    ring
  · intro k hk hkp
    have hki : k ≠ i := by simpa using hk
    have hpred : ¬ (0 < i.val ∧ k.val + 1 = i.val) := by
      intro h
      have kval : k.val = p.val := by dsimp [p]; omega
      apply hkp
      exact Fin.ext kval
    have hz : rowOp N i k = 0 := by
      simp only [rowOp, Matrix.of_apply]
      rw [if_neg hki]
      rw [if_neg hpred]
    rw [hz]
    simp
  · intro hpnot
    exfalso
    apply hpnot
    simp [p, hp_ne]

lemma prod_fin_pos_const (N : ℕ) (d : ℤ) :
    (∏ i : Fin (N+1), (if 0 < i.val then d else 1)) = d ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.prod_univ_castSucc]
    have hprod : (∏ i : Fin (N+1), (if 0 < i.castSucc.val then d else 1)) = d ^ N := by
      simpa using ih
    rw [hprod]
    simp [Fin.val_last, pow_succ]

lemma det_dvd_of_rows_dvd {N : ℕ} (M : Matrix (Fin (N+1)) (Fin (N+1)) ℤ) (d : ℤ) (hd : d ≠ 0)
    (h : ∀ i : Fin (N+1), 0 < i.val → ∀ j, d ∣ M i j) :
    d ^ N ∣ M.det := by
  let Q : Matrix (Fin (N+1)) (Fin (N+1)) ℤ :=
    Matrix.of fun i j => if hi : 0 < i.val then M i j / d else M i j
  let v : Fin (N+1) → ℤ := fun i => if 0 < i.val then d else 1
  have hM : M = Matrix.of fun i j => v i * Q i j := by
    ext i j
    dsimp [v, Q]
    by_cases hi : 0 < i.val
    · simp [hi]
      obtain ⟨z, hz⟩ := h i hi j
      rw [hz]
      rw [Int.mul_ediv_cancel_left _ hd]
    · simp [hi]
  rw [hM, Matrix.det_mul_column, prod_fin_pos_const]
  exact dvd_mul_right (d ^ N) Q.det

lemma int_dvd_natAbs {c : ℕ} {z : ℤ} (h : (c : ℤ) ∣ z) : c ∣ z.natAbs := by
  obtain ⟨w, hw⟩ := h
  use w.natAbs
  rw [hw]
  simp [Int.natAbs_mul]

lemma dvd_det_natAbs_large (N : ℕ) (hN : 4 ≤ N) (B : ℕ → ℕ)
    (h6 : ∀ m, (6 : ℤ) ∣ (B (m+1) : ℤ) + (B m : ℤ)) :
    (16 * 3^N) ∣ (let M : Matrix (Fin (N+1)) (Fin (N+1)) ℤ := Matrix.of fun i j => (B (i.val+j.val) : ℤ); M.det.natAbs) := by
  let M : Matrix (Fin (N+1)) (Fin (N+1)) ℤ := Matrix.of fun i j => (B (i.val+j.val) : ℤ)
  let R := rowOp N * M
  have hrows : ∀ i : Fin (N+1), 0 < i.val → ∀ j, (6 : ℤ) ∣ R i j := by
    intro i hi j
    rw [show R i j = M i j + M ⟨i.val-1, by omega⟩ j by exact rowOp_mul_apply_pos M hi j]
    dsimp [M]
    change (6 : ℤ) ∣ (B (i.val + j.val) : ℤ) + (B (i.val - 1 + j.val) : ℤ)
    have hidx : i.val - 1 + j.val + 1 = i.val + j.val := by omega
    rw [← hidx]
    exact h6 (i.val - 1 + j.val)
  have hdetR : (6 : ℤ)^N ∣ R.det := det_dvd_of_rows_dvd R 6 (by norm_num) hrows
  have hdet_eq : R.det = M.det := by
    dsimp [R]
    rw [Matrix.det_mul, det_rowOp, one_mul]
  rw [hdet_eq] at hdetR
  have hmain_int : ((16 * 3^N : ℕ) : ℤ) ∣ M.det := by
    have hfactor : ((16 * 3^N : ℕ) : ℤ) ∣ (6 : ℤ)^N := by
      use (2:ℤ)^(N-4)
      norm_num [pow_succ]
      -- need arithmetic powers: 6^N = 16*3^N*2^(N-4) for N>=4
      have hpow : (6:ℤ)^N = (2:ℤ)^N * (3:ℤ)^N := by
        rw [show (6:ℤ) = 2*3 by norm_num, mul_pow]
      rw [hpow]
      norm_num
      have h2 : (2:ℤ)^N = 16 * (2:ℤ)^(N-4) := by
        rw [show N = 4 + (N-4) by omega]
        rw [pow_add]
        norm_num
      rw [h2]
      ring
    exact dvd_trans hfactor hdetR
  exact int_dvd_natAbs hmain_int


lemma coeff_error_high_int (n : ℕ) (S : PowerSeries ℤ) (c : ℤ) :
    PowerSeries.coeff (n+1) ((PowerSeries.monomial (n+1) c)^2 * S) = 0 := by
  rw [PowerSeries.monomial_eq_C_mul_X_pow]
  rw [show (PowerSeries.C c * (PowerSeries.X : PowerSeries ℤ) ^ (n+1)) ^ 2 * S =
      ((PowerSeries.C c)^2 * S) * (PowerSeries.X : PowerSeries ℤ) ^ (2*(n+1)) by ring]
  rw [PowerSeries.coeff_mul_X_pow']
  have h : n + 1 < 2 * (n + 1) := by omega
  simp [h]

lemma coeff_pow7_mul_monomial_high_int (n : ℕ) (P : PowerSeries ℤ) (c : ℤ)
    (hP0 : PowerSeries.coeff 0 P = 1) :
    PowerSeries.coeff (n+1) (P ^ 7 * PowerSeries.monomial (n+1) c) = c := by
  rw [PowerSeries.monomial_eq_C_mul_X_pow]
  rw [← mul_assoc]
  rw [PowerSeries.coeff_mul_X_pow']
  have hc : PowerSeries.constantCoeff P = 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hP0
  simp [hc]

lemma coeff_pow8_add_monomial_high_int (n : ℕ) (P : PowerSeries ℤ) (c : ℤ)
    (hP0 : PowerSeries.coeff 0 P = 1) :
    PowerSeries.coeff (n+1) ((P + PowerSeries.monomial (n+1) c) ^ 8)
      = PowerSeries.coeff (n+1) (P ^ 8) + 8 * c := by
  let M : PowerSeries ℤ := PowerSeries.monomial (n+1) c
  let S : PowerSeries ℤ :=
    28 • P^6 + 56 • (P^5*M) + 70 • (P^4*M^2) + 56 • (P^3*M^3) +
    28 • (P^2*M^4) + 8 • (P*M^5) + M^6
  have hid : (P + M)^8 = P^8 + 8 • (P^7 * M) + M^2 * S := by
    dsimp [S]
    ring
  change PowerSeries.coeff (n+1) ((P + M)^8) = PowerSeries.coeff (n+1) (P^8) + 8*c
  rw [hid]
  simp only [map_add, map_nsmul]
  rw [coeff_pow7_mul_monomial_high_int n P c hP0]
  have herr : PowerSeries.coeff (n+1) (M^2 * S) = 0 := by
    dsimp [M]
    exact coeff_error_high_int n S c
  rw [herr]
  simp

lemma coeff_pos_pow8_one_add_two_dvd16_int (E : PowerSeries ℤ) {m : ℕ} (hm : 0 < m) :
    (16 : ℤ) ∣ PowerSeries.coeff m ((1 + 2 • E) ^ 8) := by
  let S : PowerSeries ℤ := E + 7 • E^2 + 28 • E^3 + 70 • E^4 + 112 • E^5 + 112 • E^6 + 64 • E^7 + 16 • E^8
  have hid : (1 + 2 • E)^8 = 1 + 16 • S := by
    dsimp [S]
    ring
  rw [hid]
  use PowerSeries.coeff m S
  simp [hm.ne']
  change PowerSeries.coeff m (PowerSeries.C (16 : ℤ) * S) = 16 * PowerSeries.coeff m S
  rw [PowerSeries.coeff_C_mul]

noncomputable def rootCoeff16 (d : ℕ → ℤ) : ℕ → ℤ
| 0 => 1
| n+1 =>
    ((16 * d (n+1) - PowerSeries.coeff (n+1)
      ((PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0 : PowerSeries ℤ) ^ 8)) / 8)
termination_by n => n

lemma rootCoeff16_zero (d : ℕ → ℤ) : rootCoeff16 d 0 = 1 := rootCoeff16.eq_1 d

lemma partial_const16 (d : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff 0 (PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0 : PowerSeries ℤ) = 1 := by
  simp [rootCoeff16_zero]

lemma partial_as_one_add_two16 (d : ℕ → ℤ) (n : ℕ)
    (hev : ∀ k, 0 < k → k < n+1 → (2 : ℤ) ∣ rootCoeff16 d k) :
    ∃ E : PowerSeries ℤ, (PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0 : PowerSeries ℤ) = 1 + 2 • E := by
  let E : PowerSeries ℤ := PowerSeries.mk fun k => if k = 0 then 0 else ((if h : k < n+1 then rootCoeff16 d k else 0 : ℤ) / 2)
  refine ⟨E, ?_⟩
  ext k
  by_cases hk0 : k = 0
  · subst hk0
    simp [E, rootCoeff16_zero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    by_cases hkn : k < n+1
    · obtain ⟨z, hz⟩ := hev k hkpos hkn
      have hklen : k ≤ n := by omega
      simp only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_mk, PowerSeries.coeff_smul]
      simp [E, hk0, hkn, hklen, hz]
    · have hklen : ¬ k ≤ n := by omega
      simp only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_mk, PowerSeries.coeff_smul]
      simp [E, hk0, hkn, hklen]

lemma partial_pow8_coeff_dvd16_16 (d : ℕ → ℤ) (n : ℕ)
    (hev : ∀ k, 0 < k → k < n+1 → (2 : ℤ) ∣ rootCoeff16 d k) :
    (16 : ℤ) ∣ PowerSeries.coeff (n+1)
      ((PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0 : PowerSeries ℤ) ^ 8) := by
  obtain ⟨E, hE⟩ := partial_as_one_add_two16 d n hev
  rw [hE]
  exact coeff_pos_pow8_one_add_two_dvd16_int E (Nat.succ_pos n)

lemma div16_sub_div8_eq (a z : ℤ) : (16 * a - 16 * z) / 8 = 2 * (a - z) := by
  rw [show 16 * a - 16 * z = 8 * (2 * (a - z)) by ring]
  rw [Int.mul_ediv_cancel_left]
  norm_num

lemma rootCoeff16_even_pos (d : ℕ → ℤ) : ∀ n, 0 < n → (2 : ℤ) ∣ rootCoeff16 d n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ m =>
      rw [rootCoeff16.eq_2]
      have hev : ∀ k, 0 < k → k < m+1 → (2 : ℤ) ∣ rootCoeff16 d k := by
        intro k hkpos hkm
        exact ih k (by omega) hkpos
      obtain ⟨z, hz⟩ := partial_pow8_coeff_dvd16_16 d m hev
      rw [hz, div16_sub_div8_eq]
      simpa [mul_comm] using dvd_mul_left 2 (d (m+1) - z)

lemma coeff_pow_eq_coeff_trunc_pow16 {m a : ℕ} (f : PowerSeries ℤ) :
    PowerSeries.coeff m (f^a) = PowerSeries.coeff m (((PowerSeries.trunc (m+1) f : Polynomial ℤ) : PowerSeries ℤ)^a) := by
  rw [← PowerSeries.coeff_coe_trunc_of_lt (f := f^a) (n := m) (m := m+1) (Nat.lt_succ_self m)]
  rw [← PowerSeries.coeff_coe_trunc_of_lt (f := (((PowerSeries.trunc (m+1) f : Polynomial ℤ) : PowerSeries ℤ)^a)) (n := m) (m := m+1) (Nat.lt_succ_self m)]
  congr 1
  exact congr_arg (fun p : Polynomial ℤ => (p : PowerSeries ℤ)) (PowerSeries.trunc_trunc_pow f (m+1) a).symm

lemma coeff_eq_of_trunc_eq_pow8 {m : ℕ} {f g : PowerSeries ℤ}
    (h : PowerSeries.trunc (m+1) f = PowerSeries.trunc (m+1) g) :
    PowerSeries.coeff m (f^8) = PowerSeries.coeff m (g^8) := by
  rw [coeff_pow_eq_coeff_trunc_pow16 (m := m) (a := 8) f]
  rw [coeff_pow_eq_coeff_trunc_pow16 (m := m) (a := 8) g]
  rw [h]

lemma trunc_C_eq_partial_add_monomial (d : ℕ → ℤ) (n : ℕ) :
    PowerSeries.trunc (n+2) (PowerSeries.mk (rootCoeff16 d)) =
    PowerSeries.trunc (n+2)
      ((PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0 : PowerSeries ℤ)
        + PowerSeries.monomial (n+1) (rootCoeff16 d (n+1))) := by
  ext k
  simp only [map_add, Polynomial.coeff_add, PowerSeries.coeff_trunc, PowerSeries.coeff_mk,
    PowerSeries.coeff_monomial]
  by_cases hk : k < n + 2
  · simp [hk]
    have hle : k ≤ n+1 := by omega
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have hne : k ≠ n+1 := by omega
      simp [hlt, hne]
      intro hbad
      omega
    · subst heq
      simp
  · simp [hk]

lemma rootCoeff16_spec_int (d : ℕ → ℤ) :
    (PowerSeries.mk (rootCoeff16 d) : PowerSeries ℤ) ^ 8 =
      PowerSeries.mk fun n => if n = 0 then 1 else 16 * d n := by
  ext m
  cases m with
  | zero =>
    simp [rootCoeff16_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    let P : PowerSeries ℤ := PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0
    let c : ℤ := rootCoeff16 d (n+1)
    have hcoeff : PowerSeries.coeff (n+1) ((PowerSeries.mk (rootCoeff16 d) : PowerSeries ℤ)^8)
        = PowerSeries.coeff (n+1) ((P + PowerSeries.monomial (n+1) c)^8) := by
      apply coeff_eq_of_trunc_eq_pow8
      dsimp [P, c]
      exact trunc_C_eq_partial_add_monomial d n
    rw [hcoeff]
    have hP0 : PowerSeries.coeff 0 P = 1 := by dsimp [P]; exact partial_const16 d n
    rw [coeff_pow8_add_monomial_high_int n P c hP0]
    dsimp [c]
    have hev : ∀ k, 0 < k → k < n+1 → (2 : ℤ) ∣ rootCoeff16 d k := by
      intro k hkpos hkn
      exact rootCoeff16_even_pos d k hkpos
    obtain ⟨z, hz⟩ := partial_pow8_coeff_dvd16_16 d n hev
    dsimp [P] at hz
    change PowerSeries.coeff (n+1) (P^8) = 16 * z at hz
    rw [rootCoeff16.eq_2]
    change PowerSeries.coeff (n+1) (P ^ 8) +
      8 * ((16 * d (n+1) - PowerSeries.coeff (n+1) (P ^ 8)) / 8) =
      PowerSeries.coeff (n+1) (PowerSeries.mk fun n => if n = 0 then 1 else 16 * d n)
    rw [hz, div16_sub_div8_eq]
    simp
    ring

/--
A228143 Conjecture: if $A(x) = 1 + 48*x + 161856*x^2 + \dots$ denotes the o.g.f. then
$A(x/3)^{1/8}$ has integer coefficients (checked up to $x^{30}$).

This is formalized as: there exists a power series $C(x)$ over $\mathbb{Z}$ such that $C(x)^8 = A(x/3)$.
The map `PowerSeries.map (Int.castRingHom ℚ)` lifts the power series from $\mathbb{Z}[[X]]$ to $\mathbb{Q}[[X]]$.
-/
theorem oeis_228143_conjecture_1 :
    ∃ C : PowerSeries ℤ,
      (PowerSeries.map (Int.castRingHom ℚ)) (C ^ 8) = OGF_A_scaled := by
  classical
  have h6 : ∀ m : ℕ, (6 : ℤ) ∣ (A005259' (m+1) : ℤ) + (A005259' m : ℤ) := by
    intro m
    have h2even : Even (A005259' (m+1) + A005259' m) := by
      exact Odd.add_odd (A005259_odd (m+1)) (A005259_odd m)
    have h2 : 2 ∣ A005259' (m+1) + A005259' m := by
      simpa [even_iff_two_dvd] using h2even
    have h3a := three_dvd_adjacent m
    have h3 : 3 ∣ A005259' (m+1) + A005259' m := by
      simpa [add_comm] using h3a
    have h6nat : 6 ∣ A005259' (m+1) + A005259' m := by
      simpa using (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3)
    exact_mod_cast h6nat
  have hdiv_pos : ∀ n : ℕ, 0 < n → (16 * 3^n) ∣ a n := by
    intro n hn
    rcases lt_or_ge n 4 with hnlt | hnge
    · interval_cases n
      · unfold a; simp only; rw [Matrix.det_fin_two]; decide
      · unfold a; simp only; rw [Matrix.det_fin_three]; decide
      · unfold a; simp only; rw [Matrix.det_apply]; decide
    · exact dvd_det_natAbs_large n hnge A005259' h6
  have ha0 : a 0 = 1 := by
    unfold a
    simp only
    rw [Matrix.det_fin_one]
    decide
  let d : ℕ → ℤ := fun n => if n = 0 then 0 else ((a n / (16 * 3^n) : ℕ) : ℤ)
  refine ⟨PowerSeries.mk (rootCoeff16 d), ?_⟩
  ext n
  rw [PowerSeries.coeff_map]
  have hroot := congr_arg (PowerSeries.coeff n) (rootCoeff16_spec_int d)
  simp only [PowerSeries.coeff_mk] at hroot
  rw [hroot]
  unfold OGF_A_scaled
  rw [PowerSeries.coeff_mk]
  by_cases hn0 : n = 0
  · subst hn0
    simp [ha0]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hdvd := hdiv_pos n hnpos
    have hcoeff : (a n : ℚ) / (3^n : ℚ) = (16 * (a n / (16 * 3^n)) : ℕ) := by
      have hmul : (16 * 3^n) * (a n / (16 * 3^n)) = a n := Nat.mul_div_cancel' hdvd
      rw [← hmul]
      norm_num
      field_simp [pow_ne_zero n (by norm_num : (3:ℚ) ≠ 0)]
    rw [hcoeff]
    simp [d, hn0]
    norm_cast
