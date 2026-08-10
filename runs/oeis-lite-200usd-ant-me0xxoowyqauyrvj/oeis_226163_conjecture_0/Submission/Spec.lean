import FormalConjectures.Util.ProblemImports

open Matrix Nat Int Finset

-- ===================== DetF.lean =====================


namespace DetF

lemma reindex (n : ℕ) (ζ : ℂ) (i0 : Fin n) :
    ∏ j ∈ Finset.Ioi i0, (ζ ^ ((j : ℕ) - (i0 : ℕ)) - 1)
      = ∏ d ∈ Finset.range (n - 1 - (i0 : ℕ)), (ζ ^ (d + 1) - 1) := by
  refine Finset.prod_bij'
    (fun (j : Fin n) (_ : j ∈ Finset.Ioi i0) => (j : ℕ) - (i0 : ℕ) - 1)
    (fun (d : ℕ) (hd : d ∈ Finset.range (n - 1 - (i0 : ℕ))) =>
        (⟨(i0 : ℕ) + d + 1, by rw [Finset.mem_range] at hd; omega⟩ : Fin n))
    ?_ ?_ ?_ ?_ ?_
  · -- hi
    intro j hj
    rw [Finset.mem_Ioi] at hj
    have h1 : (i0 : ℕ) < (j : ℕ) := hj
    rw [Finset.mem_range]
    show (j : ℕ) - (i0 : ℕ) - 1 < n - 1 - (i0 : ℕ)
    have := j.isLt; omega
  · -- hj
    intro d hd
    rw [Finset.mem_range] at hd
    rw [Finset.mem_Ioi, Fin.lt_def]
    show (i0 : ℕ) < (i0 : ℕ) + d + 1; omega
  · -- left_inv
    intro j hj
    rw [Finset.mem_Ioi] at hj
    have h1 : (i0 : ℕ) < (j : ℕ) := hj
    apply Fin.ext; show (i0 : ℕ) + ((j : ℕ) - (i0 : ℕ) - 1) + 1 = (j : ℕ); omega
  · -- right_inv
    intro d hd
    rw [Finset.mem_range] at hd
    show (i0 : ℕ) + d + 1 - (i0 : ℕ) - 1 = d; omega
  · -- h
    intro j hj
    rw [Finset.mem_Ioi] at hj
    have h1 : (i0 : ℕ) < (j : ℕ) := hj
    have he : (j : ℕ) - (i0 : ℕ) = ((j : ℕ) - (i0 : ℕ) - 1) + 1 := by omega
    rw [he]

lemma per_i (n : ℕ) (ζ : ℂ) (i0 : Fin n) :
    ∏ j ∈ Finset.Ioi i0, (ζ ^ (j : ℕ) - ζ ^ (i0 : ℕ))
      = ζ ^ ((i0 : ℕ) * (n - 1 - (i0 : ℕ))) * ∏ d ∈ Finset.range (n - 1 - (i0 : ℕ)), (ζ ^ (d + 1) - 1) := by
  have hfac : ∀ j ∈ Finset.Ioi i0, ζ ^ (j : ℕ) - ζ ^ (i0 : ℕ)
      = ζ ^ (i0 : ℕ) * (ζ ^ ((j : ℕ) - (i0 : ℕ)) - 1) := by
    intro j hj
    rw [Finset.mem_Ioi] at hj
    have h1 : (i0 : ℕ) < (j : ℕ) := hj
    rw [mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, reindex,
    Fin.card_Ioi, ← pow_mul]

lemma swap (n : ℕ) (ζ : ℂ) :
    ∏ i : Fin n, ∏ d ∈ Finset.range (n - 1 - (i : ℕ)), (ζ ^ (d + 1) - 1)
      = ∏ d ∈ Finset.range (n - 1), (ζ ^ (d + 1) - 1) ^ (n - 1 - d) := by
  have hext : ∀ i : Fin n, ∏ d ∈ Finset.range (n - 1 - (i : ℕ)), (ζ ^ (d + 1) - 1)
      = ∏ d ∈ Finset.range (n - 1), (if d < n - 1 - (i : ℕ) then (ζ ^ (d + 1) - 1) else 1) := by
    intro i
    rw [← Finset.prod_filter]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_range, Finset.mem_filter]
    have := i.isLt
    omega
  simp_rw [hext]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro d hd
  rw [Finset.mem_range] at hd
  rw [← Finset.prod_filter, Finset.prod_const]
  congr 1
  have hb : n - 1 - d < n := by omega
  have hset : Finset.filter (fun x : Fin n => d < n - 1 - (x : ℕ)) Finset.univ
      = Finset.Iio (⟨n - 1 - d, hb⟩ : Fin n) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
    have := x.isLt
    omega
  rw [hset, Fin.card_Iio]

end DetF

namespace Eval

lemma prodAll (m : ℕ) (hm1 : 1 ≤ m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    ∏ e ∈ Finset.range (2 * m - 1), (ζ ^ (e + 1) - 1) = -(2 * m : ℂ) := by
  have hn : 2 * m - 1 + 1 = 2 * m := by omega
  have hζ' : IsPrimitiveRoot ζ (2 * m - 1 + 1) := by rw [hn]; exact hζ
  have h := IsPrimitiveRoot.prod_pow_sub_one_eq_order hζ'
  rw [show ((2 * m - 1 : ℕ) : ℂ) = (2 * m : ℂ) - 1 by push_cast [Nat.cast_sub (by omega : 1 ≤ 2*m)]; ring] at h
  have hpar : ((-1 : ℂ)) ^ (2 * m - 1) = -1 := by
    rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega, pow_succ, pow_mul]
    norm_num
  rw [hpar] at h
  linear_combination -h

lemma pow_m_eq_neg_one (m : ℕ) (hm1 : 1 ≤ m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    ζ ^ m = -1 := by
  have h2 : ζ ^ m * ζ ^ m = 1 := by
    rw [← pow_add, show m + m = 2 * m by ring]; exact hζ.pow_eq_one
  have hne : ζ ^ m ≠ 1 := by
    intro hc
    rw [hζ.pow_eq_one_iff_dvd m] at hc
    have := Nat.le_of_dvd hm1 hc
    omega
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exact absurd h hne
  · exact h

lemma Asq (m : ℕ) (hmodd : Odd m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (∏ e ∈ Finset.range (m - 1), (ζ ^ (e + 1) - 1)) ^ 2
      = (m : ℂ) * ζ ^ (∑ e ∈ Finset.range (m - 1), (e + 1)) := by
  obtain ⟨t, ht⟩ := hmodd
  have hm1 : 1 ≤ m := by omega
  set A : ℂ := ∏ e ∈ Finset.range (m - 1), (ζ ^ (e + 1) - 1) with hA
  have hzne : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hz2m : ζ ^ (2 * m) = 1 := hζ.pow_eq_one
  have hzm : ζ ^ m = -1 := pow_m_eq_neg_one m hm1 ζ hζ
  set W : ℕ := ∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) with hW
  -- the "third" product
  have hthird : (∏ x ∈ Finset.range (m - 1), (ζ ^ (m + 1 + x) - 1))
      = (-1 : ℂ) ^ (m - 1) * ζ ^ W * A := by
    rw [← Finset.prod_range_reflect]
    have hcongr : ∀ x ∈ Finset.range (m - 1),
        ζ ^ (m + 1 + (m - 1 - 1 - x)) - 1
          = (-1 : ℂ) * ζ ^ (2 * m - 1 - x) * (ζ ^ (x + 1) - 1) := by
      intro x hx
      rw [Finset.mem_range] at hx
      have e1 : m + 1 + (m - 1 - 1 - x) = 2 * m - 1 - x := by omega
      have e2 : (2 * m - 1 - x) + (x + 1) = 2 * m := by omega
      have h2m : ζ ^ (2 * m - 1 - x) * ζ ^ (x + 1) = 1 := by
        rw [← pow_add, e2]; exact hz2m
      rw [e1]
      linear_combination h2m
    rw [Finset.prod_congr rfl hcongr]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_pow_eq_pow_sum, ← hW, ← hA]
  -- assemble P = -2m
  have hP : ∏ e ∈ Finset.range (2 * m - 1), (ζ ^ (e + 1) - 1) = -(2 * m : ℂ) := prodAll m hm1 ζ hζ
  have hrange : 2 * m - 1 = (m - 1) + m := by omega
  rw [hrange, Finset.prod_range_add] at hP
  -- second factor cleanup
  have hsecond : (∏ x ∈ Finset.range m, (ζ ^ (m - 1 + x + 1) - 1))
      = (ζ ^ m - 1) * (∏ x ∈ Finset.range (m - 1), (ζ ^ (m + 1 + x) - 1)) := by
    have step1 : (∏ x ∈ Finset.range m, (ζ ^ (m - 1 + x + 1) - 1))
        = ∏ x ∈ Finset.range m, (ζ ^ (m + x) - 1) := by
      apply Finset.prod_congr rfl; intro x hx; rw [show m - 1 + x + 1 = m + x by omega]
    rw [step1]
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [Finset.prod_range_succ', mul_comm]
    congr 1
    · rw [show (m - 1) + 1 + 0 = m by omega]
    · apply Finset.prod_congr rfl; intro x hx
      rw [show (m - 1) + 1 + (x + 1) = m + 1 + x by omega]
  rw [← hA] at hP
  rw [hsecond, hthird, hzm] at hP
  -- hP : A * ((-1 - 1) * ((-1)^(m-1) * ζ^W * A)) = -(2m)
  have hpar : (-1 : ℂ) ^ (m - 1) = 1 := by
    rw [show m - 1 = 2 * t by omega, pow_mul]; norm_num
  rw [hpar] at hP
  -- hP : A * ((-1 - 1) * (1 * ζ^W * A)) = -(2m)
  have hAW : A ^ 2 * ζ ^ W = (m : ℂ) := by
    have heq : A * ((-1 - 1) * (1 * ζ ^ W * A)) = (-2 : ℂ) * (A ^ 2 * ζ ^ W) := by ring
    rw [heq] at hP
    have heq2 : (-2 : ℂ) * (A ^ 2 * ζ ^ W) = (-2 : ℂ) * (m : ℂ) := by rw [hP]; ring
    exact mul_left_cancel₀ (by norm_num : (-2 : ℂ) ≠ 0) heq2
  -- finish
  have hSW : (∑ e ∈ Finset.range (m - 1), (e + 1)) + W = (m - 1) * (2 * m) := by
    rw [hW, ← Finset.sum_add_distrib]
    have hc : ∀ e ∈ Finset.range (m - 1), e + 1 + (2 * m - 1 - e) = 2 * m := by
      intro e he; rw [Finset.mem_range] at he; omega
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hz1 : ζ ^ ((∑ e ∈ Finset.range (m - 1), (e + 1)) + W) = 1 := by
    rw [hSW, mul_comm, pow_mul, hz2m, one_pow]
  apply mul_right_cancel₀ (pow_ne_zero W hzne)
  rw [hAW, mul_assoc, ← pow_add, hz1, mul_one]

/-- base identity: ζ^(2m-1-x) - 1 = -ζ^(2m-1-x) (ζ^(x+1) - 1) -/
lemma base_id (m : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) (x : ℕ) (hx : x < m - 1) :
    ζ ^ (2 * m - 1 - x) - 1 = (-1 : ℂ) * ζ ^ (2 * m - 1 - x) * (ζ ^ (x + 1) - 1) := by
  have e2 : (2 * m - 1 - x) + (x + 1) = 2 * m := by omega
  have h2m : ζ ^ (2 * m - 1 - x) * ζ ^ (x + 1) = 1 := by
    rw [← pow_add, e2]; exact hζ.pow_eq_one
  linear_combination h2m

lemma Qval (m : ℕ) (hmodd : Odd m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    ∏ d ∈ Finset.range (2 * m - 1), (ζ ^ (d + 1) - 1) ^ (2 * m - 1 - d)
      = (-2 : ℂ) ^ m * (-1 : ℂ) ^ (∑ x ∈ Finset.range (m - 1), (x + 1))
        * ζ ^ (∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) * (x + 1))
        * (∏ e ∈ Finset.range (m - 1), (ζ ^ (e + 1) - 1)) ^ (2 * m) := by
  obtain ⟨t, ht⟩ := hmodd
  have hm1 : 1 ≤ m := by omega
  have hzm : ζ ^ m = -1 := pow_m_eq_neg_one m hm1 ζ hζ
  -- split off
  have hrange : 2 * m - 1 = (m - 1) + m := by omega
  rw [hrange, Finset.prod_range_add]
  simp only [← hrange]
  -- second factor: peel x=0
  have hsecond : (∏ x ∈ Finset.range m, (ζ ^ (m - 1 + x + 1) - 1) ^ (2 * m - 1 - (m - 1 + x)))
      = (ζ ^ m - 1) ^ m
        * (∏ x ∈ Finset.range (m - 1), (ζ ^ (m + 1 + x) - 1) ^ (m - 1 - x)) := by
    have step1 : (∏ x ∈ Finset.range m, (ζ ^ (m - 1 + x + 1) - 1) ^ (2 * m - 1 - (m - 1 + x)))
        = ∏ x ∈ Finset.range m, (ζ ^ (m + x) - 1) ^ (m - x) := by
      apply Finset.prod_congr rfl; intro x hx
      rw [Finset.mem_range] at hx
      rw [show m - 1 + x + 1 = m + x by omega, show 2 * m - 1 - (m - 1 + x) = m - x by omega]
    rw [step1]
    have hmm : Finset.range m = Finset.range ((m - 1) + 1) := by rw [show (m - 1) + 1 = m by omega]
    rw [hmm, Finset.prod_range_succ', mul_comm]
    congr 1
    apply Finset.prod_congr rfl; intro x hx
    rw [show m + (x + 1) = m + 1 + x by omega, show m - (x + 1) = m - 1 - x by omega]
  rw [hsecond]
  -- third: reflect
  have hthird : (∏ x ∈ Finset.range (m - 1), (ζ ^ (m + 1 + x) - 1) ^ (m - 1 - x))
      = (-1 : ℂ) ^ (∑ x ∈ Finset.range (m - 1), (x + 1))
        * ζ ^ (∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) * (x + 1))
        * ∏ x ∈ Finset.range (m - 1), (ζ ^ (x + 1) - 1) ^ (x + 1) := by
    rw [← Finset.prod_range_reflect]
    have hc : ∀ x ∈ Finset.range (m - 1),
        (ζ ^ (m + 1 + (m - 1 - 1 - x)) - 1) ^ (m - 1 - (m - 1 - 1 - x))
          = (-1 : ℂ) ^ (x + 1) * ζ ^ ((2 * m - 1 - x) * (x + 1)) * (ζ ^ (x + 1) - 1) ^ (x + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx
      rw [show m + 1 + (m - 1 - 1 - x) = 2 * m - 1 - x by omega,
          show m - 1 - (m - 1 - 1 - x) = x + 1 by omega]
      rw [base_id m ζ hζ x hx, mul_pow, mul_pow, ← pow_mul]
    rw [Finset.prod_congr rfl hc]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        Finset.prod_pow_eq_pow_sum]
  rw [hthird]
  -- combine first product with thirdprod into A^(2m)
  have hcombine : (∏ d ∈ Finset.range (m - 1), (ζ ^ (d + 1) - 1) ^ (2 * m - 1 - d))
      * (∏ x ∈ Finset.range (m - 1), (ζ ^ (x + 1) - 1) ^ (x + 1))
      = (∏ e ∈ Finset.range (m - 1), (ζ ^ (e + 1) - 1)) ^ (2 * m) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro d hd
    rw [Finset.mem_range] at hd
    rw [← pow_add, show (2 * m - 1 - d) + (d + 1) = 2 * m by omega]
  rw [hzm, show (-1 - 1 : ℂ) = -2 by ring, ← hcombine]
  ring

/-- sum of squares -/
lemma sumsq : ∀ N : ℕ, 6 * (∑ i ∈ Finset.range N, i ^ 2) = N * (N - 1) * (2 * N - 1) := by
  intro N
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    rcases k with _ | j
    · simp
    · have e1 : j + 1 - 1 = j := by omega
      have e2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      have e3 : j + 1 + 1 - 1 = j + 1 := by omega
      have e4 : 2 * (j + 1 + 1) - 1 = 2 * j + 3 := by omega
      rw [e1, e2, e3, e4]; ring

lemma h6S (N : ℕ) : 6 * (∑ i ∈ Finset.range N, i * (N - 1 - i)) = N * (N - 1) * (N - 2) := by
  have hpt : ∀ i ∈ Finset.range N, i * (N - 1 - i) = i * (N - 1) - i * i := by
    intro i hi; rw [Nat.mul_sub]
  rw [Finset.sum_congr rfl hpt]
  rw [Finset.sum_tsub_distrib _ (fun i hi => by
    rw [Finset.mem_range] at hi; exact Nat.mul_le_mul le_rfl (by omega))]
  rw [Nat.mul_sub, ← Finset.sum_mul]
  have hsi : (∑ i ∈ Finset.range N, i) * 2 = N * (N - 1) := Finset.sum_range_id_mul_two N
  have hsq : 6 * (∑ i ∈ Finset.range N, i ^ 2) = N * (N - 1) * (2 * N - 1) := sumsq N
  have hii : (∑ i ∈ Finset.range N, i * i) = (∑ i ∈ Finset.range N, i ^ 2) := by
    apply Finset.sum_congr rfl; intro i _; rw [sq]
  rw [hii]
  have h1 : 6 * ((∑ i ∈ Finset.range N, i) * (N - 1)) = 3 * (N - 1) * ((∑ i ∈ Finset.range N, i) * 2) := by
    ring
  rw [h1, hsi, hsq]
  rcases N with _ | _ | k
  · simp
  · simp
  · rw [show k + 1 + 1 - 1 = k + 1 by omega, show 2 * (k + 1 + 1) - 1 = 2 * k + 3 by omega,
        show k + 1 + 1 - 2 = k by omega]
    apply Nat.sub_eq_of_eq_add; ring

lemma h6V (m : ℕ) (hm : 1 ≤ m) :
    6 * (∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) * (x + 1)) = m * (m - 1) * (4 * m + 1) := by
  have hpt : ∀ x ∈ Finset.range (m - 1),
      (2 * m - 1 - x) * (x + 1) = (2 * m - 1) * (x + 1) - x * (x + 1) := by
    intro x hx; rw [Nat.sub_mul]
  rw [Finset.sum_congr rfl hpt]
  rw [Finset.sum_tsub_distrib _ (fun x hx => by
    rw [Finset.mem_range] at hx; exact Nat.mul_le_mul (by omega) le_rfl)]
  rw [Nat.mul_sub, ← Finset.mul_sum]
  have hsi : (∑ i ∈ Finset.range (m - 1), i) * 2 = (m - 1) * (m - 2) := by
    have := Finset.sum_range_id_mul_two (m - 1)
    rw [show m - 1 - 1 = m - 2 by omega] at this; exact this
  have hsq : 6 * (∑ i ∈ Finset.range (m - 1), i ^ 2) = (m - 1) * (m - 2) * (2 * m - 3) := by
    have := sumsq (m - 1)
    rw [show m - 1 - 1 = m - 2 by omega, show 2 * (m - 1) - 1 = 2 * m - 3 by omega] at this
    exact this
  have hS1 : (∑ x ∈ Finset.range (m - 1), (x + 1)) * 2 = (m - 1) * m := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    simp only [smul_eq_mul, mul_one]
    rw [add_mul, hsi]
    rcases m with _ | _ | k
    · omega
    · simp
    · rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 + 1 - 2 = k by omega]; ring
  have h6xx1 : 6 * (∑ x ∈ Finset.range (m - 1), x * (x + 1)) = 2 * m * (m - 1) * (m - 2) := by
    rw [Finset.sum_congr rfl (fun x _ => by ring : ∀ x ∈ Finset.range (m - 1), x * (x + 1) = x ^ 2 + x),
        Finset.sum_add_distrib, Nat.mul_add, hsq]
    rw [show 6 * (∑ i ∈ Finset.range (m - 1), i) = 3 * ((∑ i ∈ Finset.range (m - 1), i) * 2) by ring, hsi]
    rcases m with _ | _ | k
    · omega
    · simp
    · rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 + 1 - 2 = k by omega,
          show 2 * (k + 1 + 1) - 3 = 2 * k + 1 by omega]; ring
  rw [show 6 * ((2 * m - 1) * (∑ x ∈ Finset.range (m - 1), (x + 1)))
        = 3 * (2 * m - 1) * ((∑ x ∈ Finset.range (m - 1), (x + 1)) * 2) by ring, hS1, h6xx1]
  rcases m with _ | _ | k
  · omega
  · simp
  · apply Nat.sub_eq_of_eq_add
    zify [show (1:ℕ) ≤ 2 * (k + 1 + 1) by omega, show (1:ℕ) ≤ k + 1 + 1 by omega,
      show (2:ℕ) ≤ k + 1 + 1 by omega]
    ring

lemma hS1val (m t : ℕ) (ht : m = 2 * t + 1) :
    (∑ x ∈ Finset.range (m - 1), (x + 1)) = t * (2 * t + 1) := by
  have h2 : (∑ x ∈ Finset.range (m - 1), (x + 1)) * 2 = (m - 1) * m := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    simp only [smul_eq_mul, mul_one]
    have hsi := Finset.sum_range_id_mul_two (m - 1)
    rw [add_mul, hsi]
    subst ht
    rw [show 2 * t + 1 - 1 = 2 * t by omega, show 2 * t - 1 = 2 * t - 1 from rfl]
    rcases t with _ | j
    · simp
    · rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]; ring
  subst ht
  have : (∑ x ∈ Finset.range (2 * t + 1 - 1), (x + 1)) * 2 = (t * (2 * t + 1)) * 2 := by
    rw [h2]; rw [show 2 * t + 1 - 1 = 2 * t by omega]; ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) this

lemma expdiv (m t : ℕ) (ht : m = 2 * t + 1) :
    2 * m ∣ ((∑ i ∈ Finset.range (2 * m), i * (2 * m - 1 - i))
           + (∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) * (x + 1))
           + (∑ x ∈ Finset.range (m - 1), (x + 1)) * m) := by
  refine ⟨t * (5 * t + 2), ?_⟩
  have key6 : 6 * ((∑ i ∈ Finset.range (2 * m), i * (2 * m - 1 - i))
           + (∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) * (x + 1))
           + (∑ x ∈ Finset.range (m - 1), (x + 1)) * m)
      = 6 * (2 * m * (t * (5 * t + 2))) := by
    rw [Nat.mul_add, Nat.mul_add, h6S (2 * m), h6V m (by omega), hS1val m t ht]
    subst ht
    rw [show 2 * (2 * t + 1) - 1 = 4 * t + 1 by omega, show 2 * (2 * t + 1) - 2 = 4 * t by omega,
        show 2 * t + 1 - 1 = 2 * t by omega]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) key6

theorem detF (m : ℕ) (hmodd : Odd m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (Matrix.vandermonde (fun a : Fin (2 * m) => ζ ^ (a : ℕ))).det
      = (-1 : ℂ) ^ ((m + 1) / 2) * (2 * m : ℂ) ^ m := by
  obtain ⟨t, ht⟩ := hmodd
  have hm1 : 1 ≤ m := by omega
  have hz2m : ζ ^ (2 * m) = 1 := hζ.pow_eq_one
  rw [Matrix.det_vandermonde]
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => DetF.per_i (2 * m) ζ i)]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, DetF.swap]
  rw [Eval.Qval m ⟨t, ht⟩ ζ hζ, pow_mul, Eval.Asq m ⟨t, ht⟩ ζ hζ]
  rw [Fin.sum_univ_eq_sum_range (fun k => k * (2 * m - 1 - k)) (2 * m)]
  rw [mul_pow, ← pow_mul]
  rw [show (-2 : ℂ) ^ m = (-1) ^ m * 2 ^ m by rw [← neg_one_mul, mul_pow]]
  -- big reassociation
  rw [show (ζ ^ (∑ i ∈ Finset.range (2 * m), i * (2 * m - 1 - i)))
        * ((-1) ^ m * 2 ^ m * (-1) ^ (∑ x ∈ Finset.range (m - 1), (x + 1))
          * ζ ^ (∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) * (x + 1))
          * ((m : ℂ) ^ m * ζ ^ ((∑ x ∈ Finset.range (m - 1), (x + 1)) * m)))
      = ((-1 : ℂ) ^ m * (-1) ^ (∑ x ∈ Finset.range (m - 1), (x + 1)))
        * (2 ^ m * (m : ℂ) ^ m)
        * (ζ ^ (∑ i ∈ Finset.range (2 * m), i * (2 * m - 1 - i))
          * ζ ^ (∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) * (x + 1))
          * ζ ^ ((∑ x ∈ Finset.range (m - 1), (x + 1)) * m)) by ring]
  rw [← pow_add, ← mul_pow]
  rw [show ζ ^ (∑ i ∈ Finset.range (2 * m), i * (2 * m - 1 - i))
          * ζ ^ (∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) * (x + 1))
          * ζ ^ ((∑ x ∈ Finset.range (m - 1), (x + 1)) * m)
        = ζ ^ ((∑ i ∈ Finset.range (2 * m), i * (2 * m - 1 - i))
            + (∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) * (x + 1))
            + (∑ x ∈ Finset.range (m - 1), (x + 1)) * m) by rw [← pow_add, ← pow_add]]
  -- ζ^E = 1
  have hE : ζ ^ ((∑ i ∈ Finset.range (2 * m), i * (2 * m - 1 - i))
            + (∑ x ∈ Finset.range (m - 1), (2 * m - 1 - x) * (x + 1))
            + (∑ x ∈ Finset.range (m - 1), (x + 1)) * m) = 1 := by
    obtain ⟨K, hK⟩ := expdiv m t ht
    rw [hK, pow_mul, hz2m, one_pow]
  rw [hE, mul_one]
  -- sign
  have hsign : (-1 : ℂ) ^ (m + (∑ x ∈ Finset.range (m - 1), (x + 1))) = (-1) ^ ((m + 1) / 2) := by
    rw [hS1val m t ht, show m + t * (2 * t + 1) = (m + 1) / 2 + 2 * (t * (t + 1)) by
      subst ht; rw [show (2 * t + 1 + 1) / 2 = t + 1 by omega]; ring, pow_add, pow_mul]
    norm_num
  rw [hsign]
-- ===================== Crux.lean =====================

open Matrix Finset BigOperators

namespace Crux

noncomputable section

variable {m : ℕ}

/-- Stub for the DetF result (to be replaced by the real `Eval.detF`). -/
theorem detF_stub (m : ℕ) (hmodd : Odd m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (Matrix.vandermonde (fun a : Fin (2 * m) => ζ ^ (a : ℕ))).det
      = (-1 : ℂ) ^ ((m + 1) / 2) * (2 * m : ℂ) ^ m := Eval.detF m hmodd ζ hζ

/-- Index type: `Fin m × Fin 2`, identifying with `ZMod (2m)` via `(k,c) ↦ k + m*c`. -/
abbrev Ix (m : ℕ) := Fin m × Fin 2

/-- The exponent of an index. -/
def ex (x : Ix m) : ℕ := (x.1 : ℕ) + m * (x.2 : ℕ)

/-- The DFT matrix `W (x) (y) = ζ ^ (ex x * ex y)`. -/
def W (ζ : ℂ) : Matrix (Ix m) (Ix m) ℂ := fun x y => ζ ^ (ex x * ex y)

/-- `ex` as a bijection `Ix m ≃ Fin (2*m)`. -/
def exEquiv (m : ℕ) : Ix m ≃ Fin (2 * m) where
  toFun x := ⟨ex x, by
    rcases x with ⟨k, c⟩
    simp only [ex]
    have hk := k.isLt
    have hc := c.isLt
    have : m * (c : ℕ) ≤ m * 1 := Nat.mul_le_mul_left _ (by omega)
    omega⟩
  invFun y := (⟨(y : ℕ) % m, by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; exact absurd y.isLt (by simp)
      · exact Nat.mod_lt _ h⟩, ⟨(y : ℕ) / m, by
      have hy := y.isLt
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hy
      · rw [Nat.div_lt_iff_lt_mul h]; omega⟩)
  left_inv := by
    rintro ⟨k, c⟩
    have hk := k.isLt
    have hmpos : 0 < m := by omega
    ext
    · show ((ex (k, c)) % m) = (k : ℕ)
      simp only [ex]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    · show ((ex (k, c)) / m) = (c : ℕ)
      simp only [ex]
      rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt hk, zero_add]
  right_inv := by
    intro y
    have hy := y.isLt
    have hmpos : 0 < m := by omega
    apply Fin.ext
    show ex ((⟨(y:ℕ) % m, _⟩ : Fin m), (⟨(y:ℕ) / m, _⟩ : Fin 2)) = (y : ℕ)
    simp only [ex]
    exact Nat.mod_add_div _ _

/-- `W` is the reindexed Vandermonde DFT matrix. -/
theorem W_eq_submatrix (ζ : ℂ) :
    (W ζ : Matrix (Ix m) (Ix m) ℂ)
      = (Matrix.vandermonde (fun a : Fin (2 * m) => ζ ^ (a : ℕ))).submatrix (exEquiv m) (exEquiv m) := by
  ext x y
  simp only [W, Matrix.submatrix_apply, Matrix.vandermonde_apply]
  rw [← pow_mul]
  rfl

/-- Determinant of `W` via `detF`. -/
theorem det_W (hmodd : Odd m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (W ζ : Matrix (Ix m) (Ix m) ℂ).det = (-1 : ℂ) ^ ((m + 1) / 2) * (2 * m : ℂ) ^ m := by
  rw [W_eq_submatrix, Matrix.det_submatrix_equiv_self, detF_stub m hmodd ζ hζ]

/-- The conjugate DFT matrix using `ζ⁻¹`. -/
def Wc (ζ : ℂ) : Matrix (Ix m) (Ix m) ℂ := fun x y => (ζ⁻¹) ^ (ex x * ex y)

/-- Orthogonality: `W * Wc = (2m) • 1`. -/
theorem W_mul_Wc (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (W ζ : Matrix (Ix m) (Ix m) ℂ) * Wc ζ = (2 * m : ℂ) • (1 : Matrix (Ix m) (Ix m) ℂ) := by
  ext x y
  have hmpos : 0 < m := x.1.pos
  have hζne : ζ ≠ 0 := by
    intro h; subst h
    have := hζ.pow_eq_one
    rw [zero_pow (by omega : 2 * m ≠ 0)] at this
    exact zero_ne_one this
  rw [Matrix.mul_apply]
  -- term z = r ^ (ex z) with r = ζ^(ex x) * (ζ^(ex y))⁻¹
  set r : ℂ := ζ ^ (ex x) * (ζ ^ (ex y))⁻¹ with hr
  have hterm : ∀ z : Ix m, (W ζ x z) * (Wc ζ z y) = r ^ (ex z) := by
    intro z
    simp only [W, Wc, hr]
    rw [mul_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (ex z) (ex y)]
  rw [Finset.sum_congr rfl (fun z _ => hterm z)]
  -- reindex sum over Ix to Fin (2m)
  have hreindex : (∑ z : Ix m, r ^ (ex z)) = ∑ w : Fin (2 * m), r ^ (w : ℕ) := by
    rw [← Equiv.sum_comp (exEquiv m) (fun w : Fin (2 * m) => r ^ (w : ℕ))]
    rfl
  rw [hreindex]
  -- evaluate the geometric sum
  have hpow2m : ∀ e : ℕ, (ζ ^ e) ^ (2 * m) = 1 := by
    intro e
    rw [← pow_mul, mul_comm e (2 * m), pow_mul, hζ.pow_eq_one, one_pow]
  have hr2m : r ^ (2 * m) = 1 := by
    rw [hr, mul_pow, inv_pow, hpow2m, hpow2m, inv_one, mul_one]
  rw [Matrix.smul_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    have hr1 : r = 1 := by rw [hr]; rw [mul_inv_cancel₀ (pow_ne_zero _ hζne)]
    simp only [hr1, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, if_true, smul_eq_mul]
    push_cast; ring
  · -- r ≠ 1, geometric sum = 0
    have hr1 : r ≠ 1 := by
      rw [hr]
      intro h
      rw [mul_inv_eq_one₀ (pow_ne_zero _ hζne)] at h
      apply hxy
      -- ζ^(ex x) = ζ^(ex y), ex < 2m, primitive ⟹ ex x = ex y ⟹ x = y
      have hexeq : ex x = ex y := by
        have hxlt : ex x < 2 * m := (exEquiv m x).isLt
        have hylt : ex y < 2 * m := (exEquiv m y).isLt
        have := hζ.pow_inj (by exact hxlt) (by exact hylt) h
        exact this
      exact (exEquiv m).injective (Fin.ext hexeq)
    have hsum : (∑ w : Fin (2 * m), r ^ (w : ℕ)) = 0 := by
      have := geom_sum_eq hr1 (2 * m)
      rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i) (2 * m), this, hr2m]
      simp
    rw [hsum]
    simp only [if_neg hxy, smul_eq_mul, mul_zero]

/-- The "other element" of `Fin 2`. -/
def flip2 (c : Fin 2) : Fin 2 := c + 1

@[simp] theorem flip2_flip2 (c : Fin 2) : flip2 (flip2 c) = c := by
  fin_cases c <;> rfl

theorem flip2_ne (c : Fin 2) : flip2 c ≠ c := by fin_cases c <;> decide

theorem eq_flip2_of_ne {c d : Fin 2} (h : c ≠ d) : c = flip2 d := by
  fin_cases c <;> fin_cases d <;> simp_all <;> decide

/-- Reindexing `Ix m` by a transversal selector `a`: `(k,c) ↦ inl k` if `c = a k`, else `inr k`. -/
def eR (a : Fin m → Fin 2) : Ix m ≃ (Fin m ⊕ Fin m) where
  toFun x := if x.2 = a x.1 then Sum.inl x.1 else Sum.inr x.1
  invFun s := s.elim (fun k => (k, a k)) (fun k => (k, flip2 (a k)))
  left_inv := by
    rintro ⟨k, c⟩
    by_cases h : c = a k
    · simp [h]
    · simp only [h, if_false, Sum.elim_inr]
      rw [eq_flip2_of_ne h]
  right_inv := by
    rintro (k | k)
    · simp
    · simp only [Sum.elim_inr]
      rw [if_neg (flip2_ne (a k))]

@[simp] theorem eR_symm_inl (a : Fin m → Fin 2) (k : Fin m) :
    (eR a).symm (Sum.inl k) = (k, a k) := rfl

@[simp] theorem eR_symm_inr (a : Fin m → Fin 2) (k : Fin m) :
    (eR a).symm (Sum.inr k) = (k, flip2 (a k)) := rfl

@[simp] theorem eR_apply (a : Fin m → Fin 2) (x : Ix m) :
    (eR a) x = if x.2 = a x.1 then Sum.inl x.1 else Sum.inr x.1 := rfl

/-- Standard equiv `(Fin m ⊕ Fin m) ≃ (Fin m × Fin 2)`. -/
def esum (m : ℕ) : (Fin m ⊕ Fin m) ≃ (Fin m × Fin 2) where
  toFun s := s.elim (fun k => (k, 0)) (fun k => (k, 1))
  invFun x := if x.2 = 0 then Sum.inl x.1 else Sum.inr x.1
  left_inv := by rintro (k | k) <;> simp
  right_inv := by
    rintro ⟨k, c⟩; fin_cases c <;> simp

@[simp] theorem esum_inl (k : Fin m) : esum m (Sum.inl k) = (k, 0) := rfl
@[simp] theorem esum_inr (k : Fin m) : esum m (Sum.inr k) = (k, 1) := rfl

/-- The reindex permutation `τ = (eR b).symm.trans (eR a)` on `Fin m ⊕ Fin m`. -/
def tauPerm (a b : Fin m → Fin 2) : Equiv.Perm (Fin m ⊕ Fin m) :=
  (eR b).symm.trans (eR a)

/-- The fiberwise permutation on `Fin 2` for each `k`. -/
def sigPerm (a b : Fin m → Fin 2) (k : Fin m) : Equiv.Perm (Fin 2) :=
  if a k = b k then 1 else Equiv.swap 0 1

theorem tau_conj (a b : Fin m → Fin 2) :
    ∀ s : Fin m ⊕ Fin m,
      esum m (tauPerm a b s) = (Equiv.prodCongrRight (sigPerm a b)) (esum m s) := by
  rintro (k | k)
  · show esum m ((eR a) ((eR b).symm (Sum.inl k)))
        = (Equiv.prodCongrRight (sigPerm a b)) (esum m (Sum.inl k))
    rw [eR_symm_inl, eR_apply, esum_inl, Equiv.prodCongrRight_apply]
    by_cases h : a k = b k
    · rw [if_pos h.symm, esum_inl, sigPerm, if_pos h]
      simp
    · rw [if_neg (fun hh => h hh.symm), esum_inr, sigPerm, if_neg h, Equiv.swap_apply_left]
  · show esum m ((eR a) ((eR b).symm (Sum.inr k)))
        = (Equiv.prodCongrRight (sigPerm a b)) (esum m (Sum.inr k))
    rw [eR_symm_inr, eR_apply, esum_inr, Equiv.prodCongrRight_apply]
    by_cases h : a k = b k
    · rw [if_neg (by rw [h]; exact flip2_ne (b k)), esum_inr, sigPerm, if_pos h]
      simp
    · rw [if_pos (eq_flip2_of_ne h).symm, esum_inl, sigPerm, if_neg h,
        Equiv.swap_apply_right]

theorem sign_tau (a b : Fin m → Fin 2) :
    Equiv.Perm.sign (tauPerm a b) = ∏ k, (if a k = b k then (1 : ℤˣ) else -1) := by
  rw [Equiv.Perm.sign_eq_sign_of_equiv (tauPerm a b) (Equiv.prodCongrRight (sigPerm a b)) (esum m)
        (tau_conj a b),
    Equiv.Perm.sign_prodCongrRight]
  apply Finset.prod_congr rfl
  intro k _
  simp only [sigPerm]
  by_cases h : a k = b k
  · simp [h]
  · simp [h, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]

/-- The `m × m` minor of `W` selecting rows `(k, a k)` and columns `(j, b j)`. -/
def D (a b : Fin m → Fin 2) (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun k j => ζ ^ (ex (k, a k) * ex (j, b j))

theorem eRb_eq (a b : Fin m → Fin 2) (s : Fin m ⊕ Fin m) :
    (eR b).symm s = (eR a).symm (tauPerm a b s) := by
  show (eR b).symm s = (eR a).symm ((eR a) ((eR b).symm s))
  rw [Equiv.symm_apply_apply]

/-- The reindexed full matrix `M = W.submatrix (eR a).symm (eR b).symm` has
determinant `sign(tau) * det W`. -/
theorem det_Msub (a b : Fin m → Fin 2) (ζ : ℂ) :
    ((W ζ).submatrix (eR a).symm (eR b).symm).det
      = ((Equiv.Perm.sign (tauPerm a b) : ℂ)) * (W ζ : Matrix (Ix m) (Ix m) ℂ).det := by
  have h1 : (W ζ).submatrix (eR a).symm (eR b).symm
      = ((W ζ).submatrix (eR a).symm (eR a).symm).submatrix id (tauPerm a b) := by
    rw [Matrix.submatrix_submatrix]
    congr 1
    funext s
    exact (eRb_eq a b s)
  rw [h1, Matrix.det_permute', Matrix.det_submatrix_equiv_self]

/-- `M = W.submatrix (eR a).symm (eR b).symm`. -/
def Msub (a b : Fin m → Fin 2) (ζ : ℂ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  (W ζ).submatrix (eR a).symm (eR b).symm

/-- `N = Wc.submatrix (eR b).symm (eR a).symm`. -/
def Nsub (a b : Fin m → Fin 2) (ζ : ℂ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  (Wc ζ).submatrix (eR b).symm (eR a).symm

theorem Msub_mul_Nsub (a b : Fin m → Fin 2) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    Msub a b ζ * Nsub a b ζ = (2 * m : ℂ) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ) := by
  rw [Msub, Nsub, Matrix.submatrix_mul_equiv (W ζ) (Wc ζ) (eR a).symm (eR b).symm (eR a).symm,
    W_mul_Wc ζ hζ]
  rw [show ((2 * m : ℂ) • (1 : Matrix (Ix m) (Ix m) ℂ)).submatrix (eR a).symm (eR a).symm
        = (2 * m : ℂ) • ((1 : Matrix (Ix m) (Ix m) ℂ).submatrix (eR a).symm (eR a).symm) from
      ext fun i => congrFun rfl, Matrix.submatrix_one_equiv]

/-- Block decomposition of `Msub`. -/
theorem Msub_fromBlocks (a b : Fin m → Fin 2) (ζ : ℂ) :
    Msub a b ζ = fromBlocks (D a b ζ)
      (fun k j => ζ ^ (ex (k, a k) * ex (j, flip2 (b j))))
      (fun k j => ζ ^ (ex (k, flip2 (a k)) * ex (j, b j)))
      (fun k j => ζ ^ (ex (k, flip2 (a k)) * ex (j, flip2 (b j)))) := by
  ext s t
  rcases s with k | k <;> rcases t with j | j <;>
    simp [Msub, W, D, eR_symm_inl, eR_symm_inr]

/-- Block decomposition of `Nsub`. -/
theorem Nsub_fromBlocks (a b : Fin m → Fin 2) (ζ : ℂ) :
    Nsub a b ζ = fromBlocks
      (fun k j => (ζ⁻¹) ^ (ex (k, b k) * ex (j, a j)))
      (fun k j => (ζ⁻¹) ^ (ex (k, b k) * ex (j, flip2 (a j))))
      (fun k j => (ζ⁻¹) ^ (ex (k, flip2 (b k)) * ex (j, a j)))
      (fun k j => (ζ⁻¹) ^ (ex (k, flip2 (b k)) * ex (j, flip2 (a j)))) := by
  ext s t
  rcases s with k | k <;> rcases t with j | j <;>
    simp [Nsub, Wc, eR_symm_inl, eR_symm_inr]

theorem zeta_pow_m (ζ : ℂ) (hm : 0 < m) (hζ : IsPrimitiveRoot ζ (2 * m)) : ζ ^ m = -1 := by
  have h2 : (ζ ^ m) * (ζ ^ m) = 1 := by
    rw [← pow_add, show m + m = 2 * m by ring, hζ.pow_eq_one]
  rcases mul_self_eq_one_iff.1 h2 with h | h
  · exfalso
    rw [hζ.pow_eq_one_iff_dvd] at h
    have := Nat.le_of_dvd hm h
    omega
  · exact h

/-- Entry-level identity expressing the flipped exponent in terms of the original. -/
theorem entry_flip (ζ : ℂ) (hmodd : Odd m) (hζ : IsPrimitiveRoot ζ (2 * m)) (k j : Fin m)
    (c d : Fin 2) :
    ζ ^ (ex (k, flip2 c) * ex (j, flip2 d))
      = (-1) * ((-1) ^ (ex (k, c)) * (-1) ^ (ex (j, d))) * ζ ^ (ex (k, c) * ex (j, d)) := by
  have hm : 0 < m := k.pos
  have hzm : ζ ^ m = -1 := zeta_pow_m ζ hm hζ
  have hmm : (-1 : ℂ) ^ m = -1 := Odd.neg_one_pow hmodd
  have g1 : ζ ^ (((k : ℕ) + m) * ((j : ℕ) + m))
      = ζ ^ ((k : ℕ) * (j : ℕ)) * ((-1) ^ (k : ℕ) * (-1) ^ (j : ℕ) * (-1) ^ m) := by
    rw [show ((k : ℕ) + m) * ((j : ℕ) + m) = (k : ℕ) * (j : ℕ) + m * (k : ℕ) + (m * (j : ℕ) + m * m) by ring,
      pow_add, pow_add, pow_add]
    simp only [pow_mul, hzm]; ring
  have g2 : ζ ^ (((k : ℕ) + m) * (j : ℕ))
      = ζ ^ ((k : ℕ) * (j : ℕ)) * (-1) ^ (j : ℕ) := by
    rw [show ((k : ℕ) + m) * (j : ℕ) = (k : ℕ) * (j : ℕ) + m * (j : ℕ) by ring, pow_add]
    simp only [pow_mul, hzm]
  have g3 : ζ ^ ((k : ℕ) * ((j : ℕ) + m))
      = ζ ^ ((k : ℕ) * (j : ℕ)) * (-1) ^ (k : ℕ) := by
    rw [show (k : ℕ) * ((j : ℕ) + m) = (k : ℕ) * (j : ℕ) + m * (k : ℕ) by ring, pow_add]
    simp only [pow_mul, hzm]
  have hk2 : ((-1 : ℂ)) ^ ((k : ℕ) * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
  have hj2 : ((-1 : ℂ)) ^ ((j : ℕ) * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
  fin_cases c <;> fin_cases d <;>
    simp only [ex, flip2, Fin.val_add, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.reduceMod,
      Nat.reduceAdd, mul_one, mul_zero, add_zero] <;>
    simp only [g1, g2, g3, pow_add, hmm] <;>
    ring_nf <;>
    simp only [hk2, hj2, mul_one, one_mul]

/-- The `(2,2)` block of `Nsub`, which is `conj` of a flipped `D`. -/
def Tpr (a b : Fin m → Fin 2) (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun k j => (ζ⁻¹) ^ (ex (k, flip2 (b k)) * ex (j, flip2 (a j)))

/-- Schur-complement scalar identity:
`det(Msub) * det(Tpr) = det(D a b) * (2m)^m`. -/
theorem schur_scalar (a b : Fin m → Fin 2) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m))
    (hP : IsUnit (D a b ζ).det) :
    (Msub a b ζ).det * (Tpr a b ζ).det = (D a b ζ).det * (2 * m : ℂ) ^ m := by
  -- name the blocks
  set P := D a b ζ with hPdef
  set Q : Matrix (Fin m) (Fin m) ℂ := (fun k j => ζ ^ (ex (k, a k) * ex (j, flip2 (b j)))) with hQ
  set R : Matrix (Fin m) (Fin m) ℂ := (fun k j => ζ ^ (ex (k, flip2 (a k)) * ex (j, b j))) with hR
  set T : Matrix (Fin m) (Fin m) ℂ := (fun k j => ζ ^ (ex (k, flip2 (a k)) * ex (j, flip2 (b j)))) with hT
  set P' : Matrix (Fin m) (Fin m) ℂ := (fun k j => (ζ⁻¹) ^ (ex (k, b k) * ex (j, a j))) with hP'
  set Q' : Matrix (Fin m) (Fin m) ℂ := (fun k j => (ζ⁻¹) ^ (ex (k, b k) * ex (j, flip2 (a j)))) with hQ'
  set R' : Matrix (Fin m) (Fin m) ℂ := (fun k j => (ζ⁻¹) ^ (ex (k, flip2 (b k)) * ex (j, a j))) with hR'
  -- the (2,2) block of N is Tpr
  have hTpr : (Tpr a b ζ) = (fun k j => (ζ⁻¹) ^ (ex (k, flip2 (b k)) * ex (j, flip2 (a j)))) := rfl
  -- block equations from Msub * Nsub = (2m)•1
  have hmul := Msub_mul_Nsub a b ζ hζ
  rw [Msub_fromBlocks, Nsub_fromBlocks, Matrix.fromBlocks_multiply,
    show ((2 * m : ℂ) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ))
        = fromBlocks ((2 * m : ℂ) • 1) 0 0 ((2 * m : ℂ) • 1) by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]; simp] at hmul
  rw [Matrix.fromBlocks_inj] at hmul
  obtain ⟨_, eq12, _, eq22⟩ := hmul
  -- eq12 : P * Q' + Q * (Tpr) = 0 ; eq22 : R * Q' + T * (Tpr) = (2m)•1
  change P * Q' + Q * (Tpr a b ζ) = 0 at eq12
  change R * Q' + T * (Tpr a b ζ) = (2 * m : ℂ) • 1 at eq22
  -- invertibility of P
  letI := Matrix.invertibleOfIsUnitDet P hP
  -- Schur complement
  have hdetM : (fromBlocks P Q R T).det = P.det * (T - R * (⅟ P) * Q).det :=
    Matrix.det_fromBlocks₁₁ P Q R T
  have hSchur : (T - R * (⅟ P) * Q) * (Tpr a b ζ) = (2 * m : ℂ) • 1 := by
    have hQmulT : Q * (Tpr a b ζ) = - (P * Q') := by
      have := eq12
      linear_combination (norm := module) this
    have key : R * (⅟ P) * Q * (Tpr a b ζ) = - (R * Q') := by
      rw [mul_assoc, mul_assoc, hQmulT, mul_neg, ← mul_assoc, invOf_mul_self,
        Matrix.one_mul, mul_neg]
    rw [sub_mul, key, sub_neg_eq_add, add_comm]
    exact eq22
  -- determinants
  have hMsub_det : (Msub a b ζ).det = (fromBlocks P Q R T).det := by rw [Msub_fromBlocks]
  rw [hMsub_det, hdetM]
  have hdetS : (T - R * (⅟ P) * Q).det * (Tpr a b ζ).det = (2 * m : ℂ) ^ m := by
    have := congrArg Matrix.det hSchur
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    exact this
  rw [mul_assoc, hdetS]

/-- Determinant of the doubly-flipped `D` in terms of `D a b`. -/
theorem det_DF (a b : Fin m → Fin 2) (ζ : ℂ) (hmodd : Odd m) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (D (fun k => flip2 (b k)) (fun j => flip2 (a j)) ζ).det
      = (-1) ^ (m + (∑ k, ex (k, b k)) + (∑ j, ex (j, a j))) * (D a b ζ).det := by
  have hDF : D (fun k => flip2 (b k)) (fun j => flip2 (a j)) ζ
      = (-1 : ℂ) • (Matrix.diagonal (fun k => (-1 : ℂ) ^ (ex (k, b k))) * D b a ζ
          * Matrix.diagonal (fun j => (-1 : ℂ) ^ (ex (j, a j)))) := by
    ext k j
    rw [Matrix.smul_apply,
      show (Matrix.diagonal (fun k => (-1 : ℂ) ^ (ex (k, b k))) * D b a ζ
            * Matrix.diagonal (fun j => (-1 : ℂ) ^ (ex (j, a j)))) k j
          = (-1 : ℂ) ^ (ex (k, b k)) * (D b a ζ) k j * (-1 : ℂ) ^ (ex (j, a j)) from by
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul]]
    simp only [D, smul_eq_mul]
    rw [entry_flip ζ hmodd hζ k j (b k) (a j)]
    ring
  rw [hDF, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  have htr : (D b a ζ).det = (D a b ζ).det := by
    rw [show D b a ζ = (D a b ζ)ᵀ by ext k j; simp only [D, Matrix.transpose_apply, mul_comm],
      Matrix.det_transpose]
  rw [htr, pow_add, pow_add]
  ring

/-- Determinant of `Tpr` in terms of `conj (det (D a b))`. -/
theorem det_Tpr (a b : Fin m → Fin 2) (ζ : ℂ) (hmodd : Odd m) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (Tpr a b ζ).det
      = (-1) ^ (m + (∑ k, ex (k, b k)) + (∑ j, ex (j, a j)))
          * (starRingEnd ℂ) ((D a b ζ).det) := by
  have hm : 0 < m := hmodd.pos
  have hconj : (starRingEnd ℂ) ζ = ζ⁻¹ := by
    have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega)
    rw [← Complex.inv_eq_conj hn]
  -- Tpr is the entrywise conjugate of the flipped D
  have hmap : Tpr a b ζ = ((starRingEnd ℂ).mapMatrix (D (fun k => flip2 (b k)) (fun j => flip2 (a j)) ζ)) := by
    ext k j
    simp only [Tpr, RingHom.mapMatrix_apply, Matrix.map_apply, D]
    rw [map_pow, hconj]
  rw [hmap, ← RingHom.map_det, det_DF a b ζ hmodd hζ, map_mul]
  congr 1
  rw [map_pow]
  norm_num

/-- Sign cancellation: `sign(tau) * (-1)^(Sa+Sb) = 1`. -/
theorem sign_cancel (a b : Fin m → Fin 2) (hmodd : Odd m) :
    ((Equiv.Perm.sign (tauPerm a b) : ℂ)) * (-1) ^ ((∑ j, ex (j, a j)) + (∑ k, ex (k, b k))) = 1 := by
  have hmm : (-1 : ℂ) ^ m = -1 := Odd.neg_one_pow hmodd
  rw [show ((∑ j, ex (j, a j)) + (∑ k, ex (k, b k))) = ∑ k, (ex (k, a k) + ex (k, b k)) by
        rw [Finset.sum_add_distrib], ← Finset.prod_pow_eq_pow_sum, sign_tau]
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro k _
  have hsum : ex (k, a k) + ex (k, b k) = 2 * (k : ℕ) + m * ((a k).val + (b k).val) := by
    simp only [ex]; ring
  rw [hsum, pow_add, pow_mul, pow_mul, hmm]
  by_cases h : a k = b k
  · rw [if_pos h]
    have hv : (a k).val + (b k).val = 2 * (a k).val := by rw [h]; ring
    rw [hv, pow_mul]; norm_num
  · rw [if_neg h]
    have hv : (a k).val + (b k).val = 1 := by
      have hne : (a k).val ≠ (b k).val := fun hh => h (Fin.val_injective hh)
      have h1 := (a k).isLt
      have h2 := (b k).isLt
      omega
    rw [hv]; norm_num

/-- **The crux identity.** For any selectors `a b`, with `ζ` a primitive `2m`-th root of unity
and `m` odd, `conj (det (D a b)) = (-1)^((m-1)/2) * det (D a b)`. -/
theorem crux (a b : Fin m → Fin 2) (hmodd : Odd m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (starRingEnd ℂ) ((D a b ζ).det) = (-1) ^ ((m - 1) / 2) * (D a b ζ).det := by
  by_cases hD : (D a b ζ).det = 0
  · rw [hD]; simp
  set Sa : ℕ := ∑ j, ex (j, a j) with hSa
  set Sb : ℕ := ∑ k, ex (k, b k) with hSb
  have hPunit : IsUnit (D a b ζ).det := isUnit_iff_ne_zero.2 hD
  have hsc := schur_scalar a b ζ hζ hPunit
  have hMsub : (Msub a b ζ).det = (Equiv.Perm.sign (tauPerm a b) : ℂ) * (W ζ).det :=
    det_Msub a b ζ
  rw [hMsub, det_W hmodd ζ hζ, det_Tpr a b ζ hmodd hζ] at hsc
  -- hsc : (s * ((-1)^((m+1)/2) * (2m)^m)) * ((-1)^(m+Sb+Sa) * conj detD) = detD * (2m)^m
  have hm : 0 < m := hmodd.pos
  have hpw : (2 * m : ℂ) ^ m ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 (by omega)))
  set s : ℂ := (Equiv.Perm.sign (tauPerm a b) : ℂ) with hs
  set detD : ℂ := (D a b ζ).det with hdetD
  -- cancel (2m)^m
  have hcancel : s * (-1) ^ ((m + 1) / 2) * ((-1) ^ (m + Sb + Sa) * (starRingEnd ℂ) detD) = detD := by
    have key : (2 * m : ℂ) ^ m * (s * (-1) ^ ((m + 1) / 2) * ((-1) ^ (m + Sb + Sa) * (starRingEnd ℂ) detD))
        = (2 * m : ℂ) ^ m * detD := by
      linear_combination hsc
    exact mul_left_cancel₀ hpw key
  -- compute the coefficient
  have hexp : (-1 : ℂ) ^ ((m + 1) / 2 + m) = (-1) ^ ((m - 1) / 2) := by
    obtain ⟨t, ht⟩ := hmodd
    subst ht
    rw [show (2 * t + 1 + 1) / 2 = t + 1 by omega, show (2 * t + 1 - 1) / 2 = t by omega,
      show (t + 1) + (2 * t + 1) = t + 2 * (t + 1) by ring, pow_add, pow_mul]
    norm_num
  have hsg := sign_cancel a b hmodd
  rw [← hSa, ← hSb, ← hs] at hsg
  have hcoef : s * (-1) ^ ((m + 1) / 2) * (-1) ^ (m + Sb + Sa) = (-1) ^ ((m - 1) / 2) := by
    rw [show m + Sb + Sa = (Sa + Sb) + m by ring, pow_add,
      show s * (-1) ^ ((m + 1) / 2) * ((-1) ^ (Sa + Sb) * (-1) ^ m)
        = (-1) ^ ((m + 1) / 2) * (-1) ^ m * (s * (-1) ^ (Sa + Sb)) by ring,
      hsg, mul_one, ← pow_add, hexp]
  rw [show s * (-1) ^ ((m + 1) / 2) * ((-1) ^ (m + Sb + Sa) * (starRingEnd ℂ) detD)
      = (s * (-1) ^ ((m + 1) / 2) * (-1) ^ (m + Sb + Sa)) * (starRingEnd ℂ) detD by ring,
    hcoef] at hcancel
  -- hcancel : (-1)^((m-1)/2) * conj detD = detD
  have hpm1 : ((-1 : ℂ) ^ ((m - 1) / 2)) * ((-1 : ℂ) ^ ((m - 1) / 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc (starRingEnd ℂ) detD
      = ((-1 : ℂ) ^ ((m - 1) / 2) * (-1) ^ ((m - 1) / 2)) * (starRingEnd ℂ) detD := by
          rw [hpm1, one_mul]
    _ = (-1) ^ ((m - 1) / 2) * ((-1) ^ ((m - 1) / 2) * (starRingEnd ℂ) detD) := by ring
    _ = (-1) ^ ((m - 1) / 2) * detD := by rw [hcancel]

end

end Crux
-- ===================== Char.lean =====================

open Matrix Finset BigOperators Complex

namespace CharM

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- Number of units. -/
abbrev N (p : ℕ) [Fact p.Prime] : ℕ := Nat.card (ZMod p)ˣ

/-- The cyclic isomorphism. -/
def ee (p : ℕ) [Fact p.Prime] : Multiplicative (ZMod (N p)) ≃* (ZMod p)ˣ :=
  zmodCyclicMulEquiv (inferInstance : IsCyclic (ZMod p)ˣ)

/-- The power map `ZMod N → units`. -/
def pw (p : ℕ) [Fact p.Prime] (a : ZMod (N p)) : (ZMod p)ˣ := ee p (Multiplicative.ofAdd a)

/-- Discrete log: function from units to `ZMod N`. -/
def dl (u : (ZMod p)ˣ) : ZMod (N p) := Multiplicative.toAdd ((ee p).symm u)

theorem pw_dl (u : (ZMod p)ˣ) : pw p (dl u) = u := by
  simp only [pw, dl, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem dl_pw (a : ZMod (N p)) : dl (pw p a) = a := by
  simp only [pw, dl, MulEquiv.symm_apply_apply, toAdd_ofAdd]

theorem pw_add (a b : ZMod (N p)) : pw p (a + b) = pw p a * pw p b := by
  simp only [pw, ofAdd_add, map_mul]

theorem pw_zero : pw p (0 : ZMod (N p)) = 1 := by
  simp only [pw, ofAdd_zero, map_one]

theorem dl_mul (u v : (ZMod p)ˣ) : dl (u * v) = dl u + dl v := by
  simp only [dl, map_mul, toAdd_mul]

theorem card_N : N p = p - 1 := by
  rw [N, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]

theorem N_pos : 0 < N p := by
  rw [card_N]; have := (Fact.out : p.Prime).two_le; omega

instance : NeZero (N p) := ⟨by have := @N_pos p _; omega⟩

/-- `pw a = gen ^ a.val`. -/
theorem pw_eq_gen_pow (a : ZMod (N p)) : pw p a = (pw p 1) ^ (a.val) := by
  have h1 : (pw p 1) ^ (a.val) = pw p ((a.val : ℕ) • (1 : ZMod (N p))) := by
    rw [pw, pw, ← map_pow, ← ofAdd_nsmul]
  rw [h1]
  congr 2
  rw [nsmul_eq_mul, mul_one, ZMod.natCast_val, ZMod.cast_id]

theorem N_even (hodd : p % 2 = 1) : N p = 2 * (N p / 2) := by
  rw [card_N]
  have hp := (Fact.out : p.Prime).two_le
  omega

/-- The exponential map `ZMod N → ℂ`. -/
def ze (ζ : ℂ) (a : ZMod (N p)) : ℂ := ζ ^ a.val

theorem ze_add (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (a b : ZMod (N p)) :
    ze (p := p) ζ (a + b) = ze (p := p) ζ a * ze (p := p) ζ b := by
  rw [ze, ze, ze, ← pow_add]
  have hv : a.val + b.val = N p * ((a.val + b.val) / N p) + (a + b).val := by
    rw [ZMod.val_add]; exact (Nat.div_add_mod _ _).symm
  rw [hv, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

theorem ze_zero (ζ : ℂ) : ze (p := p) ζ (0 : ZMod (N p)) = 1 := by
  rw [ze, ZMod.val_zero, pow_zero]

theorem ze_natCast (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (k : ℕ) :
    ze (p := p) ζ (k : ZMod (N p)) = ζ ^ k := by
  rw [ze, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod k (N p)]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

/-- The quadratic character of `ZMod p` (integer valued). -/
abbrev qc (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℤ := quadraticChar (ZMod p)

theorem gen_not_square (hodd : p % 2 = 1) :
    ¬ IsSquare ((pw p 1 : (ZMod p)ˣ) : ZMod p) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact (Units.ne_zero _) hr
  set u := (isUnit_iff_ne_zero.mpr hr0).unit with hu
  have hus : (u : ZMod p) = r := IsUnit.unit_spec _
  have hpw1 : pw p 1 = u * u := by
    apply Units.ext
    rw [Units.val_mul, hus, hr]
  have hdl : (1 : ZMod (N p)) = dl u + dl u := by
    rw [← dl_mul, ← hpw1, dl_pw]
  have h2 : (2 : ℕ) ∣ N p := ⟨N p / 2, N_even hodd⟩
  have key : (1 : ZMod 2)
      = (ZMod.castHom h2 (ZMod 2)) (dl u) + (ZMod.castHom h2 (ZMod 2)) (dl u) := by
    rw [← map_add, ← hdl, map_one]
  revert key
  generalize (ZMod.castHom h2 (ZMod 2)) (dl u) = y
  revert y
  decide

theorem qc_gen (hodd : p % 2 = 1) : qc p ((pw p 1 : (ZMod p)ˣ) : ZMod p) = -1 :=
  (quadraticChar_neg_one_iff_not_isSquare).2 (gen_not_square hodd)

theorem qc_pw (hodd : p % 2 = 1) (a : ZMod (N p)) :
    qc p ((pw p a : (ZMod p)ˣ) : ZMod p) = (-1) ^ a.val := by
  rw [pw_eq_gen_pow, Units.val_pow_eq_pow_val, map_pow, qc_gen hodd]

theorem sum_zmod_range (M : ℕ) [NeZero M] (f : ℕ → ℂ) :
    ∑ a : ZMod M, f (a.val) = ∑ k ∈ Finset.range M, f k := by
  refine Finset.sum_bij' (fun a _ => a.val) (fun k _ => (k : ZMod M)) ?_ ?_ ?_ ?_ ?_
  · intro a _; rw [Finset.mem_range]; exact ZMod.val_lt a
  · intro k _; exact Finset.mem_univ _
  · intro a _; simp [ZMod.natCast_val, ZMod.cast_id]
  · intro k hk; rw [Finset.mem_range] at hk; exact ZMod.val_natCast_of_lt hk
  · intro a _; rfl

theorem ze_mul_pow (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (a d : ZMod (N p)) :
    ze (p := p) ζ (a * d) = (ze (p := p) ζ d) ^ (a.val) := by
  have h1 : a * d = (((a.val * d.val : ℕ)) : ZMod (N p)) := by
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id]
  rw [h1, ze_natCast ζ hζ, ze, ← pow_mul, mul_comm]

/-- Orthogonality of the `ze` characters. -/
theorem ze_orthogonality (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (d : ZMod (N p)) :
    ∑ a : ZMod (N p), ze (p := p) ζ (a * d) = if d = 0 then (N p : ℂ) else 0 := by
  have hrw : ∀ a : ZMod (N p), ze (p := p) ζ (a * d) = (ze (p := p) ζ d) ^ (a.val) :=
    fun a => ze_mul_pow ζ hζ a d
  rw [Finset.sum_congr rfl (fun a _ => hrw a), sum_zmod_range (N p) (fun k => (ze (p := p) ζ d) ^ k)]
  by_cases hd : d = 0
  · subst hd
    rw [ze_zero]
    simp
  · rw [if_neg hd]
    have hr1 : ze (p := p) ζ d ≠ 1 := by
      rw [ze]
      intro h
      apply hd
      have hdlt : d.val < N p := ZMod.val_lt d
      have := hζ.pow_eq_one_iff_dvd d.val
      rw [h] at this
      have hdvd : (N p) ∣ d.val := this.1 rfl
      exact (ZMod.val_eq_zero d).1 (Nat.eq_zero_of_dvd_of_lt hdvd hdlt)
    have hrN : (ze (p := p) ζ d) ^ (N p) = 1 := by
      rw [ze, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [geom_sum_eq hr1 (N p), hrN, sub_self, zero_div]

/-- The value `h(g^s) = χ(1 - g^s)` as a complex number. -/
def hf (ζ : ℂ) (s : ZMod (N p)) : ℂ :=
  ((qc p (1 - ((pw p s : (ZMod p)ˣ) : ZMod p)) : ℤ) : ℂ)

/-- Fourier coefficient. -/
def hhat (ζ : ℂ) (a : ZMod (N p)) : ℂ :=
  (N p : ℂ)⁻¹ * ∑ s : ZMod (N p), hf (p := p) ζ s * ze (p := p) ζ (-(a * s))

theorem fourier_inv (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (s : ZMod (N p)) :
    hf (p := p) ζ s = ∑ a : ZMod (N p), hhat (p := p) ζ a * ze (p := p) ζ (a * s) := by
  have hN : (N p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := @N_pos p _; omega)
  have step1 : ∀ a : ZMod (N p), hhat (p := p) ζ a * ze (p := p) ζ (a * s)
      = (N p : ℂ)⁻¹ * ∑ t : ZMod (N p),
          hf (p := p) ζ t * ze (p := p) ζ (a * (s - t)) := by
    intro a
    rw [hhat, mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_assoc, ← ze_add ζ hζ]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun a _ => step1 a), ← Finset.mul_sum, Finset.sum_comm]
  have step2 : (∑ t : ZMod (N p), ∑ a : ZMod (N p),
        hf (p := p) ζ t * ze (p := p) ζ (a * (s - t)))
      = ∑ t : ZMod (N p), hf (p := p) ζ t * (if s - t = 0 then (N p : ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.mul_sum, ze_orthogonality ζ hζ (s - t)]
  rw [step2]
  have step3 : (∑ t : ZMod (N p), hf (p := p) ζ t * (if s - t = 0 then (N p : ℂ) else 0))
      = hf (p := p) ζ s * (N p : ℂ) := by
    rw [Finset.sum_eq_single s]
    · rw [sub_self, if_pos rfl]
    · intro t _ hts
      rw [if_neg (by rw [sub_eq_zero]; exact fun h => hts h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h
  rw [step3, mul_comm (hf (p := p) ζ s) (N p : ℂ), ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

instance instNeZeroP : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- The "half" element of `ZMod N`. -/
def half (p : ℕ) [Fact p.Prime] : ZMod (N p) := ((N p / 2 : ℕ) : ZMod (N p))

theorem ze_half_eq (hodd : p % 2 = 1) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) :
    ze (p := p) ζ (half p) = -1 := by
  have hNlt : N p / 2 < N p := by have := @N_pos p _; omega
  rw [ze, half, ZMod.val_natCast_of_lt hNlt]
  -- ζ^(N/2) = -1
  have h2 : (ζ ^ (N p / 2)) * (ζ ^ (N p / 2)) = 1 := by
    rw [← pow_add, ← Nat.two_mul, ← N_even hodd, hζ.pow_eq_one]
  have hN2 : 2 ≤ N p := by
    rw [card_N]; have := (Fact.out : p.Prime).two_le; omega
  rcases mul_self_eq_one_iff.1 h2 with h | h
  · exfalso
    rw [hζ.pow_eq_one_iff_dvd] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  · exact h

theorem ze_half_mul (hodd : p % 2 = 1) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (s : ZMod (N p)) :
    ze (p := p) ζ (half p * s) = (-1) ^ s.val := by
  rw [mul_comm, ze_mul_pow ζ hζ, ze_half_eq hodd ζ hζ]

theorem qc_neg_one (h4 : p % 4 = 3) : qc p (-1) = -1 := by
  have hrc : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  rw [qc, quadraticChar_neg_one hrc, ZMod.card]
  exact ZMod.χ₄_nat_three_mod_four h4

theorem pw_neg (s : ZMod (N p)) : pw p (-s) = (pw p s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pw_add, neg_add_cancel, pw_zero]

/-- Key reflection identity for `hf`. -/
theorem hf_neg (h4 : p % 4 = 3) (ζ : ℂ) (s : ZMod (N p)) :
    hf (p := p) ζ (-s) * ((-1 : ℂ) ^ s.val) = - hf (p := p) ζ s := by
  have hodd : p % 2 = 1 := by omega
  set u : ZMod p := ((pw p s : (ZMod p)ˣ) : ZMod p) with hu
  have hu0 : u ≠ 0 := Units.ne_zero _
  have hpwneg : ((pw p (-s) : (ZMod p)ˣ) : ZMod p) = u⁻¹ := by
    rw [pw_neg, hu]; exact Units.val_inv_eq_inv_val _
  -- hf ζ (-s) = qc (1 - u⁻¹)
  have hqcsq : (qc p u) ^ 2 = 1 := quadraticChar_sq_one hu0
  -- 1 - u⁻¹ = u⁻¹ * ((-1) * (1 - u))
  have hfac : (1 : ZMod p) - u⁻¹ = u⁻¹ * ((-1) * (1 - u)) := by
    field_simp
    ring
  have hsval : hf (p := p) ζ s = ((qc p (1 - u) : ℤ) : ℂ) := by
    rw [hf]
  have hnegval : hf (p := p) ζ (-s) = ((qc p (1 - u⁻¹) : ℤ) : ℂ) := by
    rw [hf, hpwneg]
  -- qc u⁻¹ = qc u
  have hqcu_inv : qc p u⁻¹ = qc p u := by
    have hmul : qc p u * qc p u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have hsq : qc p u * qc p u = 1 := by rw [← sq]; exact hqcsq
    have hne : qc p u ≠ 0 := by
      intro h; rw [h] at hsq; simp at hsq
    have heq := hsq.trans hmul.symm
    exact (mul_left_cancel₀ hne heq).symm
  have hqcu_val : qc p u = (-1) ^ s.val := by rw [hu]; exact qc_pw hodd s
  have hqcexpand : qc p (1 - u⁻¹) = (-1) ^ s.val * (-1) * qc p (1 - u) := by
    rw [hfac, map_mul, map_mul, hqcu_inv, hqcu_val, qc_neg_one h4]; ring
  rw [hnegval, hsval, hqcexpand]
  push_cast
  have hsq2 : (-1 : ℂ) ^ s.val * (-1 : ℂ) ^ s.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (-(((qc p) (1 - u) : ℤ) : ℂ)) * hsq2

/-- Reflection symmetry of the Fourier coefficients. -/
theorem hhat_symm (h4 : p % 4 = 3) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (a : ZMod (N p)) :
    hhat (p := p) ζ (half p - a) = - hhat (p := p) ζ a := by
  have hodd : p % 2 = 1 := by omega
  rw [hhat, hhat, ← mul_neg]
  congr 1
  rw [← Equiv.sum_comp (Equiv.neg (ZMod (N p)))
        (fun s => hf (p := p) ζ s * ze (p := p) ζ (-((half p - a) * s))),
      ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Equiv.neg_apply]
  have e1 : -((half p - a) * -s) = (half p) * s + (-(a * s)) := by ring
  rw [e1, ze_add ζ hζ, ze_half_mul hodd ζ hζ, ← mul_assoc, hf_neg h4 ζ s]
  ring

end

end CharM
-- ===================== Dev.lean (easy_direction) =====================
open Matrix Nat Int
namespace A226163Dev

/-! ## Development file for the A226163 determinant conjecture.

We develop the proof in pieces here, then assemble into `Spec.lean`.

Key facts established mathematically (numerically verified):
* `det M = 0 ⟺ p ≡ 3 mod 4` where `M[i,j] = legendreSym p (i'^2 - C j')`, `C = m!`, `m=(p-1)/2`.
* Easy direction (`p ≡ 1 ⟹ det ≠ 0`): elementary, via `det M ≡ det[(i²-Cj)^m] mod p`,
  the columns `k=0,m` of the Cauchy–Binet factor coincide (since QR are roots of `X^m-1`),
  leaving a 2-term factor `(nonzero)·F` with `F = 1 + (-1)^m C^{1-m}`, and `C² ≡ (-1)^{m+1}` (Wilson).
* Hard direction (`p ≡ 3 ⟹ det = 0`): spectral cancellation; the key analytic lemma
  (R-realness) is an elementary roots-of-unity identity (no Gauss sum sign needed).
-/

-- Warmup: Wilson-type fact `((p-1)/2)!^2 ≡ (-1)^{(p+1)/2} (mod p)`.
-- In ZMod p: with `m = (p-1)/2`, `(m!)^2 = (-1)^{m+1}`.

/-- `(p-1)! = (-1)^m (m!)^2` in `ZMod p`, where `m = (p-1)/2`. -/
theorem factorial_pred_eq (p : ℕ) [hp : Fact p.Prime] (hodd : Odd p) :
    ((p-1).factorial : ZMod p) = (-1)^((p-1)/2) * ((((p-1)/2).factorial : ZMod p))^2 := by
  set m := (p-1)/2 with hm
  obtain ⟨k, hk⟩ := hodd
  have hp2m : p = 2*m+1 := by simp only [hm]; omega
  have hcast : ((p-1).factorial : ZMod p) = ∏ i ∈ Finset.Ico 1 p, (i : ZMod p) := by
    rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    congr 1; omega
  -- split Ico 1 p = Ico 1 (m+1) ∪ Ico (m+1) p
  have hsplit : ∏ i ∈ Finset.Ico 1 p, (i : ZMod p)
      = (∏ i ∈ Finset.Ico 1 (m+1), (i : ZMod p)) * (∏ i ∈ Finset.Ico (m+1) p, (i : ZMod p)) := by
    rw [← Finset.prod_union]
    · congr 1
      rw [Finset.Ico_union_Ico_eq_Ico] <;> omega
    · apply Finset.Ico_disjoint_Ico_consecutive
  -- first product = m!
  have hfst : ∏ i ∈ Finset.Ico 1 (m+1), (i : ZMod p) = (m.factorial : ZMod p) := by
    rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod]
  -- second product = (-1)^m * m!  via i ↦ p - i
  have hsnd : ∏ i ∈ Finset.Ico (m+1) p, (i : ZMod p) = (-1)^m * (m.factorial : ZMod p) := by
    have hcard : (Finset.Ico (m+1) p).card = m := by rw [Nat.card_Ico]; omega
    -- rewrite each factor (i : ZMod p) = -((p - i : ℕ) : ZMod p)
    have h1 : ∏ i ∈ Finset.Ico (m+1) p, (i : ZMod p)
        = ∏ i ∈ Finset.Ico (m+1) p, (-(((p - i : ℕ) : ZMod p))) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_Ico] at hi
      have hcast : ((p - i : ℕ) : ZMod p) = (p : ZMod p) - (i : ZMod p) := by
        rw [Nat.cast_sub (by omega)]
      rw [hcast]; simp [ZMod.natCast_self]
    rw [h1]
    -- pull out the (-1)'s
    rw [show (fun i => -(((p - i : ℕ) : ZMod p))) = (fun i => (-1 : ZMod p) * (((p - i : ℕ) : ZMod p))) from by
      funext i; ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    congr 1
    -- reindex i ↦ p - i  to turn Ico (m+1) p into Ico 1 (m+1)
    rw [← hfst]
    apply Finset.prod_nbij' (fun i => p - i) (fun k => p - k)
    · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
    · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
    · intro i hi; simp only [Finset.mem_Ico] at hi; omega
    · intro k hk; simp only [Finset.mem_Ico] at hk; omega
    · intro i hi; rfl
  rw [hcast, hsplit, hfst, hsnd]
  ring

theorem wilson_half (p : ℕ) [hp : Fact p.Prime] (hodd : Odd p) :
    ((((p-1)/2).factorial : ZMod p))^2 = (-1)^(((p-1)/2)+1) := by
  have hw : ((p-1).factorial : ZMod p) = -1 := by
    exact_mod_cast ZMod.wilsons_lemma p
  have he := factorial_pred_eq p hodd
  set m := (p-1)/2 with hm
  rw [hw] at he
  -- -1 = (-1)^m * (m!)^2  ⟹  (m!)^2 = (-1)^{m+1}
  have hsq : ((((p-1)/2).factorial : ZMod p))^2 = (-1)^(m+1) := by
    have : (-1 : ZMod p)^m * ((((p-1)/2).factorial : ZMod p))^2 = -1 := he.symm
    have hu : ((-1 : ZMod p)^m) * (-1)^m = 1 := by
      rw [← pow_add]; simp [← two_mul, pow_mul]
    calc ((((p-1)/2).factorial : ZMod p))^2
        = (1 : ZMod p) * ((((p-1)/2).factorial : ZMod p))^2 := by ring
      _ = ((-1:ZMod p)^m * (-1)^m) * ((((p-1)/2).factorial : ZMod p))^2 := by rw [hu]
      _ = (-1)^m * ((-1)^m * ((((p-1)/2).factorial : ZMod p))^2) := by ring
      _ = (-1)^m * (-1) := by rw [this]
      _ = (-1)^(m+1) := by rw [pow_succ]
  rw [hsq, hm]

/-- `m! ≠ 0` in `ZMod p` when `m < p`. -/
theorem factorial_ne_zero (p m : ℕ) [Fact p.Prime] (hmp : m < p) :
    ((m.factorial : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro hdvd
  have : p ≤ m := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hdvd
  omega

/-- `p ∤ choose m k` as a nonzero element of `ZMod p`, when `m < p` and `k ≤ m`. -/
theorem choose_ne_zero (p m k : ℕ) [Fact p.Prime] (hmp : m < p) (hk : k ≤ m) :
    ((m.choose k : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro hdvd
  have hfac : p ∣ m.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]
    exact (hdvd.mul_right _).mul_right _
  have : p ≤ m := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hfac
  omega

/-- Easy direction: if `p ≡ 1 (mod 4)` then the determinant is nonzero. -/
theorem easy_direction (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (m : ℕ) (hm : m = (p-1)/2)
    (Mtx : Matrix (Fin m) (Fin m) ℤ)
    (hM : Mtx = fun i j => jacobiSym
      (((i.val+1 : ℕ) : ℤ) * ((i.val+1 : ℕ) : ℤ)
        - ((m.factorial : ℕ) : ℤ) * ((j.val+1 : ℕ) : ℤ)) p) :
    Mtx.det ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · -- p odd; p%4=1 and p prime ⟹ p ≥ 5
      have := hp.two_le; omega
  have hmpos : 0 < m := by omega
  have hmp : m < p := by omega
  have hmeven : m % 2 = 0 := by omega
  -- basic ZMod facts
  set c : ZMod p := ((m.factorial : ℕ) : ZMod p) with hc
  set x : Fin m → ZMod p := fun i => ((i.val + 1 : ℕ) : ZMod p) ^ 2 with hx
  set y : Fin m → ZMod p := fun j => ((j.val + 1 : ℕ) : ZMod p) with hy
  have hcne : c ≠ 0 := factorial_ne_zero p m hmp
  -- the base values are nonzero
  have hbase_ne : ∀ i : Fin m, ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro i
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    have := i.isLt
    omega
  -- x i ^ m = 1
  have hxm : ∀ i : Fin m, x i ^ m = 1 := by
    intro i
    show (((i.val + 1 : ℕ) : ZMod p) ^ 2) ^ m = 1
    rw [← pow_mul, show 2 * m = p - 1 from by omega]
    exact ZMod.pow_card_sub_one_eq_one (hbase_ne i)
  -- the matrix over ZMod p
  set Mbar : Matrix (Fin m) (Fin m) (ZMod p) := fun i j => (x i - c * y j) ^ m with hMbar
  -- Step 1: cast of det
  have hcast : ((Mtx.det : ℤ) : ZMod p) = Mbar.det := by
    have hmap : Mtx.map (Int.castRingHom (ZMod p)) = Mbar := by
      ext i j
      rw [Matrix.map_apply, hM]
      simp only
      rw [eq_intCast, ← jacobiSym.legendreSym.to_jacobiSym p, legendreSym.eq_pow]
      show ((_ : ℤ) : ZMod p) ^ (p/2) = (x i - c * y j) ^ m
      congr 1
      · simp only [hx, hy, hc]; push_cast; ring
      · omega
    calc ((Mtx.det : ℤ) : ZMod p)
        = (Int.castRingHom (ZMod p)) Mtx.det := by rw [eq_intCast]
      _ = (Mtx.map (Int.castRingHom (ZMod p))).det := RingHom.map_det _ _
      _ = Mbar.det := by rw [hmap]
  -- Step 2: Mbar = vandermonde x * G  (define G)
  set G : Matrix (Fin m) (Fin m) (ZMod p) :=
    fun l j => (↑(m.choose l.val) : ZMod p) * (-(c * y j)) ^ (m - l.val)
      + (if l.val = 0 then 1 else 0) with hG
  have hfactor : Mbar = (Matrix.vandermonde x) * G := by
    ext i j
    show (x i - c * y j) ^ m = ((Matrix.vandermonde x) * G) i j
    rw [Matrix.mul_apply]
    simp only [Matrix.vandermonde_apply]
    -- expand each summand
    have e1 : ∀ l : Fin m, x i ^ l.val * G l j
        = x i ^ l.val * ((↑(m.choose l.val) : ZMod p) * (-(c * y j)) ^ (m - l.val))
          + x i ^ l.val * (if l.val = 0 then (1 : ZMod p) else 0) := by
      intro l; simp only [hG]; ring
    rw [Finset.sum_congr rfl (fun l _ => e1 l), Finset.sum_add_distrib]
    -- second sum = 1
    have e2 : (∑ l : Fin m, x i ^ l.val * (if l.val = 0 then (1 : ZMod p) else 0)) = 1 := by
      rw [Finset.sum_eq_single (⟨0, hmpos⟩ : Fin m)]
      · simp
      · intro l _ hl
        have : l.val ≠ 0 := by
          intro hc0; apply hl; exact Fin.ext hc0
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    -- first sum = (x i - c y j)^m - 1
    have e3 : (∑ l : Fin m, x i ^ l.val
          * ((↑(m.choose l.val) : ZMod p) * (-(c * y j)) ^ (m - l.val)))
        = (x i - c * y j) ^ m - 1 := by
      have hap : (x i - c * y j) ^ m
          = ∑ k ∈ Finset.range (m+1), x i ^ k * (-(c * y j)) ^ (m - k) * ↑(m.choose k) := by
        rw [show x i - c * y j = x i + -(c * y j) from by ring]
        exact add_pow (x i) (-(c * y j)) m
      rw [Finset.sum_range_succ] at hap
      have hlast : x i ^ m * (-(c * y j)) ^ (m - m) * (↑(m.choose m) : ZMod p) = 1 := by
        rw [Nat.sub_self, Nat.choose_self]; simp [hxm i]
      rw [hlast] at hap
      rw [Fin.sum_univ_eq_sum_range
        (fun k => x i ^ k * ((↑(m.choose k) : ZMod p) * (-(c * y j)) ^ (m - k))) m]
      have hcomm : (∑ k ∈ Finset.range m,
            x i ^ k * ((↑(m.choose k) : ZMod p) * (-(c * y j)) ^ (m - k)))
          = ∑ k ∈ Finset.range m, x i ^ k * (-(c * y j)) ^ (m - k) * ↑(m.choose k) := by
        apply Finset.sum_congr rfl; intro k _; ring
      rw [hcomm, hap]; ring
    rw [e2, e3]; ring
  -- Step 3
  have hdetfac : Mbar.det = (Matrix.vandermonde x).det * G.det := by
    rw [hfactor, Matrix.det_mul]
  -- Step 4: det vandermonde ≠ 0
  have hxinj : Function.Injective x := by
    intro i j hij
    have h : ((i.val+1:ℕ):ZMod p) * ((i.val+1:ℕ):ZMod p)
        = ((j.val+1:ℕ):ZMod p) * ((j.val+1:ℕ):ZMod p) := by
      have h2 : x i = x j := hij
      simp only [hx, pow_two] at h2
      exact h2
    rw [mul_self_eq_mul_self_iff] at h
    have hi := i.isLt; have hj := j.isLt
    rcases h with h | h
    · apply Fin.ext
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
      have ha : i.val + 1 < p := by omega
      have hb : j.val + 1 < p := by omega
      have hmm : (i.val+1) % p = (j.val+1) % p := hmod
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmm
      omega
    · exfalso
      have h0 : ((i.val+1:ℕ):ZMod p) + ((j.val+1:ℕ):ZMod p) = 0 := by rw [h]; ring
      rw [← Nat.cast_add, CharP.cast_eq_zero_iff (ZMod p) p] at h0
      have := Nat.le_of_dvd (by omega) h0
      omega
  have hdetV : (Matrix.vandermonde x).det ≠ 0 := by
    rw [Ne, Matrix.det_vandermonde_eq_zero_iff]
    rintro ⟨i, j, hij, hne⟩
    exact hne (hxinj hij)
  -- Step 5: det G ≠ 0
  have hdetG : G.det ≠ 0 := by
    have hodd : Odd p := by rw [Nat.odd_iff]; omega
    -- y injective and vandermonde y nonzero
    have hyinj : Function.Injective y := by
      intro a b hab
      have h : ((a.val+1:ℕ):ZMod p) = ((b.val+1:ℕ):ZMod p) := hab
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
      have ha : a.val + 1 < p := by have := a.isLt; omega
      have hb : b.val + 1 < p := by have := b.isLt; omega
      have hmm : (a.val+1) % p = (b.val+1) % p := hmod
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmm
      exact Fin.ext (by omega)
    have hW : (Matrix.vandermonde y).det ≠ 0 := by
      rw [Ne, Matrix.det_vandermonde_eq_zero_iff]
      rintro ⟨a, b, hab, hne⟩; exact hne (hyinj hab)
    -- ∏ y = c
    have hprody : (∏ j : Fin m, y j) = c := by
      rw [hc]
      simp only [hy]
      rw [← Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun k => k+1) m,
        Finset.prod_range_add_one_eq_factorial]
    -- the row-scaling vector d
    set d : Fin m → ZMod p :=
      fun l => (↑(m.choose l.val) : ZMod p) * (-1) ^ (m - l.val) * c ^ (m - l.val) with hd
    have hd_ne : ∀ l : Fin m, d l ≠ 0 := by
      intro l
      simp only [hd]
      apply mul_ne_zero
      apply mul_ne_zero
      · exact choose_ne_zero p m l.val hmp (by have := l.isLt; omega)
      · exact pow_ne_zero _ (by norm_num)
      · exact pow_ne_zero _ hcne
    have hG1eq : ∀ (l j : Fin m),
        (↑(m.choose l.val) : ZMod p) * (-(c * y j)) ^ (m - l.val) = d l * y j ^ (m - l.val) := by
      intro l j
      simp only [hd]
      rw [neg_pow, mul_pow]; ring
    set Vt : Matrix (Fin m) (Fin m) (ZMod p) := (Matrix.vandermonde y)ᵀ with hVt
    set Apure : Matrix (Fin m) (Fin m) (ZMod p) := fun l j => d l * y j ^ (m - l.val) with hAp
    set pt0 : Fin m := ⟨0, hmpos⟩ with hpt0
    -- the negation permutation ρ on Fin m
    set ρf : Fin m → Fin m := fun l => ⟨if l.val = 0 then 0 else m - l.val,
      by have hl := l.isLt; split <;> omega⟩ with hρf
    have hρval : ∀ l : Fin m, (ρf l).val = if l.val = 0 then 0 else m - l.val := fun l => rfl
    have hρinv : Function.Involutive ρf := by
      intro l
      apply Fin.ext
      rw [hρval, hρval]
      have hl := l.isLt
      by_cases h : l.val = 0
      · simp [h]
      · have h2 : ¬ (m - l.val = 0) := by omega
        simp only [h, if_false, h2]; omega
    set ρ : Equiv.Perm (Fin m) := Function.Involutive.toPerm ρf hρinv with hρ
    -- factorization of Apure
    have hApure_eq : Apure = Matrix.diagonal d * (Vt.submatrix Fin.revPerm id) * Matrix.diagonal y := by
      ext l j
      have hl := l.isLt
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      show d l * y j ^ (m - l.val) = d l * (Vt.submatrix Fin.revPerm id) l j * y j
      simp only [hVt, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
        id_eq, Fin.revPerm_apply, Fin.val_rev]
      rw [show m - l.val = (m - (l.val + 1)) + 1 from by omega, pow_succ]; ring
    have hdetApure : Apure.det
        = (∏ l, d l) * (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) : ZMod p) * (Matrix.vandermonde y).det
          * (∏ j, y j) := by
      rw [hApure_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
        Matrix.det_permute, hVt, Matrix.det_transpose]
      ring
    -- factorization of Aones (= Apure with row pt0 replaced by ones)
    set ones : Fin m → ZMod p := fun _ => 1 with hones
    set Aones : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.updateRow Apure pt0 ones with hAones
    set d'' : Fin m → ZMod p := fun l => if l.val = 0 then 1 else d l with hd''
    have hAones_eq : Aones = Matrix.diagonal d'' * (Vt.submatrix ρ id) := by
      ext l j
      rw [Matrix.diagonal_mul, hAones, Matrix.updateRow_apply]
      simp only [hVt, hd'', Matrix.submatrix_apply, Matrix.transpose_apply,
        Matrix.vandermonde_apply, id_eq]
      have hρlv : (ρ l).val = if l.val = 0 then 0 else m - l.val := hρval l
      rw [hρlv]
      by_cases h : l.val = 0
      · have hlp : l = pt0 := Fin.ext (by rw [hpt0]; exact h)
        rw [if_pos hlp]
        simp [hones, h]
      · have hne : l ≠ pt0 := by intro hh; apply h; rw [hh, hpt0]
        simp only [if_neg h, if_neg hne]
        rw [hAp]
    have hdetAones : Aones.det
        = (∏ l, d'' l) * (Equiv.Perm.sign ρ : ZMod p) * (Matrix.vandermonde y).det := by
      rw [hAones_eq, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute, hVt,
        Matrix.det_transpose]
      ring
    -- split det G
    have hGeq : G = Matrix.updateRow Apure pt0 (Apure pt0 + ones) := by
      ext l j
      rw [Matrix.updateRow_apply]
      by_cases h : l = pt0
      · simp only [h, if_pos]
        rw [hG]
        simp only [Pi.add_apply, hones, hAp]
        have : (pt0 : Fin m).val = 0 := by rw [hpt0]
        rw [this]; rw [← hG1eq pt0 j]
        simp [this]
      · rw [if_neg h, hG]
        have hlv : l.val ≠ 0 := by
          intro hh; apply h; exact Fin.ext (by rw [hpt0]; exact hh)
        simp only [hlv, if_false, add_zero]
        rw [hG1eq l j, hAp]
    have hGsplit : G.det = Apure.det + Aones.det := by
      rw [hGeq, det_updateRow_add]
      congr 1
      · congr 1
        ext a b
        rw [Matrix.updateRow_apply]
        by_cases h : a = pt0 <;> simp [h]
    -- now assemble
    rw [hGsplit, hdetApure, hdetAones]
    set s1 : ZMod p := (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) : ZMod p) with hs1
    set s2 : ZMod p := (Equiv.Perm.sign ρ : ZMod p) with hs2
    have hs1sq : s1 ^ 2 = 1 := by
      rw [hs1]; rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with h | h <;>
        rw [h] <;> simp
    have hs2sq : s2 ^ 2 = 1 := by
      rw [hs2]; rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;>
        rw [h] <;> simp
    -- P := ∏ over complement of pt0
    have hsplitprod : (∏ l, d l) = d pt0 * (∏ l ∈ ({pt0} : Finset (Fin m))ᶜ, d l) :=
      Fintype.prod_eq_mul_prod_compl pt0 d
    set P : ZMod p := (∏ l ∈ ({pt0} : Finset (Fin m))ᶜ, d l) with hP
    have hPne : P ≠ 0 := by
      rw [hP, Finset.prod_ne_zero_iff]
      intro l _; exact hd_ne l
    -- ∏ d'' = P
    have hd''prod : (∏ l, d'' l) = P := by
      rw [hP, Fintype.prod_eq_mul_prod_compl pt0 d'']
      have hd''0 : d'' pt0 = 1 := by rw [hd'']; simp [hpt0]
      rw [hd''0, one_mul]
      apply Finset.prod_congr rfl
      intro l hl
      rw [hd'']
      have : l.val ≠ 0 := by
        intro hh
        rw [Finset.mem_compl, Finset.mem_singleton] at hl
        exact hl (Fin.ext (by rw [hpt0]; exact hh))
      simp [this]
    -- d pt0 = (-1)^m * c^m
    have hdpt0 : d pt0 = (-1)^m * c^m := by
      rw [hd]; simp only [hpt0]; simp
    rw [hsplitprod, hd''prod, hdpt0, hprody]
    -- goal: (-1)^m c^m * P * s1 * W * c + P * s2 * W ≠ 0
    -- rewrite W as (vandermonde y).det
    have hkey : ((-1)^m * c^m) * P * s1 * (Matrix.vandermonde y).det * c
        + P * s2 * (Matrix.vandermonde y).det
        = (Matrix.vandermonde y).det * P * (s1 * (-1)^m * c^(m+1) + s2) := by
      ring
    rw [hkey]
    apply mul_ne_zero
    apply mul_ne_zero hW hPne
    -- bracket ≠ 0
    intro hb
    have heq : s1 * (-1)^m * c^(m+1) = -s2 := eq_neg_of_add_eq_zero_left hb
    have h1 : (s1 * (-1)^m * c^(m+1))^2 = 1 := by rw [heq, neg_sq]; exact hs2sq
    have h2 : (s1 * (-1)^m * c^(m+1))^2 = c^(2*(m+1)) := by
      rw [mul_pow, mul_pow, hs1sq,
        show ((-1:ZMod p)^m)^2 = 1 from by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
        one_mul, one_mul, ← pow_mul]
      ring_nf
    rw [h2] at h1
    have hwil : c ^ 2 = (-1)^(m+1) := by
      have hw := wilson_half p hodd
      rw [← hm] at hw
      rw [← hc] at hw
      exact hw
    have hc2 : c^(2*(m+1)) = -1 := by
      rw [pow_mul, hwil, ← pow_mul]
      apply Odd.neg_one_pow
      have hom1 : Odd (m+1) := Nat.odd_iff.mpr (by omega)
      exact hom1.mul hom1
    rw [hc2] at h1
    -- h1 : (-1 : ZMod p) = 1
    have h2ne : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
    apply h2ne
    have htwo : (1 : ZMod p) + 1 = 0 := by linear_combination -h1
    push_cast
    linear_combination htwo
  -- conclude
  have hMbar_ne : Mbar.det ≠ 0 := by rw [hdetfac]; exact mul_ne_zero hdetV hdetG
  intro hzero
  have hz : ((Mtx.det : ℤ) : ZMod p) = 0 := by rw [hzero]; simp
  rw [hcast] at hz
  exact hMbar_ne hz

/-- Cauchy–Binet "function form": for `A : m × N` and `B : N × m`,
    `det (A * B) = ∑_{f : Fin m → Fin N} (∏ i, A i (f i)) * det (B ∘ f)`. -/
  -- cauchy_binet_f (full proof from CB.lean)
theorem cauchy_binet_f {m N : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin m) (Fin N) R) (B : Matrix (Fin N) (Fin m) R) :
    (A * B).det = ∑ f : Fin m → Fin N, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  set D : (Fin m → R) [⋀^Fin m]→ₗ[R] R := Matrix.detRowAlternating with hD
  have hrows : (A * B) = (fun i => ∑ k : Fin N, A i k • B k) := by
    funext i j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have key : (A * B).det = D.toMultilinearMap (fun i => ∑ k : Fin N, A i k • B k) := by
    rw [Matrix.det, ← hrows]; rfl
  rw [key, D.toMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hsmul : D.toMultilinearMap (fun i => A i (r i) • B (r i))
      = (∏ i, A i (r i)) • D.toMultilinearMap (fun i => B (r i)) :=
    D.toMultilinearMap.map_smul_univ (fun i => A i (r i)) (fun i => B (r i))
  have hdet : D.toMultilinearMap (fun i => B (r i)) = (B.submatrix r id).det := by
    rw [Matrix.det]; rfl
  rw [hsmul, hdet, smul_eq_mul]

end A226163Dev
-- ===================== Hard direction =====================
namespace Hard

open Matrix CharM Crux

variable {p : ℕ} [Fact p.Prime]

/-- `m = N p / 2 = (p-1)/2 = half p`. -/
theorem half_eq (p : ℕ) [Fact p.Prime] : N p / 2 = (p - 1) / 2 := by
  rw [card_N]

theorem two_mul_half (hodd : p % 2 = 1) : 2 * (N p / 2) = N p := (N_even hodd).symm

theorem half_odd (h4 : p % 4 = 3) : Odd (N p / 2) := by
  rw [card_N]
  refine ⟨(p - 3) / 4, ?_⟩
  have := (Fact.out : p.Prime).two_le
  omega

/-- `pw` of a difference of discrete logs. -/
theorem pw_sub (a b : ZMod (N p)) : pw p (a - b) = pw p a * (pw p b)⁻¹ := by
  rw [sub_eq_add_neg, pw_add, pw_neg]

/-- The key entry identity (integer level). -/
theorem entry_id (Y V : (ZMod p)ˣ) :
    qc p ((Y : ZMod p) ^ 2 - (V : ZMod p))
      = qc p (1 - ((pw p (dl V - dl (Y ^ 2)) : (ZMod p)ˣ) : ZMod p)) := by
  have hY0 : (Y : ZMod p) ≠ 0 := Units.ne_zero _
  -- value of pw
  have hpw : ((pw p (dl V - dl (Y ^ 2)) : (ZMod p)ˣ) : ZMod p)
      = (V : ZMod p) * ((Y : ZMod p) ^ 2)⁻¹ := by
    rw [pw_sub, pw_dl, pw_dl]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  rw [hpw]
  -- Y^2 - V = Y^2 * (1 - V * (Y^2)⁻¹)
  have hfac : (Y : ZMod p) ^ 2 - (V : ZMod p)
      = (Y : ZMod p) ^ 2 * (1 - (V : ZMod p) * ((Y : ZMod p) ^ 2)⁻¹) := by
    have hY2 : (Y : ZMod p) ^ 2 ≠ 0 := pow_ne_zero _ hY0
    field_simp
  rw [hfac, map_mul]
  have hsq : qc p ((Y : ZMod p) ^ 2) = 1 := by
    rw [sq, map_mul]
    have : qc p (Y : ZMod p) ^ 2 = 1 := quadraticChar_sq_one hY0
    rw [← sq]; exact this
  rw [hsq, one_mul]

/-- The regrouping bijection `Fin m × Fin 2 → ZMod (N p)`, `(k,t) ↦ k + m t`. -/
theorem regroup_bij (hodd : p % 2 = 1) :
    Function.Bijective
      (fun x : Fin (N p / 2) × Fin 2 =>
        ((x.1.val + (N p / 2) * x.2.val : ℕ) : ZMod (N p))) := by
  set m := N p / 2 with hm
  have h2m : 2 * m = N p := two_mul_half hodd
  have hmpos : 0 < m := by have := @N_pos p _; omega
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨k, t⟩ ⟨k', t'⟩ h
    simp only at h
    have hlt : k.val + m * t.val < N p := by
      have h1 := k.isLt; have h2 := t.isLt
      have : m * t.val ≤ m * 1 := Nat.mul_le_mul_left _ (by omega)
      omega
    have hlt' : k'.val + m * t'.val < N p := by
      have h1 := k'.isLt; have h2 := t'.isLt
      have : m * t'.val ≤ m * 1 := Nat.mul_le_mul_left _ (by omega)
      omega
    have hN : (k.val + m * t.val) = (k'.val + m * t'.val) := by
      have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
      rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at this
    have hk := k.isLt; have hk' := k'.isLt
    have ht := t.isLt; have ht' := t'.isLt
    ext
    · show k.val = k'.val
      have e1 : (k.val + m * t.val) % m = k.val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
      have e2 : (k'.val + m * t'.val) % m = k'.val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk']
      rw [← e1, ← e2, hN]
    · show t.val = t'.val
      have e1 : (k.val + m * t.val) / m = t.val := by
        rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt hk, zero_add]
      have e2 : (k'.val + m * t'.val) / m = t'.val := by
        rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt hk', zero_add]
      rw [← e1, ← e2, hN]
  · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ZMod.card]
    omega

theorem sum_regroup (hodd : p % 2 = 1) (G : ZMod (N p) → ℂ) :
    ∑ a : ZMod (N p), G a
      = ∑ k : Fin (N p / 2), ∑ t : Fin 2,
          G (((k.val + (N p / 2) * t.val : ℕ) : ZMod (N p))) := by
  rw [← (Fintype.sum_bijective _ (regroup_bij hodd)
        (fun x => G ((x.1.val + (N p / 2) * x.2.val : ℕ) : ZMod (N p)))
        (fun a => G a) (fun x => rfl))]
  rw [Fintype.sum_prod_type]

/-- The entrywise factorization `M̄ = Φ · K`. -/
theorem MeqPhiK (hodd : p % 2 = 1) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p))
    (γ δ : Fin (N p / 2) → ZMod (N p))
    (hδ : ∀ i, ((N p / 2 : ℕ) : ZMod (N p)) * δ i = 0)
    (i j : Fin (N p / 2)) :
    hf ζ (γ j - δ i)
      = ∑ k : Fin (N p / 2),
          ze ζ (-((k.val : ZMod (N p)) * δ i)) *
          (∑ t : Fin 2, hhat ζ (((k.val + (N p / 2) * t.val : ℕ) : ZMod (N p))) *
              ze ζ (((k.val + (N p / 2) * t.val : ℕ) : ZMod (N p)) * γ j)) := by
  rw [fourier_inv ζ hζ]
  have step1 : ∀ a : ZMod (N p), hhat ζ a * ze ζ (a * (γ j - δ i))
      = hhat ζ a * ze ζ (a * γ j) * ze ζ (-(a * δ i)) := by
    intro a
    rw [show a * (γ j - δ i) = a * γ j + (-(a * δ i)) by ring, ze_add ζ hζ]
    ring
  rw [Finset.sum_congr rfl (fun a _ => step1 a), sum_regroup hodd]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hkey : (((k.val + (N p / 2) * t.val : ℕ) : ZMod (N p))) * δ i
      = (k.val : ZMod (N p)) * δ i := by
    push_cast
    rw [add_mul,
      show ((N p / 2 : ℕ) : ZMod (N p)) * (t.val : ZMod (N p)) * δ i
        = (t.val : ZMod (N p)) * (((N p / 2 : ℕ) : ZMod (N p)) * δ i) by ring,
      hδ i, mul_zero, add_zero]
  rw [hkey]; ring

/-- `ze` of a product as a power of the integer product of vals. -/
theorem ze_mul_eq (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (x y : ZMod (N p)) :
    ze ζ (x * y) = ζ ^ (x.val * y.val) := by
  rw [ze, ZMod.val_mul]
  conv_rhs => rw [← Nat.div_add_mod (x.val * y.val) (N p)]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

/-- The regrouped Fourier modes. -/
noncomputable def aa (k : Fin (N p / 2)) (t : Fin 2) : ZMod (N p) :=
  ((k.val + (N p / 2) * t.val : ℕ) : ZMod (N p))

theorem aa_val (hodd : p % 2 = 1) (k : Fin (N p / 2)) (t : Fin 2) :
    (aa k t).val = k.val + (N p / 2) * t.val := by
  rw [aa, ZMod.val_natCast_of_lt]
  have h2m := two_mul_half hodd
  have := k.isLt; have := t.isLt
  have hmt : (N p / 2) * t.val ≤ (N p / 2) * 1 := Nat.mul_le_mul_left _ (by omega)
  omega

/-- The exponential matrix for a transversal choice `ε`. -/
noncomputable def Dm (ζ : ℂ) (γ : Fin (N p / 2) → ZMod (N p)) (ε : Fin (N p / 2) → Fin 2) :
    Matrix (Fin (N p / 2)) (Fin (N p / 2)) ℂ :=
  fun k j => ze ζ (aa k (ε k) * γ j)

/-- The summand in the multilinear expansion of `det K`. -/
noncomputable def Tt (ζ : ℂ) (γ : Fin (N p / 2) → ZMod (N p)) (ε : Fin (N p / 2) → Fin 2) : ℂ :=
  (∏ k, hhat ζ (aa k (ε k))) * (Dm ζ γ ε).det

/-- The matrix `K`. -/
noncomputable def Kmat (ζ : ℂ) (γ : Fin (N p / 2) → ZMod (N p)) :
    Matrix (Fin (N p / 2)) (Fin (N p / 2)) ℂ :=
  fun k j => ∑ t : Fin 2, hhat ζ (aa k t) * ze ζ (aa k t * γ j)

/-- The conjugation symmetry of `det (Dm ε)`, via `Crux.crux` and a transversal column structure. -/
theorem conj_det_Dm (hp4 : p % 4 = 3) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p))
    (γ : Fin (N p / 2) → ZMod (N p)) (ε : Fin (N p / 2) → Fin 2)
    (π : Equiv.Perm (Fin (N p / 2))) (b : Fin (N p / 2) → Fin 2)
    (hπb : ∀ j, (γ j).val = (π j).val + (N p / 2) * (b (π j)).val) :
    (starRingEnd ℂ) ((Dm ζ γ ε).det)
      = (-1) ^ ((N p / 2 - 1) / 2) * (Dm ζ γ ε).det := by
  have hodd : p % 2 = 1 := by omega
  have hmodd : Odd (N p / 2) := half_odd hp4
  have hζ2 : IsPrimitiveRoot ζ (2 * (N p / 2)) := (two_mul_half hodd).symm ▸ hζ
  -- Dm = (Crux.D ε b ζ).submatrix id π
  have hmat : Dm ζ γ ε = (Crux.D ε b ζ).submatrix id π := by
    funext k j
    show ze ζ (aa k (ε k) * γ j) = ζ ^ (Crux.ex (k, ε k) * Crux.ex (π j, b (π j)))
    rw [ze_mul_eq ζ hζ]
    congr 1
    rw [aa_val hodd, Crux.ex, Crux.ex, hπb j]
  rw [hmat, Matrix.det_permute', map_mul, Crux.crux ε b hmodd ζ hζ2]
  have hconjsign : (starRingEnd ℂ) (((Equiv.Perm.sign π : ℤ) : ℂ)) = ((Equiv.Perm.sign π : ℤ) : ℂ) := by
    simp
  rw [hconjsign]
  ring

/-- Row permutation `ρ : k ↦ (m - k) mod m`. -/
noncomputable def rhoFun (k : Fin (N p / 2)) : Fin (N p / 2) :=
  ⟨(N p / 2 - k.val) % (N p / 2), Nat.mod_lt _ (by have := k.isLt; omega)⟩

theorem rhoFun_zero {l : Fin (N p / 2)} (hl : l.val = 0) : rhoFun (p := p) l = l := by
  apply Fin.ext; show (N p / 2 - l.val) % (N p / 2) = l.val; rw [hl]; simp

theorem rhoFun_val {l : Fin (N p / 2)} (hl : l.val ≠ 0) :
    (rhoFun (p := p) l).val = N p / 2 - l.val := by
  show (N p / 2 - l.val) % (N p / 2) = N p / 2 - l.val
  have := l.isLt; rw [Nat.mod_eq_of_lt (by omega)]

theorem rho_involutive : Function.Involutive (rhoFun (p := p)) := by
  intro k
  have hk := k.isLt
  apply Fin.ext
  show ((N p / 2) - ((N p / 2 - k.val) % (N p / 2))) % (N p / 2) = k.val
  rcases Nat.eq_zero_or_pos k.val with h0 | h0
  · rw [h0]; simp [Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega : N p / 2 - k.val < N p / 2)]
    rw [show N p / 2 - (N p / 2 - k.val) = k.val by omega, Nat.mod_eq_of_lt hk]

/-- `ρ` as a permutation. -/
noncomputable def rhoPerm : Equiv.Perm (Fin (N p / 2)) :=
  Function.Involutive.toPerm _ rho_involutive

theorem rhoPerm_apply (k : Fin (N p / 2)) : rhoPerm k = rhoFun k := rfl

theorem flip2_flip2 (c : Fin 2) : Crux.flip2 (Crux.flip2 c) = c := by fin_cases c <;> decide

/-- The involution `σ` on transversal choices. -/
noncomputable def sig (ε : Fin (N p / 2) → Fin 2) : Fin (N p / 2) → Fin 2 :=
  fun l => if l.val = 0 then Crux.flip2 (ε (rhoFun l)) else ε (rhoFun l)

theorem sig_involutive (ε : Fin (N p / 2) → Fin 2) : sig (sig ε) = ε := by
  funext l
  have hk := l.isLt
  by_cases hl : l.val = 0
  · have hrho0 := rhoFun_zero (p := p) hl
    show (if l.val = 0 then Crux.flip2 (sig ε (rhoFun l)) else sig ε (rhoFun l)) = ε l
    rw [if_pos hl, hrho0]
    show Crux.flip2 (if l.val = 0 then Crux.flip2 (ε (rhoFun l)) else ε (rhoFun l)) = ε l
    rw [if_pos hl, hrho0, flip2_flip2]
  · have hrhone : (rhoFun (p := p) l).val ≠ 0 := by rw [rhoFun_val hl]; omega
    show (if l.val = 0 then Crux.flip2 (sig ε (rhoFun l)) else sig ε (rhoFun l)) = ε l
    rw [if_neg hl]
    show (if (rhoFun l).val = 0 then Crux.flip2 (ε (rhoFun (rhoFun l)))
        else ε (rhoFun (rhoFun l))) = ε l
    rw [if_neg hrhone, rho_involutive l]

theorem flip2_val (c : Fin 2) : (Crux.flip2 c).val = 1 - c.val := by fin_cases c <;> decide

/-- The key additive identity: `aa k (σε k) + aa (ρk) (ε (ρk)) = half`. -/
theorem aa_sum (hodd : p % 2 = 1) (ε : Fin (N p / 2) → Fin 2) (k : Fin (N p / 2)) :
    aa k (sig ε k) + aa (rhoFun k) (ε (rhoFun k)) = half p := by
  have hk := k.isLt
  have h2m := two_mul_half hodd
  rw [aa, aa, half, ← Nat.cast_add]
  have hcast : ∀ s c : ℕ, s = N p / 2 + N p * c →
      ((s : ZMod (N p)) = ((N p / 2 : ℕ) : ZMod (N p))) := by
    intro s c hs
    rw [hs, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
  by_cases hl : k.val = 0
  · rw [rhoFun_zero hl]
    have hsig : (sig ε k).val = 1 - (ε k).val := by
      show (if k.val = 0 then Crux.flip2 (ε (rhoFun k)) else ε (rhoFun k)).val = _
      rw [if_pos hl, rhoFun_zero hl, flip2_val]
    rw [hsig, hl]
    refine hcast _ 0 ?_
    have h1 : (ε k).val = 0 ∨ (ε k).val = 1 := by have := (ε k).isLt; omega
    rcases h1 with h | h <;> rw [h] <;> omega
  · have hrv := rhoFun_val hl
    have hsig : (sig ε k).val = (ε (rhoFun k)).val := by
      show (if k.val = 0 then Crux.flip2 (ε (rhoFun k)) else ε (rhoFun k)).val = _
      rw [if_neg hl]
    rw [hsig, hrv]
    have h1 : (ε (rhoFun (p := p) k)).val = 0 ∨ (ε (rhoFun (p := p) k)).val = 1 := by
      have := (ε (rhoFun (p := p) k)).isLt; omega
    rcases h1 with h | h
    · exact hcast _ 0 (by rw [h]; omega)
    · exact hcast _ 1 (by rw [h]; omega)

theorem inner_eq {n : ℕ} (j : Fin n) :
    ∑ i ∈ Finset.Iio j, (if i.val = 0 then 0 else 1) = j.val - 1 := by
  have hn : 0 < n := by have := j.isLt; omega
  have he : (Finset.filter (fun i : Fin n => ¬ i.val = 0) (Finset.Iio j))
      = (Finset.Iio j).erase ⟨0, hn⟩ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Iio]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun h => h2 (by rw [h]), h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, fun h => h1 (Fin.ext h)⟩
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, zero_add, smul_eq_mul, mul_one, he,
    Finset.card_erase_eq_ite]
  have h1 : (Finset.Iio j).card = j.val := by simp
  rw [h1]
  by_cases hj : (⟨0, hn⟩ : Fin n) ∈ Finset.Iio j
  · rw [if_pos hj]
  · rw [if_neg hj]; rw [Finset.mem_Iio] at hj; simp only [Fin.lt_def, not_lt] at hj; omega

theorem sum_range_pred_add (m : ℕ) :
    (∑ k ∈ Finset.range m, (k - 1)) + (m - 1) = ∑ k ∈ Finset.range m, k := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · omega

/-- Comparison for the inversion count of `ρ`. -/
theorem rho_lt_iff (hodd : p % 2 = 1) (i j : Fin (N p / 2)) (hij : i.val < j.val) :
    (rhoPerm (p := p) i < rhoPerm j) ↔ i.val = 0 := by
  have hjm := j.isLt
  rw [rhoPerm_apply, rhoPerm_apply, Fin.lt_def]
  constructor
  · intro h
    by_contra hi0
    rw [rhoFun_val hi0, rhoFun_val (by omega : j.val ≠ 0)] at h
    omega
  · intro hi0
    have hival : (rhoFun (p := p) i).val = 0 := by
      rw [show i = (⟨0, by omega⟩ : Fin (N p / 2)) from Fin.ext hi0]
      show (N p / 2 - 0) % (N p / 2) = 0; simp
    rw [hival, rhoFun_val (by omega : j.val ≠ 0)]
    omega

/-- Sign of `ρ`. -/
theorem sign_rhoPerm (hp4 : p % 4 = 3) :
    ((Equiv.Perm.sign (rhoPerm (p := p)) : ℤ) : ℂ) = (-1) ^ ((N p / 2 - 1) / 2) := by
  have hodd : p % 2 = 1 := by omega
  obtain ⟨t, ht⟩ : Odd (N p / 2) := half_odd hp4
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  have hterm : ∀ j : Fin (N p / 2), ∀ i ∈ Finset.Iio j,
      (if rhoPerm (p := p) i < rhoPerm j then (1 : ℤˣ) else -1)
        = (-1 : ℤˣ) ^ (if i.val = 0 then 0 else 1) := by
    intro j i hi
    rw [Finset.mem_Iio, Fin.lt_def] at hi
    by_cases h0 : i.val = 0
    · rw [if_pos ((rho_lt_iff hodd i j hi).2 h0), if_pos h0, pow_zero]
    · rw [if_neg (by rw [rho_lt_iff hodd i j hi]; exact h0), if_neg h0, pow_one]
  rw [Finset.prod_congr rfl (fun j _ => Finset.prod_congr rfl (hterm j))]
  -- now ∏ j ∏ i∈Iio j (-1)^(e i)  =  (-1)^E
  have hpow : ∀ j : Fin (N p / 2),
      ∏ i ∈ Finset.Iio j, (-1 : ℤˣ) ^ (if i.val = 0 then 0 else 1)
        = (-1 : ℤˣ) ^ (∑ i ∈ Finset.Iio j, (if i.val = 0 then 0 else 1)) :=
    fun j => Finset.prod_pow_eq_pow_sum _ _ _
  rw [Finset.prod_congr rfl (fun j _ => hpow j), Finset.prod_pow_eq_pow_sum]
  -- exponent E
  set E := ∑ j : Fin (N p / 2), ∑ i ∈ Finset.Iio j, (if i.val = 0 then 0 else 1) with hE
  have hEval : E % 2 = ((N p / 2 - 1) / 2) % 2 := by
    have hEeq : ∑ k ∈ Finset.range (N p / 2), (k - 1) = E := by
      rw [hE, Finset.sum_congr rfl (fun j _ => inner_eq j),
        Fin.sum_univ_eq_sum_range (fun k => k - 1)]
    have hadd := sum_range_pred_add (N p / 2)
    have hgauss := Finset.sum_range_id_mul_two (N p / 2)
    rw [hEeq] at hadd
    set S := ∑ k ∈ Finset.range (N p / 2), k with hS
    rw [ht] at hadd hgauss ⊢
    simp only [Nat.add_sub_cancel] at hadd hgauss ⊢
    rw [show (2 * t + 1) * (2 * t) = 4 * (t * t) + 2 * t by ring] at hgauss
    omega
  rw [Units.val_pow_eq_pow_val]
  push_cast
  rw [neg_one_pow_eq_pow_mod_two (n := E), neg_one_pow_eq_pow_mod_two (n := (N p / 2 - 1) / 2),
    hEval]

/-- Multilinear expansion of `det K`. -/
theorem detK_expand (ζ : ℂ) (γ : Fin (N p / 2) → ZMod (N p)) :
    (Kmat ζ γ).det = ∑ ε : Fin (N p / 2) → Fin 2, Tt ζ γ ε := by
  set D : (Fin (N p / 2) → ℂ) [⋀^Fin (N p / 2)]→ₗ[ℂ] ℂ := Matrix.detRowAlternating with hD
  have hrows : (Kmat ζ γ)
      = (fun k => ∑ t : Fin 2, hhat ζ (aa k t) • (fun j => ze ζ (aa k t * γ j))) := by
    funext k j
    simp only [Kmat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have key : (Kmat ζ γ).det
      = D.toMultilinearMap (fun k => ∑ t : Fin 2, hhat ζ (aa k t) • (fun j => ze ζ (aa k t * γ j))) := by
    rw [Matrix.det, ← hrows]; rfl
  rw [key, D.toMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro ε _
  have hsmul : D.toMultilinearMap (fun k => hhat ζ (aa k (ε k)) • (fun j => ze ζ (aa k (ε k) * γ j)))
      = (∏ k, hhat ζ (aa k (ε k))) • D.toMultilinearMap (fun k => (fun j => ze ζ (aa k (ε k) * γ j))) :=
    D.toMultilinearMap.map_smul_univ _ _
  have hdet : D.toMultilinearMap (fun k => (fun j => ze ζ (aa k (ε k) * γ j))) = (Dm ζ γ ε).det := by
    rw [Matrix.det]; rfl
  rw [hsmul, hdet, smul_eq_mul, Tt]

/-- `ze (-x) = conj (ze x)` since `|ζ| = 1`. -/
theorem ze_neg_conj (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) (x : ZMod (N p)) :
    ze (p := p) ζ (-x) = (starRingEnd ℂ) (ze (p := p) ζ x) := by
  have hζ1 : ‖ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by have := @N_pos p _; omega)
  have hznorm : ‖ze (p := p) ζ x‖ = 1 := by rw [ze, norm_pow, hζ1, one_pow]
  have hne : ze (p := p) ζ x ≠ 0 := by rw [← norm_ne_zero_iff, hznorm]; norm_num
  have hmul : ze (p := p) ζ (-x) * ze (p := p) ζ x = 1 := by
    rw [← ze_add ζ hζ, neg_add_cancel, ze_zero]
  rw [← Complex.inv_eq_conj hznorm]
  field_simp [hne]
  linear_combination hmul

/-- Entry relation between `Dm (sig ε)` and `Dm ε` after the `ρ` row permutation. -/
theorem Dm_sig_entry (hodd : p % 2 = 1) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p))
    (γ : Fin (N p / 2) → ZMod (N p)) (ε : Fin (N p / 2) → Fin 2)
    (k j : Fin (N p / 2)) :
    Dm ζ γ (sig ε) k j
      = (-1 : ℂ) ^ (γ j).val * (starRingEnd ℂ) (Dm ζ γ ε (rhoFun k) j) := by
  show ze ζ (aa k (sig ε k) * γ j) = _
  have hs : aa k (sig ε k) = half p - aa (rhoFun k) (ε (rhoFun k)) :=
    eq_sub_of_add_eq (aa_sum hodd ε k)
  rw [hs, show (half p - aa (rhoFun k) (ε (rhoFun k))) * γ j
        = half p * γ j + (-(aa (rhoFun k) (ε (rhoFun k)) * γ j)) by ring,
      ze_add ζ hζ, ze_half_mul hodd ζ hζ, ze_neg_conj ζ hζ]
  rfl

/-- The determinant invariance `det (Dm (sig ε)) = det (Dm ε)`. -/
theorem det_Dm_sig (hp4 : p % 4 = 3) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p))
    (γ : Fin (N p / 2) → ZMod (N p)) (ε : Fin (N p / 2) → Fin 2)
    (π : Equiv.Perm (Fin (N p / 2))) (b : Fin (N p / 2) → Fin 2)
    (hπb : ∀ j, (γ j).val = (π j).val + (N p / 2) * (b (π j)).val)
    (hPg : ∏ j : Fin (N p / 2), (-1 : ℂ) ^ (γ j).val = 1) :
    (Dm ζ γ (sig ε)).det = (Dm ζ γ ε).det := by
  have hodd : p % 2 = 1 := by omega
  set d : Fin (N p / 2) → ℂ := fun j => (-1 : ℂ) ^ (γ j).val with hd
  set B : Matrix (Fin (N p / 2)) (Fin (N p / 2)) ℂ := (Dm ζ γ ε).map (starRingEnd ℂ) with hB
  have hBdet : B.det = (starRingEnd ℂ) ((Dm ζ γ ε).det) := by
    rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hfac : Dm ζ γ (sig ε) = (B.submatrix rhoPerm id) * Matrix.diagonal d := by
    funext k j
    rw [Matrix.mul_diagonal]
    simp only [Matrix.submatrix_apply, rhoPerm_apply, hB, Matrix.map_apply, id_eq]
    rw [Dm_sig_entry hodd ζ hζ]
    rw [hd]
    ring
  have hprod : (∏ i, d i) = 1 := hPg
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute, hBdet, hprod, mul_one,
    conj_det_Dm hp4 ζ hζ γ ε π b hπb, sign_rhoPerm hp4]
  rw [← mul_assoc, ← pow_add,
    show (N p / 2 - 1) / 2 + (N p / 2 - 1) / 2 = 2 * ((N p / 2 - 1) / 2) by ring, pow_mul]
  norm_num

/-- `pw (half) = -1`: the generator to the half power is `-1`. -/
theorem pw_half (hodd : p % 2 = 1) : pw p (half p) = -1 := by
  have hne : half p ≠ (0 : ZMod (N p)) := by
    rw [half]
    have hlt : N p / 2 < N p := by have := @N_pos p _; omega
    have hpos : 0 < N p / 2 := by
      rw [card_N]; have := (Fact.out : p.Prime).two_le; omega
    intro hc
    have hv := ZMod.val_natCast_of_lt hlt
    rw [hc, ZMod.val_zero] at hv; omega
  have hval : ((pw p (half p) : (ZMod p)ˣ) : ZMod p) = -1 := by
    have hsq : (((pw p (half p) : (ZMod p)ˣ) : ZMod p)) * (((pw p (half p)) : ZMod p)) = 1 := by
      rw [← Units.val_mul, ← pw_add]
      have h0 : half p + half p = 0 := by
        rw [half, ← Nat.cast_add, ← two_mul, ← N_even hodd, ZMod.natCast_self]
      rw [h0, pw_zero, Units.val_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exfalso
      have hu1 : pw p (half p) = 1 := Units.ext h
      have hz : half p = 0 := by rw [← dl_pw (half p), hu1, ← pw_zero, dl_pw]
      exact hne hz
    · exact h
  exact Units.ext (by rw [hval, Units.val_neg, Units.val_one])

/-- `g ^ (N/2) = -1` for the generator `g = pw 1`. -/
theorem gen_pow_half (hodd : p % 2 = 1) : (pw p 1) ^ (N p / 2) = -1 := by
  have hv : (half p).val = N p / 2 := by
    rw [half, ZMod.val_natCast_of_lt]; have := @N_pos p _; omega
  rw [← hv, ← pw_eq_gen_pow, pw_half hodd]

/-- Injectivity of `j ↦ (dl (V j)).val % (N p / 2)` when the `V j` have no `±` collision. -/
theorem gamma_val_mod_inj (hodd : p % 2 = 1) {ν : ℕ} (V : Fin ν → (ZMod p)ˣ)
    (hV : ∀ a b : Fin ν, V a = V b ∨ V a = - V b → a = b)
    (a b : Fin ν)
    (hab : (dl (V a)).val % (N p / 2) = (dl (V b)).val % (N p / 2)) :
    a = b := by
  have h2m : 2 * (N p / 2) = N p := two_mul_half hodd
  have hmpos : 0 < N p / 2 := by have := @N_pos p _; omega
  have hx : (dl (V a)).val < 2 * (N p / 2) := by rw [h2m]; exact ZMod.val_lt _
  have hy : (dl (V b)).val < 2 * (N p / 2) := by rw [h2m]; exact ZMod.val_lt _
  have hVa : V a = (pw p 1) ^ (dl (V a)).val := by rw [← pw_eq_gen_pow, pw_dl]
  have hVb : V b = (pw p 1) ^ (dl (V b)).val := by rw [← pw_eq_gen_pow, pw_dl]
  have hgm : (pw p 1) ^ (N p / 2) = -1 := gen_pow_half hodd
  apply hV a b
  rcases le_total (dl (V a)).val (dl (V b)).val with hle | hle
  · have hdvd : (N p / 2) ∣ (dl (V b)).val - (dl (V a)).val :=
      (Nat.modEq_iff_dvd' hle).mp hab
    obtain ⟨k, hk⟩ := hdvd
    have hb2 : (N p / 2) * k < (N p / 2) * 2 := by rw [← hk]; omega
    have hk2 : k < 2 := Nat.lt_of_mul_lt_mul_left hb2
    interval_cases k
    · left
      have hxy : (dl (V a)).val = (dl (V b)).val := by omega
      rw [hVa, hVb, hxy]
    · right
      have hxy : (dl (V b)).val = (dl (V a)).val + N p / 2 := by omega
      rw [hVa, hVb, hxy, pow_add, hgm, mul_neg_one, neg_neg]
  · have hdvd : (N p / 2) ∣ (dl (V a)).val - (dl (V b)).val :=
      (Nat.modEq_iff_dvd' hle).mp hab.symm
    obtain ⟨k, hk⟩ := hdvd
    have hb2 : (N p / 2) * k < (N p / 2) * 2 := by rw [← hk]; omega
    have hk2 : k < 2 := Nat.lt_of_mul_lt_mul_left hb2
    interval_cases k
    · left
      have hxy : (dl (V a)).val = (dl (V b)).val := by omega
      rw [hVa, hVb, hxy]
    · right
      have hxy : (dl (V a)).val = (dl (V b)).val + N p / 2 := by omega
      rw [hVa, hVb, hxy, pow_add, hgm, mul_neg_one]

/-- Construction of the transversal `(π, b)` for `γ j = dl (V j)`. -/
theorem transversal (hodd : p % 2 = 1) (V : Fin (N p / 2) → (ZMod p)ˣ)
    (hV : ∀ a b : Fin (N p / 2), V a = V b ∨ V a = - V b → a = b) :
    ∃ (π : Equiv.Perm (Fin (N p / 2))) (b : Fin (N p / 2) → Fin 2),
      ∀ j, (dl (V j)).val = (π j).val + (N p / 2) * (b (π j)).val := by
  have h2m : 2 * (N p / 2) = N p := two_mul_half hodd
  have hmpos : 0 < N p / 2 := by have := @N_pos p _; omega
  have hvlt : ∀ j, (dl (V j)).val < 2 * (N p / 2) := fun j => by rw [h2m]; exact ZMod.val_lt _
  let f : Fin (N p / 2) → Fin (N p / 2) :=
    fun j => ⟨(dl (V j)).val % (N p / 2), Nat.mod_lt _ hmpos⟩
  have hf_inj : Function.Injective f := by
    intro a b h
    exact gamma_val_mod_inj hodd V hV a b (congrArg Fin.val h)
  let π : Equiv.Perm (Fin (N p / 2)) :=
    Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf_inj)
  refine ⟨π, fun j => ⟨(dl (V (π.symm j))).val / (N p / 2), ?_⟩, ?_⟩
  · exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hvlt _)
  · intro j
    have hπj : (π j).val = (dl (V j)).val % (N p / 2) := rfl
    have hsymm : π.symm (π j) = j := Equiv.symm_apply_apply π j
    show (dl (V j)).val = (π j).val + (N p / 2) * ((dl (V (π.symm (π j)))).val / (N p / 2))
    rw [hsymm, hπj]
    exact (Nat.mod_add_div _ _).symm

/-- The product flip: `∏ hhat (aa k (σε k)) = - ∏ hhat (aa k (ε k))`. -/
theorem prod_flip (hp4 : p % 4 = 3) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p))
    (ε : Fin (N p / 2) → Fin 2) :
    ∏ k, hhat ζ (aa k (sig ε k)) = - ∏ k, hhat ζ (aa k (ε k)) := by
  have hodd : p % 2 = 1 := by omega
  have hmodd : Odd (N p / 2) := half_odd hp4
  have hstep : ∀ k : Fin (N p / 2),
      hhat ζ (aa k (sig ε k)) = - hhat ζ (aa (rhoFun k) (ε (rhoFun k))) := by
    intro k
    rw [show aa k (sig ε k) = half p - aa (rhoFun k) (ε (rhoFun k)) from
        eq_sub_of_add_eq (aa_sum hodd ε k)]
    exact hhat_symm hp4 ζ hζ _
  have hre : ∏ k, hhat ζ (aa (rhoFun k) (ε (rhoFun k))) = ∏ k, hhat ζ (aa k (ε k)) :=
    Equiv.prod_comp rhoPerm (fun k => hhat ζ (aa k (ε k)))
  rw [Finset.prod_congr rfl (fun k _ => hstep k),
    Finset.prod_congr rfl
      (fun k _ => (neg_one_mul (hhat ζ (aa (rhoFun k) (ε (rhoFun k))))).symm),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    hmodd.neg_one_pow, hre, neg_one_mul]

/-- The involution sign relation `Tt (sig ε) = - Tt ε`. -/
theorem Tt_sig (hp4 : p % 4 = 3) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p))
    (γ : Fin (N p / 2) → ZMod (N p)) (ε : Fin (N p / 2) → Fin 2)
    (π : Equiv.Perm (Fin (N p / 2))) (b : Fin (N p / 2) → Fin 2)
    (hπb : ∀ j, (γ j).val = (π j).val + (N p / 2) * (b (π j)).val)
    (hPg : ∏ j : Fin (N p / 2), (-1 : ℂ) ^ (γ j).val = 1) :
    Tt ζ γ (sig ε) = - Tt ζ γ ε := by
  rw [Tt, Tt, prod_flip hp4 ζ hζ ε, det_Dm_sig hp4 ζ hζ γ ε π b hπb hPg]
  ring

/-- `det K = 0` by the sign-reversing involution `sig`. -/
theorem detK_zero (hp4 : p % 4 = 3) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p))
    (γ : Fin (N p / 2) → ZMod (N p))
    (π : Equiv.Perm (Fin (N p / 2))) (b : Fin (N p / 2) → Fin 2)
    (hπb : ∀ j, (γ j).val = (π j).val + (N p / 2) * (b (π j)).val)
    (hPg : ∏ j : Fin (N p / 2), (-1 : ℂ) ^ (γ j).val = 1) :
    (Kmat ζ γ).det = 0 := by
  rw [detK_expand]
  refine Finset.sum_involution (fun ε _ => sig ε) ?_ ?_ ?_ ?_
  · intro ε _
    rw [Tt_sig hp4 ζ hζ γ ε π b hπb hPg]; ring
  · intro ε _ hε hcontra
    apply hε
    have hcontra' : sig ε = ε := hcontra
    have h := Tt_sig hp4 ζ hζ γ ε π b hπb hPg
    rw [hcontra'] at h
    linear_combination h / 2
  · intro ε _; exact Finset.mem_univ _
  · intro ε _; exact sig_involutive ε

/-- Hard direction: if `p ≡ 3 (mod 4)` then the determinant is zero. -/
theorem hard_direction (hp4 : p % 4 = 3)
    (m : ℕ) (hm : m = (p - 1) / 2)
    (Mtx : Matrix (Fin m) (Fin m) ℤ)
    (hM : Mtx = fun i j => jacobiSym
      (((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ)
        - ((m.factorial : ℕ) : ℤ) * ((j.val + 1 : ℕ) : ℤ)) p)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (N p)) :
    Mtx.det = 0 := by
  have hp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := by omega
  have hmN : m = N p / 2 := by rw [card_N]; exact hm
  subst hmN
  have hMp : N p / 2 < p := by rw [card_N]; have := hp.two_le; omega
  -- nonzero casts
  have hFne : (((N p / 2).factorial : ℕ) : ZMod p) ≠ 0 := A226163Dev.factorial_ne_zero p (N p / 2) hMp
  have hJne : ∀ j : Fin (N p / 2), ((j.val + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro j
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hjp : j.val + 1 < p := by have := j.isLt; omega
    have := Nat.le_of_dvd (by omega) h
    omega
  -- units
  let Fu : (ZMod p)ˣ := Units.mk0 (((N p / 2).factorial : ℕ) : ZMod p) hFne
  let Ju : Fin (N p / 2) → (ZMod p)ˣ := fun j => Units.mk0 ((j.val + 1 : ℕ) : ZMod p) (hJne j)
  let Yu : Fin (N p / 2) → (ZMod p)ˣ := fun i => Units.mk0 ((i.val + 1 : ℕ) : ZMod p) (hJne i)
  let V : Fin (N p / 2) → (ZMod p)ˣ := fun j => Fu * Ju j
  let γ : Fin (N p / 2) → ZMod (N p) := fun j => dl (V j)
  let δ : Fin (N p / 2) → ZMod (N p) := fun i => dl ((Yu i) ^ 2)
  -- unit value lemmas
  have hYv : ∀ i, (Yu i : ZMod p) = ((i.val + 1 : ℕ) : ZMod p) := fun i => Units.val_mk0 _
  have hVv : ∀ j, (V j : ZMod p) = (((N p / 2).factorial : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p) := by
    intro j; show ((Fu * Ju j : (ZMod p)ˣ) : ZMod p) = _; rw [Units.val_mul]; rfl
  -- entry identity:  (Mtx.map cast) i j = hf ζ (γ j - δ i)
  have hentry : ∀ i j, (Mtx.map (Int.cast : ℤ → ℂ)) i j = hf ζ (γ j - δ i) := by
    intro i j
    have harg : (((((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ)
          - (((N p / 2).factorial : ℕ) : ℤ) * ((j.val + 1 : ℕ) : ℤ) : ℤ) : ZMod p))
        = (Yu i : ZMod p) ^ 2 - (V j : ZMod p) := by
      rw [hYv i, hVv j]; push_cast; ring
    rw [Matrix.map_apply, hM]
    show (((jacobiSym (((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ)
        - (((N p / 2).factorial : ℕ) : ℤ) * ((j.val + 1 : ℕ) : ℤ)) p : ℤ)) : ℂ)
        = hf ζ (γ j - δ i)
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    show (((qc p (((((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ)
        - (((N p / 2).factorial : ℕ) : ℤ) * ((j.val + 1 : ℕ) : ℤ)) : ℤ) : ZMod p)) : ℤ) : ℂ)
        = hf ζ (γ j - δ i)
    rw [harg, entry_id (Yu i) (V j)]
    rfl
  -- δ even
  have hδ : ∀ i, ((N p / 2 : ℕ) : ZMod (N p)) * δ i = 0 := by
    intro i
    have h2 : δ i = 2 * dl (Yu i) := by show dl ((Yu i) ^ 2) = _; rw [sq, dl_mul]; ring
    rw [h2, ← mul_assoc]
    have hz : ((N p / 2 : ℕ) : ZMod (N p)) * 2 = 0 := by
      rw [show ((N p / 2 : ℕ) : ZMod (N p)) * 2 = (((N p / 2) * 2 : ℕ) : ZMod (N p)) by push_cast; ring,
        show (N p / 2) * 2 = N p by rw [mul_comm]; exact two_mul_half hodd, ZMod.natCast_self]
    rw [hz, zero_mul]
  -- no ± collisions
  have hV : ∀ a b : Fin (N p / 2), V a = V b ∨ V a = - V b → a = b := by
    intro a b hab
    have key : ((a.val + 1 : ℕ) : ZMod p) = ((b.val + 1 : ℕ) : ZMod p) ∨
               ((a.val + 1 : ℕ) : ZMod p) = -((b.val + 1 : ℕ) : ZMod p) := by
      rcases hab with h | h
      · left
        have h' : Fu * Ju a = Fu * Ju b := h
        have hju : Ju a = Ju b := mul_left_cancel h'
        have := congrArg (Units.val) hju
        simpa only [Ju, Units.val_mk0] using this
      · right
        have h' : Fu * Ju a = Fu * (- Ju b) := by
          have hh : (Fu * Ju a : (ZMod p)ˣ) = -(Fu * Ju b) := h
          rw [hh, mul_neg]
        have hju : Ju a = - Ju b := mul_left_cancel h'
        have := congrArg (Units.val) hju
        simpa only [Ju, Units.val_mk0, Units.val_neg] using this
    have habp : a.val + 1 < p := by have := a.isLt; omega
    have hbbp : b.val + 1 < p := by have := b.isLt; omega
    rcases key with h | h
    · have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt habp, Nat.mod_eq_of_lt hbbp] at hmod
      exact Fin.ext (by omega)
    · exfalso
      have hsum : ((a.val + 1 : ℕ) : ZMod p) + ((b.val + 1 : ℕ) : ZMod p) = 0 := by rw [h]; ring
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff] at hsum
      have := Nat.le_of_dvd (by omega) hsum
      omega
  -- ∏ (-1)^(γ j).val = 1
  have hPg : ∏ j : Fin (N p / 2), (-1 : ℂ) ^ (γ j).val = 1 := by
    have hterm : ∀ j : Fin (N p / 2),
        (-1 : ℂ) ^ (γ j).val = (((qc p ((V j : (ZMod p)ˣ) : ZMod p)) : ℤ) : ℂ) := by
      intro j
      have hq := qc_pw hodd (γ j)
      rw [show pw p (γ j) = V j from pw_dl (V j)] at hq
      rw [hq]; push_cast; ring
    rw [Finset.prod_congr rfl (fun j _ => hterm j), ← Int.cast_prod]
    norm_cast
    have e1 : ∀ j : Fin (N p / 2), qc p ((V j : (ZMod p)ˣ) : ZMod p)
        = qc p (((N p / 2).factorial : ℕ) : ZMod p) * qc p ((j.val + 1 : ℕ) : ZMod p) := by
      intro j; rw [hVv j, map_mul]
    rw [Finset.prod_congr rfl (fun j _ => e1 j), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    have e2 : (∏ j : Fin (N p / 2), qc p ((j.val + 1 : ℕ) : ZMod p))
        = qc p (((N p / 2).factorial : ℕ) : ZMod p) := by
      rw [← map_prod]
      congr 1
      rw [← Nat.cast_prod]
      congr 1
      rw [Fin.prod_univ_eq_prod_range (fun i => i + 1) (N p / 2),
        Finset.prod_range_add_one_eq_factorial]
    rw [e2, ← pow_succ]
    obtain ⟨t, ht⟩ : Odd (N p / 2) := half_odd hp4
    have hsq : (qc p (((N p / 2).factorial : ℕ) : ZMod p)) ^ 2 = 1 := quadraticChar_sq_one hFne
    rw [show N p / 2 + 1 = 2 * (t + 1) by omega, pow_mul, hsq, one_pow]
  -- transversal
  obtain ⟨π, b, hπb⟩ := transversal hodd V hV
  -- factorization and determinant
  let Phi : Matrix (Fin (N p / 2)) (Fin (N p / 2)) ℂ :=
    Matrix.of (fun i k => ze ζ (-((k.val : ZMod (N p)) * δ i)))
  have heq : Mtx.map (Int.cast : ℤ → ℂ) = Phi * Kmat ζ γ := by
    funext i j
    rw [hentry i j, Matrix.mul_apply, MeqPhiK hodd ζ hζ γ δ hδ i j]
    rfl
  have hMbardet : (Mtx.map (Int.cast : ℤ → ℂ)).det = 0 := by
    rw [heq, Matrix.det_mul, detK_zero hp4 ζ hζ γ π b hπb hPg, mul_zero]
  have hcast : ((Mtx.det : ℤ) : ℂ) = (Mtx.map (Int.cast : ℤ → ℂ)).det := by
    have hmd := RingHom.map_det (Int.castRingHom ℂ) Mtx
    rw [RingHom.mapMatrix_apply] at hmd
    exact hmd
  have hz : ((Mtx.det : ℤ) : ℂ) = 0 := by rw [hcast, hMbardet]
  exact_mod_cast hz

end Hard

end Eval

open Matrix Nat Int

/--
A226163: Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! \cdot j}{p_n}\right)$$
where $p_n$ is the $n$-th prime.
The sequence is naturally indexed starting from $n=2$.
-/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else

  -- p is the n-th prime, p_n. Mathlib's nth Nat.Prime is 0-indexed, so we use (n-1).
  -- Since n >= 2, p >= 3 is an an odd prime.
  let p : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Matrix dimension m = (p-1)/2.
  let m : ℕ := (p - 1) / 2

  -- The constant C = ((p-1)/2)! as an integer.
  let C : ℤ := m.factorial.cast

  -- The matrix M has entries in ℤ.
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    -- 1-based indices i' and j' for the formula: 1 <= i', j' <= m.
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast

    -- Argument for the Legendre symbol: i'^2 - C * j'
    let arg : ℤ := i' * i' - C * j'

    -- jacobiSym is the Legendre symbol since p is prime.
    jacobiSym arg p

  M.det

/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  have hp : (Nat.nth Nat.Prime (n - 1)).Prime := Nat.prime_nth_prime (n - 1)
  haveI : Fact (Nat.nth Nat.Prime (n - 1)).Prime := ⟨hp⟩
  set p := Nat.nth Nat.Prime (n - 1) with hpe
  have hmono := Nat.nth_strictMono Nat.infinite_setOf_prime
  have h0 : Nat.nth Nat.Prime 0 = 2 := by
    have := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num); simpa using this
  have hp2 : 2 < p := by rw [hpe, ← h0]; exact hmono (by omega)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hcases : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hAeq : A226163 n = (Matrix.det (n := Fin ((p - 1) / 2))
      (fun i j => jacobiSym (((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ)
        - ((((p - 1) / 2).factorial : ℕ) : ℤ) * ((j.val + 1 : ℕ) : ℤ)) p)) := by
    rw [A226163, dif_neg (show ¬ n < 2 by omega)]
  rw [hAeq]
  set Mmat : Matrix (Fin ((p - 1) / 2)) (Fin ((p - 1) / 2)) ℤ :=
    (fun i j => jacobiSym (((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ)
      - ((((p - 1) / 2).factorial : ℕ) : ℤ) * ((j.val + 1 : ℕ) : ℤ)) p) with hMe
  constructor
  · intro hdet
    by_contra hne
    have hp1 : p % 4 = 1 := hcases.resolve_right hne
    exact (Eval.A226163Dev.easy_direction p hp hp1 ((p - 1) / 2) rfl Mmat hMe) hdet
  · intro hp4
    exact Eval.Hard.hard_direction hp4 ((p - 1) / 2) rfl Mmat hMe _
      (Complex.isPrimitiveRoot_exp (Eval.CharM.N p) (Eval.CharM.N_pos).ne')
