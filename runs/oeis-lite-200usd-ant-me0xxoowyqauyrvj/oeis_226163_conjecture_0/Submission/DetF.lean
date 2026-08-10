import FormalConjectures.Util.ProblemImports

open Matrix Finset

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
