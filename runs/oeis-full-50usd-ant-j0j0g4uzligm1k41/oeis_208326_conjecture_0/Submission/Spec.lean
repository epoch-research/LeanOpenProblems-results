import FormalConjectures.Util.ProblemImports

open Real
open scoped goldenRatio

/--
A208326: $c(n) = n + \lfloor nr/t \rfloor + \lfloor ns/t \rfloor$, where $\lfloor \cdot \rfloor$ is the floor function, $r=5$, $s=(1+\sqrt{5})/2$, and $t=1/s$.
-/
noncomputable def A208326 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * r / t)
  let term2_int : ℤ := Int.floor (n_r * s / t)

  -- Sum the components in ℤ and convert the final result back to ℕ.
  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

/--
A207672: $a(n) = n + \lfloor ns/r \rfloor + \lfloor nt/r \rfloor$.
-/
noncomputable def A207672 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * s / r)
  let term2_int : ℤ := Int.floor (n_r * t / r)

  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

/--
A207673: $b(n) = n + \lfloor nr/s \rfloor + \lfloor nt/s \rfloor$.
-/
noncomputable def A207673 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * r / s)
  let term2_int : ℤ := Int.floor (n_r * t / s)

  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat


namespace ThreeBeatty

variable (d : Fin 3 → ℝ)

/-- The "special value" of family `i` at index `n`. -/
noncomputable def value (i : Fin 3) (n : ℕ) : ℝ := (n : ℝ) / d i

/-- Number of special values `≤ x` (for `x ≥ 0`). -/
noncomputable def count (x : ℝ) : ℤ := ∑ k : Fin 3, ⌊d k * x⌋

/-- Rank of the special value `value i n`. -/
noncomputable def rank (i : Fin 3) (n : ℕ) : ℤ := count d (value d i n)

/-- The next candidate of family `k` after `x`. -/
noncomputable def cand (x : ℝ) (k : Fin 3) : ℝ := ((⌊d k * x⌋ : ℤ) + 1 : ℝ) / d k

/-- The next special value strictly after `x`. -/
noncomputable def nextv (x : ℝ) : ℝ := min (cand d x 0) (min (cand d x 1) (cand d x 2))

variable (hd : ∀ k, 0 < d k)

include hd

lemma cand_gt (x : ℝ) (k : Fin 3) : x < cand d x k := by
  have h1 : d k * x < (⌊d k * x⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [cand, lt_div_iff₀ (hd k), mul_comm]
  exact h1

lemma dk_cand (x : ℝ) (k : Fin 3) : d k * cand d x k = (⌊d k * x⌋ : ℝ) + 1 := by
  rw [cand, mul_comm, div_mul_cancel₀ _ (ne_of_gt (hd k))]

lemma nextv_le (x : ℝ) (k : Fin 3) : nextv d x ≤ cand d x k := by
  fin_cases k <;> simp only [nextv]
  · exact min_le_left _ _
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

lemma nextv_gt (x : ℝ) : x < nextv d x := by
  rw [nextv]
  exact lt_min (cand_gt d hd x 0) (lt_min (cand_gt d hd x 1) (cand_gt d hd x 2))

lemma nextv_eq_some (x : ℝ) : ∃ k, nextv d x = cand d x k := by
  rw [nextv]
  rcases le_total (cand d x 0) (min (cand d x 1) (cand d x 2)) with h | h
  · exact ⟨0, min_eq_left h⟩
  · rw [min_eq_right h]
    rcases le_total (cand d x 1) (cand d x 2) with h2 | h2
    · exact ⟨1, min_eq_left h2⟩
    · exact ⟨2, min_eq_right h2⟩

lemma floor_eq_at (x : ℝ) {k : Fin 3} (hj : nextv d x = cand d x k) :
    ⌊d k * nextv d x⌋ = ⌊d k * x⌋ + 1 := by
  have h : d k * nextv d x = ((⌊d k * x⌋ + 1 : ℤ) : ℝ) := by
    rw [hj, dk_cand d hd]; push_cast; ring
  rw [h, Int.floor_intCast]

lemma floor_lt_at (x : ℝ) {k : Fin 3} (hlt : nextv d x < cand d x k) :
    ⌊d k * nextv d x⌋ = ⌊d k * x⌋ := by
  rw [Int.floor_eq_iff]
  constructor
  · have h1 : (⌊d k * x⌋ : ℝ) ≤ d k * x := Int.floor_le _
    have h2 : d k * x ≤ d k * nextv d x :=
      mul_le_mul_of_nonneg_left (le_of_lt (nextv_gt d hd x)) (le_of_lt (hd k))
    linarith
  · have h3 : d k * nextv d x < d k * cand d x k :=
      mul_lt_mul_of_pos_left hlt (hd k)
    have h4 : d k * cand d x k = (⌊d k * x⌋ : ℝ) + 1 := dk_cand d hd x k
    push_cast; linarith

lemma count_zero : count d 0 = 0 := by
  simp [count]

lemma count_lt (x : ℝ) (j : Fin 3) (m : ℕ) (hm : 1 ≤ m)
    (hxy : x < value d j m) : count d x < count d (value d j m) := by
  have hdy : d j * value d j m = (m : ℝ) := by
    rw [value, mul_comm, div_mul_cancel₀ _ (ne_of_gt (hd j))]
  rw [count, count]
  apply Finset.sum_lt_sum
  · intro k _
    exact Int.floor_mono (mul_le_mul_of_nonneg_left (le_of_lt hxy) (le_of_lt (hd k)))
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    have hlt : d j * x < d j * value d j m := mul_lt_mul_of_pos_left hxy (hd j)
    have h1 : ⌊d j * value d j m⌋ = (m : ℤ) := by rw [hdy]; exact Int.floor_natCast m
    have h2 : ⌊d j * x⌋ < (m : ℤ) := by
      rw [Int.floor_lt]; rw [hdy] at hlt; exact hlt
    rw [h1]; exact h2

lemma rank_pos {i : Fin 3} {n : ℕ} (hn : 1 ≤ n) : 1 ≤ rank d i n := by
  have hval_pos : 0 < value d i n := by
    rw [value]
    apply div_pos
    · exact_mod_cast hn
    · exact hd i
  have allnn : ∀ k ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ ⌊d k * value d i n⌋ := by
    intro k _
    apply Int.floor_nonneg.mpr
    exact le_of_lt (mul_pos (hd k) hval_pos)
  have hi : ⌊d i * value d i n⌋ = (n : ℤ) := by
    have : d i * value d i n = (n : ℝ) := by
      rw [value, mul_comm, div_mul_cancel₀ _ (ne_of_gt (hd i))]
    rw [this]; exact Int.floor_natCast n
  have hle := Finset.single_le_sum allnn (Finset.mem_univ i)
  rw [rank, count]
  rw [hi] at hle
  have : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  omega

variable (hdist : ∀ (i j : Fin 3) (n m : ℕ), 1 ≤ n → 1 ≤ m →
    value d i n = value d j m → i = j ∧ n = m)

include hdist

/-- The candidate of family `k` after `x ≥ 0` is a genuine special value. -/
lemma cand_special (x : ℝ) (hx : 0 ≤ x) (k : Fin 3) :
    ∃ n : ℕ, 1 ≤ n ∧ cand d x k = value d k n := by
  have hfl : 0 ≤ ⌊d k * x⌋ := by
    apply Int.le_floor.mpr
    simpa using mul_nonneg (le_of_lt (hd k)) hx
  refine ⟨(⌊d k * x⌋ + 1).toNat, by omega, ?_⟩
  have hcast : ((⌊d k * x⌋ + 1).toNat : ℝ) = (⌊d k * x⌋ : ℝ) + 1 := by
    have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ ⌊d k * x⌋ + 1 by omega)
    exact_mod_cast this
  rw [value, cand, hcast]

lemma cand_distinct (x : ℝ) (hx : 0 ≤ x) {k k' : Fin 3} (hk : k ≠ k') :
    cand d x k ≠ cand d x k' := by
  intro hc
  obtain ⟨n, hn, hvn⟩ := cand_special d hd hdist x hx k
  obtain ⟨m, hm, hvm⟩ := cand_special d hd hdist x hx k'
  have : value d k n = value d k' m := by rw [← hvn, ← hvm, hc]
  exact hk (hdist k k' n m hn hm this).1

lemma count_next (x : ℝ) (hx : 0 ≤ x) : count d (nextv d x) = count d x + 1 := by
  obtain ⟨j, hj⟩ := nextv_eq_some d hd x
  have hother : ∀ k, k ≠ j → ⌊d k * nextv d x⌋ = ⌊d k * x⌋ := by
    intro k hk
    apply floor_lt_at d hd x
    refine lt_of_le_of_ne (nextv_le d hd x k) ?_
    rw [hj]
    exact cand_distinct d hd hdist x hx (Ne.symm hk)
  have key : ∀ k, ⌊d k * nextv d x⌋ = ⌊d k * x⌋ + (if k = j then 1 else 0) := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [floor_eq_at d hd x hj, if_pos rfl]
    · rw [hother k hk, if_neg hk, add_zero]
  simp only [count]
  rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ j (fun _ => (1 : ℤ))]
  simp

lemma nextv_special (x : ℝ) (hx : 0 ≤ x) :
    ∃ (k : Fin 3) (n : ℕ), 1 ≤ n ∧ nextv d x = value d k n := by
  obtain ⟨k, hk⟩ := nextv_eq_some d hd x
  obtain ⟨n, hn, hv⟩ := cand_special d hd hdist x hx k
  exact ⟨k, n, hn, hk.trans hv⟩

lemma cover_aux : ∀ p : ℕ, ∃ x : ℝ, 0 ≤ x ∧ count d x = (p : ℤ) ∧
    (1 ≤ p → ∃ (i : Fin 3) (n : ℕ), 1 ≤ n ∧ x = value d i n) := by
  intro p
  induction p with
  | zero => exact ⟨0, le_refl _, count_zero d hd, by intro h; omega⟩
  | succ p ih =>
    obtain ⟨x, hx0, hxc, _⟩ := ih
    refine ⟨nextv d x, le_of_lt (lt_of_le_of_lt hx0 (nextv_gt d hd x)), ?_, ?_⟩
    · rw [count_next d hd hdist x hx0, hxc]; push_cast; ring
    · intro _; exact nextv_special d hd hdist x hx0

lemma covering (p : ℕ) (hp : 1 ≤ p) :
    ∃ (i : Fin 3) (n : ℕ), 1 ≤ n ∧ rank d i n = (p : ℤ) := by
  obtain ⟨x, _, hxc, hsp⟩ := cover_aux d hd hdist p
  obtain ⟨i, n, hn, hv⟩ := hsp hp
  exact ⟨i, n, hn, by rw [rank, ← hv, hxc]⟩

lemma disj {i j : Fin 3} {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hr : rank d i n = rank d j m) : i = j ∧ n = m := by
  rcases lt_trichotomy (value d i n) (value d j m) with h | h | h
  · exact absurd hr (by
      have := count_lt d hd (value d i n) j m hm h
      rw [rank, rank]; omega)
  · exact hdist i j n m hn hm h
  · exact absurd hr (by
      have := count_lt d hd (value d j m) i n hn h
      rw [rank, rank]; omega)

end ThreeBeatty

open ThreeBeatty

noncomputable def dGold : Fin 3 → ℝ := ![5, φ, 1/φ]

lemma hdGold : ∀ k, 0 < dGold k := by
  intro k
  fin_cases k <;> simp only [dGold, Matrix.cons_val]
  · norm_num
  · exact goldenRatio_pos
  · exact div_pos one_pos goldenRatio_pos

/-- Key irrationality fact in linear form. -/
lemma phi_lin (k c : ℤ) (h : (k : ℝ) * φ = (c : ℝ)) : k = 0 ∧ c = 0 := by
  by_cases hk : k = 0
  · subst hk
    simp only [Int.cast_zero, zero_mul] at h
    exact ⟨rfl, by exact_mod_cast h.symm⟩
  · exact absurd h ((goldenRatio_irrational.intCast_mul hk).ne_int c)

lemma hinv : (1 : ℝ) / φ = φ - 1 := by
  rw [div_eq_iff goldenRatio_ne_zero]
  linear_combination -goldenRatio_sq

lemma hdistGold : ∀ (i j : Fin 3) (n m : ℕ), 1 ≤ n → 1 ≤ m →
    value dGold i n = value dGold j m → i = j ∧ n = m := by
  intro i j n m hn hm hv
  have heq : (n : ℝ) * dGold j = (m : ℝ) * dGold i :=
    (div_eq_div_iff (ne_of_gt (hdGold i)) (ne_of_gt (hdGold j))).mp hv
  have hne1 : φ - 1 ≠ 0 := by
    have : φ ≠ 1 := by
      intro h; have h2 := goldenRatio_sq; rw [h] at h2; norm_num at h2
    intro hc; exact this (by linarith [hc])
  fin_cases i <;> fin_cases j
  -- (0,0)
  · refine ⟨rfl, ?_⟩
    have heq2 : (n : ℝ) * 5 = (m : ℝ) * 5 := heq
    have : (n : ℝ) = m := mul_right_cancel₀ (by norm_num : (5 : ℝ) ≠ 0) heq2
    exact_mod_cast this
  -- (0,1)
  · exfalso
    have heq2 : (n : ℝ) * φ = (m : ℝ) * 5 := heq
    have hh : (n : ℝ) * φ = ((5 * m : ℤ) : ℝ) := by push_cast; linear_combination heq2
    have := phi_lin n (5 * m) hh
    omega
  -- (0,2)
  · exfalso
    have heq2 : (n : ℝ) * (1 / φ) = (m : ℝ) * 5 := heq
    rw [hinv] at heq2
    have hh : (n : ℝ) * φ = ((5 * m + n : ℤ) : ℝ) := by push_cast; linear_combination heq2
    have := phi_lin n (5 * m + n) hh
    omega
  -- (1,0)
  · exfalso
    have heq2 : (n : ℝ) * 5 = (m : ℝ) * φ := heq
    have hh : (m : ℝ) * φ = ((5 * n : ℤ) : ℝ) := by push_cast; linear_combination -heq2
    have := phi_lin m (5 * n) hh
    omega
  -- (1,1)
  · refine ⟨rfl, ?_⟩
    have heq2 : (n : ℝ) * φ = (m : ℝ) * φ := heq
    have : (n : ℝ) = m := mul_right_cancel₀ goldenRatio_ne_zero heq2
    exact_mod_cast this
  -- (1,2)
  · exfalso
    have heq2 : (n : ℝ) * (1 / φ) = (m : ℝ) * φ := heq
    rw [hinv] at heq2
    have hh : ((n - m : ℤ) : ℝ) * φ = ((n : ℤ) : ℝ) := by push_cast; linear_combination heq2
    have := phi_lin (n - m) n hh
    omega
  -- (2,0)
  · exfalso
    have heq2 : (n : ℝ) * 5 = (m : ℝ) * (1 / φ) := heq
    rw [hinv] at heq2
    have hh : (m : ℝ) * φ = ((5 * n + m : ℤ) : ℝ) := by push_cast; linear_combination -heq2
    have := phi_lin m (5 * n + m) hh
    omega
  -- (2,1)
  · exfalso
    have heq2 : (n : ℝ) * φ = (m : ℝ) * (1 / φ) := heq
    rw [hinv] at heq2
    have hh : ((n - m : ℤ) : ℝ) * φ = ((-m : ℤ) : ℝ) := by push_cast; linear_combination heq2
    have := phi_lin (n - m) (-m) hh
    omega
  -- (2,2)
  · refine ⟨rfl, ?_⟩
    have heq2 : (n : ℝ) * (1 / φ) = (m : ℝ) * (1 / φ) := heq
    rw [hinv] at heq2
    have : (n : ℝ) = m := mul_right_cancel₀ hne1 heq2
    exact_mod_cast this

lemma dval_self (i : Fin 3) (n : ℕ) : dGold i * value dGold i n = (n : ℝ) := by
  rw [value, mul_comm, div_mul_cancel₀ _ (ne_of_gt (hdGold i))]

lemma rank_dGold_0 (n : ℕ) :
    rank dGold 0 n = (n : ℤ) + ⌊(n : ℝ) * φ / 5⌋ + ⌊(n : ℝ) * (1 / φ) / 5⌋ := by
  rw [rank, count, Fin.sum_univ_three]
  have e0 : dGold 0 * value dGold 0 n = (n : ℝ) := dval_self 0 n
  have e1 : dGold 1 * value dGold 0 n = (n : ℝ) * φ / 5 := by
    show φ * ((n : ℝ) / 5) = (n : ℝ) * φ / 5; ring
  have e2 : dGold 2 * value dGold 0 n = (n : ℝ) * (1 / φ) / 5 := by
    show (1 / φ) * ((n : ℝ) / 5) = (n : ℝ) * (1 / φ) / 5; ring
  rw [e0, e1, e2, Int.floor_natCast]

lemma rank_dGold_1 (n : ℕ) :
    rank dGold 1 n = (n : ℤ) + ⌊(n : ℝ) * 5 / φ⌋ + ⌊(n : ℝ) * (1 / φ) / φ⌋ := by
  rw [rank, count, Fin.sum_univ_three]
  have e0 : dGold 0 * value dGold 1 n = (n : ℝ) * 5 / φ := by
    show (5 : ℝ) * ((n : ℝ) / φ) = (n : ℝ) * 5 / φ; ring
  have e1 : dGold 1 * value dGold 1 n = (n : ℝ) := dval_self 1 n
  have e2 : dGold 2 * value dGold 1 n = (n : ℝ) * (1 / φ) / φ := by
    show (1 / φ) * ((n : ℝ) / φ) = (n : ℝ) * (1 / φ) / φ; ring
  rw [e0, e1, e2, Int.floor_natCast]; ring

lemma rank_dGold_2 (n : ℕ) :
    rank dGold 2 n = (n : ℤ) + ⌊(n : ℝ) * 5 / (1 / φ)⌋ + ⌊(n : ℝ) * φ / (1 / φ)⌋ := by
  rw [rank, count, Fin.sum_univ_three]
  have e0 : dGold 0 * value dGold 2 n = (n : ℝ) * 5 / (1 / φ) := by
    show (5 : ℝ) * ((n : ℝ) / (1 / φ)) = (n : ℝ) * 5 / (1 / φ); ring
  have e1 : dGold 1 * value dGold 2 n = (n : ℝ) * φ / (1 / φ) := by
    show φ * ((n : ℝ) / (1 / φ)) = (n : ℝ) * φ / (1 / φ); ring
  have e2 : dGold 2 * value dGold 2 n = (n : ℝ) := dval_self 2 n
  rw [e0, e1, e2, Int.floor_natCast]; ring

lemma A672_cast (n : ℕ) (hn : 1 ≤ n) : (A207672 n : ℤ) = rank dGold 0 n := by
  rw [rank_dGold_0]
  have hpos : 0 ≤ (n : ℤ) + ⌊(n : ℝ) * φ / 5⌋ + ⌊(n : ℝ) * (1 / φ) / 5⌋ := by
    rw [← rank_dGold_0]
    exact le_trans (by norm_num) (rank_pos dGold hdGold hn)
  exact Int.toNat_of_nonneg hpos

lemma A673_cast (n : ℕ) (hn : 1 ≤ n) : (A207673 n : ℤ) = rank dGold 1 n := by
  rw [rank_dGold_1]
  have hpos : 0 ≤ (n : ℤ) + ⌊(n : ℝ) * 5 / φ⌋ + ⌊(n : ℝ) * (1 / φ) / φ⌋ := by
    rw [← rank_dGold_1]
    exact le_trans (by norm_num) (rank_pos dGold hdGold hn)
  exact Int.toNat_of_nonneg hpos

lemma A326_cast (n : ℕ) (hn : 1 ≤ n) : (A208326 n : ℤ) = rank dGold 2 n := by
  rw [rank_dGold_2]
  have hpos : 0 ≤ (n : ℤ) + ⌊(n : ℝ) * 5 / (1 / φ)⌋ + ⌊(n : ℝ) * φ / (1 / φ)⌋ := by
    rw [← rank_dGold_2]
    exact le_trans (by norm_num) (rank_pos dGold hdGold hn)
  exact Int.toNat_of_nonneg hpos

lemma mem_range_iff (A : ℕ → ℕ) (i : Fin 3)
    (hA : ∀ n, 1 ≤ n → (A n : ℤ) = rank dGold i n) (p : ℕ) :
    p ∈ Set.range (A ∘ Nat.succ) ↔ ∃ n, 1 ≤ n ∧ (p : ℤ) = rank dGold i n := by
  constructor
  · rintro ⟨k, hk⟩
    simp only [Function.comp_apply] at hk
    refine ⟨k + 1, by omega, ?_⟩
    rw [← hA (k + 1) (by omega)]
    exact_mod_cast hk.symm
  · rintro ⟨n, hn, hp⟩
    have hAn : A n = p := by
      have : (A n : ℤ) = (p : ℤ) := by rw [hA n hn]; exact hp.symm
      exact_mod_cast this
    refine ⟨n - 1, ?_⟩
    simp only [Function.comp_apply]
    have hsucc : (n - 1).succ = n := by omega
    rw [hsucc]
    exact hAn

/--
oeis_208326_conjecture_0: %C A208326 The sequences A207672, A207673, and A208326 partition the positive integers.
-/
theorem oeis_208326_conjecture_0 :
  ({n : ℕ | 0 < n} : Set ℕ) =
    (Set.range (A207672 ∘ Nat.succ)) ∪
    (Set.range (A207673 ∘ Nat.succ)) ∪
    (Set.range (A208326 ∘ Nat.succ)) ∧
  (Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A207673 ∘ Nat.succ) = ∅) ∧
  (Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅) ∧
  (Set.range (A207673 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅)
  := by
  have h0 := mem_range_iff A207672 0 A672_cast
  have h1 := mem_range_iff A207673 1 A673_cast
  have h2 := mem_range_iff A208326 2 A326_cast
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, h0, h1, h2]
    constructor
    · intro hp
      obtain ⟨i, n, hn, hrank⟩ := covering dGold hdGold hdistGold p hp
      fin_cases i
      · exact Or.inl (Or.inl ⟨n, hn, hrank.symm⟩)
      · exact Or.inl (Or.inr ⟨n, hn, hrank.symm⟩)
      · exact Or.inr ⟨n, hn, hrank.symm⟩
    · rintro ((⟨n, hn, hp⟩ | ⟨n, hn, hp⟩) | ⟨n, hn, hp⟩)
      · have hpos : (1 : ℤ) ≤ (p : ℤ) := by rw [hp]; exact rank_pos dGold hdGold hn
        omega
      · have hpos : (1 : ℤ) ≤ (p : ℤ) := by rw [hp]; exact rank_pos dGold hdGold hn
        omega
      · have hpos : (1 : ℤ) ≤ (p : ℤ) := by rw [hp]; exact rank_pos dGold hdGold hn
        omega
  · rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Set.mem_inter_iff, h0, h1] at hp
    obtain ⟨⟨n, hn, hpn⟩, ⟨m, hm, hpm⟩⟩ := hp
    have heq : rank dGold 0 n = rank dGold 1 m := by rw [← hpn, ← hpm]
    exact absurd (disj dGold hdGold hdistGold hn hm heq).1 (by decide)
  · rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Set.mem_inter_iff, h0, h2] at hp
    obtain ⟨⟨n, hn, hpn⟩, ⟨m, hm, hpm⟩⟩ := hp
    have heq : rank dGold 0 n = rank dGold 2 m := by rw [← hpn, ← hpm]
    exact absurd (disj dGold hdGold hdistGold hn hm heq).1 (by decide)
  · rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Set.mem_inter_iff, h1, h2] at hp
    obtain ⟨⟨n, hn, hpn⟩, ⟨m, hm, hpm⟩⟩ := hp
    have heq : rank dGold 1 n = rank dGold 2 m := by rw [← hpn, ← hpm]
    exact absurd (disj dGold hdGold hdistGold hn hm heq).1 (by decide)
