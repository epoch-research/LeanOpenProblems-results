import Mathlib

open Filter Set Real
open scoped Topology Matrix

noncomputable section

abbrev Idx := Fin 7

/-- The concrete 7 by 7 nonnegative matrix used in the A381358 transfer-matrix scratch work. -/
def A7 : Matrix Idx Idx ℝ := !![
  1, 1, 0, 0, 0, 0, 0;
  0, 1, 1, 0, 0, 0, 0;
  0, 0, 1, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 1;
  1, 0, 0, 0, 0, 0, 0]

def A7pow10 : Matrix Idx Idx ℝ := !![
  21, 25, 51, 37, 28, 21, 15;
  15, 21, 25, 14, 9, 7, 6;
  6, 15, 21, 11, 5, 2, 1;
  1, 6, 15, 10, 6, 3, 1;
  2, 7, 21, 15, 10, 6, 3;
  5, 9, 28, 21, 15, 10, 6;
  11, 14, 37, 28, 21, 15, 10]

set_option maxHeartbeats 2000000 in
theorem A7_pow10 : A7 ^ 10 = A7pow10 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A7, A7pow10, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem A7_primitive : Matrix.IsPrimitive A7 := by
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [A7]
  · refine ⟨10, by norm_num, ?_⟩
    intro i j
    rw [A7_pow10]
    fin_cases i <;> fin_cases j <;> norm_num [A7pow10]

/-- First coordinate of the `A7` orbit of `v`. -/
def firstCoord (v : Idx → ℝ) (n : ℕ) : ℝ := (A7 ^ n *ᵥ v) 0

/-- Total mass of the `A7` orbit of `v`; this is the comparison sequence used
for the almost-multiplicativity argument. -/
def totalMass (v : Idx → ℝ) (n : ℕ) : ℝ := ∑ i : Idx, (A7 ^ n *ᵥ v) i


/-- A Fekete-lemma wrapper: a positive, almost-submultiplicative real sequence whose
logarithms divided by `n` are bounded below has a root limit.  The harmless constant
`C` is absorbed by applying Fekete to `log (t n) + log C`. -/
theorem exists_root_limit_of_almost_submultiplicative
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n) {C : ℝ} (hC : 0 < C)
    (hsub : ∀ m n, t (m + n) ≤ C * t m * t n)
    (hbdd : BddBelow (range fun n : ℕ => (Real.log (t n) + Real.log C) / (n : ℝ))) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (t n) ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  let u : ℕ → ℝ := fun n => Real.log (t n) + Real.log C
  have hu : Subadditive u := by
    intro m n
    have hpos_m : 0 < t m := htpos m
    have hpos_n : 0 < t n := htpos n
    have hpos_mul : 0 < C * t m * t n := mul_pos (mul_pos hC hpos_m) hpos_n
    have hlog_le : Real.log (t (m + n)) ≤ Real.log (C * t m * t n) :=
      Real.log_le_log (htpos (m + n)) (hsub m n)
    calc
      u (m + n) = Real.log (t (m + n)) + Real.log C := rfl
      _ ≤ Real.log (C * t m * t n) + Real.log C := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hlog_le (Real.log C)
      _ = (Real.log (t m) + Real.log C) + (Real.log (t n) + Real.log C) := by
        rw [Real.log_mul (mul_ne_zero hC.ne' hpos_m.ne') hpos_n.ne',
            Real.log_mul hC.ne' hpos_m.ne']
        ring_nf
      _ = u m + u n := rfl
  rcases hu.tendsto_lim hbdd with hlim_u
  let a : ℝ := hu.lim
  refine ⟨Real.exp a, ?_⟩
  have hloglim : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (t n)) atTop (𝓝 a) := by
    have hCterm : Tendsto (fun n : ℕ => (Real.log C) / (n : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, mul_comm] using
        ((tendsto_const_nhds (x := Real.log C)).mul tendsto_one_div_atTop_nhds_zero_nat)
    have hdiff := hlim_u.sub hCterm
    have hdiff' : Tendsto (fun n : ℕ => u n / (n : ℝ) - Real.log C / (n : ℝ)) atTop (𝓝 a) := by
      simpa [a] using hdiff
    refine Tendsto.congr' ?_ hdiff'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    dsimp [u]
    field_simp [hn0]
    ring_nf
  have hexp : Tendsto (fun n : ℕ => Real.exp ((1 / (n : ℝ)) * Real.log (t n))) atTop (𝓝 (Real.exp a)) :=
    Real.continuous_exp.tendsto a |>.comp hloglim
  refine Tendsto.congr' ?_ hexp
  filter_upwards with n
  have hpos : 0 < t n := htpos n
  rw [Real.rpow_def_of_pos hpos]
  ring_nf


/-- Constant factors disappear after taking `n`-th roots. -/
theorem const_rpow_one_div_tendsto_one {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa using (tendsto_const_nhds.rpow h0 (Or.inl hc.ne'))

/-- If two nonnegative sequences differ only by eventual positive constant factors,
they have the same root limit. -/
theorem rpow_one_div_sandwich
    {a b : ℕ → ℝ} {L c d : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hb_nonneg : ∀ n, 0 ≤ b n)
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (hlim : Tendsto (fun n : ℕ => b n ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L))
    (hlo : ∀ᶠ n in atTop, c * b n ≤ a n)
    (hhi : ∀ᶠ n in atTop, a n ≤ d * b n) :
    Tendsto (fun n : ℕ => a n ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  have hcle : ∀ᶠ n : ℕ in atTop,
      c ^ ((1 : ℝ) / (n : ℝ)) * b n ^ ((1 : ℝ) / (n : ℝ)) ≤
        a n ^ ((1 : ℝ) / (n : ℝ)) := by
    filter_upwards [hlo, (eventually_ge_atTop (1 : ℕ))] with n hn hnpos
    rw [← Real.mul_rpow hc.le (hb_nonneg n)]
    exact Real.rpow_le_rpow (mul_nonneg hc.le (hb_nonneg n)) hn (by positivity)
  have hhle : ∀ᶠ n : ℕ in atTop,
      a n ^ ((1 : ℝ) / (n : ℝ)) ≤
        d ^ ((1 : ℝ) / (n : ℝ)) * b n ^ ((1 : ℝ) / (n : ℝ)) := by
    filter_upwards [hhi, (eventually_ge_atTop (1 : ℕ))] with n hn hnpos
    rw [← Real.mul_rpow hd.le (hb_nonneg n)]
    exact Real.rpow_le_rpow (ha_nonneg n) hn (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ hcle hhle
  · have hcroot := const_rpow_one_div_tendsto_one hc
    simpa [one_mul] using hcroot.mul hlim
  · have hdroot := const_rpow_one_div_tendsto_one hd
    simpa [one_mul] using hdroot.mul hlim

/-- Combined form tailored to matrix-coordinate applications: if a positive
almost-submultiplicative comparison sequence `b` has the logarithmic lower bound
needed by Fekete, and `a` is eventually within fixed positive multiples of `b`,
then `a n ^ (1/n)` converges. -/
theorem exists_root_limit_of_sandwiched_almost_submultiplicative
    (a b : ℕ → ℝ) (hbpos : ∀ n, 0 < b n) (hanonneg : ∀ n, 0 ≤ a n)
    {C c d : ℝ} (hC : 0 < C) (hc : 0 < c) (hd : 0 < d)
    (hsub : ∀ m n, b (m + n) ≤ C * b m * b n)
    (hbdd : BddBelow (range fun n : ℕ => (Real.log (b n) + Real.log C) / (n : ℝ)))
    (hlo : ∀ᶠ n in atTop, c * b n ≤ a n)
    (hhi : ∀ᶠ n in atTop, a n ≤ d * b n) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => a n ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  rcases exists_root_limit_of_almost_submultiplicative b hbpos hC hsub hbdd with ⟨L, hL⟩
  exact ⟨L, rpow_one_div_sandwich hc hd (fun n => (hbpos n).le) hanonneg hL hlo hhi⟩


/-- A concrete `A7`-coordinate corollary.  The remaining matrix-specific work is to
prove the displayed hypotheses for `totalMass v` and `firstCoord v`; once those
bounds are available, the root limit for the first coordinate follows without any
Perron--Frobenius eigenvalue calculation. -/
theorem exists_firstCoord_A7_root_limit_from_totalMass_bounds
    (v : Idx → ℝ) (htpos : ∀ n, 0 < totalMass v n)
    (hfirst_nonneg : ∀ n, 0 ≤ firstCoord v n)
    {C c d : ℝ} (hC : 0 < C) (hc : 0 < c) (hd : 0 < d)
    (hsub : ∀ m n, totalMass v (m + n) ≤ C * totalMass v m * totalMass v n)
    (hbdd : BddBelow (range fun n : ℕ =>
      (Real.log (totalMass v n) + Real.log C) / (n : ℝ)))
    (hlo : ∀ᶠ n in atTop, c * totalMass v n ≤ firstCoord v n)
    (hhi : ∀ᶠ n in atTop, firstCoord v n ≤ d * totalMass v n) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (firstCoord v n) ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  exact exists_root_limit_of_sandwiched_almost_submultiplicative
    (firstCoord v) (totalMass v) htpos hfirst_nonneg hC hc hd hsub hbdd hlo hhi



theorem A7_entry_nonneg (i j : Idx) : 0 ≤ A7 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [A7]

theorem A7_pow_entry_nonneg (n : ℕ) (i j : Idx) : 0 ≤ (A7 ^ n) i j := by
  induction n generalizing i j with
  | zero =>
      by_cases h : i = j <;> simp [h]
  | succ n ih =>
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (A7_entry_nonneg k j)

theorem A7_iterate_nonneg {v : Idx → ℝ} (hv : ∀ i, 0 ≤ v i) (n : ℕ) (i : Idx) :
    0 ≤ (A7 ^ n *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (A7_pow_entry_nonneg n i j) (hv j)

theorem firstCoord_nonneg_of_nonneg {v : Idx → ℝ} (hv : ∀ i, 0 ≤ v i) :
    ∀ n, 0 ≤ firstCoord v n := by
  intro n
  exact A7_iterate_nonneg hv n 0

theorem A7_pow_zero_zero_ge_one (n : ℕ) : (1 : ℝ) ≤ (A7 ^ n) (0 : Idx) (0 : Idx) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      have hterm_nonneg : ∀ x ∈ Finset.univ, 0 ≤ (A7 ^ n) (0 : Idx) x * A7 x (0 : Idx) := by
        intro x hx
        exact mul_nonneg (A7_pow_entry_nonneg n 0 x) (A7_entry_nonneg x 0)
      have hle : (A7 ^ n) (0 : Idx) (0 : Idx) * A7 (0 : Idx) (0 : Idx) ≤
          ∑ x : Idx, (A7 ^ n) (0 : Idx) x * A7 x (0 : Idx) := by
        exact Finset.single_le_sum hterm_nonneg (Finset.mem_univ _)
      have hA : A7 (0 : Idx) (0 : Idx) = 1 := by norm_num [A7]
      nlinarith

theorem firstCoord_pos_of_pos {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ n, 0 < firstCoord v n := by
  intro n
  simp only [firstCoord, Matrix.mulVec, dotProduct]
  have hterm_nonneg : ∀ x ∈ Finset.univ, 0 ≤ (A7 ^ n) (0 : Idx) x * v x := by
    intro x hx
    exact mul_nonneg (A7_pow_entry_nonneg n 0 x) (hv x).le
  have hle : (A7 ^ n) (0 : Idx) (0 : Idx) * v (0 : Idx) ≤
      ∑ x : Idx, (A7 ^ n) (0 : Idx) x * v x := by
    exact Finset.single_le_sum hterm_nonneg (Finset.mem_univ _)
  have hpos : 0 < (A7 ^ n) (0 : Idx) (0 : Idx) * v (0 : Idx) :=
    mul_pos (lt_of_lt_of_le zero_lt_one (A7_pow_zero_zero_ge_one n)) (hv 0)
  exact lt_of_lt_of_le hpos hle

theorem totalMass_pos_of_pos {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ n, 0 < totalMass v n := by
  intro n
  have hnon : ∀ i : Idx, 0 ≤ (A7 ^ n *ᵥ v) i := A7_iterate_nonneg (fun i => (hv i).le) n
  have hle : (A7 ^ n *ᵥ v) (0 : Idx) ≤ ∑ i : Idx, (A7 ^ n *ᵥ v) i := by
    exact Finset.single_le_sum (fun x hx => hnon x) (Finset.mem_univ _)
  exact lt_of_lt_of_le (firstCoord_pos_of_pos hv n) (by simpa [totalMass, firstCoord] using hle)

theorem firstCoord_ge_v0_of_pos {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ n, v (0 : Idx) ≤ firstCoord v n := by
  intro n
  simp only [firstCoord, Matrix.mulVec, dotProduct]
  have hterm_nonneg : ∀ x ∈ Finset.univ, 0 ≤ (A7 ^ n) (0 : Idx) x * v x := by
    intro x hx
    exact mul_nonneg (A7_pow_entry_nonneg n 0 x) (hv x).le
  have hle : (A7 ^ n) (0 : Idx) (0 : Idx) * v (0 : Idx) ≤
      ∑ x : Idx, (A7 ^ n) (0 : Idx) x * v x := by
    exact Finset.single_le_sum hterm_nonneg (Finset.mem_univ _)
  have hv0non : 0 ≤ v (0 : Idx) := (hv 0).le
  have hmul : v (0 : Idx) ≤ (A7 ^ n) (0 : Idx) (0 : Idx) * v (0 : Idx) := by
    calc
      v (0 : Idx) = 1 * v (0 : Idx) := by ring
      _ ≤ (A7 ^ n) (0 : Idx) (0 : Idx) * v (0 : Idx) :=
        mul_le_mul_of_nonneg_right (A7_pow_zero_zero_ge_one n) hv0non
  exact le_trans hmul hle

theorem totalMass_ge_v0_of_pos {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ n, v (0 : Idx) ≤ totalMass v n := by
  intro n
  have hnon : ∀ i : Idx, 0 ≤ (A7 ^ n *ᵥ v) i := A7_iterate_nonneg (fun i => (hv i).le) n
  have hle : (A7 ^ n *ᵥ v) (0 : Idx) ≤ ∑ i : Idx, (A7 ^ n *ᵥ v) i := by
    exact Finset.single_le_sum (fun x hx => hnon x) (Finset.mem_univ _)
  exact le_trans (firstCoord_ge_v0_of_pos hv n) (by simpa [totalMass, firstCoord] using hle)


theorem invSum_pos_of_pos {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    0 < ∑ i : Idx, (v i)⁻¹ := by
  exact Finset.sum_pos (fun i hi => inv_pos.mpr (hv i)) (Finset.univ_nonempty)

theorem A7_col_sum_mul_v_le_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i)
    (m : ℕ) (j : Idx) :
    (∑ i : Idx, (A7 ^ m) i j) * v j ≤ totalMass v m := by
  rw [Finset.sum_mul]
  simp only [totalMass, Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun i hi =>
    Finset.single_le_sum
      (fun k hk => mul_nonneg (A7_pow_entry_nonneg m i k) (le_of_lt (hv k)))
      (Finset.mem_univ j)

theorem A7_col_sum_le_inv_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i)
    (m : ℕ) (j : Idx) :
    (∑ i : Idx, (A7 ^ m) i j) ≤ (v j)⁻¹ * totalMass v m := by
  have h := mul_le_mul_of_nonneg_left (A7_col_sum_mul_v_le_totalMass hv m j)
      (inv_nonneg.mpr (le_of_lt (hv j)))
  have hvne : v j ≠ 0 := (hv j).ne'
  calc
    (∑ i : Idx, (A7 ^ m) i j) = (v j)⁻¹ * ((∑ i : Idx, (A7 ^ m) i j) * v j) := by
      field_simp [hvne]
    _ ≤ (v j)⁻¹ * totalMass v m := h

theorem totalMass_almost_submultiplicative_invSum {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ m n, totalMass v (m + n) ≤ (∑ j : Idx, (v j)⁻¹) * totalMass v m * totalMass v n := by
  intro m n
  let C : ℝ := ∑ j : Idx, (v j)⁻¹
  have hC_nonneg : 0 ≤ C := (invSum_pos_of_pos hv).le
  have htm_nonneg : 0 ≤ totalMass v m := (totalMass_pos_of_pos hv m).le
  have hx_nonneg : ∀ j : Idx, 0 ≤ (A7 ^ n *ᵥ v) j := A7_iterate_nonneg (fun i => (hv i).le) n
  have h_expand : totalMass v (m + n) =
      ∑ j : Idx, (∑ i : Idx, (A7 ^ m) i j) * (A7 ^ n *ᵥ v) j := by
    simp only [totalMass]
    rw [pow_add, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp [Finset.sum_mul]
  rw [h_expand]
  calc
    (∑ j : Idx, (∑ i : Idx, (A7 ^ m) i j) * (A7 ^ n *ᵥ v) j)
        ≤ ∑ j : Idx, ((v j)⁻¹ * totalMass v m) * (A7 ^ n *ᵥ v) j := by
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (A7_col_sum_le_inv_totalMass hv m j) (hx_nonneg j)
    _ ≤ ∑ j : Idx, (C * totalMass v m) * (A7 ^ n *ᵥ v) j := by
      exact Finset.sum_le_sum fun j hj => by
        have hinv_le : (v j)⁻¹ ≤ C := by
          exact Finset.single_le_sum (fun k hk => (inv_pos.mpr (hv k)).le) (Finset.mem_univ j)
        have hleft : (v j)⁻¹ * totalMass v m ≤ C * totalMass v m :=
          mul_le_mul_of_nonneg_right hinv_le htm_nonneg
        exact mul_le_mul_of_nonneg_right hleft (hx_nonneg j)
    _ = C * totalMass v m * totalMass v n := by
      simp [totalMass, Finset.mul_sum]

theorem totalMass_log_bddBelow_invSum {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    BddBelow (range fun n : ℕ =>
      (Real.log (totalMass v n) + Real.log (∑ j : Idx, (v j)⁻¹)) / (n : ℝ)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  let C : ℝ := ∑ j : Idx, (v j)⁻¹
  have hCpos : 0 < C := invSum_pos_of_pos hv
  have htmpos : 0 < totalMass v n := totalMass_pos_of_pos hv n
  have hinv_le_C : (v (0 : Idx))⁻¹ ≤ C := by
    exact Finset.single_le_sum (fun k hk => (inv_pos.mpr (hv k)).le) (Finset.mem_univ _)
  have hv0pos : 0 < v (0 : Idx) := hv 0
  have h_one_le_v0C : (1 : ℝ) ≤ v (0 : Idx) * C := by
    calc
      (1 : ℝ) = v (0 : Idx) * (v (0 : Idx))⁻¹ := by
        field_simp [hv0pos.ne']
      _ ≤ v (0 : Idx) * C := mul_le_mul_of_nonneg_left hinv_le_C hv0pos.le
  have h_one_le_tmC : (1 : ℝ) ≤ totalMass v n * C := by
    exact le_trans h_one_le_v0C
      (mul_le_mul_of_nonneg_right (totalMass_ge_v0_of_pos hv n) hCpos.le)
  have hlog_mul_nonneg : 0 ≤ Real.log (totalMass v n * C) := by
    rw [← Real.log_one]
    exact Real.log_le_log zero_lt_one h_one_le_tmC
  have hnum_nonneg : 0 ≤ Real.log (totalMass v n) + Real.log C := by
    rwa [Real.log_mul htmpos.ne' hCpos.ne'] at hlog_mul_nonneg
  exact div_nonneg hnum_nonneg (Nat.cast_nonneg n)

theorem A7pow10_row0_ge_one (j : Idx) : (1 : ℝ) ≤ A7pow10 (0 : Idx) j := by
  fin_cases j <;> norm_num [A7pow10]

theorem A7pow10_col_sum_le_300 (j : Idx) :
    (∑ i : Idx, A7pow10 i j) ≤ (300 : ℝ) := by
  fin_cases j <;> norm_num [A7pow10, Fin.sum_univ_succ]

theorem firstCoord_ten_add_ge_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i) (n : ℕ) :
    totalMass v n ≤ firstCoord v (10 + n) := by
  let x : Idx → ℝ := A7 ^ n *ᵥ v
  have hx_nonneg : ∀ j : Idx, 0 ≤ x j := A7_iterate_nonneg (fun i => (hv i).le) n
  have h_expand : firstCoord v (10 + n) = ∑ j : Idx, A7pow10 (0 : Idx) j * x j := by
    simp only [firstCoord]
    rw [pow_add, ← Matrix.mulVec_mulVec, A7_pow10]
    rfl
  rw [h_expand]
  simp only [totalMass]
  calc
    (∑ j : Idx, x j) = ∑ j : Idx, (1 : ℝ) * x j := by simp
    _ ≤ ∑ j : Idx, A7pow10 (0 : Idx) j * x j := by
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (A7pow10_row0_ge_one j) (hx_nonneg j)

theorem totalMass_ten_add_le_300 {v : Idx → ℝ} (hv : ∀ i, 0 < v i) (n : ℕ) :
    totalMass v (10 + n) ≤ (300 : ℝ) * totalMass v n := by
  let w : Idx → ℝ := A7 ^ n *ᵥ v
  have hw_nonneg : ∀ j : Idx, 0 ≤ w j := A7_iterate_nonneg (fun i => (hv i).le) n
  have h_expand : totalMass v (10 + n) = ∑ j : Idx, (∑ i : Idx, A7pow10 i j) * w j := by
    simp only [totalMass]
    rw [pow_add, ← Matrix.mulVec_mulVec, A7_pow10]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp [w, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [h_expand]
  calc
    (∑ j : Idx, (∑ i : Idx, A7pow10 i j) * w j)
        ≤ ∑ j : Idx, (300 : ℝ) * w j := by
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (A7pow10_col_sum_le_300 j) (hw_nonneg j)
    _ = (300 : ℝ) * totalMass v n := by
      simp [totalMass, w, Finset.mul_sum]

theorem firstCoord_eventually_lower_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ᶠ n in atTop, ((1 : ℝ) / 300) * totalMass v n ≤ firstCoord v n := by
  filter_upwards [eventually_ge_atTop (10 : ℕ)] with N hN
  rcases Nat.exists_eq_add_of_le hN with ⟨n, rfl⟩
  have htm_pos : 0 < totalMass v (10 + n) := totalMass_pos_of_pos hv (10 + n)
  have hupper := totalMass_ten_add_le_300 hv n
  have hlower := firstCoord_ten_add_ge_totalMass hv n
  have h300pos : (0 : ℝ) < 300 := by norm_num
  calc
    ((1 : ℝ) / 300) * totalMass v (10 + n)
        ≤ (1 / 300 : ℝ) * ((300 : ℝ) * totalMass v n) := by
      exact mul_le_mul_of_nonneg_left hupper (by norm_num)
    _ = totalMass v n := by ring
    _ ≤ firstCoord v (10 + n) := hlower

theorem firstCoord_le_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ n, firstCoord v n ≤ totalMass v n := by
  intro n
  have hnon : ∀ i : Idx, 0 ≤ (A7 ^ n *ᵥ v) i := A7_iterate_nonneg (fun i => (hv i).le) n
  exact Finset.single_le_sum (fun x hx => hnon x) (Finset.mem_univ _)

theorem firstCoord_eventually_upper_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ᶠ n in atTop, firstCoord v n ≤ (1 : ℝ) * totalMass v n := by
  filter_upwards with n
  simpa using firstCoord_le_totalMass hv n

/-- Fully automatic concrete corollary: every strictly positive initial vector has a
convergent first-coordinate root-growth sequence for the `A7` orbit. -/
theorem exists_firstCoord_A7_root_limit_of_pos
    (v : Idx → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (firstCoord v n) ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  refine exists_firstCoord_A7_root_limit_from_totalMass_bounds
    v (totalMass_pos_of_pos hv) (firstCoord_nonneg_of_nonneg (fun i => (hv i).le))
    (C := ∑ j : Idx, (v j)⁻¹) (c := (1 : ℝ) / 300) (d := 1)
    ?hC ?hc ?hd ?hsub ?hbdd ?hlo ?hhi
  · exact invSum_pos_of_pos hv
  · norm_num
  · norm_num
  · exact totalMass_almost_submultiplicative_invSum hv
  · exact totalMass_log_bddBelow_invSum hv
  · exact firstCoord_eventually_lower_totalMass hv
  · exact firstCoord_eventually_upper_totalMass hv





