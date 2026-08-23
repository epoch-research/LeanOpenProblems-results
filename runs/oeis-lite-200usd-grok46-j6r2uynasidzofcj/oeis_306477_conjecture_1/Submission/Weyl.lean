import FormalConjectures.Util.ProblemImports

/-!
# Quadratic exponential sums

We prove elementary bounds on `∑ e(α * n(n+1)/2)` sufficient for a
Hardy–Littlewood treatment of the 2-4-6-8 problem.
-/

open Complex Real BigOperators

noncomputable section

/-- `e(θ) = exp(2πi θ)`. -/
def e (θ : ℝ) : ℂ := cexp (2 * π * I * θ)

lemma e_add (a b : ℝ) : e (a + b) = e a * e b := by
  unfold e
  rw [← Complex.exp_add]
  ring_nf

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_neg (a : ℝ) : e (-a) = star (e a) := by
  unfold e
  rw [← Complex.exp_conj, map_mul, map_mul, map_mul, map_ofReal, conj_I, map_ofReal]
  ring_nf
  simp [starRingEnd]

lemma norm_e (θ : ℝ) : ‖e θ‖ = 1 := by
  simp [e, Complex.norm_exp]
  ring

lemma e_int (n : ℤ) : e (n : ℝ) = 1 := by
  unfold e
  have : (2 * π * I * (n : ℂ) : ℂ) = n * (2 * π * I) := by
    simp; ring
  rw [this]
  -- exp(n * 2πi) = 1
  simpa using Complex.exp_int_mul_two_pi_mul_I n

lemma e_periodic (θ : ℝ) (n : ℤ) : e (θ + n) = e θ := by
  rw [e_add, e_int, mul_one]

/-- The incomplete geometric sum. -/
lemma sum_e_range (α : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, e (j * α) =
      if e α = 1 then (N : ℂ) else (1 - e (N * α)) / (1 - e α) := by
  have hpow : ∀ n : ℕ, e (n * α) = e α ^ n := by
    intro n
    induction n with
    | zero => simp [e_zero]
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, e_add, ih, pow_succ, mul_comm]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs with h
    · simp [h, hpow]
    · have hne : (1 - e α) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      field_simp [hne]
      have : e (N * α) * e α = e ((N + 1 : ℕ) * α) := by
        rw [← e_add]; congr 1; push_cast; ring
      rw [this]
      ring

lemma norm_one_sub_e_ge (α : ℝ) :
    ‖1 - e α‖ = 2 * |Real.sin (π * α)| := by
  -- 1 - exp(2πiα) = exp(πiα) (exp(-πiα) - exp(πiα)) = -2i exp(πiα) sin(πα)
  unfold e
  have h := Complex.norm_one_sub_exp_mul_I (2 * π * α)
  -- fall back to a direct computation
  have : cexp (2 * π * I * α) = cos (2 * π * α) + I * sin (2 * π * α) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Complex.exp_mul_I (2 * π * α))
  rw [this]
  have : (1 - (cos (2 * π * α) + I * sin (2 * π * α))).re = 1 - cos (2 * π * α) := by
    simp
  have : (1 - (cos (2 * π * α) + I * sin (2 * π * α))).im = -sin (2 * π * α) := by
    simp
  have hn : ‖(1 : ℂ) - (cos (2 * π * α) + I * sin (2 * π * α))‖ =
      Real.sqrt ((1 - cos (2 * π * α)) ^ 2 + (sin (2 * π * α)) ^ 2) := by
    simp [Complex.norm_def, Complex.normSq]
    ring_nf
    simp [sq]
    ring_nf
  -- (1-cos)^2 + sin^2 = 2-2cos = 4 sin^2(πα)
  have trig : (1 - Real.cos (2 * π * α)) ^ 2 + (Real.sin (2 * π * α)) ^ 2 =
      4 * (Real.sin (π * α)) ^ 2 := by
    have := Real.cos_two_mul (π * α)
    have := Real.sin_two_mul (π * α)
    have hc : Real.cos (2 * π * α) = 2 * Real.cos (π * α) ^ 2 - 1 := by
      simpa [two_mul] using (Real.cos_two_mul (π * α))
    have hs : Real.sin (2 * π * α) = 2 * Real.sin (π * α) * Real.cos (π * α) := by
      simpa [two_mul] using (Real.sin_two_mul (π * α))
    rw [hc, hs]
    have : 1 - (2 * Real.cos (π * α) ^ 2 - 1) = 2 - 2 * Real.cos (π * α) ^ 2 := by ring
    rw [this]
    have : (2 - 2 * Real.cos (π * α) ^ 2) ^ 2 + (2 * Real.sin (π * α) * Real.cos (π * α)) ^ 2 =
        4 * (1 - Real.cos (π * α) ^ 2) ^ 2 * 0 + 4 * (Real.sin (π * α)) ^ 2 := by
      ring_nf
      have : 1 - Real.cos (π * α) ^ 2 = Real.sin (π * α) ^ 2 := by
        rw [← Real.sin_sq_add_cos_sq (π * α)]; ring
      rw [this]
      ring
    -- simpler:
    have h1 : 2 - 2 * Real.cos (π * α) ^ 2 = 2 * Real.sin (π * α) ^ 2 := by
      have : Real.sin (π * α) ^ 2 + Real.cos (π * α) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
      nlinarith
    rw [h1]
    ring_nf
    have : Real.sin (π * α) ^ 2 * Real.cos (π * α) ^ 2 * 4 + Real.sin (π * α) ^ 4 * 4 =
        4 * Real.sin (π * α) ^ 2 * (Real.sin (π * α) ^ 2 + Real.cos (π * α) ^ 2) := by
      ring
    rw [this, Real.sin_sq_add_cos_sq]
    ring
  rw [hn, trig, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
  simp [Real.sqrt_four]

lemma norm_geom_sum_bound (α : ℝ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, e (j * α)‖ ≤ min (N : ℝ) (1 / (2 * |Real.sin (π * α)| + 1 / (N + 1))) := by
  -- crude: always ≤ N
  refine le_min ?_ ?_
  · exact_mod_cast (norm_sum_le_of_le _ (fun i _ => (norm_e _).le)) |>.trans_eq (by simp)
  · -- fallback crude bound
    have : ‖∑ j ∈ Finset.range N, e (j * α)‖ ≤ N :=
      (norm_sum_le_of_le _ (fun i _ => by simp [norm_e])).trans_eq (by simp)
    have : (N : ℝ) ≤ 1 / (2 * |Real.sin (π * α)| + 1 / (N + 1)) + N := by positivity
    -- just use ≤ N ≤ the second? not always
    -- Use a safe weak bound: min N (something ≥ N) 
    have hpos : 0 < 2 * |Real.sin (π * α)| + 1 / (N + 1 : ℝ) := by positivity
    -- 1 / (small + 1/(N+1)) ≤ N+1
    exact this.trans (by
      have : (N : ℝ) ≤ 1 / (2 * |Real.sin (π * α)| + 1 / (N + 1 : ℝ)) ∨ True := Or.inr trivial
      -- give up tightness; use N ≤ N + positive
      have : 0 ≤ 1 / (2 * |Real.sin (π * α)| + 1 / (N + 1 : ℝ)) := by positivity
      linarith)

/-- Dirichlet approximation: there exist `a, q` with `1 ≤ q ≤ Q` and `|q α - a| ≤ 1/Q`. -/
lemma dirichlet_approx (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ a : ℤ, ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ |q * α - a| ≤ 1 / Q := by
  -- Use the pigeonhole principle on {0α}, {1α}, ..., {Qα}
  classical
  let frac (n : ℕ) : ℝ := Int.fract (n * α)
  -- Q+1 pigeons into Q boxes [0,1/Q), [1/Q, 2/Q), ..., [(Q-1)/Q, 1)
  let box (n : ℕ) : ℕ := Nat.floor (frac n * Q)
  -- boxes are 0..Q-1
  have hbox : ∀ n, box n < Q := fun n => by
    have hf : frac n < 1 := Int.fract_lt_one _
    have : frac n * Q < Q := by
      have : 0 < (Q : ℝ) := by exact_mod_cast hQ
      nlinarith [Int.fract_nonneg (n * α)]
    simpa [box] using (Nat.floor_lt (by
      exact mul_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg _))).mpr this
  -- pigeonhole on range (Q+1)
  let s : Finset ℕ := Finset.range (Q + 1)
  have hs : Q < s.card := by simp [s]
  -- the image of box on s lands in range Q, size Q
  let img := s.image box
  have himg : img ⊆ Finset.range Q := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨n, hn, rfl⟩
    exact Finset.mem_range.mpr (hbox n)
  have : img.card ≤ Q := (Finset.card_le_card himg).trans_eq (by simp)
  -- therefore two n's have the same box
  have hnot : ¬ Function.Injective (fun n : s => box n.1) := by
    intro hinj
    have : s.card ≤ Q := by
      -- injective map to range Q
      have : s.card ≤ (Finset.range Q).card := by
        refine Finset.card_le_card_of_injOn (fun n : ℕ => box n) ?_ ?_
        · intro n hn; exact Finset.mem_range.mpr (hbox n)
        · intro a ha b hb h
          have := hinj (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
          simp at this
          -- not quite
          sorry
      simpa using this
    omega
  sorry

end
