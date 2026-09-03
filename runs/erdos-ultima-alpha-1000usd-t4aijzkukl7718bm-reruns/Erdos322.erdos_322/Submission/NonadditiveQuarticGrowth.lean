import Submission.QuarticAdditiveBound

/-! Nonadditive quartic representations are also unbounded. -/
namespace Erdos322Research

/-- A common denominator for a finite collection of points on the rational curve. -/
def quarticCurveDenominator (m : ℕ) : ℕ :=
  ∏ i : Fin (m + 1), (((i : ℕ) + 3) ^ 4 + 1)

private lemma curveDenominator_pos (m : ℕ) : 0 < quarticCurveDenominator m := by
  unfold quarticCurveDenominator
  apply Finset.prod_pos
  intro i _
  positivity

private lemma curveFactor_dvd (m : ℕ) (i : Fin (m + 1)) :
    ((i : ℕ) + 3) ^ 4 + 1 ∣ quarticCurveDenominator m := by
  unfold quarticCurveDenominator
  exact Finset.dvd_prod_of_mem (fun j : Fin (m + 1) ↦ ((j : ℕ) + 3) ^ 4 + 1)
    (Finset.mem_univ i)

private def curveScale (m : ℕ) (i : Fin (m + 1)) : ℕ :=
  quarticCurveDenominator m / (((i : ℕ) + 3) ^ 4 + 1)

private lemma curveScale_pos (m : ℕ) (i : Fin (m + 1)) : 0 < curveScale m i := by
  exact Nat.div_pos (Nat.le_of_dvd (curveDenominator_pos m) (curveFactor_dvd m i))
    (by positivity)

private lemma curveScale_mul (m : ℕ) (i : Fin (m + 1)) :
    (((i : ℕ) + 3) ^ 4 + 1) * curveScale m i = quarticCurveDenominator m :=
  Nat.mul_div_cancel' (curveFactor_dvd m i)

private def curveTuple (m : ℕ) (i : Fin (m + 1)) : Fin 4 → ℕ :=
  ![2 * ((i : ℕ) + 3) * curveScale m i,
    2 * ((i : ℕ) + 3) ^ 3 * curveScale m i,
    (((i : ℕ) + 3) ^ 4 - 1) * curveScale m i,
    (((i : ℕ) + 3) ^ 4 - 1) * curveScale m i]

private lemma curveTuple_sum (m : ℕ) (i : Fin (m + 1)) :
    ∑ j, curveTuple m i j ^ 4 = 2 * quarticCurveDenominator m ^ 4 := by
  let x : ℕ := i + 3
  have hx : 3 ≤ x := by dsimp [x]; omega
  have hxp : 1 ≤ x ^ 4 := by have := Nat.le_pow (a := x) (by decide : 0 < 4); omega
  have hid : (2 * x) ^ 4 + (2 * x ^ 3) ^ 4 + 2 * (x ^ 4 - 1) ^ 4 =
      2 * (x ^ 4 + 1) ^ 4 := by
    zify [hxp]
    ring
  calc
    ∑ j, curveTuple m i j ^ 4 =
        ((2 * x) ^ 4 + (2 * x ^ 3) ^ 4 + 2 * (x ^ 4 - 1) ^ 4) * curveScale m i ^ 4 := by
      simp only [Fin.sum_univ_four, curveTuple, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      dsimp [x]
      ring
    _ = 2 * ((x ^ 4 + 1) * curveScale m i) ^ 4 := by rw [hid]; ring
    _ = 2 * quarticCurveDenominator m ^ 4 := by rw [curveScale_mul]

private lemma curveTuple_gap (m : ℕ) (i : Fin (m + 1)) :
    curveTuple m i 0 + curveTuple m i 1 < curveTuple m i 2 := by
  let x : ℕ := i + 3
  have hx : 3 ≤ x := by dsimp [x]; omega
  have hx2 : 9 ≤ x ^ 2 := by simpa using Nat.pow_le_pow_left hx 2
  have hx3 : 9 * x ≤ x ^ 3 := by nlinarith
  have hx4 : 3 * x ^ 3 ≤ x ^ 4 := by
    calc
      3 * x ^ 3 ≤ x * x ^ 3 := Nat.mul_le_mul_right _ hx
      _ = x ^ 4 := by ring
  have hbase : 2 * x + 2 * x ^ 3 < x ^ 4 - 1 := by omega
  change 2 * x * curveScale m i + 2 * x ^ 3 * curveScale m i <
    (x ^ 4 - 1) * curveScale m i
  rw [← add_mul]
  exact Nat.mul_lt_mul_of_pos_right hbase (curveScale_pos m i)

private lemma no_additive_triple_of_gap {u v w : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hgap : u + v < w) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ![u,v,w,w] k ≠ ![u,v,w,w] i + ![u,v,w,w] j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> omega

private lemma curveTuple_nonadditive (m : ℕ) (i : Fin (m + 1)) (σ : Equiv.Perm (Fin 4)) :
    curveTuple m i (σ 2) ≠ curveTuple m i (σ 0) + curveTuple m i (σ 1) := by
  apply no_additive_triple_of_gap (u := curveTuple m i 0) (v := curveTuple m i 1)
    (w := curveTuple m i 2)
  · change 0 < 2 * ((i : ℕ) + 3) * curveScale m i
    have := curveScale_pos m i
    positivity
  · change 0 < 2 * ((i : ℕ) + 3) ^ 3 * curveScale m i
    have := curveScale_pos m i
    positivity
  · exact curveTuple_gap m i
  · exact σ.injective.ne (by decide)
  · exact σ.injective.ne (by decide)
  · exact σ.injective.ne (by decide)

private def boundedCurveTuple (m : ℕ) (i : Fin (m + 1)) :
    Fin 4 → Fin (2 * quarticCurveDenominator m ^ 4 + 1) := fun j ↦
  ⟨curveTuple m i j, by
    have hs := curveTuple_sum m i
    have hb : curveTuple m i j ^ 4 ≤ ∑ l, curveTuple m i l ^ 4 :=
      Finset.single_le_sum (f := fun l ↦ curveTuple m i l ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    have hp := Nat.le_pow (a := curveTuple m i j) (by decide : 0 < 4)
    omega⟩

private lemma boundedCurveTuple_injective (m : ℕ) : Function.Injective (boundedCurveTuple m) := by
  intro i j heq
  have h0 := congrArg (fun a ↦ ((a 0 : Fin (2 * quarticCurveDenominator m ^ 4 + 1)) : ℕ)) heq
  have h1 := congrArg (fun a ↦ ((a 1 : Fin (2 * quarticCurveDenominator m ^ 4 + 1)) : ℕ)) heq
  change curveTuple m i 0 = curveTuple m j 0 at h0
  change curveTuple m i 1 = curveTuple m j 1 at h1
  have hi : curveTuple m i 1 = curveTuple m i 0 * ((i : ℕ) + 3) ^ 2 := by
    dsimp [curveTuple]
    ring
  have hj : curveTuple m j 1 = curveTuple m j 0 * ((j : ℕ) + 3) ^ 2 := by
    dsimp [curveTuple]
    ring
  have hpos : 0 < curveTuple m i 0 := by
    change 0 < 2 * ((i : ℕ) + 3) * curveScale m i
    have := curveScale_pos m i
    positivity
  have hp : ((i : ℕ) + 3) ^ 2 = ((j : ℕ) + 3) ^ 2 := by
    apply Nat.mul_left_cancel hpos
    rw [← hi, h0, ← hj, h1]
  have hval := Nat.pow_left_injective (by decide : 2 ≠ 0) hp
  apply Fin.ext
  omega

/-- The complement of the additive-triple locus has arbitrarily large counts. -/
theorem nonadditive_quartic_count_lower (m : ℕ) :
    m + 1 ≤ nonadditiveQuarticCount (2 * quarticCurveDenominator m ^ 4) := by
  classical
  unfold nonadditiveQuarticCount
  have h := Finset.card_le_card_of_injOn (boundedCurveTuple m)
    (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 4 → Fin (2 * quarticCurveDenominator m ^ 4 + 1) ↦
      (∑ i, (a i : ℕ) ^ 4 = 2 * quarticCurveDenominator m ^ 4) ∧ ¬ HasAdditiveTriple a))
    (by
      intro i _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨curveTuple_sum m i, ?_⟩
      rintro ⟨σ,hσ⟩
      exact curveTuple_nonadditive m i σ hσ)
    (boundedCurveTuple_injective m).injOn
  simpa using h

private lemma curveTarget_large (m : ℕ) : m < 2 * quarticCurveDenominator m ^ 4 := by
  have hd := curveFactor_dvd m (⟨m, by omega⟩ : Fin (m + 1))
  have hle := Nat.le_of_dvd (curveDenominator_pos m) hd
  change (m + 3) ^ 4 + 1 ≤ quarticCurveDenominator m at hle
  have h1 := Nat.le_pow (a := m + 3) (by decide : 0 < 4)
  have h2 := Nat.le_pow (a := quarticCurveDenominator m) (by decide : 0 < 4)
  omega

/-- Even after all additive triples are removed, no fixed uniform count bound
is possible. This remains much weaker than a positive-power lower bound. -/
theorem nonadditive_quartic_counts_exceed_any_bound (M : ℕ) :
    {n : ℕ | M < nonadditiveQuarticCount n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨2 * quarticCurveDenominator (max M N) ^ 4, ?_, ?_⟩
  · change M < nonadditiveQuarticCount (2 * quarticCurveDenominator (max M N) ^ 4)
    have h := nonadditive_quartic_count_lower (max M N)
    omega
  · have h := curveTarget_large (max M N)
    omega

end Erdos322Research
