import FormalConjecturesUtil

/-! Irrational lines meet any two-dimensional residue-grid near arbitrarily
large abscissas, in absolute value. -/
namespace Erdos952Investigation
namespace IrrationalLatticeApproximation

set_option maxHeartbeats 0

lemma dense_linear_combinations {α : ℝ} (hα : Irrational α) :
    DenseRange (fun v : ℤ × ℤ => α * (v.1 : ℝ) + (v.2 : ℝ)) := by
  have hd : Dense (AddSubgroup.closure ({α, 1} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (by simpa using hα)
  apply hd.mono
  intro y hy
  obtain ⟨k, l, hkl⟩ := AddSubgroup.mem_closure_pair.mp hy
  refine ⟨(k, l), ?_⟩
  simpa [zsmul_eq_mul, mul_comm] using hkl

lemma dense_affine_grid {α : ℝ} (hα : Irrational α) (A P : ℤ) (hP : P ≠ 0) :
    DenseRange (fun v : ℤ × ℤ => α * ((A : ℝ) + (P : ℝ)*v.1) - (P : ℝ)*v.2) := by
  let g : ℝ → ℝ := fun t => α*(A : ℝ) + (P : ℝ)*t
  have hg : Function.Surjective g := by
    intro y
    refine ⟨(y - α*(A : ℝ))/(P : ℝ), ?_⟩
    dsimp [g]
    have hP' : (P : ℝ) ≠ 0 := by exact_mod_cast hP
    field_simp
    ring
  have hcont : Continuous g := by fun_prop
  have hd := hg.denseRange.comp (dense_linear_combinations hα) hcont
  apply hd.mono
  rintro y ⟨⟨k, l⟩, rfl⟩
  refine ⟨(k, -l), ?_⟩
  simp only [Function.comp_apply, g, Int.cast_neg]
  ring

lemma arbitrarily_far_grid_center {α : ℝ} (hα : Irrational α)
    (A P M : ℤ) (hP : 0 < P) :
    ∃ k l : ℤ, M < |A + P*k| ∧ |α*((A + P*k : ℤ) : ℝ) - ((P*l : ℤ) : ℝ)| < 1 := by
  obtain ⟨B, hB⟩ := exists_int_gt (|α| * |(M : ℝ)| + 2)
  let T : Set (ℤ × ℤ) := Set.Icc (-|M|) |M| ×ˢ Set.Icc (-B) B
  have hT : T.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  let f : ℤ × ℤ → ℝ := fun v => α * (v.1 : ℝ) - (v.2 : ℝ)
  have hbad : (f '' T).Finite := hT.image f
  let g : ℤ × ℤ → ℝ := fun v => α * ((A : ℝ) + (P : ℝ)*v.1) - (P : ℝ)*v.2
  have hd : Dense (Set.range g \ (f '' T)) :=
    (dense_affine_grid hα A P hP.ne').diff_finite hbad
  obtain ⟨y, ⟨⟨⟨k, l⟩, hkl⟩, hybad⟩, hy⟩ :=
    hd.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr (by norm_num : (-1 : ℝ) < 1))
  have hnear : |α*((A + P*k : ℤ) : ℝ) - ((P*l : ℤ) : ℝ)| < 1 := by
    have hy' : (-1 : ℝ) < g (k, l) ∧ g (k, l) < 1 := by rw [hkl]; exact hy
    simpa only [g, Int.cast_add, Int.cast_mul] using (abs_lt.mpr hy')
  refine ⟨k, l, ?_, hnear⟩
  by_contra hn
  have hM : |A + P*k| ≤ |M| := (le_of_not_gt hn).trans (le_abs_self M)
  have hMr : |((A + P*k : ℤ) : ℝ)| ≤ |(M : ℝ)| := by exact_mod_cast hM
  have hprod : |α * ((A + P*k : ℤ) : ℝ)| ≤ |α| * |(M : ℝ)| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hMr (abs_nonneg α)
  have hpl : |((P*l : ℤ) : ℝ)| < B := by
    have hb := abs_sub_comm (α*((A + P*k : ℤ) : ℝ)) ((P*l : ℤ) : ℝ)
    have ht := abs_add_le (((P*l : ℤ) : ℝ) - α*((A + P*k : ℤ) : ℝ))
      (α*((A + P*k : ℤ) : ℝ))
    rw [sub_add_cancel] at ht
    rw [← hb] at ht
    linarith
  have hplZ : |P*l| ≤ B := by
    have ht : |P*l| < B := by exact_mod_cast hpl
    exact ht.le
  have hmem : (A + P*k, P*l) ∈ T := ⟨abs_le.mp hM, abs_le.mp hplZ⟩
  apply hybad
  refine ⟨(A + P*k, P*l), hmem, ?_⟩
  dsimp [f]
  rw [← hkl]
  simp [g]

#print axioms arbitrarily_far_grid_center

end IrrationalLatticeApproximation
end Erdos952Investigation
