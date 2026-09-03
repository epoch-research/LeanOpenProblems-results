import Submission.FixedHeptadGeometry

/-! Finite-local controls attached to the fixed heptad. No global rational-
distance extension is asserted. -/
open EuclideanGeometry
namespace Erdos213.FixedHeptadLocal
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000
lemma px_old (t u : ℤ) (i : Fin 7) : px t i.castSucc=px u i.castSucc := by
  fin_cases i <;> norm_num [px,Fin.castSucc,Fin.castAdd,Fin.castLE]
lemma py_old (t u : ℤ) (i : Fin 7) : py t i.castSucc=py u i.castSucc := by
  fin_cases i <;> norm_num [py,Fin.castSucc,Fin.castAdd,Fin.castLE]
lemma old_points_fixed (t u : ℤ) (i : Fin 7) : point t i.castSucc=point u i.castSucc := by
  have h : (px t i.castSucc,py t i.castSucc)=(px u i.castSucc,py u i.castSucc) :=
    Prod.ext (px_old t u i) (py_old t u i)
  exact congrArg (fun q : ℤ×ℤ => (!₂[(q.1 : ℝ),(q.2 : ℝ)*Real.sqrt 2002] : ℝ²))
    h


def oldDistance : Fin 7 → Fin 7 → ℕ :=
  !![0,49595290,19232372,37050599,20595296,49212246,19838116;
    49595290,0,30612342,25381119,33712326,47853776,46094446;
    19232372,30612342,0,24606123,13174932,44686982,23926888;
    37050599,25381119,24606123,0,16468665,24040465,24797645;
    20595296,33712326,13174932,16468665,0,32180150,12872060;
    49212246,47853776,44686982,24040465,32180150,0,29908610;
    19838116,46094446,23926888,24797645,12872060,29908610,0]

lemma old_squared_distances (t : ℤ) (i j : Fin 7) :
    sqDist t i.castSucc j.castSucc=(oldDistance i j : ℤ)^2 := by
  fin_cases i <;> fin_cases j
  · change (0-(0 : ℤ))^2+2002*(0-(0))^2=(0 : ℤ)^2
    norm_num
  · change (0-(49595290 : ℤ))^2+2002*(0-(0))^2=(49595290 : ℤ)^2
    norm_num
  · change (0-(19079044 : ℤ))^2+2002*(0-(54168))^2=(19232372 : ℤ)^2
    norm_num
  · change (0-(32142553 : ℤ))^2+2002*(0-(-411864))^2=(37050599 : ℤ)^2
    norm_num
  · change (0-(17615968 : ℤ))^2+2002*(0-(-238464))^2=(20595296 : ℤ)^2
    norm_num
  · change (0-(26127018 : ℤ))^2+2002*(0-(-932064))^2=(49212246 : ℤ)^2
    norm_num
  · change (0-(7344908 : ℤ))^2+2002*(0-(-411864))^2=(19838116 : ℤ)^2
    norm_num
  · change (49595290-(0 : ℤ))^2+2002*(0-(0))^2=(49595290 : ℤ)^2
    norm_num
  · change (49595290-(49595290 : ℤ))^2+2002*(0-(0))^2=(0 : ℤ)^2
    norm_num
  · change (49595290-(19079044 : ℤ))^2+2002*(0-(54168))^2=(30612342 : ℤ)^2
    norm_num
  · change (49595290-(32142553 : ℤ))^2+2002*(0-(-411864))^2=(25381119 : ℤ)^2
    norm_num
  · change (49595290-(17615968 : ℤ))^2+2002*(0-(-238464))^2=(33712326 : ℤ)^2
    norm_num
  · change (49595290-(26127018 : ℤ))^2+2002*(0-(-932064))^2=(47853776 : ℤ)^2
    norm_num
  · change (49595290-(7344908 : ℤ))^2+2002*(0-(-411864))^2=(46094446 : ℤ)^2
    norm_num
  · change (19079044-(0 : ℤ))^2+2002*(54168-(0))^2=(19232372 : ℤ)^2
    norm_num
  · change (19079044-(49595290 : ℤ))^2+2002*(54168-(0))^2=(30612342 : ℤ)^2
    norm_num
  · change (19079044-(19079044 : ℤ))^2+2002*(54168-(54168))^2=(0 : ℤ)^2
    norm_num
  · change (19079044-(32142553 : ℤ))^2+2002*(54168-(-411864))^2=(24606123 : ℤ)^2
    norm_num
  · change (19079044-(17615968 : ℤ))^2+2002*(54168-(-238464))^2=(13174932 : ℤ)^2
    norm_num
  · change (19079044-(26127018 : ℤ))^2+2002*(54168-(-932064))^2=(44686982 : ℤ)^2
    norm_num
  · change (19079044-(7344908 : ℤ))^2+2002*(54168-(-411864))^2=(23926888 : ℤ)^2
    norm_num
  · change (32142553-(0 : ℤ))^2+2002*(-411864-(0))^2=(37050599 : ℤ)^2
    norm_num
  · change (32142553-(49595290 : ℤ))^2+2002*(-411864-(0))^2=(25381119 : ℤ)^2
    norm_num
  · change (32142553-(19079044 : ℤ))^2+2002*(-411864-(54168))^2=(24606123 : ℤ)^2
    norm_num
  · change (32142553-(32142553 : ℤ))^2+2002*(-411864-(-411864))^2=(0 : ℤ)^2
    norm_num
  · change (32142553-(17615968 : ℤ))^2+2002*(-411864-(-238464))^2=(16468665 : ℤ)^2
    norm_num
  · change (32142553-(26127018 : ℤ))^2+2002*(-411864-(-932064))^2=(24040465 : ℤ)^2
    norm_num
  · change (32142553-(7344908 : ℤ))^2+2002*(-411864-(-411864))^2=(24797645 : ℤ)^2
    norm_num
  · change (17615968-(0 : ℤ))^2+2002*(-238464-(0))^2=(20595296 : ℤ)^2
    norm_num
  · change (17615968-(49595290 : ℤ))^2+2002*(-238464-(0))^2=(33712326 : ℤ)^2
    norm_num
  · change (17615968-(19079044 : ℤ))^2+2002*(-238464-(54168))^2=(13174932 : ℤ)^2
    norm_num
  · change (17615968-(32142553 : ℤ))^2+2002*(-238464-(-411864))^2=(16468665 : ℤ)^2
    norm_num
  · change (17615968-(17615968 : ℤ))^2+2002*(-238464-(-238464))^2=(0 : ℤ)^2
    norm_num
  · change (17615968-(26127018 : ℤ))^2+2002*(-238464-(-932064))^2=(32180150 : ℤ)^2
    norm_num
  · change (17615968-(7344908 : ℤ))^2+2002*(-238464-(-411864))^2=(12872060 : ℤ)^2
    norm_num
  · change (26127018-(0 : ℤ))^2+2002*(-932064-(0))^2=(49212246 : ℤ)^2
    norm_num
  · change (26127018-(49595290 : ℤ))^2+2002*(-932064-(0))^2=(47853776 : ℤ)^2
    norm_num
  · change (26127018-(19079044 : ℤ))^2+2002*(-932064-(54168))^2=(44686982 : ℤ)^2
    norm_num
  · change (26127018-(32142553 : ℤ))^2+2002*(-932064-(-411864))^2=(24040465 : ℤ)^2
    norm_num
  · change (26127018-(17615968 : ℤ))^2+2002*(-932064-(-238464))^2=(32180150 : ℤ)^2
    norm_num
  · change (26127018-(26127018 : ℤ))^2+2002*(-932064-(-932064))^2=(0 : ℤ)^2
    norm_num
  · change (26127018-(7344908 : ℤ))^2+2002*(-932064-(-411864))^2=(29908610 : ℤ)^2
    norm_num
  · change (7344908-(0 : ℤ))^2+2002*(-411864-(0))^2=(19838116 : ℤ)^2
    norm_num
  · change (7344908-(49595290 : ℤ))^2+2002*(-411864-(0))^2=(46094446 : ℤ)^2
    norm_num
  · change (7344908-(19079044 : ℤ))^2+2002*(-411864-(54168))^2=(23926888 : ℤ)^2
    norm_num
  · change (7344908-(32142553 : ℤ))^2+2002*(-411864-(-411864))^2=(24797645 : ℤ)^2
    norm_num
  · change (7344908-(17615968 : ℤ))^2+2002*(-411864-(-238464))^2=(12872060 : ℤ)^2
    norm_num
  · change (7344908-(26127018 : ℤ))^2+2002*(-411864-(-932064))^2=(29908610 : ℤ)^2
    norm_num
  · change (7344908-(7344908 : ℤ))^2+2002*(-411864-(-411864))^2=(0 : ℤ)^2
    norm_num

lemma old_distances_integral (t : ℤ) (i j : Fin 7) :
    dist (point t i.castSucc) (point t j.castSucc)∈Set.range ((↑) : ℤ → ℝ) := by
  refine ⟨oldDistance i j,?_⟩
  have h := point_dist_sq t i.castSucc j.castSucc
  rw [old_squared_distances] at h
  push_cast at h ⊢
  nlinarith [dist_nonneg (x := point t i.castSucc) (y := point t j.castSucc),
    Nat.cast_nonneg (α := ℝ) (oldDistance i j)]

lemma sqDist_comm (t : ℤ) (i j : Fin 8) : sqDist t i j=sqDist t j i := by
  dsimp [sqDist]
  ring

lemma origin_squared (t : ℤ) : sqDist t 7 0=(2003*t)^2 := by
  dsimp [sqDist,px,py]
  ring

lemma origin_distance_integral {t : ℤ} (ht : threshold≤t) :
    dist (point t 7) (point t 0)∈Set.range ((↑) : ℤ → ℝ) := by
  refine ⟨2003*t,?_⟩
  have h := point_dist_sq t 7 0
  rw [origin_squared] at h
  have ht0 : (0 : ℝ)≤t := by exact_mod_cast (by dsimp [threshold] at ht; omega : (0 : ℤ)≤t)
  push_cast at h ⊢
  nlinarith [dist_nonneg (x := point t 7) (y := point t 0)]

lemma all_local_distances {p : ℕ} [Fact p.Prime] (t : ℤ)
    (h : ∀ i : Fin 6, IsSquare ((sqDist t 7 (oldIndex i) : ℤ) : ℤ_[p])) :
    ∀ i j : Fin 8, IsSquare ((sqDist t i j : ℤ) : ℤ_[p]) := by
  have hnew (i : Fin 7) : IsSquare ((sqDist t 7 i.castSucc : ℤ) : ℤ_[p]) := by
    rcases i.eq_zero_or_eq_succ with rfl | ⟨i,rfl⟩
    · rw [Fin.castSucc_zero,origin_squared]
      push_cast
      exact IsSquare.sq _
    · exact h i
  intro i j
  rcases i.eq_castSucc_or_eq_last with ⟨i,rfl⟩ | rfl
  · rcases j.eq_castSucc_or_eq_last with ⟨j,rfl⟩ | rfl
    · rw [old_squared_distances]
      push_cast
      exact IsSquare.sq _
    · rw [sqDist_comm]
      exact hnew i
  · rcases j.eq_castSucc_or_eq_last with ⟨j,rfl⟩ | rfl
    · exact hnew j
    · exact ⟨0,by simp [sqDist]⟩

/-- Any finite list of p-adic square tests can be passed by a genuine GP eighth
point attached to the fixed heptad, even though six new distances are irrational. -/
theorem fixed_heptad_local_control (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℤ) :
    ∃ t : ℤ, N<t ∧ threshold≤t ∧
      InGeneralPosition (Set.range (point t)) ∧
      (∀ (p : ℕ) (hp : p∈P), letI : Fact p.Prime := ⟨hP p hp⟩
        ∀ i j : Fin 8, IsSquare ((sqDist t i j : ℤ) : ℤ_[p])) ∧
      (∀ i : Fin 6, dist (point t 7) (point t (oldIndex i))∉Set.range ((↑) : ℚ → ℝ)) := by
  obtain ⟨t,ht,hs⟩ := FixedSourceLocal.simultaneous_local_perturbations P hP
    radii (fun _ => 2003^2) (fun i => -2*dots i) (by decide) (max N threshold)
  have hN : N<t := lt_of_le_of_lt (le_max_left _ _) ht
  have hT : threshold≤t := (le_max_right N threshold).trans ht.le
  refine ⟨t,hN,hT,(geometric_eight hT).2.2,?_,ray_distance_irrational hT⟩
  intro p hp
  letI : Fact p.Prime := ⟨hP p hp⟩
  apply all_local_distances
  intro i
  have h := hs p hp i
  rw [ray_formula]
  convert h using 1
  congr 1
  ring

#print axioms old_points_fixed
#print axioms old_distances_integral
#print axioms geometric_eight
#print axioms ray_distance_irrational
#print axioms fixed_heptad_local_control
end Erdos213.FixedHeptadLocal
