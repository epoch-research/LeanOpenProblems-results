import FormalConjecturesUtil

/-! A normalized spiral distance model. The existence of admissible parameters
of arbitrary length is not proved here. -/
namespace Erdos213.Spiral

noncomputable def point (z : ℂ) (n : ℕ) : ℂ := ∑ i ∈ Finset.range n, z^i

@[simp] lemma point_zero (z : ℂ) : point z 0=0 := by simp [point]
@[simp] lemma point_one (z : ℂ) : point z 1=1 := by simp [point]

lemma point_add (z : ℂ) (m n : ℕ) : point z (m+n)=point z m+z^m*point z n := by
  simp only [point,Finset.sum_range_add,pow_add,Finset.mul_sum]

lemma point_sub (z : ℂ) (m n : ℕ) : point z (m+n)-point z m=z^m*point z n := by
  rw [point_add]
  ring

lemma dist_shift (z : ℂ) (m n : ℕ) :
    dist (point z (m+n)) (point z m)=‖z‖^m*‖point z n‖ := by
  rw [dist_eq_norm,point_sub,norm_mul,norm_pow]

lemma rational_distances {z : ℂ} {n : ℕ}
    (hz : ‖z‖ ∈ Set.range ((↑) : ℚ → ℝ))
    (hp : ∀ k < n, ‖point z k‖ ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∀ i < n, ∀ j < n, dist (point z i) (point z j) ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := hz
  have hh (i j : ℕ) (hi : i < n) (hji : j ≤ i) :
      dist (point z i) (point z j) ∈ Set.range ((↑) : ℚ → ℝ) := by
    obtain ⟨a,ha⟩ := hp (i-j) (by omega)
    have he : i=j+(i-j) := by omega
    have hd := dist_shift z j (i-j)
    rw [← he] at hd
    rw [hd]
    exact ⟨r^j*a,by simp [hr,ha]⟩
  intro i hi j hj
  rcases le_total j i with h|h
  · exact hh i j hi h
  · rw [dist_comm]
    exact hh j i hj h

/-- The norm of 1-z is deliberately absent: normalizing the first edge removes it. -/
lemma rational_distances_iff {z : ℂ} {n : ℕ} (hn : 3 ≤ n) :
    (∀ i < n, ∀ j < n, dist (point z i) (point z j) ∈ Set.range ((↑) : ℚ → ℝ)) ↔
    ‖z‖ ∈ Set.range ((↑) : ℚ → ℝ) ∧
      ∀ k < n, ‖point z k‖ ∈ Set.range ((↑) : ℚ → ℝ) := by
  constructor
  · intro hd
    constructor
    · have hh := hd 2 (by omega) 1 (by omega)
      have he := dist_shift z 1 1
      simp only [point_one,norm_one,pow_one,mul_one] at he
      simpa only [point_one,he] using hh
    · intro k hk
      have hh := hd k hk 0 (by omega)
      simpa using hh
  · rintro ⟨hz,hp⟩
    exact rational_distances hz hp

lemma point_two (z : ℂ) : point z 2=1+z := by simp [point,Finset.sum_range_succ]
lemma point_three (z : ℂ) : point z 3=1+z+z^2 := by simp [point,Finset.sum_range_succ]
lemma point_four (z : ℂ) : point z 4=(1+z)*(1+z^2) := by
  simp [point,Finset.sum_range_succ]
  ring

lemma normSq_two (z : ℂ) : Complex.normSq (point z 2)=Complex.normSq z+2*z.re+1 := by
  rw [point_two]
  simp [Complex.normSq_apply]
  ring

lemma normSq_three (z : ℂ) :
    Complex.normSq (point z 3)=(Complex.normSq z)^2-Complex.normSq z+1+
      2*z.re*(Complex.normSq z+1)+4*z.re^2 := by
  rw [point_three]
  simp [Complex.normSq_apply,pow_two]
  ring

lemma normSq_four (z : ℂ) :
    Complex.normSq (point z 4)=(Complex.normSq z+2*z.re+1)*
      ((Complex.normSq z-1)^2+4*z.re^2) := by
  rw [point_four,map_mul]
  simp [Complex.normSq_apply,pow_two]
  ring

lemma quartic_model (a b : ℚ) :
    (a^2)^2-a^2+1+2*((b^2-a^2-1)/2)*(a^2+1)+4*((b^2-a^2-1)/2)^2 =
      a^4-a^2*b^2+b^4-a^2-b^2+1 := by ring

lemma quartic_section (a : ℚ) :
    a^4-a^2*(a^2/2)^2+(a^2/2)^4-a^2-(a^2/2)^2+1=
      (a^4/4-a^2/2+1)^2 := by ring

noncomputable def seed : ℂ := ⟨-39/128,3*Real.sqrt 3927/128⟩

lemma seed_normSq : Complex.normSq seed=9/4 := by
  simp only [seed,Complex.normSq_apply]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤3927)]

private lemma norm_of_normSq {z : ℂ} {r : ℝ} (hr : 0≤r)
    (he : Complex.normSq z=r^2) : ‖z‖=r := by
  rw [Complex.normSq_eq_norm_sq] at he
  exact (sq_eq_sq₀ (norm_nonneg _) hr).mp he

lemma seed_norm : ‖seed‖=3/2 := by
  apply norm_of_normSq (by norm_num)
  rw [seed_normSq]
  norm_num

lemma seed_chords : ‖point seed 2‖=13/8 ∧ ‖point seed 3‖=95/64 ∧
    ‖point seed 4‖=1157/512 := by
  have hre : seed.re=-39/128 := rfl
  refine ⟨?_,?_,?_⟩
  · apply norm_of_normSq (by norm_num)
    norm_num [normSq_two,seed_normSq,hre]
  · apply norm_of_normSq (by norm_num)
    norm_num [normSq_three,seed_normSq,hre]
  · apply norm_of_normSq (by norm_num)
    norm_num [normSq_four,seed_normSq,hre]

lemma seed_five_rational_distances :
    ∀ i<5, ∀ j<5, dist (point seed i) (point seed j) ∈ Set.range ((↑) : ℚ → ℝ) := by
  apply rational_distances
  · exact ⟨3/2,by norm_num [seed_norm]⟩
  · intro k hk
    interval_cases k
    · exact ⟨0,by simp⟩
    · exact ⟨1,by simp⟩
    · exact ⟨13/8,by norm_num [seed_chords.1]⟩
    · exact ⟨95/64,by norm_num [seed_chords.2.1]⟩
    · exact ⟨1157/512,by norm_num [seed_chords.2.2]⟩

#print axioms dist_shift
#print axioms rational_distances_iff
#print axioms normSq_four
#print axioms quartic_section
#print axioms seed_five_rational_distances
end Erdos213.Spiral
