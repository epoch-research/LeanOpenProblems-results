import FormalConjecturesUtil

/-! Convexity, affine cells, and affine tails for finite nonnegative hinge sums.
These generic real lemmas are for certifying scalar budget tables. -/
namespace Erdos7FiniteHingeFunctions
open scoped BigOperators
set_option maxHeartbeats 1500000

noncomputable def hinge (t x : ℝ) : ℝ := max 0 (x-t)
noncomputable def eval (v : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  v 0+v 1*(x-1)+∑ j ∈ Finset.range N, v (j+2)*hinge (j+2) x
noncomputable def slope (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  v 1+∑ j ∈ Finset.range N, v (j+2)

lemma convex_affine (A B : ℝ) : ConvexOn ℝ Set.univ (fun x : ℝ => A*x+B) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hh : (a+b)*B=B := by rw [hab, one_mul]
  nlinarith

lemma convex_hinge (t : ℝ) : ConvexOn ℝ Set.univ (hinge t) := by
  have hh := (convexOn_const (0:ℝ) (convex_univ : Convex ℝ (Set.univ : Set ℝ))).sup
    (convex_affine 1 (-t))
  simpa only [Pi.sup_apply, one_mul, ← sub_eq_add_neg] using hh

lemma monotone_hinge (t : ℝ) : Monotone (hinge t) := by
  intro x y hxy
  exact max_le_max le_rfl (sub_le_sub_right hxy t)

lemma convex_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (fun x => ∑ i ∈ S, f i x) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  calc
    _ ≤ ∑ i ∈ S, (a*f i x+b*f i y) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [smul_eq_mul] using (hf i hi).2 hx hy ha hb hab
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

lemma eval_convex (v : ℕ → ℝ) (N : ℕ) (hv : ∀ j<N, 0 ≤ v (j+2)) :
    ConvexOn ℝ Set.univ (eval v N) := by
  have hlin : ConvexOn ℝ Set.univ (fun x => v 0+v 1*(x-1)) := by
    convert convex_affine (v 1) (v 0-v 1) using 1
    funext x; ring
  have hs : ConvexOn ℝ Set.univ (fun x => ∑ j ∈ Finset.range N, v (j+2)*hinge (j+2) x) :=
    convex_sum _ _ (fun j hj => by
      simpa only [smul_eq_mul] using ConvexOn.smul (hv j (Finset.mem_range.mp hj)) (convex_hinge (j+2)))
  exact hlin.add hs

lemma eval_monotone (v : ℕ → ℝ) (N : ℕ) (hv1 : 0 ≤ v 1)
    (hv : ∀ j<N, 0 ≤ v (j+2)) : Monotone (eval v N) := by
  intro x y hxy
  apply add_le_add
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right hxy _) hv1)
  · apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (monotone_hinge _ hxy) (hv j (Finset.mem_range.mp hj))

lemma eval_nonneg (v : ℕ → ℝ) (N : ℕ) (hv0 : 0 ≤ v 0) (hv1 : 0 ≤ v 1)
    (hv : ∀ j<N, 0 ≤ v (j+2)) (x : ℝ) (hx : 1 ≤ x) : 0 ≤ eval v N x := by
  exact add_nonneg (add_nonneg hv0 (mul_nonneg hv1 (sub_nonneg.mpr hx)))
    (Finset.sum_nonneg (fun j hj => mul_nonneg (hv j (Finset.mem_range.mp hj)) (le_max_left _ _)))

lemma eval_add (v w : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    eval (fun j => v j+w j) N x = eval v N x+eval w N x := by
  simp only [eval, add_mul, Finset.sum_add_distrib]
  ring

lemma eval_affine_tail (v : ℕ → ℝ) (N : ℕ) (x : ℝ) (hx : (N:ℝ)+1 ≤ x) :
    eval v N x = eval v N ((N:ℝ)+1)+slope v N*(x-((N:ℝ)+1)) := by
  have he (j : ℕ) (hj : j<N) :
      hinge (j+2) x = hinge (j+2) ((N:ℝ)+1)+(x-((N:ℝ)+1)) := by
    have hj' : (j:ℝ)+2 ≤ (N:ℝ)+1 := by exact_mod_cast (show j+2 ≤ N+1 by omega)
    rw [hinge, hinge, max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  dsimp only [eval, slope]
  calc
    _ = v 0+v 1*(x-1)+∑ j ∈ Finset.range N,
        v (j+2)*(hinge (j+2) ((N:ℝ)+1)+(x-((N:ℝ)+1))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [he j (Finset.mem_range.mp hj)]
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

lemma hinge_on_segment (t A B a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b=1) (hcell : t ≤ A ∧ t ≤ B ∨ A ≤ t ∧ B ≤ t) :
    hinge t (a*A+b*B) = a*hinge t A+b*hinge t B := by
  rcases hcell with h | h
  · have hh : t ≤ a*A+b*B := by
      have h₁ := mul_le_mul_of_nonneg_left h.1 ha
      have h₂ := mul_le_mul_of_nonneg_left h.2 hb
      nlinarith [show (a+b)*t=t by rw [hab, one_mul]]
    simp only [hinge, max_eq_right (sub_nonneg.mpr h.1), max_eq_right (sub_nonneg.mpr h.2),
      max_eq_right (sub_nonneg.mpr hh)]
    nlinarith [show (a+b)*t=t by rw [hab, one_mul]]
  · have hh : a*A+b*B ≤ t := by
      have h₁ := mul_le_mul_of_nonneg_left h.1 ha
      have h₂ := mul_le_mul_of_nonneg_left h.2 hb
      nlinarith [show (a+b)*t=t by rw [hab, one_mul]]
    simp only [hinge, max_eq_left (sub_nonpos.mpr h.1), max_eq_left (sub_nonpos.mpr h.2),
      max_eq_left (sub_nonpos.mpr hh), mul_zero, add_zero]

/-- Zero hinge coefficients do not require a breakpoint in the cell list. -/
lemma eval_on_segment (v : ℕ → ℝ) (N : ℕ) (A B a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hcell : ∀ j<N, v (j+2)=0 ∨ ((j:ℝ)+2 ≤ A ∧ (j:ℝ)+2 ≤ B) ∨
      (A ≤ (j:ℝ)+2 ∧ B ≤ (j:ℝ)+2)) :
    eval v N (a*A+b*B) = a*eval v N A+b*eval v N B := by
  have he (j : ℕ) (hj : j<N) :
      v (j+2)*hinge (j+2) (a*A+b*B) = a*(v (j+2)*hinge (j+2) A)+b*(v (j+2)*hinge (j+2) B) := by
    rcases hcell j hj with hz | hc
    · simp [hz]
    · rw [hinge_on_segment _ A B a b ha hb hab hc]
      ring
  have hsum := Finset.sum_congr rfl (fun j hj => he j (Finset.mem_range.mp hj))
  dsimp only [eval]
  rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h₀ : (a+b)*v 0=v 0 := by rw [hab, one_mul]
  have h₁ : (a+b)*v 1=v 1 := by rw [hab, one_mul]
  nlinarith

lemma eval_on_unit_interval (v : ℕ → ℝ) (N j : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    eval v N (a*(j+1)+b*(j+2)) = a*eval v N (j+1)+b*eval v N (j+2) := by
  apply eval_on_segment v N _ _ a b ha hb hab
  intro i hi
  by_cases hij : i<j
  · right; left
    constructor
    · exact_mod_cast (by omega : i+2 ≤ j+1)
    · exact_mod_cast (by omega : i+2 ≤ j+2)
  · right; right
    constructor
    · exact_mod_cast (by omega : j+1 ≤ i+2)
    · exact_mod_cast (by omega : j+2 ≤ i+2)

/-- Endpoint bounds extend across an affine majorant cell. -/
lemma convex_below_affine_cell (g v : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (A B a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hv : v (a*A+b*B)=a*v A+b*v B) (hA : g A ≤ v A) (hB : g B ≤ v B) :
    g (a*A+b*B) ≤ v (a*A+b*B) := by
  rw [hv]
  have hh := hg.2 (Set.mem_univ A) (Set.mem_univ B) ha hb hab
  simp only [smul_eq_mul] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hA ha) (mul_le_mul_of_nonneg_left hB hb))

lemma interval_combination (A B x : ℝ) (hx : x ∈ Set.Icc A B) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a+b=1 ∧ x=a*A+b*B := by
  by_cases he : A=B
  · have hx' : x=A := by obtain ⟨h₁,h₂⟩ := hx; linarith
    exact ⟨1,0,by norm_num,by norm_num,by norm_num,by simp [hx']⟩
  · have hp : 0 < B-A := by obtain ⟨h₁,h₂⟩ := hx; rcases lt_or_gt_of_ne he with h | h <;> linarith
    refine ⟨(B-x)/(B-A),(x-A)/(B-A),div_nonneg (sub_nonneg.mpr hx.2) hp.le,
      div_nonneg (sub_nonneg.mpr hx.1) hp.le, ?_, ?_⟩ <;> field_simp <;> ring

lemma exists_unit_interval (N : ℕ) (hN : 0<N) (x : ℝ) (hx : 1 ≤ x)
    (hxN : x ≤ (N:ℝ)+1) : ∃ j<N, x ∈ Set.Icc ((j:ℝ)+1) ((j:ℝ)+2) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hN0 : N=0
    · subst N
      exact ⟨0,by omega,by simpa using hx,by norm_num at hxN ⊢; exact hxN⟩
    · by_cases hx' : x ≤ (N:ℝ)+1
      · obtain ⟨j,hj,hxj⟩ := ih (by omega) hx'
        exact ⟨j,by omega,hxj⟩
      · refine ⟨N,by omega,by linarith,?_⟩
        simp only [Nat.cast_add, Nat.cast_one] at hxN
        linarith

#print axioms eval_convex
#print axioms eval_affine_tail
#print axioms eval_on_segment
#print axioms exists_unit_interval
end Erdos7FiniteHingeFunctions
