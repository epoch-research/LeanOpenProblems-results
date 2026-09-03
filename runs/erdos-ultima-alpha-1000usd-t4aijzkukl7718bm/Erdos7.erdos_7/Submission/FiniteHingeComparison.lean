import FormalConjecturesUtil

/-! Finite hinge certificates for increasing-convex comparison of bounded
integer counts. These auxiliary results do not settle the odd covering problem. -/
namespace Erdos7FiniteHingeComparison
open scoped BigOperators
set_option maxHeartbeats 1500000

noncomputable def curvature (f : ℕ → ℝ) (t : ℕ) : ℝ :=
  f (t+2)-2*f (t+1)+f t

lemma sum_curvature (f : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.range n, curvature f t) = f (n+1)-f n-(f 1-f 0) := by
  let d (t : ℕ) := f (t+1)-f t
  have he (t : ℕ) : curvature f t = d (t+1)-d t := by
    dsimp [curvature, d]
    ring
  simp_rw [he]
  rw [Finset.sum_range_sub]

lemma nat_hinge_step (n t : ℕ) :
    ((n+1-(t+1) : ℕ) : ℝ) = ((n-(t+1) : ℕ) : ℝ) + if t<n then 1 else 0 := by
  by_cases ht : t<n
  · rw [if_pos ht]
    have he : n+1-(t+1) = (n-(t+1))+1 := by omega
    rw [he, Nat.cast_add, Nat.cast_one]
  · rw [if_neg ht]
    have h₁ : n+1-(t+1)=0 := by omega
    have h₂ : n-(t+1)=0 := by omega
    simp [h₁, h₂]

lemma truncated_sum (g : ℕ → ℝ) (N n : ℕ) (hn : n ≤ N) :
    (∑ t ∈ Finset.range N, if t<n then g t else 0) = ∑ t ∈ Finset.range n, g t := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Exact finite expansion into a constant, the first difference, and integer
hinges. No convexity assumption is needed for this identity. -/
theorem hinge_expansion (f : ℕ → ℝ) (N n : ℕ) (hn : n ≤ N) :
    f n = f 0+(f 1-f 0)*(n : ℝ) +
      ∑ t ∈ Finset.range N, curvature f t*((n-(t+1) : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnN : n ≤ N := by omega
    have he := ih hnN
    have hsum :
        (∑ t ∈ Finset.range N, curvature f t*((n+1-(t+1) : ℕ) : ℝ)) =
        (∑ t ∈ Finset.range N, curvature f t*((n-(t+1) : ℕ) : ℝ)) +
          ∑ t ∈ Finset.range n, curvature f t := by
      simp_rw [nat_hinge_step, mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        _ = ∑ t ∈ Finset.range N, if t<n then curvature f t else 0 := by
          apply Finset.sum_congr rfl
          intro t _
          split_ifs <;> simp
        _ = _ := truncated_sum _ N n hnN
    rw [hsum, sum_curvature, Nat.cast_add, Nat.cast_one]
    linarith

/-- A signed test is bounded using its nonnegative first and second
 differences. The total mass need not be one. -/
theorem weighted_hinge_certificate {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (Z : Ω → ℕ) (N : ℕ) (f : ℕ → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hZ : ∀ x, Z x ≤ N)
    (hf : 0 ≤ f 1-f 0) (hcurv : ∀ t<N, 0 ≤ curvature f t)
    (m M : ℝ) (H : ℕ → ℝ)
    (hmass : (∑ x, μ x)=m) (hmean : (∑ x, μ x*(Z x : ℝ)) ≤ M)
    (hhinge : ∀ t<N, (∑ x, μ x*((Z x-(t+1) : ℕ) : ℝ)) ≤ H t) :
    (∑ x, μ x*f (Z x)) ≤ m*f 0+(f 1-f 0)*M+
      ∑ t ∈ Finset.range N, curvature f t*H t := by
  have he : (∑ x, μ x*f (Z x)) = m*f 0+(f 1-f 0)*(∑ x, μ x*(Z x : ℝ))+
      ∑ t ∈ Finset.range N, curvature f t*(∑ x, μ x*((Z x-(t+1) : ℕ) : ℝ)) := by
    calc
      _ = ∑ x, μ x*(f 0+(f 1-f 0)*(Z x : ℝ)+
          ∑ t ∈ Finset.range N, curvature f t*((Z x-(t+1) : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← hinge_expansion f N (Z x) (hZ x)]
      _ = _ := by
        simp_rw [mul_add, Finset.mul_sum]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hmass]
        congr 1
        · congr 1
          apply Finset.sum_congr rfl
          intro x _
          ring
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro x _
          ring
  rw [he]
  exact add_le_add
    (add_le_add_right (mul_le_mul_of_nonneg_left hmean hf) _)
    (Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left
      (hhinge t (Finset.mem_range.mp ht)) (hcurv t (Finset.mem_range.mp ht))))

/-- Equal masses and upper bounds for the mean and all integer hinges imply
comparison for every increasing discrete-convex test. -/
theorem finite_hinge_comparison {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : Ω → ℝ) (ν : Ξ → ℝ) (X : Ω → ℕ) (Y : Ξ → ℕ) (N : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hX : ∀ x, X x ≤ N) (hY : ∀ y, Y y ≤ N)
    (hmass : (∑ x, μ x) = ∑ y, ν y)
    (hmean : (∑ x, μ x*(X x : ℝ)) ≤ ∑ y, ν y*(Y y : ℝ))
    (hhinge : ∀ t<N, (∑ x, μ x*((X x-(t+1) : ℕ) : ℝ)) ≤
      ∑ y, ν y*((Y y-(t+1) : ℕ) : ℝ))
    (f : ℕ → ℝ) (hf : 0 ≤ f 1-f 0) (hcurv : ∀ t<N, 0 ≤ curvature f t) :
    (∑ x, μ x*f (X x)) ≤ ∑ y, ν y*f (Y y) := by
  have hc := weighted_hinge_certificate μ X N f hμ hX hf hcurv
    (∑ y, ν y) (∑ y, ν y*(Y y : ℝ))
    (fun t => ∑ y, ν y*((Y y-(t+1) : ℕ) : ℝ)) hmass hmean hhinge
  have he : (∑ y, ν y*f (Y y)) = (∑ y, ν y)*f 0+
      (f 1-f 0)*(∑ y, ν y*(Y y : ℝ)) +
      ∑ t ∈ Finset.range N, curvature f t*(∑ y, ν y*((Y y-(t+1) : ℕ) : ℝ)) := by
    simp_rw [hinge_expansion f N _ (hY _), mul_add, Finset.mul_sum]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro y _
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro y _
      ring
  exact hc.trans_eq he.symm

lemma convex_nat_curvature (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (b : ℝ) (t : ℕ) : 0 ≤ curvature (fun n => φ (b+(n : ℝ))) t := by
  have hh := hφ.2 (Set.mem_univ (b+(t : ℝ))) (Set.mem_univ (b+(t : ℝ)+2))
    (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : 0 ≤ (1/2 : ℝ))
    (by norm_num : (1/2 : ℝ)+(1/2 : ℝ)=1)
  simp only [smul_eq_mul] at hh
  have he : (1/2 : ℝ)*(b+(t : ℝ))+(1/2)*(b+(t : ℝ)+2) = b+(t : ℝ)+1 := by ring
  rw [he] at hh
  simp only [curvature, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  simp only [← add_assoc]
  linarith

/-- Real convex monotone tests are covered by the finite integer-hinge
 criterion. The shift b permits counts with a fixed nonzero baseline. -/
theorem convex_monotone_comparison {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : Ω → ℝ) (ν : Ξ → ℝ) (X : Ω → ℕ) (Y : Ξ → ℕ) (N : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hX : ∀ x, X x ≤ N) (hY : ∀ y, Y y ≤ N)
    (hmass : (∑ x, μ x) = ∑ y, ν y)
    (hmean : (∑ x, μ x*(X x : ℝ)) ≤ ∑ y, ν y*(Y y : ℝ))
    (hhinge : ∀ t<N, (∑ x, μ x*((X x-(t+1) : ℕ) : ℝ)) ≤
      ∑ y, ν y*((Y y-(t+1) : ℕ) : ℝ))
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) (b : ℝ) :
    (∑ x, μ x*φ (b+(X x : ℝ))) ≤ ∑ y, ν y*φ (b+(Y y : ℝ)) := by
  apply finite_hinge_comparison μ ν X Y N hμ hν hX hY hmass hmean hhinge
    (fun n => φ (b+(n : ℝ)))
  · simp only [Nat.cast_zero, Nat.cast_one, add_zero]
    exact sub_nonneg.mpr (hmφ (by linarith))
  · intro t _
    exact convex_nat_curvature φ hφ b t

/-- A common convex-test bound is preserved by averaging different families.
The families need not have the same distribution or the same maximizing point. -/
theorem family_mixture_bound {Ω ι : Type*} [Fintype Ω]
    (S : Finset ι) (w : ι → ℝ) (μ : Ω → ℝ) (X : ι → Ω → ℝ)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hw1 : (∑ i ∈ S, w i)=1)
    (hμ : ∀ x, 0 ≤ μ x) (B : ℝ)
    (hB : ∀ i ∈ S, (∑ x, μ x*φ (X i x)) ≤ B) :
    (∑ x, μ x*φ (∑ i ∈ S, w i*X i x)) ≤ B := by
  calc
    _ ≤ ∑ x, μ x*(∑ i ∈ S, w i*φ (X i x)) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hμ x)
      simpa only [smul_eq_mul] using hφ.map_sum_le hw hw1
        (fun i hi => Set.mem_univ (X i x))
    _ = ∑ i ∈ S, w i*(∑ x, μ x*φ (X i x)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ i ∈ S, w i*B := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hB i hi) (hw i hi))
    _ = B := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Integer hinge certificates also control convex tests of noninteger
normalized counts obtained as averages of complete integer-count families. -/
theorem averaged_integer_comparison {Ω Ξ ι : Type*} [Fintype Ω] [Fintype Ξ]
    (S : Finset ι) (w : ι → ℝ) (μ : Ω → ℝ) (ν : Ξ → ℝ)
    (X : ι → Ω → ℕ) (Y : Ξ → ℕ) (N : ℕ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hw1 : (∑ i ∈ S, w i)=1)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hX : ∀ i ∈ S, ∀ x, X i x ≤ N) (hY : ∀ y, Y y ≤ N)
    (hmass : (∑ x, μ x) = ∑ y, ν y)
    (hmean : ∀ i ∈ S, (∑ x, μ x*(X i x : ℝ)) ≤ ∑ y, ν y*(Y y : ℝ))
    (hhinge : ∀ i ∈ S, ∀ t<N, (∑ x, μ x*((X i x-(t+1) : ℕ) : ℝ)) ≤
      ∑ y, ν y*((Y y-(t+1) : ℕ) : ℝ))
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) (b : ℝ) :
    (∑ x, μ x*φ (b+∑ i ∈ S, w i*(X i x : ℝ))) ≤
      ∑ y, ν y*φ (b+(Y y : ℝ)) := by
  have he (x : Ω) : (∑ i ∈ S, w i*(b+(X i x : ℝ))) =
      b+∑ i ∈ S, w i*(X i x : ℝ) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
  have hh := family_mixture_bound S w μ (fun i x => b+(X i x : ℝ)) φ hφ hw hw1 hμ
    (∑ y, ν y*φ (b+(Y y : ℝ))) (fun i hi =>
      convex_monotone_comparison μ ν (X i) Y N hμ hν (hX i hi) hY
        hmass (hmean i hi) (hhinge i hi) φ hφ hmφ b)
  simpa only [he] using hh

#print axioms averaged_integer_comparison
#print axioms convex_monotone_comparison
#print axioms finite_hinge_comparison
end Erdos7FiniteHingeComparison
