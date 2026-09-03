import Submission.PairedPresentGeometry
import Submission.PairedSelectionBridge

/-! Exact finite initial moments of actual weighted paired ternary counts.
These are initial sampling bounds, not a complete covering obstruction. -/
namespace Erdos7PairedWeightedMoments
open scoped BigOperators
open Erdos7PresentCylinderArithmetic Erdos7IndependentPureLifts
open Erdos7PairedTernaryRoot Erdos7PairedPresentGeometry Erdos7PairedSelectionBridge
set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable def positiveSquare (t : ℝ) : ℝ := (max 0 t)^2

lemma positiveSquare_eq (t : ℝ) (ht : 0 ≤ t) : positiveSquare t=t^2 := by
  simp [positiveSquare,max_eq_right ht]

lemma positiveSquare_convex : ConvexOn ℝ Set.univ positiveSquare := by
  have h : ConvexOn ℝ Set.univ (fun t : ℝ => max 0 t) :=
    (convexOn_const 0 convex_univ).sup (convexOn_id convex_univ)
  exact h.pow (fun t ht => le_max_left _ _) 2

lemma positiveSquare_mono : Monotone positiveSquare := by
  intro x y hxy
  have h : max (0:ℝ) x ≤ max 0 y := max_le_max le_rfl hxy
  dsimp only [positiveSquare]
  nlinarith [le_max_left (0:ℝ) x,le_max_left (0:ℝ) y]

lemma law_congr_ge_one (D : ℕ) (f g : ℝ → ℝ)
    (h : ∀ t, 1 ≤ t → f t=g t) : law D f=law D g := by
  unfold law
  rw [h (3/2) (by norm_num)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h _ (by have := Nat.cast_nonneg (α := ℝ) j; linarith)]

lemma both_positiveSquare_law (D : ℕ) :
    law D (bothCost positiveSquare)=11/2-((D:ℝ)+3)*(1/3:ℝ)^D := by
  calc
    _ = law D (bothCost (fun t => t^2)) := by
      apply law_congr_ge_one
      intro t ht
      simp only [bothCost,positiveSquare_eq _ (by linarith : 0 ≤ 2*t-1),
        positiveSquare_eq 1 (by norm_num)]
    _ = _ := both_law_second_moment D

noncomputable def measure (D : ℕ) (a : ℕ → ℤ)
    (z : ZMod (3^(D+1)) × ZMod (3^(D+1))) : ℝ :=
  uniformOn (branchGood 3 (D+1) a 1 ×ˢ branchGood 3 (D+1) a 2) z

lemma measure_nonneg (D : ℕ) (a : ℕ → ℤ)
    (z : ZMod (3^(D+1)) × ZMod (3^(D+1))) : 0 ≤ measure D a z :=
  uniformOn_nonneg _ _

noncomputable def branchCount (D : ℕ) (c : ℕ → ℤ) (x : ZMod (3^(D+1))) : ℝ :=
  count (fun e => cylinder 3 (D+1) e (c e)) D x

lemma branchCount_ge_one (D : ℕ) (c : ℕ → ℤ) (x : ZMod (3^(D+1))) :
    1 ≤ branchCount D c x := count_ge_one _ _ _

lemma mean_sum (D : ℕ) (a c : ℕ → ℤ) :
    (∑ z, measure D a z*(branchCount D c z.1+branchCount D c z.2)) ≤
      4-(1/3:ℝ)^D := by
  have h := arithmetic_pair_average_comparison D a c
    (fun t => t) (convexOn_id convex_univ) monotone_id
  rw [law_mean] at h
  have he : (∑ z, measure D a z*(branchCount D c z.1+branchCount D c z.2))/2 =
      ∑ z, measure D a z*pairAverage (fun e => cylinder 3 (D+1) e (c e)) D z := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z hz
    rcases z with ⟨x,y⟩
    rw [pairAverage_eq_count]
    dsimp only [branchCount]
    ring
  change (∑ z, measure D a z*pairAverage (fun e => cylinder 3 (D+1) e (c e)) D z) ≤ _ at h
  rw [←he] at h
  linarith

lemma second_sum (D : ℕ) (a c : ℕ → ℤ) :
    (∑ z, measure D a z*((branchCount D c z.1)^2+(branchCount D c z.2)^2)) ≤
      11-(2*(D:ℝ)+6)*(1/3:ℝ)^D := by
  have h := arithmetic_pair_average_comparison D a c (bothCost positiveSquare)
    (bothCost_convex _ positiveSquare_convex) (bothCost_mono _ positiveSquare_mono)
  rw [both_positiveSquare_law] at h
  have hp (z : ZMod (3^(D+1)) × ZMod (3^(D+1))) :
      (branchCount D c z.1)^2+(branchCount D c z.2)^2 ≤
        2*bothCost positiveSquare (pairAverage (fun e => cylinder 3 (D+1) e (c e)) D z) := by
    have hb := both_bound positiveSquare positiveSquare_convex
      (branchCount D c z.1) (branchCount D c z.2)
      (branchCount_ge_one D c z.1) (branchCount_ge_one D c z.2)
    rw [positiveSquare_eq _ (by linarith [branchCount_ge_one D c z.1]),
      positiveSquare_eq _ (by linarith [branchCount_ge_one D c z.2])] at hb
    rcases z with ⟨x,y⟩
    rw [pairAverage_eq_count]
    change _ ≤ 2*bothCost positiveSquare ((branchCount D c x+branchCount D c y)/2)
    linarith
  have hs := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hp z) (measure_nonneg D a z))
  have he : (∑ z, measure D a z*(2*bothCost positiveSquare
      (pairAverage (fun e => cylinder 3 (D+1) e (c e)) D z))) =
      2*∑ z, measure D a z*bothCost positiveSquare
        (pairAverage (fun e => cylinder 3 (D+1) e (c e)) D z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  change (∑ z, measure D a z*bothCost positiveSquare
    (pairAverage (fun e => cylinder 3 (D+1) e (c e)) D z)) ≤ _ at h
  change (∑ z, measure D a z*((branchCount D c z.1)^2+(branchCount D c z.2)^2)) ≤
    (∑ z, measure D a z*(2*bothCost positiveSquare
      (pairAverage (fun e => cylinder 3 (D+1) e (c e)) D z))) at hs
  rw [he] at hs
  linarith

lemma square_weighted {I : Type*} [Fintype I]
    (w f : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1) :
    (∑ i, w i*f i)^2 ≤ ∑ i, w i*(f i)^2 := by
  have hc : ConvexOn ℝ Set.univ (fun t : ℝ => t^2) := (by decide : Even (2:ℕ)).convexOn_pow
  simpa only [smul_eq_mul] using hc.map_sum_le (fun i hi => hw i) hm (fun i hi => Set.mem_univ (f i))

noncomputable def weightedCount {I : Type*} [Fintype I]
    (w : I → ℝ) (D : ℕ) (c : I → ℕ → ℤ) (x : ZMod (3^(D+1))) : ℝ :=
  ∑ i, w i*branchCount D (c i) x

lemma weighted_mean_sum {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (D : ℕ) (a : ℕ → ℤ) (c : I → ℕ → ℤ) :
    (∑ z, measure D a z*(weightedCount w D c z.1+weightedCount w D c z.2)) ≤
      4-(1/3:ℝ)^D := by
  calc
    _ = ∑ i, w i*(∑ z, measure D a z*(branchCount D (c i) z.1+branchCount D (c i) z.2)) := by
      simp only [weightedCount, ← Finset.sum_add_distrib, ← mul_add, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ ≤ ∑ i, w i*(4-(1/3:ℝ)^D) := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (mean_sum D a (c i)) (hw i))
    _ = _ := by rw [← Finset.sum_mul,hm,one_mul]

lemma weighted_second_sum {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (D : ℕ) (a : ℕ → ℤ) (c : I → ℕ → ℤ) :
    (∑ z, measure D a z*((weightedCount w D c z.1)^2+(weightedCount w D c z.2)^2)) ≤
      11-(2*(D:ℝ)+6)*(1/3:ℝ)^D := by
  have hp (z : ZMod (3^(D+1)) × ZMod (3^(D+1))) :
      (weightedCount w D c z.1)^2+(weightedCount w D c z.2)^2 ≤
        ∑ i, w i*((branchCount D (c i) z.1)^2+(branchCount D (c i) z.2)^2) := by
    have h₁ := square_weighted w (fun i => branchCount D (c i) z.1) hw hm
    have h₂ := square_weighted w (fun i => branchCount D (c i) z.2) hw hm
    simp only [mul_add,Finset.sum_add_distrib]
    exact add_le_add h₁ h₂
  calc
    _ ≤ ∑ z, measure D a z*(∑ i, w i*((branchCount D (c i) z.1)^2+(branchCount D (c i) z.2)^2)) :=
      Finset.sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hp z) (measure_nonneg D a z))
    _ = ∑ i, w i*(∑ z, measure D a z*((branchCount D (c i) z.1)^2+(branchCount D (c i) z.2)^2)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ ≤ ∑ i, w i*(11-(2*(D:ℝ)+6)*(1/3:ℝ)^D) := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (second_sum D a (c i)) (hw i))
    _ = _ := by rw [← Finset.sum_mul,hm,one_mul]

lemma uniform_product {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (x : X) (y : Y) :
    uniformOn (S ×ˢ T) (x,y)=uniformOn S x*uniformOn T y := by
  simp only [uniformOn,Finset.mem_product,Finset.card_product,Nat.cast_mul]
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ T <;>
    simp [hx,hy,div_eq_mul_inv,mul_inv_rev,mul_comm]

lemma independent_product {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (S : Finset X) (T : Finset Y)
    (f : X → ℝ) (g : Y → ℝ) :
    (∑ z, uniformOn (S ×ˢ T) z*(f z.1*g z.2))=
      (∑ x, uniformOn S x*f x)*(∑ y, uniformOn T y*g y) := by
  rw [Fintype.sum_prod_type,Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [uniform_product]
  ring

lemma independent_sum {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (S : Finset X) (T : Finset Y)
    (hS : S.Nonempty) (hT : T.Nonempty) (f : X → ℝ) (g : Y → ℝ) :
    (∑ z, uniformOn (S ×ˢ T) z*(f z.1+g z.2))=
      (∑ x, uniformOn S x*f x)+(∑ y, uniformOn T y*g y) := by
  have h₁ := independent_product S T f (fun _ => 1)
  have h₂ := independent_product S T (fun _ => 1) g
  simp only [mul_one,uniformOn_mass T hT] at h₁
  simp only [one_mul,mul_one,uniformOn_mass S hS] at h₂
  rw [show (∑ z, uniformOn (S ×ˢ T) z*(f z.1+g z.2))=
    (∑ z, uniformOn (S ×ˢ T) z*f z.1)+(∑ z, uniformOn (S ×ˢ T) z*g z.2) by
      simp only [mul_add,Finset.sum_add_distrib]]
  rw [h₁,h₂]

lemma weightedCount_nonneg {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (D : ℕ) (c : I → ℕ → ℤ)
    (x : ZMod (3^(D+1))) : 0 ≤ weightedCount w D c x := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i)
    (by linarith [branchCount_ge_one D (c i) x]))

lemma nonneg_mul_bound (u v M : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u+v ≤ M) :
    u*v ≤ (M/2)^2 := by
  have hp := mul_nonneg (sub_nonneg.mpr h) (by linarith : 0 ≤ M+u+v)
  nlinarith [sq_nonneg (u-v)]

/-- Independence is used only in the INITIAL uniform product sampling law.
No such factorization is asserted after retention or branch selection. -/
theorem weighted_mixed_moment {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (D : ℕ) (a : ℕ → ℤ) (c : I → ℕ → ℤ) :
    (∑ z, measure D a z*(weightedCount w D c z.1*weightedCount w D c z.2)) ≤
      (2-(1/3:ℝ)^D/2)^2 := by
  let S := branchGood 3 (D+1) a 1
  let T := branchGood 3 (D+1) a 2
  have hS : S.Nonempty := branchGood_nonempty 3 (D+1) (by omega) (by omega) a 1
  have hT : T.Nonempty := branchGood_nonempty 3 (D+1) (by omega) (by omega) a 2
  have h := weighted_mean_sum w hw hm D a c
  change (∑ z, uniformOn (S ×ˢ T) z*(weightedCount w D c z.1+weightedCount w D c z.2)) ≤ _ at h
  rw [independent_sum S T hS hT] at h
  have hL : 0 ≤ ∑ x, uniformOn S x*weightedCount w D c x :=
    Finset.sum_nonneg (fun x hx => mul_nonneg (uniformOn_nonneg S x) (weightedCount_nonneg w hw D c x))
  have hR : 0 ≤ ∑ y, uniformOn T y*weightedCount w D c y :=
    Finset.sum_nonneg (fun y hy => mul_nonneg (uniformOn_nonneg T y) (weightedCount_nonneg w hw D c y))
  change (∑ z, uniformOn (S ×ˢ T) z*(weightedCount w D c z.1*weightedCount w D c z.2)) ≤ _
  rw [independent_product]
  have hb := nonneg_mul_bound _ _ _ hL hR h
  convert hb using 1; ring

lemma weighted_moments_strict {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (D : ℕ) (a : ℕ → ℤ) (c : I → ℕ → ℤ) :
    (∑ z, measure D a z*(weightedCount w D c z.1+weightedCount w D c z.2)) < 4 ∧
    (∑ z, measure D a z*((weightedCount w D c z.1)^2+(weightedCount w D c z.2)^2)) < 11 ∧
    (∑ z, measure D a z*(weightedCount w D c z.1*weightedCount w D c z.2)) < 4 := by
  have hu : 0 < (1/3:ℝ)^D := by positivity
  have hu1 : (1/3:ℝ)^D ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨?_,?_,?_⟩
  · have h := weighted_mean_sum w hw hm D a c
    linarith
  · have h := weighted_second_sum w hw hm D a c
    have hd : 0 ≤ (D:ℝ) := Nat.cast_nonneg D
    nlinarith
  · have h := weighted_mixed_moment w hw hm D a c
    nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]

lemma measure_mass (D : ℕ) (a : ℕ → ℤ) : (∑ z, measure D a z)=1 := by
  apply uniformOn_mass
  exact (branchGood_nonempty 3 (D+1) (by omega) (by omega) a 1).product
    (branchGood_nonempty 3 (D+1) (by omega) (by omega) a 2)

lemma quadratic_integral {X : Type*} [Fintype X]
    (μ L R : X → ℝ) (hm : (∑ x, μ x)=1) (A B C T : ℝ) :
    (∑ x, μ x*(A+B*(L x+R x)+C*((L x)^2+(R x)^2)+T*(L x*R x))) =
      A+B*(∑ x, μ x*(L x+R x))+C*(∑ x, μ x*((L x)^2+(R x)^2))+
        T*(∑ x, μ x*(L x*R x)) := by
  calc
    _ = ∑ x, (A*μ x+B*(μ x*(L x+R x))+C*(μ x*((L x)^2+(R x)^2))+
        T*(μ x*(L x*R x))) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,hm,mul_one]

/-- Exact initial bound for the nonnegative quadratic current budget used in
one diagnostic. It supplies no backward or terminal budget by itself. -/
theorem quadratic_budget_bound {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (D : ℕ) (a : ℕ → ℤ) (c : I → ℕ → ℤ)
    (A B C T : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hT : 0 ≤ T) :
    let L := fun z : ZMod (3^(D+1)) × ZMod (3^(D+1)) => weightedCount w D c z.1
    let R := fun z : ZMod (3^(D+1)) × ZMod (3^(D+1)) => weightedCount w D c z.2
    (∑ z, measure D a z*(A+B*(L z+R z)+C*((L z)^2+(R z)^2)+T*(L z*R z))) ≤
      A+B*(4-(1/3:ℝ)^D)+C*(11-(2*(D:ℝ)+6)*(1/3:ℝ)^D)+T*(2-(1/3:ℝ)^D/2)^2 := by
  dsimp only
  rw [quadratic_integral _ _ _ (measure_mass D a)]
  have h₁ := mul_le_mul_of_nonneg_left (weighted_mean_sum w hw hm D a c) hB
  have h₂ := mul_le_mul_of_nonneg_left (weighted_second_sum w hw hm D a c) hC
  have h₃ := mul_le_mul_of_nonneg_left (weighted_mixed_moment w hw hm D a c) hT
  linarith

lemma quadratic_budget_strict {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : (∑ i, w i)=1)
    (D : ℕ) (a : ℕ → ℤ) (c : I → ℕ → ℤ)
    (A B C T : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hn : 0 < B ∨ 0 < C ∨ 0 < T) :
    let L := fun z : ZMod (3^(D+1)) × ZMod (3^(D+1)) => weightedCount w D c z.1
    let R := fun z : ZMod (3^(D+1)) × ZMod (3^(D+1)) => weightedCount w D c z.2
    (∑ z, measure D a z*(A+B*(L z+R z)+C*((L z)^2+(R z)^2)+T*(L z*R z))) <
      A+4*B+11*C+4*T := by
  dsimp only
  rw [quadratic_integral _ _ _ (measure_mass D a)]
  obtain ⟨h₁,h₂,h₃⟩ := weighted_moments_strict w hw hm D a c
  have hb := mul_le_mul_of_nonneg_left h₁.le hB
  have hc := mul_le_mul_of_nonneg_left h₂.le hC
  have ht := mul_le_mul_of_nonneg_left h₃.le hT
  rcases hn with hn | hn | hn
  · have hs := mul_lt_mul_of_pos_left h₁ hn
    linarith
  · have hs := mul_lt_mul_of_pos_left h₂ hn
    linarith
  · have hs := mul_lt_mul_of_pos_left h₃ hn
    linarith

#print axioms mean_sum
#print axioms second_sum
#print axioms weighted_mean_sum
#print axioms weighted_second_sum
#print axioms weighted_mixed_moment
#print axioms weighted_moments_strict
#print axioms quadratic_budget_bound
#print axioms quadratic_budget_strict
end Erdos7PairedWeightedMoments
