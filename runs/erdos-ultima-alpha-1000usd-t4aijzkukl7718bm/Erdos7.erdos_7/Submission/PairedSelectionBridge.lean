import Submission.StateSharedCompression
import Submission.PairedTernaryRoot

/-! A conservative, actual pair-to-single selection bridge. Selection uses
ONE branch for the whole family of costs. This is not a covering obstruction. -/
namespace Erdos7PairedSelectionBridge
open scoped BigOperators
open Erdos7RealChain Erdos7StateSharedCompression
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- For a fixed sum and a lower endpoint, convex cost is largest at an
endpoint pair. No upper bound by the convex cost of the average is asserted. -/
lemma endpoint_pair (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (a x y : ℝ) (hx : a ≤ x) (hy : a ≤ y) :
    φ x + φ y ≤ φ a + φ (x+y-a) := by
  have h := convex_increasingIncrements φ hφ a x (y-a) hx (sub_nonneg.mpr hy)
  rw [show a+(y-a)=y by ring, show x+(y-a)=x+y-a by ring] at h
  linarith

noncomputable def singleCost (φ : ℝ → ℝ) (t : ℝ) : ℝ := φ (2*t-1)
noncomputable def bothCost (φ : ℝ → ℝ) (t : ℝ) : ℝ := (φ (2*t-1)+φ 1)/2

lemma singleCost_mono (φ : ℝ → ℝ) (hφ : Monotone φ) : Monotone (singleCost φ) := by
  intro x y hxy
  exact hφ (by linarith : 2*x-1 ≤ 2*y-1)

lemma bothCost_mono (φ : ℝ → ℝ) (hφ : Monotone φ) : Monotone (bothCost φ) := by
  intro x y hxy
  have h := singleCost_mono φ hφ hxy
  dsimp only [singleCost, bothCost] at h ⊢
  linarith

lemma singleCost_convex (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    ConvexOn ℝ Set.univ (singleCost φ) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hφ.2 (Set.mem_univ (2*x-1)) (Set.mem_univ (2*y-1)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  dsimp only [singleCost]
  have he : a*(2*x-1)+b*(2*y-1)=2*(a*x+b*y)-1 := by nlinarith
  rw [he] at h
  exact h

lemma bothCost_convex (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    ConvexOn ℝ Set.univ (bothCost φ) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := (singleCost_convex φ hφ).2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  dsimp only [singleCost, bothCost] at h ⊢
  nlinarith [show (a+b)*φ 1=φ 1 by rw [hab]; ring]

lemma ordered_increments (φ : ℝ → ℝ) (hφ : Monotone φ) :
    Monotone (fun t => singleCost φ t-bothCost φ t) := by
  intro x y hxy
  have h := singleCost_mono φ hφ hxy
  dsimp only [singleCost,bothCost] at h ⊢
  linarith

lemma single_bound (φ : ℝ → ℝ) (hφ : Monotone φ)
    (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    φ x ≤ singleCost φ ((x+y)/2) ∧ φ y ≤ singleCost φ ((x+y)/2) := by
  constructor <;> apply hφ <;> linarith

lemma both_bound (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (φ x+φ y)/2 ≤ bothCost φ ((x+y)/2) := by
  have h := endpoint_pair φ hφ 1 x y hx hy
  dsimp only [bothCost]
  rw [show 2*((x+y)/2)-1=x+y-1 by ring]
  linarith

/-- Split the both-live mass according to the smaller TOTAL future cost.
This is one choice per sample, not a separate choice for each family label.
The exact varying-cost identity holds without sign assumptions on costs. -/
theorem choose_one {A : Type*} [Fintype A]
    (L R B C₁ C₂ : A → ℝ)
    (hL : ∀ y, 0 ≤ L y) (hR : ∀ y, 0 ≤ R y) (hB : ∀ y, 0 ≤ B y) :
    ∃ ℓ r : A → ℝ,
      (∀ y, 0 ≤ ℓ y ∧ 0 ≤ r y) ∧
      (∀ y, ℓ y+r y=L y+R y+B y) ∧
      (∀ y, ℓ y ≤ L y+B y ∧ r y ≤ R y+B y) ∧
      (∀ y, ℓ y*C₁ y+r y*C₂ y =
        L y*C₁ y+R y*C₂ y+B y*min (C₁ y) (C₂ y)) := by
  classical
  let ℓ := fun y => L y + if C₁ y ≤ C₂ y then B y else 0
  let r := fun y => R y + if C₁ y ≤ C₂ y then 0 else B y
  refine ⟨ℓ,r,?_,?_,?_,?_⟩
  · intro y
    dsimp only [ℓ,r]
    split_ifs <;> constructor <;> linarith [hL y,hR y,hB y]
  · intro y
    dsimp only [ℓ,r]
    split_ifs <;> ring
  · intro y
    dsimp only [ℓ,r]
    split_ifs <;> constructor <;> linarith [hB y]
  · intro y
    dsimp only [ℓ,r]
    split_ifs with h
    · rw [min_eq_left h]; ring
    · rw [min_eq_right (le_of_not_ge h)]; ring

/-- Selection preserves both support conditions and the SHARED density cap. -/
lemma support_and_cap {A : Type*} (L R B ℓ r w : A → ℝ)
    (P Q : A → Prop) (hn : ∀ y, 0 ≤ ℓ y ∧ 0 ≤ r y)
    (hm : ∀ y, ℓ y+r y=L y+R y+B y)
    (hb : ∀ y, ℓ y ≤ L y+B y ∧ r y ≤ R y+B y)
    (hP : ∀ y, P y → L y=0 ∧ B y=0)
    (hQ : ∀ y, Q y → R y=0 ∧ B y=0)
    (hcap : ∀ y, L y+R y+B y ≤ w y) :
    (∀ y, P y → ℓ y=0) ∧ (∀ y, Q y → r y=0) ∧
      ∀ y, ℓ y+r y ≤ w y := by
  refine ⟨?_,?_,?_⟩
  · intro y hy
    obtain ⟨hL,hB⟩ := hP y hy
    have h := (hb y).1
    rw [hL,hB,add_zero] at h
    exact le_antisymm h (hn y).1
  · intro y hy
    obtain ⟨hR,hB⟩ := hQ y hy
    have h := (hb y).2
    rw [hR,hB,add_zero] at h
    exact le_antisymm h (hn y).2
  · intro y
    rw [hm y]
    exact hcap y

/-- The cost of one selected survivor is bounded using the common pair average
and its conservative endpoint transforms. The selected branch is shared
across ALL family labels; the branch counts themselves can differ. -/
theorem exists_selection_bound {A I : Type*} [Fintype A] [Fintype I]
    (L R B : A → ℝ)
    (hL : ∀ y, 0 ≤ L y) (hR : ∀ y, 0 ≤ R y) (hB : ∀ y, 0 ≤ B y)
    (X Y : I → A → ℝ) (hX : ∀ i y, 1 ≤ X i y) (hY : ∀ i y, 1 ≤ Y i y)
    (φ : I → ℝ → ℝ) (hc : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hm : ∀ i, Monotone (φ i)) :
    ∃ ℓ r : A → ℝ,
      (∀ y, 0 ≤ ℓ y ∧ 0 ≤ r y) ∧
      (∀ y, ℓ y+r y=L y+R y+B y) ∧
      (∀ y, ℓ y ≤ L y+B y ∧ r y ≤ R y+B y) ∧
      (∑ y, (ℓ y*(∑ i, φ i (X i y))+r y*(∑ i, φ i (Y i y)))) ≤
        ∑ i, ∑ y, ((L y+R y)*singleCost (φ i) ((X i y+Y i y)/2) +
          B y*bothCost (φ i) ((X i y+Y i y)/2)) := by
  obtain ⟨ℓ,r,hn,ht,hb,he⟩ := choose_one L R B
    (fun y => ∑ i, φ i (X i y)) (fun y => ∑ i, φ i (Y i y)) hL hR hB
  refine ⟨ℓ,r,hn,ht,hb,?_⟩
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro y _
  rw [he y]
  have h₁ : (∑ i, φ i (X i y)) ≤ ∑ i, singleCost (φ i) ((X i y+Y i y)/2) :=
    Finset.sum_le_sum (fun i _ => (single_bound (φ i) (hm i) _ _ (hX i y) (hY i y)).1)
  have h₂ : (∑ i, φ i (Y i y)) ≤ ∑ i, singleCost (φ i) ((X i y+Y i y)/2) :=
    Finset.sum_le_sum (fun i _ => (single_bound (φ i) (hm i) _ _ (hX i y) (hY i y)).2)
  have h₃ : min (∑ i, φ i (X i y)) (∑ i, φ i (Y i y)) ≤
      ∑ i, bothCost (φ i) ((X i y+Y i y)/2) := by
    have hp := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      both_bound (φ i) (hc i) _ _ (hX i y) (hY i y))
    rw [← Finset.sum_div, Finset.sum_add_distrib] at hp
    have hmin₁ := min_le_left (∑ i, φ i (X i y)) (∑ i, φ i (Y i y))
    have hmin₂ := min_le_right (∑ i, φ i (X i y)) (∑ i, φ i (Y i y))
    linarith
  have h := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h₁ (hL y))
    (mul_le_mul_of_nonneg_left h₂ (hR y)))
    (mul_le_mul_of_nonneg_left h₃ (hB y))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith

/-- The selection bridge composes with the shared-capacity finite mixture.
The hypothesis on the average counts is explicit. In particular, it is not
inferred from separate marginal bounds on two different branch events. -/
theorem selected_shared_comparison {A I : Type*} [Fintype A] [Fintype I]
    (L R B : A → ℝ)
    (hL : ∀ y, 0 ≤ L y) (hR : ∀ y, 0 ≤ R y) (hB : ∀ y, 0 ≤ B y)
    (hS hD : ℝ) (hmS : (∑ y, (L y+R y))=hS) (hmD : (∑ y, B y)=hD)
    (X Y : I → A → ℝ) (hX : ∀ i y, 1 ≤ X i y) (hY : ∀ i y, 1 ≤ Y i y)
    (φ : I → ℝ → ℝ) (hc : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hm : ∀ i, Monotone (φ i))
    (s : I → ℕ → A → ℝ) (q : ℕ → ℝ) (D : ℕ)
    (hq : ∀ j < D, 0 ≤ q j) (hqD : q D=0)
    (hqdec : ∀ j < D, q (j+1) ≤ q j)
    (hs : ∀ i j, j < D → ∀ y, s i j y ∈ Set.Icc (0:ℝ) 1)
    (havg : ∀ i y, (X i y+Y i y)/2 = 1+prefixWeight (fun j => s i j y) D)
    (hmarg : ∀ i j, j < D → (∑ y, (L y+R y+B y)*s i j y) ≤ q j)
    (F : ℝ → ℝ) (hF : ∀ t, (∑ i, φ i t) ≤ F t) :
    ∃ ℓ r : A → ℝ,
      (∀ y, 0 ≤ ℓ y ∧ 0 ≤ r y) ∧
      (∀ y, ℓ y+r y=L y+R y+B y) ∧
      (∀ y, ℓ y ≤ L y+B y ∧ r y ≤ R y+B y) ∧
      (∑ y, (ℓ y*(∑ i, φ i (X i y))+r y*(∑ i, φ i (Y i y)))) ≤
        mixValue hS (fun j => firstCap hS (q j)) D (singleCost F) +
          mixValue hD (fun j => secondCap hS hD (q j)) D (bothCost F) := by
  obtain ⟨ℓ,r,hn,ht,hb,hcost⟩ := exists_selection_bound L R B hL hR hB X Y hX hY φ hc hm
  refine ⟨ℓ,r,hn,ht,hb,hcost.trans ?_⟩
  simp_rw [havg]
  apply separate_families (fun y => L y+R y) B
    (fun y => add_nonneg (hL y) (hR y)) hB hS hD hmS hmD
    (fun i => singleCost (φ i)) (fun i => bothCost (φ i))
    (fun i => singleCost_convex _ (hc i)) (fun i => bothCost_convex _ (hc i))
    (fun i => singleCost_mono _ (hm i)) (fun i => bothCost_mono _ (hm i))
    (fun i => ordered_increments _ (hm i)) s q D hq hqD hqdec hs hmarg
    (singleCost F) (bothCost F)
  · intro t
    exact hF (2*t-1)
  · intro t
    dsimp only [bothCost]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith [hF (2*t-1),hF 1]

open Erdos7PairedTernaryRoot

lemma law_linear (D : ℕ) (f g : ℝ → ℝ) (a b : ℝ) :
    law D (fun t => a*f t+b*g t)=a*law D f+b*law D g := by
  simp only [law, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

lemma law_ext (D : ℕ) (f g : ℝ → ℝ) (h : ∀ t, f t=g t) : law D f=law D g := by
  exact congrArg (law D) (funext h)

/-- The safe endpoint transform has a larger first moment than the average.
There is no suppressed selection cost in this identity. -/
lemma single_law_mean (D : ℕ) : law D (singleCost (fun t => t))=3-(1/3:ℝ)^D := by
  have h := law_linear D (fun t => t) (fun _ => 1) 2 (-1)
  rw [law_mean,law_mass] at h
  calc
    _ = law D (fun t => 2*t+(-1)*1) :=
      law_ext _ _ _ (fun t => by dsimp only [singleCost]; ring)
    _ = _ := by rw [h]; ring

lemma both_law_mean (D : ℕ) : law D (bothCost (fun t => t))=2-(1/3:ℝ)^D/2 := by
  calc
    _ = law D (fun t => t) := law_ext _ _ _ (fun t => by dsimp only [bothCost]; ring)
    _ = _ := law_mean D

lemma single_law_second_moment (D : ℕ) :
    law D (singleCost (fun t => t^2))=10-(2*(D:ℝ)+6)*(1/3:ℝ)^D := by
  have h₁ := law_linear D (fun t => t^2) (fun t => t) 4 (-4)
  rw [law_second_moment,law_mean] at h₁
  have h₂ := law_linear D (fun t => 4*t^2+(-4)*t) (fun _ => 1) 1 1
  rw [h₁,law_mass] at h₂
  calc
    _ = law D (fun t => 1*(4*t^2+(-4)*t)+1*1) :=
      law_ext _ _ _ (fun t => by dsimp only [singleCost]; ring)
    _ = _ := by rw [h₂]; ring

lemma both_law_second_moment (D : ℕ) :
    law D (bothCost (fun t => t^2))=11/2-((D:ℝ)+3)*(1/3:ℝ)^D := by
  have h := law_linear D (singleCost (fun t => t^2)) (fun _ => 1) (1/2) (1/2)
  rw [single_law_second_moment,law_mass] at h
  calc
    _ = law D (fun t => 1/2*singleCost (fun t => t^2) t+1/2*1) :=
      law_ext _ _ _ (fun t => by dsimp only [singleCost,bothCost]; ring)
    _ = _ := by rw [h]; ring

/-- Even with both candidates available, one branch must be chosen for all
labels. The convex cost of each pair average is not a valid upper bound. -/
lemma different_label_selection_control :
    let X : Bool → ℝ := fun i => if i then 4 else 1
    let Y : Bool → ℝ := fun i => if i then 1 else 4
    (∑ i, ((X i+Y i)/2)^2) < min (∑ i, (X i)^2) (∑ i, (Y i)^2) := by
  norm_num [Fintype.sum_bool]

#print axioms endpoint_pair
#print axioms exists_selection_bound
#print axioms support_and_cap
#print axioms selected_shared_comparison
#print axioms single_law_mean
#print axioms both_law_second_moment
#print axioms different_label_selection_control
end Erdos7PairedSelectionBridge
