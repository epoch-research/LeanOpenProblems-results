import Submission.PacketMatchingMassExplore

/-! Finite selection allowing o(log n) unintended sums rather than requiring
a Sidon family. Both self and mixed counts are controlled by potentials. -/
namespace Erdos66MatchingPacketSelection
open Erdos66MultiPacket Erdos66MultiPacketSelection Erdos66PacketMatching
  Erdos66PacketMatchingMass Erdos66HeterogeneousSelection
open Erdos66UniformSelection (mean mean_sum mean_add mean_mono mean_const mean_const_mul
  mean_indicator exists_lt_of_mean_lt)
open scoped Classical
set_option maxHeartbeats 1600000
variable {ι ζ : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, DecidableEq (α i)]

lemma mean_hits (B : ∀ i, Finset (α i)) : mean (hits B) = hitMass B := by
  unfold hits hitMass
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hprod := Erdos66HeterogeneousSelection.mean_product
    (fun j (a : α j) ↦ if h : j = i then (if h ▸ a ∈ B i then (1 : ℝ) else 0) else 1)
  have hl (ω : ∀ i, α i) :
      (∏ j, if h : j = i then (if h ▸ ω j ∈ B i then (1 : ℝ) else 0) else 1) =
      if ω i ∈ B i then (1 : ℝ) else 0 := by simp
  simp_rw [hl] at hprod
  have hr : (∏ j, mean (fun a : α j ↦ if h : j = i then
      (if h ▸ a ∈ B i then (1 : ℝ) else 0) else 1)) =
      mean (fun a : α i ↦ if a ∈ B i then (1 : ℝ) else 0) := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hji; simp [hji,mean_const]
    · simp
  rw [hr] at hprod
  rw [hprod,mean_indicator]
  simp

lemma hitTerm_mean_le (B : ∀ i, Finset (α i)) (R t : ℝ) :
    mean (fun ω ↦ Real.exp (t*(hits B ω-R))) ≤
      Real.exp (Real.exp t * hitMass B-t*R) := by
  have he (ω : ∀ i, α i) : Real.exp (t*(hits B ω-R)) =
      Real.exp (-t*R)*Real.exp (t*hits B ω) := by rw [← Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [mean_const_mul]
  apply (mul_le_mul_of_nonneg_left (hit_mgf_bound B t) (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

lemma offTerm_mean_le (n : ι → ℤ) (x : ∀ i, α i → ℤ)
    (hx : ∀ i, Function.Injective (x i)) (z : ℤ) (R t : ℝ) (ht : 0 ≤ t) :
    mean (fun ω ↦ Real.exp (-t*R)*offTest n x z t ω) ≤
      Real.exp ((Real.exp (8*t)-1)*4*(sqrtMass (fun i ↦ Fintype.card (α i)))^2-t*R) := by
  rw [mean_const_mul]
  apply (mul_le_mul_of_nonneg_left (mean_offTest_le n x hx z t ht) (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

/-- A bounded reciprocal-square-root mass supports joint self and mixed
representation tests. All selected labels are distinct and avoid B. -/
theorem exists_matching_packets (n : ι → ℤ) (x : ∀ i, α i → ℤ)
    (hx : ∀ i, Function.Injective (x i)) (B : ∀ i, Finset (α i))
    (T : Finset ζ) (z : ζ → ℤ) (S : ζ → ∀ i, Finset (α i)) (R t : ζ → ℝ)
    (ht : ∀ j ∈ T, 0 < t j)
    (hsmall : 4*(sqrtMass (fun i ↦ Fintype.card (α i)))^2+hitMass B+
      (∑ j ∈ T, (Real.exp (Real.exp (t j)*hitMass (S j)-t j*R j)+
        Real.exp ((Real.exp (8*t j)-1)*4*(sqrtMass (fun i ↦ Fintype.card (α i)))^2-t j*R j))) < 1) :
    ∃ ω : ∀ i, α i, Function.Injective (point n (chosen x ω)) ∧ (∀ i, ω i ∉ B i) ∧
      ∀ j ∈ T, hits (S j) ω < R j ∧ ((offPairs n x (z j) ω).card : ℝ) < R j := by
  let q := fun i ↦ Fintype.card (α i)
  let bad (ω : ∀ i, α i) : ℝ := ∑ p ∈ (pointEvents : Finset (Edge ι)),
    if point n (chosen x ω) p.1 = point n (chosen x ω) p.2 then (1 : ℝ) else 0
  let hterm (j : ζ) (ω : ∀ i, α i) := Real.exp (t j*(hits (S j) ω-R j))
  let oterm (j : ζ) (ω : ∀ i, α i) := Real.exp (-t j*R j)*offTest n x (z j) (t j) ω
  let F (ω : ∀ i, α i) := bad ω+hits B ω+∑ j ∈ T, (hterm j ω+oterm j ω)
  have hbad (ω : ∀ i, α i) : 0 ≤ bad ω := by
    exact Finset.sum_nonneg (fun _ _ ↦ by (try dsimp only); split_ifs <;> norm_num)
  have hht (j : ζ) (ω : ∀ i, α i) : 0 ≤ hterm j ω := (Real.exp_pos _).le
  have hot (j : ζ) (ω : ∀ i, α i) : 0 ≤ oterm j ω :=
    mul_nonneg (Real.exp_pos _).le (offTest_nonneg n x (z j) (t j) ω)
  have htests (ω : ∀ i, α i) : 0 ≤ ∑ j ∈ T, (hterm j ω+oterm j ω) :=
    Finset.sum_nonneg (fun j _ ↦ add_nonneg (hht j ω) (hot j ω))
  have hbadmean : mean bad ≤ 4*(sqrtMass q)^2 := by
    rw [show bad = (fun ω ↦ ∑ p ∈ (pointEvents : Finset (Edge ι)),
      if point n (chosen x ω) p.1 = point n (chosen x ω) p.2 then (1 : ℝ) else 0) from rfl,mean_sum]
    apply (Finset.sum_le_sum (fun p hp ↦ ?_)).trans (payer_cost_sum_le q (fun i ↦ Fintype.card_pos) pointEvents)
    apply one_fiber_indicator_bound _ (payer q p)
    intro ω a b ha hb
    have hh := point_collision_fiber n p.1 p.2 (Finset.mem_filter.mp hp).2
      (payer q p) (payer_mem q p) (chosen x ω) (x (payer q p) a) (x (payer q p) b)
    rw [chosen_update] at ha hb
    exact hx _ (hh ha hb)
  have hF : mean F < 1 := by
    dsimp only [F]
    rw [mean_add,mean_add,mean_hits,mean_sum T]
    have hh : (∑ j ∈ T, mean (fun ω ↦ hterm j ω+oterm j ω)) ≤
        ∑ j ∈ T, (Real.exp (Real.exp (t j)*hitMass (S j)-t j*R j)+
        Real.exp ((Real.exp (8*t j)-1)*4*(sqrtMass q)^2-t j*R j)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [mean_add]
      exact add_le_add (hitTerm_mean_le (S j) (R j) (t j))
        (offTerm_mean_le n x hx (z j) (R j) (t j) (ht j hj).le)
    dsimp only [q] at hbadmean hh
    linarith
  obtain ⟨ω,hω⟩ := exists_lt_of_mean_lt F 1 hF
  have hb0 := hbad ω
  have hB0 := hits_nonneg B ω
  have hT0 := htests ω
  have hinj : Function.Injective (point n (chosen x ω)) := by
    intro u v he
    by_contra hne
    have hp : (u,v) ∈ (pointEvents : Finset (Edge ι)) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩
    have hh := Finset.single_le_sum (f := fun p : Edge ι ↦
      if point n (chosen x ω) p.1 = point n (chosen x ω) p.2 then (1 : ℝ) else 0)
      (fun _ _ ↦ by (try dsimp only); split_ifs <;> norm_num) hp
    dsimp only at hh
    rw [if_pos he] at hh
    change 1 ≤ bad ω at hh
    dsimp only [F] at hω
    linarith
  refine ⟨ω,hinj,?_,?_⟩
  · intro i hi
    have hh := Finset.single_le_sum (f := fun i ↦ if ω i ∈ B i then (1 : ℝ) else 0)
      (fun _ _ ↦ by (try dsimp only); split_ifs <;> norm_num) (Finset.mem_univ i)
    dsimp only at hh
    rw [if_pos hi] at hh
    change 1 ≤ hits B ω at hh
    dsimp only [F] at hω
    linarith
  · intro j hj
    have hh := Finset.single_le_sum (f := fun j ↦ hterm j ω+oterm j ω)
      (fun j _ ↦ add_nonneg (hht j ω) (hot j ω)) hj
    have hh1 : hterm j ω < 1 := by dsimp only [F] at hω; linarith [hot j ω]
    have ho1 : oterm j ω < 1 := by dsimp only [F] at hω; linarith [hht j ω]
    have htm := ht j hj
    constructor
    · have hh' := Real.exp_lt_one_iff.mp hh1
      simp only [hterm] at hh'
      nlinarith
    · dsimp only [oterm,offTest] at ho1
      rw [if_pos hinj,← Real.exp_add] at ho1
      have hh' := Real.exp_lt_one_iff.mp ho1
      nlinarith

end Erdos66MatchingPacketSelection
