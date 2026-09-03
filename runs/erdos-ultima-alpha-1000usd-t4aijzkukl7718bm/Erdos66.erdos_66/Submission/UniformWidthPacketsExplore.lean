import Submission.JointFiniteRepairExplore

/-! Joint packets with a common choice width. A constant representation
upper bound supplies all old-point avoidance and mixed-hit estimates through
local window counts, independently of the old set's total cardinality. -/
namespace Erdos66UniformWidthPackets
open Erdos66MultiPacket Erdos66MultiPacketSelection Erdos66HeterogeneousSelection
  Erdos66JointFiniteRepair Erdos66FiniteRepair Erdos66OriginRepair Erdos66LocalWindow
open scoped Classical
set_option maxHeartbeats 1800000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pointEvents_card_le : ((pointEvents : Finset (Label ι × Label ι)).card : ℝ) ≤
    (2*(Fintype.card ι : ℝ))^2 := by
  have hh := Finset.card_le_univ (pointEvents : Finset (Label ι × Label ι))
  have hc : Fintype.card (Label ι × Label ι)=(2*Fintype.card ι)^2 := by
    simp only [Fintype.card_prod,Fintype.card_bool,pow_two,Label]
    ring
  rw [hc] at hh
  exact_mod_cast hh

lemma pairEvents_card_le : ((pairEvents : Finset (Quad ι)).card : ℝ) ≤
    (2*(Fintype.card ι : ℝ))^4 := by
  have hh := Finset.card_le_univ (pairEvents : Finset (Quad ι))
  have hc : Fintype.card (Quad ι)=(2*Fintype.card ι)^4 := by
    simp only [Quad,Label,Fintype.card_prod,Fintype.card_bool]
    ring
  rw [hc] at hh
  exact_mod_cast hh

lemma hitMass_le_uniform (W : ℕ) (hW : 0<W) (B : ι → Finset (Fin W)) (K : ℝ)
    (hB : ∀ i, ((B i).card : ℝ) ≤ K) :
    hitMass B ≤ (Fintype.card ι : ℝ)*K/W := by
  unfold hitMass
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∑ _i : ι, K/(W : ℝ) := Finset.sum_le_sum (fun i _ ↦
      div_le_div_of_nonneg_right (hB i) (Nat.cast_nonneg W))
    _ = _ := by simp; ring

/-- The output preserves the labelled pairs, so independent algebraic data
can subsequently be attached to each designated pair. -/
theorem exists_uniform_width_packets (A : Finset ℤ) (V : ℝ)
    (hA : ∀ z : ℤ, (pairCount A A z : ℝ) ≤ V)
    (n a : ι → ℤ) (W : ℕ) (hW : 0<W) (T : Finset ℤ) (R t : ℝ) (ht : 0<t)
    (hsmall : ((2*(Fintype.card ι : ℝ))^2+(2*(Fintype.card ι : ℝ))^4)/W +
      (Fintype.card ι : ℝ)*(2*Real.sqrt (2*(W : ℝ)*V))/W +
      (T.card : ℝ)*Real.exp (Real.exp t*((Fintype.card ι : ℝ)*(2*Real.sqrt (2*(W : ℝ)*V))/W)-t*R) < 1) :
    ∃ ω : ι → Fin W,
      Function.Injective (point n (fun i ↦ a i+(ω i).val)) ∧
      (∀ i, a i+(ω i).val ∉ A ∧ n i-(a i+(ω i).val) ∉ A) ∧
      (∀ u v w s : Label ι, ¬Designated u v → ¬Designated w s →
        point n (fun i ↦ a i+(ω i).val) u+point n (fun i ↦ a i+(ω i).val) v=
          point n (fun i ↦ a i+(ω i).val) w+point n (fun i ↦ a i+(ω i).val) s →
          (u=w ∧ v=s) ∨ (u=s ∧ v=w)) ∧
      (∀ z∈T, (pairCount (packet n (fun i ↦ a i+(ω i).val)) A z : ℝ) < 2*R) := by
  letI : NeZero W := ⟨by omega⟩
  let x : ι → Fin W → ℤ := fun i j ↦ a i+j.val
  let K := 2*Real.sqrt (2*(W : ℝ)*V)
  let H := (Fintype.card ι : ℝ)*K/W
  have hx (i : ι) : Function.Injective (x i) := by
    intro j k hjk
    apply Fin.ext
    dsimp [x] at hjk
    exact_mod_cast add_left_cancel hjk
  have hc (i : ι) := interval_choice_bounds A V hA (n i) (a i) W
  have hb : hitMass (fun i ↦ forbidden A (n i) (x i)) ≤ H :=
    hitMass_le_uniform W hW _ K (fun i ↦ (hc i).1)
  have hh (z : ℤ) : hitMass (fun i ↦ hitChoices A (n i) (x i) z) ≤ H :=
    hitMass_le_uniform W hW _ K (fun i ↦ (hc i).2 z)
  have hcost :
      (∑ _p∈(pointEvents : Finset (Label ι × Label ι)), 1/(W : ℝ))+
      (∑ _p∈(pairEvents : Finset (Quad ι)), 1/(W : ℝ)) ≤
        ((2*(Fintype.card ι : ℝ))^2+(2*(Fintype.card ι : ℝ))^4)/W := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    have h₁ := mul_le_mul_of_nonneg_right (pointEvents_card_le (ι := ι)) (show 0 ≤ 1/(W : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right (pairEvents_card_le (ι := ι)) (show 0 ≤ 1/(W : ℝ) by positivity)
    convert add_le_add h₁ h₂ using 1 <;> ring
  have htests : (∑ z∈T, Real.exp (Real.exp t*hitMass (fun i ↦ hitChoices A (n i) (x i) z)-t*R)) ≤
      (T.card : ℝ)*Real.exp (Real.exp t*H-t*R) := by
    calc
      _ ≤ ∑ _z∈T, Real.exp (Real.exp t*H-t*R) := Finset.sum_le_sum (fun z _ ↦
        Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left (hh z) (Real.exp_pos _).le) _))
      _ = _ := by simp
  have hsmall' :
      (∑ p∈(pointEvents : Finset (Label ι × Label ι)), 1/(Fintype.card (Fin W) : ℝ))+
      (∑ p∈(pairEvents : Finset (Quad ι)), 1/(Fintype.card (Fin W) : ℝ))+
      hitMass (fun i ↦ forbidden A (n i) (x i))+
      (∑ z∈T, Real.exp (Real.exp t*hitMass (fun i ↦ hitChoices A (n i) (x i) z)-t*R)) < 1 := by
    simp only [Fintype.card_fin]
    dsimp [H,K] at hb htests
    linarith
  obtain ⟨ω,hinj,havoid,hunique,hits⟩ := exists_joint_packets n x hx
    (fun i ↦ forbidden A (n i) (x i)) (fun p ↦ p.1.1) (fun p ↦ p.1.1)
    (fun _ _ ↦ Or.inl rfl) (fun _ _ ↦ Or.inl rfl) T
    (fun z i ↦ hitChoices A (n i) (x i) z) (fun _ ↦ R) (fun _ ↦ t) (fun _ _ ↦ ht) hsmall'
  refine ⟨ω,hinj,?_,hunique,?_⟩
  · intro i
    have hh := havoid i
    simpa only [forbidden,Finset.mem_filter,Finset.mem_univ,true_and,not_or,x] using hh
  · intro z hz
    have hh := joint_mixed_le_hits A n x ω z
    have ht' := hits z hz
    change (pairCount (packet n (chosen x ω)) A z : ℝ) < 2*R
    linarith

end Erdos66UniformWidthPackets
