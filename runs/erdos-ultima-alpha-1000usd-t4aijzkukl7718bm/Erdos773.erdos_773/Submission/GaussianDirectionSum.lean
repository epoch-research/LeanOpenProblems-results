import Submission.GaussianRadialCounting
import Submission.GaussianIncidentCounting

/-! A finite uniform reciprocal-sum estimate for Gaussian directions. -/
namespace Erdos773.GaussianDirectionSum
open Finset GaussianIncidentEncoding GaussianDirectionWeights GaussianRadialCounting
set_option maxHeartbeats 2000000
noncomputable section

def radial (u v : ℕ) : ℝ := (weight u v : ℝ)/((u:ℝ)^2+(v:ℝ)^2)

lemma radial_nonneg (u v : ℕ) : 0 ≤ radial u v := by unfold radial; positivity
lemma radial_symm (u v : ℕ) : radial u v = radial v u := by
  have hw : weight u v = weight v u := by unfold weight; split_ifs <;> omega
  simp only [radial,hw,add_comm]
lemma radial_diag (u : ℕ) : radial u u=0 := by simp [radial,weight]

lemma triangle_as_square (R : ℕ) :
    (∑ u ∈ Icc 1 R, ∑ v ∈ Icc 1 R, if v<u then radial u v else 0) = triangleSum R := by
  apply sum_congr rfl
  intro u hu
  rw [← sum_filter]
  have he : (Icc 1 R).filter (fun v => v<u)=Icc 1 (u-1) := by
    ext v
    simp only [mem_filter,mem_Icc]
    have := mem_Icc.mp hu
    omega
  rw [he]
  rfl

lemma square_sum (R : ℕ) :
    (∑ p ∈ (Icc 1 R) ×ˢ (Icc 1 R), radial p.1 p.2) = 2*triangleSum R := by
  rw [sum_product]
  have he (u v : ℕ) : radial u v =
      (if v<u then radial u v else 0)+(if u<v then radial v u else 0) := by
    rcases lt_trichotomy v u with h | h | h
    · simp [h,show ¬u<v by omega]
    · subst v; simp [radial_diag]
    · simp [h,show ¬v<u by omega,radial_symm u v]
  calc
    _ = ∑ u ∈ Icc 1 R, ∑ v ∈ Icc 1 R,
        ((if v<u then radial u v else 0)+(if u<v then radial v u else 0)) := by
      apply sum_congr rfl
      intro u hu
      exact sum_congr rfl (fun v hv => he u v)
    _ = 2*triangleSum R := by
      simp_rw [sum_add_distrib]
      rw [triangle_as_square,sum_comm,triangle_as_square]
      ring

lemma direction_box {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N) :
    p.1 ≤ Nat.sqrt (2*N) ∧ p.2 ≤ Nat.sqrt (2*N) := by
  have hn := (mem_directions hp).2.2.2
  dsimp [normSq] at hn
  constructor <;> apply Nat.le_sqrt'.mpr <;> omega

lemma directions_card (N : ℕ) : (directions N).card ≤ 4*N := by
  have hs : directions N ⊆ (Icc 1 (Nat.sqrt (2*N))) ×ˢ (Icc 0 (Nat.sqrt (2*N))) := by
    intro p hp
    obtain ⟨h₁,h₂⟩ := direction_box hp
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨(mem_directions hp).1,h₁⟩,
      mem_Icc.mpr ⟨Nat.zero_le _,h₂⟩⟩
  have hc := card_le_card hs
  rw [card_product,Nat.card_Icc,Nat.card_Icc] at hc
  simp only [Nat.add_sub_cancel,Nat.sub_zero] at hc
  have hs := Nat.sqrt_le' (2*N)
  have ht : Nat.sqrt (2*N) ≤ Nat.sqrt (2*N)^2 := Nat.le_pow (by omega)
  nlinarith

lemma reciprocal_sum_bound (N : ℕ) :
    (∑ p ∈ directions N, 1/(normSq p : ℝ)) ≤ 1+2*triangleSum (Nat.sqrt (2*N)) := by
  classical
  let R := Nat.sqrt (2*N)
  let B := (Icc 1 R) ×ˢ (Icc 1 R)
  have hs : directions N ⊆ insert (1,0) B := by
    intro p hp
    obtain ⟨hu,hcop,hpar,hn⟩ := mem_directions hp
    obtain ⟨h₁,h₂⟩ := direction_box hp
    by_cases hv : p.2=0
    · have he : p.1=1 := by simpa [hv] using hcop
      apply mem_insert.mpr
      left
      exact Prod.ext he hv
    · apply mem_insert_of_mem
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨hu,h₁⟩,mem_Icc.mpr ⟨by omega,h₂⟩⟩
  have he : (∑ p ∈ directions N, 1/(normSq p : ℝ)) =
      ∑ p ∈ directions N, radial p.1 p.2 := by
    apply sum_congr rfl
    intro p hp
    obtain ⟨hu,hcop,hpar,hn⟩ := mem_directions hp
    simp [radial,weight_of_coprime hcop hpar,normSq]
  rw [he]
  calc
    _ ≤ ∑ p ∈ insert (1,0) B, radial p.1 p.2 :=
      sum_le_sum_of_subset_of_nonneg hs (fun p hp _ => radial_nonneg _ _)
    _ = 1+2*triangleSum R := by
      rw [sum_insert (by simp [B])]
      have hr : radial 1 0=1 := by norm_num [radial,weight]
      rw [hr,square_sum]

#print axioms square_sum
#print axioms directions_card
#print axioms reciprocal_sum_bound
end
end Erdos773.GaussianDirectionSum
