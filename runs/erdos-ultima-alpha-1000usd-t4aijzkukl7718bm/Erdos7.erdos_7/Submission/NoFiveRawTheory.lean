import Submission.NoFiveScalarData
import Submission.SharpRawBudget

/-! Raw second-moment algebra for the mixed controls at three and later primes. -/
namespace Erdos7NoFiveRaw
open scoped BigOperators
open Erdos7NoFiveScalar
set_option maxHeartbeats 4000000

def multiplierC (p : ℕ) : ℚ := 1+cap p*(3*(p : ℚ)-1)/(p-1)^2
def chargeC (p : ℕ) : ℚ := (cap p)^2/(4*(cap p-1))/(p-1 : ℚ)^2
def productC (S : Finset ℕ) : ℚ := ∏ p ∈ S, multiplierC p
def costC (S : Finset ℕ) : ℚ := ∑ p ∈ S, chargeC p*productC (S.filter (· < p))
def stepC (s : ℚ × ℚ) (p : ℕ) : ℚ × ℚ :=
  (s.1*multiplierC p,s.2+s.1*chargeC p)

lemma productC_union {A B : Finset ℕ} (h : Disjoint A B) :
    productC (A ∪ B) = productC A * productC B :=
  Finset.prod_union h

lemma costC_union {A B : Finset ℕ}
    (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    costC (A ∪ B) = costC A + productC A * costC B := by
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (lt_irrefl a) (h a ha a hb)
  have hA (a : ℕ) (ha : a ∈ A) :
      (A ∪ B).filter (· < a) = A.filter (· < a) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hp | hp, hpa⟩
      · exact ⟨hp, hpa⟩
      · exact False.elim ((not_lt_of_gt (h a ha p hp)) hpa)
    · rintro ⟨hp,hpa⟩; exact ⟨Or.inl hp,hpa⟩
  have hB (b : ℕ) (hb : b ∈ B) :
      (A ∪ B).filter (· < b) = A ∪ B.filter (· < b) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hp | hp,hpb⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hp,hpb⟩
    · rintro (hp | ⟨hp,hpb⟩)
      · exact ⟨Or.inl hp,h p hp b hb⟩
      · exact ⟨Or.inr hp,hpb⟩
  unfold costC
  rw [Finset.sum_union hd, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha; rw [hA a ha]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [hB b hb, productC_union (hd.mono_right (Finset.filter_subset _ _))]
    ring

lemma productC_empty : productC ∅ = 1 := by simp [productC]
lemma costC_empty : costC ∅ = 0 := by simp [costC]
lemma productC_singleton (p : ℕ) : productC {p} = multiplierC p := by
  simp [productC]
lemma costC_singleton (p : ℕ) : costC {p} = chargeC p := by
  have hf : ({p} : Finset ℕ).filter (· < p) = ∅ := by ext; simp; omega
  simp [costC, hf, productC_empty]

lemma foldC_eq (L : List ℕ) (hL : L.Pairwise (· < ·)) (P C : ℚ) :
    L.foldl stepC (P,C) =
      (P*productC L.toFinset, C+P*costC L.toFinset) := by
  induction L generalizing P C with
  | nil => simp [productC_empty, costC_empty]
  | cons p L ih =>
    obtain ⟨hp,hL⟩ := List.pairwise_cons.mp hL
    have hpN : p ∉ L.toFinset := by
      intro h
      exact (lt_irrefl p) (hp p (List.mem_toFinset.mp h))
    have hD : Disjoint ({p} : Finset ℕ) L.toFinset := Finset.disjoint_singleton_left.mpr hpN
    have hO : ∀ a ∈ ({p} : Finset ℕ), ∀ b ∈ L.toFinset, a < b := by
      intro a ha b hb
      rw [Finset.mem_singleton.mp ha]
      exact hp b (List.mem_toFinset.mp hb)
    have hU : (p :: L).toFinset = {p} ∪ L.toFinset := by simp
    rw [List.foldl_cons]
    change L.foldl stepC (P*multiplierC p,C+P*chargeC p) = _
    rw [ih hL, hU, productC_union hD, costC_union hO,
      productC_singleton, costC_singleton]
    congr 1 <;> ring

lemma productC_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 3) :
    productC S = Erdos7No23Sieve.budgetProduct S := by
  unfold productC Erdos7No23Sieve.budgetProduct
  apply Finset.prod_congr rfl
  intro p hp
  simp only [multiplierC,cap,if_neg (hS p hp),Erdos7No23Sieve.multiplier]

lemma costC_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 3) :
    costC S = Erdos7No23Sieve.budgetCost S := by
  unfold costC Erdos7No23Sieve.budgetCost
  apply Finset.sum_congr rfl
  intro p hp
  rw [productC_eq _ (fun q hq => hS q (Finset.mem_filter.mp hq).1)]
  congr 1
  simp only [chargeC,cap,if_neg (hS p hp),Erdos7No23Sieve.charge]
  norm_num

lemma costC_three_union (T : Finset ℕ) (hT : ∀ p ∈ T, 3 < p) :
    costC ({3} ∪ T) = 1/4+5*Erdos7No23Sieve.budgetCost T := by
  rw [costC_union (by
    intro a ha b hb
    rw [Finset.mem_singleton.mp ha]
    exact hT b hb),costC_singleton,productC_singleton,
    costC_eq T (fun p hp => ne_of_gt (hT p hp))]
  norm_num [chargeC,multiplierC,cap]

lemma costC_lt_bound (S : Finset ℕ) (hthree : 3 ∈ S)
    (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p ∧ p ≠ 5) :
    costC S < (27041/13400 : ℚ) := by
  classical
  let T := S.erase 3
  have hT (p : ℕ) (hp : p ∈ T) : p.Prime ∧ 7 ≤ p := by
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hp
    obtain ⟨hpr,hlo,hfive⟩ := hS p hmem
    refine ⟨hpr,?_⟩
    by_contra hh
    have hp6 : p ≤ 6 := by omega
    interval_cases p <;> norm_num at *
  have he : S = {3} ∪ T := by simp [T,Finset.insert_erase hthree]
  rw [he,costC_three_union T (fun p hp => by have := (hT p hp).2; omega)]
  have hbudget := Erdos7SharpRawBudget.budgetCost_lt_419_500 ({5} ∪ T) (by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rw [Finset.mem_singleton.mp hp]
      norm_num
    · exact ⟨(hT p hp).1,by have := (hT p hp).2; omega⟩)
  rw [Erdos7No23Sieve.budgetCost_union (by
    intro a ha b hb
    rw [Finset.mem_singleton.mp ha]
    have := (hT b hb).2
    omega),Erdos7No23Sieve.budgetCost_singleton,Erdos7No23Sieve.budgetProduct_singleton] at hbudget
  norm_num [Erdos7No23Sieve.charge,Erdos7No23Sieve.multiplier] at hbudget
  linarith

lemma secondMomentCost_eq {n : ℕ} (p : Fin n → ℕ) (hmono : StrictMono p) :
    Erdos7Distortion.secondMomentCost p (fun i => cap (p i)) = costC (Finset.univ.image p) := by
  unfold Erdos7Distortion.secondMomentCost costC
  rw [Finset.sum_image hmono.injective.injOn]
  apply Finset.sum_congr rfl
  intro i _
  unfold productC
  rw [Finset.filter_image,Finset.prod_image hmono.injective.injOn]
  simp only [hmono.lt_iff_lt]
  dsimp [multiplierC,chargeC]
  ring

def raw {n : ℕ} (p : Fin n → ℕ) (i : Fin n) : ℚ :=
  chargeC (p i) * ∏ j ∈ Finset.univ.filter (fun j => j < i), multiplierC (p j)

lemma sum_raw {n : ℕ} (p : Fin n → ℕ) :
    (∑ i, raw p i) = Erdos7Distortion.secondMomentCost p (fun i => cap (p i)) := by
  unfold raw Erdos7Distortion.secondMomentCost chargeC multiplierC
  apply Finset.sum_congr rfl
  intro i hi
  ring

#print axioms costC_lt_bound
#print axioms secondMomentCost_eq
end Erdos7NoFiveRaw
