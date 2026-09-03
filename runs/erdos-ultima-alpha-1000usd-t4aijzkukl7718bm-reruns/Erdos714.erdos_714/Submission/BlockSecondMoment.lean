import Submission.UnbalancedBounds

/-! Block averaging with second moments, for testing low-rank incidence constructions. -/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714BlockMoment

lemma mixed_power_bound (m n q : ℕ) : m^3*n^4*q ≤ (m^2+n^2+q^2)^4 := by
  have hm : m^3*q ≤ (m^2+q^2)^2 := by
    rcases le_total m q with h | h
    · calc
        _ ≤ q^3*q := Nat.mul_le_mul_right q (Nat.pow_le_pow_left h 3)
        _ = (q^2)^2 := by ring
        _ ≤ _ := Nat.pow_le_pow_left (Nat.le_add_left _ _) 2
    · calc
        _ ≤ m^3*m := Nat.mul_le_mul_left _ h
        _ = (m^2)^2 := by ring
        _ ≤ _ := Nat.pow_le_pow_left (Nat.le_add_right _ _) 2
  have hs : m^2+q^2 ≤ m^2+n^2+q^2 := by omega
  have hn : n^2 ≤ m^2+n^2+q^2 := by omega
  calc
    _ = (m^3*q)*n^4 := by ring
    _ ≤ (m^2+q^2)^2*n^4 := Nat.mul_le_mul_right _ hm
    _ = (m^2+q^2)^2*(n^2)^2 := by ring
    _ ≤ (m^2+n^2+q^2)^2*(m^2+n^2+q^2)^2 := by gcongr
    _ = _ := by ring

/-- An integer-parameter substitute for a fractional-power Holder bound. -/
lemma local_bound (e m n q u : ℕ) (he : (e-3*m)^4 ≤ 3*m^3*n^4)
    (hu : q^3 ≤ u^4) :
    q*e ≤ 3*q*m+2*u*(m^2+n^2+q^2) := by
  have hpow : (q*(e-3*m))^4 ≤ (2*u*(m^2+n^2+q^2))^4 := by
    calc
      _ = q^3*((e-3*m)^4*q) := by ring
      _ ≤ q^3*(3*m^3*n^4*q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ he)
      _ = 3*q^3*(m^3*n^4*q) := by ring
      _ ≤ 3*u^4*(m^2+n^2+q^2)^4 := by gcongr; exact mixed_power_bound m n q
      _ ≤ (2*u*(m^2+n^2+q^2))^4 := by ring_nf; omega
  have hle := (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp hpow
  have he' : e ≤ 3*m+(e-3*m) := by omega
  calc
    q*e ≤ q*(3*m+(e-3*m)) := Nat.mul_le_mul_left _ he'
    _ = 3*q*m+q*(e-3*m) := by ring
    _ ≤ _ := Nat.add_le_add_left hle _

variable {I C : Type*} [Fintype I] [Fintype C]

/-- Point and distinct-pair coverage bounds control the block-size second moment. -/
theorem second_moment (S : I → Finset C) (a b : ℕ)
    (ha : ∀ c, (univ.filter (fun i => c ∈ S i)).card ≤ a)
    (hb : ∀ c d, c ≠ d → (univ.filter (fun i => c ∈ S i ∧ d ∈ S i)).card ≤ b) :
    ∑ i, (S i).card^2 ≤ a*Fintype.card C+b*Fintype.card C^2 := by
  have expand (i : I) : (S i).card^2 =
      ∑ c : C, ∑ d : C, if c ∈ S i ∧ d ∈ S i then 1 else 0 := by
    simp_rw [show ∀ c d : C, (if c ∈ S i ∧ d ∈ S i then 1 else 0 : ℕ) =
      (if c ∈ S i then 1 else 0)*(if d ∈ S i then 1 else 0) from
      fun c d => by split_ifs <;> simp_all]
    simp only [← mul_sum, ← sum_mul, sum_boole, filter_mem_eq_inter, univ_inter, pow_two, Nat.cast_id]
  calc
    _ = ∑ c : C, ∑ d : C, (univ.filter (fun i => c ∈ S i ∧ d ∈ S i)).card := by
      simp_rw [expand]
      rw [sum_comm]
      congr 1
      ext c
      rw [sum_comm]
      simp only [sum_boole, Nat.cast_id]
    _ ≤ ∑ c : C, ∑ d : C, ((if c = d then a else 0)+b) := by
      apply sum_le_sum
      intro c _
      apply sum_le_sum
      intro d _
      by_cases h : c = d
      · subst d
        simpa only [and_self, if_true] using (ha c).trans (Nat.le_add_right a b)
      · simpa only [h, if_false, zero_add] using hb c d h
    _ = _ := by simp [sum_add_distrib, pow_two]; ring

/-- A first-moment version with the same indexing conventions. -/
theorem first_moment (S : I → Finset C) (a : ℕ)
    (ha : ∀ c, (univ.filter (fun i => c ∈ S i)).card ≤ a) :
    ∑ i, (S i).card ≤ a*Fintype.card C := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun i c => c ∈ S i) (s := (univ : Finset I)) (t := (univ : Finset C))
  simp only [bipartiteAbove, bipartiteBelow, filter_mem_eq_inter, univ_inter] at h
  rw [h]
  simpa only [sum_const, card_univ, smul_eq_mul, mul_comm] using
    sum_le_sum (s := (univ : Finset C)) (fun c _ => ha c)

/-- The global inequality assumes only block moments and an edge-coverage lower bound.
It is not an assertion that arbitrary incidence models have these hypotheses. -/
theorem bound (e m n : I → ℕ) (q u t E A B C : ℕ)
    (he : ∀ i, (e i-3*m i)^4 ≤ 3*(m i)^3*(n i)^4)
    (hu : q^3 ≤ u^4) (hcover : t*E ≤ ∑ i, e i)
    (hm : ∑ i, (m i)^2 ≤ A) (hn : ∑ i, (n i)^2 ≤ B)
    (hm₁ : ∑ i, m i ≤ C) :
    q*t*E ≤ 3*q*C+2*u*(A+B+Fintype.card I*q^2) := by
  calc
    _ = q*(t*E) := by ring
    _ ≤ q*∑ i, e i := Nat.mul_le_mul_left _ hcover
    _ = ∑ i, q*e i := mul_sum _ _ _
    _ ≤ ∑ i, (3*q*m i+2*u*((m i)^2+(n i)^2+q^2)) :=
      sum_le_sum (fun i _ => local_bound _ _ _ _ _ (he i) hu)
    _ = 3*q*(∑ i, m i)+2*u*((∑ i, (m i)^2)+(∑ i, (n i)^2)+Fintype.card I*q^2) := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, smul_eq_mul]
    _ ≤ _ := by gcongr

#print axioms local_bound
#print axioms second_moment
#print axioms first_moment
#print axioms bound
end Erdos714BlockMoment
