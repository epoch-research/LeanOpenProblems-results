import FormalConjecturesUtil

/-! A finite weak-square-tail bound for the total mass of nonnegative integer lengths. -/
namespace Erdos773.FiniteTailCapacity

open Finset

set_option maxHeartbeats 1000000

lemma truncated_step {α : Type*} (S : Finset α) (H : α → ℕ) (t : ℕ) :
    (∑ i ∈ S, ((min (H i) (t + 1) : ℕ) : ℝ)) =
      (∑ i ∈ S, ((min (H i) t : ℕ) : ℝ)) + ((S.filter (fun i => t < H i)).card : ℝ) := by
  classical
  have hterm (i : α) : ((min (H i) (t + 1) : ℕ) : ℝ) =
      ((min (H i) t : ℕ) : ℝ) + if t < H i then 1 else 0 := by
    split_ifs with h
    · have he : min (H i) (t + 1) = min (H i) t + 1 := by omega
      exact_mod_cast he
    · have he : min (H i) (t + 1) = min (H i) t := by omega
      simpa only [add_zero] using congrArg (Nat.cast : ℕ → ℝ) he
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

lemma reciprocal_step {A C x : ℝ} (hC : 0 ≤ C) (hx : 0 < x)
    (h : C * (x + 1) ^ 2 ≤ A) : C ≤ A / x - A / (x + 1) := by
  have hprod : 0 ≤ C * (x + 1) := mul_nonneg hC (by linarith)
  have hh : C * (x * (x + 1)) ≤ A := by nlinarith only [h, hprod]
  calc
    C ≤ A / (x * (x + 1)) := (le_div_iff₀ (by positivity)).mpr hh
    _ = A / x - A / (x + 1) := by field_simp; ring

/-- An integer cutoff gives the elementary head-plus-tail estimate. -/
theorem cutoff_bound {α : Type*} (S : Finset α) (H : α → ℕ) (A : ℝ)
    (hA : 0 ≤ A)
    (htail : ∀ t : ℕ, 0 < t →
      ((S.filter (fun i => t ≤ H i)).card : ℝ) * (t : ℝ) ^ 2 ≤ A)
    (T : ℕ) (hT : 0 < T) :
    (∑ i ∈ S, (H i : ℝ)) ≤ S.card * (T : ℝ) + A / T := by
  classical
  have htrunc (K : ℕ) :
      (∑ i ∈ S, ((min (H i) (T + K) : ℕ) : ℝ)) ≤
        S.card * (T : ℝ) + A / T - A / (T + K : ℕ) := by
    induction K with
    | zero =>
      simp only [add_zero, add_sub_cancel_right]
      calc
        _ ≤ ∑ _i ∈ S, (T : ℝ) := Finset.sum_le_sum (fun i _ => by exact_mod_cast Nat.min_le_right (H i) T)
        _ = _ := by simp
    | succ K ih =>
      have ht := htail (T + K + 1) (by omega)
      have hfilter : S.filter (fun i => T + K + 1 ≤ H i) =
          S.filter (fun i => T + K < H i) := by
        ext i
        simp only [Finset.mem_filter, Nat.add_one_le_iff]
      rw [hfilter] at ht
      push_cast at ht
      have hc := reciprocal_step
        (show (0 : ℝ) ≤ (S.filter (fun i => T + K < H i)).card by positivity)
        (show (0 : ℝ) < (T : ℝ) + K by exact_mod_cast (show 0 < T + K by omega)) ht
      have hs := truncated_step S H (T + K)
      have he : T + (K + 1) = T + K + 1 := by omega
      rw [he]
      push_cast at ih hs ⊢
      simp only [add_assoc] at hs hc ⊢
      nlinarith only [ih, hs, hc]
  let K := S.sup H
  have hh := htrunc K
  have hmins : (∑ i ∈ S, ((min (H i) (T + K) : ℕ) : ℝ)) = ∑ i ∈ S, (H i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.min_eq_left ((Finset.le_sup hi).trans (Nat.le_add_left K T))]
  rw [hmins] at hh
  have hnonneg : 0 ≤ A / (T + K : ℕ) := by positivity
  linarith

/-- A square-tail bound controls unequal lengths without a logarithmic loss. -/
theorem mass_square_bound {α : Type*} (S : Finset α) (H : α → ℕ) (A : ℝ)
    (hA : (S.card : ℝ) ≤ A)
    (htail : ∀ t : ℕ, 0 < t →
      ((S.filter (fun i => t ≤ H i)).card : ℝ) * (t : ℝ) ^ 2 ≤ A) :
    (∑ i ∈ S, ((H i + 1 : ℕ) : ℝ)) ^ 2 ≤ 16 * A * S.card := by
  classical
  by_cases hne : S.Nonempty
  · have hm : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hne
    have hA0 : 0 ≤ A := by linarith
    let x := Real.sqrt (A / S.card)
    have hx1 : 1 ≤ x := by
      apply Real.one_le_sqrt.mpr
      exact (le_div_iff₀ hm).mpr (by simpa using hA)
    have hx : 0 < x := by linarith
    have he : (S.card : ℝ) * x ^ 2 = A := by
      have hh := Real.sq_sqrt (show 0 ≤ A / S.card by positivity)
      dsimp only [x]
      simpa only [mul_comm] using ((div_eq_iff hm.ne').mp hh.symm).symm
    let T := ⌈x⌉₊
    have hlo : x ≤ (T : ℝ) := Nat.le_ceil x
    have hThi : (T : ℝ) < x + 1 := Nat.ceil_lt_add_one hx.le
    have hT : 0 < T := by exact_mod_cast (show (0 : ℝ) < T by linarith)
    have hcut := cutoff_bound S H A (by linarith) htail T hT
    have hdiv : A / T ≤ S.card * x := by
      apply (div_le_iff₀ (by exact_mod_cast hT : (0 : ℝ) < T)).mpr
      have hh := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (S.card : ℝ) * x by positivity)
      nlinarith only [hh, he]
    have hlinear : (∑ i ∈ S, ((H i + 1 : ℕ) : ℝ)) ≤ 4 * S.card * x := by
      have hh := mul_lt_mul_of_pos_left hThi hm
      have hh1 := mul_le_mul_of_nonneg_left hx1 hm.le
      push_cast
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      nlinarith only [hcut, hdiv, hh, hh1]
    have hs := pow_le_pow_left₀ (show (0 : ℝ) ≤ ∑ i ∈ S, ((H i + 1 : ℕ) : ℝ) by positivity) hlinear 2
    have he' := congrArg (fun y : ℝ => 16 * S.card * y) he
    nlinarith only [hs, he']
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

#print axioms cutoff_bound
#print axioms mass_square_bound

end Erdos773.FiniteTailCapacity
