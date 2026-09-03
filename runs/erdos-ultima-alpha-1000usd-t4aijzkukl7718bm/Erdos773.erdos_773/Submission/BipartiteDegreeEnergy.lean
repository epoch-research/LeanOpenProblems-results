import FormalConjecturesUtil

/-!
A scope check for sharp greedy tracking, not a disproof of Erdős 773.
Even when the error is the actual degree minus its mean, signless energy
need not dominate mean degree times variance by any positive uniform factor.
The exact examples are the complete bipartite graphs K_(k,k+1).
-/
namespace Erdos773.BipartiteDegreeEnergy
open Finset
set_option maxHeartbeats 1500000
noncomputable section

abbrev Vertex (m n : ℕ) := Fin m ⊕ Fin n

def weight {m n : ℕ} : Vertex m n → Vertex m n → ℝ
  | .inl _, .inr _ => 1
  | .inr _, .inl _ => 1
  | _, _ => 0

def degree {m n : ℕ} (u : Vertex m n) : ℝ := ∑ v, weight u v

def mean (m n : ℕ) : ℝ := 2*m*n/(m+n)

def energy (m n : ℕ) : ℝ := ∑ u : Vertex m n, (degree u-mean m n)^2

def dissipation (m n : ℕ) : ℝ :=
  (1/2:ℝ)*∑ u : Vertex m n, ∑ v : Vertex m n,
    weight u v*((degree u-mean m n)+(degree v-mean m n))^2

lemma weight_symm {m n : ℕ} (u v : Vertex m n) : weight u v = weight v u := by
  cases u <;> cases v <;> rfl

lemma weight_nonneg {m n : ℕ} (u v : Vertex m n) : 0 ≤ weight u v := by
  cases u <;> cases v <;> norm_num [weight]

@[simp] lemma degree_left {m n : ℕ} (a : Fin m) : degree (Sum.inl a : Vertex m n) = n := by
  simp [degree, Fintype.sum_sum_type, weight]

@[simp] lemma degree_right {m n : ℕ} (b : Fin n) : degree (Sum.inr b : Vertex m n) = m := by
  simp [degree, Fintype.sum_sum_type, weight]

lemma mean_eq (m n : ℕ) :
    mean m n = (∑ u : Vertex m n, degree u)/Fintype.card (Vertex m n) := by
  simp [mean, Fintype.sum_sum_type, Vertex]
  ring

lemma energy_expand (m n : ℕ) :
    energy m n = m*((n:ℝ)-mean m n)^2+n*((m:ℝ)-mean m n)^2 := by
  simp [energy, Fintype.sum_sum_type]

lemma dissipation_expand (m n : ℕ) :
    dissipation m n = m*n*((m:ℝ)+n-2*mean m n)^2 := by
  simp [dissipation, Fintype.sum_sum_type, weight]
  ring

lemma energy_formula {m n : ℕ} (h : 0 < m+n) :
    energy m n = m*n*((m:ℝ)-n)^2/(m+n) := by
  have hh : (m:ℝ)+n ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h)
  rw [energy_expand, mean]
  field_simp
  ring

lemma dissipation_formula {m n : ℕ} (h : 0 < m+n) :
    dissipation m n = m*n*((m:ℝ)-n)^4/(m+n)^2 := by
  have hh : (m:ℝ)+n ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h)
  rw [dissipation_expand, mean]
  field_simp
  ring

lemma energy_consecutive (k : ℕ) :
    energy k (k+1) = (k:ℝ)*(k+1)/(2*k+1) := by
  rw [energy_formula (by omega)]
  push_cast
  ring

lemma dissipation_consecutive (k : ℕ) :
    dissipation k (k+1) = (k:ℝ)*(k+1)/(2*k+1)^2 := by
  rw [dissipation_formula (by omega)]
  push_cast
  ring

/-- The normalized gap is exactly 1/(2k(k+1)), despite the fact that
    the test vector consists of actual centered degrees. -/
theorem normalized_gap (k : ℕ) :
    2*(k:ℝ)*(k+1)*dissipation k (k+1) = mean k (k+1)*energy k (k+1) := by
  rw [dissipation_consecutive, energy_consecutive, mean]
  push_cast
  have h : (2*(k:ℝ)+1) ≠ 0 := by positivity
  have h' : (k:ℝ)+(k+1) ≠ 0 := by positivity
  field_simp
  ring

/-- No positive universal degree-times-variance gap holds, even on
    complete bipartite graphs with degrees differing by only one. -/
theorem arbitrarily_small_gap (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 0 < k ∧ 0 < energy k (k+1) ∧
      dissipation k (k+1) < δ*mean k (k+1)*energy k (k+1) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1/δ)
  have hk0 : (0:ℝ) < k := (one_div_pos.mpr hδ).trans hk
  have hkN : 0 < k := by exact_mod_cast hk0
  have hδk : 1 < δ*k := by
    have ht := (div_lt_iff₀ hδ).mp hk
    simpa only [mul_comm] using ht
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hkN
  have hcoeff : 1 < δ*(2*(k:ℝ)*(k+1)) := by nlinarith
  have hd : 0 < dissipation k (k+1) := by
    rw [dissipation_consecutive]
    positivity
  refine ⟨k, hkN, ?_, ?_⟩
  · rw [energy_consecutive]
    positivity
  · have ht := mul_lt_mul_of_pos_right hcoeff hd
    rw [mul_assoc δ, normalized_gap] at ht
    simpa only [one_mul, mul_assoc] using ht

#print axioms mean_eq
#print axioms energy_formula
#print axioms dissipation_formula
#print axioms normalized_gap
#print axioms arbitrarily_small_gap
end
end Erdos773.BipartiteDegreeEnergy
