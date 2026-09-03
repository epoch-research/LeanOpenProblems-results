import FormalConjecturesUtil
import Submission.TwoLinearSieve

/-! Bounds for the Euler product and the exceptional coefficient weight in
  the finite two-linear-form sieve. These do not imply orientation balance. -/

namespace Erdos371SieveEulerProduct

open Finset Erdos371TwoLinearSieve

attribute [local instance] Classical.propDecidable

noncomputable def euler (s : Finset ℕ) : ℝ := ∏ p ∈ s, (1 - 1/(p:ℝ))
noncomputable def weight (s : Finset ℕ) (m : ℕ) : ℝ :=
  ∏ p ∈ s, if p ∣ m then (1 - 1/(p:ℝ))⁻¹ else 1

lemma prime_factor_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1/(p:ℝ) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hp1)

lemma prime_factor_le_one {p : ℕ} : 1 - 1/(p:ℝ) ≤ 1 := by
  have : 0 ≤ 1/(p:ℝ) := by positivity
  linarith

lemma euler_pos {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) : 0 < euler s :=
  Finset.prod_pos (fun p hp => prime_factor_pos (hs p hp))

lemma weight_nonneg {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (m : ℕ) :
    0 ≤ weight s m := by
  apply Finset.prod_nonneg
  intro p hp
  split_ifs
  · exact inv_nonneg.mpr (prime_factor_pos (hs p hp)).le
  · norm_num

noncomputable def reciprocal : ℕ →* ℝ where
  toFun n := (n:ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by simp [mul_inv_rev, mul_comm]

lemma reciprocal_prime_norm {p : ℕ} (hp : p.Prime) : ‖reciprocal p‖ < 1 := by
  change ‖(p:ℝ)⁻¹‖ < 1
  rw [Real.norm_of_nonneg (by positivity), inv_lt_one₀ (by exact_mod_cast hp.pos)]
  exact_mod_cast hp.one_lt

lemma harmonic_le_inverse_euler (N : ℕ) :
    (harmonic N : ℝ) ≤ (euler (N+1).primesBelow)⁻¹ := by
  have hh := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    reciprocal_prime_norm (N+1)).2
  let f : {m // m ∈ Finset.Icc 1 N} ↪ (N+1).smoothNumbers :=
    ⟨fun m => ⟨m.val, Nat.mem_smoothNumbers_of_lt
      (by have := (Finset.mem_Icc.mp m.property).1; omega)
      (by have := (Finset.mem_Icc.mp m.property).2; omega)⟩,
      fun a b h => Subtype.ext (congrArg (fun x : (N+1).smoothNumbers => x.val) h)⟩
  have hsum := sum_le_hasSum ((Finset.Icc 1 N).attach.map f)
    (fun m _ => show 0 ≤ reciprocal m.val from by change 0 ≤ (m.val:ℝ)⁻¹; positivity) hh
  have heq : (∑ x ∈ (Finset.Icc 1 N).attach, ((x.val:ℕ):ℝ)⁻¹) =
      ∑ x ∈ Finset.Icc 1 N, (x:ℝ)⁻¹ := Finset.sum_attach (Finset.Icc 1 N) (fun n : ℕ => (n:ℝ)⁻¹)
  simpa [Finset.sum_map, f, reciprocal, harmonic_eq_sum_Icc,
    ← Finset.prod_inv_distrib, euler, one_div, heq] using hsum

lemma log_le_inverse_euler {N : ℕ} (hN : 0 < N) :
    Real.log N ≤ (euler N.primesBelow)⁻¹ := by
  have h1 := log_add_one_le_harmonic (N-1)
  have h2 := harmonic_le_inverse_euler (N-1)
  have he : N-1+1=N := by omega
  rw [he] at h1 h2
  exact h1.trans h2

lemma euler_le_inverse_log {N : ℕ} (hN : 1 < N) :
    euler N.primesBelow ≤ 1 / Real.log N := by
  have he : 0 < euler N.primesBelow := euler_pos (fun p hp => (Nat.mem_primesBelow.mp hp).2)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have h := log_le_inverse_euler (by omega : 0<N)
  apply (le_div_iff₀ hl).mpr
  have hh := mul_le_mul_of_nonneg_right h he.le
  rw [inv_mul_cancel₀ (ne_of_gt he)] at hh
  nlinarith

lemma local_product_bound {p a c : ℕ} (hp : p.Prime) :
    1 - linearDensity a c p ≤
      (1-1/(p:ℝ))^2 * (if p ∣ a*c then (1-1/(p:ℝ))⁻¹ else 1) := by
  have hpos := prime_factor_pos hp
  unfold linearDensity
  by_cases h : p ∣ a*c
  · simp only [if_pos h]
    rw [sq, mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
  · simp only [if_neg h, mul_one]
    simp only [div_eq_mul_inv, one_mul]
    nlinarith [sq_nonneg ((p:ℝ)⁻¹)]

lemma linearDensity_nonneg {p a c : ℕ} : 0 ≤ linearDensity a c p := by
  unfold linearDensity
  split_ifs <;> positivity

lemma linearDensity_le_one {p a c : ℕ} (hp : p.Prime) : linearDensity a c p ≤ 1 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold linearDensity
  split_ifs <;> apply (div_le_one hp0).mpr <;> linarith

lemma linearDensity_le_two_div {p a c : ℕ} : linearDensity a c p ≤ 2/(p:ℝ) := by
  unfold linearDensity
  split_ifs
  · exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  · rfl

lemma linear_euler_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (a c : ℕ) :
    (∏ p ∈ s, (1-linearDensity a c p)) ≤ (euler s)^2 * weight s (a*c) := by
  calc
    _ ≤ ∏ p ∈ s, (1-1/(p:ℝ))^2 *
        (if p ∣ a*c then (1-1/(p:ℝ))⁻¹ else 1) := by
      exact Finset.prod_le_prod (fun p hp => sub_nonneg.mpr (linearDensity_le_one (hs p hp)))
        (fun p hp => local_product_bound (hs p hp))
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow]; rfl

lemma weight_mul_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (a c : ℕ) :
    weight s (a*c) ≤ weight s a * weight s c := by
  unfold weight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    split_ifs <;> first | exact inv_nonneg.mpr (prime_factor_pos (hs p hp)).le | norm_num
  · intro p hp
    have hd : p ∣ a*c ↔ p ∣ a ∨ p ∣ c := (hs p hp).dvd_mul
    have hpos := prime_factor_pos (hs p hp)
    have hinv : 1 ≤ (1-1/(p:ℝ))⁻¹ := (one_le_inv₀ hpos).mpr prime_factor_le_one
    by_cases ha : p ∣ a <;> by_cases hc : p ∣ c
    · simp only [ha, hc, hd, true_or, if_true]
      nlinarith
    · simp [ha, hc, hd]
    · simp [ha, hc, hd]
    · simp [ha, hc, hd]

lemma product_dvd_iff {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (m : ℕ) :
    (∏ p ∈ s, p) ∣ m ↔ ∀ p ∈ s, p ∣ m := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      have hsp := hs p (Finset.mem_insert_self _ _)
      have hss : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hc : p.Coprime (∏ q ∈ s, q) := Nat.coprime_prod_right_iff.mpr (by
        intro q hq
        exact (Nat.coprime_primes hsp (hss q hq)).mpr (fun he => hp (he ▸ hq)))
      rw [Finset.prod_insert hp]
      exact hc.mul_dvd_of_dvd_of_dvd (h p (Finset.mem_insert_self _ _))
        (ih hss (fun q hq => h q (Finset.mem_insert_of_mem hq)))

lemma inverse_prime_factor_eq {p : ℕ} (hp : p.Prime) :
    (1-1/(p:ℝ))⁻¹ = 1+1/((p:ℝ)-1) := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hp0 : (p:ℝ) ≠ 0 := by linarith
  have hpm : (p:ℝ)-1 ≠ 0 := by linarith
  have hpf : 1-1/(p:ℝ) ≠ 0 := ne_of_gt (prime_factor_pos hp)
  field_simp
  <;> ring

lemma weight_expansion {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (m : ℕ) :
    weight s m = ∑ t ∈ s.powerset,
      if (∏ p ∈ t, p) ∣ m then ∏ p ∈ t, 1/((p:ℝ)-1) else 0 := by
  calc
    _ = ∏ p ∈ s, (1 + if p ∣ m then 1/((p:ℝ)-1) else 0) := by
      apply Finset.prod_congr rfl
      intro p hp
      split_ifs
      · exact inverse_prime_factor_eq (hs p hp)
      · simp
    _ = ∑ t ∈ s.powerset, ∏ p ∈ t, if p ∣ m then 1/((p:ℝ)-1) else 0 :=
      Finset.prod_one_add _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_ite_zero]
      have he := product_dvd_iff (fun p hp => hs p (Finset.mem_powerset.mp ht hp)) m
      simp only [he]

lemma mean_weight_le_product {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (A : ℕ) :
    (∑ m ∈ Finset.range A, weight s (m+1)) ≤
      (A:ℝ) * ∏ p ∈ s, (1+1/((p:ℝ)*((p:ℝ)-1))) := by
  simp_rw [weight_expansion hs]
  rw [Finset.sum_comm, Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have htprime : ∀ p ∈ t, p.Prime := fun p hp => hs p (Finset.mem_powerset.mp ht hp)
  have hnonneg : 0 ≤ ∏ p ∈ t, 1/((p:ℝ)-1) := by
    apply Finset.prod_nonneg
    intro p hp
    have : (1:ℝ) < p := by exact_mod_cast (htprime p hp).one_lt
    have : 0 < (p:ℝ)-1 := by linarith
    positivity
  calc
    _ = ((A / (∏ p ∈ t, p) : ℕ):ℝ) * (∏ p ∈ t, 1/((p:ℝ)-1)) := by
      rw [← Finset.sum_filter]
      simp [Nat.card_multiples]
    _ ≤ ((A:ℝ)/(∏ p ∈ t, p : ℕ)) * (∏ p ∈ t, 1/((p:ℝ)-1)) :=
      mul_le_mul_of_nonneg_right Nat.cast_div_le hnonneg
    _ = (A:ℝ) * ∏ p ∈ t, 1/((p:ℝ)*((p:ℝ)-1)) := by
      push_cast
      simp only [one_div, mul_inv_rev, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      ring

lemma reciprocal_adjacent_sum_le_one (M : ℕ) :
    (∑ n ∈ Finset.range M, 1/(((n:ℝ)+1)*((n:ℝ)+2))) ≤ 1 := by
  have he (n : ℕ) : 1/(((n:ℝ)+1)*((n:ℝ)+2)) =
      1/((n:ℝ)+1) - 1/((n:ℝ)+2) := by
    field_simp
    <;> ring
  simp_rw [he]
  have hh := Finset.sum_range_sub' (fun n : ℕ => 1/((n:ℝ)+1)) M
  simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] at hh
  rw [hh]
  have : 0 ≤ 1/((M:ℝ)+1) := by positivity
  norm_num at *
  linarith

lemma prime_correction_sum_le_one {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, 1/((p:ℝ)*((p:ℝ)-1))) ≤ 1 := by
  let t := s.image (fun p => p-2)
  have heq : (∑ p ∈ s, 1/((p:ℝ)*((p:ℝ)-1))) =
      ∑ n ∈ t, 1/(((n:ℝ)+1)*((n:ℝ)+2)) := by
    rw [show t=s.image (fun p => p-2) from rfl, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      have h2 : 2 ≤ p := (hs p hp).two_le
      have he : ((p-2:ℕ):ℝ) = (p:ℝ)-2 := by norm_cast
      rw [he]
      congr 1
      ring
    · intro p hp q hq he
      have := (hs p hp).two_le
      have := (hs q hq).two_le
      change p-2 = q-2 at he
      omega
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Finset.range (s.sup id + 1), 1/(((n:ℝ)+1)*((n:ℝ)+2)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
        have hle : p ≤ s.sup id := Finset.le_sup (f := id) hp
        apply Finset.mem_range.mpr
        omega
      · intro n _ _
        positivity
    _ ≤ 1 := reciprocal_adjacent_sum_le_one _

lemma prime_correction_product_le_exp_one {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, (1+1/((p:ℝ)*((p:ℝ)-1)))) ≤ Real.exp 1 := by
  calc
    _ ≤ ∏ p ∈ s, Real.exp (1/((p:ℝ)*((p:ℝ)-1))) := by
      apply Finset.prod_le_prod
      · intro p hp
        have : (1:ℝ)<p := by exact_mod_cast (hs p hp).one_lt
        have : 0 < (p:ℝ)-1 := by linarith
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (1/((p:ℝ)*((p:ℝ)-1)))
    _ = Real.exp (∑ p ∈ s, 1/((p:ℝ)*((p:ℝ)-1))) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (prime_correction_sum_le_one hs)

/-- The average exceptional coefficient weight is bounded uniformly in the
  sieving primes. Positivity of the coefficient is essential here. -/
theorem mean_weight_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (A : ℕ) :
    (∑ m ∈ Finset.range A, weight s (m+1)) ≤ Real.exp 1 * A := by
  calc
    _ ≤ (A:ℝ) * ∏ p ∈ s, (1+1/((p:ℝ)*((p:ℝ)-1))) := mean_weight_le_product hs A
    _ ≤ (A:ℝ) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (prime_correction_product_le_exp_one hs) (by positivity)
    _ = _ := by ring

end Erdos371SieveEulerProduct

#print axioms Erdos371SieveEulerProduct.harmonic_le_inverse_euler
#print axioms Erdos371SieveEulerProduct.linear_euler_le
#print axioms Erdos371SieveEulerProduct.weight_mul_le

#print axioms Erdos371SieveEulerProduct.mean_weight_le
