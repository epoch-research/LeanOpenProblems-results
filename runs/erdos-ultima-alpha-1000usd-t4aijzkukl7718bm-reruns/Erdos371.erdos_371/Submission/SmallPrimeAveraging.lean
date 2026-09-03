import FormalConjecturesUtil
import Submission.PrimeDiscrepancy

/-! A finite small-prime second-moment averaging tool. This does not assert
cancellation of the prime-divisor-weighted signed correlation. -/

namespace Erdos371SmallPrimeAveraging

open Filter
open scoped Topology

noncomputable def mean (f : ℕ → ℝ) (N : ℕ) : ℝ := (∑ n ∈ Finset.range N, f n) / N

def ind (p n : ℕ) : ℝ := if p ∣ n+1 then 1 else 0

noncomputable def mass (s : Finset ℕ) : ℝ := ∑ p ∈ s, 1 / (p:ℝ)
def smallCount (s : Finset ℕ) (n : ℕ) : ℝ := ∑ p ∈ s, ind p n

noncomputable def varianceMean (s : Finset ℕ) (N : ℕ) : ℝ :=
  mean (fun n => (smallCount s n - mass s)^2) N

lemma mean_add (f g : ℕ → ℝ) (N : ℕ) :
    mean (fun n => f n + g n) N = mean f N + mean g N := by
  simp [mean, Finset.sum_add_distrib, add_div]

lemma mean_sub (f g : ℕ → ℝ) (N : ℕ) :
    mean (fun n => f n - g n) N = mean f N - mean g N := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

lemma mean_const_mul (c : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    mean (fun n => c * f n) N = c * mean f N := by
  simp [mean, ← Finset.mul_sum, mul_div_assoc]

lemma mean_const (c : ℝ) {N : ℕ} (hN : 0 < N) : mean (fun _ => c) N = c := by
  simp [mean, Nat.cast_ne_zero.mpr hN.ne']

lemma mean_sum (s : Finset ℕ) (f : ℕ → ℕ → ℝ) (N : ℕ) :
    mean (fun n => ∑ p ∈ s, f p n) N = ∑ p ∈ s, mean (f p) N := by
  simp only [mean, Finset.sum_comm (s := Finset.range N), Finset.sum_div]

lemma mean_ind (p N : ℕ) : mean (ind p) N = ((N/p:ℕ):ℝ) / N := by
  simp only [mean, ind]
  rw [Finset.sum_boole, Nat.card_multiples]

lemma mean_ind_tendsto {p : ℕ} (hp : 0 < p) :
    Tendsto (mean (ind p)) atTop (𝓝 (1/(p:ℝ))) := by
  have hp' : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hl : Tendsto (fun N : ℕ => 1/(p:ℝ) - 1/(N:ℝ)) atTop (𝓝 (1/(p:ℝ))) := by
    simpa using (tendsto_const_nhds (x := 1/(p:ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with N hN
    rw [mean_ind]
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
    have hr : ((N%p:ℕ):ℝ) ≤ p := Nat.cast_le.mpr (Nat.mod_lt N hp).le
    have he : (p:ℝ) * (N/p:ℕ) + (N%p:ℕ) = N := by exact_mod_cast Nat.div_add_mod N p
    have hd : (N:ℝ)/p - 1 ≤ (N/p:ℕ) := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hp').mpr
      nlinarith
    calc
      _ = ((N:ℝ)/p - 1) / N := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hd hn.le
  · filter_upwards [eventually_gt_atTop 0] with N hN
    rw [mean_ind]
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
    calc
      _ ≤ ((N:ℝ)/p) / N := div_le_div_of_nonneg_right Nat.cast_div_le hn.le
      _ = _ := by field_simp

lemma ind_product_of_coprime {p q : ℕ} (hpq : p.Coprime q) (n : ℕ) :
    ind p n * ind q n = ind (p*q) n := by
  have he : p*q ∣ n+1 ↔ p ∣ n+1 ∧ q ∣ n+1 :=
    ⟨fun h => ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩,
      fun h => hpq.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  simp only [ind, he]
  split_ifs <;> simp_all

lemma ind_square (p n : ℕ) : ind p n * ind p n = ind p n := by
  unfold ind
  split_ifs <;> norm_num

lemma mean_ind_product_tendsto {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Tendsto (mean (fun n => ind p n * ind q n)) atTop
      (𝓝 (if p=q then 1/(p:ℝ) else (1/(p:ℝ))*(1/(q:ℝ)))) := by
  by_cases he : p=q
  · subst q
    simp only [ind_square, if_true]
    exact mean_ind_tendsto hp.pos
  · simp only [if_neg he]
    have hc := (Nat.coprime_primes hp hq).mpr he
    simp only [ind_product_of_coprime hc]
    simpa [Nat.cast_mul, one_div, mul_inv, mul_comm] using mean_ind_tendsto (Nat.mul_pos hp.pos hq.pos)

lemma mean_centered_product_tendsto {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Tendsto (mean (fun n => (ind p n - 1/(p:ℝ)) * (ind q n - 1/(q:ℝ)))) atTop
      (𝓝 (if p=q then 1/(p:ℝ) - (1/(p:ℝ))^2 else 0)) := by
  have hh := (((mean_ind_product_tendsto hp hq).sub
    ((tendsto_const_nhds (x := 1/(q:ℝ))).mul (mean_ind_tendsto hp.pos))).sub
    ((tendsto_const_nhds (x := 1/(p:ℝ))).mul (mean_ind_tendsto hq.pos))).add
      (tendsto_const_nhds (x := (1/(p:ℝ))*(1/(q:ℝ))))
  have he : (if p=q then 1/(p:ℝ) else (1/(p:ℝ))*(1/(q:ℝ))) -
      (1/(q:ℝ))*(1/(p:ℝ)) - (1/(p:ℝ))*(1/(q:ℝ)) + (1/(p:ℝ))*(1/(q:ℝ)) =
      (if p=q then 1/(p:ℝ) - (1/(p:ℝ))^2 else 0) := by
    split_ifs with h
    · subst q; ring
    · ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  change _ = mean (fun n => (ind p n - 1/(p:ℝ)) * (ind q n - 1/(q:ℝ))) N
  rw [← mean_const ((1/(p:ℝ))*(1/(q:ℝ))) hN, ← mean_const_mul, ← mean_const_mul, ← mean_sub, ← mean_sub, ← mean_add]
  congr 1
  funext n
  ring

lemma varianceMean_eq (s : Finset ℕ) (N : ℕ) : varianceMean s N =
    ∑ p ∈ s, ∑ q ∈ s,
      mean (fun n => (ind p n - 1/(p:ℝ)) * (ind q n - 1/(q:ℝ))) N := by
  have he (n : ℕ) : (smallCount s n - mass s)^2 =
      ∑ p ∈ s, ∑ q ∈ s, (ind p n - 1/(p:ℝ)) * (ind q n - 1/(q:ℝ)) := by
    rw [smallCount, mass, ← Finset.sum_sub_distrib, pow_two, Finset.sum_mul_sum]
  simp only [varianceMean, he, mean_sum]

lemma varianceMean_tendsto (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Tendsto (varianceMean s) atTop (𝓝 (∑ p ∈ s, (1/(p:ℝ) - (1/(p:ℝ))^2))) := by
  change Tendsto (fun N => varianceMean s N) _ _
  simp only [varianceMean_eq]
  have hh := tendsto_finset_sum s (fun p hp => tendsto_finset_sum s
    (fun q hq => mean_centered_product_tendsto (hs p hp) (hs q hq)))
  simpa using hh

lemma variance_limit_le_mass (s : Finset ℕ) :
    (∑ p ∈ s, (1/(p:ℝ) - (1/(p:ℝ))^2)) ≤ mass s := by
  apply Finset.sum_le_sum
  intro p hp
  nlinarith [sq_nonneg (1/(p:ℝ))]

lemma averaging_square_bound (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (N : ℕ) :
    (mass s * mean f N - mean (fun n => f n * smallCount s n) N)^2 ≤
      varianceMean s N := by
  by_cases hN : N = 0
  · subst N
    simp [mean, varianceMean]
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  let g : ℕ → ℝ := fun n => f n * (mass s - smallCount s n)
  have he : mass s * mean f N - mean (fun n => f n * smallCount s n) N = mean g N := by
    rw [← mean_const_mul, ← mean_sub]
    congr 1
    funext n
    dsimp [g]
    ring
  rw [he]
  have hpt (n : ℕ) : (g n)^2 ≤ (smallCount s n - mass s)^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg (f n)) (hf n)
    have hfsq : (f n)^2 ≤ 1 := by nlinarith [sq_abs (f n)]
    calc
      (g n)^2 = (f n)^2 * (mass s - smallCount s n)^2 := by dsimp [g]; ring
      _ ≤ 1 * (mass s - smallCount s n)^2 :=
        mul_le_mul_of_nonneg_right hfsq (sq_nonneg _)
      _ = _ := by ring
  have hsum : (∑ n ∈ Finset.range N, g n)^2 ≤
      (N:ℝ) * ∑ n ∈ Finset.range N, (smallCount s n - mass s)^2 := by
    have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := g)
    simp only [Finset.card_range] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => hpt n)) hn.le)
  unfold varianceMean mean
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  convert hsum using 1
  field_simp

lemma signed_averaging_square_bound (s : Finset ℕ) (N : ℕ) :
    (mass s * ((Erdos371PrimeDiscrepancy.total N:ℤ):ℝ) / N -
      mean (fun n => (Erdos371PrimeDiscrepancy.sign n:ℝ) * smallCount s n) N)^2 ≤
      varianceMean s N := by
  have hs (n : ℕ) : |(Erdos371PrimeDiscrepancy.sign n:ℝ)| ≤ 1 := by
    unfold Erdos371PrimeDiscrepancy.sign
    split_ifs <;> norm_num
  convert averaging_square_bound s (fun n => (Erdos371PrimeDiscrepancy.sign n:ℝ)) hs N using 1
  simp [mean, Erdos371PrimeDiscrepancy.total, mul_div_assoc]

lemma weighted_mean_decomposition (s : Finset ℕ) (f : ℕ → ℝ) (N : ℕ) :
    mean (fun n => f n * smallCount s n) N =
      ∑ p ∈ s, mean (fun n => if p ∣ n+1 then f n else 0) N := by
  simp only [smallCount, Finset.mul_sum, mean_sum]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  funext n
  simp [ind]

/-- The variance bound controls the error of prime-divisor weighting. It does
not say that the weighted mean itself vanishes. -/
lemma averaging_limit_constraint (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) {a b : ℝ}
    (ha : Tendsto (mean f) atTop (𝓝 a))
    (hb : Tendsto (mean (fun n => f n * smallCount s n)) atTop (𝓝 b)) :
    (mass s * a - b)^2 ≤ mass s := by
  have ht : Tendsto (fun N => (mass s * mean f N - mean (fun n => f n * smallCount s n) N)^2)
      atTop (𝓝 ((mass s * a - b)^2)) := ((tendsto_const_nhds.mul ha).sub hb).pow 2
  exact (le_of_tendsto_of_tendsto ht (varianceMean_tendsto s hs)
    (Eventually.of_forall (averaging_square_bound s f hf))).trans (variance_limit_le_mass s)

end Erdos371SmallPrimeAveraging

#print axioms Erdos371SmallPrimeAveraging.varianceMean_tendsto
#print axioms Erdos371SmallPrimeAveraging.signed_averaging_square_bound
#print axioms Erdos371SmallPrimeAveraging.averaging_limit_constraint

