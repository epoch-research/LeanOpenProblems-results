import FormalConjecturesUtil

/-!
Uniform bounds on logarithmic blocks of primes, for a prime-ratio density approach.
These do not by themselves settle the prime-pair conjecture.
-/
namespace Erdos972LogPrimeBlocks

open Finset

noncomputable def primeWeight (ε : ℝ) (p : ℕ) : ℝ :=
  (Real.log p / p) * Real.exp (-ε * Real.log p)

lemma primeWeight_nonneg (ε : ℝ) {p : ℕ} (hp : p.Prime) : 0 ≤ primeWeight ε p := by
  apply mul_nonneg
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) (Nat.cast_nonneg p)
  · exact (Real.exp_pos _).le

lemma primeWeight_eq_div_rpow (ε : ℝ) {p : ℕ} (hp : 0 < p) :
    primeWeight ε p = Real.log p / (p : ℝ) ^ (1 + ε) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  unfold primeWeight
  rw [Real.rpow_add hpR, Real.rpow_one, Real.rpow_def_of_pos hpR ε]
  rw [show -ε * Real.log p = -(Real.log p * ε) by ring, Real.exp_neg]
  ring

/-- A uniform upper bound on the reciprocal logarithmic prime mass in any
unit interval on the logarithmic axis. -/
theorem sum_log_div_le_of_log_block (S : Finset ℕ) (x : ℝ)
    (hS : ∀ p ∈ S, p.Prime ∧ x ≤ Real.log p ∧ Real.log p ≤ x + 1) :
    (∑ p ∈ S, Real.log p / p) ≤ Real.exp 1 * Real.log 4 := by
  classical
  have hlogsum : (∑ p ∈ S, Real.log p) ≤ Chebyshev.theta (Real.exp (x + 1)) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp, _, hphi⟩ := hS p hp
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpp.pos, ?_⟩, hpp⟩
      apply Nat.le_floor
      have h := Real.exp_le_exp.mpr hphi
      rwa [Real.exp_log (Nat.cast_pos.mpr hpp.pos)] at h
    · intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
  calc
    _ ≤ ∑ p ∈ S, Real.exp (-x) * Real.log p := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpp, hx, _⟩ := hS p hp
      have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hpp.pos
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
      have hinv : (p : ℝ)⁻¹ ≤ Real.exp (-x) := by
        rw [Real.exp_neg]
        apply inv_le_inv₀ hpR (Real.exp_pos _) |>.mpr
        have h := Real.exp_le_exp.mpr hx
        rwa [Real.exp_log hpR] at h
      simpa only [div_eq_mul_inv, mul_comm (Real.exp (-x))] using
        mul_le_mul_of_nonneg_left hinv hlogp
    _ = Real.exp (-x) * ∑ p ∈ S, Real.log p := by rw [mul_sum]
    _ ≤ Real.exp (-x) * Chebyshev.theta (Real.exp (x + 1)) :=
      mul_le_mul_of_nonneg_left hlogsum (Real.exp_pos _).le
    _ ≤ Real.exp (-x) * (Real.log 4 * Real.exp (x + 1)) :=
      mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Real.exp_pos _).le)
        (Real.exp_pos _).le
    _ = _ := by
      rw [show Real.exp (-x) * (Real.log 4 * Real.exp (x + 1)) =
        (Real.exp (-x) * Real.exp (x + 1)) * Real.log 4 by ring,
        ← Real.exp_add, show -x + (x + 1) = 1 by ring]

lemma sum_primeWeight_le_of_log_block {ε : ℝ} (hε : 0 ≤ ε)
    (S : Finset ℕ) (x : ℝ)
    (hS : ∀ p ∈ S, p.Prime ∧ x ≤ Real.log p ∧ Real.log p ≤ x + 1) :
    (∑ p ∈ S, primeWeight ε p) ≤ Real.exp 1 * Real.log 4 * Real.exp (-ε * x) := by
  calc
    _ ≤ ∑ p ∈ S, (Real.log p / p) * Real.exp (-ε * x) := by
      apply sum_le_sum
      intro p hp
      have h := hS p hp
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left h.2.1 (neg_nonpos.mpr hε)
      · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h.1.one_le)) (Nat.cast_nonneg p)
    _ = (∑ p ∈ S, Real.log p / p) * Real.exp (-ε * x) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_log_div_le_of_log_block S x hS) (Real.exp_pos _).le

/-- A cutoff on the logarithmic prime size gives an exponentially small tail,
uniformly in the finite set of primes being summed. -/
theorem sum_primeWeight_tail_le {ε : ℝ} (hε : 0 < ε) (S : Finset ℕ) (L : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ (L : ℝ) ≤ Real.log p) :
    (∑ p ∈ S, primeWeight ε p) ≤
      Real.exp 1 * Real.log 4 * Real.exp (-ε * L) / (1 - Real.exp (-ε)) := by
  classical
  let g : ℕ → ℕ := fun p => ⌊Real.log p⌋₊ - L
  let T := S.image g
  have hgeom0 : 0 ≤ Real.exp (-ε) := (Real.exp_pos _).le
  have hgeom1 : Real.exp (-ε) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hsum := (summable_geometric_of_lt_one hgeom0 hgeom1).mul_left
    (Real.exp 1 * Real.log 4 * Real.exp (-ε * L))
  calc
    _ = ∑ k ∈ T, ∑ p ∈ S.filter (fun p => g p = k), primeWeight ε p := by
      symm
      exact sum_fiberwise_of_maps_to (fun p hp => mem_image.mpr ⟨p, hp, rfl⟩) _
    _ ≤ ∑ k ∈ T, Real.exp 1 * Real.log 4 * Real.exp (-ε * (L + k : ℕ)) := by
      apply sum_le_sum
      intro k _
      apply sum_primeWeight_le_of_log_block hε.le
      intro p hp
      obtain ⟨hp, he⟩ := mem_filter.mp hp
      obtain ⟨hpp, hLp⟩ := hS p hp
      have hLfloor : L ≤ ⌊Real.log p⌋₊ := Nat.le_floor hLp
      have heq : L + k = ⌊Real.log p⌋₊ := by dsimp [g] at he; omega
      rw [heq]
      refine ⟨hpp, Nat.floor_le (Real.log_nonneg (by exact_mod_cast hpp.one_le)), ?_⟩
      exact (Nat.lt_floor_add_one _).le
    _ = ∑ k ∈ T, (Real.exp 1 * Real.log 4 * Real.exp (-ε * L)) * Real.exp (-ε) ^ k := by
      apply sum_congr rfl
      intro k _
      rw [Nat.cast_add, mul_add, Real.exp_add,
        show -ε * (k : ℝ) = (k : ℝ) * (-ε) by ring, Real.exp_nat_mul]
      ring
    _ ≤ ∑' k : ℕ, (Real.exp 1 * Real.log 4 * Real.exp (-ε * L)) * Real.exp (-ε) ^ k :=
      hsum.sum_le_tsum T (fun k _ => by positivity)
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hgeom0 hgeom1]
      rfl

lemma primeWeight_le_log_div {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : p.Prime) :
    primeWeight ε p ≤ Real.log p / p := by
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have he : Real.exp (-ε * Real.log p) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he
    (div_nonneg hl (Nat.cast_nonneg p))

lemma summable_lorentz : Summable (fun k : ℤ => 1 / (1 + (k : ℝ) ^ 2)) := by
  have hp := Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)
  have hd := (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  apply (hp.add hd).of_nonneg_of_le (fun k => by positivity)
  intro k
  by_cases hk : k = 0
  · subst k
    norm_num
  · simp only [if_neg hk, add_zero]
    apply one_div_le_one_div_of_le
    · exact sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hk)
    · linarith

noncomputable def lorentzMass : ℝ := ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)

lemma lorentzMass_nonneg : 0 ≤ lorentzMass := tsum_nonneg (fun k => by positivity)

lemma lorentz_le_of_floor {x : ℝ} {k : ℤ} (hk : ⌊x⌋ = k) :
    1 / (1 + x ^ 2) ≤ 3 / (1 + (k : ℝ) ^ 2) := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  rw [hk] at hlo hhi
  have hd : (x - (k : ℝ)) ^ 2 ≤ 1 := by nlinarith
  have hs := sq_nonneg (2 * x - (k : ℝ))
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg x]

/-- Uniform control of the prime mass against a decaying kernel centered anywhere
on the logarithmic axis. This is the row bound needed in a two-prime kernel energy. -/
theorem sum_primeWeight_lorentz_le {ε : ℝ} (hε : 0 ≤ ε)
    (S : Finset ℕ) (c : ℝ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, primeWeight ε p / (1 + (Real.log p - c) ^ 2)) ≤
      3 * (Real.exp 1 * Real.log 4) * lorentzMass := by
  classical
  let g : ℕ → ℤ := fun p => ⌊Real.log p - c⌋
  let T := S.image g
  have hfiber (k : ℤ) :
      (∑ p ∈ S.filter (fun p => g p = k), primeWeight ε p / (1 + (Real.log p - c) ^ 2)) ≤
        (3 * (Real.exp 1 * Real.log 4)) * (1 / (1 + (k : ℝ) ^ 2)) := by
    let U := S.filter (fun p => g p = k)
    have hU (p : ℕ) (hp : p ∈ U) :
        p.Prime ∧ c + k ≤ Real.log p ∧ Real.log p ≤ (c + k) + 1 := by
      obtain ⟨hpS, he⟩ := mem_filter.mp hp
      have hlo := Int.floor_le (Real.log p - c)
      have hhi := Int.lt_floor_add_one (Real.log p - c)
      change ⌊Real.log p - c⌋ = k at he
      rw [he] at hlo hhi
      exact ⟨hS p hpS, by linarith, by linarith⟩
    calc
      _ ≤ ∑ p ∈ U, (Real.log p / p) * (3 / (1 + (k : ℝ) ^ 2)) := by
        apply sum_le_sum
        intro p hp
        have hpp := (hU p hp).1
        have he : ⌊Real.log p - c⌋ = k := (mem_filter.mp hp).2
        calc
          _ ≤ (Real.log p / p) / (1 + (Real.log p - c) ^ 2) :=
            div_le_div_of_nonneg_right (primeWeight_le_log_div hε hpp) (by positivity)
          _ ≤ _ := by
            rw [div_eq_mul_inv, ← one_div]
            exact mul_le_mul_of_nonneg_left (lorentz_le_of_floor he)
              (div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (Nat.cast_nonneg p))
      _ = (∑ p ∈ U, Real.log p / p) * (3 / (1 + (k : ℝ) ^ 2)) := by rw [sum_mul]
      _ ≤ (Real.exp 1 * Real.log 4) * (3 / (1 + (k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right (sum_log_div_le_of_log_block U (c + k) hU) (by positivity)
      _ = _ := by ring
  calc
    _ = ∑ k ∈ T, ∑ p ∈ S.filter (fun p => g p = k),
        primeWeight ε p / (1 + (Real.log p - c) ^ 2) := by
      symm
      exact sum_fiberwise_of_maps_to (fun p hp => mem_image.mpr ⟨p, hp, rfl⟩) _
    _ ≤ ∑ k ∈ T, (3 * (Real.exp 1 * Real.log 4)) * (1 / (1 + (k : ℝ) ^ 2)) :=
      sum_le_sum (fun k _ => hfiber k)
    _ ≤ ∑' k : ℤ, (3 * (Real.exp 1 * Real.log 4)) * (1 / (1 + (k : ℝ) ^ 2)) :=
      (summable_lorentz.mul_left _).sum_le_tsum T (fun k _ => by positivity)
    _ = _ := by rw [tsum_mul_left]; rfl

#print axioms sum_primeWeight_lorentz_le
#print axioms sum_log_div_le_of_log_block
#print axioms sum_primeWeight_tail_le

end Erdos972LogPrimeBlocks
