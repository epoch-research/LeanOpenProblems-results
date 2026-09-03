import Submission.UniformSimilaritySegments

/-!
Constant squared jump norms2^k*a^2 are excluded when every rational prime factor
of a is3 modulo4. The common similarity factor can have arbitrarily large norm.
This does not exclude mixtures of different jump norms.
-/
namespace Erdos952Investigation.InertNormStepObstruction
open SimilarityStepObstruction PowerTwoNormObstruction UniformSimilaritySegments
set_option maxHeartbeats 0

/-- All rational prime divisors remain prime in the Gaussian integers. -/
def InertSupported (a : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ a → p%4 = 3

lemma inert_supported_ne_zero {a : ℕ} (ha : InertSupported a) : a ≠ 0 := by
  intro he
  have hh := ha 2 Nat.prime_two (he ▸ dvd_zero 2)
  norm_num at hh

lemma inert_prime_dvd_of_norm {p : ℕ} (hp : p.Prime) (hp4 : p%4 = 3)
    (z : GaussianInt) (hd : (p : ℤ) ∣ z.norm) : (p : GaussianInt) ∣ z := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpG : Prime (p : GaussianInt) :=
    (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr hp4
  have hdG : (p : GaussianInt) ∣ (z.norm : GaussianInt) := by
    simpa using (Zsqrtd.intCast_dvd_intCast (p : ℤ) z.norm).mpr hd
  rw [Zsqrtd.norm_eq_mul_conj] at hdG
  rcases hpG.dvd_or_dvd hdG with h | h
  · exact h
  · have hh := map_dvd (starRingEnd GaussianInt) h
    change star (p : GaussianInt) ∣ star (star z) at hh
    simpa using hh

lemma inert_supported_coprime (a : ℕ) (ha : InertSupported a) : a.Coprime 65 := by
  have h5 : a.Coprime 5 := by
    apply Nat.Coprime.symm
    apply (Nat.prime_five.coprime_iff_not_dvd).mpr
    intro hd
    have hh := ha 5 Nat.prime_five hd
    norm_num at hh
  have h13 : a.Coprime 13 := by
    apply Nat.Coprime.symm
    apply ((by decide : Nat.Prime 13).coprime_iff_not_dvd).mpr
    intro hd
    have hh := ha 13 (by decide) hd
    norm_num at hh
  simpa using h5.mul_right h13

/-- With only inert factors and the ramified factor2 in the norm, all Gaussian
representations differ by a unit. -/
theorem norm_inert_factorization (a : ℕ) (ha : InertSupported a)
    (k : ℕ) (z : GaussianInt) (hn : z.norm = (2 : ℤ)^k*(a : ℤ)^2) :
    ∃ e : GaussianInt, e.norm = 1 ∧ z = ((a : GaussianInt)*ramified^k)*e := by
  induction a using Nat.strong_induction_on generalizing k z with
  | h a ih =>
    have ha0 := inert_supported_ne_zero ha
    by_cases ha1 : a = 1
    · subst a
      simpa using norm_two_power_factorization k z (by simpa using hn)
    obtain ⟨p,hp,hpa⟩ := Nat.exists_prime_and_dvd ha1
    have hp4 := ha p hp hpa
    obtain ⟨b,hb⟩ := hpa
    have hba : b < a := by
      have hp2 := hp.two_le
      have hb0 : 0 < b := by
        by_contra hh
        have hbz : b = 0 := by omega
        apply ha0
        simpa only [hbz,mul_zero] using hb
      rw [hb]
      nlinarith
    have hpn : (p : ℤ) ∣ z.norm := by
      refine ⟨(2 : ℤ)^k*(p : ℤ)*(b : ℤ)^2,?_⟩
      rw [hn,hb,Nat.cast_mul]
      ring
    obtain ⟨w,hw⟩ := inert_prime_dvd_of_norm hp hp4 z hpn
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hnp : (p : GaussianInt).norm = (p : ℤ)^2 := by simp [gaussian_norm_sq,pow_two]
    have hwn : w.norm = (2 : ℤ)^k*(b : ℤ)^2 := by
      rw [hw,Zsqrtd.norm_mul,hnp,hb,Nat.cast_mul] at hn
      have he : (p : ℤ)^2*w.norm = (p : ℤ)^2*((2 : ℤ)^k*(b : ℤ)^2) := by
        linear_combination hn
      exact mul_left_cancel₀ (pow_ne_zero 2 hp0) he
    have hbs : InertSupported b := by
      intro q hq hqb
      apply ha q hq
      rw [hb]
      exact dvd_mul_of_dvd_right hqb p
    obtain ⟨e,he,hwe⟩ := ih b hba hbs k w hwn
    refine ⟨e,he,?_⟩
    rw [hw,hwe,hb,Nat.cast_mul]
    ring

lemma inert_similarity_coprime (a k : ℕ) (ha : InertSupported a) :
    IsCoprime (((a : GaussianInt)*ramified^k).norm) 65 := by
  rw [Zsqrtd.norm_mul]
  have hna : (a : GaussianInt).norm = (a : ℤ)^2 := by simp [gaussian_norm_sq,pow_two]
  rw [hna]
  exact ((inert_supported_coprime a ha).isCoprime.pow_left).mul_left
    (ramified_power_coprime k)

/-- An infinite prime ray cannot have one fixed squared jump norm of the
stated form. Neither the inert factor nor the exponent is bounded. -/
theorem no_constant_inert_norm_prime_ray (a k : ℕ) (ha : InertSupported a)
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ¬ ∀ n, (x (n+1)-x n).norm = (2 : ℤ)^k*(a : ℤ)^2 := by
  intro hs
  apply no_unit_multiple_prime_ray ((a : GaussianInt)*ramified^k)
    (inert_similarity_coprime a k ha) x hx hp
  exact fun n => norm_inert_factorization a ha k _ (hs n)

/-- The same explicit finite path bound works throughout this family. -/
theorem no_3084980_constant_inert_norm_steps (a k : ℕ) (ha : InertSupported a)
    (x : ℕ → GaussianInt) (hx : Set.InjOn x (Set.Iic 3084980))
    (hp : ∀ n ≤ 3084980, Prime (x n)) :
    ¬ ∀ n < 3084980, (x (n+1)-x n).norm = (2 : ℤ)^k*(a : ℤ)^2 := by
  intro hs
  apply no_3084980_similar_prime_steps ((a : GaussianInt)*ramified^k)
    (inert_similarity_coprime a k ha) x hx hp
  exact fun n hn => norm_inert_factorization a ha k _ (hs n hn)

lemma inert_supported_prime_power {p : ℕ} (hp : p.Prime) (hp4 : p%4 = 3)
    (m : ℕ) : InertSupported (p^m) := by
  intro q hq hdiv
  have he : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdiv)
  simpa only [he] using hp4

/-- In particular, all fixed norms2^k*p^(2m), with p prime3 modulo4, are
excluded for prime rays. This is still a restriction on every jump. -/
theorem no_constant_two_inert_prime_power_norm {p : ℕ} (hp : p.Prime)
    (hp4 : p%4 = 3) (k m : ℕ) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hprime : ∀ n, Prime (x n)) :
    ¬ ∀ n, (x (n+1)-x n).norm = (2 : ℤ)^k*(p : ℤ)^(2*m) := by
  intro hs
  apply no_constant_inert_norm_prime_ray (p^m) k
    (inert_supported_prime_power hp hp4 m) x hx hprime
  intro n
  simpa only [Nat.cast_pow,← pow_mul,Nat.mul_comm m 2] using hs n

/-- A single tail index works for all inert-supported factors and exponents.
This does not prevent switching between different norms within each block. -/
theorem inert_norm_runs_eventually_break (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ∃ K : ℕ, ∀ a k : ℕ, InertSupported a → ∀ N ≥ K,
      ∃ n, N ≤ n ∧ n < N+4225 ∧
        (x (n+1)-x n).norm ≠ (2 : ℤ)^k*(a : ℤ)^2 := by
  obtain ⟨K,hK⟩ := similar_step_runs_eventually_break x hx hp
  refine ⟨K,?_⟩
  intro a k ha N hN
  obtain ⟨n,hn,hn',hno⟩ := hK ((a : GaussianInt)*ramified^k)
    (inert_similarity_coprime a k ha) N hN
  exact ⟨n,hn,hn',fun he => hno (norm_inert_factorization a ha k _ he)⟩

#print axioms inert_norm_runs_eventually_break


#print axioms norm_inert_factorization
#print axioms no_constant_inert_norm_prime_ray
#print axioms no_3084980_constant_inert_norm_steps
#print axioms no_constant_two_inert_prime_power_norm
end Erdos952Investigation.InertNormStepObstruction
