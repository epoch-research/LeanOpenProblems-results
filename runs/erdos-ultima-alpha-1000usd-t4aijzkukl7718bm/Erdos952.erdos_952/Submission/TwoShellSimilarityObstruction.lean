import Submission.Sieve729Sharp
import Submission.InertNormStepObstruction

/-! Similarity transfer of the six-prime king-step barrier. This excludes
mixtures of two consecutive power-of-two squared jump norms, but not arbitrary
bounded mixtures. -/
namespace Erdos952Investigation.TwoShellSimilarityObstruction
open PowerTwoNormObstruction Sieve729
set_option maxHeartbeats 0

lemma norm_add_int_mul (M : ℤ) (z w : GaussianInt) :
    (z+(M : GaussianInt)*w).norm ≡ z.norm [ZMOD M] := by
  have hr : (z+(M : GaussianInt)*w).re ≡ z.re [ZMOD M] := by
    simp only [Zsqrtd.re_add,Zsqrtd.re_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast,
      zero_mul,mul_zero,add_zero]
    change (z.re+M*w.re)%M = z.re%M
    simp
  have hi : (z+(M : GaussianInt)*w).im ≡ z.im [ZMOD M] := by
    simp only [Zsqrtd.im_add,Zsqrtd.im_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast,
      zero_mul,mul_zero,add_zero]
    change (z.im+M*w.im)%M = z.im%M
    simp
  simpa only [gaussian_norm_sq] using (hr.pow 2).add (hi.pow 2)

lemma ramified_ne_zero : ramified ≠ 0 := by decide

/-- The transfer preserves only the required norm residues, not primality. -/
theorem no_small_multiple_allowed_ray (g : GaussianInt)
    (hg : IsCoprime g.norm (period : ℤ))
    (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (ha : ∀ n (j : Fin 6), (x n).norm % (prime j : ℤ) ≠ 0) :
    ¬ ∀ n, ∃ e : GaussianInt, e.norm ≤ 2 ∧ x (n+1)-x n = g*e := by
  intro hs
  choose e he hstep using hs
  obtain ⟨a,b,hab⟩ := hg
  let q (n : ℕ) : GaussianInt := ∑ i ∈ Finset.range n, e i
  have hq0 : q 0 = 0 := by simp [q]
  have hqS (n : ℕ) : q (n+1) = q n+e n := by simp [q,Finset.sum_range_succ]
  have hform (n : ℕ) : x n = x 0+g*q n := by
    induction n with
    | zero => rw [hq0]; ring
    | succ n ih =>
      calc
        x (n+1) = x n+g*e n := by linear_combination hstep n
        _ = x 0+g*q (n+1) := by rw [ih,hqS]; ring
  let t : GaussianInt := (a : GaussianInt)*star g*x 0
  let y (n : ℕ) : GaussianInt := (period : GaussianInt)+ramified*(t+q n)
  have hyodd (n : ℕ) : ((y n).re+(y n).im)%2 = 1 := by
    simp only [y,ramified,Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_mul,
      Zsqrtd.im_mul,Zsqrtd.re_natCast,Zsqrtd.im_natCast]
    norm_num [period]
    omega
  have hrel (n : ℕ) : g*y n = ramified*x n+(period : GaussianInt)*
      (g-(b : GaussianInt)*ramified*x 0) := by
    have ht : (a : GaussianInt)*(g.norm : GaussianInt)+
        (b : GaussianInt)*(period : GaussianInt) = 1 := by exact_mod_cast hab
    rw [Zsqrtd.norm_eq_mul_conj] at ht
    dsimp only [y,t]
    rw [hform n]
    linear_combination (ramified*x 0)*ht
  have hnrel (n : ℕ) : g.norm*(y n).norm ≡ 2*(x n).norm [ZMOD (period : ℤ)] := by
    have hh := norm_add_int_mul (period : ℤ) (ramified*x n)
      (g-(b : GaussianInt)*ramified*x 0)
    norm_cast at hh
    rw [← hrel n,Zsqrtd.norm_mul,Zsqrtd.norm_mul,ramified_norm] at hh
    exact hh
  have hy : Function.Injective y := by
    intro i j hij
    change (period : GaussianInt)+ramified*(t+q i) =
      (period : GaussianInt)+ramified*(t+q j) at hij
    have hq := add_left_cancel (mul_left_cancel₀ ramified_ne_zero (add_left_cancel hij))
    apply hx
    rw [hform i,hform j,hq]
  have hyS (n : ℕ) : (y (n+1)-y n).norm < 8 := by
    have hh : y (n+1)-y n = ramified*e n := by
      dsimp only [y]
      rw [hqS]
      ring
    rw [hh,Zsqrtd.norm_mul,ramified_norm]
    have := he n
    omega
  apply Sieve729Sharp.no_ray_le_eight 8 le_rfl
  refine ⟨y,hy,fun n => ⟨hyodd n,?_,hyS n⟩⟩
  intro j hj
  have hcon := (hnrel n).of_dvd (show (prime j : ℤ) ∣ (period : ℤ) by
    exact_mod_cast prime_dvd_period j)
  have hval : (2*(x n).norm) % (prime j : ℤ) = 0 := by
    change (g.norm*(y n).norm) % (prime j : ℤ) =
      (2*(x n).norm) % (prime j : ℤ) at hcon
    rw [Int.mul_emod g.norm (y n).norm,hj,mul_zero,Int.zero_emod] at hcon
    exact hcon.symm
  have hcop : IsCoprime (2 : ℤ) (prime j : ℤ) := by
    refine ⟨(1-(prime j : ℤ))/2,1,?_⟩
    fin_cases j <;> norm_num [prime]
  have hd : (prime j : ℤ) ∣ (x n).norm :=
    hcop.symm.dvd_of_dvd_mul_left (Int.dvd_of_emod_eq_zero hval)
  exact ha n j (Int.emod_eq_zero_of_dvd hd)

/-- Arbitrary signs and switches among eight similarity-related directions
are allowed, provided the common factor is invertible modulo the sieve period. -/
theorem no_small_multiple_prime_ray (g : GaussianInt)
    (hg : IsCoprime g.norm (period : ℤ))
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ¬ ∀ n, ∃ e : GaussianInt, e.norm ≤ 2 ∧ x (n+1)-x n = g*e := by
  intro hs
  obtain ⟨K,hK⟩ := injective_escapes_norm x hx 841
  apply no_small_multiple_allowed_ray g hg (fun n => x (K+n))
    (fun _ _ h => Nat.add_left_cancel (hx h))
  · intro n j
    apply prime_large_norm_residue (hp (K+n)) (prime_is_prime j)
    have hj : (prime j : ℤ) ≤ 29 := by exact_mod_cast prime_le j
    have hj0 : (0 : ℤ) ≤ prime j := Int.natCast_nonneg _
    have hn := hK (K+n) (by omega)
    nlinarith
  · intro n
    simpa only [Nat.add_assoc] using hs (K+n)

lemma ramified_power_period_coprime (k : ℕ) :
    IsCoprime (ramified^k).norm (period : ℤ) := by
  rw [norm_power,ramified_norm]
  exact (show IsCoprime (2 : ℤ) (period : ℤ) from
    ⟨-336472,1,by norm_num [period]⟩).pow_left

/-- Unlike a constant-norm obstruction, this permits arbitrary mixing of the
two consecutive shells. The exponent is fixed along the ray but unrestricted. -/
theorem no_two_consecutive_power_norms (k : ℕ) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ¬ ∀ n, (x (n+1)-x n).norm = (2 : ℤ)^k ∨
      (x (n+1)-x n).norm = (2 : ℤ)^(k+1) := by
  intro hs
  apply no_small_multiple_prime_ray (ramified^k) (ramified_power_period_coprime k) x hx hp
  intro n
  rcases hs n with h | h
  · obtain ⟨e,he,hh⟩ := norm_two_power_factorization k _ h
    exact ⟨e,by omega,hh⟩
  · obtain ⟨e,he,hh⟩ := norm_two_power_factorization (k+1) _ h
    refine ⟨ramified*e,?_,?_⟩
    · rw [Zsqrtd.norm_mul,ramified_norm,he]; norm_num
    · rw [hh,pow_succ,mul_assoc]

/-- The two-shell restriction fails arbitrarily late in any injective prime sequence. -/
theorem infinitely_often_outside_two_shells (k : ℕ) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) (N : ℕ) :
    ∃ n ≥ N, (x (n+1)-x n).norm ≠ (2 : ℤ)^k ∧
      (x (n+1)-x n).norm ≠ (2 : ℤ)^(k+1) := by
  by_contra! hs
  apply no_two_consecutive_power_norms k (fun n => x (N+n))
    (fun _ _ h => Nat.add_left_cancel (hx h)) (fun n => hp (N+n))
  intro n
  have hn : N ≤ N+n := by omega
  by_cases hh : (x (N+n+1)-x (N+n)).norm = (2 : ℤ)^k
  · exact Or.inl (by simpa only [Nat.add_assoc] using hh)
  · exact Or.inr (by simpa only [Nat.add_assoc] using hs (N+n) hn hh)

/-- Two consecutive shells may also share an inert-supported factor, provided
it is coprime to the six-prime sieve period. -/
theorem no_two_consecutive_inert_norms (a k : ℕ)
    (ha : InertNormStepObstruction.InertSupported a) (hac : a.Coprime period)
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ¬ ∀ n, (x (n+1)-x n).norm = (2 : ℤ)^k*(a : ℤ)^2 ∨
      (x (n+1)-x n).norm = (2 : ℤ)^(k+1)*(a : ℤ)^2 := by
  intro hs
  have hgc : IsCoprime (((a : GaussianInt)*ramified^k).norm) (period : ℤ) := by
    rw [Zsqrtd.norm_mul]
    have hna : (a : GaussianInt).norm = (a : ℤ)^2 := by
      simp [gaussian_norm_sq,pow_two]
    rw [hna]
    exact hac.isCoprime.pow_left.mul_left (ramified_power_period_coprime k)
  apply no_small_multiple_prime_ray ((a : GaussianInt)*ramified^k) hgc x hx hp
  intro n
  rcases hs n with h | h
  · obtain ⟨e,he,hh⟩ := InertNormStepObstruction.norm_inert_factorization a ha k _ h
    exact ⟨e,by omega,hh⟩
  · obtain ⟨e,he,hh⟩ := InertNormStepObstruction.norm_inert_factorization a ha (k+1) _ h
    refine ⟨ramified*e,?_,?_⟩
    · rw [Zsqrtd.norm_mul,ramified_norm,he]; norm_num
    · rw [hh,pow_succ]; ring

#print axioms no_two_consecutive_inert_norms
#print axioms no_small_multiple_prime_ray
#print axioms no_two_consecutive_power_norms
#print axioms infinitely_often_outside_two_shells
end Erdos952Investigation.TwoShellSimilarityObstruction
