import Submission.PeriodicIncrementObstruction

/-! A modular obstruction for some two-increment prime walks.  The hypotheses
on the two increments are essential; this is not a solution of the moat problem. -/
namespace Erdos952Investigation
namespace TwoIncrementObstruction
set_option maxHeartbeats 0

lemma one_way_walk_stabilizes {p : ℕ} (hp : p.Prime) (f : ℕ → ZMod p)
    (hne : ∀ n, f n ≠ 0)
    (hstep : ∀ n, f (n+1) = f n ∨ f (n+1) = f n + 1) :
    ∃ N, ∀ n ≥ N, f (n+1) = f n := by
  letI : Fact p.Prime := ⟨hp⟩
  have hincrease (n : ℕ) (h : f (n+1) = f n + 1) :
      (f (n+1)).val = (f n).val + 1 := by
    have hlt := ZMod.val_lt (f n)
    have hval : (f (n+1)).val = ((f n).val + 1) % p := by
      rw [h,ZMod.val_add,ZMod.val_one]
    have hpos : (f (n+1)).val ≠ 0 := by
      intro hh
      apply hne (n+1)
      apply ZMod.val_injective
      simpa using hh
    have hb : (f n).val + 1 < p := by
      by_contra hh
      have he : (f n).val + 1 = p := by omega
      rw [he,Nat.mod_self] at hval
      exact hpos hval
    rwa [Nat.mod_eq_of_lt hb] at hval
  have hmono : Monotone (fun n => (f n).val) := by
    apply monotone_nat_of_le_succ
    intro n
    rcases hstep n with h | h
    · rw [h]
    · rw [hincrease n h]; omega
  obtain ⟨z,⟨N,rfl⟩,hmax⟩ := Set.exists_max_image (Set.range f) ZMod.val
    (Set.toFinite _) (Set.range_nonempty f)
  refine ⟨N,?_⟩
  intro n hn
  apply ZMod.val_injective
  exact le_antisymm ((hmax _ ⟨n+1,rfl⟩).trans (hmono hn))
    (hmono (by omega))

lemma single_nonzero_increment_stabilizes {p : ℕ} (hp : p.Prime)
    (a : ZMod p) (ha : a ≠ 0) (f : ℕ → ZMod p)
    (hne : ∀ n, f n ≠ 0)
    (hstep : ∀ n, f (n+1)-f n = 0 ∨ f (n+1)-f n = a) :
    ∃ N, ∀ n ≥ N, f (n+1) = f n := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨N,hN⟩ := one_way_walk_stabilizes hp (fun n => f n / a)
    (fun n => div_ne_zero (hne n) ha) (by
      intro n
      rcases hstep n with h | h
      · exact Or.inl (congrArg (fun t => t/a) (sub_eq_zero.mp h))
      · right
        dsimp only
        rw [eq_add_of_sub_eq h,add_div,div_self ha]
        ring)
  refine ⟨N,fun n hn => ?_⟩
  exact (div_left_inj' ha).mp (hN n hn)

def projection {p : ℕ} (r : ZMod p) (z : GaussianInt) : ZMod p :=
  (z.re : ZMod p) + r * (z.im : ZMod p)

lemma projection_sub {p : ℕ} (r : ZMod p) (z w : GaussianInt) :
    projection r (z-w) = projection r z - projection r w := by
  simp only [projection,Zsqrtd.re_sub,Zsqrtd.im_sub,Int.cast_sub]
  ring

lemma projection_nonzero {p : ℕ} (hp : p.Prime) (r : ZMod p)
    (hr : r^2 = -1) {z : GaussianInt} (hz : Prime z)
    (hlarge : (p : ℤ)^2 < z.norm) : projection r z ≠ 0 := by
  intro he
  have hnorm : (z.norm : ZMod p) = 0 := by
    rw [gaussian_norm_sq]
    push_cast
    have hf : (z.re : ZMod p)^2 + (z.im : ZMod p)^2 =
        projection r z * ((z.re : ZMod p)-r*(z.im : ZMod p)) := by
      dsimp only [projection]
      linear_combination (z.im : ZMod p)^2 * hr
    rw [hf,he,zero_mul]
  have hb := prime_norm_divisor_bound hz hp
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hnorm)
  omega

/-- If a split-prime projection annihilates exactly one of the two allowed
increments, no injective prime walk can use only those increments. -/
theorem no_two_increment_prime_walk {p : ℕ} (hp : p.Prime)
    (r : ZMod p) (hr : r^2 = -1) (u v : GaussianInt)
    (hu : projection r u = 0) (hv : projection r v ≠ 0)
    (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hprime : ∀ n, Prime (x n)) :
    ¬ ∀ n, x (n+1)-x n = u ∨ x (n+1)-x n = v := by
  intro hstep
  obtain ⟨K,hK⟩ := injective_escapes_norm x hx ((p : ℤ)^2)
  let f : ℕ → ZMod p := fun n => projection r (x (K+n))
  have hfstep : ∀ n, f (n+1)-f n = 0 ∨
      f (n+1)-f n = projection r v := by
    intro n
    have he : f (n+1)-f n = projection r (x (K+n+1)-x (K+n)) := by
      simp only [f,projection_sub,Nat.add_assoc]
    rw [he]
    rcases hstep (K+n) with h | h
    · left; rw [h,hu]
    · right; rw [h]
  obtain ⟨N,hN⟩ := single_nonzero_increment_stabilizes hp (projection r v) hv f
    (fun n => projection_nonzero hp r hr (hprime (K+n)) (hK _ (by omega))) hfstep
  have hconst : ∀ n ≥ K+N, x (n+1)-x n = u := by
    intro n hn
    rcases hstep n with h | h
    · exact h
    · exfalso
      have he := hN (n-K) (by omega)
      have hk : K+(n-K) = n := by omega
      have hk' : K+(n-K+1) = n+1 := by omega
      dsimp only [f] at he
      rw [hk,hk'] at he
      apply hv
      rw [← h,projection_sub,he,sub_self]
  apply prime_walk_increments_not_eventually_periodic x hx hprime
  refine ⟨K+N,1,by omega,?_⟩
  intro n hn
  rw [hconst n hn,hconst (n+1) (by omega)]

#print axioms one_way_walk_stabilizes

lemma exists_odd_prime_dvd_square_add_one (K : ℕ) (hK : 2 ≤ K) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ K^2+1 := by
  have hlarge : 4 ≤ K^2 := by nlinarith
  by_cases heven : K % 2 = 0
  · obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (show K^2+1 ≠ 1 by omega)
    refine ⟨p,hp,?_,hpd⟩
    intro he
    subst p
    have hm : (K^2+1) % 2 = 1 := by
      norm_num [Nat.add_mod,Nat.pow_mod,heven]
    have := Nat.mod_eq_zero_of_dvd hpd
    omega
  · have hodd : K % 2 = 1 := by omega
    have hm : (K^2+1) % 4 = 2 := by
      have hk4 : K % 4 = 1 ∨ K % 4 = 3 := by omega
      rcases hk4 with h | h <;> norm_num [Nat.add_mod,Nat.pow_mod,h]
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd
      (show (K^2+1)/2 ≠ 1 by omega)
    refine ⟨p,hp,?_,hpd.trans ?_⟩
    · intro he
      subst p
      have := Nat.mod_eq_zero_of_dvd hpd
      omega
    · exact ⟨2,by omega⟩

/-- Arbitrary choices of the signs do not produce a prime ray of this form.
No recurrence or finite-state rule for the sign word is assumed. -/
theorem no_horizontal_two_increment_prime_walk (K : ℕ) (hK : 2 ≤ K)
    (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hprime : ∀ n, Prime (x n)) :
    ¬ ∀ n, x (n+1)-x n = ⟨K,1⟩ ∨ x (n+1)-x n = ⟨K,-1⟩ := by
  obtain ⟨p,hp,hp2,hpd⟩ := exists_odd_prime_dvd_square_add_one K hK
  letI : Fact p.Prime := ⟨hp⟩
  have he : (K : ZMod p)^2+1 = 0 := by
    have hh := (ZMod.natCast_eq_zero_iff (K^2+1) p).mpr hpd
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hh
  have hr : (-(K : ZMod p))^2 = -1 := by linear_combination he
  have hk : (K : ZMod p) ≠ 0 := by
    intro hh
    simp [hh] at he
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hh
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp hh))
  apply no_two_increment_prime_walk hp (-(K : ZMod p)) hr
    (⟨K,1⟩ : GaussianInt) (⟨K,-1⟩ : GaussianInt) _ _ x hx hprime
  · simp [projection]
  · have hh : projection (-(K : ZMod p)) (⟨K,-1⟩ : GaussianInt) =
        2*(K : ZMod p) := by
      simp only [projection,Int.cast_natCast,Int.cast_neg,Int.cast_one]
      ring
    rw [hh]
    exact mul_ne_zero htwo hk

#print axioms no_horizontal_two_increment_prime_walk

#print axioms no_two_increment_prime_walk
end TwoIncrementObstruction
end Erdos952Investigation
