import Submission.LambertMinFactorCongruence

/-!
Prime-scaling congruences for the exact Lambert coefficient sequence.
These are auxiliary arithmetic facts, not an irrationality proof.
-/

namespace LambertPrimeScaling

open Erdos68Development

def uniform (d k : ℕ) : ℕ := (d*k).factorial/d.factorial^k

lemma uniform_multinomial (d k : ℕ) :
    uniform d k = Nat.multinomial (Finset.range k) (fun _ => d) := by
  simp [uniform, Nat.multinomial, Nat.mul_comm]

lemma uniform_zero (d : ℕ) : uniform d 0 = 1 := by simp [uniform]

lemma uniform_succ (d k : ℕ) :
    uniform d (k+1) = (d*(k+1)).choose d * uniform d k := by
  rw [uniform_multinomial, Finset.range_add_one,
    Nat.multinomial_insert (by simp), ← uniform_multinomial]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  congr 2
  ring

lemma choose_prime_scaling (p : ℕ) (hp : p.Prime) (n k : ℕ) :
    Nat.ModEq p ((p*n).choose (p*k)) (n.choose k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := p) (n := p*n) (k := p*k)
  simpa [Nat.mul_div_cancel_left _ hp.pos] using h

lemma uniform_prime_scaling (p : ℕ) (hp : p.Prime) (d k : ℕ) :
    Nat.ModEq p (uniform (p*d) k) (uniform d k) := by
  induction k with
  | zero => simp only [uniform_zero]; rfl
  | succ k ih =>
    rw [uniform_succ, uniform_succ]
    have he := choose_prime_scaling p hp (d*(k+1)) d
    rw [← Nat.mul_assoc] at he
    exact he.mul ih

/-- Include the block size one, which contributes n!. -/
def fullCoeff (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, n.factorial/d.factorial^(n/d)

lemma fullCoeff_uniform (n : ℕ) :
    fullCoeff n = ∑ d ∈ n.divisors, uniform d (n/d) := by
  unfold fullCoeff
  apply Finset.sum_congr rfl
  intro d hd
  rw [uniform, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

lemma fullCoeff_eq (n : ℕ) (hn : 0 < n) : fullCoeff n = lambertCoeff n+n.factorial := by
  have hone : (∑ d ∈ n.divisors, if d=1 then n.factorial else 0) = n.factorial := by
    simp [Nat.mem_divisors, hn.ne']
  rw [← hone, lambertCoeff, ← Finset.sum_add_distrib]
  unfold fullCoeff
  apply Finset.sum_congr rfl
  intro d hd
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn
  by_cases he : d=1
  · subst d; simp
  · simp [he, show 2 ≤ d by omega]

lemma prime_dvd_uniform_of_not_dvd (p n d : ℕ) (hp : p.Prime) (hn : 0 < n)
    (hd : d ∣ p*n) (hpd : ¬p ∣ d) : p ∣ uniform d ((p*n)/d) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.mul_pos hp.pos hn)
  have he : d*((p*n)/d) = p*n := Nat.mul_div_cancel' hd
  have hpk : p ∣ (p*n)/d := by
    apply (hp.dvd_mul.mp ?_).resolve_left hpd
    rw [he]
    exact dvd_mul_right p n
  have hkpos : 0 < (p*n)/d := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hp.pos hn) hd) hdpos
  have hpf : p ∣ ((p*n)/d).factorial :=
    Nat.dvd_factorial hp.pos (Nat.le_of_dvd hkpos hpk)
  exact hpf.trans (factorial_dvd_uniform_multinomial hdpos _)

lemma scaled_divisors (p n : ℕ) (hp : 0 < p) (hn : 0 < n) :
    (p*n).divisors.filter (fun d => p ∣ d) = n.divisors.image (fun d => p*d) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hd, ⟨e, rfl⟩⟩
    refine ⟨e, Nat.mem_divisors.mpr ⟨?_, hn.ne'⟩, rfl⟩
    exact (Nat.mul_dvd_mul_iff_left hp).mp (Nat.dvd_of_mem_divisors hd)
  · rintro ⟨e, he, rfl⟩
    refine ⟨Nat.mem_divisors.mpr ⟨?_, (Nat.mul_pos hp hn).ne'⟩, dvd_mul_right p e⟩
    exact Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors he)

/-- The version including singleton blocks is invariant under multiplication
of the index by p, modulo p. -/
lemma fullCoeff_prime_scaling (p n : ℕ) (hp : p.Prime) (hn : 0 < n) :
    Nat.ModEq p (fullCoeff (p*n)) (fullCoeff n) := by
  rw [fullCoeff_uniform, fullCoeff_uniform]
  trans ∑ d ∈ (p*n).divisors, if p ∣ d then uniform d ((p*n)/d) else 0
  · apply Nat.ModEq.sum
    intro d hd
    by_cases hpd : p ∣ d
    · rw [if_pos hpd]
    · rw [if_neg hpd]
      exact Nat.modEq_zero_iff_dvd.mpr
        (prime_dvd_uniform_of_not_dvd p n d hp hn (Nat.dvd_of_mem_divisors hd) hpd)
  · rw [← Finset.sum_filter, scaled_divisors p n hp.pos hn,
      Finset.sum_image (by intro a _ b _ hab; exact (Nat.mul_left_cancel_iff hp.pos).mp hab)]
    apply Nat.ModEq.sum
    intro d hd
    rw [Nat.mul_div_mul_left n d hp.pos]
    exact uniform_prime_scaling p hp d (n/d)

/-- The singleton-block correction is essential: in general the right side
is `a_n+n!`, not merely `a_n`. -/
theorem lambertCoeff_prime_scaling (p n : ℕ) (hp : p.Prime) (hn : 0 < n) :
    Nat.ModEq p (lambertCoeff (p*n)) (lambertCoeff n+n.factorial) := by
  have h := fullCoeff_prime_scaling p n hp hn
  rw [fullCoeff_eq (p*n) (Nat.mul_pos hp.pos hn), fullCoeff_eq n hn] at h
  have hd : p ∣ (p*n).factorial :=
    Nat.dvd_factorial hp.pos (Nat.le_mul_of_pos_right p hn)
  have he : Nat.ModEq p (lambertCoeff (p*n)+(p*n).factorial) (lambertCoeff (p*n)) := by
    simpa only [Nat.add_zero] using (Nat.ModEq.refl (lambertCoeff (p*n))).add
      (Nat.modEq_zero_iff_dvd.mpr hd)
  exact he.symm.trans h

lemma lambertCoeff_prime_scaling_large (p n : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    Nat.ModEq p (lambertCoeff (p*n)) (lambertCoeff n) := by
  have h := lambertCoeff_prime_scaling p n hp (hp.pos.trans_le hpn)
  have hd := Nat.dvd_factorial hp.pos hpn
  exact h.trans (by simpa only [Nat.add_zero] using
    (Nat.ModEq.refl (lambertCoeff n)).add (Nat.modEq_zero_iff_dvd.mpr hd))

lemma lambertCoeff_twice_prime (p : ℕ) (hp : p.Prime) :
    Nat.ModEq p (lambertCoeff (2*p)) 3 := by
  have h := lambertCoeff_prime_scaling p 2 hp (by omega)
  have he : lambertCoeff 2 = 1 := lambertCoeff_prime (by decide)
  simpa only [Nat.mul_comm p 2, he, Nat.factorial_two, show 1+2=3 by omega] using h

#print axioms lambertCoeff_prime_scaling
#print axioms lambertCoeff_prime_scaling_large
#print axioms lambertCoeff_twice_prime

end LambertPrimeScaling
