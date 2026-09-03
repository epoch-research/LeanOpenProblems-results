import Submission.FiniteSieveReduction

/-! Multiplicative closure and exact rational translation periods of the finite
Gaussian sieve. These facts do not establish termination of a moat search. -/
namespace Erdos952Investigation
namespace ExactSievePeriod
open FiniteSieveReduction
set_option maxHeartbeats 0

lemma allowed_mul_iff (N : ℕ) (z w : GaussianInt) :
    Allowed N (z*w) ↔ Allowed N z ∧ Allowed N w := by
  constructor
  · intro h
    constructor
    · intro p hpN hp hd
      apply h p hpN hp
      rw [Zsqrtd.norm_mul]
      exact dvd_mul_of_dvd_left hd _
    · intro p hpN hp hd
      apply h p hpN hp
      rw [Zsqrtd.norm_mul]
      exact dvd_mul_of_dvd_right hd _
  · rintro ⟨hz,hw⟩ p hpN hp hd
    rw [Zsqrtd.norm_mul] at hd
    have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact (hprime.dvd_mul.mp hd).elim (hz p hpN hp) (hw p hpN hp)

lemma prime_dvd_primorial {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) :
    p ∣ primorial N := by
  unfold primorial
  apply Finset.dvd_prod_of_mem
  simp [hp, hpN]

lemma primorial_dvd_iff (N : ℕ) (t : ℤ) :
    (primorial N : ℤ) ∣ t ↔ ∀ p ≤ N, p.Prime → (p : ℤ) ∣ t := by
  constructor
  · intro h p hpN hp
    have hh : (p : ℤ) ∣ primorial N := by
      exact_mod_cast prime_dvd_primorial hp hpN
    exact hh.trans h
  · intro h
    let T := (Finset.range (N+1)).filter Nat.Prime
    have hmem {p : ℕ} (hp : p ∈ T) : p ≤ N ∧ p.Prime := by
      simpa only [T, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] using hp
    have hcop : (T : Set ℕ).Pairwise (Function.onFun IsCoprime (fun p : ℕ => (p : ℤ))) := by
      intro p hp q hq hpq
      exact ((Nat.coprime_primes (hmem hp).2 (hmem hq).2).mpr hpq).isCoprime
    have hh := Finset.prod_dvd_of_coprime hcop (fun p hp => h p (hmem hp).1 (hmem hp).2)
    simpa [primorial, T] using hh

/-- Every locally allowed residue at one sieve prime has a globally allowed
lift. At the other primes choose the residue `1`. -/
lemma lift_allowed_residue (N p : ℕ) (hp : p.Prime) (hpN : p ≤ N)
    (a b : ZMod p) (hab : a^2+b^2 ≠ 0) :
    ∃ z : GaussianInt, Allowed N z ∧ (z.re : ZMod p) = a ∧ (z.im : ZMod p) = b := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A,hA⟩ := prime_crt N (fun q _ => if q=p then (a.val : ZMod q) else 1)
  obtain ⟨B,hB⟩ := prime_crt N (fun q _ => if q=p then (b.val : ZMod q) else 0)
  have hAp : (A : ZMod p) = a := by simpa using hA p hpN hp
  have hBp : (B : ZMod p) = b := by simpa using hB p hpN hp
  refine ⟨⟨A,B⟩,?_,?_,?_⟩
  · intro q hqN hq hd
    letI : Fact q.Prime := ⟨hq⟩
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (⟨A,B⟩ : GaussianInt).norm q).mpr hd
    have he' : (A : ZMod q)^2+(B : ZMod q)^2 = 0 := by
      simpa [gaussian_norm_sq] using he
    by_cases hqp : q=p
    · subst q
      rw [hAp,hBp] at he'
      exact hab he'
    · simp [hA q hqN hq,hB q hqN hq,hqp] at he'
  · simpa using hAp
  · simpa using hBp

def TranslationPeriod (N : ℕ) (d : GaussianInt) : Prop :=
  ∀ z : GaussianInt, Allowed N (z+d) ↔ Allowed N z

lemma norm_ne_zero_after_period {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    {d : GaussianInt} (hd : TranslationPeriod N d) (a b : ZMod p)
    (hab : a^2+b^2 ≠ 0) :
    (a+d.re)^2+(b+d.im)^2 ≠ 0 := by
  obtain ⟨z,hz,hza,hzb⟩ := lift_allowed_residue N p hp hpN a b hab
  have hh := (hd z).mpr hz p hpN hp
  intro he
  apply hh
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simpa [gaussian_norm_sq,hza,hzb] using he

lemma norm_zero_of_period {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    {d : GaussianInt} (hd : TranslationPeriod N d) :
    (d.re : ZMod p)^2+(d.im : ZMod p)^2 = 0 := by
  by_contra hn
  have hh := norm_ne_zero_after_period hp hpN hd (-(d.re : ZMod p)) (-(d.im : ZMod p))
    (by simpa using hn)
  simp at hh

lemma translation_period_of_primorial_dvd {N : ℕ} {d : GaussianInt}
    (hr : (primorial N : ℤ) ∣ d.re) (hi : (primorial N : ℤ) ∣ d.im) :
    TranslationPeriod N d := by
  intro z
  have hnorm (p : ℕ) (hpN : p ≤ N) (hp : p.Prime) :
      ((z+d).norm : ZMod p) = (z.norm : ZMod p) := by
    have hpr := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr ((primorial_dvd_iff N d.re).mp hr p hpN hp)
    have hpi := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr ((primorial_dvd_iff N d.im).mp hi p hpN hp)
    simp [gaussian_norm_sq,hpr,hpi]
  constructor <;> intro hz p hpN hp hd
  · apply hz p hpN hp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [hnorm p hpN hp]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
  · apply hz p hpN hp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [← hnorm p hpN hp]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd

/-- The primorial, not the factorial, is the least positive real translation
period. This is an exact statement about the sieve itself. -/
theorem real_translation_period_iff (N : ℕ) (t : ℤ) :
    TranslationPeriod N (⟨t,0⟩ : GaussianInt) ↔ (primorial N : ℤ) ∣ t := by
  constructor
  · intro hd
    apply (primorial_dvd_iff N t).mpr
    intro p hpN hp
    letI : Fact p.Prime := ⟨hp⟩
    have he := norm_zero_of_period hp hpN hd
    have ht : (t : ZMod p)^2 = 0 := by simpa using he
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (eq_zero_of_pow_eq_zero ht)
  · intro ht
    exact translation_period_of_primorial_dvd ht (dvd_zero _)

lemma coordinates_zero_of_period {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (hp2 : p ≠ 2) {d : GaussianInt} (hd : TranslationPeriod N d) :
    (d.re : ZMod p) = 0 ∧ (d.im : ZMod p) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro he
    have hh := (ZMod.natCast_eq_zero_iff 2 p).mp he
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hh)
  have hnorm := norm_zero_of_period hp hpN hd
  have hi : (d.im : ZMod p) = 0 := by
    by_contra hi
    have hgood : (0 : ZMod p)^2+(-2*(d.im : ZMod p))^2 ≠ 0 := by
      simpa only [zero_pow (by decide : 2 ≠ 0),zero_add] using
        pow_ne_zero 2 (mul_ne_zero (neg_ne_zero.mpr h2) hi)
    have hh := norm_ne_zero_after_period hp hpN hd 0 (-2*(d.im : ZMod p)) hgood
    apply hh
    calc
      _ = (d.re : ZMod p)^2+(d.im : ZMod p)^2 := by ring
      _ = 0 := hnorm
  refine ⟨?_,hi⟩
  rw [hi,zero_pow (by decide : 2 ≠ 0),add_zero] at hnorm
  exact eq_zero_of_pow_eq_zero hnorm

/-- The full translation lattice has the usual coordinatewise divisibility at
odd primes, and only the checkerboard constraint at the ramified prime `2`. -/
theorem translation_period_iff (N : ℕ) (d : GaussianInt) :
    TranslationPeriod N d ↔
      (∀ p ≤ N, p.Prime → p ≠ 2 → (p : ℤ) ∣ d.re ∧ (p : ℤ) ∣ d.im) ∧
      (2 ≤ N → (2 : ℤ) ∣ d.re+d.im) := by
  constructor
  · intro hd
    constructor
    · intro p hpN hp hp2
      have hh := coordinates_zero_of_period hp hpN hp2 hd
      exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hh.1,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hh.2⟩
    · intro hN
      have hh := norm_zero_of_period Nat.prime_two hN hd
      rw [ZMod.pow_card,ZMod.pow_card] at hh
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by simpa using hh)
  · rintro ⟨hodd,heven⟩ z
    have hnorm (p : ℕ) (hpN : p ≤ N) (hp : p.Prime) :
        ((z+d).norm : ZMod p) = (z.norm : ZMod p) := by
      letI : Fact p.Prime := ⟨hp⟩
      by_cases hp2 : p=2
      · subst p
        have hh : (d.re : ZMod 2)+(d.im : ZMod 2) = 0 := by
          have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (heven hpN)
          simpa using hh
        simp only [gaussian_norm_sq,Zsqrtd.re_add,Zsqrtd.im_add,Int.cast_add,
          Int.cast_pow,ZMod.pow_card]
        calc
          _ = ((z.re : ZMod 2)+z.im)+((d.re : ZMod 2)+d.im) := by ring
          _ = _ := by rw [hh,add_zero]
      · obtain ⟨hr,hi⟩ := hodd p hpN hp hp2
        have hr' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hr
        have hi' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hi
        simp [gaussian_norm_sq,hr',hi']
    constructor <;> intro hz p hpN hp hd
    · apply hz p hpN hp
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      rw [hnorm p hpN hp]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    · apply hz p hpN hp
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      rw [← hnorm p hpN hp]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd

#print axioms allowed_mul_iff
#print axioms real_translation_period_iff
#print axioms translation_period_iff
end ExactSievePeriod
end Erdos952Investigation
