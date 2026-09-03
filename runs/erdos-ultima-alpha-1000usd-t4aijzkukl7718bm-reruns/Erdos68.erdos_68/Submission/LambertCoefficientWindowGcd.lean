import Submission.LambertMinFactorCongruence

/-!
Gcds of finite factorial-scaled Lambert coefficient windows beginning at a
prime. This concerns the individual coefficients, not the gcd of their sum.
The bounded-representation result leaves the first coefficient unbounded;
it does not by itself settle the irrationality conjecture.
-/

namespace LambertCoefficientWindowGcd

open Finset Erdos68Development

def scaled (p r i : ℕ) : ℕ :=
  lambertCoeff (p + i) * ((p + r).factorial / (p + i).factorial)

def windowGcd (p r : ℕ) : ℕ := (range (r + 1)).gcd (scaled p r)

lemma scaled_last (p r : ℕ) : scaled p r r = lambertCoeff (p + r) := by
  simp [scaled, Nat.div_self (Nat.factorial_pos _)]

lemma scaled_succ (p r i : ℕ) (hi : i ≤ r) :
    scaled p (r + 1) i = (p + r + 1) * scaled p r i := by
  unfold scaled
  rw [show p + (r + 1) = p + r + 1 by omega, Nat.factorial_succ,
    Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (by omega : p+i ≤ p+r))]
  ring

lemma windowGcd_zero (p : ℕ) : windowGcd p 0 = lambertCoeff p := by
  simp [windowGcd, scaled, Nat.div_self (Nat.factorial_pos _)]

lemma windowGcd_succ (p r : ℕ) :
    windowGcd p (r + 1) =
      Nat.gcd (lambertCoeff (p + r + 1)) ((p + r + 1) * windowGcd p r) := by
  unfold windowGcd
  rw [Finset.range_add_one, Finset.gcd_insert, scaled_last]
  have he : (range (r + 1)).gcd (scaled p (r + 1)) =
      (range (r + 1)).gcd (fun i => (p + r + 1) * scaled p r i) := by
    apply Finset.gcd_congr rfl
    intro i hi
    exact scaled_succ p r i (by have := mem_range.mp hi; omega)
  rw [he, Finset.gcd_mul_left]
  simp [Nat.add_assoc, gcd_eq_nat_gcd]

lemma coefficient_coprime_predecessor (n : ℕ) (hn : 2 ≤ n) :
    Nat.Coprime (lambertCoeff n) (n - 1) := by
  have hm : lambertCoeff n % (n-1) = 1 % (n-1) := lambertCoeff_modEq_pred hn
  change Nat.gcd (lambertCoeff n) (n-1) = 1
  rw [Nat.gcd_comm, Nat.gcd_rec, hm, ← Nat.gcd_rec]
  simp

/-- The common gcd of all scaled coefficients in a prime-starting window
is just the gcd of the last coefficient with its index. -/
theorem windowGcd_eq (p r : ℕ) (hp : p.Prime) :
    windowGcd p r = Nat.gcd (lambertCoeff (p + r)) (p + r) := by
  induction r with
  | zero => simp [windowGcd_zero, lambertCoeff_prime hp]
  | succ r ih =>
    rw [windowGcd_succ]
    have hc : Nat.Coprime (lambertCoeff (p+r+1)) (p+r) := by
      simpa using coefficient_coprime_predecessor (p+r+1)
        (by have := hp.two_le; omega)
    have hd : windowGcd p r ∣ p+r := by rw [ih]; exact Nat.gcd_dvd_right _ _
    have hcop : Nat.Coprime (windowGcd p r) (lambertCoeff (p+r+1)) :=
      (Nat.Coprime.coprime_dvd_right hd hc).symm
    simpa [Nat.add_assoc] using
      Nat.Coprime.gcd_mul_right_cancel_right (p+r+1) hcop

lemma windowGcd_dvd_index (p r : ℕ) (hp : p.Prime) :
    windowGcd p r ∣ p + r := by
  rw [windowGcd_eq p r hp]
  exact Nat.gcd_dvd_right _ _

lemma windowGcd_pos (p r : ℕ) (hp : p.Prime) : 0 < windowGcd p r := by
  rw [windowGcd_eq p r hp]
  exact Nat.gcd_pos_of_pos_right _ (by have := hp.pos; omega)

/-- A bounded digit in any solvable integral linear congruence. -/
lemma bounded_digit (a m : ℕ) (hm : 0 < m) (t : ℤ)
    (ht : (Nat.gcd a m : ℤ) ∣ t) :
    ∃ w u : ℤ, 0 ≤ w ∧ w < m ∧ t = (a : ℤ)*w + (m : ℤ)*u := by
  obtain ⟨k, hk⟩ := ht
  let x : ℤ := Nat.gcdA a m * k
  let y : ℤ := Nat.gcdB a m * k
  have he : t = (a : ℤ)*x + (m : ℤ)*y := by
    rw [hk, Nat.gcd_eq_gcd_ab]
    dsimp [x, y]
    ring
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  refine ⟨x % m, y + (a : ℤ)*(x / m), Int.emod_nonneg _ (by omega),
    Int.emod_lt_of_pos _ hmZ, ?_⟩
  rw [he]
  have hx := Int.emod_add_mul_ediv x m
  linear_combination (a : ℤ) * hx.symm

/-- Every multiple of the common gcd can be represented using the scaled
coefficients. All weights except the first are bounded by the square of
their own index. The first weight is deliberately NOT bounded here. -/
theorem bounded_representation_except_first (p r : ℕ) (hp : p.Prime)
    (t : ℤ) (ht : (windowGcd p r : ℤ) ∣ t) :
    ∃ w : ℕ → ℤ,
      t = ∑ i ∈ range (r + 1), w i * (scaled p r i : ℤ) ∧
      ∀ i, 0 < i → i ≤ r → 0 ≤ w i ∧ w i < (p+i)*(p+i-1) := by
  induction r generalizing t with
  | zero =>
    refine ⟨fun _ => t, ?_, ?_⟩
    · simp only [Nat.zero_add, sum_range_one, scaled_last, Nat.add_zero, lambertCoeff_prime hp,
        Nat.cast_one, mul_one]
    · intro i hi hir
      omega
  | succ r ih =>
    have ht' : (Nat.gcd (lambertCoeff (p+r+1))
        ((p+r+1)*windowGcd p r) : ℤ) ∣ t := by
      simpa only [windowGcd_succ] using ht
    have hm : 0 < (p+r+1)*windowGcd p r :=
      Nat.mul_pos (by omega) (windowGcd_pos p r hp)
    obtain ⟨d, u, hd0, hdlt, hde⟩ :=
      bounded_digit (lambertCoeff (p+r+1)) ((p+r+1)*windowGcd p r) hm t ht'
    obtain ⟨v, hv, hvb⟩ := ih ((windowGcd p r : ℤ)*u) (dvd_mul_right _ _)
    let w : ℕ → ℤ := fun i => if i = r+1 then d else v i
    refine ⟨w, ?_, ?_⟩
    · rw [sum_range_succ]
      have hs : (∑ i ∈ range (r+1), w i * (scaled p (r+1) i : ℤ)) =
          (p+r+1 : ℕ) * (∑ i ∈ range (r+1), v i * (scaled p r i : ℤ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        have hir : i ≤ r := by have := mem_range.mp hi; omega
        simp only [w, if_neg (by omega : i ≠ r+1), scaled_succ p r i hir,
          Nat.cast_mul]
        ring
      rw [hs, ← hv, scaled_last]
      simp only [w, if_pos rfl]
      rw [hde]
      simp only [Nat.add_assoc]
      push_cast
      ring
    · intro i hi hir
      by_cases he : i = r+1
      · subst i
        simp only [w, if_pos rfl]
        refine ⟨hd0, ?_⟩
        have hg : windowGcd p r ≤ p+r :=
          Nat.le_of_dvd (by have := hp.pos; omega) (windowGcd_dvd_index p r hp)
        have hmul : (p+r+1)*windowGcd p r ≤ (p+r+1)*(p+r) :=
          Nat.mul_le_mul_left _ hg
        have hmulZ : (((p+r+1)*windowGcd p r : ℕ) : ℤ) ≤
            ((p+r+1)*(p+r) : ℕ) := by exact_mod_cast hmul
        have hres := hdlt.trans_le hmulZ
        calc
          d < (((p+r+1)*(p+r) : ℕ) : ℤ) := hres
          _ = (p+(r+1))*(p+(r+1)-1) := by push_cast; ring
      · simp only [w, if_neg he]
        exact hvb i hi (by omega)

lemma successor_windowGcd_lt (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    windowGcd p 1 < p + 1 := by
  have ho := hp.eq_two_or_odd.resolve_left (by omega)
  have he : 2 ∣ p+1 := by omega
  have hmin : (p+1).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr he
  have ha := lambertCoeff_modEq_minFac_factorial (show 2 ≤ p+1 by omega)
  rw [hmin] at ha
  have hodd : lambertCoeff (p+1) % 2 = 1 := by
    simpa only [Nat.factorial, Nat.ModEq, Nat.reduceMul, Nat.one_mod] using ha
  have hd := windowGcd_dvd_index p 1 hp
  have hl := Nat.le_of_dvd (show 0 < p+1 by omega) hd
  by_contra h
  have hg : windowGcd p 1 = p+1 := by omega
  have hda : p+1 ∣ lambertCoeff (p+1) := by
    have hh := Nat.gcd_dvd_left (lambertCoeff (p+1)) (p+1)
    rw [← windowGcd_eq p 1 hp, hg] at hh
    exact hh
  have ht := he.trans hda
  omega

/-- In the shortest odd-prime window, the apparently uncontrolled first
weight really can be expensive. Any representation of the positive window
gcd with a nonnegative second weight satisfies this factorial lower bound. -/
theorem first_weight_cost (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (w₀ w₁ : ℤ) (hw₁ : 0 ≤ w₁)
    (he : (windowGcd p 1 : ℤ) = (p+1 : ℤ)*w₀ +
      (lambertCoeff (p+1) : ℤ)*w₁) :
    (p.factorial : ℤ) < (2 : ℤ)^((p+1)/2) * (1-w₀) := by
  have ht0 : (0 : ℤ) < windowGcd p 1 := by
    exact_mod_cast windowGcd_pos p 1 hp
  have ht1 : (windowGcd p 1 : ℤ) < (p+1 : ℤ) := by
    exact_mod_cast successor_windowGcd_lt p hp hp3
  have hpZ : (0 : ℤ) < p+1 := by omega
  have hw : 1 ≤ w₁ := by
    by_contra h
    have hz : w₁ = 0 := by omega
    rw [hz, mul_zero, add_zero] at he
    by_cases hpos : 0 < w₀
    · have hh : 1 ≤ w₀ := by omega
      nlinarith
    · have hh : w₀ ≤ 0 := by omega
      nlinarith
  have ha0 : (0 : ℤ) ≤ lambertCoeff (p+1) := by positivity
  have ha : (lambertCoeff (p+1) : ℤ) < (p+1 : ℤ)*(1-w₀) := by
    have hm := mul_le_mul_of_nonneg_left hw ha0
    nlinarith
  have ho := hp.eq_two_or_odd.resolve_left (by omega)
  have hindex : 2*((p+1)/2) = p+1 := by omega
  have hmpos : 0 < (p+1)/2 := by omega
  have hd : 2^((p+1)/2) ∣ (p+1).factorial := by
    simpa only [show (2 : ℕ).factorial = 2 by decide, hindex] using
      factorial_pow_dvd_factorial_mul 2 ((p+1)/2)
  have hl := lambertCoeff_even_lower ((p+1)/2) hmpos
  rw [hindex] at hl
  have hmul := Nat.mul_le_mul_right (2^((p+1)/2)) hl
  rw [Nat.div_mul_cancel hd] at hmul
  have hfac : ((p+1).factorial : ℤ) ≤
      (lambertCoeff (p+1) : ℤ) * (2 : ℤ)^((p+1)/2) := by exact_mod_cast hmul
  have hpow : (0 : ℤ) < 2^((p+1)/2) := by positivity
  have hh : (p+1 : ℤ)*(p.factorial : ℤ) <
      (p+1 : ℤ)*((2 : ℤ)^((p+1)/2)*(1-w₀)) := by
    calc
      _ = ((p+1).factorial : ℤ) := by rw [Nat.factorial_succ]; push_cast; ring
      _ ≤ (lambertCoeff (p+1) : ℤ) * (2 : ℤ)^((p+1)/2) := hfac
      _ < ((p+1 : ℤ)*(1-w₀)) * (2 : ℤ)^((p+1)/2) :=
        mul_lt_mul_of_pos_right ha hpow
      _ = _ := by ring
  exact (Int.mul_lt_mul_left hpZ).mp hh

/-- Allowing either sign for the second digit does not remove the large
first-coordinate cost in a two-index window. -/
theorem first_weight_cost_signed (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (w₀ w₁ : ℤ)
    (he : (windowGcd p 1 : ℤ) = (p+1 : ℤ)*w₀ +
      (lambertCoeff (p+1) : ℤ)*w₁) :
    (p.factorial : ℤ) < (2 : ℤ)^((p+1)/2) * (1+|w₀|) := by
  by_cases hw₁ : 0 ≤ w₁
  · have h := first_weight_cost p hp hp3 w₀ w₁ hw₁ he
    have habs : -w₀ ≤ |w₀| := neg_le_abs w₀
    have hpow : (0 : ℤ) ≤ 2^((p+1)/2) := by positivity
    exact h.trans_le (mul_le_mul_of_nonneg_left (by omega) hpow)
  have hw₁' : w₁ ≤ -1 := by omega
  have ht0 : (0 : ℤ) < windowGcd p 1 := by
    exact_mod_cast windowGcd_pos p 1 hp
  have ha0 : (0 : ℤ) ≤ lambertCoeff (p+1) := by positivity
  have ha : (lambertCoeff (p+1) : ℤ) < (p+1 : ℤ)*w₀ := by
    have hm := mul_le_mul_of_nonneg_left hw₁' ha0
    nlinarith
  have ho := hp.eq_two_or_odd.resolve_left (by omega)
  have hindex : 2*((p+1)/2) = p+1 := by omega
  have hd : 2^((p+1)/2) ∣ (p+1).factorial := by
    simpa only [show (2 : ℕ).factorial = 2 by decide, hindex] using
      factorial_pow_dvd_factorial_mul 2 ((p+1)/2)
  have hl := lambertCoeff_even_lower ((p+1)/2) (by omega)
  rw [hindex] at hl
  have hmul := Nat.mul_le_mul_right (2^((p+1)/2)) hl
  rw [Nat.div_mul_cancel hd] at hmul
  have hfac : ((p+1).factorial : ℤ) ≤
      (lambertCoeff (p+1) : ℤ) * (2 : ℤ)^((p+1)/2) := by exact_mod_cast hmul
  have hpow : (0 : ℤ) < 2^((p+1)/2) := by positivity
  have hpZ : (0 : ℤ) < p+1 := by omega
  have hh : (p+1 : ℤ)*(p.factorial : ℤ) <
      (p+1 : ℤ)*((2 : ℤ)^((p+1)/2)*w₀) := by
    calc
      _ = ((p+1).factorial : ℤ) := by rw [Nat.factorial_succ]; push_cast; ring
      _ ≤ (lambertCoeff (p+1) : ℤ) * (2 : ℤ)^((p+1)/2) := hfac
      _ < ((p+1 : ℤ)*w₀) * (2 : ℤ)^((p+1)/2) :=
        mul_lt_mul_of_pos_right ha hpow
      _ = _ := by ring
  have h := (Int.mul_lt_mul_left hpZ).mp hh
  exact h.trans_le (mul_le_mul_of_nonneg_left
    (by have := le_abs_self w₀; omega) hpow.le)

#print axioms first_weight_cost_signed

#print axioms first_weight_cost


#print axioms windowGcd_eq
#print axioms bounded_representation_except_first

end LambertCoefficientWindowGcd
