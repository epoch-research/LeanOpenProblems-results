import Submission.SieveMassUpper
import Submission.SieveMassLower

/-! Grouping reciprocal integers by their squarefree radicals gives the
sharper elementary bound `harmonic R <= sieveMass R`. This is sieve
normalization, not a prime-pair theorem. -/
namespace Erdos972SharpSieveMassLower

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972SelbergWeights Erdos972SelbergLocalCost Erdos972SieveMassUpper

set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma hasSum_factored_reciprocal {d : ℕ} (hd : Squarefree d) :
    HasSum (fun n : Nat.factoredNumbers d.primeFactors => 1/((n:ℕ):ℝ))
      ((d:ℝ)/d.totient) := by
  classical
  have hgeom {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => ‖(1:ℝ)/(p^k:ℕ)‖) := by
    have hp1 : (1:ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
    have hh := summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ 1/p)
      ((div_lt_one (by positivity : (0:ℝ) < p)).mpr hp1)
    simpa only [Nat.cast_pow, one_div_pow, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(p:ℝ)^_)] using hh
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (1:ℝ)/n) (by norm_num)
    (by intro m n hmn; simp [Nat.cast_mul, div_mul_eq_div_mul_one_div])
    (fun hp => hgeom hp) d.primeFactors).2
  have hfilter : d.primeFactors.filter Nat.Prime = d.primeFactors := by
    apply filter_eq_self.mpr
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  rw [hfilter] at hh
  have hterm (p : ℕ) (hp : p ∈ d.primeFactors) :
      (∑' k : ℕ, (1:ℝ)/(p^k:ℕ)) = 1+sieveAtom p := by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1:ℝ) < p := Nat.one_lt_cast.mpr hpp.one_lt
    simp only [Nat.cast_pow, ← one_div_pow]
    rw [tsum_geometric_of_lt_one (by positivity)
      ((div_lt_one (by positivity : (0:ℝ) < p)).mpr hp1), sieveAtom_prime hpp]
    rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
    have hp0 : (p:ℝ) ≠ 0 := by positivity
    have hpm : (p:ℝ)-1 ≠ 0 := by linarith
    field_simp
    ring
  have he : (∏ p ∈ d.primeFactors, ∑' k : ℕ, (1:ℝ)/(p^k:ℕ)) = (d:ℝ)/d.totient := by
    rw [prod_congr rfl hterm]
    have hprod := atomAF_mult.prodPrimeFactors_one_add_of_squarefree hd
    simp only [atomAF_apply] at hprod
    rw [hprod, sieveAtom_divisors hd]
  rwa [he] at hh

/-- Summing over multiples of `d` whose prime factors all divide `d`
costs at most `1/totient(d)`, even without a size cutoff. -/
lemma reciprocal_multiples_factored_bound {d : ℕ} (hd : Squarefree d)
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, d ∣ n ∧ n ∈ Nat.factoredNumbers d.primeFactors) :
    (∑ n ∈ S, (1:ℝ)/n) ≤ 1/(d.totient:ℝ) := by
  classical
  let T := S.image (fun n => n/d)
  have hm (n : ℕ) (hn : n ∈ S) : n/d ∈ Nat.factoredNumbers d.primeFactors :=
    Nat.mem_factoredNumbers_of_dvd (hS n hn).2 (Nat.div_dvd_of_dvd (hS n hn).1)
  have hinj : Set.InjOn (fun n => n/d) (↑S : Set ℕ) := by
    intro n hn m hm he
    have hn' := Nat.mul_div_cancel' (hS n hn).1
    have hm' := Nat.mul_div_cancel' (hS m hm).1
    change n/d = m/d at he
    rw [he] at hn'
    exact hn'.symm.trans hm'
  have hsum : (∑ m ∈ T, (1:ℝ)/m) ≤ (d:ℝ)/d.totient := by
    have hh := (hasSum_subtype_iff_indicator (f := fun n : ℕ => (1:ℝ)/n)
      (s := Nat.factoredNumbers d.primeFactors)).mp (hasSum_factored_reciprocal hd)
    calc
      _ = ∑ m ∈ T, (Nat.factoredNumbers d.primeFactors).indicator (fun n : ℕ => (1:ℝ)/n) m := by
        apply sum_congr rfl
        intro m hmT
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hmT
        rw [Set.indicator_of_mem (hm n hn)]
      _ ≤ _ := sum_le_hasSum T (fun m _ =>
        Set.indicator_nonneg (fun _ _ => by positivity) m) hh
  have hterm (n : ℕ) (hn : n ∈ S) :
      (1:ℝ)/n = (1/(d:ℝ))*(1/(n/d:ℕ)) := by
    rw [one_div_mul_one_div, ← Nat.cast_mul, Nat.mul_div_cancel' (hS n hn).1]
  calc
    _ = (1/(d:ℝ))*(∑ m ∈ T, (1:ℝ)/m) := by
      dsimp only [T]
      rw [sum_image hinj, mul_sum]
      exact sum_congr rfl hterm
    _ ≤ (1/(d:ℝ))*((d:ℝ)/d.totient) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1/(d.totient:ℝ) := by
      have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne_zero
      field_simp

noncomputable def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma radical_squarefree (n : ℕ) : Squarefree (radical n) :=
  squarefree_prime_product (fun _ hp => Nat.prime_of_mem_primeFactors hp)

lemma radical_primeFactors (n : ℕ) : (radical n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors hp)

lemma radical_dvd (n : ℕ) : radical n ∣ n := Nat.prod_primeFactors_dvd n

lemma radical_le {n : ℕ} (hn : 0 < n) : radical n ≤ n :=
  Nat.le_of_dvd hn (radical_dvd n)

lemma radical_fiber_reciprocal_bound (R d : ℕ) :
    (∑ n ∈ (Ioc 0 R).filter (fun n => radical n = d), (1:ℝ)/n) ≤ sieveAtom d := by
  classical
  by_cases hd : Squarefree d
  · have hbound := reciprocal_multiples_factored_bound hd
      ((Ioc 0 R).filter (fun n => radical n = d)) (by
        intro n hn
        obtain ⟨hnI, he⟩ := mem_filter.mp hn
        constructor
        · rw [← he]
          exact radical_dvd n
        · apply Nat.mem_factoredNumbers_of_primeFactors_subset (mem_Ioc.mp hnI).1.ne'
          rw [← he, radical_primeFactors])
    have hmu : (μ d : ℝ)^2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hd
    simpa only [sieveAtom, hmu] using hbound
  · have he : (Ioc 0 R).filter (fun n => radical n = d) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro n hn he
      exact hd (he ▸ radical_squarefree n)
    rw [he, sum_empty]
    exact sieveAtom_nonneg d

/-- Exact elementary improvement over the earlier factor-two bound. -/
theorem harmonic_le_sieveMass (R : ℕ) : (harmonic R : ℝ) ≤ sieveMass R := by
  have hmap : ∀ n ∈ Ioc 0 R, radical n ∈ Ioc 0 R := by
    intro n hn
    exact mem_Ioc.mpr ⟨Nat.pos_of_ne_zero (radical_squarefree n).ne_zero,
      (radical_le (mem_Ioc.mp hn).1).trans (mem_Ioc.mp hn).2⟩
  have hh : (harmonic R : ℝ) = ∑ n ∈ Ioc 0 R, (1:ℝ)/n := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    rfl
  rw [hh, ← sum_fiberwise_of_maps_to hmap]
  exact sum_le_sum (fun d _ => radical_fiber_reciprocal_bound R d)

theorem log_le_sieveMass (R : ℕ) : Real.log (R+1) ≤ sieveMass R := by
  have hh := log_add_one_le_harmonic R
  push_cast at hh
  exact hh.trans (harmonic_le_sieveMass R)

#print axioms hasSum_factored_reciprocal
#print axioms harmonic_le_sieveMass
#print axioms log_le_sieveMass

end Erdos972SharpSieveMassLower
