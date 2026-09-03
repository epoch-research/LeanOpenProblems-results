import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Lemmas
import Submission.FixedTriangleExtensions

/-! Prime-power restrictions on rational anchor-distance differences at primes
where the quadratic norm is anisotropic. These are necessary conditions only;
they neither bound all denominators nor settle the cardinality conjecture. -/
namespace Erdos213.InertDifferenceDenominators

lemma anisotropic_mod {p : ℕ} [Fact p.Prime] {D x y : ZMod p}
    (hD : ¬ IsSquare (-D)) (h : x^2+D*y^2=0) : x=0 ∧ y=0 := by
  have hy : y=0 := by
    by_contra hy
    apply hD
    refine ⟨x/y,?_⟩
    field_simp
    linear_combination -h
  constructor
  · rw [hy] at h
    simpa using h
  · exact hy

lemma prime_dvd_norm {p : ℕ} [Fact p.Prime] {D x y : ℤ}
    (hD : ¬ IsSquare (-(D : ZMod p))) (h : (p : ℤ)∣x^2+D*y^2) :
    (p : ℤ)∣x ∧ (p : ℤ)∣y := by
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (x^2+D*y^2) p).mpr h
  push_cast at hz
  obtain ⟨hx,hy⟩ := anisotropic_mod hD hz
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx,
    (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy⟩

lemma norm_power_divisibility {p : ℕ} [Fact p.Prime] {D : ℤ}
    (hD : ¬ IsSquare (-(D : ZMod p))) (e : ℕ) {x y : ℤ}
    (h : (p : ℤ)^(2*e)∣x^2+D*y^2) : (p : ℤ)^e∣x ∧ (p : ℤ)^e∣y := by
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  induction e generalizing x y with
  | zero => simp
  | succ e ih =>
    have hp1 : (p : ℤ)∣x^2+D*y^2 :=
      (dvd_pow_self (p : ℤ) (by omega : 2*(e+1)≠0)).trans h
    obtain ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩ := prime_dvd_norm hD hp1
    rw [show 2*(e+1)=2+2*e by omega,pow_add] at h
    have hh : (p : ℤ)^2*(p : ℤ)^(2*e)∣(p : ℤ)^2*(u^2+D*v^2) := by
      convert h using 1
      ring
    have hh' := (mul_dvd_mul_iff_left (pow_ne_zero 2 hp.ne_zero)).mp hh
    obtain ⟨hu,hv⟩ := ih hh'
    constructor
    · simpa only [pow_succ,mul_comm] using mul_dvd_mul_left (p : ℤ) hu
    · simpa only [pow_succ,mul_comm] using mul_dvd_mul_left (p : ℤ) hv

lemma cancel_square_factor {s F : ℤ} (hs : s≠0)
    (h : IsSquare ((s : ℚ)^2*(F : ℚ))) : IsSquare F := by
  rw [← Rat.isSquare_intCast_iff]
  obtain ⟨t,ht⟩ := h
  refine ⟨t/(s : ℚ),?_⟩
  have hsQ : (s : ℚ)≠0 := by exact_mod_cast hs
  field_simp
  linear_combination ht

/-- At an inert prime power dividing the common denominator, the product of
the three scaled differences must vanish modulo that whole prime power. -/
lemma prime_power_product {p : ℕ} [Fact p.Prime] {D a b c q k l : ℤ}
    (hD : ¬ IsSquare (-(D : ZMod p))) (e : ℕ) (hq : (p : ℤ)^e∣q)
    (h : IsSquare (D*((a*q)^2-k^2)*((b*q)^2-l^2)*((c*q)^2-(k-l)^2))) :
    (p : ℤ)^e∣k*l*(k-l) := by
  obtain ⟨t,ht⟩ := h
  have hid : t^2+D*(k*l*(k-l))^2 = q^2 * (D *
      (a^2*b^2*c^2*q^4 -
       q^2*(a^2*b^2*(k-l)^2+a^2*c^2*l^2+b^2*c^2*k^2) +
       a^2*l^2*(k-l)^2+b^2*k^2*(k-l)^2+c^2*k^2*l^2)) := by
    rw [sq,← ht]
    ring
  have hpow : (p : ℤ)^(2*e)∣q^2 := by
    simpa only [pow_mul,mul_comm] using pow_dvd_pow_of_dvd hq 2
  have hn : (p : ℤ)^(2*e)∣t^2+D*(k*l*(k-l))^2 := by
    rw [hid]
    exact dvd_mul_of_dvd_left hpow _
  exact (norm_power_divisibility hD e hn).2

/-- If the denominator is primitive at p, at most one of the three difference
factors is p-divisible; hence the full required p^e divides one factor. -/
theorem prime_power_three_lines {p : ℕ} [Fact p.Prime] {D a b c q k l : ℤ}
    (hD : ¬ IsSquare (-(D : ZMod p))) (e : ℕ) (hq : (p : ℤ)^e∣q)
    (hkl : ¬ ((p : ℤ)∣k ∧ (p : ℤ)∣l))
    (h : IsSquare (D*((a*q)^2-k^2)*((b*q)^2-l^2)*((c*q)^2-(k-l)^2))) :
    (p : ℤ)^e∣k ∨ (p : ℤ)^e∣l ∨ (p : ℤ)^e∣k-l := by
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  have hv := prime_power_product hD e hq h
  by_cases hk : (p : ℤ)∣k
  · have hl : ¬ (p : ℤ)∣l := fun hl => hkl ⟨hk,hl⟩
    have hd : ¬ (p : ℤ)∣k-l := by
      intro hd
      apply hl
      simpa only [sub_sub_cancel] using dvd_sub hk hd
    exact Or.inl (hp.pow_dvd_of_dvd_mul_right e hl
      (hp.pow_dvd_of_dvd_mul_right e hd hv))
  · have hv' : (p : ℤ)^e∣l*(k-l) := by
      apply hp.pow_dvd_of_dvd_mul_left e hk
      simpa only [mul_assoc] using hv
    by_cases hl : (p : ℤ)∣l
    · have hd : ¬ (p : ℤ)∣k-l := by
        intro hd
        apply hk
        simpa only [sub_add_cancel] using dvd_add hd hl
      exact Or.inr (Or.inl (hp.pow_dvd_of_dvd_mul_right e hd hv'))
    · exact Or.inr (Or.inr (hp.pow_dvd_of_dvd_mul_left e hl hv'))

lemma cancel_integer_square_factor {s F : ℤ} (hs : s≠0)
    (h : IsSquare (s^2*F)) : IsSquare F := by
  apply cancel_square_factor hs
  obtain ⟨t,ht⟩ := h
  refine ⟨(t : ℚ),?_⟩
  exact_mod_cast ht

/-- The primitivity assumption can be removed by cancelling common powers of p
from q,k,l. This is still only a necessary denominator restriction. -/
theorem prime_power_three_lines_general {p : ℕ} [Fact p.Prime]
    {D a b c : ℤ} (hD : ¬ IsSquare (-(D : ZMod p))) (e : ℕ)
    {q k l : ℤ} (hq : (p : ℤ)^e∣q)
    (h : IsSquare (D*((a*q)^2-k^2)*((b*q)^2-l^2)*((c*q)^2-(k-l)^2))) :
    (p : ℤ)^e∣k ∨ (p : ℤ)^e∣l ∨ (p : ℤ)^e∣k-l := by
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  induction e generalizing q k l with
  | zero => simp
  | succ e ih =>
    by_cases hkl : ¬ ((p : ℤ)∣k ∧ (p : ℤ)∣l)
    · exact prime_power_three_lines hD (e+1) hq hkl h
    push_neg at hkl
    obtain ⟨⟨k,rfl⟩,⟨l,rfl⟩⟩ := hkl
    have hpq : (p : ℤ)∣q := (dvd_pow_self (p : ℤ) (by omega : e+1≠0)).trans hq
    obtain ⟨q,rfl⟩ := hpq
    have hq' : (p : ℤ)^e∣q := by
      apply (mul_dvd_mul_iff_left hp.ne_zero).mp
      simpa only [pow_succ,mul_comm] using hq
    have hf : IsSquare (((p : ℤ)^3)^2 *
        (D*((a*q)^2-k^2)*((b*q)^2-l^2)*((c*q)^2-(k-l)^2))) := by
      convert h using 1
      ring
    have hf' := cancel_integer_square_factor (pow_ne_zero 3 hp.ne_zero) hf
    rcases ih hq' hf' with hk | hl | hd
    · left
      simpa only [pow_succ,mul_comm] using mul_dvd_mul_left (p : ℤ) hk
    · right; left
      simpa only [pow_succ,mul_comm] using mul_dvd_mul_left (p : ℤ) hl
    · right; right
      have hmul := mul_dvd_mul_left (p : ℤ) hd
      simpa only [pow_succ,mul_comm,mul_sub,sub_mul] using hmul

open FixedTriangleExtensions in
/-- Bridge from the rational radius equation to the integral square-class test.
The radius itself need not be integral or have a prescribed denominator. -/
theorem rational_radius_three_lines {p : ℕ} [Fact p.Prime]
    {D a b c q k l s : ℤ} {r : ℚ}
    (hD : ¬ IsSquare (-(D : ZMod p))) (e : ℕ) (hq : (p : ℤ)^e∣q)
    (hs : s≠0)
    (hH : heron (a*q) (b*q) (c*q)=s^2*D)
    (hr : qa ((a*q : ℤ) : ℚ) ((b*q : ℤ) : ℚ) ((c*q : ℤ) : ℚ) k l*r^2+
      qb ((a*q : ℤ) : ℚ) ((b*q : ℤ) : ℚ) ((c*q : ℤ) : ℚ) k l*r+
      qc ((a*q : ℤ) : ℚ) ((b*q : ℤ) : ℚ) ((c*q : ℤ) : ℚ) k l=0) :
    (p : ℤ)^e∣k ∨ (p : ℤ)^e∣l ∨ (p : ℤ)^e∣k-l := by
  have hh : heron ((a*q : ℤ) : ℚ) ((b*q : ℤ) : ℚ) ((c*q : ℤ) : ℚ)=
      (s : ℚ)^2*(D : ℚ) := by
    unfold heron at hH ⊢
    exact_mod_cast hH
  have hv := radius_isSquare hr
  rw [hh] at hv
  have hi : IsSquare ((s : ℚ)^2 *
      ((D*((a*q)^2-k^2)*((b*q)^2-l^2)*((c*q)^2-(k-l)^2) : ℤ) : ℚ)) := by
    convert hv using 1
    push_cast
    ring
  exact prime_power_three_lines_general hD e hq (cancel_square_factor hs hi)

open FixedTriangleExtensions in
/-- End-to-end metric form for the normalized triangle with vertices 0,a*q,z.
All radius and anchor-distance hypotheses refer to actual Euclidean distances. -/
theorem complex_metric_three_lines {p : ℕ} [Fact p.Prime]
    {D a b c q k l s : ℤ} {r : ℚ} {z P : ℂ}
    (hD : ¬ IsSquare (-(D : ZMod p))) (e : ℕ) (hq : (p : ℤ)^e∣q)
    (hs : s≠0) (hH : heron (a*q) (b*q) (c*q)=s^2*D)
    (hn : ‖z‖=((b*q : ℤ) : ℝ))
    (hc : dist z ((((a*q : ℤ) : ℝ)) : ℂ)=((c*q : ℤ) : ℝ))
    (hr : ‖P‖=(r : ℝ))
    (hk : dist P ((((a*q : ℤ) : ℝ)) : ℂ)=(r : ℝ)+(k : ℝ))
    (hl : dist P z=(r : ℝ)+(l : ℝ)) :
    (p : ℤ)^e∣k ∨ (p : ℤ)^e∣l ∨ (p : ℤ)^e∣k-l := by
  apply rational_radius_three_lines (r := r) hD e hq hs hH
  have he := complex_radius_equation hn hc hr hk hl
  unfold qa qb qc heron at he ⊢
  exact_mod_cast he

lemma characteristic2002_inert_three : ¬ IsSquare (-(2002 : ZMod 3)) := by
  decide

lemma characteristic2002_inert_five : ¬ IsSquare (-(2002 : ZMod 5)) := by
  decide

/-- Without the inertness hypothesis the three-line restriction is false.
This is an arithmetic control, not a GP configuration. -/
lemma split_prime_arithmetic_control :
    IsSquare (-(1 : ZMod 17)) ∧
    IsSquare ((102^2-60^2)*(85^2-5^2)*(85^2-55^2) : ℤ) ∧
    ¬ ((17 : ℤ)∣60 ∨ (17 : ℤ)∣5 ∨ (17 : ℤ)∣55) := by
  exact ⟨⟨4,by decide⟩,⟨453600,by norm_num⟩,by decide⟩

open FixedTriangleExtensions in
lemma split_prime_radius_control :
    heron (102 : ℚ) 85 85=13872^2 ∧
    qa (102 : ℚ) 85 85 60 5*45^2+qb (102 : ℚ) 85 85 60 5*45+
      qc (102 : ℚ) 85 85 60 5=0 := by
  norm_num [heron,qa,qb,qc]

#print axioms complex_metric_three_lines
#print axioms split_prime_arithmetic_control
#print axioms split_prime_radius_control
#print axioms prime_power_three_lines_general
#print axioms rational_radius_three_lines
#print axioms characteristic2002_inert_three
#print axioms characteristic2002_inert_five
#print axioms anisotropic_mod
#print axioms norm_power_divisibility
#print axioms cancel_square_factor
#print axioms prime_power_product
#print axioms prime_power_three_lines
end Erdos213.InertDifferenceDenominators
