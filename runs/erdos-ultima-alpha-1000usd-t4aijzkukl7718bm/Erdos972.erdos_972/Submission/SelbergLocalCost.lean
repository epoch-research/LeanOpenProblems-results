import Submission.PairSieve

/-! Local divisibility costs of the actual optimal finite Selberg weights.
These identities are intended for a lower-supported sieve test. -/
namespace Erdos972SelbergLocalCost

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972SelbergWeights

set_option maxHeartbeats 1500000

noncomputable def sieveAtom (n : ℕ) : ℝ := (μ n : ℝ)^2/n.totient

lemma sieveAtom_nonneg (n : ℕ) : 0 ≤ sieveAtom n := by unfold sieveAtom; positivity

noncomputable def coprimeMass (R p : ℕ) : ℝ :=
  ∑ r ∈ Ioc 0 R, if p ∣ r then 0 else sieveAtom r

lemma sum_multiples {p : ℕ} (hp : 0 < p) (R : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Ioc 0 R, if p ∣ n then f n else 0) = ∑ r ∈ Ioc 0 (R/p), f (p*r) := by
  classical
  rw [← sum_filter]
  apply sum_bij' (fun n _ => n/p) (fun r _ => p*r)
  · intro n hn
    obtain ⟨hnR, hpn⟩ := mem_filter.mp hn
    exact mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (mem_Ioc.mp hnR).1 hpn) hp,
      Nat.div_le_div_right (mem_Ioc.mp hnR).2⟩
  · intro r hr
    obtain ⟨hr0, hrR⟩ := mem_Ioc.mp hr
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos hp hr0, ?_⟩, dvd_mul_right _ _⟩
    have hh := (Nat.le_div_iff_mul_le hp).mp hrR
    simpa only [mul_comm p r] using hh
  · intro n hn
    exact Nat.mul_div_cancel' (mem_filter.mp hn).2
  · intro r _
    exact Nat.mul_div_cancel_left r hp
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

lemma sieveAtom_prime_mul {p r : ℕ} (hp : p.Prime) :
    sieveAtom (p*r) = if p ∣ r then 0 else sieveAtom r/(p-1 : ℕ) := by
  by_cases hpr : p ∣ r
  · rw [if_pos hpr]
    have hsq : ¬ Squarefree (p*r) := by
      intro hs
      exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp) (Nat.mul_dvd_mul_left p hpr)
    simp [sieveAtom, moebius_eq_zero_of_not_squarefree hsq]
  · rw [if_neg hpr]
    have hc := hp.coprime_iff_not_dvd.mpr hpr
    simp only [sieveAtom, isMultiplicative_moebius.map_mul_of_coprime hc,
      moebius_apply_prime hp, Nat.totient_mul hc, Nat.totient_prime hp,
      Int.cast_mul, Int.cast_neg, Int.cast_one, Nat.cast_mul]
    ring

lemma sieveMass_split_prime {p : ℕ} (hp : p.Prime) (R : ℕ) :
    sieveMass R = coprimeMass R p+coprimeMass (R/p) p/(p-1 : ℕ) := by
  have he : sieveMass R =
      (∑ r ∈ Ioc 0 R, if p ∣ r then 0 else sieveAtom r)+
      (∑ r ∈ Ioc 0 R, if p ∣ r then sieveAtom r else 0) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun r _ => by split_ifs <;> simp [sieveAtom])
  rw [he, sum_multiples hp.pos]
  congr 1
  simp only [coprimeMass, sum_div]
  apply sum_congr rfl
  intro r _
  rw [sieveAtom_prime_mul hp]
  split_ifs <;> simp

noncomputable def boundedTarget (R r : ℕ) : ℝ :=
  if r ≤ R then targetWeight R r else 0

lemma sum_selberg_multiples_any (R : ℕ) {r : ℕ} (hr : 0 < r) :
    (∑ d ∈ Ioc 0 R, if r ∣ d then selbergWeight R d/d else 0) = boundedTarget R r := by
  by_cases hrR : r ≤ R
  · rw [boundedTarget, if_pos hrR]
    exact sum_selbergWeight_multiples R (mem_Ioc.mpr ⟨hr, hrR⟩)
  · rw [boundedTarget, if_neg hrR]
    apply sum_eq_zero
    intro d hd
    apply if_neg
    intro hrd
    exact hrR ((Nat.le_of_dvd (mem_Ioc.mp hd).1 hrd).trans (mem_Ioc.mp hd).2)

lemma masked_row (R : ℕ) {p r : ℕ} (hp : 0 < p) (hr : 0 < r) :
    (∑ d ∈ Ioc 0 R, if r ∣ d then (if p ∣ d then 0 else selbergWeight R d)/d else 0) =
      boundedTarget R r-boundedTarget R (r.lcm p) := by
  rw [← sum_selberg_multiples_any R hr,
    ← sum_selberg_multiples_any R (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hr.ne' hp.ne')),
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  simp only [Nat.lcm_dvd_iff]
  by_cases hrd : r ∣ d <;> by_cases hpd : p ∣ d <;> simp [hrd, hpd]

noncomputable def localMain (R p : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 R, ∑ e ∈ Ioc 0 R, selbergWeight R d*selbergWeight R e/(d.lcm e).lcm p

lemma localMain_complement {p : ℕ} (hp : p.Prime) (R : ℕ) :
    localMain R p = quadraticMain R (selbergWeight R)-
      (1-1/(p : ℝ))*quadraticMain R (fun d => if p ∣ d then 0 else selbergWeight R d) := by
  simp only [localMain, quadraticMain, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  by_cases hpd : p ∣ d
  · rw [Nat.lcm_eq_left (hpd.trans (Nat.dvd_lcm_left d e)), if_pos hpd]
    simp
  by_cases hpe : p ∣ e
  · rw [Nat.lcm_eq_left (hpe.trans (Nat.dvd_lcm_right d e)), if_pos hpe]
    simp
  have hpl : ¬ p ∣ d.lcm e := by simpa only [hp.dvd_lcm, not_or] using And.intro hpd hpe
  rw [(hp.coprime_iff_not_dvd.mpr hpl).symm.lcm_eq_mul, if_neg hpd, if_neg hpe, Nat.cast_mul]
  ring

lemma target_prime_mul {R p r : ℕ} (hp : p.Prime) (hpr : ¬p ∣ r) :
    targetWeight R (r*p) = -targetWeight R r/(p-1 : ℕ) := by
  have hc := (hp.coprime_iff_not_dvd.mpr hpr).symm
  simp only [targetWeight, isMultiplicative_moebius.map_mul_of_coprime hc,
    moebius_apply_prime hp, Nat.totient_mul hc, Nat.totient_prime hp,
    Int.cast_mul, Int.cast_neg, Int.cast_one, Nat.cast_mul]
  ring

lemma masked_row_square {R p r : ℕ} (hp : p.Prime) (hr : r ∈ Ioc 0 R) :
    (r.totient : ℝ)*(boundedTarget R r-boundedTarget R (r.lcm p))^2 =
      if p ∣ r then 0 else
        (sieveAtom r/(sieveMass R)^2)*
          (if r ≤ R/p then ((p : ℝ)/(p-1 : ℕ))^2 else 1) := by
  by_cases hpr : p ∣ r
  · simp only [if_pos hpr, Nat.lcm_eq_left hpr, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · rw [if_neg hpr, (hp.coprime_iff_not_dvd.mpr hpr).symm.lcm_eq_mul,
      boundedTarget, if_pos (mem_Ioc.mp hr).2, boundedTarget, target_prime_mul hp hpr]
    have htf : (r.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (mem_Ioc.mp hr).1).ne'
    have hpm : ((p-1 : ℕ) : ℝ) = (p : ℝ)-1 := by simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hp.one_le)
    have hpR : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
    have hpn : ((p-1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hp.two_le; omega : p-1 ≠ 0)
    have hi : r*p ≤ R ↔ r ≤ R/p := (Nat.le_div_iff_mul_le hp.pos).symm
    simp only [hi]
    have hG : sieveMass R ≠ 0 := (lt_of_lt_of_le (by norm_num) (one_le_sieveMass (show 1 ≤ R by have := mem_Ioc.mp hr; omega))).ne'
    split_ifs <;> simp only [targetWeight, sieveAtom, sub_zero, mul_one] <;> field_simp
    rw [hpm]
    ring

lemma masked_quadraticMain {R p : ℕ} (_hR : 1 ≤ R) (hp : p.Prime) :
    quadraticMain R (fun d => if p ∣ d then 0 else selbergWeight R d) =
      (coprimeMass R p+(((p : ℝ)/(p-1 : ℕ))^2-1)*coprimeMass (R/p) p)/(sieveMass R)^2 := by
  rw [quadraticMain_diagonal]
  have hrows : (∑ r ∈ Ioc 0 R, (r.totient : ℝ)*
      (∑ d ∈ Ioc 0 R, if r ∣ d then (if p ∣ d then 0 else selbergWeight R d)/d else 0)^2) =
      ∑ r ∈ Ioc 0 R, (r.totient : ℝ)*(boundedTarget R r-boundedTarget R (r.lcm p))^2 := by
    apply sum_congr rfl
    intro r hr
    rw [masked_row R hp.pos (mem_Ioc.mp hr).1]
  rw [hrows]
  have hs : (∑ r ∈ Ioc 0 R,
      (r.totient : ℝ)*(boundedTarget R r-boundedTarget R (r.lcm p))^2) =
      ∑ r ∈ Ioc 0 R, ((if p ∣ r then 0 else sieveAtom r)/(sieveMass R)^2+
        (((p : ℝ)/(p-1 : ℕ))^2-1)/(sieveMass R)^2 *
          (if r ≤ R/p then (if p ∣ r then 0 else sieveAtom r) else 0)) := by
    apply sum_congr rfl
    intro r hr
    rw [masked_row_square hp hr]
    split_ifs <;> ring
  rw [hs, sum_add_distrib, ← sum_div, ← mul_sum, ← sum_filter]
  have hf : (Ioc 0 R).filter (fun r => r ≤ R/p) = Ioc 0 (R/p) := by
    ext r
    simp only [mem_filter, mem_Ioc]
    have hh := Nat.div_le_self R p
    omega
  rw [hf]
  change coprimeMass R p/(sieveMass R)^2+
    (((p : ℝ)/(p-1 : ℕ))^2-1)/(sieveMass R)^2*coprimeMass (R/p) p = _
  ring

/-- The exact local cost is a short interval of the coprime Selberg mass,
not the much larger unsifted proportion 1/p times its full mass. -/
theorem localMain_exact {R p : ℕ} (hR : 1 ≤ R) (hp : p.Prime) :
    localMain R p = (coprimeMass R p-coprimeMass (R/p) p)/((p : ℝ)*(sieveMass R)^2) := by
  rw [localMain_complement hp, quadraticMain_selbergWeight hR, masked_quadraticMain hR hp]
  have hG : sieveMass R ≠ 0 := (lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)).ne'
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpm : ((p-1 : ℕ) : ℝ) = (p : ℝ)-1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hp.one_le)
  have hpn : ((p-1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hp.two_le; omega)
  have hsplit := sieveMass_split_prime hp R
  field_simp at hsplit ⊢
  rw [hpm] at hsplit ⊢
  linear_combination (p : ℝ)*((p : ℝ)-1)*hsplit

#print axioms localMain_exact

end Erdos972SelbergLocalCost
