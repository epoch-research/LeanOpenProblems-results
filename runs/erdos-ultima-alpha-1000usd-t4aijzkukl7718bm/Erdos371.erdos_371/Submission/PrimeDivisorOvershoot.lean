import Submission.PrimeResidueSelberg
import Submission.WeightedPrimeHarmonic

/-! Cofactor compression for large prime products with a small marked prime.
The number of prime-divisor marks, not just their union, is bounded. -/
namespace Erdos371.FiniteSieve
open Finset
set_option autoImplicit false

def primeDivisorOvershoot (D p b : ℕ) : Finset (ℕ×ℕ) :=
  (Icc 1 D ×ˢ (D+1).primesBelow).filter fun mq =>
    mq.2 ∣ mq.1 ∧ D < p*mq.2 ∧ Nat.ModEq p mq.1 b

lemma primeDivisorOvershoot_cofactor_bound (D p b z : ℕ)
    (hsize : p*z ≤ D) :
    (primeDivisorOvershoot D p b).card ≤
      ∑ a ∈ Ico 1 p, ((range (D/a+1)).filter
        (fun q => q.Prime ∧ z<q ∧ Nat.ModEq p (a*q) b)).card := by
  rw [← card_sigma]
  apply card_le_card_of_injOn (fun mq : ℕ×ℕ => (⟨mq.1/mq.2,mq.2⟩ : Σ _a : ℕ, ℕ))
  · intro mq hmq
    obtain ⟨hmq,hd,hlarge,hmod⟩ := mem_filter.mp hmq
    obtain ⟨hm,hq⟩ := mem_product.mp hmq
    obtain ⟨hm1,hmD⟩ := mem_Icc.mp hm
    have hqp := (Nat.mem_primesBelow.mp hq).2
    have hqm := Nat.le_of_dvd (by omega : 0 < mq.1) hd
    have ha : 0 < mq.1/mq.2 := Nat.div_pos hqm hqp.pos
    have he : (mq.1/mq.2)*mq.2=mq.1 := Nat.div_mul_cancel hd
    have hap : mq.1/mq.2 < p := by nlinarith
    have hzq : z < mq.2 := by nlinarith
    have hqD : mq.2 ≤ D/(mq.1/mq.2) := (Nat.le_div_iff_mul_le ha).mpr (by nlinarith)
    simp only [mem_coe,mem_sigma,mem_Ico,mem_filter,mem_range]
    refine ⟨⟨ha,hap⟩,by omega,hqp,hzq,?_⟩
    simpa only [he] using hmod
  · intro mq hmq nr hnr he
    have hmq' := mem_filter.mp hmq
    have hnr' := mem_filter.mp hnr
    have ha : mq.1/mq.2=nr.1/nr.2 := congrArg Sigma.fst he
    have hq : mq.2=nr.2 := congrArg (fun x : Σ _a : ℕ, ℕ => x.2) he
    have hm := Nat.div_mul_cancel hmq'.2.1
    have hn := Nat.div_mul_cancel hnr'.2.1
    apply Prod.ext _ hq
    rw [ha,hq] at hm
    omega

lemma primeDivisorOvershoot_bound (D p b z : ℕ) (hp : p.Prime) (hz : 1 ≤ z)
    (hpD : p ≤ D) (hsize : p*z ≤ D) :
    ((primeDivisorOvershoot D p b).card : ℝ) ≤
      4*Real.exp 2*D*(1+Real.log p)/(p*Real.log (z+1 : ℝ))+
      2*(p : ℝ)^9*(z+1 : ℝ)^32 := by
  have hlog : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcount := (Nat.cast_le (α := ℝ)).mpr (primeDivisorOvershoot_cofactor_bound D p b z hsize)
  rw [Nat.cast_sum] at hcount
  have hpoint (a : ℕ) (ha : a ∈ Ico 1 p) :
      (((range (D/a+1)).filter (fun q => q.Prime ∧ z<q ∧ Nat.ModEq p (a*q) b)).card : ℝ) ≤
        (4*Real.exp 2*D/(p*Real.log (z+1 : ℝ)))*(1/(a : ℝ))+
          2*(p : ℝ)^8*(z+1 : ℝ)^32 := by
    obtain ⟨ha1,hap⟩ := mem_Ico.mp ha
    have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have hcop : p.Coprime a := hp.coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd (by omega : 0 < a) hd
      omega)
    have ht := prime_linear_congruence_bound p a b (D/a+1) z hp hcop hz
    have haD : (a : ℝ) ≤ D := by exact_mod_cast hap.le.trans hpD
    have hL : ((D/a+1 : ℕ) : ℝ) ≤ 2*D/(a : ℝ) := by
      rw [Nat.cast_add,Nat.cast_one]
      have hd := Nat.cast_div_le (m := D) (n := a) (α := ℝ)
      have h1 : (1 : ℝ) ≤ D/(a : ℝ) := (le_div_iff₀ haR).mpr (by simpa using haD)
      rw [mul_div_assoc]
      linarith
    apply ht.trans
    apply add_le_add _ le_rfl
    have hh := mul_le_mul_of_nonneg_left hL
      (by positivity : (0 : ℝ) ≤ 2*Real.exp 2/(p*Real.log (z+1 : ℝ)))
    convert hh using 1 <;> ring
  have hs := hcount.trans (sum_le_sum hpoint)
  rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul] at hs
  have hcard : ((Ico 1 p).card : ℝ) ≤ p := by
    exact_mod_cast (show (Ico 1 p).card ≤ p by simp)
  have hsum : (∑ a ∈ Ico 1 p, (1 : ℝ)/a) ≤ 1+Real.log p := by
    calc
      _ ≤ ∑ a ∈ Icc 1 p, (1 : ℝ)/a :=
        sum_le_sum_of_subset_of_nonneg (Ico_subset_Icc_self) (fun _ _ _ => by positivity)
      _ = harmonic p := by simp [harmonic_eq_sum_Icc,one_div]
      _ ≤ _ := harmonic_le_one_add_log p
  have hmain := mul_le_mul_of_nonneg_left hsum
    (by positivity : (0 : ℝ) ≤ 4*Real.exp 2*D/(p*Real.log (z+1 : ℝ)))
  have herr := mul_le_mul_of_nonneg_right hcard
    (by positivity : (0 : ℝ) ≤ 2*(p : ℝ)^8*(z+1 : ℝ)^32)
  apply hs.trans
  convert add_le_add hmain herr using 1 <;> ring

lemma prime_log_harmonic_weight_bound (X : ℕ) (hX : 1 ≤ X) :
    (∑ p ∈ (X+1).primesBelow, (1+Real.log p)/(p : ℝ)) ≤ 9*Real.log (X+1 : ℝ) := by
  have hp (p : ℕ) (hp : p ∈ (X+1).primesBelow) : 1 ≤ 2*Real.log p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
    have hl := Real.log_le_log (by norm_num : (0 : ℝ)<2) hp2
    linarith [Real.log_two_gt_d9]
  have hs : (∑ p ∈ (X+1).primesBelow, (1+Real.log p)/(p : ℝ)) ≤ 3*primeLogHarmonic X := by
    unfold primeLogHarmonic
    rw [mul_sum]
    apply sum_le_sum
    intro p hpp
    have hh := div_le_div_of_nonneg_right (show 1+Real.log p ≤ 3*Real.log p by linarith [hp p hpp])
      (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
    convert hh using 1; ring
  have hu := primeLogHarmonic_upper X (by omega)
  have hlX : Real.log X ≤ Real.log (X+1 : ℝ) := Real.log_le_log
    (by exact_mod_cast (show 0 < X by omega)) (by linarith)
  have hl2 : Real.log 2 ≤ Real.log (X+1 : ℝ) := Real.log_le_log
    (by norm_num) (by exact_mod_cast (show 2 ≤ X+1 by omega))
  have hl4 : Real.log 4 = 2*Real.log 2 := by rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  linarith

/-- Summing all small marked primes and both opposite residues still costs
only log(X), not log(X)*loglog(X), in the main term. -/
theorem small_prime_overshoot_total_bound (D X z : ℕ) (hX : 1 ≤ X) (hXD : X ≤ D)
    (hz : 1 ≤ z) (hsize : X*z ≤ D) :
    (∑ p ∈ (X+1).primesBelow,
      (((primeDivisorOvershoot D p 1).card : ℝ)+(primeDivisorOvershoot D p (p-1)).card)) ≤
      72*Real.exp 2*D*Real.log (X+1 : ℝ)/Real.log (z+1 : ℝ)+
      4*(X+1 : ℝ)^10*(z+1 : ℝ)^32 := by
  have hlog : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  have hpoint (p : ℕ) (hp : p ∈ (X+1).primesBelow) :
      ((primeDivisorOvershoot D p 1).card : ℝ)+(primeDivisorOvershoot D p (p-1)).card ≤
      8*Real.exp 2*D/Real.log (z+1 : ℝ)*((1+Real.log p)/(p : ℝ))+
        4*(X+1 : ℝ)^9*(z+1 : ℝ)^32 := by
    obtain ⟨hpX,hpp⟩ := Nat.mem_primesBelow.mp hp
    have hpD : p ≤ D := (by omega : p ≤ X).trans hXD
    have hps : p*z ≤ D := (Nat.mul_le_mul_right z (by omega : p ≤ X)).trans hsize
    have h1 := primeDivisorOvershoot_bound D p 1 z hpp hz hpD hps
    have h2 := primeDivisorOvershoot_bound D p (p-1) z hpp hz hpD hps
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
      (by exact_mod_cast hpX.le : (p : ℝ) ≤ X+1) 9
    have hh := mul_le_mul_of_nonneg_right hpow (by positivity : (0 : ℝ) ≤ 4*(z+1 : ℝ)^32)
    have hb := add_le_add h1 h2
    have he : 4*Real.exp 2*D*(1+Real.log p)/(p*Real.log (z+1 : ℝ))+
      2*(p : ℝ)^9*(z+1 : ℝ)^32+
      (4*Real.exp 2*D*(1+Real.log p)/(p*Real.log (z+1 : ℝ))+
      2*(p : ℝ)^9*(z+1 : ℝ)^32) =
      8*Real.exp 2*D/Real.log (z+1 : ℝ)*((1+Real.log p)/(p : ℝ))+
        4*(p : ℝ)^9*(z+1 : ℝ)^32 := by ring
    rw [he] at hb
    exact hb.trans (add_le_add le_rfl (by convert hh using 1 <;> ring))
  have hs := sum_le_sum hpoint
  simp only [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul] at hs
  rw [sum_add_distrib]
  have hmain := mul_le_mul_of_nonneg_left (prime_log_harmonic_weight_bound X hX)
    (by positivity : (0 : ℝ) ≤ 8*Real.exp 2*D/Real.log (z+1 : ℝ))
  have hcard : ((X+1).primesBelow.card : ℝ) ≤ X+1 := by
    exact_mod_cast (card_le_card (filter_subset Nat.Prime (range (X+1)))).trans_eq (card_range (X+1))
  have herr := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ 4*(X+1 : ℝ)^9*(z+1 : ℝ)^32)
  apply hs.trans
  convert add_le_add hmain herr using 1 <;> ring

#print axioms primeDivisorOvershoot_bound
#print axioms small_prime_overshoot_total_bound
end Erdos371.FiniteSieve
