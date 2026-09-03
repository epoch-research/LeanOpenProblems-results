import Submission.ConicPrimeCovariance
import Submission.SharpPrimeBlockVariance

/-! A finite-prime second moment for the inner-minus-outer conic contrast.
The main terms at distinct primes cancel. This is not a Sidon construction. -/
namespace Erdos1206.ConicSmallPrimeVariance
open Finset SquarefreeConicFamily ConicPrimeCovariance DualPrimeConditionalCounts
  QuadraticConditionalCounts BoxDensityLimits
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def score (P : Finset ℕ) (w : ℕ → ℝ) (x : ℕ × ℕ) : ℝ :=
  ∑p∈P,w p*contrast p x

noncomputable def variance (S P : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑x∈positiveBox N (Head a b c S),score P w x^2

lemma variance_expand (S P : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) :
    variance S P w N=∑p∈P,∑q∈P,w p*w q*covariance S N p q := by
  simp only [variance,score,pow_two,sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  simp only [covariance,mul_sum]
  apply sum_congr rfl
  intro x hx
  ring

lemma error_nonneg (S : Finset ℕ) (N p q : ℕ) : 0≤ error S N p q := by
  dsimp [error,modulus]
  positivity

noncomputable def maxError (S : Finset ℕ) (N T : ℕ) : ℝ :=
  2*(N:ℝ)*modulus S*(T:ℝ)^2+(modulus S)^2*(T:ℝ)^4+N

lemma error_le_maxError (S : Finset ℕ) (N : ℕ) {p q T : ℕ}
    (hp : p≤T) (hq : q≤T) : error S N p q≤ maxError S N T := by
  have hD : 0≤ modulus S := by dsimp [modulus]; positivity
  have hpR : (p:ℝ)≤T := by exact_mod_cast hp
  have hqR : (q:ℝ)≤T := by exact_mod_cast hq
  calc
    _ ≤ 2*(N:ℝ)*(modulus S*T*T)+(modulus S*T*T)^2+N := by
      dsimp only [error]
      gcongr
    _ = _ := by dsimp [maxError]; ring

lemma weighted_bound (S P : Finset ℕ) (hS : ∀p∈S,p.Prime) (w : ℕ → ℝ)
    (N T : ℕ) (hP : ∀p∈P,p.Prime ∧ p∉S ∧ 1000000<p ∧ p≤T) :
    variance S P w N ≤
      4*(∑p∈P,w p^2*∑i,((counts a b c S i N p).card:ℝ))+
      16*maxError S N T*(∑p∈P,|w p|)^2 := by
  have hE : 0≤ maxError S N T := (error_nonneg S N T T).trans (error_le_maxError S N le_rfl le_rfl)
  have hterm (p : ℕ) (hp : p∈P) (q : ℕ) (hq : q∈P) :
      w p*w q*covariance S N p q ≤
        (if p=q then 4*w p^2*∑i,((counts a b c S i N p).card:ℝ) else 0)+
        16*maxError S N T* |w p| * |w q| := by
    by_cases he : p=q
    · subst q
      rw [if_pos rfl]
      have hh := mul_le_mul_of_nonneg_left (diagonal_bound S N p) (sq_nonneg (w p))
      calc
        _ = w p^2*covariance S N p p := by ring
        _ ≤ w p^2*(4*∑i,((counts a b c S i N p).card:ℝ)) := hh
        _ = 4*w p^2*∑i,((counts a b c S i N p).card:ℝ) := by ring
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · rw [if_neg he,zero_add]
      have hc := (off_diagonal_bound S hS N (hP p hp).1 (hP q hq).1 he
        (hP p hp).2.1 (hP q hq).2.1 (hP p hp).2.2.1).trans
        (mul_le_mul_of_nonneg_left (error_le_maxError S N (hP p hp).2.2.2 (hP q hq).2.2.2) (by norm_num))
      calc
        _ ≤ |w p*w q*covariance S N p q| := le_abs_self _
        _ = |w p| * |w q| * |covariance S N p q| := by rw [abs_mul,abs_mul]
        _ ≤ |w p| * |w q| *(16*maxError S N T) := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = _ := by ring
  rw [variance_expand]
  calc
    _ ≤ ∑p∈P,∑q∈P,((if p=q then 4*w p^2*∑i,((counts a b c S i N p).card:ℝ) else 0)+
        16*maxError S N T* |w p| * |w q|) :=
      sum_le_sum (fun p hp => sum_le_sum (fun q hq => hterm p hp q hq))
    _ = _ := by
      simp only [sum_add_distrib]
      have hdiag (p : ℕ) (hp : p∈P) :
          (∑q∈P,if p=q then 4*w p^2*∑i,((counts a b c S i N p).card:ℝ) else 0)=
            4*w p^2*∑i,((counts a b c S i N p).card:ℝ) := by simp [hp]
      rw [sum_congr rfl hdiag]
      congr 1
      · rw [mul_sum]
        apply sum_congr rfl
        intros
        ring
      · simp only [pow_two,mul_sum,sum_mul]
        apply sum_congr rfl
        intro p hp
        apply sum_congr rfl
        intros
        ring

lemma weighted_energy_bound (S P : Finset ℕ) (hS : ∀p∈S,p.Prime) (w : ℕ → ℝ)
    (N T : ℕ) (hP : ∀p∈P,p.Prime ∧ p∉S ∧ 1000000<p ∧ p≤T) :
    variance S P w N ≤
      4*(∑p∈P,w p^2*∑i,((counts a b c S i N p).card:ℝ))+
      16*maxError S N T*SharpPrimeBlockVariance.mass P w*(T:ℝ)^2 := by
  have hsub : P⊆Icc 1 T := fun p hp => mem_Icc.mpr ⟨(hP p hp).1.pos,(hP p hp).2.2.2⟩
  have hcard : P.card≤T := by simpa using card_le_card hsub
  have hsum : (∑p∈P,(p:ℝ))≤(T:ℝ)^2 := by
    calc
      _ ≤ ∑_p∈P,(T:ℝ) := sum_le_sum (fun p hp => by exact_mod_cast (hP p hp).2.2.2)
      _ = (P.card:ℝ)*T := by simp
      _ ≤ (T:ℝ)*T := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by ring
  have hcs := (SharpPrimeBlockVariance.weighted_cauchy P w (fun p hp => (hP p hp).1.pos)).trans
    (mul_le_mul_of_nonneg_left hsum (SharpPrimeBlockVariance.mass_nonneg P w))
  have hE : 0≤ maxError S N T := (error_nonneg S N T T).trans (error_le_maxError S N le_rfl le_rfl)
  calc
    _ ≤ _ := weighted_bound S P hS w N T hP
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hcs (show 0≤16*maxError S N T by positivity)
      nlinarith only [hh]

#print axioms weighted_bound
#print axioms weighted_energy_bound
end Erdos1206.ConicSmallPrimeVariance
