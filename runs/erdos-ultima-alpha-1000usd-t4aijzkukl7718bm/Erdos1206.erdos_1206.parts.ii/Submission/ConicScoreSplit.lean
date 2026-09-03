import Submission.ConicSmallPrimeVariance
import Submission.QuadraticScoreTailBounds
import Submission.SquarefreeSummablePrimeObstruction

/-! Small/large prime decomposition of the four-form score contrast. -/
namespace Erdos1206.ConicScoreSplit
open Finset SquarefreeConicFamily QuadraticPrimeMoments QuadraticScoreTailBounds
  QuadraticEqualDiscriminant ConicPrimeCovariance DualPrimeConditionalCounts
  QuadraticConditionalCounts QuadraticSquarefreeSieve BoxDensityLimits
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def smallPrimes (S : Finset ℕ) (T : ℕ) : Finset ℕ :=
  (range (T+1)).filter (fun p => p.Prime ∧ p∉S)

noncomputable def totalContrast (w : ℕ → ℝ) (x : ℕ × ℕ) : ℝ :=
  ∑i,sign i*primeScore w (F i x.1 x.2)

noncomputable def largeContrast (w : ℕ → ℝ) (T : ℕ) (x : ℕ × ℕ) : ℝ :=
  ∑i,sign i*largeScore w T (F i x.1 x.2)

lemma F_pos (i : Fin 4) {x : ℕ × ℕ} (hx : 0<x.1) : 0<F i x.1 x.2 := by
  have hc : 0<c i := by fin_cases i <;> norm_num [c]
  dsimp only [F,quad]
  positivity

lemma score_split (S : Finset ℕ) (hS : ∀p∈S,p.Prime) (T : ℕ)
    (w : ℕ → ℝ) (i : Fin 4) {x : ℕ × ℕ} (hx0 : 0<x.1) (hx : Head a b c S x) :
    primeScore w (F i x.1 x.2)=
      (∑p∈smallPrimes S T,w p*indicator (a i) (b i) (c i) p x)+
        largeScore w T (F i x.1 x.2) := by
  have he : (F i x.1 x.2).primeFactors.filter (fun p => p≤T)=
      (smallPrimes S T).filter (fun p => p∣F i x.1 x.2) := by
    ext p
    simp only [smallPrimes,mem_filter,mem_range,Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp,hd,hn⟩,hT⟩
      refine ⟨⟨by omega,hp,?_⟩,hd⟩
      exact fun hpS => (mem_head a b c S hS x).mp hx p hpS i hd
    · rintro ⟨⟨hT,hp,hpS⟩,hd⟩
      exact ⟨⟨hp,hd,(F_pos i hx0).ne'⟩,by omega⟩
  have hsmall : (∑p∈(F i x.1 x.2).primeFactors.filter (fun p => p≤T),w p)=
      ∑p∈smallPrimes S T,w p*indicator (a i) (b i) (c i) p x := by
    rw [he,sum_filter]
    apply sum_congr rfl
    intro p hp
    dsimp only [indicator,F]
    split_ifs <;> simp
  have hsplit := sum_filter_add_sum_filter_not (F i x.1 x.2).primeFactors
    (fun p => p≤T) w
  simpa only [hsmall,not_le,primeScore,largeScore,largeFactors] using hsplit.symm

lemma contrast_split (S : Finset ℕ) (hS : ∀p∈S,p.Prime) (T : ℕ)
    (w : ℕ → ℝ) {x : ℕ × ℕ} (hx0 : 0<x.1) (hx : Head a b c S x) :
    totalContrast w x=ConicSmallPrimeVariance.score (smallPrimes S T) w x+largeContrast w T x := by
  dsimp only [totalContrast,largeContrast,ConicSmallPrimeVariance.score,contrast]
  simp_rw [score_split S hS T w _ hx0 hx,mul_add,sum_add_distrib,mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intros
  ring

lemma F_height (i : Fin 4) {N : ℕ} {x : ℕ × ℕ} (hx : x∈range N ×ˢ range N) :
    F i x.1 x.2≤1000000*N^2 := by
  have ht : x.1≤N := (mem_range.mp (mem_product.mp hx).1).le
  have hu : x.2≤N := (mem_range.mp (mem_product.mp hx).2).le
  calc
    _ ≤ a i*N^2+b i*N*N+c i*N^2 := by dsimp [F,quad]; gcongr
    _ = (a i+b i+c i)*N^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (coefficient_bounds i).2.2.2

lemma F_power_height (i : Fin 4) {T : ℕ} (hT : 1000000≤T) {x : ℕ × ℕ}
    (hx : x∈range (T^8) ×ˢ range (T^8)) : F i x.1 x.2≤T^17 := by
  calc
    _ ≤ 1000000*(T^8)^2 := F_height i hx
    _ ≤ T*(T^8)^2 := Nat.mul_le_mul_right _ hT
    _ = _ := by ring

lemma largeContrast_sq_le (w : ℕ → ℝ) {T : ℕ} (hT : 1000000≤T) {x : ℕ × ℕ}
    (hx : x∈range (T^8) ×ˢ range (T^8)) (hx0 : 0<x.1) :
    largeContrast w T x^2 ≤ 68*∑i,primeScore (fun p => if T<p then w p^2 else 0) (F i x.1 x.2) := by
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin 4)) sign
    (fun i => largeScore w T (F i x.1 x.2))
  simp only [sign_sq,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcs
  calc
    _ ≤ 4*∑i,largeScore w T (F i x.1 x.2)^2 := hcs
    _ ≤ 4*∑i,(17:ℝ)*primeScore (fun p => if T<p then w p^2 else 0) (F i x.1 x.2) := by
      gcongr with i
      exact largeScore_sq_le w (by omega) (F_pos i hx0) (F_power_height i hT hx)
    _ = _ := by rw [←mul_sum]; ring

lemma indicator_sq_score_le (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    (w : ℕ → ℝ) (i : Fin 4) {x : ℕ × ℕ} (hx0 : 0<x.1) :
    (∑p∈P,w p^2*indicator (a i) (b i) (c i) p x)≤primeScore (fun p => w p^2) (F i x.1 x.2) := by
  have he : (∑p∈P,w p^2*indicator (a i) (b i) (c i) p x)=
      ∑p∈P.filter (fun p => p∣F i x.1 x.2),w p^2 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    dsimp only [indicator,F]
    split_ifs <;> simp
  rw [he]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hP p (mem_filter.mp hp).1,(mem_filter.mp hp).2,(F_pos i hx0).ne'⟩
  · intros; exact sq_nonneg _

lemma diagonal_sum_le (S P : Finset ℕ) (hP : ∀p∈P,p.Prime) (w : ℕ → ℝ) (N : ℕ) :
    (∑p∈P,w p^2*∑i,((counts a b c S i N p).card:ℝ)) ≤
      ∑i,∑x∈positiveBox N (Head a b c S),primeScore (fun p => w p^2) (F i x.1 x.2) := by
  have he : (∑p∈P,w p^2*∑i,((counts a b c S i N p).card:ℝ))=
      ∑i,∑x∈positiveBox N (Head a b c S),∑p∈P,w p^2*indicator (a i) (b i) (c i) p x := by
    simp_rw [←sum_indicator,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    exact sum_comm
  rw [he]
  apply sum_le_sum
  intro i hi
  apply sum_le_sum
  intro x hx
  exact indicator_sq_score_le P hP w i (mem_filter.mp hx).2.1

#print axioms contrast_split
#print axioms largeContrast_sq_le
#print axioms diagonal_sum_le
end Erdos1206.ConicScoreSplit
