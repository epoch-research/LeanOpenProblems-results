import Submission.ConicScoreSplit

/-! A convergent upper bound for the full conic contrast second moment. -/
namespace Erdos1206.ConicContrastMoments
open Finset Filter SquarefreeConicFamily QuadraticPrimeMoments QuadraticScoreTailBounds
  ConicScoreSplit ConicSmallPrimeVariance DualPrimeConditionalCounts
  QuadraticConditionalCounts QuadraticSquarefreeSieve BoxDensityLimits
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def energy (w : ℕ → ℝ) : ℝ := ∑'p,if p.Prime then w p^2/p else 0
noncomputable def tailEnergy (w : ℕ → ℝ) (H : ℕ) : ℝ :=
  ∑'p,if p.Prime ∧ H≤p then w p^2/p else 0
noncomputable def constant : ℝ := ∑i : Fin 4,
  (48*QuadraticRootLattice.mass (c i) (b i) (a i)+1:ℝ)
noncomputable def firstMoment (S : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑i,(∑x∈positiveBox N (Head a b c S),primeScore w (F i x.1 x.2))/(N:ℝ)^2
noncomputable def momentLimit (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑i : Fin 4,∑'p,w p^2*frequency a b c S i p
noncomputable def secondMoment (S : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑x∈positiveBox N (Head a b c S),totalContrast w x^2)/(N:ℝ)^2

lemma constant_pos : 0<constant := by
  apply sum_pos _ univ_nonempty
  intro i hi
  positivity

lemma energy_nonneg (w : ℕ → ℝ) : 0≤energy w := by
  apply tsum_nonneg
  intro p
  split_ifs <;> positivity

lemma small_mass_le (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0)) (S : Finset ℕ) (T : ℕ) :
    SharpPrimeBlockVariance.mass (smallPrimes S T) w≤energy w := by
  have hh := hs.sum_le_tsum (smallPrimes S T) (fun p _ => show
      0≤ if p.Prime then w p^2/p else 0 by split_ifs <;> positivity)
  have he (p : ℕ) (hp : p∈smallPrimes S T) :
      (if p.Prime then w p^2/p else 0)=w p^2/p := if_pos (mem_filter.mp hp).2.1
  simpa only [sum_congr rfl he] using hh

lemma firstMoment_upper (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀p,0≤w p)
    (hs : Summable (fun p : ℕ => if p.Prime then w p/p else 0)) (N : ℕ) :
    firstMoment S w N≤constant*(∑'p,if p.Prime then w p/p else 0) := by
  have hcost : 0≤∑'p,if p.Prime then w p/p else 0 := by
    apply tsum_nonneg
    intro p; split_ifs
    · exact div_nonneg (hw p) (Nat.cast_nonneg p)
    · exact le_rfl
  dsimp only [firstMoment,constant]
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  have hc : 0<c i := by fin_cases i <;> norm_num [c]
  calc
    _ ≤ (48*QuadraticRootLattice.mass (c i) (b i) (a i):ℝ)*(∑'p,if p.Prime then w p/p else 0) :=
      moment_upper a b c S w hw hs i hc (SquarefreeSummablePrimeObstruction.anisotropic_reversed i) N
    _ ≤ _ := by gcongr; linarith

lemma tailMoment_upper (S : Finset ℕ) (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0)) (N T : ℕ) :
    firstMoment S (fun p => if T<p then w p^2 else 0) N≤constant*tailEnergy w (T+1) := by
  have he (p : ℕ) : (if p.Prime then (if T<p then w p^2 else 0)/p else 0)=
      if p.Prime ∧ T+1≤p then w p^2/p else 0 := by
    by_cases hp : p.Prime <;> by_cases hT : T<p <;> simp [hp,hT]
  have hs' : Summable (fun p : ℕ => if p.Prime then (if T<p then w p^2 else 0)/p else 0) := by
    simp only [he]
    exact tail_summable (fun p => w p^2) (fun p => sq_nonneg _) hs (T+1)
  have hh := firstMoment_upper S (fun p => if T<p then w p^2 else 0)
    (fun p => by dsimp only; split_ifs <;> positivity) hs' N
  simpa only [he,tailEnergy] using hh

lemma raw_bound (S : Finset ℕ) (hS : ∀p∈S,p.Prime)
    (hhead : ∀p,p.Prime → p≤1000000 → p∈S) (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {T : ℕ} (hT : 1000000≤T) :
    (∑x∈positiveBox (T^8) (Head a b c S),totalContrast w x^2) ≤
      8*(∑i,∑x∈positiveBox (T^8) (Head a b c S),primeScore (fun p => w p^2) (F i x.1 x.2))+
      32*maxError S (T^8) T*energy w*(T:ℝ)^2+
      136*(∑i,∑x∈positiveBox (T^8) (Head a b c S),primeScore
        (fun p => if T<p then w p^2 else 0) (F i x.1 x.2)) := by
  let P := smallPrimes S T
  have hP (p : ℕ) (hp : p∈P) : p.Prime ∧ p∉S ∧ 1000000<p ∧ p≤T := by
    obtain ⟨hpT,hpr,hpn⟩ := mem_filter.mp hp
    exact ⟨hpr,hpn,by by_contra! hn; exact hpn (hhead p hpr hn),by simpa using mem_range.mp hpT⟩
  have hv := weighted_energy_bound S P hS w (T^8) T hP
  have hdiag := diagonal_sum_le S P (fun p hp => (hP p hp).1) w (T^8)
  have hE : 0≤ maxError S (T^8) T := (error_nonneg S (T^8) T T).trans (error_le_maxError S (T^8) le_rfl le_rfl)
  have hm := mul_le_mul_of_nonneg_left (small_mass_le w hs S T)
    (show 0≤16*maxError S (T^8) T*(T:ℝ)^2 by positivity)
  have hpoint (x : ℕ × ℕ) (hx : x∈positiveBox (T^8) (Head a b c S)) :
      totalContrast w x^2 ≤ 2*score P w x^2+
        136*∑i,primeScore (fun p => if T<p then w p^2 else 0) (F i x.1 x.2) := by
    obtain ⟨hxN,hx0,hxH⟩ := mem_filter.mp hx
    have hsplit := contrast_split S hS T w hx0 hxH
    have hlarge := largeContrast_sq_le w hT hxN hx0
    have hsq := sq_nonneg (score P w x-largeContrast w T x)
    change totalContrast w x=score P w x+largeContrast w T x at hsplit
    rw [hsplit]
    nlinarith only [hlarge,hsq]
  have hsum := sum_le_sum hpoint
  simp only [sum_add_distrib,←mul_sum] at hsum
  rw [sum_comm] at hsum
  change _ ≤ 2*variance S P w (T^8)+_ at hsum
  nlinarith only [hv,hdiag,hm,hsum]

noncomputable def errorRatio (S : Finset ℕ) (w : ℕ → ℝ) (T : ℕ) : ℝ :=
  maxError S (T^8) T*energy w*(T:ℝ)^2/((T^8:ℕ):ℝ)^2

noncomputable def upper (S : Finset ℕ) (w : ℕ → ℝ) (T : ℕ) : ℝ :=
  8*firstMoment S (fun p => w p^2) (T^8)+32*errorRatio S w T+136*constant*tailEnergy w (T+1)

lemma secondMoment_le_upper (S : Finset ℕ) (hS : ∀p∈S,p.Prime)
    (hhead : ∀p,p.Prime → p≤1000000 → p∈S) (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {T : ℕ} (hT : 1000000≤T) : secondMoment S w (T^8)≤upper S w T := by
  have hh := div_le_div_of_nonneg_right (raw_bound S hS hhead w hs hT) (sq_nonneg (((T^8:ℕ):ℝ)))
  have htail := tailMoment_upper S w hs (T^8) T
  have he : (8*(∑i,∑x∈positiveBox (T^8) (Head a b c S),primeScore (fun p => w p^2) (F i x.1 x.2))+
      32*maxError S (T^8) T*energy w*(T:ℝ)^2+
      136*(∑i,∑x∈positiveBox (T^8) (Head a b c S),primeScore
        (fun p => if T<p then w p^2 else 0) (F i x.1 x.2)))/((T^8:ℕ):ℝ)^2 =
      8*firstMoment S (fun p => w p^2) (T^8)+32*errorRatio S w T+
        136*firstMoment S (fun p => if T<p then w p^2 else 0) (T^8) := by
    simp only [firstMoment,errorRatio,add_div,←sum_div]
    ring
  rw [he] at hh
  dsimp only [secondMoment,upper]
  nlinarith only [hh,htail]

lemma errorRatio_tendsto (S : Finset ℕ) (w : ℕ → ℝ) :
    Tendsto (errorRatio S w) atTop (nhds 0) := by
  have hi : Tendsto (fun T : ℕ => (1:ℝ)/T) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have ht : Tendsto (fun T : ℕ => energy w*(2*modulus S*(1/(T:ℝ))^4+
      modulus S^2*(1/(T:ℝ))^10+(1/(T:ℝ))^6)) atTop (nhds 0) := by
    simpa using ((((hi.pow 4).const_mul (2*modulus S)).add
      ((hi.pow 10).const_mul (modulus S^2))).add (hi.pow 6)).const_mul (energy w)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hTR : (T:ℝ)≠0 := by exact_mod_cast hT.ne'
  dsimp only [errorRatio,maxError]
  push_cast
  field_simp

lemma firstMoment_tendsto (S : Finset ℕ) (hS : ∀p∈S,p.Prime) (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0)) :
    Tendsto (firstMoment S (fun p => w p^2)) atTop (nhds (momentLimit S w)) := by
  apply tendsto_finset_sum
  intro i hi
  exact moment_tendsto a b c S hS (fun p => w p^2) (fun p => sq_nonneg _) hs i
    (by fin_cases i <;> norm_num [c]) (SquarefreeSummablePrimeObstruction.anisotropic_reversed i)

lemma upper_tendsto (S : Finset ℕ) (hS : ∀p∈S,p.Prime) (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0)) :
    Tendsto (upper S w) atTop (nhds (8*momentLimit S w)) := by
  have hm := (firstMoment_tendsto S hS w hs).comp (tendsto_pow_atTop (by decide : 8≠0))
  have ht := (tail_tendsto (fun p => w p^2) (fun p => sq_nonneg _) hs).comp
    (tendsto_add_atTop_nat 1)
  simpa only [upper,tailEnergy,mul_zero,add_zero] using
    ((hm.const_mul 8).add ((errorRatio_tendsto S w).const_mul 32)).add
      (ht.const_mul (136*constant))

#print axioms secondMoment_le_upper
#print axioms upper_tendsto
end Erdos1206.ConicContrastMoments
