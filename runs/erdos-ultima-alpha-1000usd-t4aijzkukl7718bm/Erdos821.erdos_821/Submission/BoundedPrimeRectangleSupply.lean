import Submission.ParametricSmallPrimeMean
import Submission.StructuredPrimeFactors

/-!
# An actual prime-successor supply for a bounded prime input

The below-half structured prime count supplies many distinct prime outputs
in a two-cofactor rectangle for at least one bounded prime input. This
uses prime arithmetic-progression information, not a prime-detecting
inference from the Kloosterman mean. Both free intervals are retained.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman
set_option maxHeartbeats 4000000

noncomputable def rectanglePrimeOutputs (p L : ℕ) : Finset ℕ :=
  (((Icc 1 L) ×ˢ (Icc 1 L)).image (fun ab => ab.1*ab.2*p+1)).filter Nat.Prime

lemma mem_rectanglePrimeOutputs (p L R : ℕ) :
    R ∈ rectanglePrimeOutputs p L ↔ R.Prime ∧
      ∃ a ∈ Icc 1 L, ∃ b ∈ Icc 1 L, a*b*p+1=R := by
  simp only [rectanglePrimeOutputs,mem_filter,mem_image,mem_product]
  constructor
  · rintro ⟨⟨⟨a,b⟩,⟨ha,hb⟩,he⟩,hR⟩
    exact ⟨hR,a,ha,b,hb,he⟩
  · rintro ⟨hR,a,ha,b,hb,he⟩
    exact ⟨⟨(a,b),⟨ha,hb⟩,he⟩,hR⟩

lemma structured_prime_has_rectangle (r m R : ℕ) (hr : 1 ≤ r) (hm : r ≤ m)
    (hR : R ∈ structuredWitnessPrimes r m (progressionScaleN ((2*r+1)*m))) :
    R.Prime ∧ ∃ p ∈ geometricBlockPrimes m,
      ∃ a ∈ Icc 1 (progressionScaleN ((r+1)*m)),
      ∃ b ∈ Icc 1 (progressionScaleN ((r+1)*m)), a*b*p+1=R := by
  obtain ⟨hRp,hRN,d,hd,hdiv⟩ := structuredWitnessPrimes_has_divisor hR
  have hdprops := primeProductModuli_properties hd
  have hcard : 0 < d.primeFactors.card := by rw [hdprops.2.2.1]; omega
  obtain ⟨p,hp⟩ := card_pos.mp hcard
  have hpP := prime_product_prime_factor_mem hd hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  let a := d/p
  let b := (R-1)/d
  have hda : p*a=d := Nat.mul_div_cancel' hpd
  have hdb : d*b=R-1 := Nat.mul_div_cancel' hdiv
  have ha : 0<a := Nat.div_pos (Nat.le_of_dvd hdprops.1 hpd) hpp.pos
  have hRpred : 0<R-1 := Nat.sub_pos_of_lt hRp.one_lt
  have hb : 0<b := Nat.div_pos (Nat.le_of_dvd hRpred hdiv) hdprops.1
  have hdle : d ≤ progressionScaleN ((r+1)*m) := by
    apply hdprops.2.2.2.2.trans
    simp only [progressionScaleN,← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith
  have hale : a ≤ progressionScaleN ((r+1)*m) :=
    (Nat.div_le_self d p).trans hdle
  have hpow : (progressionScaleN m)^r * progressionScaleN ((r+1)*m) =
      progressionScaleN ((2*r+1)*m) := by
    simp only [progressionScaleN,← pow_mul,← pow_add]
    congr 1
    ring
  have hble : b ≤ progressionScaleN ((r+1)*m) := by
    apply Nat.le_of_mul_le_mul_left (c := d) _ hdprops.1
    rw [hdb]
    calc
      R-1 ≤ progressionScaleN ((2*r+1)*m) := (Nat.sub_le R 1).trans hRN
      _ = _ := hpow.symm
      _ ≤ _ := Nat.mul_le_mul_right _ hdprops.2.2.2.1
  refine ⟨hRp,p,hpP,a,mem_Icc.mpr ⟨ha,hale⟩,b,mem_Icc.mpr ⟨hb,hble⟩,?_⟩
  calc
    a*b*p+1 = (p*a)*b+1 := by ring
    _ = R := by rw [hda,hdb,Nat.sub_add_cancel hRp.pos]

lemma exists_common_prime_rectangle (S P : Finset ℕ) (L B : ℕ)
    (hS : ∀ R ∈ S, R.Prime ∧ ∃ p ∈ P,
      ∃ a ∈ Icc 1 L, ∃ b ∈ Icc 1 L, a*b*p+1=R)
    (hlarge : P.card*B < S.card) :
    ∃ p ∈ P, B < (rectanglePrimeOutputs p L).card := by
  let pick (R : ℕ) : ℕ := if h : R ∈ S then Classical.choose (hS R h).2 else 0
  have hpick (R : ℕ) (hR : R ∈ S) : pick R ∈ P ∧
      ∃ a ∈ Icc 1 L, ∃ b ∈ Icc 1 L, a*b*(pick R)+1=R := by
    dsimp only [pick]
    rw [dif_pos hR]
    exact Classical.choose_spec (hS R hR).2
  obtain ⟨p,hp,hcard⟩ := Finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to
    (fun R hR => (hpick R hR).1) (by simpa only [nsmul_eq_mul] using hlarge)
  refine ⟨p,hp,hcard.trans_le (card_le_card ?_)⟩
  intro R hR
  obtain ⟨hRS,he⟩ := mem_filter.mp hR
  apply (mem_rectanglePrimeOutputs p L R).mpr
  refine ⟨(hS R hRS).1,?_⟩
  simpa only [he] using (hpick R hRS).2

lemma geometricBlockPrimes_card_le_scale (m : ℕ) (hm : 1 ≤ m) :
    (geometricBlockPrimes m).card ≤ progressionScaleN (2*m) := by
  apply (card_le_card (show geometricBlockPrimes m ⊆ Icc 1 (progressionScaleN (2*m)) by
    intro p hp
    have hh := mem_geometricBlockPrimes.mp hp
    exact mem_Icc.mpr ⟨hh.1.pos,hh.2.2.trans (progressionScaleN_monotone (by omega))⟩)).trans_eq
  simp

/-- A positive lower bound for distinct prime outputs for a common input,
not merely a count of divisibility solutions. The structured AP estimate
is the additional arithmetic input used here. -/
theorem eventually_exists_prime_rectangle_supply (r : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∃ p ∈ geometricBlockPrimes m,
      progressionScaleN ((2*r)*m) <
        (rectanglePrimeOutputs p (progressionScaleN ((r+2)*m))).card := by
  let t := 2*r+3
  let C := structuredPrimeCountConstant (r+1) t
  filter_upwards [eventually_structured_prime_count (r+1) t (by dsimp [t]; omega),
    eventually_nat_poly_le_two_pow 1 C (r+2),eventually_ge_atTop (r+1)]
    with m hcount hpoly hm
  have hm1 : 1 ≤ m := by omega
  let S := structuredWitnessPrimes (r+1) m (progressionScaleN (t*m))
  have hs : progressionScaleN (t*m) ≤ 2^m*S.card := by
    apply hcount.trans
    apply Nat.mul_le_mul_right S.card
    simpa only [one_mul] using hpoly
  have hpow : progressionScaleN (2*m)*progressionScaleN ((2*r)*m)*2^m <
      progressionScaleN (t*m) := by
    simp only [progressionScaleN,← pow_add]
    apply Nat.pow_lt_pow_right (by decide)
    dsimp [t]
    nlinarith
  have hlarge : (geometricBlockPrimes m).card*progressionScaleN ((2*r)*m) < S.card := by
    have hh : ((geometricBlockPrimes m).card*progressionScaleN ((2*r)*m))*2^m < S.card*2^m := by
      calc
        _ ≤ progressionScaleN (2*m)*progressionScaleN ((2*r)*m)*2^m :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (geometricBlockPrimes_card_le_scale m hm1))
        _ < progressionScaleN (t*m) := hpow
        _ ≤ S.card*2^m := by simpa only [mul_comm] using hs
    exact Nat.lt_of_mul_lt_mul_right hh
  apply exists_common_prime_rectangle S (geometricBlockPrimes m)
    (progressionScaleN ((r+2)*m)) (progressionScaleN ((2*r)*m)) _ hlarge
  intro R hR
  convert structured_prime_has_rectangle (r+1) m R (by omega) hm hR using 1

lemma rectanglePrimeOutputs_pred_smooth (p L R : ℕ) (hp : 0 < p) (hpL : p ≤ L)
    (hR : R ∈ rectanglePrimeOutputs p L) : R-1 ∈ Nat.smoothNumbers (L+1) := by
  obtain ⟨_,a,ha,b,hb,rfl⟩ := (mem_rectanglePrimeOutputs p L R).mp hR
  rw [Nat.add_sub_cancel]
  apply Nat.mem_smoothNumbers'.mpr
  intro q hq hdiv
  rcases hq.dvd_mul.mp hdiv with hab | hqp
  · rcases hq.dvd_mul.mp hab with hqa | hqb
    · exact ((Nat.le_of_dvd (mem_Icc.mp ha).1 hqa).trans (mem_Icc.mp ha).2).trans_lt
        (Nat.lt_succ_self L)
    · exact ((Nat.le_of_dvd (mem_Icc.mp hb).1 hqb).trans (mem_Icc.mp hb).2).trans_lt
        (Nat.lt_succ_self L)
  · exact ((Nat.le_of_dvd hp hqp).trans hpL).trans_lt (Nat.lt_succ_self L)

/-- A common bounded prime input supplies many distinct prime successors,
and simultaneously satisfies the squarefree-modulus congruence mean.
The successor lower bound comes from the separate structured AP theorem.
The stated smoothness cutoff approaches a half power, not arbitrary roots. -/
theorem eventually_bounded_prime_supply_and_mean (k : ℕ) (hk : 5 ≤ k)
    (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2^(64*m) < p ∧ p ≤ 2^(128*m) ∧
      2^((14*k+10)*(64*m)) < (rectanglePrimeOutputs p (parametricInterval k (64*m))).card ∧
      (∀ R ∈ rectanglePrimeOutputs p (parametricInterval k (64*m)),
        R ≤ parametricAmbient k (64*m)+1 ∧
        R-1 ∈ Nat.smoothNumbers (parametricInterval k (64*m)+1)) ∧
      parametricAmbient k (64*m)+1 < parametricModulus k (64*m)^2 ∧
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ parametricModulus k (64*m)) →
      (1+Real.log (parametricAmbient k (64*m) : ℝ))^d*
        (∑ q ∈ P, |(∑ i ∈ range (parametricInterval k (64*m)),
          ∑ j ∈ range (parametricInterval k (64*m)),
            if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
          (parametricInterval k (64*m) : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
        η*(parametricInterval k (64*m) : ℝ)^2 := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (eventually_parametric_successor_log_rate k (by omega) d η hη)
  filter_upwards [eventually_exists_prime_rectangle_supply (7*k+5),
    eventually_ge_atTop (max M 1)] with m hs hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  have hmM : M ≤ 64*m := by have := (le_max_left _ _).trans hm; omega
  obtain ⟨p,hpB,hcount⟩ := hs
  obtain ⟨hp,hlo,hhi⟩ := mem_geometricBlockPrimes.mp hpB
  have hpLo : 2^(64*m) < p := hlo
  have hpTop : p ≤ 2^(128*m) := by
    apply hhi.trans
    unfold progressionScaleN
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hpTop' : p ≤ 2^(2*(64*m)) := by
    simpa only [show 2*(64*m)=128*m by ring] using hpTop
  have hpL : p ≤ parametricInterval k (64*m) := by
    apply hpTop'.trans
    unfold parametricInterval
    exact Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right (64*m) (by omega))
  have hL : progressionScaleN (((7*k+5)+2)*m) = parametricInterval k (64*m) := by
    unfold progressionScaleN parametricInterval
    congr 1
    ring
  have hB : progressionScaleN ((2*(7*k+5))*m) = 2^((14*k+10)*(64*m)) := by
    unfold progressionScaleN
    congr 1
    ring
  rw [hL,hB] at hcount
  refine ⟨p,hp,hpLo,hpTop,hcount,?_,parametric_ambient_above_half k (64*m) hk (by omega),
    hM (64*m) hmM p hp hpLo.le⟩
  intro R hR
  refine ⟨?_,rectanglePrimeOutputs_pred_smooth p _ R hp.pos hpL hR⟩
  obtain ⟨_,a,ha,b,hb,rfl⟩ := (mem_rectanglePrimeOutputs _ _ _).mp hR
  exact Nat.add_le_add_right
    (parametric_rectangle_product_bound k (64*m) p a b hpTop' (mem_Icc.mp ha).2 (mem_Icc.mp hb).2) 1

end Erdos821.AnalyticSieve
