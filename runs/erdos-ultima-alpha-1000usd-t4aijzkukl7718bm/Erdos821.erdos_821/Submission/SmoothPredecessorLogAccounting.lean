import Submission.SmoothPrimeOnlyBias
import Submission.MertensPrimeLog
import Submission.Sublinear

/-!
# Logarithmic accounting below a smooth predecessor cutoff

These finite estimates retain the prime-power contribution to a predecessor's
logarithm. They do not assume distribution of the restricted prime family,
and do not settle Erdős 821.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma smooth_prime_power_le_of_no_large_square (n Y W d : ℕ)
    (hs : n ∈ Nat.smoothNumbers Y) (hWY : W^3 ≤ Y)
    (hno : ¬∃ a : ℕ, W ≤ a ∧ a^2 ∣ n)
    (hd : IsPrimePow d) (hdn : d ∣ n) : d ≤ Y := by
  obtain ⟨q,k,hq,hk,rfl⟩ := (isPrimePow_nat_iff d).mp hd
  by_cases hk1 : k = 1
  · subst k
    simpa only [pow_one] using
      (Nat.mem_smoothNumbers'.mp hs q hq (by simpa using hdn)).le
  have hk2 : 2 ≤ k := by omega
  have ha : q^(k/2) < W := by
    by_contra h
    apply hno
    refine ⟨q^(k/2), Nat.le_of_not_gt h, ?_⟩
    rw [← pow_mul]
    exact (Nat.pow_dvd_pow q (by omega : k/2*2 ≤ k)).trans hdn
  calc
    q^k ≤ q^(k/2*3) := Nat.pow_le_pow_right hq.pos (by omega)
    _ = (q^(k/2))^3 := pow_mul _ _ _
    _ ≤ W^3 := Nat.pow_le_pow_left ha.le _
    _ ≤ Y := hWY

noncomputable def truncatedPredecessorLog (n Y : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 Y, if d ∣ n then vonMangoldt d else 0

lemma truncatedPredecessorLog_nonneg (n Y : ℕ) :
    0 ≤ truncatedPredecessorLog n Y := by
  apply sum_nonneg
  intro d hd
  split_ifs <;> positivity [vonMangoldt_nonneg (n := d)]

lemma truncatedPredecessorLog_eq (n Y W : ℕ) (hn : 0 < n)
    (hs : n ∈ Nat.smoothNumbers Y) (hWY : W^3 ≤ Y)
    (hno : ¬∃ a : ℕ, W ≤ a ∧ a^2 ∣ n) :
    truncatedPredecessorLog n Y = Real.log n := by
  unfold truncatedPredecessorLog
  rw [← sum_filter, ← vonMangoldt_sum]
  apply sum_subset
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2,hn.ne'⟩
  · intro d hd hnot
    by_contra hΛ
    apply hnot
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      smooth_prime_power_le_of_no_large_square n Y W d hs hWY hno
        (vonMangoldt_ne_zero_iff.mp hΛ) (Nat.dvd_of_mem_divisors hd)⟩,
      Nat.dvd_of_mem_divisors hd⟩

noncomputable def largeSquarePredecessorPool (N W : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => 2 ≤ n ∧ ∃ a : ℕ, W ≤ a ∧ a^2 ∣ n-1)

lemma largeSquarePredecessorPool_card (N W : ℕ) (hW : 0 < W) :
    ((largeSquarePredecessorPool N W).card : ℝ) ≤ 2*(N : ℝ)/W := by
  let P := largeSquarePredecessorPool N W
  let S := P.image (fun n => n-1)
  have hcard : S.card = P.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb he
    simp only [P,largeSquarePredecessorPool,Finset.mem_coe,mem_filter] at ha hb
    change a-1=b-1 at he
    have ha2 := ha.2.1
    have hb2 := hb.2.1
    omega
  rw [← hcard]
  apply Erdos821.card_large_square_divisor_le S N W hW
  intro n hn
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
  obtain ⟨hpI,hp2,hsq⟩ := mem_filter.mp hp
  exact ⟨by omega, (Nat.sub_le p 1).trans (mem_Icc.mp hpI).2, hsq⟩

lemma prime_power_le_twice_totient (d : ℕ) (hd : IsPrimePow d) :
    d ≤ 2*d.totient := by
  obtain ⟨q,k,hq,hk,rfl⟩ := (isPrimePow_nat_iff d).mp hd
  rw [Nat.totient_prime_pow hq hk]
  have he : k = (k-1)+1 := by omega
  conv_lhs => rw [he,pow_succ]
  have hq2 : q ≤ 2*(q-1) := by have := hq.two_le; omega
  have hh := Nat.mul_le_mul_left (q^(k-1)) hq2
  nlinarith only [hh]

lemma mangoldt_div_totient_le_twice (d : ℕ) :
    vonMangoldt d/(d.totient : ℝ) ≤ 2*(vonMangoldt d/(d : ℝ)) := by
  by_cases hd : IsPrimePow d
  · have hdR : (0 : ℝ) < d := by exact_mod_cast hd.pos
    have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd.pos
    apply (div_le_iff₀ hφ).mpr
    have hn : (d : ℝ) ≤ 2*d.totient := by exact_mod_cast prime_power_le_twice_totient d hd
    have hh := mul_le_mul_of_nonneg_left hn (div_nonneg (vonMangoldt_nonneg (n := d)) hdR.le)
    convert hh using 1 <;> field_simp
  · simp only [vonMangoldt_eq_zero_iff.mpr hd,zero_div,mul_zero,le_refl]

noncomputable def truncatedLogMainTerm (Y : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 Y, vonMangoldt d/(d.totient : ℝ)

lemma exists_truncatedLogMainTerm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 1 ≤ Y →
      truncatedLogMainTerm Y ≤ 2*Real.log Y+C := by
  let S : ℝ := ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n)/(n : ℝ)
  have hS : 0 ≤ S := tsum_nonneg (fun n => by
    split_ifs <;> positivity [vonMangoldt_nonneg (n := n)])
  obtain ⟨K,hK,HK⟩ := Erdos821.exists_primeLogMass_log_bound
  refine ⟨2*(K+S),by positivity,?_⟩
  intro Y hY
  have hbase := Erdos821.mangoldt_harmonic_le_primeLogMass_add Y
  have hlog := (abs_le.mp (HK Y hY)).2
  have hsum : truncatedLogMainTerm Y ≤ 2*∑ d ∈ Icc 1 Y, vonMangoldt d/(d : ℝ) := by
    rw [mul_sum]
    exact sum_le_sum (fun d _ => mangoldt_div_totient_le_twice d)
  change (∑ d ∈ Icc 1 Y, vonMangoldt d/(d : ℝ)) ≤ Erdos821.primeLogMass Y+S at hbase
  linarith only [hsum,hbase,hlog]

lemma restricted_truncated_log_identity (f : ArithmeticFunction ℝ) (N Y : ℕ) :
    (∑ n ∈ Icc 1 N, f n*truncatedPredecessorLog (n-1) Y) =
      ∑ d ∈ Icc 1 Y, vonMangoldt d*restrictedCofactorWeight f d 1 0 1 N := by
  simp only [truncatedPredecessorLog,restricted_cofactor_singleton,mul_sum,mul_ite,mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro n hn
  split_ifs <;> ring

lemma restricted_truncated_log_upper (f : ArithmeticFunction ℝ)
    (N Y : ℕ) :
    (∑ n ∈ Icc 1 N, f n*truncatedPredecessorLog (n-1) Y) ≤
      restrictedMass f N*truncatedLogMainTerm Y+
        Real.log Y*primeOnlyRestrictedError f Y N := by
  rw [restricted_truncated_log_identity]
  unfold truncatedLogMainTerm primeOnlyRestrictedError
  rw [mul_sum,mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have hΛ : vonMangoldt d ≤ Real.log Y :=
    vonMangoldt_le_log.trans (log_nat_mono (mem_Icc.mp hd).2)
  have he : restrictedCofactorWeight f d 1 0 1 N ≤
      restrictedMass f N/(d.totient : ℝ)+
        |restrictedCofactorWeight f d 1 0 1 N-restrictedMass f N/(d.totient : ℝ)| := by
    linarith only [le_abs_self (restrictedCofactorWeight f d 1 0 1 N-restrictedMass f N/(d.totient : ℝ))]
  have hmul := mul_le_mul_of_nonneg_left he (vonMangoldt_nonneg (n := d))
  have herr := mul_le_mul_of_nonneg_right hΛ
    (abs_nonneg (restrictedCofactorWeight f d 1 0 1 N-restrictedMass f N/(d.totient : ℝ)))
  rw [mul_add] at hmul
  have heq : vonMangoldt d*(restrictedMass f N/(d.totient : ℝ)) =
      restrictedMass f N*(vonMangoldt d/(d.totient : ℝ)) := by ring
  rw [heq] at hmul
  linarith only [hmul,herr]

lemma summable_log_square_correction :
    Summable (fun n : ℕ => 2*Real.log n/(n : ℝ)^2) := by
  have H : Summable (fun n : ℕ => 4*(n : ℝ)^(-3/2 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ) < -1)).mul_left 4
  apply H.of_nonneg_of_le
  · intro n
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg n)) (sq_nonneg _)
  · intro n
    by_cases hn : n = 0
    · subst n
      norm_num
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hh := Real.log_le_rpow_div hnR.le (by norm_num : (0 : ℝ) < 1/2)
    calc
      2*Real.log n/(n : ℝ)^2 ≤ 4*(n : ℝ)^(1/2 : ℝ)/(n : ℝ)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        linarith only [hh]
      _ = 4*(n : ℝ)^(-3/2 : ℝ) := by
        rw [mul_div_assoc,← Real.rpow_natCast,← Real.rpow_sub hnR]
        norm_num

lemma prime_log_totient_correction (p : ℕ) (hp : p.Prime) :
    Real.log p/(p.totient : ℝ) ≤ Real.log p/(p : ℝ)+2*Real.log p/(p : ℝ)^2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm : (0 : ℝ) < (p : ℝ)-1 := by linarith
  have hlog := Real.log_natCast_nonneg p
  rw [Nat.totient_prime hp,Nat.cast_sub hp.one_lt.le,Nat.cast_one]
  have he : Real.log p/((p : ℝ)-1)-Real.log p/(p : ℝ) =
      Real.log p/((p : ℝ)*((p : ℝ)-1)) := by
    field_simp
    ring
  have hbound : Real.log p/((p : ℝ)*((p : ℝ)-1)) ≤ 2*Real.log p/(p : ℝ)^2 := by
    apply (div_le_div_iff₀ (mul_pos hp0 hpm) (sq_pos_of_pos hp0)).mpr
    have hh := mul_le_mul_of_nonneg_left
      (show (p : ℝ)^2 ≤ 2*((p : ℝ)*((p : ℝ)-1)) by nlinarith only [hp2]) hlog
    nlinarith only [hh]
  linarith only [he,hbound]

/-- The coefficient of log Y is one; all higher prime powers and the
prime reciprocal-totient correction contribute only a bounded constant. -/
lemma exists_truncatedLogMainTerm_sharp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 1 ≤ Y →
      truncatedLogMainTerm Y ≤ Real.log Y+C := by
  let S : ℝ := ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n)/(n : ℝ)
  let T : ℝ := ∑' n : ℕ, 2*Real.log n/(n : ℝ)^2
  have hS : 0 ≤ S := tsum_nonneg (fun n => by
    split_ifs <;> positivity [vonMangoldt_nonneg (n := n)])
  have hT : 0 ≤ T := tsum_nonneg (fun n =>
    div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg n)) (sq_nonneg _))
  obtain ⟨K,hK,HK⟩ := Erdos821.exists_primeLogMass_log_bound
  refine ⟨K+T+2*S,by positivity,?_⟩
  intro Y hY
  have hpoint (d : ℕ) : vonMangoldt d/(d.totient : ℝ) ≤
      (if d.Prime then Real.log d/(d : ℝ) else 0)+
        2*Real.log d/(d : ℝ)^2+2*((if d.Prime then 0 else vonMangoldt d)/(d : ℝ)) := by
    by_cases hd : d.Prime
    · simpa only [hd,if_true,zero_div,mul_zero,add_zero,vonMangoldt_apply_prime hd]
        using prime_log_totient_correction d hd
    · simp only [hd,if_false,zero_add]
      have hcor : 0 ≤ 2*Real.log d/(d : ℝ)^2 := by
        positivity [Real.log_natCast_nonneg d]
      linarith only [mangoldt_div_totient_le_twice d,hcor]
  have hprime : (∑ d ∈ Icc 1 Y, if d.Prime then Real.log d/(d : ℝ) else 0) =
      Erdos821.primeLogMass Y := by
    rw [← sum_filter]
    apply sum_congr
    · ext p
      simp only [mem_filter,mem_Icc,Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨hp1,hpY⟩,hp⟩
        exact ⟨by omega,hp⟩
      · rintro ⟨hpY,hp⟩
        exact ⟨⟨hp.pos,by omega⟩,hp⟩
    · intros
      rfl
  have hnonprime : (∑ d ∈ Icc 1 Y,
      (if d.Prime then 0 else vonMangoldt d)/(d : ℝ)) ≤ S :=
    Summable.sum_le_tsum _ (fun d _ => by
      split_ifs <;> positivity [vonMangoldt_nonneg (n := d)])
      Erdos821.summable_nonprime_mangoldt_div
  have hcor : (∑ d ∈ Icc 1 Y, 2*Real.log d/(d : ℝ)^2) ≤ T :=
    Summable.sum_le_tsum _ (fun d _ => by positivity [Real.log_natCast_nonneg d])
      summable_log_square_correction
  have hsum := sum_le_sum (s := Icc 1 Y) (fun d _ => hpoint d)
  rw [sum_add_distrib,sum_add_distrib,hprime,← mul_sum] at hsum
  have hlog := (abs_le.mp (HK Y hY)).2
  change truncatedLogMainTerm Y ≤ _ at hsum
  linarith only [hsum,hnonprime,hcor,hlog]


end Erdos821.AnalyticSieve
