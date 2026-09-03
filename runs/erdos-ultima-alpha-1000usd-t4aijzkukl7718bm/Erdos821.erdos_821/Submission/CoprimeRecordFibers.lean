import Submission.PrimeExcisionApplications
import Submission.RecordPairs

/-!
# Coprime pairs in prime-excluded normalized record fibers

Above the half line, the common-divisor tail is summable. After a fixed
finite prime exclusion, full record fibers have an arbitrarily large
proportion of coprime pairs. This structural result does not increase the
attained multiplicity exponent.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.CoprimeRecords

noncomputable def avoidingFiber (K n : ℕ) : Finset ℕ :=
  (finite_avoiding_totient_fiber K n).toFinset

@[simp] lemma mem_avoidingFiber {m K n : ℕ} :
    m ∈ avoidingFiber K n ↔ Squarefree m ∧ Nat.Coprime m K ∧ totient m = n :=
  (finite_avoiding_totient_fiber K n).mem_toFinset

@[simp] lemma avoidingFiber_card (K n : ℕ) : (avoidingFiber K n).card = gAvoiding K n :=
  (Set.ncard_eq_toFinset_card _ (finite_avoiding_totient_fiber K n)).symm

lemma card_avoidingFiber_dvd_le (K n d : ℕ) (hd : 0 < d) :
    ((avoidingFiber K n).filter (fun m => d ∣ m)).card ≤ gAvoiding K (n / totient d) := by
  let S := (avoidingFiber K n).filter (fun m => d ∣ m)
  have hinj : Set.InjOn (fun m : ℕ => m/d) (S : Set ℕ) := by
    intro a ha b hb hab
    have hda := (Finset.mem_filter.mp ha).2
    have hdb := (Finset.mem_filter.mp hb).2
    calc
      a = d*(a/d) := (Nat.mul_div_cancel' hda).symm
      _ = d*(b/d) := congrArg (fun m : ℕ => d*m) hab
      _ = b := Nat.mul_div_cancel' hdb
  have hmap (q : ℕ) (hq : q ∈ S.image (fun m => m/d)) :
      Squarefree q ∧ Nat.Coprime q K ∧ totient q = n / totient d := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hmF, hdm⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmSq, hmK, hmphi⟩ := mem_avoidingFiber.mp hmF
    have hdiv := Nat.div_dvd_of_dvd hdm
    refine ⟨hmSq.squarefree_of_dvd hdiv, hmK.of_dvd_left hdiv, ?_⟩
    apply Nat.eq_div_of_mul_eq_right (Nat.totient_pos.mpr hd).ne'
    exact (PrimitiveCollisions.totient_divisor_factor hmSq hdm).symm.trans hmphi
  have hcard := card_le_gAvoiding K (n / totient d) (S.image (fun m => m/d)) hmap
  rwa [Finset.card_image_of_injOn hinj] at hcard

/-- Divisibility frequency at a record in the full prime-excluded fiber. -/
lemma normalized_record_core_bound (K n d : ℕ) (hn : 0 < n) (s : ℝ)
    (hrec : ∀ j : ℕ, j ≤ n → (gAvoiding K j : ℝ)/(j : ℝ)^s ≤
      (gAvoiding K n : ℝ)/(n : ℝ)^s) :
    (totient d : ℝ)^s * (((avoidingFiber K n).filter (fun m => d ∣ m)).card : ℝ) ≤
      (gAvoiding K n : ℝ) := by
  by_cases hne : ((avoidingFiber K n).filter (fun m => d ∣ m)).Nonempty
  · obtain ⟨m, hm⟩ := hne
    obtain ⟨hmF, hdm⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmSq, _, hmphi⟩ := mem_avoidingFiber.mp hmF
    have hdSq := hmSq.squarefree_of_dvd hdm
    have hd : 0 < d := Nat.pos_of_ne_zero hdSq.ne_zero
    have hphi : 0 < totient d := Nat.totient_pos.mpr hd
    have hphidiv : totient d ∣ n := by
      rw [← hmphi]
      exact Nat.totient_dvd_of_dvd hdm
    let q := n / totient d
    have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hn hphidiv) hphi
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hqPow : 0 < (q : ℝ)^s := Real.rpow_pos_of_pos hqR s
    have hnPow : 0 < (n : ℝ)^s := Real.rpow_pos_of_pos hnR s
    have hprod := (div_le_div_iff₀ hqPow hnPow).mp (hrec q (Nat.div_le_self _ _))
    have hpowid : (n : ℝ)^s = (q : ℝ)^s * (totient d : ℝ)^s := by
      rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      congr 1
      exact_mod_cast (Nat.div_mul_cancel hphidiv).symm
    have hG : (totient d : ℝ)^s * (gAvoiding K q : ℝ) ≤ (gAvoiding K n : ℝ) := by
      apply (mul_le_mul_iff_left₀ hqPow).mp
      calc
        ((totient d : ℝ)^s * (gAvoiding K q : ℝ)) * (q : ℝ)^s =
            (gAvoiding K q : ℝ) * (n : ℝ)^s := by rw [hpowid]; ring
        _ ≤ _ := hprod
    have hcard : (((avoidingFiber K n).filter (fun m => d ∣ m)).card : ℝ) ≤
        (gAvoiding K q : ℝ) := by exact_mod_cast card_avoidingFiber_dvd_le K n d hd
    exact (mul_le_mul_of_nonneg_left hcard (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans hG
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero,
      mul_zero, Nat.cast_nonneg]

lemma normalized_record_core_square_bound (K n d : ℕ) (hn : 0 < n) (hd : 0 < d) (s : ℝ)
    (hrec : ∀ j : ℕ, j ≤ n → (gAvoiding K j : ℝ)/(j : ℝ)^s ≤
      (gAvoiding K n : ℝ)/(n : ℝ)^s) :
    ((((avoidingFiber K n).filter (fun m => d ∣ m)).card : ℝ))^2 ≤
      (gAvoiding K n : ℝ)^2 * (totient d : ℝ)^(-(2*s)) := by
  have hphi : (0 : ℝ) < totient d := by exact_mod_cast Nat.totient_pos.mpr hd
  have hcore := normalized_record_core_bound K n d hn s hrec
  have hf : (((avoidingFiber K n).filter (fun m => d ∣ m)).card : ℝ) ≤
      (gAvoiding K n : ℝ)/(totient d : ℝ)^s :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hphi s)).mpr (by nlinarith only [hcore])
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hf 2).trans_eq
  rw [div_pow, ← Real.rpow_mul_natCast hphi.le]
  norm_num only [Nat.cast_ofNat]
  rw [show s*(2 : ℝ) = 2*s by ring, Real.rpow_neg hphi.le, div_eq_mul_inv]

noncomputable def coprimePairs (K n : ℕ) : Finset (ℕ × ℕ) :=
  ((avoidingFiber K n) ×ˢ (avoidingFiber K n)).filter (fun ab => Nat.Coprime ab.1 ab.2)

noncomputable def noncoprimePairs (K n : ℕ) : Finset (ℕ × ℕ) :=
  ((avoidingFiber K n) ×ˢ (avoidingFiber K n)).filter (fun ab => ¬Nat.Coprime ab.1 ab.2)

lemma pair_card_partition (K n : ℕ) :
    (coprimePairs K n).card + (noncoprimePairs K n).card = (gAvoiding K n)^2 := by
  rw [coprimePairs, noncoprimePairs, Finset.card_filter_add_card_filter_not,
    Finset.card_product, avoidingFiber_card, pow_two]

lemma noncoprime_gcd_gt_cutoff (B a b : ℕ)
    (haK : Nat.Coprime a B.factorial) (ha : 0 < a) (hbad : ¬Nat.Coprime a b) :
    B < Nat.gcd a b := by
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
  have hpB : B < p := by
    by_contra h
    have hpK := hp.dvd_factorial.mpr (le_of_not_gt h)
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes haK hpa hpK)
  exact hpB.trans_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left b ha) (Nat.dvd_gcd hpa hpb))

/-- Counting by the exact gcd avoids any independence assumption. -/
lemma noncoprimePairs_le_core_sum (B n : ℕ) :
    (noncoprimePairs B.factorial n).card ≤
      ∑ d ∈ Finset.Icc (B+1) ((avoidingFiber B.factorial n).sup id),
        ((avoidingFiber B.factorial n).filter (fun m => d ∣ m)).card^2 := by
  let S := avoidingFiber B.factorial n
  let P := noncoprimePairs B.factorial n
  let T := Finset.Icc (B+1) (S.sup id)
  have hmem (ab : ℕ × ℕ) (hab : ab ∈ P) :
      ab.1 ∈ S ∧ ab.2 ∈ S ∧ ¬Nat.Coprime ab.1 ab.2 := by
    obtain ⟨hab, hbad⟩ := Finset.mem_filter.mp hab
    exact ⟨(Finset.mem_product.mp hab).1, (Finset.mem_product.mp hab).2, hbad⟩
  have hmap : Set.MapsTo (fun ab : ℕ × ℕ => Nat.gcd ab.1 ab.2) (P : Set (ℕ × ℕ)) (T : Set ℕ) := by
    intro ab hab
    obtain ⟨ha, hb, hbad⟩ := hmem ab hab
    have ha' := mem_avoidingFiber.mp ha
    have ha0 := Nat.pos_of_ne_zero ha'.1.ne_zero
    change Nat.gcd ab.1 ab.2 ∈ Finset.Icc (B+1) (S.sup id)
    exact Finset.mem_Icc.mpr
      ⟨by have := noncoprime_gcd_gt_cutoff B ab.1 ab.2 ha'.2.1 ha0 hbad; omega,
        (Nat.gcd_le_left ab.2 ha0).trans (Finset.le_sup (f := id) ha)⟩
  change P.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_le_sum
  intro d hd
  have hsub : P.filter (fun ab => Nat.gcd ab.1 ab.2 = d) ⊆
      (S.filter (fun m => d ∣ m)) ×ˢ (S.filter (fun m => d ∣ m)) := by
    intro ab hab
    obtain ⟨hab, he⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha, hb, _⟩ := hmem ab hab
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨ha, he ▸ Nat.gcd_dvd_left _ _⟩,
        Finset.mem_filter.mpr ⟨hb, he ▸ Nat.gcd_dvd_right _ _⟩⟩
  simpa only [Finset.card_product, pow_two] using Finset.card_le_card hsub

lemma noncoprimePairs_record_le (B n : ℕ) (hn : 0 < n) (s : ℝ)
    (hrec : ∀ j : ℕ, j ≤ n → (gAvoiding B.factorial j : ℝ)/(j : ℝ)^s ≤
      (gAvoiding B.factorial n : ℝ)/(n : ℝ)^s) :
    ((noncoprimePairs B.factorial n).card : ℝ) ≤
      (gAvoiding B.factorial n : ℝ)^2 *
        ∑ d ∈ Finset.Icc (B+1) ((avoidingFiber B.factorial n).sup id),
          (totient d : ℝ)^(-(2*s)) := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc (B+1) ((avoidingFiber B.factorial n).sup id),
        ((((avoidingFiber B.factorial n).filter (fun m => d ∣ m)).card : ℝ))^2 := by
      exact_mod_cast noncoprimePairs_le_core_sum B n
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      exact normalized_record_core_square_bound B.factorial n d hn
        (by have := (Finset.mem_Icc.mp hd).1; omega) s hrec

lemma exists_small_totient_tail (s η : ℝ) (hs : 1/2 < s) (hη : 0 < η) :
    ∃ B : ℕ, ∀ U : ℕ,
      (∑ d ∈ Finset.Icc (B+1) U, (totient d : ℝ)^(-(2*s))) < η := by
  obtain ⟨S, hS⟩ := (summable_totient_neg_rpow (2*s) (by linarith)).vanishing
    (Iio_mem_nhds hη)
  refine ⟨S.sup id, fun U => hS (Finset.Icc (S.sup id+1) U) ?_⟩
  apply Finset.disjoint_left.mpr
  intro d hd hdS
  have h1 := (Finset.mem_Icc.mp hd).1
  have h2 := Finset.le_sup (f := id) hdS
  dsimp only [id_eq] at h2
  omega

/-- For a fixed exponent above one half and any desired loss η, a FIXED
prime cutoff makes every positive-output record almost entirely coprime
in ordered pairs. No independence of divisibility events is assumed. -/
theorem exists_cutoff_record_coprime_proportion (s η : ℝ) (hs : 1/2 < s) (hη : 0 < η) :
    ∃ B : ℕ, ∀ n : ℕ, 0 < n →
      (∀ j : ℕ, j ≤ n → (gAvoiding B.factorial j : ℝ)/(j : ℝ)^s ≤
        (gAvoiding B.factorial n : ℝ)/(n : ℝ)^s) →
      (1-η)*(gAvoiding B.factorial n : ℝ)^2 ≤ (coprimePairs B.factorial n).card := by
  obtain ⟨B, hB⟩ := exists_small_totient_tail s η hs hη
  refine ⟨B, ?_⟩
  intro n hn hrec
  have hbad := (noncoprimePairs_record_le B n hn s hrec).trans
    (mul_le_mul_of_nonneg_left (hB _).le (sq_nonneg (gAvoiding B.factorial n : ℝ)))
  have hpartition : ((coprimePairs B.factorial n).card : ℝ) +
      ((noncoprimePairs B.factorial n).card : ℝ) = (gAvoiding B.factorial n : ℝ)^2 := by
    exact_mod_cast pair_card_partition B.factorial n
  nlinarith only [hbad, hpartition]

lemma coprimePairs_distinct (K n : ℕ) (hn : 1 < n) (ab : ℕ × ℕ)
    (hab : ab ∈ coprimePairs K n) : ab.1 ≠ ab.2 := by
  obtain ⟨habS, hcop⟩ := Finset.mem_filter.mp hab
  have ha := mem_avoidingFiber.mp (Finset.mem_product.mp habS).1
  intro he
  have hone : ab.1 = 1 := by
    simpa only [← he, Nat.Coprime, Nat.gcd_self] using hcop
  have hphi := ha.2.2
  rw [hone, Nat.totient_one] at hphi
  omega

/-- Unconditional at every exponent in the currently proved above-half
range: there are arbitrarily large, full restricted fibers with both high
multiplicity and any prescribed proportion of coprime ordered pairs. -/
theorem exists_large_mostly_coprime_records (α η : ℝ) (hα : 1/2 < α)
    (hupper : α < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10))
    (hη : 0 < η) :
    ∃ B : ℕ, ∀ N : ℕ, ∃ n : ℕ, max N 1 < n ∧
      (n : ℝ)^α < (gAvoiding B.factorial n : ℝ) ∧
      (1-η)*(gAvoiding B.factorial n : ℝ)^2 ≤ (coprimePairs B.factorial n).card := by
  let s : ℝ := (α+1/2)/2
  have hs : 1/2 < s := by dsimp [s]; linarith
  have hsα : s < α := by dsimp [s]; linarith
  obtain ⟨B, hB⟩ := exists_cutoff_record_coprime_proportion s η hs hη
  refine ⟨B, ?_⟩
  intro N
  have H := infinite_gAvoiding_composite_range B.factorial (Nat.factorial_pos B) α
    (by linarith) hupper
  have H' : {n : ℕ | (n : ℝ)^α < (gAvoiding B.factorial n : ℝ)}.Infinite :=
    H.mono (fun n hn => hn.2)
  obtain ⟨n, hnN, hnG, hrec⟩ := exists_large_normalized_record_at
    (gAvoiding B.factorial) α s hsα H' (max N 1)
  exact ⟨n, hnN, hnG, hB n (by omega) hrec⟩

/-- In particular, primitive collisions occur superlinearly often at some
common outputs. The factor of two in the exponent counts ORDERED PAIRS;
it is not a doubling of the inverse-totient multiplicity exponent. -/
theorem infinite_large_primitive_pair_count (γ : ℝ) (hγ : 1/2 < γ)
    (hupper : γ < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)) :
    ∃ B : ℕ, {n : ℕ | 1 < n ∧
      (n : ℝ)^(2*γ) < ((coprimePairs B.factorial n).card : ℝ)}.Infinite := by
  let A : ℝ := 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)
  let α : ℝ := (γ+A)/2
  have hγα : γ < α := by dsimp [α, A]; linarith
  have hαA : α < A := by dsimp [α, A]; linarith
  obtain ⟨B, hB⟩ := exists_large_mostly_coprime_records α (1/2)
    (hγ.trans hγα) hαA (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^(2*(α-γ))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 2*(α-γ))).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hlim.eventually (eventually_gt_atTop (2 : ℝ)))
  refine ⟨B, Set.infinite_of_forall_exists_gt ?_⟩
  intro N
  obtain ⟨n, hn, hnG, hnP⟩ := hB (max N M)
  have hn1 : 1 < n := (le_max_right _ _).trans_lt hn
  have hnN : N < n := (le_max_left N M).trans_lt ((le_max_left _ _).trans_lt hn)
  have hnM : M ≤ n := (le_max_right N M).trans ((le_max_left _ _).trans hn.le)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (n : ℝ)^(2*α) = (n : ℝ)^(2*(α-γ))*(n : ℝ)^(2*γ) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hlarge : 2*(n : ℝ)^(2*γ) < (n : ℝ)^(2*α) := by
    rw [hpow]
    exact mul_lt_mul_of_pos_right (hM n hnM) (Real.rpow_pos_of_pos hn0 _)
  have hsq : (n : ℝ)^(2*α) = ((n : ℝ)^α)^2 := by
    simpa only [Nat.cast_ofNat, mul_comm] using Real.rpow_mul_natCast hn0.le α 2
  rw [hsq] at hlarge
  have hpos := Real.rpow_pos_of_pos hn0 α
  refine ⟨n, ⟨hn1, ?_⟩, hnN⟩
  nlinarith only [hlarge, hnG, hnP, hpos]

/-- The natural product construction lands at output n², not at n. -/
lemma coprimePair_product_mem (K n : ℕ) (ab : ℕ × ℕ) (hab : ab ∈ coprimePairs K n) :
    ab.1*ab.2 ∈ avoidingFiber K (n^2) := by
  obtain ⟨habS, hcop⟩ := Finset.mem_filter.mp hab
  have ha := mem_avoidingFiber.mp (Finset.mem_product.mp habS).1
  have hb := mem_avoidingFiber.mp (Finset.mem_product.mp habS).2
  apply mem_avoidingFiber.mpr
  refine ⟨?_, ha.2.1.mul_left hb.2.1, ?_⟩
  · exact (Nat.squarefree_mul hcop).mpr ⟨ha.1, hb.1⟩
  · rw [Nat.totient_mul hcop, ha.2.2, hb.2.2, pow_two]

end Erdos821.CoprimeRecords
