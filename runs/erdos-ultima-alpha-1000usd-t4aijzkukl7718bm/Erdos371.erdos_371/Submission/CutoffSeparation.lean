import Submission.Explore

/-! Separation between finite-cutoff comparison signs.
These results concern the cutoff approximation, not a settlement of Erdős 371. -/

namespace Erdos371

lemma sum_range_coprime {α : Type*} [AddCommMonoid α]
    (M R : ℕ) (hM : 0 < M) (hR : 0 < R) (hc : M.Coprime R) (f : ℕ → ℕ → α) :
    (∑ n ∈ Finset.range (M * R), f (n % M) (n % R)) =
      ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range R, f a b := by
  rw [← Finset.sum_product (Finset.range M) (Finset.range R) (fun x => f x.1 x.2)]
  apply Finset.sum_bij (fun n _ => (n % M, n % R))
  · intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hM),
      Finset.mem_range.mpr (Nat.mod_lt n hR)⟩
  · intro a ha b hb he
    have hmod : Nat.ModEq (M * R) a b :=
      (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    exact hmod.eq_of_lt_of_lt (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)
  · intro x hx
    have hxM := Finset.mem_range.mp (Finset.mem_product.mp hx).1
    have hxR := Finset.mem_range.mp (Finset.mem_product.mp hx).2
    let n := Nat.chineseRemainder hc x.1 x.2
    refine ⟨n, Finset.mem_range.mpr (Nat.chineseRemainder_lt_mul hc _ _ hM.ne' hR.ne'), ?_⟩
    apply Prod.ext
    · exact (show n.val % M = x.1 % M from n.prop.1).trans (Nat.mod_eq_of_lt hxM)
    · exact (show n.val % R = x.2 % R from n.prop.2).trans (Nat.mod_eq_of_lt hxR)
  · intro n hn
    rfl

def cutoffSign (M n : ℕ) : ℝ :=
  predicateSign (fun k => cutoffPrime M k < cutoffPrime M (k + 1)) n

lemma cutoffSign_periodic (M : ℕ) : Function.Periodic (cutoffSign M) M := by
  intro n
  simp only [cutoffSign, predicateSign, show n + M + 1 = n + 1 + M by omega,
    cutoffPrime_periodic M n, cutoffPrime_periodic M (n + 1)]

lemma cutoffSign_sq (M n : ℕ) : cutoffSign M n * cutoffSign M n = 1 := by
  unfold cutoffSign predicateSign
  split_ifs <;> norm_num

lemma cutoffSign_sum_zero (M : ℕ) (hM : 0 < M) (heven : 2 ∣ M) :
    ∑ n ∈ Finset.range M, cutoffSign M n = 0 := by
  change (∑ n ∈ Finset.range M, predicateSign (fun k => cutoffPrime M k < cutoffPrime M (k + 1)) n) = 0
  rw [predicateSign_sum]
  have h : 2 * (((Finset.range M).filter fun n =>
      cutoffPrime M (n + 1) > cutoffPrime M n).card : ℝ) = M := by
    exact_mod_cast cutoff_comparison_count_half M hM heven
  linarith

lemma cutoffPrime_pos (M n : ℕ) (hM : 0 < M) : 0 < cutoffPrime M n := by
  have hg : 0 < n.gcd M := Nat.gcd_pos_of_pos_right n hM
  by_cases h : n.gcd M = 1
  · simp [cutoffPrime, h]
  · exact (Nat.prime_maxPrimeFac_of_one_lt (n.gcd M) (by omega)).pos

lemma cutoffPrime_le (M n : ℕ) (hM : 0 < M) : cutoffPrime M n ≤ M :=
  Nat.maxPrimeFac_le.trans (Nat.gcd_le_right n hM)

lemma cutoffPrime_le_maxPrimeFac (M n : ℕ) (hM : 0 < M) :
    cutoffPrime M n ≤ Nat.maxPrimeFac M := by
  by_cases hg : n.gcd M = 1
  · have hpos := cutoffPrime_pos M 0 hM
    simpa [cutoffPrime, hg] using hpos
  · have hgt : 1 < n.gcd M := by
      have := Nat.gcd_pos_of_pos_right n hM
      omega
    exact Nat.le_maxPrimeFac hM.ne' (Nat.prime_maxPrimeFac_of_one_lt _ hgt)
      (Nat.maxPrimeFac_dvd.trans (Nat.gcd_dvd_right n M))

lemma cutoffPrime_mul (M R n : ℕ) (hM : 0 < M) (hR : 0 < R) (hc : M.Coprime R) :
    cutoffPrime (M * R) n = max (cutoffPrime M n) (cutoffPrime R n) := by
  rw [cutoffPrime, hc.gcd_mul, Nat.maxPrimeFac_mul
    (Nat.gcd_pos_of_pos_right n hM).ne' (Nat.gcd_pos_of_pos_right n hR).ne']
  rfl

lemma cutoffPrime_eq_one_iff (R n : ℕ) (hR : 0 < R) :
    cutoffPrime R n = 1 ↔ R.Coprime n := by
  have hg : 0 < n.gcd R := Nat.gcd_pos_of_pos_right n hR
  constructor
  · intro h
    have hn : n.gcd R = 1 := by
      by_contra hn
      have hp := (Nat.prime_maxPrimeFac_of_one_lt (n.gcd R) (by omega)).one_lt
      change 1 < cutoffPrime R n at hp
      omega
    exact Nat.coprime_comm.mp hn
  · intro h
    simp [cutoffPrime, h.symm.gcd_eq_one]

lemma cutoffPrime_ties_iff (R n : ℕ) (hR : 0 < R) :
    cutoffPrime R n = cutoffPrime R (n + 1) ↔
      R.Coprime n ∧ R.Coprime (n + 1) := by
  have hd (k : ℕ) : cutoffPrime R k ∣ k :=
    Nat.maxPrimeFac_dvd.trans (Nat.gcd_dvd_left k R)
  constructor
  · intro he
    have h1 : cutoffPrime R n = 1 := Nat.dvd_one.mp
      ((Nat.dvd_add_iff_right (hd n)).mpr (he ▸ hd (n + 1)))
    exact ⟨(cutoffPrime_eq_one_iff R n hR).mp h1,
      (cutoffPrime_eq_one_iff R (n + 1) hR).mp (he ▸ h1)⟩
  · rintro ⟨ha, hb⟩
    rw [(cutoffPrime_eq_one_iff R n hR).mpr ha,
      (cutoffPrime_eq_one_iff R (n + 1) hR).mpr hb]

lemma cutoffPrime_one_or_large (M R n : ℕ) (hR : 0 < R)
    (hlarge : ∀ p, p.Prime → p ∣ R → M < p) :
    cutoffPrime R n = 1 ∨ M < cutoffPrime R n := by
  by_cases h : n.gcd R = 1
  · exact Or.inl (by simp [cutoffPrime, h])
  · have hg : 1 < n.gcd R := by
      have := Nat.gcd_pos_of_pos_right n hR
      omega
    apply Or.inr
    exact hlarge _ (Nat.prime_maxPrimeFac_of_one_lt _ hg)
      (Nat.maxPrimeFac_dvd.trans (Nat.gcd_dvd_right n R))

lemma comparison_max_of_separated (a b c d M : ℕ)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (haM : a ≤ M) (hcM : c ≤ M)
    (hb : b = 1 ∨ M < b) (hd : d = 1 ∨ M < d)
    (htie : b = d → b = 1) :
    (if max a b < max c d then (1 : ℝ) else -1) =
      if b = d then (if a < c then 1 else -1) else (if b < d then 1 else -1) := by
  rcases hb with rfl | hb <;> rcases hd with rfl | hd
  · simp [max_eq_left ha, max_eq_left hc]
  · have hbd : 1 < d := (ha.trans haM).trans_lt hd
    simp [max_eq_left ha, max_eq_right (hcM.trans hd.le), (haM.trans_lt hd), hbd, hbd.ne]
  · have hbd : 1 < b := (hc.trans hcM).trans_lt hb
    simp [max_eq_left hc, max_eq_right (haM.trans hb.le), not_lt.mpr (hcM.trans hb.le),
      hbd.ne', not_lt.mpr hbd.le]
  · rw [max_eq_right (haM.trans hb.le), max_eq_right (hcM.trans hd.le)]
    by_cases he : b = d
    · have h1 := htie he
      omega
    · simp [he]


lemma cutoffSign_mul (M R n : ℕ) (hM : 0 < M) (hR : 0 < R) (hc : M.Coprime R)
    (hlarge : ∀ p, p.Prime → p ∣ R → Nat.maxPrimeFac M < p) :
    cutoffSign (M * R) n =
      if cutoffPrime R n = cutoffPrime R (n + 1) then cutoffSign M n else cutoffSign R n := by
  have htie : cutoffPrime R n = cutoffPrime R (n + 1) → cutoffPrime R n = 1 := by
    intro h
    exact (cutoffPrime_eq_one_iff R n hR).mpr ((cutoffPrime_ties_iff R n hR).mp h).1
  unfold cutoffSign predicateSign
  dsimp only
  rw [cutoffPrime_mul M R n hM hR hc, cutoffPrime_mul M R (n + 1) hM hR hc]
  exact comparison_max_of_separated _ _ _ _ (Nat.maxPrimeFac M)
    (cutoffPrime_pos M n hM) (cutoffPrime_pos M (n + 1) hM)
    (cutoffPrime_le_maxPrimeFac M n hM) (cutoffPrime_le_maxPrimeFac M (n + 1) hM)
    (cutoffPrime_one_or_large (Nat.maxPrimeFac M) R n hR hlarge)
    (cutoffPrime_one_or_large (Nat.maxPrimeFac M) R (n + 1) hR hlarge) htie

def cutoffTied (R n : ℕ) : Prop := cutoffPrime R n = cutoffPrime R (n + 1)

instance (R n : ℕ) : Decidable (cutoffTied R n) := inferInstanceAs (Decidable (_ = _))

lemma cutoffTied_periodic (R : ℕ) : Function.Periodic (cutoffTied R) R := by
  intro n
  simp only [cutoffTied, show n + R + 1 = n + 1 + R by omega,
    cutoffPrime_periodic R n, cutoffPrime_periodic R (n + 1)]

lemma cutoffSign_correlation_sum (M R : ℕ) (hM : 0 < M) (hR : 0 < R)
    (heven : 2 ∣ M) (hc : M.Coprime R)
    (hlarge : ∀ p, p.Prime → p ∣ R → Nat.maxPrimeFac M < p) :
    (∑ n ∈ Finset.range (M * R), cutoffSign (M * R) n * cutoffSign M n) =
      (M : ℝ) * ((Finset.range R).filter (cutoffTied R)).card := by
  let f (a b : ℕ) : ℝ :=
    (if cutoffTied R b then cutoffSign M a else cutoffSign R b) * cutoffSign M a
  have hterm (n : ℕ) : cutoffSign (M * R) n * cutoffSign M n = f (n % M) (n % R) := by
    rw [cutoffSign_mul M R n hM hR hc hlarge]
    change (if cutoffTied R n then cutoffSign M n else cutoffSign R n) * cutoffSign M n = _
    simp only [f, (cutoffSign_periodic M).map_mod_nat n,
      (cutoffSign_periodic R).map_mod_nat n, (cutoffTied_periodic R).map_mod_nat n]
  simp_rw [hterm]
  rw [sum_range_coprime M R hM hR hc, Finset.sum_comm]
  have hinner (b : ℕ) : (∑ a ∈ Finset.range M, f a b) = if cutoffTied R b then (M : ℝ) else 0 := by
    by_cases hb : cutoffTied R b
    · simp [f, hb, cutoffSign_sq]
    · simp only [f, if_neg hb, ← Finset.mul_sum, cutoffSign_sum_zero M hM heven, mul_zero]
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  simp [mul_comm]

lemma cutoffTied_card_le_totient (R : ℕ) (hR : 0 < R) :
    ((Finset.range R).filter (cutoffTied R)).card ≤ R.totient := by
  rw [Nat.totient_eq_card_coprime]
  apply Finset.card_le_card
  intro n hn
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
    ((cutoffPrime_ties_iff R n hR).mp (Finset.mem_filter.mp hn).2).1⟩

def cutoffDisagree (M L n : ℕ) : Prop := cutoffSign M n ≠ cutoffSign L n

noncomputable instance (M L n : ℕ) : Decidable (cutoffDisagree M L n) := Classical.propDecidable _

lemma cutoffDisagree_indicator (M L n : ℕ) :
    (if cutoffDisagree M L n then (1 : ℝ) else 0) =
      (1 - cutoffSign L n * cutoffSign M n) / 2 := by
  unfold cutoffDisagree cutoffSign predicateSign
  split_ifs <;> norm_num at *

lemma cutoffDisagree_count_eq (M R : ℕ) (hM : 0 < M) (hR : 0 < R)
    (heven : 2 ∣ M) (hc : M.Coprime R)
    (hlarge : ∀ p, p.Prime → p ∣ R → Nat.maxPrimeFac M < p) :
    2 * (((Finset.range (M * R)).filter (cutoffDisagree M (M * R))).card : ℝ) =
      (M : ℝ) * (R - ((Finset.range R).filter (cutoffTied R)).card) := by
  have h := Finset.sum_congr (s₁ := Finset.range (M * R)) rfl
    (fun n _ => cutoffDisagree_indicator M (M * R) n)
  rw [← Finset.sum_div, Finset.sum_sub_distrib] at h
  simp only [Finset.sum_boole,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    cutoffSign_correlation_sum M R hM hR heven hc hlarge, Nat.cast_mul] at h
  linarith

lemma prod_one_sub_mul_one_add_sum_le_one {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    (∏ i ∈ s, (1 - f i)) * (1 + ∑ i ∈ s, f i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg fun i hi => (hfs i hi).1
    have hprod : 0 ≤ ∏ i ∈ s, (1 - f i) := Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hfs i hi).2
    have hi := ih hfs
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hex : 0 ≤ (∏ i ∈ s, (1 - f i)) * f a * ((∑ i ∈ s, f i) + f a) :=
      mul_nonneg (mul_nonneg hprod hfa.1) (add_nonneg hsum hfa.1)
    nlinarith

lemma totient_prod_bound (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime)
    (hsum : (1 / 2 : ℝ) ≤ ∑ p ∈ S, (1 : ℝ) / p) :
    3 * (∏ p ∈ S, p).totient ≤ 2 * (∏ p ∈ S, p) := by
  let R := ∏ p ∈ S, p
  have hfac : R.primeFactors = S := Nat.primeFactors_prod hp
  have hf (p : ℕ) (hpS : p ∈ S) : 0 ≤ (1 : ℝ) / p ∧ (1 : ℝ) / p ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast (hp p hpS).pos)).mpr
      exact_mod_cast (hp p hpS).one_le
  have hprod := prod_one_sub_mul_one_add_sum_le_one S (fun p => (1 : ℝ) / p) hf
  have hnonneg : 0 ≤ ∏ p ∈ S, (1 - (1 : ℝ) / p) :=
    Finset.prod_nonneg fun p hpS => sub_nonneg.mpr (hf p hpS).2
  have hratio : 3 * (∏ p ∈ S, (1 - (1 : ℝ) / p)) ≤ 2 := by
    nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hsum)]
  have he := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors R)
  push_cast at he
  rw [hfac] at he
  simp only [← one_div] at he
  have : (3 : ℝ) * R.totient ≤ 2 * R := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg (α := ℝ) R)]
  exact_mod_cast this

lemma exists_large_prime_modulus (M : ℕ) (hM : 0 < M) :
    ∃ R : ℕ, 0 < R ∧ M.Coprime R ∧ (∀ p, p.Prime → p ∣ R → M < p) ∧
      3 * R.totient ≤ 2 * R := by
  let S := (4 ^ ((M + 1).primesBelow.card + 1)).succ.primesBelow \ (M + 1).primesBelow
  have hp (p : ℕ) (hpS : p ∈ S) : p.Prime :=
    Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hpS).1
  have hlarge (p : ℕ) (hpS : p ∈ S) : M < p := by
    have hnot := (Finset.mem_sdiff.mp hpS).2
    have hprime := hp p hpS
    simp only [Nat.mem_primesBelow, hprime, and_true, not_lt] at hnot
    omega
  let R := ∏ p ∈ S, p
  have hR : 0 < R := Finset.prod_pos fun p hpS => (hp p hpS).pos
  have hfac : R.primeFactors = S := Nat.primeFactors_prod hp
  have hc : M.Coprime R := by
    apply Nat.Coprime.prod_right
    intro p hpS
    apply Nat.Coprime.symm
    apply (hp p hpS).coprime_iff_not_dvd.mpr
    intro hd
    exact (not_le.mpr (hlarge p hpS)) (Nat.le_of_dvd hM hd)
  refine ⟨R, hR, hc, ?_, ?_⟩
  · intro p hprime hd
    apply hlarge
    rw [← hfac]
    exact Nat.mem_primeFactors.mpr ⟨hprime, hd, hR.ne'⟩
  · exact totient_prod_bound S hp (one_half_le_sum_primes_ge_one_div (M + 1))


open Filter in
lemma periodic_predicate_hasDensity (P : ℕ → Prop) [DecidablePred P] (M : ℕ)
    (hM : 0 < M) (hper : Function.Periodic P M) :
    {n | P n}.HasDensity (((Finset.range M).filter P).card / (M : ℝ)) := by
  let d : ℝ := ((Finset.range M).filter P).card / (M : ℝ)
  have hd0 : 0 ≤ d := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd1 : d ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hM)).mpr
    exact_mod_cast (Finset.card_filter_le (Finset.range M) P).trans_eq (Finset.card_range M)
  let f (n : ℕ) : ℝ := (if P n then 1 else 0) - d
  have hfper : Function.Periodic f M := by
    intro n
    simp only [f, hper n]
  have hsum (N : ℕ) : (∑ n ∈ Finset.range N, f n) =
      (((Finset.range N).filter P).card : ℝ) - N * d := by
    simp [f, Finset.sum_sub_distrib]
  have hfzero : ∑ n ∈ Finset.range M, f n = 0 := by
    rw [hsum]
    dsimp [d]
    have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
    ring
  have hfbound (n : ℕ) : ‖f n‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    dsimp [f]
    split_ifs <;> constructor <;> linarith
  have ht := (periodic_zero_mean_tendsto f M hM hfper hfzero hfbound).add_const d
  rw [density_iff_count]
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [hsum]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

lemma cutoffDisagree_periodic (M R : ℕ) :
    Function.Periodic (cutoffDisagree M (M * R)) (M * R) := by
  have hm : Function.Periodic (cutoffSign M) (M * R) := by
    simpa only [nsmul_eq_mul, mul_comm] using (cutoffSign_periodic M).nsmul R
  intro n
  simp only [cutoffDisagree, hm n, cutoffSign_periodic (M * R) n]

/-- The exact density of disagreement between an old even cutoff and its
extension by larger primes. -/
theorem cutoffDisagree_hasDensity (M R : ℕ) (hM : 0 < M) (hR : 0 < R)
    (heven : 2 ∣ M) (hc : M.Coprime R)
    (hlarge : ∀ p, p.Prime → p ∣ R → Nat.maxPrimeFac M < p) :
    {n | cutoffDisagree M (M * R) n}.HasDensity
      ((R - (((Finset.range R).filter (cutoffTied R)).card : ℝ)) / (2 * R)) := by
  have ht := periodic_predicate_hasDensity (cutoffDisagree M (M * R)) (M * R)
    (Nat.mul_pos hM hR) (cutoffDisagree_periodic M R)
  have he := cutoffDisagree_count_eq M R hM hR heven hc hlarge
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  convert ht using 1
  push_cast
  field_simp
  nlinarith

/-- For every even cutoff, there is a finer cutoff whose comparison signs
differ from the original cutoff on a set of natural density at least one sixth.
This rules out mean-Cauchy convergence of the cutoff comparisons. -/
theorem cutoff_signs_uniformly_separated (M : ℕ) (hM : 0 < M) (heven : 2 ∣ M) :
    ∃ L : ℕ, M ∣ L ∧ 0 < L ∧ ∃ d : ℝ, 1 / 6 ≤ d ∧
      {n | cutoffDisagree M L n}.HasDensity d := by
  obtain ⟨R, hR, hc, hlarge, htotient⟩ := exists_large_prime_modulus M hM
  have hlarge' (p : ℕ) (hp : p.Prime) (hd : p ∣ R) : Nat.maxPrimeFac M < p :=
    Nat.maxPrimeFac_le.trans_lt (hlarge p hp hd)
  let T := ((Finset.range R).filter (cutoffTied R)).card
  refine ⟨M * R, Nat.dvd_mul_right M R, Nat.mul_pos hM hR,
    ((R : ℝ) - T) / (2 * R), ?_, cutoffDisagree_hasDensity M R hM hR heven hc hlarge'⟩
  have ht : T ≤ R.totient := cutoffTied_card_le_totient R hR
  have ht' : (3 : ℝ) * T ≤ 2 * R := by exact_mod_cast (htotient.trans' (Nat.mul_le_mul_left 3 ht))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * R)).mpr
  linarith

#print axioms cutoffSign_correlation_sum
#print axioms cutoffDisagree_hasDensity
#print axioms cutoff_signs_uniformly_separated


/-- Uniform separation also holds for the standard cutoffs that include every
prime up to the threshold, rather than just for arbitrary cutoff moduli. -/
theorem primorial_cutoff_signs_uniformly_separated (B : ℕ) (hB : 2 ≤ B) :
    ∃ C : ℕ, B ≤ C ∧ ∃ d : ℝ, 1 / 6 ≤ d ∧
      {n | cutoffDisagree (primorial B) (primorial C) n}.HasDensity d := by
  let S₀ := (B + 1).primesBelow
  let C := max B (4 ^ (S₀.card + 1))
  let S₁ := (C + 1).primesBelow
  let S := S₁ \ S₀
  let M := primorial B
  let R := ∏ p ∈ S, p
  have hBC : B ≤ C := le_max_left _ _
  have hS₀ : ∀ p ∈ S₀, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  have hS : ∀ p ∈ S, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hM : 0 < M := primorial_pos B
  have hR : 0 < R := Finset.prod_pos fun p hp => (hS p hp).pos
  have hprodM : M = ∏ p ∈ S₀, p := rfl
  have hfacM : M.primeFactors = S₀ := hprodM ▸ Nat.primeFactors_prod hS₀
  have hfacR : R.primeFactors = S := Nat.primeFactors_prod hS
  have heven : 2 ∣ M := by
    rw [hprodM]
    apply Finset.dvd_prod_of_mem id
    exact Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  have hmax : Nat.maxPrimeFac M ≤ B := by
    have hM2 := Nat.le_of_dvd hM heven
    have hmem : Nat.maxPrimeFac M ∈ M.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.prime_maxPrimeFac_of_one_lt M (by omega), Nat.maxPrimeFac_dvd, hM.ne'⟩
    rw [hfacM] at hmem
    exact Nat.le_of_lt_succ (Nat.mem_primesBelow.mp hmem).1
  have hlarge (p : ℕ) (hprime : p.Prime) (hd : p ∣ R) : Nat.maxPrimeFac M < p := by
    have hmem : p ∈ S := by
      rw [← hfacR]
      exact Nat.mem_primeFactors.mpr ⟨hprime, hd, hR.ne'⟩
    have hnot := (Finset.mem_sdiff.mp hmem).2
    have hBp : B < p := by
      simp only [S₀, Nat.mem_primesBelow, hprime, and_true, not_lt] at hnot
      omega
    exact hmax.trans_lt hBp
  have hc : M.Coprime R := by
    apply Nat.Coprime.prod_right
    intro p hp
    apply Nat.Coprime.symm
    apply (hS p hp).coprime_iff_not_dvd.mpr
    intro hd
    have hmem : p ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hS p hp, hd, hM.ne'⟩
    rw [hfacM] at hmem
    exact (Finset.mem_sdiff.mp hp).2 hmem
  have hsub : S₀ ⊆ S₁ := by
    intro p hp
    obtain ⟨hpB, hprime⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩
  have he : M * R = primorial C := by
    rw [hprodM, mul_comm]
    exact Finset.prod_sdiff hsub
  have hsub' : (4 ^ (S₀.card + 1)).succ.primesBelow \ S₀ ⊆ S := by
    intro p hp
    obtain ⟨hpC, hpB⟩ := Finset.mem_sdiff.mp hp
    have hC : 4 ^ (S₀.card + 1) ≤ C := le_max_right _ _
    obtain ⟨hpC', hprime⟩ := Nat.mem_primesBelow.mp hpC
    exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩, hpB⟩
  have hsum : (1 / 2 : ℝ) ≤ ∑ p ∈ S, (1 : ℝ) / p :=
    (one_half_le_sum_primes_ge_one_div (B + 1)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun _ _ _ => by positivity))
  have htotient := totient_prod_bound S hS hsum
  let T := ((Finset.range R).filter (cutoffTied R)).card
  refine ⟨C, hBC, ((R : ℝ) - T) / (2 * R), ?_, ?_⟩
  · have ht : T ≤ R.totient := cutoffTied_card_le_totient R hR
    have ht' : (3 : ℝ) * T ≤ 2 * R := by
      exact_mod_cast (htotient.trans' (Nat.mul_le_mul_left 3 ht))
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * R)).mpr
    linarith
  · simpa only [he] using cutoffDisagree_hasDensity M R hM hR heven hc hlarge

#print axioms primorial_cutoff_signs_uniformly_separated


lemma cutoff_disagreement_triangle (A B : ℕ) (f : ℕ → ℝ) (N : ℕ) :
    ((Finset.range N).filter (cutoffDisagree A B)).card ≤
      ((Finset.range N).filter fun n => cutoffSign A n ≠ f n).card +
      ((Finset.range N).filter fun n => cutoffSign B n ≠ f n).card := by
  classical
  apply (Finset.card_le_card (show (Finset.range N).filter (cutoffDisagree A B) ⊆
      ((Finset.range N).filter fun n => cutoffSign A n ≠ f n) ∪
      ((Finset.range N).filter fun n => cutoffSign B n ≠ f n) from ?_)).trans
    (Finset.card_union_le _ _)
  intro n hn
  obtain ⟨hnN, hne⟩ := Finset.mem_filter.mp hn
  by_cases ha : cutoffSign A n = f n
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hnN, fun hb => hne (ha.trans hb.symm)⟩
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnN, ha⟩)

open Filter in
/-- Even though every finite cutoff has balanced comparisons, the standard
cutoff signs do not converge in density to any sequence. -/
theorem cutoff_signs_do_not_approximate_any_sequence (f : ℕ → ℝ) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∀ᶠ N : ℕ in atTop,
        (((Finset.range N).filter fun n => cutoffSign (primorial B) n ≠ f n).card : ℝ) / N < ε) := by
  classical
  intro h
  obtain ⟨B₀, hB₀⟩ := h (1 / 24) (by norm_num)
  let B := max B₀ 2
  obtain ⟨C, hBC, d, hd, hden⟩ :=
    primorial_cutoff_signs_uniformly_separated B (le_max_right _ _)
  have hEB := hB₀ B (le_max_left _ _)
  have hEC := hB₀ C ((le_max_left _ _).trans hBC)
  have ht := (density_iff_count (cutoffDisagree (primorial B) (primorial C)) d).mp hden
  have hlim : ∀ᶠ N : ℕ in atTop,
      (1 / 8 : ℝ) < (((Finset.range N).filter (cutoffDisagree (primorial B) (primorial C))).card : ℝ) / N :=
    ht.eventually (lt_mem_nhds (by linarith : (1 / 8 : ℝ) < d))
  have hbad : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hEB, hEC, hlim] with N hEB hEC hlim
    have hc := cutoff_disagreement_triangle (primorial B) (primorial C) f N
    have hc' : (((Finset.range N).filter (cutoffDisagree (primorial B) (primorial C))).card : ℝ) / N ≤
        (((Finset.range N).filter fun n => cutoffSign (primorial B) n ≠ f n).card : ℝ) / N +
        (((Finset.range N).filter fun n => cutoffSign (primorial C) n ≠ f n).card : ℝ) / N := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      exact_mod_cast hc
    linarith
  exact hbad.exists.choose_spec

lemma cutoffPrime_primorial_eq (B n : ℕ) (hn : 0 < n) (hnB : n ≤ B) :
    cutoffPrime (primorial B) n = Nat.maxPrimeFac n := by
  have hm : 0 < primorial B := primorial_pos B
  have hupper : cutoffPrime (primorial B) n ≤ Nat.maxPrimeFac n := by
    simpa only [cutoffPrime, Nat.gcd_comm] using cutoffPrime_le_maxPrimeFac n (primorial B) hn
  apply le_antisymm hupper
  by_cases hn1 : n = 1
  · subst n
    simp [cutoffPrime]
  · have hp := Nat.prime_maxPrimeFac_of_one_lt n (by omega)
    have hd : Nat.maxPrimeFac n ∣ primorial B := by
      apply Finset.dvd_prod_of_mem id
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.maxPrimeFac_le.trans hnB)), hp⟩
    exact Nat.le_maxPrimeFac (Nat.gcd_pos_of_pos_right n hm).ne' hp
      (Nat.dvd_gcd Nat.maxPrimeFac_dvd hd)

lemma cutoffSign_primorial_eq_factorSign (B n : ℕ) (hn : 0 < n) (hnB : n + 1 ≤ B) :
    cutoffSign (primorial B) n = factorSign n := by
  unfold cutoffSign factorSign predicateSign
  dsimp only
  rw [cutoffPrime_primorial_eq B n hn (by omega),
    cutoffPrime_primorial_eq B (n + 1) (by omega) hnB]

open Filter in
/-- Pointwise stabilization does hold away from the single exceptional index zero;
the preceding theorem shows that it cannot be upgraded to convergence in density. -/
theorem cutoff_signs_eventually_pointwise (n : ℕ) (hn : 0 < n) :
    ∀ᶠ B : ℕ in atTop, cutoffSign (primorial B) n = factorSign n := by
  filter_upwards [eventually_ge_atTop (n + 1)] with B hB
  exact cutoffSign_primorial_eq_factorSign B n hn hB

#print axioms cutoff_signs_do_not_approximate_any_sequence
#print axioms cutoff_signs_eventually_pointwise

end Erdos371
