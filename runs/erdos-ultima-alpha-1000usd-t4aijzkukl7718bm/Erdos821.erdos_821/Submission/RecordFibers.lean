import Submission.SmoothInputFamilies

/-!
# Record normalized multiplicities in full odd squarefree fibers

These are structural consequences of the previously proved fixed-exponent
lower bound. They do not prove exponents approaching one or settle Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

noncomputable def gOddSquarefree (n : ℕ) : ℕ :=
  {m : ℕ | Squarefree m ∧ Odd m ∧ totient m = n}.ncard

lemma finite_odd_squarefree_totient_fiber (n : ℕ) :
    {m : ℕ | Squarefree m ∧ Odd m ∧ totient m = n}.Finite :=
  (finite_totient_fiber n).subset (fun _ hm => hm.2.2)

noncomputable def oddSquarefreeFiber (n : ℕ) : Finset ℕ :=
  (finite_odd_squarefree_totient_fiber n).toFinset

@[simp] lemma mem_oddSquarefreeFiber {m n : ℕ} :
    m ∈ oddSquarefreeFiber n ↔ Squarefree m ∧ Odd m ∧ totient m = n :=
  (finite_odd_squarefree_totient_fiber n).mem_toFinset

lemma card_oddSquarefreeFiber (n : ℕ) : (oddSquarefreeFiber n).card = gOddSquarefree n :=
  (Set.ncard_eq_toFinset_card _ (finite_odd_squarefree_totient_fiber n)).symm

lemma card_le_gOddSquarefree (S : Finset ℕ) (n : ℕ)
    (hS : ∀ m ∈ S, Squarefree m ∧ Odd m ∧ totient m = n) : S.card ≤ gOddSquarefree n := by
  have hsub : (S : Set ℕ) ⊆ {m : ℕ | Squarefree m ∧ Odd m ∧ totient m = n} := hS
  have h := Set.ncard_le_ncard hsub (finite_odd_squarefree_totient_fiber n)
  simpa only [Set.ncard_coe_finset, gOddSquarefree] using h

lemma exists_positive_power_gOddSquarefree :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      {n : ℕ | (n : ℝ) ^ δ < (gOddSquarefree n : ℝ)}.Infinite := by
  obtain ⟨δ, hδ, hδ1, H⟩ := exists_fixed_power_odd_fibers_without_large_input_primes
  refine ⟨δ, hδ, hδ1, Set.infinite_of_forall_exists_gt ?_⟩
  intro N
  obtain ⟨n, R, hn, hcard, hR⟩ := H 1 (by norm_num) N
  have hle : (R.card : ℝ) ≤ (gOddSquarefree n : ℝ) := by
    exact_mod_cast card_le_gOddSquarefree R n
      (fun m hm => ⟨(hR m hm).1, (hR m hm).2.1, (hR m hm).2.2.1⟩)
  exact ⟨n, hcard.trans_le hle, hn⟩

/-- An elementary record-value principle. Infinitely many positive-power
witnesses yield arbitrarily large record maxima of a weaker normalization,
while preserving the original witness exponent. -/
lemma exists_large_normalized_record (f : ℕ → ℕ) (δ : ℝ) (hδ : 0 < δ)
    (H : {n : ℕ | (n : ℝ) ^ δ < (f n : ℝ)}.Infinite) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ (n : ℝ) ^ δ < (f n : ℝ) ∧
      ∀ j : ℕ, j ≤ n → (f j : ℝ) / (j : ℝ) ^ (δ / 2) ≤
        (f n : ℝ) / (n : ℝ) ^ (δ / 2) := by
  let s := δ / 2
  let F : ℕ → ℝ := fun n => (f n : ℝ) / (n : ℝ) ^ s
  let C := ∑ j ∈ Finset.range (N + 1), F j
  have hs : 0 < s := half_pos hδ
  have hFnonneg (j : ℕ) : 0 ≤ F j := by dsimp [F]; positivity
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ s) atTop atTop :=
    (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hlim.eventually (eventually_gt_atTop C))
  obtain ⟨m, hmf, hmM⟩ := H.exists_gt M
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmPow : 0 < (m : ℝ) ^ s := Real.rpow_pos_of_pos hmpos s
  have hFmbig : (m : ℝ) ^ s < F m := by
    apply (lt_div_iff₀ hmPow).mpr
    rw [← Real.rpow_add hmpos]
    have heq : s + s = δ := by dsimp [s]; ring
    rw [heq]
    exact hmf
  obtain ⟨n, hnmem, hmax⟩ := Finset.exists_max_image (Finset.range (m + 1)) F
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hnm : n ≤ m := by have := Finset.mem_range.mp hnmem; omega
  have hFn : F m ≤ F n := hmax m (Finset.mem_range.mpr (by omega))
  have hNn : N < n := by
    by_contra h
    have hnN : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hFC : F n ≤ C := Finset.single_le_sum (fun j _ => hFnonneg j) hnN
    exact (not_lt_of_ge hFC) ((hM m hmM.le).trans (hFmbig.trans_le hFn))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnPow : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos hnpos s
  have hpowid : (n : ℝ) ^ δ = (n : ℝ) ^ s * (n : ℝ) ^ s := by
    rw [← Real.rpow_add hnpos]
    congr 1
    dsimp [s]
    ring
  refine ⟨n, hNn, ?_, ?_⟩
  · calc
      (n : ℝ) ^ δ = (n : ℝ) ^ s * (n : ℝ) ^ s := hpowid
      _ ≤ (m : ℝ) ^ s * (n : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnm) hs.le) hnPow.le
      _ < F n * (n : ℝ) ^ s := mul_lt_mul_of_pos_right (hFmbig.trans_le hFn) hnPow
      _ = (f n : ℝ) := div_mul_cancel₀ _ hnPow.ne'
  · intro j hj
    exact hmax j (Finset.mem_range.mpr (by omega))

/-- Division by a common divisor maps an odd squarefree fiber injectively
into the full odd squarefree fiber at the reduced output. -/
lemma card_oddSquarefreeFiber_dvd_le (n d : ℕ) (hd : 0 < d) :
    ((oddSquarefreeFiber n).filter (fun m => d ∣ m)).card ≤ gOddSquarefree (n / totient d) := by
  let S := (oddSquarefreeFiber n).filter (fun m => d ∣ m)
  have hinj : Set.InjOn (fun m : ℕ => m / d) (S : Set ℕ) := by
    intro a ha b hb hab
    have hda := (Finset.mem_filter.mp ha).2
    have hdb := (Finset.mem_filter.mp hb).2
    calc
      a = d * (a / d) := (Nat.mul_div_cancel' hda).symm
      _ = d * (b / d) := congrArg (fun m : ℕ => d * m) hab
      _ = b := Nat.mul_div_cancel' hdb
  have hmap (q : ℕ) (hq : q ∈ S.image (fun m => m / d)) :
      Squarefree q ∧ Odd q ∧ totient q = n / totient d := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hmF, hdm⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmSq, hmOdd, hmφ⟩ := mem_oddSquarefreeFiber.mp hmF
    have hdiv := Nat.div_dvd_of_dvd hdm
    have hcop : Nat.Coprime d (m / d) := by
      apply Nat.coprime_of_squarefree_mul
      rw [Nat.mul_div_cancel' hdm]
      exact hmSq
    have hφ : totient (m / d) = n / totient d := by
      have h := Nat.totient_mul hcop
      rw [Nat.mul_div_cancel' hdm, hmφ] at h
      exact Nat.eq_div_of_mul_eq_right (Nat.totient_pos.mpr hd).ne' h.symm
    exact ⟨hmSq.squarefree_of_dvd hdiv, hmOdd.of_dvd_nat hdiv, hφ⟩
  have hcard := card_le_gOddSquarefree (S.image (fun m => m / d)) (n / totient d) hmap
  rwa [Finset.card_image_of_injOn hinj] at hcard

/-- At a normalized record, divisibility by `d` has frequency at most
`totient(d)^(-s)` in the FULL odd squarefree fiber. -/
lemma normalized_record_odd_fiber_core_bound (n d : ℕ) (hn : 0 < n) (s : ℝ)
    (hrec : ∀ j : ℕ, j ≤ n → (gOddSquarefree j : ℝ) / (j : ℝ) ^ s ≤
      (gOddSquarefree n : ℝ) / (n : ℝ) ^ s) :
    (totient d : ℝ) ^ s * (((oddSquarefreeFiber n).filter (fun m => d ∣ m)).card : ℝ) ≤
      (gOddSquarefree n : ℝ) := by
  by_cases hne : ((oddSquarefreeFiber n).filter (fun m => d ∣ m)).Nonempty
  · obtain ⟨m, hm⟩ := hne
    obtain ⟨hmF, hdm⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmSq, _, hmφ⟩ := mem_oddSquarefreeFiber.mp hmF
    have hdSq := hmSq.squarefree_of_dvd hdm
    have hd : 0 < d := Nat.pos_of_ne_zero hdSq.ne_zero
    have hφpos : 0 < totient d := Nat.totient_pos.mpr hd
    have hφdiv : totient d ∣ n := by
      rw [← hmφ]
      exact Nat.totient_dvd_of_dvd hdm
    let q := n / totient d
    have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hn hφdiv) hφpos
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hqPow : 0 < (q : ℝ) ^ s := Real.rpow_pos_of_pos hqR s
    have hnPow : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos hnR s
    have hprod := (div_le_div_iff₀ hqPow hnPow).mp (hrec q (Nat.div_le_self _ _))
    have hpowid : (n : ℝ) ^ s = (q : ℝ) ^ s * (totient d : ℝ) ^ s := by
      rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      congr 1
      exact_mod_cast (Nat.div_mul_cancel hφdiv).symm
    have hG : (totient d : ℝ) ^ s * (gOddSquarefree q : ℝ) ≤ (gOddSquarefree n : ℝ) := by
      apply (mul_le_mul_iff_left₀ hqPow).mp
      calc
        ((totient d : ℝ) ^ s * (gOddSquarefree q : ℝ)) * (q : ℝ) ^ s =
            (gOddSquarefree q : ℝ) * (n : ℝ) ^ s := by rw [hpowid]; ring
        _ ≤ _ := hprod
    have hcard : (((oddSquarefreeFiber n).filter (fun m => d ∣ m)).card : ℝ) ≤
        (gOddSquarefree q : ℝ) := by exact_mod_cast card_oddSquarefreeFiber_dvd_le n d hd
    exact (mul_le_mul_of_nonneg_left hcard (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans hG
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero,
      mul_zero, Nat.cast_nonneg]

lemma le_totient_sq_of_squarefree_odd (d : ℕ) (hdSq : Squarefree d) (hdOdd : Odd d) :
    d ≤ (totient d) ^ 2 := by
  calc
    d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hdSq).symm
    _ ≤ ∏ p ∈ d.primeFactors, (p - 1) ^ 2 := by
      apply Finset.prod_le_prod'
      intro p hp
      have hpprime := Nat.prime_of_mem_primeFactors hp
      have hp2 := hpprime.two_le
      have hpne : p ≠ 2 := by
        intro h
        exact hdOdd.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors hp)
      have hp3 : 3 ≤ p := by omega
      have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
      nlinarith
    _ = (∏ p ∈ d.primeFactors, (p - 1)) ^ 2 := Finset.prod_pow _ _ _
    _ = (totient d) ^ 2 := by
      congr 1
      rw [← totient_prod_primes d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp),
        Nat.prod_primeFactors_of_squarefree hdSq]

/-- Full odd squarefree fibers can have polynomial cardinality while every
polynomially large common divisor occurs on a polynomially small fraction.
Unlike the earlier subset construction, this is about the ENTIRE restricted
fiber. The positive exponent remains fixed, not arbitrarily close to one. -/
theorem exists_large_full_odd_fibers_with_sparse_common_divisors :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ N : ℕ,
      ∃ n : ℕ, N < n ∧ (n : ℝ) ^ δ < (gOddSquarefree n : ℝ) ∧
        ∀ (η : ℝ) (d : ℕ), (n : ℝ) ^ η ≤ d →
          (n : ℝ) ^ (δ * η / 4) *
            (((oddSquarefreeFiber n).filter (fun m => d ∣ m)).card : ℝ) ≤
              (gOddSquarefree n : ℝ) := by
  obtain ⟨δ, hδ, hδ1, H⟩ := exists_positive_power_gOddSquarefree
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro N
  obtain ⟨n, hnN, hnG, hrec⟩ := exists_large_normalized_record gOddSquarefree δ hδ H N
  have hn : 0 < n := by omega
  refine ⟨n, hnN, hnG, ?_⟩
  intro η d hd
  by_cases hne : ((oddSquarefreeFiber n).filter (fun m => d ∣ m)).Nonempty
  · obtain ⟨m, hm⟩ := hne
    obtain ⟨hmF, hdm⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmSq, hmOdd, _⟩ := mem_oddSquarefreeFiber.mp hmF
    have hdSq := hmSq.squarefree_of_dvd hdm
    have hdOdd := hmOdd.of_dvd_nat hdm
    have hdBound : (d : ℝ) ≤ (totient d : ℝ) ^ 2 := by
      exact_mod_cast le_totient_sq_of_squarefree_odd d hdSq hdOdd
    have hbase : (n : ℝ) ^ (δ * η / 4) ≤ (totient d : ℝ) ^ (δ / 2) := by
      calc
        (n : ℝ) ^ (δ * η / 4) = ((n : ℝ) ^ η) ^ (δ / 4) := by
          rw [← Real.rpow_mul (Nat.cast_nonneg n)]
          congr 1
          ring
        _ ≤ (d : ℝ) ^ (δ / 4) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hd (by positivity)
        _ ≤ ((totient d : ℝ) ^ 2) ^ (δ / 4) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hdBound (by positivity)
        _ = (totient d : ℝ) ^ (δ / 2) := by
          rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
          congr 1
          norm_num
          ring
    exact (mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg _)).trans
      (normalized_record_odd_fiber_core_bound n d hn (δ / 2) hrec)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero,
      mul_zero, Nat.cast_nonneg]

lemma gOddSquarefree_le_gSquarefree (n : ℕ) : gOddSquarefree n ≤ gSquarefree n :=
  Set.ncard_le_ncard (fun _ hm => ⟨hm.1, hm.2.2⟩) (finite_squarefree_totient_fiber n)

lemma gSquarefree_le_two_gOddSquarefree (n : ℕ) : gSquarefree n ≤ 2 * gOddSquarefree n := by
  let S := (finite_squarefree_totient_fiber n).toFinset
  have hS (m : ℕ) (hm : m ∈ S) : Squarefree m ∧ totient m = n :=
    (finite_squarefree_totient_fiber n).mem_toFinset.mp hm
  obtain ⟨R, hcard, hR⟩ := exists_odd_squarefree_subfiber S n hS
  have hRcard : R.card ≤ gOddSquarefree n :=
    card_le_gOddSquarefree R n (fun m hm => ⟨(hR m hm).1, (hR m hm).2.1, (hR m hm).2.2.1⟩)
  calc
    gSquarefree n = S.card := Set.ncard_eq_toFinset_card _ (finite_squarefree_totient_fiber n)
    _ ≤ 2 * R.card := hcard
    _ ≤ _ := Nat.mul_le_mul_left 2 hRcard

/-- Restricting to the FULL odd squarefree fiber does not change the
near-linear-exponent conjecture. This is an equivalence, not a proof of it. -/
lemma erdos_821_iff_odd_squarefree_inputs :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔
      ∀ ε > (0 : ℝ),
        {n : ℕ | (gOddSquarefree n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  apply erdos_821_iff_squarefree_inputs.trans
  constructor
  · intro H ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (ε / 2)) atTop atTop :=
      (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
    have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 2 ≤ (n : ℝ) ^ (ε / 2) := by
      filter_upwards [eventually_ge_atTop 1, hlim.eventually (eventually_ge_atTop (2 : ℝ))]
        with n hn hp
      exact ⟨hn, hp⟩
    obtain ⟨M, hM⟩ := eventually_atTop.mp hev
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hnG, hnN⟩ := (H (ε / 2) hhalf).exists_gt (max N M)
    obtain ⟨hn1, hnPow⟩ := hM n ((le_max_right _ _).trans hnN.le)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpow : 2 * (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - ε / 2) := by
      calc
        2 * (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (1 - ε) :=
          mul_le_mul_of_nonneg_right hnPow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = _ := by rw [← Real.rpow_add hnpos]; congr 1; ring
    have hle : (gSquarefree n : ℝ) ≤ 2 * (gOddSquarefree n : ℝ) := by
      exact_mod_cast gSquarefree_le_two_gOddSquarefree n
    refine ⟨n, ?_, (le_max_left _ _).trans_lt hnN⟩
    change (n : ℝ) ^ (1 - ε / 2) < (gSquarefree n : ℝ) at hnG
    change (n : ℝ) ^ (1 - ε) < (gOddSquarefree n : ℝ)
    linarith
  · intro H ε hε
    apply (H ε hε).mono
    intro n hn
    have hle : (gOddSquarefree n : ℝ) ≤ (gSquarefree n : ℝ) := by
      exact_mod_cast gOddSquarefree_le_gSquarefree n
    exact hn.trans_le hle

#print axioms exists_large_normalized_record
#print axioms card_oddSquarefreeFiber_dvd_le
#print axioms normalized_record_odd_fiber_core_bound
#print axioms le_totient_sq_of_squarefree_odd
#print axioms exists_large_full_odd_fibers_with_sparse_common_divisors
#print axioms erdos_821_iff_odd_squarefree_inputs

end Erdos821
