import FormalConjecturesUtil

namespace Erdos970

def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

noncomputable def jacobsthalFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | IsJacobsthalBound k m}

/-- A progression step divisible by all small primes provides a uniform interval bound. -/
theorem isJacobsthalBound_of_small_primes_dvd (k Q : ℕ) (hQpos : 0 < Q)
    (hprime : ∀ p : ℕ, p.Prime → p ≤ k → p ∣ Q) :
    IsJacobsthalBound k ((k + 1) * Q) := by
  classical
  intro n hn hnk a
  have hQposZ : 0 < (Q : ℤ) := by exact_mod_cast hQpos
  let r : ℕ := ((1 - a) % (Q : ℤ)).toNat
  have hr : (r : ℤ) = (1 - a) % (Q : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hQposZ))
  have hrlt : r < Q := by
    have := Int.emod_lt_of_pos (1 - a) hQposZ
    rw [← hr] at this
    exact_mod_cast this
  have hQr : (Q : ℤ) ∣ a + r - 1 := by
    have h := Int.dvd_emod_sub_self (x := 1 - a) (m := (Q : ℤ))
    rw [← hr] at h
    convert h using 1; ring
  by_contra h
  push_neg at h
  have hbad (j : Fin (k + 1)) : ¬(a + (r + Q * j.val : ℕ)).natAbs.Coprime n := by
    apply h
    have := j.isLt
    nlinarith
  have hex (j : Fin (k + 1)) : ∃ p : n.primeFactors,
      (p.val : ℤ) ∣ a + r + (Q : ℤ) * j.val := by
    obtain ⟨p, hp, hpj, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp (hbad j)
    refine ⟨⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩⟩, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_mul, add_assoc] using Int.natCast_dvd.mpr hpj
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    have hp := Nat.prime_of_mem_primeFactors (f i).property
    have hpZ := Nat.prime_iff_prime_int.mp hp
    have hi := hf i
    have hj : ((f i).val : ℤ) ∣ a + r + (Q : ℤ) * j.val := by
      simpa only [hij] using hf j
    have hnQ : ¬((f i).val : ℤ) ∣ (Q : ℤ) := by
      intro hd
      have hbase : ((f i).val : ℤ) ∣ a + r := by
        convert dvd_sub hi (dvd_mul_of_dvd_left hd (i.val : ℤ)) using 1; ring
      have hone : ((f i).val : ℤ) ∣ (1 : ℤ) := by
        convert dvd_sub hbase (dvd_trans hd hQr) using 1; ring
      exact hpZ.not_dvd_one hone
    have hkp : k < (f i).val := by
      by_contra hle
      apply hnQ
      exact_mod_cast (hprime (f i).val hp (by omega))
    have hdiff : ((f i).val : ℤ) ∣ (Q : ℤ) * ((j.val : ℤ) - i.val) := by
      convert dvd_sub hj hi using 1; ring
    have hd : ((f i).val : ℤ) ∣ (j.val : ℤ) - i.val :=
      (hpZ.dvd_mul.mp hdiff).resolve_left hnQ
    have hm : i.val ≡ j.val [MOD (f i).val] := Nat.modEq_of_dvd hd
    apply Fin.ext
    exact hm.eq_of_lt_of_lt (by omega) (by omega)
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  omega

/-- A basic factorial upper bound, ensuring that the defining infimum is nonempty. -/
theorem isJacobsthalBound_factorial (k : ℕ) : IsJacobsthalBound k (k + 1).factorial := by
  simpa only [Nat.factorial_succ] using
    isJacobsthalBound_of_small_primes_dvd k k.factorial (Nat.factorial_pos k)
      (fun p hp hpk => Nat.dvd_factorial hp.pos hpk)

/-- Only the product of primes up to `k`, rather than the factorial, is needed. -/
theorem isJacobsthalBound_primorial (k : ℕ) :
    IsJacobsthalBound k ((k + 1) * primorial k) := by
  apply isJacobsthalBound_of_small_primes_dvd k (primorial k) (primorial_pos k)
  intro p hp hpk
  exact Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hp⟩)

theorem isJacobsthalBound_mono {k m m' : ℕ} (h : IsJacobsthalBound k m)
    (hmm' : m ≤ m') : IsJacobsthalBound k m' := by
  intro n hn hnk a
  obtain ⟨i, him, hi⟩ := h n hn hnk a
  exact ⟨i, lt_of_lt_of_le him hmm', hi⟩

theorem isJacobsthalBound_jacobsthalFunction (k : ℕ) :
    IsJacobsthalBound k (jacobsthalFunction k) := by
  change sInf {m : ℕ | IsJacobsthalBound k m} ∈ {m : ℕ | IsJacobsthalBound k m}
  exact Nat.sInf_mem ⟨(k + 1).factorial, isJacobsthalBound_factorial k⟩

theorem jacobsthalFunction_le_iff (k m : ℕ) :
    jacobsthalFunction k ≤ m ↔ IsJacobsthalBound k m := by
  constructor
  · exact isJacobsthalBound_mono (isJacobsthalBound_jacobsthalFunction k)
  · intro h
    exact csInf_le' (s := {m : ℕ | IsJacobsthalBound k m}) h

theorem jacobsthalFunction_le_primorial (k : ℕ) :
    jacobsthalFunction k ≤ (k + 1) * primorial k :=
  (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_primorial k)

theorem jacobsthalFunction_le_exponential (k : ℕ) :
    jacobsthalFunction k ≤ (k + 1) * 4 ^ k :=
  (jacobsthalFunction_le_primorial k).trans
    (Nat.mul_le_mul_left (k + 1) (primorial_le_4_pow k))

theorem jacobsthalFunction_pos (k : ℕ) : 0 < jacobsthalFunction k := by
  obtain ⟨i, hi, _⟩ := isJacobsthalBound_jacobsthalFunction k 1 (by decide) (by simp) 0
  omega

theorem jacobsthalFunction_one : jacobsthalFunction 1 = 2 := by
  have hu : jacobsthalFunction 1 ≤ 2 :=
    (jacobsthalFunction_le_iff 1 2).mpr (isJacobsthalBound_factorial 1)
  obtain ⟨i, hi, hc⟩ := isJacobsthalBound_jacobsthalFunction 1 2 (by decide) (by simp [Nat.prime_two.primeFactors]) 0
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · norm_num at hc
  · omega


/-- The real-valued asymptotic conjecture is equivalent to a uniform integer interval bound. -/
theorem quadratic_bound_iff_nat :
    (∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2) ↔
    ∃ D : ℕ, 0 < D ∧ ∀ k : ℕ, 0 < k → IsJacobsthalBound k (D * k ^ 2) := by
  constructor
  · rintro ⟨C, hC, h⟩
    obtain ⟨D, hD⟩ := exists_nat_gt C
    have hDpos : 0 < D := by
      exact_mod_cast lt_trans hC hD
    refine ⟨D, hDpos, fun k hk => ?_⟩
    apply (jacobsthalFunction_le_iff k (D * k ^ 2)).mp
    have hh : (jacobsthalFunction k : ℝ) ≤ (D : ℝ) * (k : ℝ) ^ 2 :=
      (h k hk).trans (mul_le_mul_of_nonneg_right hD.le (sq_nonneg _))
    exact_mod_cast hh
  · rintro ⟨D, hD, h⟩
    refine ⟨(D : ℝ), by exact_mod_cast hD, fun k hk => ?_⟩
    have hh := (jacobsthalFunction_le_iff k (D * k ^ 2)).mpr (h k hk)
    exact_mod_cast hh


/-- Failure of a uniform interval bound is exactly a cover by prime residue classes. -/
theorem not_isJacobsthalBound_iff_cover (k m : ℕ) :
    ¬IsJacobsthalBound k m ↔
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ P.card ≤ k ∧
      ∃ r : ℕ → ℕ, ∀ i : ℕ, i < m → ∃ p ∈ P, i ≡ r p [MOD p] := by
  classical
  constructor
  · intro h
    unfold IsJacobsthalBound at h
    push_neg at h
    obtain ⟨n, hn, hnk, a, hbad⟩ := h
    let b := ((-a) % (n : ℤ)).toNat
    have hb : (b : ℤ) = (-a) % (n : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))
    have hnb : (n : ℤ) ∣ (b : ℤ) + a := by
      have h := Int.dvd_emod_sub_self (x := -a) (m := (n : ℤ))
      simpa only [← hb, sub_neg_eq_add] using h
    refine ⟨n.primeFactors, fun p hp => Nat.prime_of_mem_primeFactors hp,
      hnk, fun _ => b, fun i hi => ?_⟩
    obtain ⟨p, hp, hpi, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp (hbad i hi)
    refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩, ?_⟩
    have hpnZ : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
    have hd : (p : ℤ) ∣ (b : ℤ) - i := by
      convert dvd_sub (hpnZ.trans hnb) (Int.natCast_dvd.mpr hpi) using 1; ring
    exact Nat.modEq_of_dvd hd
  · rintro ⟨P, hP, hPk, r, hcover⟩ hbound
    let n := ∏ p ∈ P, p
    have hn : 0 < n := Finset.prod_pos (fun p hp => (hP p hp).pos)
    have hnk : n.primeFactors.card ≤ k := by
      simpa only [n, Nat.primeFactors_prod hP] using hPk
    have hco : Set.Pairwise (↑P : Set ℕ) Nat.Coprime :=
      fun p hp q hq hpq => (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
    let b := Nat.chineseRemainderOfFinset r id P (fun p hp => (hP p hp).ne_zero) hco
    obtain ⟨i, hi, hc⟩ := hbound n hn hnk (-(b.val : ℤ))
    obtain ⟨p, hpP, hpi⟩ := hcover i hi
    have hbpi : b.val ≡ i [MOD p] := (b.property p hpP).trans hpi.symm
    have hd : (p : ℤ) ∣ -(b.val : ℤ) + i := by
      convert hbpi.dvd using 1; ring
    exact Nat.not_coprime_of_dvd_of_dvd (hP p hpP).one_lt
      (Int.natCast_dvd.mp hd) (Finset.dvd_prod_of_mem id hpP) hc

/-- Each prime at least the interval length can cover at most one of its positions. -/
theorem cover_large_prime_budget (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ)
    (hcover : ∀ i : ℕ, i < m → ∃ p ∈ P, i ≡ r p [MOD p]) :
    ((Finset.range m).filter (fun i => ∀ p ∈ P, p < m → ¬i ≡ r p [MOD p])).card ≤
      (P.filter (fun p => m ≤ p)).card := by
  classical
  let S := (Finset.range m).filter (fun i => ∀ p ∈ P, p < m → ¬i ≡ r p [MOD p])
  let L := P.filter (fun p => m ≤ p)
  have hex (i : S) : ∃ p : L, i.val ≡ r p.val [MOD p.val] := by
    have hi := Finset.mem_filter.mp i.property
    obtain ⟨p, hpP, hpi⟩ := hcover i.val (Finset.mem_range.mp hi.1)
    have hmp : m ≤ p := by
      by_contra h
      exact hi.2 p hpP (by omega) hpi
    exact ⟨⟨p, Finset.mem_filter.mpr ⟨hpP, hmp⟩⟩, hpi⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    have hi : i.val < m := Finset.mem_range.mp (Finset.mem_filter.mp i.property).1
    have hj : j.val < m := Finset.mem_range.mp (Finset.mem_filter.mp j.property).1
    have hp : m ≤ (f i).val := (Finset.mem_filter.mp (f i).property).2
    have hjmod : j.val ≡ r (f i).val [MOD (f i).val] := by
      simpa only [hij] using hf j
    apply Subtype.ext
    exact ((hf i).trans hjmod.symm).eq_of_lt_of_lt (by omega) (by omega)
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe] using hc


/-- Distinct primes can be assigned to cover any prescribed finite interval. -/
theorem lt_jacobsthalFunction (k : ℕ) : k < jacobsthalFunction k := by
  classical
  apply Nat.lt_of_not_ge
  intro hle
  have hbound := (jacobsthalFunction_le_iff k k).mp hle
  apply ((not_isJacobsthalBound_iff_cover k k).mpr ?_) hbound
  obtain ⟨P, hP, hPk⟩ := Nat.infinite_setOf_prime.exists_subset_card_eq k
  let e : P ≃ Fin k := Finset.equivFinOfCardEq hPk
  let r : ℕ → ℕ := fun p => if hp : p ∈ P then (e ⟨p, hp⟩).val else 0
  refine ⟨P, fun p hp => hP hp, hPk.le, r, fun i hi => ?_⟩
  let p : P := e.symm ⟨i, hi⟩
  refine ⟨p.val, p.property, ?_⟩
  have hr : r p.val = i := by
    dsimp only [r]
    rw [dif_pos p.property]
    exact congrArg Fin.val (e.apply_symm_apply ⟨i, hi⟩)
  rw [hr]


/-- A fresh prime can extend any covered interval by one position. -/
theorem jacobsthalFunction_lt_succ (k : ℕ) :
    jacobsthalFunction k < jacobsthalFunction (k + 1) := by
  classical
  let m := jacobsthalFunction k
  have hm : 0 < m := jacobsthalFunction_pos k
  have hbad : ¬IsJacobsthalBound k (m - 1) := by
    intro h
    have := (jacobsthalFunction_le_iff k (m - 1)).mpr h
    change m ≤ m - 1 at this
    omega
  obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k (m - 1)).mp hbad
  obtain ⟨p, hp, hpP⟩ := Nat.infinite_setOf_prime.exists_notMem_finset P
  have hbad' : ¬IsJacobsthalBound (k + 1) m := by
    apply (not_isJacobsthalBound_iff_cover (k + 1) m).mpr
    refine ⟨insert p P, ?_, ?_, fun q => if q = p then m - 1 else r q, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hp
      · exact hP q hq
    · simp only [Finset.card_insert_of_notMem hpP]
      omega
    · intro i hi
      by_cases hi' : i < m - 1
      · obtain ⟨q, hq, hiq⟩ := hcover i hi'
        refine ⟨q, Finset.mem_insert_of_mem hq, ?_⟩
        have hqp : q ≠ p := by rintro rfl; exact hpP hq
        simpa only [if_neg hqp] using hiq
      · have hi' : i = m - 1 := by omega
        refine ⟨p, Finset.mem_insert_self p P, ?_⟩
        simp [hi', Nat.ModEq]
  apply Nat.lt_of_not_ge
  intro hle
  exact hbad' ((jacobsthalFunction_le_iff (k + 1) m).mp hle)

theorem jacobsthalFunction_strictMono : StrictMono jacobsthalFunction :=
  strictMono_nat_of_lt_succ jacobsthalFunction_lt_succ


/-- The interval from `2` through `x` is covered by the primes at most `x`. -/
theorem le_jacobsthalFunction_primeCounting (x : ℕ) (hx : 2 ≤ x) :
    x ≤ jacobsthalFunction x.primeCounting := by
  classical
  by_contra h
  have hbound : IsJacobsthalBound x.primeCounting (x - 1) :=
    (jacobsthalFunction_le_iff _ _).mp (by omega)
  have hfac : (primorial x).primeFactors = (Finset.range (x + 1)).filter Nat.Prime := by
    apply Nat.primeFactors_prod
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hcard : (primorial x).primeFactors.card ≤ x.primeCounting := by
    rw [hfac]
    simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range, le_refl]
  obtain ⟨i, hi, hc⟩ := hbound (primorial x) (primorial_pos x) hcard 2
  have hc' : (2 + i).Coprime (primorial x) := by simpa using hc
  obtain ⟨p, hp, hpi⟩ := Nat.exists_prime_and_dvd (by omega : 2 + i ≠ 1)
  have hpx : p ≤ x := (Nat.le_of_dvd (by omega) hpi).trans (by omega)
  have hpn : p ∣ primorial x := Finset.dvd_prod_of_mem id
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpi hpn hc'

/-- In particular, a uniform linear upper bound is impossible. -/
theorem not_linear_bound :
    ¬(∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C * k) := by
  rintro ⟨C, hC, hbound⟩
  have hcheb : ∀ᶠ n : ℕ in Filter.atTop,
      (n.primeCounting : ℝ) ≤ (Real.log 4 + 1) * (n : ℝ) / Real.log n := by
    have hh := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
    simpa using hh
  have hlog : ∀ᶠ n : ℕ in Filter.atTop,
      C * (Real.log 4 + 1) < Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_gt_atTop _)
  obtain ⟨n, hnCheb, hnlog, hn2⟩ :=
    (hcheb.and (hlog.and (Filter.eventually_ge_atTop (2 : ℕ)))).exists
  have hk : 0 < n.primeCounting := by
    by_contra h
    have := Nat.primeCounting_eq_zero_iff.mp (show n.primeCounting = 0 by omega)
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hineq : (n : ℝ) ≤ C * ((Real.log 4 + 1) * (n : ℝ) / Real.log n) := by
    calc
      (n : ℝ) ≤ (jacobsthalFunction n.primeCounting : ℝ) := by
        exact_mod_cast le_jacobsthalFunction_primeCounting n hn2
      _ ≤ C * n.primeCounting := hbound n.primeCounting hk
      _ ≤ C * ((Real.log 4 + 1) * (n : ℝ) / Real.log n) :=
        mul_le_mul_of_nonneg_left hnCheb hC.le
  rw [← mul_div_assoc] at hineq
  have hmul := (le_div_iff₀ hlogpos).mp hineq
  have hstrict := mul_lt_mul_of_pos_left hnlog hnpos
  nlinarith


/-- A quantitative lower bound: `h(k)` is eventually at least a constant times `k log k`. -/
theorem eventually_mul_log_le_jacobsthalFunction :
    ∀ᶠ k : ℕ in Filter.atTop,
      (k : ℝ) * Real.log k ≤ (Real.log 4 + 1) * (jacobsthalFunction k : ℝ) := by
  have hnth : Filter.Tendsto (Nat.nth Nat.Prime) Filter.atTop Filter.atTop :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime).tendsto_atTop
  have hcheb : ∀ᶠ k : ℕ in Filter.atTop,
      ((Nat.nth Nat.Prime k).primeCounting : ℝ) ≤
        (Real.log 4 + 1) * (Nat.nth Nat.Prime k : ℝ) / Real.log (Nat.nth Nat.Prime k) := by
    have hh := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hnth).eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
    simpa using hh
  have hsucc : ∀ᶠ k : ℕ in Filter.atTop,
      ((k + 1 : ℕ) : ℝ) * Real.log (k + 1 : ℕ) ≤
        (Real.log 4 + 1) * (jacobsthalFunction (k + 1) : ℝ) := by
    filter_upwards [hcheb] with k hk
    have hcount : (Nat.nth Nat.Prime k).primeCounting = k + 1 := by
      rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
      simp only [Nat.prime_nth_prime, if_true]
      exact congrArg (fun n : ℕ => n + 1) (Nat.primeCounting'_nth_eq k)
    have hkp : k + 1 ≤ Nat.nth Nat.Prime k :=
      (by omega : k + 1 ≤ k + 2).trans (Nat.add_two_le_nth_prime k)
    have hp2 := (Nat.prime_nth_prime k).two_le
    have hlogpos : 0 < Real.log (Nat.nth Nat.Prime k : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < Nat.nth Nat.Prime k))
    have hlogle : Real.log ((k + 1 : ℕ) : ℝ) ≤ Real.log (Nat.nth Nat.Prime k : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hkp)
    have hlow : Nat.nth Nat.Prime k ≤ jacobsthalFunction (k + 1) := by
      simpa only [hcount] using le_jacobsthalFunction_primeCounting (Nat.nth Nat.Prime k) hp2
    have hA : 0 ≤ Real.log 4 + 1 := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      linarith
    rw [hcount] at hk
    calc
      ((k + 1 : ℕ) : ℝ) * Real.log (k + 1 : ℕ) ≤
          ((k + 1 : ℕ) : ℝ) * Real.log (Nat.nth Nat.Prime k) :=
        mul_le_mul_of_nonneg_left hlogle (by positivity)
      _ ≤ (Real.log 4 + 1) * (Nat.nth Nat.Prime k : ℝ) := (le_div_iff₀ hlogpos).mp hk
      _ ≤ (Real.log 4 + 1) * (jacobsthalFunction (k + 1) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hlow) hA
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hsucc
  apply Filter.eventually_atTop.mpr
  refine ⟨K + 1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact hK j (by omega)


/-- Any finite set of remaining positions can be covered with one fresh prime per position. -/
theorem extend_cover_by_fresh_primes (m : ℕ) (S : Finset ℕ) :
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ r : ℕ → ℕ,
      (∀ i : ℕ, i < m → i ∉ S → ∃ p ∈ P, i ≡ r p [MOD p]) →
      ∃ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) ∧ Q.card ≤ P.card + S.card ∧
        ∃ s : ℕ → ℕ, ∀ i : ℕ, i < m → ∃ p ∈ Q, i ≡ s p [MOD p] := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro P hP r hcover
    exact ⟨P, hP, by simp, r, fun i hi => hcover i hi (by simp)⟩
  | @insert a S ha ih =>
    intro P hP r hcover
    obtain ⟨p, hp, hpP⟩ := Nat.infinite_setOf_prime.exists_notMem_finset P
    let r' : ℕ → ℕ := fun q => if q = p then a else r q
    have hP' : ∀ q ∈ insert p P, q.Prime := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hp
      · exact hP q hq
    have hcover' : ∀ i : ℕ, i < m → i ∉ S →
        ∃ q ∈ insert p P, i ≡ r' q [MOD q] := by
      intro i hi hiS
      by_cases hia : i = a
      · refine ⟨p, Finset.mem_insert_self p P, ?_⟩
        simp [r', hia, Nat.ModEq]
      · obtain ⟨q, hq, hiq⟩ := hcover i hi (by simp [hia, hiS])
        refine ⟨q, Finset.mem_insert_of_mem hq, ?_⟩
        have hqp : q ≠ p := by rintro rfl; exact hpP hq
        simpa only [r', if_neg hqp] using hiq
    obtain ⟨Q, hQ, hcard, s, hs⟩ := ih (insert p P) hP' r' hcover'
    refine ⟨Q, hQ, ?_, s, hs⟩
    simp only [Finset.card_insert_of_notMem hpP] at hcard
    simp only [Finset.card_insert_of_notMem ha]
    omega

/-- Exact finite reduction: small prime classes plus one prime per uncovered position. -/
theorem isJacobsthalBound_iff_small_prime_budget (k m : ℕ) :
    IsJacobsthalBound k m ↔
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p < m) → ∀ r : ℕ → ℕ,
      k < P.card + ((Finset.range m).filter
        (fun i => ∀ p ∈ P, ¬i ≡ r p [MOD p])).card := by
  classical
  constructor
  · intro hbound P hP r
    by_contra hbudget
    let S := (Finset.range m).filter (fun i => ∀ p ∈ P, ¬i ≡ r p [MOD p])
    have hpartial : ∀ i : ℕ, i < m → i ∉ S → ∃ p ∈ P, i ≡ r p [MOD p] := by
      intro i hi hiS
      have hh : ¬∀ p ∈ P, ¬i ≡ r p [MOD p] := by
        intro hh
        exact hiS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hh⟩)
      push_neg at hh
      exact hh
    obtain ⟨Q, hQ, hQcard, s, hs⟩ :=
      extend_cover_by_fresh_primes m S P (fun p hp => (hP p hp).1) r hpartial
    apply ((not_isJacobsthalBound_iff_cover k m).mpr ?_) hbound
    refine ⟨Q, hQ, ?_, s, hs⟩
    dsimp only [S] at hQcard
    omega
  · intro hbudget
    by_contra hbad
    obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
    let A := P.filter (fun p => p < m)
    have hA : ∀ p ∈ A, p.Prime ∧ p < m := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact ⟨hP p hp'.1, hp'.2⟩
    have hc := hbudget A hA r
    have heq : ((Finset.range m).filter (fun i => ∀ p ∈ A, ¬i ≡ r p [MOD p])) =
        ((Finset.range m).filter (fun i => ∀ p ∈ P, p < m → ¬i ≡ r p [MOD p])) := by
      apply Finset.filter_congr
      intro i hi
      simp only [A, Finset.mem_filter, and_imp]
    rw [heq] at hc
    have hlarge := cover_large_prime_budget P r m hcover
    have hcards : A.card + (P.filter (fun p => m ≤ p)).card = P.card := by
      simpa only [A, not_lt] using
        (Finset.card_filter_add_card_filter_not (s := P) (fun p => p < m))
    omega



/-- Every disjoint block of length `g` contains a position surviving the given small primes. -/
theorem survivor_card_lower (P : Finset ℕ) (r : ℕ → ℕ) (m s g : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPs : P.card ≤ s)
    (hbound : IsJacobsthalBound s g) :
    m / g ≤ ((Finset.range m).filter
      (fun i => ∀ p ∈ P, ¬i ≡ r p [MOD p])).card := by
  classical
  let n := ∏ p ∈ P, p
  have hn : 0 < n := Finset.prod_pos (fun p hp => (hP p hp).pos)
  have hnk : n.primeFactors.card ≤ s := by
    simpa only [n, Nat.primeFactors_prod hP] using hPs
  have hco : Set.Pairwise (↑P : Set ℕ) Nat.Coprime :=
    fun p hp q hq hpq => (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  let b := Nat.chineseRemainderOfFinset r id P (fun p hp => (hP p hp).ne_zero) hco
  let S := (Finset.range m).filter (fun i => ∀ p ∈ P, ¬i ≡ r p [MOD p])
  have hex (j : Fin (m / g)) : ∃ i : S, j.val * g ≤ i.val ∧ i.val < (j.val + 1) * g := by
    obtain ⟨i, hi, hc⟩ := hbound n hn hnk ((j.val * g : ℕ) - (b.val : ℤ))
    have hib : j.val * g + i < (j.val + 1) * g := by nlinarith
    have him : j.val * g + i < m := by
      have hj := j.isLt
      have hh := Nat.div_mul_le_self m g
      have hh' : (j.val + 1) * g ≤ m / g * g := Nat.mul_le_mul_right g (by omega)
      omega
    have hsurv (p : ℕ) (hp : p ∈ P) : ¬j.val * g + i ≡ r p [MOD p] := by
      intro heq
      have hbpi : b.val ≡ j.val * g + i [MOD p] := (b.property p hp).trans heq.symm
      have hd : (p : ℤ) ∣ ((j.val * g : ℕ) : ℤ) - (b.val : ℤ) + i := by
        convert hbpi.dvd using 1; push_cast; ring
      exact Nat.not_coprime_of_dvd_of_dvd (hP p hp).one_lt
        (Int.natCast_dvd.mp hd) (Finset.dvd_prod_of_mem id hp) hc
    refine ⟨⟨j.val * g + i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr him, hsurv⟩⟩, ?_, hib⟩
    exact Nat.le_add_right _ _
  choose f hf using hex
  have hfi : Function.Injective f := by
    intro j k heq
    have hj := hf j
    have hk := hf k
    have hval : (f j).val = (f k).val := congrArg Subtype.val heq
    have hle : j.val ≤ k.val := by
      by_contra h
      have hg : (k.val + 1) * g ≤ j.val * g := Nat.mul_le_mul_right g (by omega)
      omega
    have hge : k.val ≤ j.val := by
      by_contra h
      have hg : (j.val + 1) * g ≤ k.val * g := Nat.mul_le_mul_right g (by omega)
      omega
    exact Fin.ext (by omega)
  have hh := Fintype.card_le_of_injective f hfi
  simpa only [Fintype.card_fin, Fintype.card_coe] using hh

/-- An individual residue class has at most `m / p + 1` representatives below `m`. -/
theorem residue_class_card_le (p r m : ℕ) :
    ((Finset.range m).filter (fun i => i ≡ r [MOD p])).card ≤ m / p + 1 := by
  classical
  have hh := Finset.card_le_card_of_injOn (s := (Finset.range m).filter
    (fun i => i ≡ r [MOD p])) (t := Finset.range (m / p + 1)) (fun i => i / p) ?_ ?_
  · simpa only [Finset.card_range] using hh
  · intro i hi
    have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hi'.le))
  · intro i hi j hj hij
    change i ∈ (Finset.range m).filter (fun i => i ≡ r [MOD p]) at hi
    change j ∈ (Finset.range m).filter (fun i => i ≡ r [MOD p]) at hj
    have himod : i ≡ r [MOD p] := (Finset.mem_filter.mp hi).2
    have hjmod : j ≡ r [MOD p] := (Finset.mem_filter.mp hj).2
    have hm : i % p = j % p := himod.trans hjmod.symm
    change i / p = j / p at hij
    have hi' := Nat.div_add_mod i p
    have hj' := Nat.div_add_mod j p
    rw [hij, hm] at hi'
    omega

/-- The remaining primes must supply all the survivors of any chosen smaller set. -/
theorem cover_bootstrap_necessary (P A : Finset ℕ) (r : ℕ → ℕ) (m s g : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hAP : A ⊆ P) (hAs : A.card ≤ s)
    (hbound : IsJacobsthalBound s g)
    (hcover : ∀ i : ℕ, i < m → ∃ p ∈ P, i ≡ r p [MOD p]) :
    m / g ≤ ∑ p ∈ P \ A, (m / p + 1) := by
  classical
  let S := (Finset.range m).filter (fun i => ∀ p ∈ A, ¬i ≡ r p [MOD p])
  let T := (P \ A).biUnion (fun p => (Finset.range m).filter (fun i => i ≡ r p [MOD p]))
  have hST : S ⊆ T := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨p, hp, hip⟩ := hcover i (Finset.mem_range.mp hi'.1)
    have hpA : p ∉ A := fun ha => hi'.2 p ha hip
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpA⟩,
      Finset.mem_filter.mpr ⟨hi'.1, hip⟩⟩
  calc
    m / g ≤ S.card := survivor_card_lower A r m s g (fun p hp => hP p (hAP hp)) hAs hbound
    _ ≤ T.card := Finset.card_le_card hST
    _ ≤ ∑ p ∈ P \ A, ((Finset.range m).filter (fun i => i ≡ r p [MOD p])).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p ∈ P \ A, (m / p + 1) :=
      Finset.sum_le_sum (fun p hp => residue_class_card_le p (r p) m)


/-- This counting test is automatic whenever an unremoved prime is at most the block bound. -/
theorem bootstrap_inequality_automatic (P A : Finset ℕ) (m g p : ℕ)
    (hpP : p ∈ P \ A) (hp : 0 < p) (hpg : p ≤ g) :
    m / g ≤ ∑ q ∈ P \ A, (m / q + 1) := by
  classical
  calc
    m / g ≤ m / p := Nat.div_le_div_left hpg hp
    _ ≤ m / p + 1 := Nat.le_succ _
    _ ≤ ∑ q ∈ P \ A, (m / q + 1) :=
      Finset.single_le_sum (f := fun q => m / q + 1) (fun q hq => Nat.zero_le _) hpP

/-- In particular, retaining more than `s` primes below `g` makes every size-`s` test automatic. -/
theorem bootstrap_inequality_automatic_of_card (P A : Finset ℕ) (m s g : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hAs : A.card ≤ s)
    (hsmall : s < (P.filter (fun p => p ≤ g)).card) :
    m / g ≤ ∑ q ∈ P \ A, (m / q + 1) := by
  classical
  obtain ⟨p, hp, hpA⟩ := Finset.exists_mem_notMem_of_card_lt_card (hAs.trans_lt hsmall)
  have hp' := Finset.mem_filter.mp hp
  exact bootstrap_inequality_automatic P A m g p
    (Finset.mem_sdiff.mpr ⟨hp'.1, hpA⟩) (hP p hp'.1).pos hp'.2

#print axioms survivor_card_lower
#print axioms cover_bootstrap_necessary
#print axioms bootstrap_inequality_automatic_of_card
end Erdos970
