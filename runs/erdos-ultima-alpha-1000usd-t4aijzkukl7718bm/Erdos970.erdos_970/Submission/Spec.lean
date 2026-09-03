import FormalConjecturesUtil

/-!
# Erdős Problem 970

*Reference:* [erdosproblems.com/970](https://www.erdosproblems.com/970)
-/

namespace Erdos970

/--
`IsJacobsthalBound k m` says that every interval of `m` consecutive integers contains an
integer coprime to every positive natural number having at most `k` distinct prime factors.
-/
def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

/--
Jacobsthal's function, uniformly parametrized by the maximum number of distinct prime factors.
-/
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


/-- A sum of `s.card` geometric sequences is determined by that many initial terms. -/
theorem exponential_sum_zero_of_initial {ι R : Type*} [CommRing R]
    (s : Finset ι) (c z : ι → R)
    (hzero : ∀ n : ℕ, n < s.card → ∑ i ∈ s, c i * z i ^ n = 0) :
    ∀ n : ℕ, ∑ i ∈ s, c i * z i ^ n = 0 := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => simp
  | @insert a s ha ih =>
    let F : ℕ → R := fun n => ∑ i ∈ insert a s, c i * z i ^ n
    have hdiff (n : ℕ) :
        (∑ i ∈ s, (c i * (z i - z a)) * z i ^ n) = F (n + 1) - z a * F n := by
      calc
        (∑ i ∈ s, (c i * (z i - z a)) * z i ^ n) =
            ∑ i ∈ s, (c i * z i ^ (n + 1) - z a * (c i * z i ^ n)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ]
          ring
        _ = F (n + 1) - z a * F n := by
          simp only [F, Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_insert ha, pow_succ]
          ring
    have hsmall (n : ℕ) (hn : n < s.card) :
        (∑ i ∈ s, (c i * (z i - z a)) * z i ^ n) = 0 := by
      rw [hdiff]
      have h0 : F n = 0 := hzero n (by simp only [Finset.card_insert_of_notMem ha]; omega)
      have h1 : F (n + 1) = 0 := hzero (n + 1)
        (by simp only [Finset.card_insert_of_notMem ha]; omega)
      rw [h0, h1]
      ring
    have hall := ih (fun i => c i * (z i - z a)) hsmall
    intro n
    change F n = 0
    induction n with
    | zero => exact hzero 0 (by simp only [Finset.card_insert_of_notMem ha]; omega)
    | succ n hn =>
      have hh := hall n
      rw [hdiff, hn, mul_zero, sub_zero] at hh
      exact hh

/-- A product of `k` binomial exponential factors cannot have `2^k` initial zeros
unless it vanishes at every natural index. -/
theorem product_pow_sub_zero_of_initial {ι R : Type*} [CommRing R]
    (s : Finset ι) (z c : ι → R)
    (hzero : ∀ n : ℕ, n < 2 ^ s.card → ∏ i ∈ s, (z i ^ n - c i) = 0) :
    ∀ n : ℕ, ∏ i ∈ s, (z i ^ n - c i) = 0 := by
  classical
  let coeff : Finset ι → R := fun t => (-1) ^ t.card * ∏ i ∈ t, c i
  let base : Finset ι → R := fun t => ∏ i ∈ s \ t, z i
  have hexpand (n : ℕ) :
      (∏ i ∈ s, (z i ^ n - c i)) = ∑ t ∈ s.powerset, coeff t * base t ^ n := by
    rw [Finset.prod_sub]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [coeff, base, Finset.prod_pow]
    ring
  have hz : ∀ n : ℕ, n < s.powerset.card →
      ∑ t ∈ s.powerset, coeff t * base t ^ n = 0 := by
    intro n hn
    rw [← hexpand]
    exact hzero n (by simpa only [Finset.card_powerset] using hn)
  have hh := exponential_sum_zero_of_initial s.powerset coeff base hz
  intro n
  rw [hexpand]
  exact hh n

/-- Kanold's global exponential bound for the uniform Jacobsthal function. -/
theorem isJacobsthalBound_two_pow (k : ℕ) : IsJacobsthalBound k (2 ^ k) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k (2 ^ k)).mp hbad
  let z : ℕ → ℂ := fun p => Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))
  have hz (p : ℕ) (hp : p ∈ P) : IsPrimitiveRoot (z p) p :=
    Complex.isPrimitiveRoot_exp p (hP p hp).ne_zero
  have heq (p : ℕ) (hp : p ∈ P) (i j : ℕ) :
      z p ^ i = z p ^ j ↔ i ≡ j [MOD p] := by
    have hfin : IsOfFinOrder (z p) :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨p, (hP p hp).pos, (hz p hp).pow_eq_one⟩
    simpa only [← (hz p hp).eq_orderOf] using
      (hfin.pow_eq_pow_iff_modEq (n := i) (m := j))
  have hinit (i : ℕ) (hi : i < 2 ^ P.card) :
      (∏ p ∈ P, (z p ^ i - z p ^ r p)) = 0 := by
    obtain ⟨p, hp, hip⟩ := hcover i (hi.trans_le (Nat.pow_le_pow_right (by decide) hPk))
    exact Finset.prod_eq_zero_iff.mpr ⟨p, hp, sub_eq_zero.mpr ((heq p hp i (r p)).mpr hip)⟩
  have hall := product_pow_sub_zero_of_initial P z (fun p => z p ^ r p) hinit
  have hcoverall (i : ℕ) : ∃ p ∈ P, i ≡ r p [MOD p] := by
    obtain ⟨p, hp, hzero⟩ := Finset.prod_eq_zero_iff.mp (hall i)
    exact ⟨p, hp, (heq p hp i (r p)).mp (sub_eq_zero.mp hzero)⟩
  exact ((not_isJacobsthalBound_iff_cover k (k + 1).factorial).mpr
    ⟨P, hP, hPk, r, fun i hi => hcoverall i⟩) (isJacobsthalBound_factorial k)

theorem jacobsthalFunction_le_two_pow (k : ℕ) : jacobsthalFunction k ≤ 2 ^ k :=
  (jacobsthalFunction_le_iff k (2 ^ k)).mpr (isJacobsthalBound_two_pow k)



/-
Truncated inclusion–exclusion for uniform prime-residue covers.
This file develops finite upper-bound criteria; it does not assert the quadratic conjecture.
-/
open scoped Function

namespace BrunCriterion

noncomputable def truncSets (P : Finset ℕ) (t : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun Q => Q.card ≤ t)

noncomputable def truncDensity (P : Finset ℕ) (t : ℕ) : ℝ :=
  ∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card / (∏ p ∈ Q, (p : ℝ))

theorem signed_trunc_eq (P : Finset ℕ) (t : ℕ) :
    (∑ Q ∈ truncSets P t, (-1 : ℤ) ^ Q.card) =
      ∑ j ∈ Finset.range (t + 1), (-1 : ℤ) ^ j * P.card.choose j := by
  classical
  have hmap : ∀ Q ∈ truncSets P t, Q.card ∈ Finset.range (t + 1) := by
    intro Q hQ
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hQ).2; omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro j hj
  have heq : (truncSets P t).filter (fun Q => Q.card = j) = P.powersetCard j := by
    ext Q
    simp only [truncSets, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    have hjt := Finset.mem_range.mp hj
    constructor
    · rintro ⟨⟨hQP, hqt⟩, hcard⟩
      exact ⟨hQP, hcard⟩
    · rintro ⟨hQP, hcard⟩
      exact ⟨⟨hQP, by omega⟩, hcard⟩
  rw [heq, Finset.sum_powersetCard]
  simp [mul_comm]

theorem signed_trunc_nonpos {P : Finset ℕ} {t : ℕ}
    (hP : P.Nonempty) (ht : Odd t) : (∑ Q ∈ truncSets P t, (-1 : ℤ) ^ Q.card) ≤ 0 := by
  rw [signed_trunc_eq]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr hP).ne'
  rw [hn, Int.alternating_sum_range_choose_eq_choose, ht.neg_one_pow]
  simp

/-- A covered interval makes every odd Bonferroni truncation nonpositive. -/
theorem cover_truncated_count_nonpos (P : Finset ℕ) (r : ℕ → ℕ) (m t : ℕ)
    (ht : Odd t) (hcover : ∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) :
    (∑ Q ∈ truncSets P t, (-1 : ℤ) ^ Q.card *
      ((Finset.range m).filter (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card) ≤ 0 := by
  classical
  have hpoint (i : ℕ) (hi : i ∈ Finset.range m) :
      (∑ Q ∈ truncSets P t, if (∀ p ∈ Q, i ≡ r p [MOD p]) then (-1 : ℤ) ^ Q.card else 0) ≤ 0 := by
    let B := P.filter (fun p => i ≡ r p [MOD p])
    have hB : B.Nonempty := by
      obtain ⟨p, hp, hip⟩ := hcover i (Finset.mem_range.mp hi)
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hip⟩⟩
    have heq : (truncSets P t).filter (fun Q => ∀ p ∈ Q, i ≡ r p [MOD p]) = truncSets B t := by
      ext Q
      simp only [truncSets, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, B]
      aesop
    rw [← Finset.sum_filter, heq]
    exact signed_trunc_nonpos hB ht
  have heq (Q : Finset ℕ) :
      (-1 : ℤ) ^ Q.card * ((Finset.range m).filter (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card =
        ∑ i ∈ Finset.range m, if (∀ p ∈ Q, i ≡ r p [MOD p]) then (-1 : ℤ) ^ Q.card else 0 := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  simp_rw [heq]
  rw [Finset.sum_comm]
  exact Finset.sum_nonpos hpoint

/-- Counting a single residue class differs from interval length divided by the modulus by at most one. -/
theorem residue_count_error (m d r : ℕ) (hd : 0 < d) :
    |(((Finset.range m).filter (fun i => i ≡ r [MOD d])).card : ℝ) - (m : ℝ) / d| ≤ 1 := by
  classical
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card m hd r]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdiv : ((m / d : ℕ) : ℝ) * d ≤ m := by exact_mod_cast Nat.div_mul_le_self m d
  have hdiv' : (m : ℝ) < (((m / d : ℕ) : ℝ) + 1) * d := by
    exact_mod_cast (show m < (m / d + 1) * d by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ m hd)
  have hlo := (le_div_iff₀ hdR).mpr hdiv
  have hhi := (div_lt_iff₀ hdR).mpr hdiv'
  rw [abs_le]
  split_ifs <;> push_cast <;> constructor <;> linarith

/-- Intersections of prime classes are a single residue class modulo the prime product. -/
theorem intersection_residue (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (r : ℕ → ℕ) :
    ∃ b : ℕ, ∀ i : ℕ, (∀ p ∈ Q, i ≡ r p [MOD p]) ↔ i ≡ b [MOD ∏ p ∈ Q, p] := by
  classical
  have hco : Set.Pairwise (↑Q : Set ℕ) Nat.Coprime :=
    fun p hp q hq hpq => (Nat.coprime_primes (hQ p hp) (hQ q hq)).mpr hpq
  let b := Nat.chineseRemainderOfFinset r id Q (fun p hp => (hQ p hp).ne_zero) hco
  refine ⟨b.val, fun i => ?_⟩
  have hlist : Q.toList.Pairwise (Nat.Coprime on id) :=
    Q.nodup_toList.pairwise_of_forall_ne (by simpa using hco)
  have heq : i ≡ b.val [MOD ∏ p ∈ Q, p] ↔ ∀ p ∈ Q, i ≡ b.val [MOD p] := by
    simpa using (Nat.modEq_list_map_prod_iff (a := i) (b := b.val) hlist)
  rw [heq]
  constructor
  · intro hi p hp
    exact (hi p hp).trans (b.property p hp).symm
  · intro hi p hp
    exact (hi p hp).trans (b.property p hp)

theorem intersection_count_error (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (r : ℕ → ℕ) (m : ℕ) :
    |(((Finset.range m).filter (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card : ℝ) -
      (m : ℝ) / (∏ p ∈ Q, (p : ℝ))| ≤ 1 := by
  classical
  obtain ⟨b, hb⟩ := intersection_residue Q hQ r
  simp_rw [hb]
  rw [← Nat.cast_prod]
  exact residue_count_error m _ b (Finset.prod_pos (fun p hp => (hQ p hp).pos))

/-- Every cover satisfies the truncated-sieve upper bound on its length. -/
theorem cover_density_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ) (m t : ℕ)
    (ht : Odd t) (hcover : ∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) :
    (m : ℝ) * truncDensity P t ≤ (truncSets P t).card := by
  classical
  let C (Q : Finset ℕ) := ((Finset.range m).filter (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card
  have hsum : (∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card * C Q) ≤ 0 := by
    exact_mod_cast cover_truncated_count_nonpos P r m t ht hcover
  have hterm (Q : Finset ℕ) (hQ : Q ∈ truncSets P t) :
      (m : ℝ) * ((-1 : ℝ) ^ Q.card / (∏ p ∈ Q, (p : ℝ))) ≤
        (-1 : ℝ) ^ Q.card * C Q + 1 := by
    have hQP := Finset.mem_powerset.mp (Finset.mem_filter.mp hQ).1
    have hh := intersection_count_error Q (fun p hp => hP p (hQP hp)) r m
    change |(C Q : ℝ) - _| ≤ 1 at hh
    have hh' : |(-1 : ℝ) ^ Q.card * ((C Q : ℝ) - (m : ℝ) / (∏ p ∈ Q, (p : ℝ)))| ≤ 1 := by
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hh
    have hlo := (abs_le.mp hh').1
    simp only [div_eq_mul_inv] at hlo ⊢
    nlinarith only [hlo]
  calc
    (m : ℝ) * truncDensity P t = ∑ Q ∈ truncSets P t,
        (m : ℝ) * ((-1 : ℝ) ^ Q.card / (∏ p ∈ Q, (p : ℝ))) := Finset.mul_sum ..
    _ ≤ ∑ Q ∈ truncSets P t, ((-1 : ℝ) ^ Q.card * C Q + 1) := Finset.sum_le_sum hterm
    _ = (∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card * C Q) + (truncSets P t).card := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := by linarith

/-- A simple polynomial bound on the number of retained subsets. -/
theorem truncSets_card_le (P : Finset ℕ) (t : ℕ) :
    (truncSets P t).card ≤ (P.card + 1) ^ t := by
  classical
  have heq : (truncSets P t).card = ∑ j ∈ Finset.range (t + 1), P.card.choose j := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range (t + 1))
      (fun Q hQ => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hQ).2; omega))]
    apply Finset.sum_congr rfl
    intro j hj
    have he : (truncSets P t).filter (fun Q => Q.card = j) = P.powersetCard j := by
      ext Q
      simp only [truncSets, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      have hjt := Finset.mem_range.mp hj
      constructor
      · rintro ⟨⟨hQP, hqt⟩, hcard⟩
        exact ⟨hQP, hcard⟩
      · rintro ⟨hQP, hcard⟩
        exact ⟨⟨hQP, by omega⟩, hcard⟩
    rw [he, Finset.card_powersetCard]
  rw [heq, add_pow]
  apply Finset.sum_le_sum
  intro j hj
  have hjt : j ≤ t := by simpa using hj
  have hchoose : 1 ≤ t.choose j := Nat.choose_pos hjt
  simpa only [one_pow, mul_one] using
    (Nat.choose_le_pow P.card j).trans (Nat.le_mul_of_pos_right _ hchoose)

/-- The discarded tail is bounded by evaluating the subset generating function at `2`. -/
theorem trunc_value_lower (P : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) (t : ℕ) :
    (∏ p ∈ P, (1 - w p)) - (∏ p ∈ P, (1 + 2 * w p)) / (2 : ℝ) ^ (t + 1) ≤
      ∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, w p := by
  classical
  let A := truncSets P t
  let U := P.powerset
  let f (Q : Finset ℕ) := (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, w p
  let v (Q : Finset ℕ) := ∏ p ∈ Q, 2 * w p
  have hAU : A ⊆ U := Finset.filter_subset _ _
  have hfull : (∏ p ∈ P, (1 - w p)) = ∑ Q ∈ U, f Q := by
    simpa only [Finset.prod_const_one, mul_one] using Finset.prod_sub (fun _ => (1 : ℝ)) w P
  have hgen : (∏ p ∈ P, (1 + 2 * w p)) = ∑ Q ∈ U, v Q := Finset.prod_one_add P
  have hnonneg (Q : Finset ℕ) (hQ : Q ∈ U) : 0 ≤ ∏ p ∈ Q, w p :=
    Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp hQ hp))
  have hvnonneg (Q : Finset ℕ) (hQ : Q ∈ U) : 0 ≤ v Q :=
    Finset.prod_nonneg (fun p hp => mul_nonneg (by norm_num) (hw p (Finset.mem_powerset.mp hQ hp)))
  have hterm (Q : Finset ℕ) (hQ : Q ∈ U \ A) : (2 : ℝ) ^ (t + 1) * f Q ≤ v Q := by
    obtain ⟨hQU, hQA⟩ := Finset.mem_sdiff.mp hQ
    have htQ : t + 1 ≤ Q.card := by
      have hnot : ¬Q.card ≤ t := fun hh => hQA (Finset.mem_filter.mpr ⟨hQU, hh⟩)
      omega
    have hsign : (-1 : ℝ) ^ Q.card ≤ 1 := by
      simpa only [abs_pow, abs_neg, abs_one, one_pow] using le_abs_self ((-1 : ℝ) ^ Q.card)
    have hf : f Q ≤ ∏ p ∈ Q, w p := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsign (hnonneg Q hQU)
    have hpow : (2 : ℝ) ^ (t + 1) ≤ 2 ^ Q.card := pow_le_pow_right₀ (by norm_num) htQ
    calc
      (2 : ℝ) ^ (t + 1) * f Q ≤ 2 ^ (t + 1) * (∏ p ∈ Q, w p) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ ≤ 2 ^ Q.card * (∏ p ∈ Q, w p) := mul_le_mul_of_nonneg_right hpow (hnonneg Q hQU)
      _ = v Q := by simp only [v, Finset.prod_mul_distrib, Finset.prod_const]
  have hsum : (2 : ℝ) ^ (t + 1) * (∑ Q ∈ U \ A, f Q) ≤ ∏ p ∈ P, (1 + 2 * w p) := by
    rw [Finset.mul_sum, hgen]
    exact (Finset.sum_le_sum hterm).trans
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun Q hQ _ => hvnonneg Q hQ))
  have htail := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (t + 1))).mpr
    (show (∑ Q ∈ U \ A, f Q) * 2 ^ (t + 1) ≤ ∏ p ∈ P, (1 + 2 * w p) by nlinarith only [hsum])
  have hsplit := Finset.sum_sdiff hAU (f := f)
  rw [hfull]
  change _ ≤ ∑ Q ∈ A, f Q
  linarith

/-- Distinct primes give elementary bounds for the density and its generating function. -/
theorem prime_product_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (1 / ((P.card : ℝ) + 1) ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ))) ∧
    (∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))) ≤ ((P.card : ℝ) + 1) ^ 2 := by
  classical
  induction P using Finset.induction_on_max with
  | h0 => norm_num
  | @step p P hlt ih =>
    have hp : p.Prime := hP p (Finset.mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hpP : p ∉ P := fun hh => (hlt p hh).false
    have hsub : P ⊆ Finset.Ico 2 p := fun q hq => Finset.mem_Ico.mpr ⟨(hP' q hq).two_le, hlt q hq⟩
    have hcard : P.card + 2 ≤ p := by
      have hh := Finset.card_le_card hsub
      simp only [Nat.card_Ico] at hh
      have := hp.two_le
      omega
    have hpR : (P.card : ℝ) + 2 ≤ p := by exact_mod_cast hcard
    have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hkpos : 0 < (P.card : ℝ) + 1 := by positivity
    have hkpos2 : 0 < (P.card : ℝ) + 2 := by positivity
    have hinv := one_div_le_one_div_of_le hkpos2 hpR
    have hinv' := one_div_le_one_div_of_le hkpos (show (P.card : ℝ) + 1 ≤ p by linarith)
    have hfac : 0 ≤ 1 - 1 / (p : ℝ) := by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
      have hh := (div_le_one hpRpos).mpr hp1
      linarith
    obtain ⟨hden, hgen⟩ := ih hP'
    rw [Finset.card_insert_of_notMem hpP, Nat.cast_add, Nat.cast_one]
    simp only [Finset.prod_insert hpP]
    constructor
    · have heq : (1 - 1 / ((P.card : ℝ) + 2)) * (1 / ((P.card : ℝ) + 1)) =
          1 / ((P.card : ℝ) + 2) := by field_simp; ring
      have hh : 1 / ((P.card : ℝ) + 2) ≤
          (1 - 1 / (p : ℝ)) * (1 / ((P.card : ℝ) + 1)) := by
        rw [← heq]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      convert hh.trans (mul_le_mul_of_nonneg_left hden hfac) using 1 <;> congr 1 <;> ring
    · have heq : (1 + 2 * (1 / ((P.card : ℝ) + 1))) * ((P.card : ℝ) + 1) ^ 2 =
          ((P.card : ℝ) + 2) ^ 2 - 1 := by field_simp; ring
      calc
        _ ≤ (1 + 2 * (1 / (p : ℝ))) * ((P.card : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hgen (by positivity)
        _ ≤ (1 + 2 * (1 / ((P.card : ℝ) + 1))) * ((P.card : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        _ = ((P.card : ℝ) + 2) ^ 2 - 1 := heq
        _ ≤ _ := by nlinarith

/-- A fully explicit finite upper bound from an odd truncation of sufficiently high order. -/
theorem isJacobsthalBound_of_trunc_order (k t : ℕ) (ht : Odd t)
    (hpow : 2 * (k + 1) ^ 3 ≤ 2 ^ (t + 1)) :
    IsJacobsthalBound k (4 * (k + 1) ^ (t + 1)) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k (4 * (k + 1) ^ (t + 1))).mp hbad
  let K : ℝ := (k : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hPkR : (P.card : ℝ) + 1 ≤ K := by
    dsimp only [K]
    exact_mod_cast Nat.add_le_add_right hPk 1
  obtain ⟨hden, hgen⟩ := prime_product_bounds P hP
  have hden' : 1 / K ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ)) :=
    (one_div_le_one_div_of_le (by positivity) hPkR).trans hden
  have hgen' : (∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))) ≤ K ^ 2 :=
    hgen.trans (pow_le_pow_left₀ (by positivity) hPkR _)
  have hpowR : 2 * K ^ 3 ≤ (2 : ℝ) ^ (t + 1) := by
    dsimp only [K]
    exact_mod_cast hpow
  have herr : K ^ 2 / (2 : ℝ) ^ (t + 1) ≤ 1 / (2 * K) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hpowR]
  have htail := trunc_value_lower P (fun p => 1 / (p : ℝ)) (fun p hp => by positivity) t
  have heq : (∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, (1 / (p : ℝ))) =
      truncDensity P t := by
    simp only [truncDensity, div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]
  rw [heq] at htail
  have hgen'' := (div_le_div_of_nonneg_right hgen' (by positivity : (0 : ℝ) ≤ 2 ^ (t + 1))).trans herr
  have hinv : 1 / K = 2 * (1 / (2 * K)) := by field_simp
  have hdensity : 1 / (2 * K) ≤ truncDensity P t := by linarith
  have hc := cover_density_le P hP r (4 * (k + 1) ^ (t + 1)) t ht hcover
  have hcardR : ((truncSets P t).card : ℝ) ≤ K ^ t := by
    have hh : (truncSets P t).card ≤ (k + 1) ^ t :=
      (truncSets_card_le P t).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hPk 1) t)
    dsimp only [K]
    exact_mod_cast hh
  have hm : ((4 * (k + 1) ^ (t + 1) : ℕ) : ℝ) = 4 * K ^ (t + 1) := by
    dsimp only [K]
    push_cast
    rfl
  rw [hm] at hc
  have hl := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ 4 * K ^ (t + 1) by positivity)
  have hcancel : 4 * K ^ (t + 1) * (1 / (2 * K)) = 2 * K ^ t := by
    rw [pow_succ]
    field_simp
    ring
  rw [hcancel] at hl
  have hpos : 0 < K ^ t := by positivity
  linarith

/-- A quasipolynomial uniform bound obtained by elementary truncated inclusion–exclusion. -/
theorem isJacobsthalBound_quasipolynomial (k : ℕ) :
    IsJacobsthalBound k (4 * (k + 1) ^ (4 * Nat.clog 2 (k + 1) + 2)) := by
  let L := Nat.clog 2 (k + 1)
  have hL : k + 1 ≤ 2 ^ L := Nat.le_pow_clog (by decide) (k + 1)
  have hodd : Odd (4 * L + 1) := ⟨2 * L, by omega⟩
  have hpow : 2 * (k + 1) ^ 3 ≤ 2 ^ ((4 * L + 1) + 1) := by
    calc
      2 * (k + 1) ^ 3 ≤ 2 * (2 ^ L) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 3)
      _ = 2 ^ (3 * L + 1) := by
        rw [show 3 * L + 1 = L * 3 + 1 by omega, pow_add, pow_mul]
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  convert isJacobsthalBound_of_trunc_order k (4 * L + 1) hodd hpow using 1

theorem jacobsthalFunction_le_quasipolynomial (k : ℕ) :
    jacobsthalFunction k ≤ 4 * (k + 1) ^ (4 * Nat.clog 2 (k + 1) + 2) :=
  (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_quasipolynomial k)

end BrunCriterion


/-
Explicit reciprocal-prime estimates for the truncated sieve. Chebyshev's theta
bound controls each dyadic block, reducing the necessary truncation order.
-/
namespace BrunCriterion

noncomputable def dyadicPrimes (j : ℕ) : Finset ℕ :=
  (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime

/-- Each dyadic block contributes at most `4/j` to the sum of prime reciprocals. -/
theorem dyadic_reciprocal_sum_le (j : ℕ) (hj : 0 < j) :
    (∑ p ∈ dyadicPrimes j, (1 : ℝ) / p) ≤ 4 / (j : ℝ) := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpowpos : 0 < (2 : ℝ) ^ j := by positivity
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogs : ((dyadicPrimes j).card : ℝ) * (j * Real.log 2) ≤
      Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) := by
    calc
      _ = ∑ p ∈ dyadicPrimes j, (j : ℝ) * Real.log 2 := by simp
      _ ≤ ∑ p ∈ dyadicPrimes j, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hplo := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
        have hh := Real.log_le_log hpowpos (show (2 : ℝ) ^ j ≤ p by exact_mod_cast hplo)
        simpa only [Real.log_pow] using hh
      _ ≤ Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) := by
        simp only [Chebyshev.theta, Nat.floor_natCast]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
          obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hpI
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpp.pos, hhi.le⟩, hpp⟩
        · intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  have htheta : Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) ≤ 4 * Real.log 2 * (2 : ℝ) ^ j := by
    calc
      _ ≤ Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ) := Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = _ := by rw [hlog4, Nat.cast_pow, Nat.cast_ofNat, pow_succ]; ring
  have hcard : ((dyadicPrimes j).card : ℝ) * j ≤ 4 * (2 : ℝ) ^ j := by
    apply (mul_le_mul_iff_left₀ hlog2).mp
    nlinarith only [hlogs, htheta]
  calc
    (∑ p ∈ dyadicPrimes j, (1 : ℝ) / p) ≤ ∑ p ∈ dyadicPrimes j, 1 / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro p hp
      have hplo := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
      exact one_div_le_one_div_of_le hpowpos (by exact_mod_cast hplo)
    _ = ((dyadicPrimes j).card : ℝ) / (2 : ℝ) ^ j := by simp [div_eq_mul_inv]
    _ ≤ 4 / (j : ℝ) := (div_le_div_iff₀ hpowpos hjR).mpr hcard

/-- A bound uniform over arbitrary sets of at most `k` primes, not just prime prefixes. -/
theorem prime_reciprocal_sum_le (k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPk : P.card ≤ k) :
    (∑ p ∈ P, (1 : ℝ) / p) ≤
      5 + 4 * (Nat.clog 2 (Nat.log 2 (k + 1) + 1) : ℝ) * Real.log 2 := by
  classical
  let L := Nat.log 2 (k + 1) + 1
  let J := Nat.clog 2 L
  let A := P.filter (fun p => p ≤ k)
  let B := P.filter (fun p => ¬p ≤ k)
  have hL : 0 < L := by dsimp [L]; omega
  have hsplit : (∑ p ∈ A, (1 : ℝ) / p) + (∑ p ∈ B, (1 : ℝ) / p) = ∑ p ∈ P, (1 : ℝ) / p :=
    Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ k) (fun p => (1 : ℝ) / p)
  have hBcard : B.card ≤ k := (Finset.card_filter_le _ _).trans hPk
  have hlarge : (∑ p ∈ B, (1 : ℝ) / p) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ B, 1 / ((k : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpk : k + 1 ≤ p := by have := (Finset.mem_filter.mp hp).2; omega
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpk)
      _ = (B.card : ℝ) / ((k : ℝ) + 1) := by simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
        (by exact_mod_cast hBcard.trans (Nat.le_succ k))
  have hmap : ∀ p ∈ A, Nat.log 2 p ∈ Finset.Icc 1 L := by
    intro p hp
    obtain ⟨hpP, hpk⟩ := Finset.mem_filter.mp hp
    have hpprime := hP p hpP
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact Nat.le_log_of_pow_le (by decide) (by simpa using hpprime.two_le)
    · have hh : Nat.log 2 p ≤ Nat.log 2 (k + 1) :=
        Nat.log_mono_right (show p ≤ k + 1 by omega)
      dsimp [L]
      omega
  have hsmall : (∑ p ∈ A, (1 : ℝ) / p) ≤ 4 * (1 + Real.log (L : ℝ)) := by
    calc
      _ = ∑ j ∈ Finset.Icc 1 L, ∑ p ∈ A.filter (fun p => Nat.log 2 p = j), (1 : ℝ) / p :=
        (Finset.sum_fiberwise_of_maps_to hmap _).symm
      _ ≤ ∑ j ∈ Finset.Icc 1 L, ∑ p ∈ dyadicPrimes j, (1 : ℝ) / p := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpA, hlog⟩ := Finset.mem_filter.mp hp
          have hpprime := hP p (Finset.mem_filter.mp hpA).1
          have hjpos : 0 < j := by have := (Finset.mem_Icc.mp hj).1; omega
          have hb := (Nat.log_eq_iff (Or.inl hjpos.ne')).mp hlog
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hb, hpprime⟩
        · intro p hp _
          positivity
      _ ≤ ∑ j ∈ Finset.Icc 1 L, 4 / (j : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact dyadic_reciprocal_sum_le j (by have := (Finset.mem_Icc.mp hj).1; omega)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (by norm_num : (0 : ℝ) ≤ 4)
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
          Finset.mul_sum, div_eq_mul_inv] using hh
  have hlog : Real.log (L : ℝ) ≤ (J : ℝ) * Real.log 2 := by
    have hLpow : L ≤ 2 ^ J := Nat.le_pow_clog (by decide) L
    have hh := Real.log_le_log (by exact_mod_cast hL) (show (L : ℝ) ≤ (2 : ℝ) ^ J by exact_mod_cast hLpow)
    simpa only [Real.log_pow] using hh
  change _ ≤ 5 + 4 * (J : ℝ) * Real.log 2
  linarith

end BrunCriterion


/-
A refinement of the explicit Brun upper bound to truncation order `O(log log k)`.
This remains a partial result, not a proof of the quadratic conjecture.
-/
namespace BrunCriterion

/-- Exponential bounds for the sieve density and the tail generating function. -/
theorem prime_product_exp_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (Real.exp (-2 * ∑ p ∈ P, (1 : ℝ) / p) ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ))) ∧
    ((∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))) ≤ Real.exp (2 * ∑ p ∈ P, (1 : ℝ) / p)) := by
  classical
  have hfactor (p : ℕ) (hp : p ∈ P) : Real.exp (-2 * (1 / (p : ℝ))) ≤ 1 - 1 / (p : ℝ) := by
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hpRpos : 0 < (p : ℝ) := by linarith
    have hx0 : 0 ≤ 1 / (p : ℝ) := by positivity
    have hx1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
    have hy : 0 < 1 - 1 / (p : ℝ) := by linarith
    have hpoly : 1 ≤ (1 + 2 * (1 / (p : ℝ))) * (1 - 1 / (p : ℝ)) := by
      nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - 2 * (1 / (p : ℝ)) by linarith)]
    have hinv : (1 - 1 / (p : ℝ))⁻¹ ≤ 1 + 2 * (1 / (p : ℝ)) := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hy).mpr hpoly
    have hl := Real.one_sub_inv_le_log_of_pos hy
    have hh : -2 * (1 / (p : ℝ)) ≤ Real.log (1 - 1 / (p : ℝ)) := by linarith
    simpa only [Real.exp_log hy] using Real.exp_le_exp.mpr hh
  constructor
  · rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod (fun p hp => (Real.exp_pos _).le) hfactor
  · rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      positivity
    · intro p hp
      simpa only [add_comm] using Real.add_one_le_exp (2 * (1 / (p : ℝ)))

/-- The truncation order only needs to dominate the total reciprocal-prime mass. -/
theorem isJacobsthalBound_of_reciprocal_order (k t : ℕ) (ht : Odd t)
    (horder : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      4 * (∑ p ∈ P, (1 : ℝ) / p) ≤ (t : ℝ) * Real.log 2) :
    IsJacobsthalBound k (4 * (k + 1) ^ (t + 1)) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k (4 * (k + 1) ^ (t + 1))).mp hbad
  let K : ℝ := (k : ℝ) + 1
  let S : ℝ := ∑ p ∈ P, (1 : ℝ) / p
  let D : ℝ := ∏ p ∈ P, (1 - 1 / (p : ℝ))
  let R : ℝ := ∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))
  have hK : 0 < K := by dsimp [K]; positivity
  have hPkR : (P.card : ℝ) + 1 ≤ K := by dsimp [K]; exact_mod_cast Nat.add_le_add_right hPk 1
  have hD : 1 / K ≤ D := (one_div_le_one_div_of_le (by positivity) hPkR).trans
    (prime_product_bounds P hP).1
  obtain ⟨hden, hgen⟩ := prime_product_exp_bounds P hP
  change Real.exp (-2 * S) ≤ D at hden
  change R ≤ Real.exp (2 * S) at hgen
  have hR : R ≤ (2 : ℝ) ^ t * D := by
    calc
      R ≤ Real.exp (2 * S) := hgen
      _ ≤ (2 : ℝ) ^ t * Real.exp (-2 * S) := by
        have heq : (2 : ℝ) ^ t = Real.exp ((t : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        rw [heq, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hh := horder P hP hPk
        change 4 * S ≤ _ at hh
        linarith
      _ ≤ (2 : ℝ) ^ t * D := mul_le_mul_of_nonneg_left hden (by positivity)
  have herr : R / (2 : ℝ) ^ (t + 1) ≤ D / 2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    rw [pow_succ]
    nlinarith only [hR]
  have htail := trunc_value_lower P (fun p => 1 / (p : ℝ)) (fun p hp => by positivity) t
  have heq : (∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, (1 / (p : ℝ))) =
      truncDensity P t := by
    simp only [truncDensity, div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]
  rw [heq] at htail
  change D - R / (2 : ℝ) ^ (t + 1) ≤ truncDensity P t at htail
  have hinv : (1 / K) / 2 = 1 / (2 * K) := by rw [div_div, mul_comm K 2]
  have hdensity : 1 / (2 * K) ≤ truncDensity P t := by
    rw [← hinv]
    linarith
  have hc := cover_density_le P hP r (4 * (k + 1) ^ (t + 1)) t ht hcover
  have hcardR : ((truncSets P t).card : ℝ) ≤ K ^ t := by
    have hh : (truncSets P t).card ≤ (k + 1) ^ t :=
      (truncSets_card_le P t).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hPk 1) t)
    dsimp [K]
    exact_mod_cast hh
  have hm : ((4 * (k + 1) ^ (t + 1) : ℕ) : ℝ) = 4 * K ^ (t + 1) := by
    dsimp only [K]
    push_cast
    rfl
  rw [hm] at hc
  have hl := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ 4 * K ^ (t + 1) by positivity)
  have hcancel : 4 * K ^ (t + 1) * (1 / (2 * K)) = 2 * K ^ t := by
    rw [pow_succ]
    field_simp
    ring
  rw [hcancel] at hl
  have hpos : 0 < K ^ t := by positivity
  linarith

/-- An explicit upper bound with exponent of order `log log k`. -/
theorem isJacobsthalBound_refined (k : ℕ) :
    IsJacobsthalBound k
      (4 * (k + 1) ^ (16 * Nat.clog 2 (Nat.log 2 (k + 1) + 1) + 42)) := by
  let J := Nat.clog 2 (Nat.log 2 (k + 1) + 1)
  have hodd : Odd (16 * J + 41) := ⟨8 * J + 20, by omega⟩
  have horder : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      4 * (∑ p ∈ P, (1 : ℝ) / p) ≤ ((16 * J + 41 : ℕ) : ℝ) * Real.log 2 := by
    intro P hP hPk
    have hh := prime_reciprocal_sum_le k P hP hPk
    change (∑ p ∈ P, (1 : ℝ) / p) ≤ 5 + 4 * (J : ℝ) * Real.log 2 at hh
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hl ⊢
      exact hl
    push_cast
    nlinarith only [hh, hlog]
  convert isJacobsthalBound_of_reciprocal_order k (16 * J + 41) hodd horder using 1

theorem jacobsthalFunction_le_refined (k : ℕ) :
    jacobsthalFunction k ≤
      4 * (k + 1) ^ (16 * Nat.clog 2 (Nat.log 2 (k + 1) + 1) + 42) :=
  (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_refined k)

end BrunCriterion

/-
Finite sieve polynomials and products on disjoint prime blocks. The coefficients
and all error estimates are explicit; no new analytic estimate is assumed.
-/
namespace BlockSieve

open Erdos970.BrunCriterion

structure SievePolynomial where
  Term : Type
  fintypeTerm : Fintype Term
  primes : Term → Finset ℕ
  coefficient : Term → ℝ

attribute [instance] SievePolynomial.fintypeTerm

namespace SievePolynomial

noncomputable def value (S : SievePolynomial) (r : ℕ → ℕ) (i : ℕ) : ℝ :=
  ∑ a : S.Term, S.coefficient a * if (∀ p ∈ S.primes a, i ≡ r p [MOD p]) then 1 else 0

noncomputable def mean (S : SievePolynomial) : ℝ :=
  ∑ a : S.Term, S.coefficient a / ∏ p ∈ S.primes a, (p : ℝ)

noncomputable def cost (S : SievePolynomial) : ℝ :=
  ∑ a : S.Term, |S.coefficient a|

def SupportedOn (S : SievePolynomial) (P : Finset ℕ) : Prop :=
  ∀ a : S.Term, S.primes a ⊆ P

theorem cost_nonneg (S : SievePolynomial) : 0 ≤ S.cost :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Each term has one CRT remainder of size at most one. -/
theorem interval_error (S : SievePolynomial) (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) :
    |(∑ i ∈ Finset.range m, S.value r i) - (m : ℝ) * S.mean| ≤ S.cost := by
  classical
  let C (a : S.Term) := ((Finset.range m).filter (fun i => ∀ p ∈ S.primes a, i ≡ r p [MOD p])).card
  have hcount : (∑ i ∈ Finset.range m, S.value r i) = ∑ a : S.Term, S.coefficient a * C a := by
    simp only [value]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.mul_sum]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, C]
  have hmain : (m : ℝ) * S.mean = ∑ a : S.Term,
      S.coefficient a * ((m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ)) := by
    rw [mean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hcount, hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : S.Term, |S.coefficient a * C a -
        S.coefficient a * ((m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ S.cost := by
      apply Finset.sum_le_sum
      intro a ha
      rw [← mul_sub, abs_mul]
      have hh := intersection_count_error (S.primes a) (hS a) r m
      change |(C a : ℝ) - _| ≤ 1 at hh
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (abs_nonneg (S.coefficient a))

noncomputable def product {ι : Type} [Fintype ι] (S : ι → SievePolynomial) : SievePolynomial := by
  classical
  exact {
    Term := ∀ j, (S j).Term
    fintypeTerm := inferInstance
    primes := fun a => Finset.univ.biUnion (fun j => (S j).primes (a j))
    coefficient := fun a => ∏ j, (S j).coefficient (a j)
  }

theorem product_supportedOn {ι : Type} [Fintype ι] (S : ι → SievePolynomial)
    (P : ι → Finset ℕ) (hS : ∀ j, (S j).SupportedOn (P j)) :
    (product S).SupportedOn (Finset.univ.biUnion P) := by
  classical
  intro a p hp
  obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨j, hj, hS j (a j) hpj⟩

/-- Evaluation factorizes even without disjointness, since hit indicators are idempotent. -/
theorem value_product {ι : Type} [Fintype ι] (S : ι → SievePolynomial) (r : ℕ → ℕ) (i : ℕ) :
    (product S).value r i = ∏ j, (S j).value r i := by
  classical
  simp only [value, product, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.prod_mul_distrib, Finset.prod_boole]
  congr 1
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, forall_exists_index]
  aesop

/-- Absolute coefficient costs multiply exactly. -/
theorem cost_product {ι : Type} [Fintype ι] (S : ι → SievePolynomial) :
    (product S).cost = ∏ j, (S j).cost := by
  classical
  simp only [cost, Fintype.prod_sum]
  change (∑ a : ∀ j, (S j).Term, |∏ j, (S j).coefficient (a j)|) = _
  simp only [Finset.abs_prod]

/-- Main terms multiply when the prime supports are disjoint. -/
theorem mean_product {ι : Type} [Fintype ι] (S : ι → SievePolynomial)
    (P : ι → Finset ℕ) (hS : ∀ j, (S j).SupportedOn (P j))
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) :
    (product S).mean = ∏ j, (S j).mean := by
  classical
  simp only [mean, Fintype.prod_sum]
  change (∑ a : ∀ j, (S j).Term, (∏ j, (S j).coefficient (a j)) /
      ∏ p ∈ Finset.univ.biUnion (fun j => (S j).primes (a j)), (p : ℝ)) = _
  apply Finset.sum_congr rfl
  intro a ha
  have hd : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun j => (S j).primes (a j)) := by
    intro i hi j hj hij
    exact (hdis hij).mono (hS i (a i)) (hS j (a j))
  rw [Finset.prod_biUnion hd, Finset.prod_div_distrib]

noncomputable def upper (P : Finset ℕ) (t : ℕ) : SievePolynomial := by
  classical
  exact {
    Term := ↥(truncSets P t)
    fintypeTerm := inferInstance
    primes := Subtype.val
    coefficient := fun Q => (-1 : ℝ) ^ Q.val.card
  }

noncomputable def errorTerm (P : Finset ℕ) (t : ℕ) : SievePolynomial := by
  classical
  exact {
    Term := ↥(P.powersetCard (t + 1))
    fintypeTerm := inferInstance
    primes := Subtype.val
    coefficient := fun _ => 1
  }

theorem upper_supportedOn (P : Finset ℕ) (t : ℕ) : (upper P t).SupportedOn P := by
  intro Q
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp Q.property).1

theorem errorTerm_supportedOn (P : Finset ℕ) (t : ℕ) : (errorTerm P t).SupportedOn P := by
  intro Q
  exact (Finset.mem_powersetCard.mp Q.property).1

theorem mean_upper (P : Finset ℕ) (t : ℕ) : (upper P t).mean = truncDensity P t := by
  classical
  exact Finset.sum_coe_sort (truncSets P t) (fun Q => (-1 : ℝ) ^ Q.card / ∏ p ∈ Q, (p : ℝ))

theorem cost_upper (P : Finset ℕ) (t : ℕ) : (upper P t).cost = (truncSets P t).card := by
  classical
  change (∑ Q : ↥(truncSets P t), |(-1 : ℝ) ^ Q.val.card|) = _
  simp

theorem cost_errorTerm (P : Finset ℕ) (t : ℕ) : (errorTerm P t).cost = P.card.choose (t + 1) := by
  classical
  change (∑ _Q : ↥(P.powersetCard (t + 1)), |(1 : ℝ)|) = _
  simp

end SievePolynomial
end BlockSieve

/-
Pointwise and mean estimates for the upper and error factors in a block sieve.
-/
namespace BlockSieve.SievePolynomial

open Erdos970.BrunCriterion

noncomputable def badPrimes (P : Finset ℕ) (r : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  P.filter (fun p => i ≡ r p [MOD p])

theorem value_upper_eq (P : Finset ℕ) (r : ℕ → ℕ) (i t : ℕ) :
    (upper P t).value r i =
      ∑ Q ∈ truncSets (badPrimes P r i) t, (-1 : ℝ) ^ Q.card := by
  classical
  have hcoe : (upper P t).value r i = ∑ Q ∈ truncSets P t,
      (-1 : ℝ) ^ Q.card * (if ∀ p ∈ Q, i ≡ r p [MOD p] then 1 else 0) :=
    by
      simpa only [upper, value] using (Finset.sum_coe_sort (truncSets P t)
        (fun Q => (-1 : ℝ) ^ Q.card * (if ∀ p ∈ Q, i ≡ r p [MOD p] then 1 else 0)))
  rw [hcoe]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext Q
  simp only [truncSets, badPrimes, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
  aesop

theorem value_errorTerm_eq (P : Finset ℕ) (r : ℕ → ℕ) (i t : ℕ) :
    (errorTerm P t).value r i = ((badPrimes P r i).card.choose (t + 1) : ℝ) := by
  classical
  have hcoe : (errorTerm P t).value r i = ∑ Q ∈ P.powersetCard (t + 1),
      (1 : ℝ) * (if ∀ p ∈ Q, i ≡ r p [MOD p] then 1 else 0) :=
    by
      simpa only [errorTerm, value] using (Finset.sum_coe_sort (P.powersetCard (t + 1))
        (fun Q => (1 : ℝ) * (if ∀ p ∈ Q, i ≡ r p [MOD p] then 1 else 0)))
  rw [hcoe]
  simp only [one_mul]
  rw [← Finset.sum_filter]
  have heq : (P.powersetCard (t + 1)).filter (fun Q => ∀ p ∈ Q, i ≡ r p [MOD p]) =
      (badPrimes P r i).powersetCard (t + 1) := by
    ext Q
    simp only [badPrimes, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_iff]
    aesop
  rw [heq]
  simp

theorem value_upper_formula (P : Finset ℕ) (r : ℕ → ℕ) (i t : ℕ) :
    (upper P t).value r i =
      ∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ j * ((badPrimes P r i).card.choose j : ℝ) := by
  rw [value_upper_eq]
  exact_mod_cast signed_trunc_eq (badPrimes P r i) t

/-- Even truncations are pointwise nonnegative; if a block hits, its error factor dominates it. -/
theorem value_factor_bounds (P : Finset ℕ) (r : ℕ → ℕ) (i t : ℕ) (ht : Even t) :
    0 ≤ (upper P t).value r i ∧ 0 ≤ (errorTerm P t).value r i ∧
      ((∃ p ∈ P, i ≡ r p [MOD p]) → (upper P t).value r i ≤ (errorTerm P t).value r i) := by
  classical
  rw [value_upper_formula, value_errorTerm_eq]
  cases hc : (badPrimes P r i).card with
  | zero =>
    have hbad : ¬∃ p ∈ P, i ≡ r p [MOD p] := by
      rintro ⟨p, hp, hip⟩
      have hh : (badPrimes P r i).Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hp, hip⟩⟩
      have := Finset.card_pos.mpr hh
      omega
    have heq : (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ j * (Nat.choose 0 j : ℝ)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        rw [Nat.choose_eq_zero_of_lt (by omega : 0 < j)]
        simp
      · simp
    simp [heq, Nat.choose_zero_succ, hbad]
  | succ n =>
    have heq : (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ j * (Nat.choose (n + 1) j : ℝ)) =
        (-1 : ℝ) ^ t * (n.choose t : ℝ) := by
      exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := t))
    rw [heq, ht.neg_one_pow, one_mul]
    refine ⟨by positivity, by positivity, fun _ => ?_⟩
    exact_mod_cast (show n.choose t ≤ (n + 1).choose (t + 1) by
      rw [Nat.choose_succ_succ]
      omega)

/-- The degree-`t+1` error is bounded by the same generating function as the discarded tail. -/
theorem mean_errorTerm_le (P : Finset ℕ) (t : ℕ) :
    (errorTerm P t).mean ≤ (∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))) / (2 : ℝ) ^ (t + 1) := by
  classical
  have heq : (errorTerm P t).mean = ∑ Q ∈ P.powersetCard (t + 1), ∏ p ∈ Q, (1 / (p : ℝ)) := by
    have hcoe : (errorTerm P t).mean = ∑ Q ∈ P.powersetCard (t + 1), (1 : ℝ) / ∏ p ∈ Q, (p : ℝ) :=
      Finset.sum_coe_sort (P.powersetCard (t + 1)) (fun Q => (1 : ℝ) / ∏ p ∈ Q, (p : ℝ))
    rw [hcoe]
    simp only [div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]
  rw [heq]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (t + 1))).mpr
  rw [Finset.sum_mul, Finset.prod_one_add]
  have heq' : (∑ Q ∈ P.powersetCard (t + 1), (∏ p ∈ Q, (1 / (p : ℝ))) * 2 ^ (t + 1)) =
      ∑ Q ∈ P.powersetCard (t + 1), ∏ p ∈ Q, 2 * (1 / (p : ℝ)) := by
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hQ).2, mul_comm]
  rw [heq']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro Q hQ
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hQ).1
  · intro Q hQ _
    positivity

/-- Bounded reciprocal mass permits geometrically decreasing relative errors. -/
theorem block_mean_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ)
    (hmass : (∑ p ∈ P, (1 : ℝ) / p) ≤ 4) :
    let D := ∏ p ∈ P, (1 - 1 / (p : ℝ))
    D / 2 ≤ (upper P (2 * (n + 18))).mean ∧
      (errorTerm P (2 * (n + 18))).mean ≤ D / (2 : ℝ) ^ (n + 3) := by
  classical
  let D := ∏ p ∈ P, (1 - 1 / (p : ℝ))
  let R := ∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))
  let S := ∑ p ∈ P, (1 : ℝ) / p
  obtain ⟨hDexp, hRexp⟩ := prime_product_exp_bounds P hP
  change Real.exp (-2 * S) ≤ D at hDexp
  change R ≤ Real.exp (2 * S) at hRexp
  have hD : 0 < D := (Real.exp_pos _).trans_le hDexp
  have hR : R ≤ (2 : ℝ) ^ 32 * D := by
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hl ⊢
      exact hl
    calc
      R ≤ Real.exp (2 * S) := hRexp
      _ ≤ (2 : ℝ) ^ 32 * Real.exp (-2 * S) := by
        have heq : (2 : ℝ) ^ 32 = Real.exp (32 * Real.log 2) := by
          rw [show (32 : ℝ) = (32 : ℕ) by norm_num, Real.exp_nat_mul,
            Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        rw [heq, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        change S ≤ 4 at hmass
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hDexp (by positivity)
  have hpower : (2 : ℝ) ^ 32 * 2 ^ (n + 3) ≤ 2 ^ (2 * (n + 18) + 1) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have herr : R / (2 : ℝ) ^ (2 * (n + 18) + 1) ≤ D / 2 ^ (n + 3) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hR (by positivity : (0 : ℝ) ≤ 2 ^ (n + 3))
    have hh' := mul_le_mul_of_nonneg_left hpower hD.le
    nlinarith only [hh, hh']
  have herrhalf : D / (2 : ℝ) ^ (n + 3) ≤ D / 2 := by
    apply div_le_div_of_nonneg_left hD.le (by norm_num)
    have hh : (2 : ℝ) ^ 1 ≤ 2 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    simpa only [pow_one] using hh
  have hlow := trunc_value_lower P (fun p => (1 : ℝ) / p) (fun p hp => by positivity) (2 * (n + 18))
  have heq : (∑ Q ∈ truncSets P (2 * (n + 18)), (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, (1 / (p : ℝ))) =
      (upper P (2 * (n + 18))).mean := by
    rw [mean_upper]
    simp only [truncDensity, div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]
  rw [heq] at hlow
  change D - R / _ ≤ _ at hlow
  refine ⟨?_, (mean_errorTerm_le P _).trans herr⟩
  change D / 2 ≤ _
  linarith

theorem factor_cost_bounds (P : Finset ℕ) (t : ℕ) :
    (upper P t).cost ≤ ((P.card + 1 : ℕ) : ℝ) ^ (t + 1) ∧
    (errorTerm P t).cost ≤ ((P.card + 1 : ℕ) : ℝ) ^ (t + 1) := by
  constructor
  · rw [cost_upper]
    exact_mod_cast (truncSets_card_le P t).trans (Nat.pow_le_pow_right (by omega) (by omega : t ≤ t + 1))
  · rw [cost_errorTerm]
    exact_mod_cast (Nat.choose_le_pow P.card (t + 1)).trans (Nat.pow_le_pow_left (Nat.le_succ P.card) (t + 1))

end BlockSieve.SievePolynomial

/-
A finite block-sieve criterion. It keeps the pointwise, main-term, and remainder
estimates separate; all hypotheses are explicit.
-/
namespace BlockSieve

open SievePolynomial

/-- A hit in one block forces the combined lower weight to be nonpositive. -/
theorem pointwise_product_le_error_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (U E : ι → ℝ) (hU : ∀ i, 0 ≤ U i) (hE : ∀ i, 0 ≤ E i)
    (hhit : ∃ i, U i ≤ E i) :
    (∏ j, U j) ≤ ∑ i, ∏ j, if j = i then E j else U j := by
  obtain ⟨i, hi⟩ := hhit
  calc
    (∏ j, U j) ≤ ∏ j, if j = i then E j else U j := by
      apply Finset.prod_le_prod (fun j _ => hU j)
      intro j hj
      by_cases hji : j = i
      · simpa [hji] using hi
      · simp [hji]
    _ ≤ _ := Finset.single_le_sum (f := fun i : ι => ∏ j, if j = i then E j else U j)
      (fun i _ => Finset.prod_nonneg (fun j _ => by split_ifs <;> aesop)) (Finset.mem_univ i)

/-- Geometrically small relative errors leave a positive combined main term. -/
theorem product_main_lower {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B D ε : ι → ℝ) (hD : ∀ i, 0 ≤ D i) (hA : ∀ i, D i / 2 ≤ A i)
    (hB0 : ∀ i, 0 ≤ B i) (hε0 : ∀ i, 0 ≤ ε i) (hB : ∀ i, B i ≤ ε i * D i)
    (hε : (∑ i, ε i) ≤ 1 / 4) :
    (∏ i, D i) / (2 : ℝ) ^ (Fintype.card ι + 1) ≤
      (∏ i, A i) - ∑ i, ∏ j, if j = i then B j else A j := by
  have hA0 (i : ι) : 0 ≤ A i := (div_nonneg (hD i) (by norm_num)).trans (hA i)
  have hprod0 : 0 ≤ ∏ i, A i := Finset.prod_nonneg (fun i _ => hA0 i)
  have hBi (i : ι) : B i ≤ (2 * ε i) * A i := by
    have hh := mul_le_mul_of_nonneg_left (hA i) (hε0 i)
    nlinarith only [hB i, hh]
  have hterm (i : ι) : (∏ j, if j = i then B j else A j) ≤ (2 * ε i) * ∏ j, A j := by
    calc
      (∏ j, if j = i then B j else A j) ≤ ∏ j, (if j = i then 2 * ε i else 1) * A j := by
        apply Finset.prod_le_prod
        · intro j hj
          split_ifs <;> aesop
        · intro j hj
          by_cases hji : j = i
          · simpa [hji] using hBi i
          · simp [hji]
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hsum : (∑ i, ∏ j, if j = i then B j else A j) ≤ (1 / 2 : ℝ) * ∏ j, A j := by
    calc
      _ ≤ ∑ i, (2 * ε i) * ∏ j, A j := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (2 * ∑ i, ε i) * ∏ j, A j := by rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hprod0
  have hprod : (∏ i, D i) / (2 : ℝ) ^ Fintype.card ι ≤ ∏ i, A i := by
    have hh : (∏ i, D i / 2) ≤ ∏ i, A i := Finset.prod_le_prod
      (fun i _ => div_nonneg (hD i) (by norm_num)) (fun i _ => hA i)
    simpa only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ] using hh
  have hh := div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 2)
  rw [div_div, ← pow_succ] at hh
  linarith

/-- Abstract finite block-sieve estimate, using arbitrary upper and error polynomials. -/
theorem block_cover_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (U E : ι → SievePolynomial) (P : ι → Finset ℕ)
    (hU : ∀ j, (U j).SupportedOn (P j)) (hE : ∀ j, (E j).SupportedOn (P j))
    (hP : ∀ j, ∀ p ∈ P j, p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (r : ℕ → ℕ) (m : ℕ)
    (hpoint : ∀ x < m, (∀ j, 0 ≤ (U j).value r x) ∧ (∀ j, 0 ≤ (E j).value r x) ∧
      ∃ j, (U j).value r x ≤ (E j).value r x) :
    (m : ℝ) * ((∏ j, (U j).mean) - ∑ i, ∏ j, (if j = i then E j else U j).mean) ≤
      (∏ j, (U j).cost) + ∑ i, ∏ j, (if j = i then E j else U j).cost := by
  classical
  let V (i : ι) (j : ι) := if j = i then E j else U j
  have hV (i j : ι) : (V i j).SupportedOn (P j) := by
    dsimp only [V]
    split_ifs <;> aesop
  have hprimeU : ∀ a, ∀ p ∈ (product U).primes a, p.Prime := by
    intro a p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hP j p (hU j (a j) hpj)
  have hprimeV (i : ι) : ∀ a, ∀ p ∈ (product (V i)).primes a, p.Prime := by
    intro a p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hP j p (hV i j (a j) hpj)
  have hintU := interval_error (product U) hprimeU r m
  rw [mean_product U P hU hdis, cost_product] at hintU
  have hintV (i : ι) :
      (∑ x ∈ Finset.range m, (product (V i)).value r x) ≤
        (m : ℝ) * (∏ j, (V i j).mean) + ∏ j, (V i j).cost := by
    have hh := interval_error (product (V i)) (hprimeV i) r m
    rw [mean_product (V i) P (hV i) hdis, cost_product] at hh
    have hh' := (abs_le.mp hh).2
    linarith
  have hsum : (∑ x ∈ Finset.range m, (product U).value r x) ≤
      ∑ i, ∑ x ∈ Finset.range m, (product (V i)).value r x := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro x hx
    obtain ⟨hxU, hxE, hxhit⟩ := hpoint x (Finset.mem_range.mp hx)
    simp only [value_product]
    have hh := pointwise_product_le_error_sum (fun j => (U j).value r x) (fun j => (E j).value r x)
      hxU hxE hxhit
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    dsimp only [V]
    split_ifs <;> rfl
  have hvsum := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset ι)) => hintV i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hvsum
  have hu := (abs_le.mp hintU).1
  change (m : ℝ) * ((∏ j, (U j).mean) - ∑ i, ∏ j, (V i j).mean) ≤
    (∏ j, (U j).cost) + ∑ i, ∏ j, (V i j).cost
  linarith

/-- A numerical cover-length estimate for disjoint blocks with bounded reciprocal mass. -/
theorem cover_bound_of_blocks (b k : ℕ) (P : Fin b → Finset ℕ) (n : Fin b → ℕ)
    (hP : ∀ j, ∀ p ∈ P j, p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hcard : (Finset.univ.biUnion P).card ≤ k)
    (hmass : ∀ j, (∑ p ∈ P j, (1 : ℝ) / p) ≤ 4)
    (hε : (∑ j, (1 : ℝ) / 2 ^ (n j + 3)) ≤ 1 / 4)
    (r : ℕ → ℕ) (m : ℕ) (hcover : ∀ x < m, ∃ j, ∃ p ∈ P j, x ≡ r p [MOD p]) :
    m ≤ (b + 1) * (k + 1) * 2 ^ (b + 1) *
      ∏ j, ((P j).card + 1) ^ (2 * (n j + 18) + 1) := by
  classical
  let U (j : Fin b) := upper (P j) (2 * (n j + 18))
  let E (j : Fin b) := errorTerm (P j) (2 * (n j + 18))
  let D (j : Fin b) := ∏ p ∈ P j, (1 - 1 / (p : ℝ))
  let ε (j : Fin b) : ℝ := 1 / 2 ^ (n j + 3)
  let N (j : Fin b) := ((P j).card + 1) ^ (2 * (n j + 18) + 1)
  have hUs (j : Fin b) : (U j).SupportedOn (P j) := upper_supportedOn _ _
  have hEs (j : Fin b) : (E j).SupportedOn (P j) := errorTerm_supportedOn _ _
  have hpoint : ∀ x < m, (∀ j, 0 ≤ (U j).value r x) ∧ (∀ j, 0 ≤ (E j).value r x) ∧
      ∃ j, (U j).value r x ≤ (E j).value r x := by
    intro x hx
    have hb (j : Fin b) := value_factor_bounds (P j) r x (2 * (n j + 18)) (even_two_mul _)
    refine ⟨fun j => (hb j).1, fun j => (hb j).2.1, ?_⟩
    obtain ⟨j, p, hp, hxp⟩ := hcover x hx
    exact ⟨j, (hb j).2.2 ⟨p, hp, hxp⟩⟩
  have hc := block_cover_bound U E P hUs hEs hP hdis r m hpoint
  have hDj (j : Fin b) : 0 < D j := by
    have hh := (Erdos970.BrunCriterion.prime_product_exp_bounds (P j) (hP j)).1
    exact (Real.exp_pos _).trans_le hh
  have hb (j : Fin b) := block_mean_bounds (P j) (hP j) (n j) (hmass j)
  have hA (j : Fin b) : D j / 2 ≤ (U j).mean := (hb j).1
  have hB (j : Fin b) : (E j).mean ≤ ε j * D j := by
    have hh := (hb j).2
    simpa only [ε, D, div_eq_mul_inv, one_mul, mul_comm] using hh
  have hB0 (j : Fin b) : 0 ≤ (E j).mean := by
    change 0 ≤ ∑ Q : ↥((P j).powersetCard (2 * (n j + 18) + 1)),
      (1 : ℝ) / ∏ p ∈ Q.val, (p : ℝ)
    exact Finset.sum_nonneg (fun Q _ => by positivity)
  have hmain0 := product_main_lower (fun j => (U j).mean) (fun j => (E j).mean) D ε
    (fun j => (hDj j).le) hA hB0 (fun j => by dsimp [ε]; positivity) hB hε
  have hmain : (∏ j, D j) / (2 : ℝ) ^ (b + 1) ≤
      (∏ j, (U j).mean) - ∑ i, ∏ j, (if j = i then E j else U j).mean := by
    simpa only [Fintype.card_fin, apply_ite] using hmain0
  have hPall : ∀ p ∈ Finset.univ.biUnion P, p.Prime := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hP j p hpj
  have hdall : (↑(Finset.univ : Finset (Fin b)) : Set (Fin b)).PairwiseDisjoint P :=
    fun i hi j hj hij => hdis hij
  have hDall : (1 : ℝ) / (k + 1) ≤ ∏ j, D j := by
    have hh := (Erdos970.BrunCriterion.prime_product_bounds (Finset.univ.biUnion P) hPall).1
    rw [Finset.prod_biUnion hdall] at hh
    exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hcard 1)).trans hh
  let Q : ℕ := (k + 1) * 2 ^ (b + 1)
  have hQpos : 0 < (Q : ℝ) := by dsimp [Q]; positivity
  have hmain' : 1 / (Q : ℝ) ≤
      (∏ j, (U j).mean) - ∑ i, ∏ j, (if j = i then E j else U j).mean := by
    have hh := (div_le_div_of_nonneg_right hDall (by positivity : (0 : ℝ) ≤ 2 ^ (b + 1))).trans hmain
    simpa only [Q, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, div_div] using hh
  have hCU : (∏ j, (U j).cost) ≤ ∏ j, (N j : ℝ) :=
    Finset.prod_le_prod (fun j _ => cost_nonneg _) (fun j _ => by
      simpa only [N, Nat.cast_pow] using (factor_cost_bounds (P j) (2 * (n j + 18))).1)
  have hCE (i : Fin b) : (∏ j, (if j = i then E j else U j).cost) ≤ ∏ j, (N j : ℝ) := by
    apply Finset.prod_le_prod (fun j _ => cost_nonneg _)
    intro j hj
    have hh := factor_cost_bounds (P j) (2 * (n j + 18))
    by_cases hji : j = i
    · simpa only [if_pos hji, N, Nat.cast_pow] using hh.2
    · simpa only [if_neg hji, N, Nat.cast_pow] using hh.1
  have hCsum : (∏ j, (U j).cost) + ∑ i, ∏ j, (if j = i then E j else U j).cost ≤
      ((b : ℝ) + 1) * ∏ j, (N j : ℝ) := by
    have hh := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin b))) => hCE i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    nlinarith only [hh, hCU]
  have hmQ : (m : ℝ) / Q ≤ ((b : ℝ) + 1) * ∏ j, (N j : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hmain' (Nat.cast_nonneg m)
    simpa only [mul_one_div] using hh.trans (hc.trans hCsum)
  have hmle := (div_le_iff₀ hQpos).mp hmQ
  have hnat : m ≤ (b + 1) * (∏ j, N j) * Q := by
    exact_mod_cast hmle
  dsimp only [Q, N] at hnat
  convert hnat using 1 <;> ring

end BlockSieve

/- A doubly dyadic partition of an arbitrary finite set of primes. -/
namespace BlockSieve
open Erdos970.BrunCriterion

/-- The final block includes the entire remaining tail. -/
def primeBlock (P : Finset ℕ) (J : ℕ) (j : Fin (J + 1)) : Finset ℕ :=
  P.filter (fun p => min (Nat.log 2 (Nat.log 2 p)) J = j.val)

theorem primeBlock_subset (P : Finset ℕ) (J : ℕ) (j : Fin (J + 1)) :
    primeBlock P J j ⊆ P := Finset.filter_subset _ _

theorem primeBlock_union (P : Finset ℕ) (J : ℕ) :
    Finset.univ.biUnion (primeBlock P J) = P := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact primeBlock_subset P J j hj
  · intro hp
    exact ⟨⟨min (Nat.log 2 (Nat.log 2 p)) J,
      Nat.lt_succ_of_le (min_le_right _ _)⟩, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩

theorem primeBlock_disjoint (P : Finset ℕ) (J : ℕ) :
    Pairwise (fun i j => Disjoint (primeBlock P J i) (primeBlock P J j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  apply hij
  exact Fin.ext ((Finset.mem_filter.mp hpi).2.symm.trans (Finset.mem_filter.mp hpj).2)

theorem primeBlock_log_bounds (P : Finset ℕ) (J : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (j : Fin (J + 1)) (hj : j.val < J)
    {p : ℕ} (hp : p ∈ primeBlock P J j) :
    2 ^ j.val ≤ Nat.log 2 p ∧ Nat.log 2 p < 2 ^ (j.val + 1) := by
  have hpP := primeBlock_subset P J j hp
  have hplog : 0 < Nat.log 2 p := Nat.log_pos (by decide) (hP p hpP).two_le
  have hmin := (Finset.mem_filter.mp hp).2
  have heq : Nat.log 2 (Nat.log 2 p) = j.val := by omega
  exact (Nat.log_eq_iff (Or.inr ⟨by decide, hplog.ne'⟩)).mp heq

/-- Every nonfinal block has reciprocal mass at most four. -/
theorem primeBlock_mass_small (P : Finset ℕ) (J : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (j : Fin (J + 1)) (hj : j.val < J) :
    (∑ p ∈ primeBlock P J j, (1 : ℝ) / p) ≤ 4 := by
  classical
  let A := primeBlock P J j
  let lo := 2 ^ j.val
  let hi := 2 ^ (j.val + 1)
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hmap : ∀ p ∈ A, Nat.log 2 p ∈ Finset.Ico lo hi := by
    intro p hp
    exact Finset.mem_Ico.mpr (primeBlock_log_bounds P J hP j hj hp)
  calc
    _ = ∑ l ∈ Finset.Ico lo hi, ∑ p ∈ A.filter (fun p => Nat.log 2 p = l), (1 : ℝ) / p :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ l ∈ Finset.Ico lo hi, 4 / (l : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      have hlpos : 0 < l := hlo.trans_le (Finset.mem_Ico.mp hl).1
      apply le_trans _ (dyadic_reciprocal_sum_le l hlpos)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpA, heq⟩ := Finset.mem_filter.mp hp
        have hpprime := hP p (primeBlock_subset P J j hpA)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
          ((Nat.log_eq_iff (Or.inl hlpos.ne')).mp heq), hpprime⟩
      · intro p hp hnot
        positivity
    _ ≤ ∑ l ∈ Finset.Ico lo hi, 4 / (lo : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hlo)
        (by exact_mod_cast (Finset.mem_Ico.mp hl).1)
    _ = 4 := by
      have hhi : hi = 2 * lo := by dsimp [hi, lo]; rw [pow_succ]; omega
      have hcard : (Finset.Ico lo hi).card = lo := by simp [hhi]; omega
      simp only [Finset.sum_const, hcard, nsmul_eq_mul]
      have hloR : (lo : ℝ) ≠ 0 := by exact_mod_cast hlo.ne'
      field_simp

/-- If the final cutoff exceeds the cardinality budget, the final mass is at most one. -/
theorem primeBlock_mass_last (P : Finset ℕ) (J k : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcard : P.card ≤ k) (hcut : k + 1 ≤ 2 ^ (2 ^ J)) :
    (∑ p ∈ primeBlock P J (Fin.last J), (1 : ℝ) / p) ≤ 1 := by
  have hbig (p : ℕ) (hp : p ∈ primeBlock P J (Fin.last J)) : k + 1 ≤ p := by
    have hpprime := hP p (primeBlock_subset P J (Fin.last J) hp)
    have hplog : 0 < Nat.log 2 p := Nat.log_pos (by decide) hpprime.two_le
    have hmin := (Finset.mem_filter.mp hp).2
    have hJ : J ≤ Nat.log 2 (Nat.log 2 p) := by
      simpa only [Fin.val_last, min_eq_right_iff] using hmin
    have hlo : 2 ^ J ≤ Nat.log 2 p := Nat.pow_le_of_le_log hplog.ne' hJ
    exact hcut.trans (Nat.pow_le_of_le_log hpprime.ne_zero hlo)
  calc
    _ ≤ ∑ p ∈ primeBlock P J (Fin.last J), 1 / ((k : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hbig p hp)
    _ = ((primeBlock P J (Fin.last J)).card : ℝ) / ((k : ℝ) + 1) := by
      simp [div_eq_mul_inv]
    _ ≤ 1 := by
      apply (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
      have hh := (Finset.card_le_card (primeBlock_subset P J (Fin.last J))).trans hcard
      exact_mod_cast hh.trans (Nat.le_succ k)

theorem primeBlock_card_bound (P : Finset ℕ) (J k : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcard : P.card ≤ k)
    (hcut : k + 1 ≤ 2 ^ (2 ^ J)) (j : Fin (J + 1)) :
    (primeBlock P J j).card + 1 ≤ 2 ^ (2 ^ (j.val + 1)) := by
  by_cases hj : j.val < J
  · have hsub : primeBlock P J j ⊆ Finset.Ico 1 (2 ^ (2 ^ (j.val + 1))) := by
      intro p hp
      have hpprime := hP p (primeBlock_subset P J j hp)
      refine Finset.mem_Ico.mpr ⟨hpprime.one_le, ?_⟩
      exact Nat.lt_pow_of_log_lt (by decide) (primeBlock_log_bounds P J hP j hj hp).2
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at hc
    have hpos : 0 < 2 ^ (2 ^ (j.val + 1)) := by positivity
    omega
  · have hjJ : j.val = J := by omega
    have hc := (Finset.card_le_card (primeBlock_subset P J j)).trans hcard
    calc
      _ ≤ k + 1 := Nat.add_le_add_right hc 1
      _ ≤ 2 ^ (2 ^ J) := hcut
      _ ≤ _ := by rw [hjJ]; gcongr <;> omega

end BlockSieve

/- Explicit geometric-sum estimates for the block sieve. -/
namespace BlockSieve

theorem geometric_error_sum (J : ℕ) :
    (∑ j : Fin (J + 1), (1 : ℝ) / 2 ^ (J - j.val + 3)) ≤ 1 / 4 := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, zero_add]
    have hsum : (∑ j : Fin (J + 1), (1 : ℝ) / 2 ^ (J + 1 - j.val + 3)) =
        (∑ j : Fin (J + 1), (1 : ℝ) / 2 ^ (J - j.val + 3)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have heq : J + 1 - j.val + 3 = (J - j.val + 3) + 1 := by omega
      rw [heq, pow_succ, div_mul_eq_div_div]
    rw [hsum]
    norm_num
    simp only [one_div] at ih
    linarith

theorem weighted_exponent_sum (J : ℕ) :
    (∑ j : Fin (J + 1), 2 ^ (j.val + 1) * (2 * (J - j.val) + 37)) +
      4 * J + 82 = 156 * 2 ^ J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
    have hsum : (∑ j : Fin (J + 1), 2 ^ (j.val + 1 + 1) * (2 * (J - j.val) + 37)) =
        2 * ∑ j : Fin (J + 1), 2 ^ (j.val + 1) * (2 * (J - j.val) + 37) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring
    rw [hsum]
    simp only [Nat.zero_add, pow_succ] at ih ⊢
    nlinarith

theorem two_pow_clog_le (x : ℕ) (hx : 0 < x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  by_cases hx1 : x = 1
  · simp [hx1]
  have hx2 : 1 < x := by omega
  have hc := Nat.clog_pos (by decide : 1 < 2) hx2
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hx2
  rw [Nat.pred_eq_sub_one] at hp
  have he : Nat.clog 2 x = (Nat.clog 2 x - 1) + 1 := by omega
  calc
    2 ^ Nat.clog 2 x = 2 ^ (Nat.clog 2 x - 1) * 2 := by
      conv_lhs => rw [he]
      rw [pow_succ]
    _ ≤ 2 * x := by nlinarith

/-- A coarse fixed-power bound for the product of all block costs. -/
theorem block_cost_product_le (k : ℕ) (hk : 0 < k)
    (A : Fin (Nat.clog 2 (Nat.clog 2 (k + 1)) + 1) → ℕ)
    (hA : ∀ j, A j ≤ 2 ^ (2 ^ (j.val + 1))) :
    (∏ j, A j ^ (2 * (Nat.clog 2 (Nat.clog 2 (k + 1)) - j.val + 18) + 1)) ≤
      (k + 1) ^ 624 := by
  let K := k + 1
  let L := Nat.clog 2 K
  let J := Nat.clog 2 L
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hL : 0 < L := Nat.clog_pos (by decide) (by omega)
  have hJpow : 2 ^ J ≤ 2 * L := two_pow_clog_le L hL
  have hLpow : 2 ^ L ≤ 2 * K := two_pow_clog_le K (by omega)
  have hsum := weighted_exponent_sum J
  change (∏ j : Fin (J + 1), A j ^ (2 * (J - j.val + 18) + 1)) ≤ K ^ 624
  calc
    _ ≤ ∏ j : Fin (J + 1), (2 ^ (2 ^ (j.val + 1))) ^ (2 * (J - j.val + 18) + 1) := by
      exact Finset.prod_le_prod' (fun j _ => Nat.pow_le_pow_left (hA j) _)
    _ = 2 ^ (∑ j : Fin (J + 1), 2 ^ (j.val + 1) * (2 * (J - j.val) + 37)) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j hj
      rw [← pow_mul]
      congr 2
    _ ≤ 2 ^ (156 * 2 ^ J) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ 2 ^ (312 * L) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = (2 ^ L) ^ 312 := by rw [← pow_mul]; congr 1; omega
    _ ≤ (2 * K) ^ 312 := Nat.pow_le_pow_left hLpow _
    _ ≤ (K * K) ^ 312 := Nat.pow_le_pow_left (Nat.mul_le_mul_right K hK) _
    _ = K ^ 624 := by rw [← pow_two, ← pow_mul]

/-- The remaining factors consume at most another eight powers. -/
theorem block_prefactor_le (k : ℕ) (hk : 0 < k) :
    (Nat.clog 2 (Nat.clog 2 (k + 1)) + 2) * (k + 1) *
      2 ^ (Nat.clog 2 (Nat.clog 2 (k + 1)) + 2) ≤ (k + 1) ^ 8 := by
  let K := k + 1
  let L := Nat.clog 2 K
  let J := Nat.clog 2 L
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hL : 0 < L := Nat.clog_pos (by decide) (by omega)
  have hLK : L ≤ K := Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hJpow : 2 ^ J ≤ 2 * L := two_pow_clog_le L hL
  have hJsize : J + 2 ≤ 2 * 2 ^ J := by
    have hh := Nat.lt_pow_self (n := J + 1) (by decide : 1 < 2)
    rw [pow_succ] at hh
    omega
  have h32 : 32 ≤ K ^ 5 := by
    have hh := Nat.pow_le_pow_left hK 5
    norm_num at hh
    exact hh
  change (J + 2) * K * 2 ^ (J + 2) ≤ K ^ 8
  calc
    _ ≤ (2 * 2 ^ J) * K * (4 * 2 ^ J) := by
      have he : 2 ^ (J + 2) = 4 * 2 ^ J := by rw [pow_add]; ring
      rw [he]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right K hJsize)
    _ = 8 * K * (2 ^ J) ^ 2 := by ring
    _ ≤ 8 * K * (2 * L) ^ 2 := by gcongr
    _ = 32 * K * L ^ 2 := by ring
    _ ≤ 32 * K * K ^ 2 := by gcongr
    _ ≤ K ^ 5 * K * K ^ 2 := by gcongr
    _ = K ^ 8 := by ring

end BlockSieve

/-
An unconditional fixed-power upper bound obtained from the finite block sieve.
The exponent is deliberately coarse; this does not prove the quadratic conjecture.
-/
namespace BlockSieve

/-- No union of one residue class for each of at most `k` primes covers a longer interval. -/
theorem cover_length_le_fixed_power (k : ℕ) (hk : 0 < k)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hcard : P.card ≤ k)
    (r : ℕ → ℕ) (m : ℕ) (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) :
    m ≤ (k + 1) ^ 632 := by
  classical
  let L := Nat.clog 2 (k + 1)
  let J := Nat.clog 2 L
  let B := primeBlock P J
  have hcut : k + 1 ≤ 2 ^ (2 ^ J) :=
    (Nat.le_pow_clog (by decide) (k + 1)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_pow_clog (by decide) L))
  have hB (j : Fin (J + 1)) (p : ℕ) (hp : p ∈ B j) : p.Prime :=
    hP p (primeBlock_subset P J j hp)
  have hBcard : (Finset.univ.biUnion B).card ≤ k := by
    simpa only [B, primeBlock_union] using hcard
  have hmass (j : Fin (J + 1)) : (∑ p ∈ B j, (1 : ℝ) / p) ≤ 4 := by
    by_cases hj : j.val < J
    · exact primeBlock_mass_small P J hP j hj
    · have heq : j = Fin.last J := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [heq]
      exact (primeBlock_mass_last P J k hP hcard hcut).trans (by norm_num)
  have hcov : ∀ x < m, ∃ j : Fin (J + 1), ∃ p ∈ B j, x ≡ r p [MOD p] := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hcover x hx
    rw [← primeBlock_union P J] at hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact ⟨j, p, hpj, hxp⟩
  have hc := cover_bound_of_blocks (J + 1) k B (fun j => J - j.val) hB
    (primeBlock_disjoint P J) hBcard hmass (geometric_error_sum J) r m hcov
  have hcost : (∏ j, ((B j).card + 1) ^ (2 * (J - j.val + 18) + 1)) ≤ (k + 1) ^ 624 :=
    block_cost_product_le k hk (fun j => (B j).card + 1) (primeBlock_card_bound P J k hP hcard hcut)
  have hpref : (J + 2) * (k + 1) * 2 ^ (J + 2) ≤ (k + 1) ^ 8 := block_prefactor_le k hk
  calc
    m ≤ ((J + 2) * (k + 1) * 2 ^ (J + 2)) *
        ∏ j, ((B j).card + 1) ^ (2 * (J - j.val + 18) + 1) := hc
    _ ≤ (k + 1) ^ 8 * (k + 1) ^ 624 := Nat.mul_le_mul hpref hcost
    _ = (k + 1) ^ 632 := by rw [← pow_add]

/-- A uniform polynomial bound with a fixed, explicit exponent. -/
theorem isJacobsthalBound_fixed_power (k : ℕ) : IsJacobsthalBound k ((k + 1) ^ 633) := by
  by_cases hk : 0 < k
  · by_contra hbad
    obtain ⟨P, hP, hcard, r, hcover⟩ :=
      (not_isJacobsthalBound_iff_cover k ((k + 1) ^ 633)).mp hbad
    have hc := cover_length_le_fixed_power k hk P hP hcard r ((k + 1) ^ 633) hcover
    exact (Nat.pow_lt_pow_right (by omega : 1 < k + 1) (by decide : 632 < 633)).not_ge hc
  · have hk0 : k = 0 := by omega
    subst k
    simpa using isJacobsthalBound_factorial 0

theorem jacobsthalFunction_le_fixed_power (k : ℕ) :
    jacobsthalFunction k ≤ (k + 1) ^ 633 :=
  (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_fixed_power k)

end BlockSieve

/- A sharper, one-sided error bound for arbitrary finite sieve polynomials. -/
namespace BlockSieve.SievePolynomial
open Erdos970.BrunCriterion

/-- Positive coefficients can lose at most their expected count, or one if that is smaller. -/
noncomputable def lowerCost (S : SievePolynomial) (m : ℕ) : ℝ :=
  ∑ a : S.Term, (max (S.coefficient a) 0 *
    min 1 ((m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ)) + max (-S.coefficient a) 0)

theorem lowerCost_nonneg (S : SievePolynomial) (m : ℕ) : 0 ≤ S.lowerCost m := by
  apply Finset.sum_nonneg
  intro a ha
  exact add_nonneg (mul_nonneg (le_max_right _ _) (le_min (by norm_num) (by positivity)))
    (le_max_right _ _)

theorem lowerCost_le_cost (S : SievePolynomial) (m : ℕ) : S.lowerCost m ≤ S.cost := by
  apply Finset.sum_le_sum
  intro a ha
  have hh := mul_le_mul_of_nonneg_left
    (min_le_left 1 ((m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ)))
    (le_max_right (S.coefficient a) 0)
  by_cases hc : 0 ≤ S.coefficient a
  · rw [max_eq_left hc, max_eq_right (by linarith), abs_of_nonneg hc, add_zero]
    simpa only [max_eq_left hc, mul_one] using hh
  · have hc' : S.coefficient a ≤ 0 := by linarith
    simp only [max_eq_right hc', max_eq_left (neg_nonneg.mpr hc'),
      abs_of_nonpos hc', zero_mul, zero_add, le_refl]

/-- The elementary one-sided error estimate, independent of any sieve construction. -/
theorem coefficient_error_le (c E N : ℝ) (hN : 0 ≤ N) (herror : |N - E| ≤ 1) :
    c * E - c * N ≤ max c 0 * min 1 E + max (-c) 0 := by
  obtain ⟨hl, hu⟩ := abs_le.mp herror
  by_cases hc : 0 ≤ c
  · rw [max_eq_left hc, max_eq_right (by linarith), add_zero]
    have hsmall : E - N ≤ min 1 E := le_min (by linarith) (by linarith)
    have hh := mul_le_mul_of_nonneg_left hsmall hc
    nlinarith only [hh]
  · have hc' : c ≤ 0 := by linarith
    rw [max_eq_right hc', max_eq_left (neg_nonneg.mpr hc'), zero_mul, zero_add]
    have hh := mul_le_mul_of_nonneg_left hu (neg_nonneg.mpr hc')
    nlinarith only [hh]

/-- Unlike the absolute-error bound, this retains savings from sparse positive terms. -/
theorem interval_lower_error (S : SievePolynomial)
    (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime) (r : ℕ → ℕ) (m : ℕ) :
    (m : ℝ) * S.mean - (∑ i ∈ Finset.range m, S.value r i) ≤ S.lowerCost m := by
  classical
  let C (a : S.Term) := ((Finset.range m).filter
    (fun i => ∀ p ∈ S.primes a, i ≡ r p [MOD p])).card
  have hcount : (∑ i ∈ Finset.range m, S.value r i) =
      ∑ a : S.Term, S.coefficient a * C a := by
    simp only [value]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.mul_sum]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, C]
  have hmain : (m : ℝ) * S.mean = ∑ a : S.Term,
      S.coefficient a * ((m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ)) := by
    rw [mean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hmain, hcount, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a ha
  exact coefficient_error_le _ _ _ (Nat.cast_nonneg _)
    (intersection_count_error (S.primes a) (hS a) r m)

/-- A lower sieve weight that is nonpositive throughout an interval yields this improved test. -/
theorem cover_mean_le_lowerCost (S : SievePolynomial)
    (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime) (r : ℕ → ℕ) (m : ℕ)
    (hpoint : ∀ i < m, S.value r i ≤ 0) :
    (m : ℝ) * S.mean ≤ S.lowerCost m := by
  have hh := interval_lower_error S hS r m
  have hs : (∑ i ∈ Finset.range m, S.value r i) ≤ 0 :=
    Finset.sum_nonpos (fun i hi => hpoint i (Finset.mem_range.mp hi))
  linarith

end BlockSieve.SievePolynomial

/- Exact floor/ceiling versions of the finite sieve certificate. -/
namespace BlockSieve.SievePolynomial
open Erdos970.BrunCriterion

/-- The integral ceiling quotient; its intended use has positive denominator. -/
def ceilQuotient (m d : ℕ) : ℕ := m / d + if m % d = 0 then 0 else 1

theorem residue_count_bounds (m d r : ℕ) (hd : 0 < d) :
    m / d ≤ ((Finset.range m).filter (fun i => i ≡ r [MOD d])).card ∧
    ((Finset.range m).filter (fun i => i ≡ r [MOD d])).card ≤ ceilQuotient m d := by
  classical
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card m hd r]
  dsimp only [ceilQuotient]
  by_cases hm : m % d = 0
  · simp [hm]
  · simp only [if_neg hm]
    split_ifs <;> omega

theorem intersection_count_bounds (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) :
    m / (∏ p ∈ Q, p) ≤ ((Finset.range m).filter
      (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card ∧
    ((Finset.range m).filter (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card ≤
      ceilQuotient m (∏ p ∈ Q, p) := by
  classical
  obtain ⟨b, hb⟩ := intersection_residue Q hQ r
  simp_rw [hb]
  exact residue_count_bounds m _ b (Finset.prod_pos (fun p hp => (hQ p hp).pos))

/-- Each term is rounded in the direction dictated by its coefficient's sign. -/
noncomputable def roundedMain (S : SievePolynomial) (m : ℕ) : ℝ :=
  ∑ a : S.Term, if 0 ≤ S.coefficient a then
    S.coefficient a * (m / (∏ p ∈ S.primes a, p) : ℕ)
  else S.coefficient a * (ceilQuotient m (∏ p ∈ S.primes a, p) : ℕ)

theorem roundedMain_le_interval (S : SievePolynomial)
    (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime) (r : ℕ → ℕ) (m : ℕ) :
    S.roundedMain m ≤ ∑ i ∈ Finset.range m, S.value r i := by
  classical
  let C (a : S.Term) := ((Finset.range m).filter
    (fun i => ∀ p ∈ S.primes a, i ≡ r p [MOD p])).card
  have hcount : (∑ i ∈ Finset.range m, S.value r i) =
      ∑ a : S.Term, S.coefficient a * C a := by
    simp only [value]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.mul_sum]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, C]
  rw [hcount]
  apply Finset.sum_le_sum
  intro a ha
  obtain ⟨hlo, hhi⟩ := intersection_count_bounds (S.primes a) (hS a) r m
  change m / (∏ p ∈ S.primes a, p) ≤ C a at hlo
  change C a ≤ ceilQuotient m (∏ p ∈ S.primes a, p) at hhi
  by_cases hc : 0 ≤ S.coefficient a
  · rw [if_pos hc]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlo) hc
  · rw [if_neg hc]
    exact mul_le_mul_of_nonpos_left (by exact_mod_cast hhi) (le_of_not_ge hc)

/-- A covered interval cannot have a positive rounded lower main term. -/
theorem roundedMain_nonpos_of_nonpos (S : SievePolynomial)
    (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime) (r : ℕ → ℕ) (m : ℕ)
    (hpoint : ∀ i < m, S.value r i ≤ 0) : S.roundedMain m ≤ 0 :=
  (roundedMain_le_interval S hS r m).trans
    (Finset.sum_nonpos (fun i hi => hpoint i (Finset.mem_range.mp hi)))

/-- A positive rounded certificate proves existence of a survivor, without asymptotic errors. -/
theorem survivor_of_positive_roundedMain (P : Finset ℕ) (S : SievePolynomial)
    (hP : ∀ p ∈ P, p.Prime) (hS : S.SupportedOn P) (r : ℕ → ℕ) (m : ℕ)
    (hpoint : ∀ i < m, (∃ p ∈ P, i ≡ r p [MOD p]) → S.value r i ≤ 0)
    (hmain : 0 < S.roundedMain m) :
    ∃ i < m, ∀ p ∈ P, ¬i ≡ r p [MOD p] := by
  classical
  by_contra hbad
  push_neg at hbad
  have hSp : ∀ a, ∀ p ∈ S.primes a, p.Prime := fun a p hp => hP p (hS a hp)
  exact hmain.not_ge (roundedMain_nonpos_of_nonpos S hSp r m
    (fun i hi => hpoint i hi (hbad i hi)))

/-- Empty prime products, and every other divisor of the interval length, incur no error. -/
theorem roundedMain_eq_main_of_dvd (S : SievePolynomial) (m : ℕ)
    (hd : ∀ a, (∏ p ∈ S.primes a, p) ∣ m)
    (hp : ∀ a, 0 < ∏ p ∈ S.primes a, p) :
    S.roundedMain m = (m : ℝ) * S.mean := by
  classical
  rw [roundedMain, mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hmod : m % (∏ p ∈ S.primes a, p) = 0 := Nat.mod_eq_zero_of_dvd (hd a)
  have hquot : ((m / (∏ p ∈ S.primes a, p) : ℕ) : ℝ) =
      (m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.cast_div (hd a) (by exact_mod_cast (hp a).ne')]
  simp only [ceilQuotient, hmod, if_true, Nat.add_zero, hquot]
  split_ifs <;> ring

end BlockSieve.SievePolynomial

/--
Let $h(k)$ be Jacobsthal's function, defined to as the minimal $m$ such that, if $n$ has at most $k$ prime factors, then in any set of $m$ consecutive integers there exists an integer coprime to $n$. Determine the order of magnitude of $h(k)$. In particular, is it true that\[h(k) \ll k^2?\]
-/
theorem erdos_970 :
    (∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C * k ^ 2) := by
  sorry

end Erdos970
