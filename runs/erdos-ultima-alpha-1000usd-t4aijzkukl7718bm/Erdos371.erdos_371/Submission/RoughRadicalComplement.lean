import Submission.SuperlinearRoughCutoff

/-! An exact complementary-divisor formula for the rough tail. Passing to
the rough radical handles repeated prime factors without an exceptional set.
The input-dependent Möbius and least-factor weights remain explicit. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def roughRadical (B m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => B<p), p

lemma roughRadical_pos (B m : ℕ) : 0<roughRadical B m :=
  prod_pos fun _p hp => (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos

lemma roughRadical_squarefree (B m : ℕ) : Squarefree (roughRadical B m) :=
  squarefree_prod_primes _ (fun _p hp => Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)

lemma roughRadical_dvd (B m : ℕ) : roughRadical B m∣m :=
  (prod_dvd_prod_of_subset _ m.primeFactors id (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd m)

lemma roughRadical_prime_large (B m p : ℕ) (hp : p.Prime) (hd : p∣roughRadical B m) : B<p := by
  have hm := Nat.mem_primeFactors.mpr ⟨hp,hd,(roughRadical_pos B m).ne'⟩
  rw [roughRadical,Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)] at hm
  exact (mem_filter.mp hm).2

lemma squarefree_rough_dvd_radical (B m d : ℕ) (hm : m≠0) (hd : d∣m)
    (hs : Squarefree d) (hrough : B<d.minFac) : d∣roughRadical B m := by
  have hsub : d.primeFactors ⊆ m.primeFactors.filter (fun p => B<p) := by
    intro p hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp,hpd.trans hd,hm⟩,
      hrough.trans_le (Nat.minFac_le_of_dvd hpp.two_le hpd)⟩
  have h := prod_dvd_prod_of_subset _ _ id hsub
  simpa only [id_eq,Nat.prod_primeFactors_of_squarefree hs,roughRadical] using h

/-- Möbius support lets the rough divisor sum be taken over the rough
radical exactly; no squarefreeness assumption on m is needed. -/
theorem rough_moebius_tail_radical (B D m : ℕ) (hm : m≠0) (hD : 1≤D) (f : ℕ → ℝ) :
    (∑ d ∈ m.divisors.filter (fun d => D<d ∧ B<d.minFac),
      (ArithmeticFunction.moebius d : ℝ)*f d) =
    ∑ d ∈ (roughRadical B m).divisors.filter (fun d => D<d),
      (ArithmeticFunction.moebius d : ℝ)*f d := by
  classical
  let S := m.divisors.filter (fun d => D<d ∧ B<d.minFac)
  have he : (S.filter Squarefree) = (roughRadical B m).divisors.filter (fun d => D<d) := by
    ext d
    simp only [S,mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hd,_⟩,hDd,hBd⟩,hs⟩
      exact ⟨⟨squarefree_rough_dvd_radical B m d hm hd hs hBd,(roughRadical_pos B m).ne'⟩,hDd⟩
    · rintro ⟨⟨hd,_⟩,hDd⟩
      have hd1 : 1<d := lt_of_le_of_lt hD hDd
      have hpd := (Nat.minFac_dvd d).trans hd
      exact ⟨⟨⟨hd.trans (roughRadical_dvd B m),hm⟩,hDd,
        roughRadical_prime_large B m _ (Nat.minFac_prime (by omega)) hpd⟩,
        (roughRadical_squarefree B m).squarefree_of_dvd hd⟩
  change (∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ)*f d) = _
  rw [← he]
  conv_rhs => rw [sum_filter]
  apply sum_congr rfl
  intro d hd
  by_cases hs : Squarefree d
  · simp [hs]
  · simp [hs,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]

lemma moebius_complement_squarefree (R e : ℕ) (hR : Squarefree R) (he : e∣R) :
    (ArithmeticFunction.moebius (R/e) : ℝ) =
      (ArithmeticFunction.moebius R : ℝ)*(ArithmeticFunction.moebius e : ℝ) := by
  have hprod := Nat.mul_div_cancel' he
  have hc : e.Coprime (R/e) := Nat.coprime_of_squarefree_mul (by rwa [hprod])
  have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
  rw [hprod] at hm
  have hm' : (ArithmeticFunction.moebius R : ℝ) =
      (ArithmeticFunction.moebius e : ℝ)*(ArithmeticFunction.moebius (R/e) : ℝ) := by exact_mod_cast hm
  have hs : (ArithmeticFunction.moebius e : ℝ)^2=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hR.squarefree_of_dvd he)
  rw [hm']
  calc
    _ = (ArithmeticFunction.moebius e : ℝ)^2*(ArithmeticFunction.moebius (R/e) : ℝ) := by rw [hs,one_mul]
    _ = _ := by ring

lemma divisor_complement_cutoff (R e D : ℕ) (hR : 0<R) (he : e∣R) :
    D<R/e ↔ D*e<R := by
  have he0 := Nat.pos_of_dvd_of_pos he hR
  have hprod := Nat.div_mul_cancel he
  constructor
  · intro h
    have hm := Nat.mul_lt_mul_of_pos_right h he0
    rwa [hprod] at hm
  · intro h
    by_contra hn
    have hle : R/e≤D := by omega
    have hm := Nat.mul_le_mul_right e hle
    rw [hprod] at hm
    omega

/-- The complementary Möbius factor is retained rather than discarded. -/
theorem squarefree_moebius_tail_complement (R D : ℕ) (hR : 0<R) (hs : Squarefree R)
    (f : ℕ → ℝ) :
    (∑ d ∈ R.divisors.filter (fun d => D<d), (ArithmeticFunction.moebius d : ℝ)*f d) =
      (ArithmeticFunction.moebius R : ℝ)*
        ∑ e ∈ R.divisors.filter (fun e => D*e<R), (ArithmeticFunction.moebius e : ℝ)*f (R/e) := by
  rw [sum_filter,← Nat.sum_div_divisors R (fun d => if D<d then (ArithmeticFunction.moebius d : ℝ)*f d else 0),
    sum_filter,mul_sum]
  apply sum_congr rfl
  intro e he
  have hed := (Nat.mem_divisors.mp he).1
  simp only [divisor_complement_cutoff R e D hR hed,moebius_complement_squarefree R e hs hed]
  split_ifs <;> ring

noncomputable def divisorSideColour (n d : ℕ) : ℝ :=
  if d.minFac∣n+1 then 1 else -1

/-- The exact original tail has been rewritten, not merely majorized. -/
theorem roughLargeDivisorTail_complement (B D n : ℕ) (hn : 0<n) (hD : 1≤D) :
    roughLargeDivisorTail B D n =
      (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
        ∑ e ∈ (roughRadical B (n*(n+1))).divisors.filter
            (fun e => D*e<roughRadical B (n*(n+1))),
          (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e) := by
  have hm : n*(n+1)≠0 := by positivity
  have he : roughLargeDivisorTail B D n =
      ∑ d ∈ (n*(n+1)).divisors.filter (fun d => D<d ∧ B<d.minFac),
        (ArithmeticFunction.moebius d : ℝ)*divisorSideColour n d := by
    unfold roughLargeDivisorTail
    apply sum_congr rfl
    intro d hd
    obtain ⟨hd,hdD,hdB⟩ := mem_filter.mp hd
    have hd1 : 1<d := lt_of_le_of_lt hD hdD
    simp only [orientedDivisorTerm,if_pos (Nat.mem_divisors.mp hd).1,
      leastFactorTerm_eq_moebius,if_pos hd1,divisorSideColour]
  rw [he,rough_moebius_tail_radical B D _ hm hD]
  exact squarefree_moebius_tail_complement _ D (roughRadical_pos B _) (roughRadical_squarefree B _)
    (divisorSideColour n)

/-- The superlinear divisor cutoff puts every complementary index inside
an explicit sublinear interval. The weights still depend on n. -/
lemma roughRadical_complement_support (B H N n e : ℕ) (hH : 0<H) (hN : 0<N)
    (hn : 0<n) (hnN : n≤N)
    (he : e ∈ (roughRadical B (n*(n+1))).divisors.filter
      (fun e => (H*N)*e<roughRadical B (n*(n+1)))) :
    e ∈ Icc 1 ((N+1)/H) := by
  obtain ⟨hed,hlarge⟩ := mem_filter.mp he
  have hd := (Nat.mem_divisors.mp hed).1
  have he0 := Nat.pos_of_dvd_of_pos hd (roughRadical_pos B _)
  have hR : roughRadical B (n*(n+1))≤N*(N+1) :=
    (Nat.le_of_dvd (by positivity : 0<n*(n+1)) (roughRadical_dvd B _)).trans
      (Nat.mul_le_mul hnN (Nat.add_le_add_right hnN 1))
  have hmul : N*(H*e)≤N*(N+1) := by nlinarith
  have hsmall : H*e≤N+1 := (mul_le_mul_iff_right₀ hN).mp hmul
  exact mem_Icc.mpr ⟨he0,(Nat.le_div_iff_mul_le hH).mpr (by simpa only [Nat.mul_comm] using hsmall)⟩

noncomputable def complementedRoughTail (B H N n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ Icc 1 ((N+1)/H),
      if e∣roughRadical B (n*(n+1)) ∧ (H*N)*e<roughRadical B (n*(n+1)) then
        (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e)
      else 0

theorem roughLargeDivisorTail_eq_sublinear_complement (B H N n : ℕ) (hH : 0<H) (hN : 0<N)
    (hn : 0<n) (hnN : n≤N) :
    roughLargeDivisorTail B (H*N) n = complementedRoughTail B H N n := by
  rw [roughLargeDivisorTail_complement B (H*N) n hn (Nat.mul_pos hH hN)]
  unfold complementedRoughTail
  congr 1
  rw [← sum_filter]
  apply sum_congr _ (fun e he => rfl)
  ext e
  simp only [mem_filter,Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hed,_⟩,helt⟩
    exact ⟨roughRadical_complement_support B H N n e hH hN hn hnN
      (mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hed,(roughRadical_pos B _).ne'⟩,helt⟩),hed,helt⟩
  · rintro ⟨_,hed,helt⟩
    exact ⟨⟨hed,(roughRadical_pos B _).ne'⟩,helt⟩

lemma roughLargeDivisorTail_prefix_eq_complement (B H N : ℕ) (hH : 0<H) (hN : 0<N) :
    (∑ n ∈ range N, roughLargeDivisorTail B (H*N) (n+1)) =
      ∑ n ∈ range N, complementedRoughTail B H N (n+1) := by
  apply sum_congr rfl
  intro n hn
  exact roughLargeDivisorTail_eq_sublinear_complement B H N (n+1) hH hN (by omega)
    (by have := mem_range.mp hn; omega)

theorem complementedRoughTail_mixed_remainder_tendsto (B H : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) :
    Tendsto (fun N : ℕ => ((∑ n ∈ range N, complementedRoughTail (B N) (H N) N (n+1))-
      ∑ n ∈ range N, roughMixedDivisorTail (B N) (H N*N) (n+1))/N) atTop (𝓝 0) := by
  have ht := rough_one_sided_average_tendsto_zero B (fun N => H N*N)
  apply ht.congr'
  filter_upwards [hH.eventually_gt_atTop 0,eventually_gt_atTop (0 : ℕ)] with N hh hn
  rw [roughLargeDivisorTail_prefix_eq_complement (B N) (H N) N hh hn,sub_div]

/-- An exact arithmetic reduction to the sublinear complementary index
range. Cancellation of this input-dependent weighted sum is NOT asserted. -/
theorem density_iff_sublinear_complement (B H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (hlog : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hsmall : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, roughSmallDivisorSum (B N) (H N*N) (n+1))/N) atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N : ℕ =>
        (∑ n ∈ range N, complementedRoughTail (B N) (H N) N (n+1))/N) atTop (𝓝 0) := by
  rw [density_iff_rough_mixed_tail_of_small_and_subpower B (fun N => H N*N) hlog hsmall]
  have he := complementedRoughTail_mixed_remainder_tendsto B H hH
  constructor
  · intro h
    have ht := h.add he
    simp only [add_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro h
    have ht := h.sub he
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring

theorem exists_sublinear_complement_criterion :
    ∃ B H : ℕ → ℕ, Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      ({n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
        Tendsto (fun N : ℕ =>
          (∑ n ∈ range N, complementedRoughTail (B N) (H N) N (n+1))/N) atTop (𝓝 0)) := by
  obtain ⟨B,H,hB,hH,hlog,_,hsmall⟩ := exists_subpower_superlinear_rough_cutoff
  exact ⟨B,H,hB,hH,hlog,density_iff_sublinear_complement B H hH hlog hsmall⟩

#print axioms rough_moebius_tail_radical
#print axioms squarefree_moebius_tail_complement
#print axioms roughLargeDivisorTail_complement
#print axioms roughLargeDivisorTail_eq_sublinear_complement
#print axioms exists_sublinear_complement_criterion
end Erdos371
