import FormalConjecturesUtil

/-! Exact checks of a proposed local recurrence, not a disproof of Erdős Problem 970. -/
namespace GreedyCheck

def Covered (P : Finset (ℕ × ℕ)) (i : ℕ) : Prop :=
  ∃ pr ∈ P, i % pr.1 = pr.2 % pr.1

instance (P : Finset (ℕ × ℕ)) (i : ℕ) : Decidable (Covered P i) := by
  unfold Covered
  infer_instance

def fiveClasses : Finset (ℕ × ℕ) := {(7, 0), (5, 1), (11, 2), (3, 0), (2, 0)}

theorem jump_counterexample :
    (∀ i : Fin 5, Covered fiveClasses i.val) ∧
    ¬Covered fiveClasses 5 ∧
    (∀ i : Fin 17, Covered (insert (13, 5) fiveClasses) i.val) ∧
    ¬Covered (insert (13, 5) fiveClasses) 17 ∧
    fiveClasses.card = 5 ∧
    (∀ pr ∈ fiveClasses, pr.1.Prime) ∧
    Nat.Prime 13 ∧ 2 * fiveClasses.card + 1 < 17 - 5 := by
  decide


/-- The zero classes for primes through `x` cover `[-x,x]` except for `-1` and `1`. -/
theorem prime_covers_mirrored_interval (x : ℕ) (hx : 2 ≤ x) (z : ℤ)
    (hl : -(x : ℤ) ≤ z) (hu : z ≤ x) (hz1 : z ≠ 1) (hzn1 : z ≠ -1) :
    ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ (p : ℤ) ∣ z := by
  by_cases hz0 : z = 0
  · exact ⟨2, Nat.prime_two, hx, by simp [hz0]⟩
  have hzabs : z.natAbs ≤ x := by
    have hh : |z| ≤ (x : ℤ) := abs_le.mpr ⟨hl, hu⟩
    rw [Int.abs_eq_natAbs] at hh
    exact_mod_cast hh
  have hzne1 : z.natAbs ≠ 1 := by
    intro hh
    rcases Int.natAbs_eq_iff.mp hh with hh | hh
    · exact hz1 (by simpa using hh)
    · exact hzn1 (by simpa using hh)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hzne1
  exact ⟨p, hp, (Nat.le_of_dvd (Int.natAbs_pos.mpr hz0) hpd).trans hzabs,
    Int.natCast_dvd.mpr hpd⟩

/-- A first hole at `1` can be filled by one fresh prime, extending the cover through `x`.
The previous cover uses only `π(x) + 1` primes. This is not a quadratic counterexample. -/
theorem long_last_step (x : ℕ) (hx : 2 ≤ x) :
    ∃ A : Finset ℕ, ∃ r : ℕ → ℤ, ∃ q : ℕ,
      (∀ p ∈ A, p.Prime) ∧ A.card = x.primeCounting + 1 ∧ q.Prime ∧ q ∉ A ∧
      (∀ z : ℤ, -(x : ℤ) ≤ z → z < 1 → ∃ p ∈ A, (p : ℤ) ∣ z - r p) ∧
      (∀ p ∈ A, ¬(p : ℤ) ∣ 1 - r p) ∧
      (∀ z : ℤ, -(x : ℤ) ≤ z → z ≤ x →
        ∃ p ∈ insert q A, (p : ℤ) ∣ z - (if p = q then 1 else r p)) := by
  classical
  let P := (Finset.range (x + 1)).filter Nat.Prime
  obtain ⟨q, hqx, hq⟩ := Nat.exists_infinite_primes (2 * x + 3)
  obtain ⟨t, htq, ht⟩ := Nat.exists_infinite_primes (q + 1)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ x := by
    have hh := Finset.mem_filter.mp hp
    exact ⟨hh.2, by have := Finset.mem_range.mp hh.1; omega⟩
  have hqP : q ∉ P := by intro hp; have := (hP q hp).2; omega
  have htP : t ∉ P := by intro hp; have := (hP t hp).2; omega
  have htne : t ≠ q := by omega
  let A := insert q P
  let r : ℕ → ℤ := fun p => if p = q then -1 else 0
  have hAprime (p : ℕ) (hp : p ∈ A) : p.Prime := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hq
    · exact (hP p hp).1
  have hpcard : P.card = x.primeCounting := by
    simp only [P, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hAcard : A.card = x.primeCounting + 1 := by
    simp only [A, Finset.card_insert_of_notMem hqP, hpcard]
  have htA : t ∉ A := by simp only [A, Finset.mem_insert, not_or]; exact ⟨htne, htP⟩
  have hplain (z : ℤ) (hl : -(x : ℤ) ≤ z) (hu : z ≤ x)
      (hz1 : z ≠ 1) (hzn1 : z ≠ -1) : ∃ p ∈ P, (p : ℤ) ∣ z := by
    obtain ⟨p, hp, hpx, hpd⟩ := prime_covers_mirrored_interval x hx z hl hu hz1 hzn1
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩, hpd⟩
  refine ⟨A, r, t, hAprime, hAcard, ht, htA, ?_, ?_, ?_⟩
  · intro z hl hu
    by_cases hz : z = -1
    · refine ⟨q, Finset.mem_insert_self q P, ?_⟩
      simp [r, hz]
    · obtain ⟨p, hp, hpd⟩ := hplain z hl (by omega) (by omega) hz
      have hpq : p ≠ q := by rintro rfl; exact hqP hp
      exact ⟨p, Finset.mem_insert_of_mem hp, by simpa [r, hpq] using hpd⟩
  · intro p hp hdiv
    change p ∈ insert q P at hp
    have hpCases : p = q ∨ p ∈ P := Finset.mem_insert.mp hp
    rcases hpCases with hpq | hp0
    · subst p
      have hdiv' : (q : ℤ) ∣ 2 := by simpa [r] using hdiv
      have hh : q ∣ 2 := by exact_mod_cast hdiv'
      have hh' := Nat.le_of_dvd (by decide : 0 < 2) hh
      omega
    · have hpq : p ≠ q := by rintro rfl; exact hqP hp0
      have hdiv' : (p : ℤ) ∣ 1 := by simpa [r, hpq] using hdiv
      have hh : p ∣ 1 := by exact_mod_cast hdiv'
      exact (hP p hp0).1.not_dvd_one hh
  · intro z hl hu
    by_cases hz : z = 1
    · refine ⟨t, Finset.mem_insert_self t A, ?_⟩
      simp [hz]
    by_cases hzn : z = -1
    · refine ⟨q, Finset.mem_insert_of_mem (Finset.mem_insert_self q P), ?_⟩
      simp [r, hzn, Ne.symm htne]
    · obtain ⟨p, hp, hpd⟩ := hplain z hl hu hz hzn
      have hpq : p ≠ q := by rintro rfl; exact hqP hp
      have hpt : p ≠ t := by rintro rfl; exact htP hp
      refine ⟨p, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp), ?_⟩
      simpa [r, hpq, hpt] using hpd


/-- The jumps in `long_last_step` are not bounded by any constant times the prime count. -/
theorem unbounded_step_ratio (C : ℝ) (hC : 0 < C) :
    ∃ x : ℕ, 2 ≤ x ∧ C * (x.primeCounting + 1 : ℕ) < (x : ℝ) := by
  have hcheb : ∀ᶠ x : ℕ in Filter.atTop,
      (x.primeCounting : ℝ) ≤ (Real.log 4 + 1) * (x : ℝ) / Real.log x := by
    have hh := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
    simpa using hh
  have hlog : ∀ᶠ x : ℕ in Filter.atTop,
      2 * C * (Real.log 4 + 1) < Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_gt_atTop _)
  have hxlarge : ∀ᶠ x : ℕ in Filter.atTop, 2 * C < (x : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (Filter.eventually_gt_atTop _)
  obtain ⟨x, hxCheb, hxlog, hxlarge, hx2⟩ :=
    (hcheb.and (hlog.and (hxlarge.and (Filter.eventually_ge_atTop (2 : ℕ))))).exists
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hhalf : 2 * C * x.primeCounting < (x : ℝ) := by
    calc
      2 * C * x.primeCounting ≤ 2 * C *
          ((Real.log 4 + 1) * (x : ℝ) / Real.log x) :=
        mul_le_mul_of_nonneg_left hxCheb (by positivity)
      _ < (x : ℝ) := by
        rw [← mul_div_assoc, div_lt_iff₀ hlogpos]
        have hh := mul_lt_mul_of_pos_right hxlog hxpos
        nlinarith
  refine ⟨x, hx2, ?_⟩
  push_cast
  nlinarith

#print axioms jump_counterexample
#print axioms long_last_step
#print axioms unbounded_step_ratio
end GreedyCheck
