import Submission.Spec

/-! Explicit target-size bounds for the primitive quartic construction. -/

namespace Erdos322.QuarticSuperlog

lemma good_system_quantitative (r : ℕ) : ∃ (q : Fin r → ℕ) (a : Fin r → EZ),
    (∀ i, 1 < q i) ∧ (∀ i, (a i).norm = (q i : ℤ)) ∧
    Pairwise (Function.onFun Nat.Coprime q) ∧
    (∀ i j, IsCoprime (a i) (star (a j))) ∧
    4 * (∏ i, q i) ≤ 4 ^ (3 ^ r) := by
  induction r with
  | zero =>
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · norm_num
  | succ r ih =>
    obtain ⟨q,a,hq,ha,hqq,haa,hsize⟩ := ih
    let B := ∏ i, q i
    have hB : 0 < B := Finset.prod_pos fun i _ ↦ (by have := hq i; omega)
    let Q := 1 + 12 * B ^ 2
    let A : EZ := ⟨1, 2 * B⟩
    have hQ : 1 < Q := by dsimp [Q]; nlinarith [sq_pos_of_pos hB]
    have hA : A.norm = (Q : ℤ) := by simp [A, Q, Zsqrtd.norm]; ring
    have hQi (i : Fin r) : Nat.Coprime Q (q i) :=
      (new_norm_coprime B).of_dvd_right (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    refine ⟨Fin.cons Q q, Fin.cons A a, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; refine Fin.cases hQ (fun j ↦ hq j) i
    · intro i; refine Fin.cases hA (fun j ↦ ha j) i
    · intro i
      induction i using Fin.cases with
      | zero =>
        intro j
        induction j using Fin.cases with
        | zero => exact fun h ↦ False.elim (h rfl)
        | succ j => exact fun _ ↦ hQi j
      | succ i =>
        intro j
        induction j using Fin.cases with
        | zero => exact fun _ ↦ (hQi i).symm
        | succ j =>
          intro hij
          exact hqq (by intro he; exact hij (congrArg Fin.succ he))
    · intro i j
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · refine Fin.cases (new_element_coprime B) (fun j' ↦ ?_) j
        apply norm_cast_coprime
        simp only [Fin.cons_zero, Fin.cons_succ, hA, ha]
        exact (hQi j').isCoprime
      · refine Fin.cases ?_ (fun j' ↦ haa i' j') j
        apply norm_cast_coprime
        simp only [Fin.cons_zero, Fin.cons_succ, ha, hA]
        exact (hQi i').symm.isCoprime
    · simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      change 4 * (Q * B) ≤ 4 ^ (3 ^ (r + 1))
      have hcube : B ≤ B ^ 3 := Nat.le_pow (by decide)
      calc
        4 * (Q * B) ≤ (4 * B) ^ 3 := by dsimp [Q]; nlinarith
        _ ≤ (4 ^ (3 ^ r)) ^ 3 := Nat.pow_le_pow_left hsize 3
        _ = 4 ^ (3 ^ (r + 1)) := by rw [← pow_mul, pow_succ]

/-- A quantitative version of the superlogarithmic lower bound. The target is
at most doubly exponential in `r`, while the count is at least exponential in `r²`. -/
theorem quartic_quantitative_peaks (r : ℕ) :
    ∃ n : ℕ, 2 * 2 ^ (4 * 3 ^ r) + 1 ≤ n ∧
      n ≤ 3 * 4 ^ (12 * 9 ^ r) ∧
      3 ^ (r * (r + 1)) ≤ Erdos322.primitiveRepresentationCount 4 n := by
  obtain ⟨q,a,hq,ha,hqq,haa,hsize⟩ := good_system_quantitative (r + 1)
  let B := ∏ i, q i
  have hpos : 0 < B := Finset.prod_pos fun i _ ↦ by have := hq i; omega
  have hB : 2 ≤ B := by
    have hd : q 0 ∣ B := Finset.dvd_prod_of_mem q (Finset.mem_univ 0)
    exact (hq 0).trans_le (Nat.le_of_dvd hpos hd)
  have hBupper : B ≤ 4 ^ (3 ^ (r + 1)) := by change 4 * B ≤ _ at hsize; omega
  refine ⟨2 * B ^ (4 * 3 ^ r) + 1, ?_, ?_, ?_⟩
  · gcongr
  · have hp : 1 ≤ B ^ (4 * 3 ^ r) := one_le_pow₀ (by omega)
    calc
      2 * B ^ (4 * 3 ^ r) + 1 ≤ 3 * B ^ (4 * 3 ^ r) := by omega
      _ ≤ 3 * (4 ^ (3 ^ (r + 1))) ^ (4 * 3 ^ r) := by gcongr
      _ = 3 * 4 ^ (12 * 9 ^ r) := by
        rw [← pow_mul]
        congr 2
        calc
          3 ^ (r + 1) * (4 * 3 ^ r) = 12 * (3 ^ r * 3 ^ r) := by rw [pow_succ]; ring
          _ = 12 * 9 ^ r := by rw [← mul_pow]; norm_num
  · calc
      3 ^ (r * (r + 1)) = (3 ^ r) ^ (r + 1) := pow_mul _ _ _
      _ ≤ (3 ^ r + 1) ^ (r + 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ Erdos322.primitiveRepresentationCount 4 (2 * B ^ (4 * 3 ^ r) + 1) :=
        system_lower_bound q a hq ha hqq haa (3 ^ r)

lemma loglog_bound_of_target_bound {r n : ℕ} (hr : 1 ≤ r) (hn : 3 ≤ n)
    (hupper : n ≤ 3 * 4 ^ (12 * 9 ^ r)) :
    0 ≤ Real.log (Real.log n) ∧ Real.log (Real.log n) ≤ 73 * (r : ℝ) := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hlower : 1 ≤ Real.log (n : ℝ) := by
    apply (Real.le_log_iff_exp_le hnpos).mpr
    exact Real.exp_one_lt_three.le.trans hnreal
  have hp : 1 ≤ (9 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have hlogupper : Real.log (n : ℝ) ≤ 64 * (9 : ℝ) ^ r := by
    calc
      Real.log (n : ℝ) ≤ Real.log (3 * (4 : ℝ) ^ (12 * 9 ^ r)) := by
        apply Real.log_le_log hnpos
        exact_mod_cast hupper
      _ = Real.log 3 + (12 * 9 ^ r : ℕ) * Real.log 4 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      _ ≤ 3 + (12 * 9 ^ r : ℕ) * 4 := by
        gcongr
        · exact Real.log_le_self (by norm_num)
        · exact Real.log_le_self (by norm_num)
      _ ≤ 64 * (9 : ℝ) ^ r := by push_cast; nlinarith
  refine ⟨Real.log_nonneg hlower, ?_⟩
  calc
    Real.log (Real.log n) ≤ Real.log (64 * (9 : ℝ) ^ r) :=
      Real.log_le_log (by linarith) hlogupper
    _ = Real.log 64 + (r : ℝ) * Real.log 9 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    _ ≤ 64 + (r : ℝ) * 9 := by
      gcongr
      · exact Real.log_le_self (by norm_num)
      · exact Real.log_le_self (by norm_num)
    _ ≤ 73 * (r : ℝ) := by
      have hrreal : (1 : ℝ) ≤ r := by exact_mod_cast hr
      linarith

/-- Explicit quasipolylogarithmic peaks for the primitive quartic count. -/
theorem primitive_quartic_loglog_square :
    {n : ℕ | (2 : ℝ) ^ ((Real.log (Real.log n)) ^ 2 / 10000) <
      Erdos322.primitiveRepresentationCount 4 n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  let r := M + 1
  have hr : 1 ≤ r := by dsimp [r]; omega
  obtain ⟨n,hnlow,hnupper,hncount⟩ := quartic_quantitative_peaks r
  have htwo : 1 ≤ 2 ^ (4 * 3 ^ r) := one_le_pow₀ (by omega)
  have hn : 3 ≤ n := by omega
  obtain ⟨hllpos,hllupper⟩ := loglog_bound_of_target_bound hr hn hnupper
  have hrreal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsquare : (Real.log (Real.log n)) ^ 2 ≤ (73 * (r : ℝ)) ^ 2 :=
    (sq_le_sq₀ hllpos (by positivity)).mpr hllupper
  have hexp : (Real.log (Real.log n)) ^ 2 / 10000 < (r * (r + 1) : ℕ) := by
    push_cast
    nlinarith [sq_nonneg (r : ℝ)]
  refine ⟨n, ?_, ?_⟩
  · change (2 : ℝ) ^ ((Real.log (Real.log n)) ^ 2 / 10000) < _
    calc
      (2 : ℝ) ^ ((Real.log (Real.log n)) ^ 2 / 10000) <
          (2 : ℝ) ^ ((r * (r + 1) : ℕ) : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
      _ = (2 : ℝ) ^ (r * (r + 1)) := Real.rpow_natCast _ _
      _ ≤ (3 : ℝ) ^ (r * (r + 1)) := by gcongr; norm_num
      _ ≤ Erdos322.primitiveRepresentationCount 4 n := by exact_mod_cast hncount
  · have h3 := Nat.lt_pow_self (n := r) (by decide : 1 < 3)
    have h2 := Nat.lt_pow_self (n := 4 * 3 ^ r) (by decide : 1 < 2)
    have hrM : M < r := by dsimp [r]; omega
    omega

/-- The same explicit lower bound holds without the primitivity restriction. -/
theorem quartic_loglog_square :
    {n : ℕ | (2 : ℝ) ^ ((Real.log (Real.log n)) ^ 2 / 10000) <
      Erdos322.representationCount 4 n}.Infinite := by
  apply primitive_quartic_loglog_square.mono
  intro n hn
  have hle : (Erdos322.primitiveRepresentationCount 4 n : ℝ) ≤
      Erdos322.representationCount 4 n := by
    exact_mod_cast Erdos322.primitiveRepresentationCount_le 4 n
  exact lt_of_lt_of_le hn hle

end Erdos322.QuarticSuperlog
