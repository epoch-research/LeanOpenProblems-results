import FormalConjecturesUtil
import Submission.BinomialRelaxationEquivalence

/-! A diagnostic for bounded-local-degree elimination arguments. This is an
integer optimization problem, not a graph extremal problem. Its quadratic
power-chain constraints have an optimum asymptotic to n^(sqrt 2). -/

open Filter Asymptotics
open scoped Topology
namespace Erdos713QuadraticOptimizationDiagnostic
set_option maxHeartbeats 1000000

noncomputable def numerator (n : ℕ) : ℕ := ⌊Real.sqrt 2 * (n : ℝ)⌋₊
noncomputable def exponent (n : ℕ) : ℝ := (numerator n : ℝ) / n
noncomputable def relaxation (n : ℕ) : ℝ := (n : ℝ) ^ exponent n
noncomputable def optimum (n : ℕ) : ℕ := if n = 0 then 0 else ⌊relaxation n⌋₊

/-- An intermediate formulation with an explicitly selected array index. -/
def Feasible (n m : ℕ) : Prop :=
  m ≤ n*n ∧ ∃ p : Fin (2*n+1),
    p.val*p.val ≤ 2*(n*n) ∧ 2*(n*n) < (p.val+1)*(p.val+1) ∧
    ∃ x : Fin (n+1) → ℕ, ∃ y : Fin (2*n+1) → ℕ,
      x 0 = 1 ∧ y 0 = 1 ∧
      (∀ i : Fin n, x i.succ = m*x i.castSucc) ∧
      (∀ i : Fin (2*n), y i.succ = n*y i.castSucc) ∧
      x (Fin.last n) ≤ y p

/-- A formulation without variable-index array lookup. All atomic equalities
and inequalities are polynomial of total degree at most two, with integer
coefficients of absolute value at most two (including n among the inputs).
The counter array t supplies the selector indices using unit increments. -/
def QuadraticFeasible (n m : ℕ) : Prop :=
  m ≤ n*n ∧ ∃ p : ℕ,
    p*p ≤ 2*(n*n) ∧ 2*(n*n) < (p+1)*(p+1) ∧
    ∃ x : Fin (n+1) → ℕ, ∃ y b t : Fin (2*n+1) → ℕ,
      x 0 = 1 ∧ y 0 = 1 ∧ t 0 = 0 ∧
      (∀ i : Fin n, x i.succ = m*x i.castSucc) ∧
      (∀ i : Fin (2*n), y i.succ = n*y i.castSucc) ∧
      (∀ i : Fin (2*n), t i.succ = t i.castSucc+1) ∧
      (∀ i, b i*b i = b i) ∧
      (∑ i, b i) = 1 ∧ p = (∑ i, b i*t i) ∧
      x (Fin.last n) ≤ (∑ i, b i*y i)

/-- A sum represented by local accumulator equations. -/
def SumChain {k : ℕ} (a : Fin k → ℕ) (s : Fin (k+1) → ℕ) : Prop :=
  s 0 = 0 ∧ ∀ i : Fin k, s i.succ = s i.castSucc+a i

lemma SumChain.last_eq {k : ℕ} {a : Fin k → ℕ} {s : Fin (k+1) → ℕ}
    (h : SumChain a s) : s (Fin.last k) = ∑ i, a i := by
  have hs (i : Fin (k+1)) : s i = Fin.partialSum a i := by
    induction i using Fin.induction with
    | zero => simpa using h.1
    | succ i ih => rw [h.2 i,Fin.partialSum_succ,ih]
  rw [hs]
  change (List.take k (List.ofFn a)).sum = _
  rw [List.take_of_length_le (by simp),List.sum_ofFn]

lemma sumChain_partialSum {k : ℕ} (a : Fin k → ℕ) : SumChain a (Fin.partialSum a) :=
  ⟨Fin.partialSum_zero a,Fin.partialSum_succ a⟩

/-- The fully local formulation: after unfolding SumChain, every atomic
constraint has at most four scalar variables and total degree at most two.
There are O(n) variables and constraints; variable values are not Boolean. -/
def LocalQuadraticFeasible (n m : ℕ) : Prop :=
  m ≤ n*n ∧ ∃ p : ℕ,
    p*p ≤ 2*(n*n) ∧ 2*(n*n) < (p+1)*(p+1) ∧
    ∃ x : Fin (n+1) → ℕ, ∃ y b t : Fin (2*n+1) → ℕ,
      x 0 = 1 ∧ y 0 = 1 ∧ t 0 = 0 ∧
      (∀ i : Fin n, x i.succ = m*x i.castSucc) ∧
      (∀ i : Fin (2*n), y i.succ = n*y i.castSucc) ∧
      (∀ i : Fin (2*n), t i.succ = t i.castSucc+1) ∧
      (∀ i, b i*b i = b i) ∧
      ∃ r v w : Fin ((2*n+1)+1) → ℕ,
        SumChain b r ∧ SumChain (fun i => b i*t i) v ∧
        SumChain (fun i => b i*y i) w ∧
        r (Fin.last (2*n+1)) = 1 ∧ p = v (Fin.last (2*n+1)) ∧
        x (Fin.last n) ≤ w (Fin.last (2*n+1))

lemma local_quadratic_iff (n m : ℕ) :
    LocalQuadraticFeasible n m ↔ QuadraticFeasible n m := by
  constructor
  · rintro ⟨hm,p,hp,hp',x,y,b,t,hx,hy,ht,hxs,hys,hts,hb,r,v,w,hr,hv,hw,hs,he,hxy⟩
    rw [hr.last_eq] at hs
    rw [hv.last_eq] at he
    rw [hw.last_eq] at hxy
    exact ⟨hm,p,hp,hp',x,y,b,t,hx,hy,ht,hxs,hys,hts,hb,hs,he,hxy⟩
  · rintro ⟨hm,p,hp,hp',x,y,b,t,hx,hy,ht,hxs,hys,hts,hb,hs,he,hxy⟩
    refine ⟨hm,p,hp,hp',x,y,b,t,hx,hy,ht,hxs,hys,hts,hb,
      Fin.partialSum b,Fin.partialSum (fun i => b i*t i),Fin.partialSum (fun i => b i*y i),
      sumChain_partialSum _,sumChain_partialSum _,sumChain_partialSum _,?_,?_,?_⟩
    · rwa [(sumChain_partialSum _).last_eq]
    · rwa [(sumChain_partialSum _).last_eq]
    · rwa [(sumChain_partialSum _).last_eq]

lemma onehot_exists {ι : Type*} [Fintype ι] (b : ι → ℕ)
    (hs : ∑ i, b i = 1) : ∃ j, b j = 1 ∧ ∀ i, i ≠ j → b i = 0 := by
  classical
  obtain ⟨j,_,hjpos⟩ := Finset.sum_pos_iff.mp (show 0 < ∑ i, b i by omega)
  have hjle := Finset.single_le_sum (s := Finset.univ) (f := b)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  have hj : b j = 1 := by omega
  have he := Finset.sum_erase_add Finset.univ b (Finset.mem_univ j)
  have he0 : ∑ i ∈ Finset.univ.erase j, b i = 0 := by omega
  refine ⟨j,hj,?_⟩
  intro i hi
  exact Finset.sum_eq_zero_iff.mp he0 i (by simpa using hi)

lemma counter_chain {k : ℕ} {t : Fin (k+1) → ℕ} (ht : t 0 = 0)
    (hstep : ∀ i : Fin k, t i.succ = t i.castSucc+1) (i : Fin (k+1)) :
    t i = i.val := by
  induction i using Fin.induction with
  | zero => exact ht
  | succ i ih => simpa using (hstep i).trans (congrArg (·+1) ih)

lemma quadratic_iff (n m : ℕ) : QuadraticFeasible n m ↔ Feasible n m := by
  classical
  constructor
  · rintro ⟨hm,p,hp,hp',x,y,b,t,hx,hy,ht,hxs,hys,hts,_,hs,hpEq,hxy⟩
    obtain ⟨j,hj,hother⟩ := onehot_exists b hs
    have hsum (a : Fin (2*n+1) → ℕ) : (∑ i, b i*a i) = a j := by
      rw [Finset.sum_eq_single j]
      · simp [hj]
      · intro i _ hi
        simp [hother i hi]
      · simp
    rw [hsum] at hpEq hxy
    rw [counter_chain ht hts j] at hpEq
    subst p
    exact ⟨hm,j,hp,hp',x,y,hx,hy,hxs,hys,hxy⟩
  · rintro ⟨hm,p,hp,hp',x,y,hx,hy,hxs,hys,hxy⟩
    let b : Fin (2*n+1) → ℕ := fun i => if i = p then 1 else 0
    have hsum (a : Fin (2*n+1) → ℕ) : (∑ i, b i*a i) = a p := by
      simp [b,ite_mul]
    refine ⟨hm,p.val,hp,hp',x,y,b,(fun i => i.val),hx,hy,rfl,hxs,hys,
      (fun _ => rfl),?_,?_,?_,?_⟩
    · intro i
      by_cases hi : i = p <;> simp [b,hi]
    · simp [b]
    · exact (hsum _).symm
    · rwa [hsum]

lemma numerator_bounds (n : ℕ) :
    (numerator n : ℝ) ≤ Real.sqrt 2*n ∧ Real.sqrt 2*n < numerator n+1 := by
  exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩

lemma numerator_le (n : ℕ) : numerator n ≤ 2*n := by
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hh := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hb := (numerator_bounds n).1
  have : (numerator n : ℝ) ≤ 2*n := hb.trans hh
  exact_mod_cast this

lemma numerator_square (n : ℕ) :
    numerator n*numerator n ≤ 2*(n*n) ∧
      2*(n*n) < (numerator n+1)*(numerator n+1) := by
  have hs : (Real.sqrt 2*(n : ℝ))^2 = 2*(n : ℝ)^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hb := numerator_bounds n
  have hn : (0 : ℝ) ≤ numerator n := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ Real.sqrt 2*n := by positivity
  constructor
  · have hh : (numerator n : ℝ)*(numerator n : ℝ) ≤ 2*((n : ℝ)*n) := by nlinarith
    exact_mod_cast hh
  · have hh : 2*((n : ℝ)*n) < ((numerator n : ℝ)+1)*((numerator n : ℝ)+1) := by
      nlinarith
    exact_mod_cast hh

lemma numerator_unique {n p : ℕ} (hp : p*p ≤ 2*(n*n))
    (hp' : 2*(n*n) < (p+1)*(p+1)) : p = numerator n := by
  have hb := numerator_square n
  nlinarith

lemma power_chain {b k : ℕ} {x : Fin (k+1) → ℕ} (hx : x 0 = 1)
    (hstep : ∀ i : Fin k, x i.succ = b*x i.castSucc) (i : Fin (k+1)) :
    x i = b^i.val := by
  induction i using Fin.induction with
  | zero => simpa using hx
  | succ i ih => simpa [pow_succ, Nat.mul_comm] using (hstep i).trans (congrArg (b*·) ih)

lemma relaxation_power {n : ℕ} (hn : 0 < n) :
    relaxation n ^ n = (n : ℝ) ^ numerator n := by
  unfold relaxation exponent
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n),
    div_mul_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), Real.rpow_natCast]

lemma power_le_iff {n m : ℕ} (hn : 0 < n) :
    m^n ≤ n^numerator n ↔ m ≤ ⌊relaxation n⌋₊ := by
  have hg : 0 ≤ relaxation n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Nat.le_floor_iff hg]
  have hh := relaxation_power hn
  constructor
  · intro h
    have hm : (m : ℝ)^n ≤ (n : ℝ)^numerator n := by exact_mod_cast h
    rw [← hh] at hm
    exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg m) hg hn.ne').mp hm
  · intro h
    have hm := pow_le_pow_left₀ (Nat.cast_nonneg m) h n
    rw [hh] at hm
    exact_mod_cast hm

lemma relaxation_le {n : ℕ} (hn : 0 < n) : relaxation n ≤ (n : ℝ)^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : exponent n ≤ 2 := by
    unfold exponent
    apply (div_le_iff₀ hnR).mpr
    exact_mod_cast numerator_le n
  simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hn1 he

lemma feasible_iff {n m : ℕ} (hn : 0 < n) : Feasible n m ↔ m ≤ optimum n := by
  simp only [optimum, if_neg hn.ne']
  constructor
  · rintro ⟨_,p,hp,hp',x,y,hx,hy,hxs,hys,hxy⟩
    have he := numerator_unique hp hp'
    have hx' := power_chain hx hxs (Fin.last n)
    have hy' := power_chain hy hys p
    rw [hx',hy',he] at hxy
    exact (power_le_iff hn).mp hxy
  · intro hm
    have hpow := (power_le_iff hn).mpr hm
    have hcap : m ≤ n*n := by
      have hh := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (exponent n))
      change (⌊relaxation n⌋₊ : ℝ) ≤ relaxation n at hh
      have hmR : (m : ℝ) ≤ ⌊relaxation n⌋₊ := by exact_mod_cast hm
      have hb := relaxation_le hn
      have : (m : ℝ) ≤ (n : ℝ)*n := by nlinarith
      exact_mod_cast this
    let p : Fin (2*n+1) := ⟨numerator n, by have := numerator_le n; omega⟩
    refine ⟨hcap,p,(numerator_square n).1,(numerator_square n).2,
      (fun i => m^i.val),(fun i => n^i.val),by simp,by simp,?_,?_,hpow⟩
    · intro i
      simp [pow_succ, Nat.mul_comm]
    · intro i
      simp [pow_succ, Nat.mul_comm]

/-- `optimum` is the global integer optimum, including at order zero. -/
theorem is_optimum (n : ℕ) :
    Feasible n (optimum n) ∧ ∀ m, Feasible n m → m ≤ optimum n := by
  by_cases hn : n = 0
  · subst n
    simp only [optimum]
    constructor
    · refine ⟨by simp,0,by simp,by simp,(fun _ => 1),(fun _ => 1),rfl,rfl,?_,?_,by simp⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
    · intro m hm
      exact hm.1
  · have hp := Nat.pos_of_ne_zero hn
    exact ⟨(feasible_iff hp).mpr le_rfl,fun m => (feasible_iff hp).mp⟩

/-- Exact global maximization for the actual quadratic formulation. -/
theorem quadratic_is_optimum (n : ℕ) :
    QuadraticFeasible n (optimum n) ∧
      ∀ m, QuadraticFeasible n m → m ≤ optimum n :=
  ⟨(quadratic_iff n _).mpr (is_optimum n).1,
    fun m hm => (is_optimum n).2 m ((quadratic_iff n m).mp hm)⟩

/-- The same global optimum is realized by the bounded-arity formulation. -/
theorem local_quadratic_is_optimum (n : ℕ) :
    LocalQuadraticFeasible n (optimum n) ∧
      ∀ m, LocalQuadraticFeasible n m → m ≤ optimum n :=
  ⟨(local_quadratic_iff n _).mpr (quadratic_is_optimum n).1,
    fun m hm => (quadratic_is_optimum n).2 m ((local_quadratic_iff n m).mp hm)⟩

lemma normalized_bounds {n : ℕ} (hn : 0 < n) :
    (n : ℝ)^(-(1 : ℝ)/n) ≤ relaxation n/(n : ℝ)^Real.sqrt 2 ∧
      relaxation n/(n : ℝ)^Real.sqrt 2 ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb := numerator_bounds n
  have helo : -(1 : ℝ)/n ≤ exponent n-Real.sqrt 2 := by
    unfold exponent
    apply (mul_le_mul_iff_left₀ hnR).mp
    field_simp
    nlinarith
  have hehi : exponent n-Real.sqrt 2 ≤ 0 := by
    have hh : exponent n ≤ Real.sqrt 2 := by
      exact (div_le_iff₀ hnR).mpr hb.1
    linarith
  have he : relaxation n/(n : ℝ)^Real.sqrt 2 = (n : ℝ)^(exponent n-Real.sqrt 2) := by
    rw [Real.rpow_sub hnR]
    rfl
  rw [he]
  exact ⟨Real.rpow_le_rpow_of_exponent_le hn1 helo,
    by simpa using Real.rpow_le_rpow_of_exponent_le hn1 hehi⟩

lemma relaxation_asymptotic :
    relaxation ~[atTop] (fun n : ℕ => (n : ℝ)^Real.sqrt 2) := by
  apply (isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).ne')).mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_rpow_neg_div.comp tendsto_natCast_atTop_atTop) tendsto_const_nhds
    ((eventually_gt_atTop (0 : ℕ)).mono fun n hn => (normalized_bounds hn).1)
    ((eventually_gt_atTop (0 : ℕ)).mono fun n hn => (normalized_bounds hn).2)

/-- Exact irrational power growth occurs despite the quadratic local
constraints and the exact global maximum property. No graph realization
of this optimization problem is claimed. -/
theorem optimum_asymptotic :
    (fun n : ℕ => (optimum n : ℝ)) ~[atTop]
      (fun n : ℕ => (1 : ℝ)*(n : ℝ)^Real.sqrt 2) := by
  have hg : Tendsto relaxation atTop atTop :=
    relaxation_asymptotic.symm.tendsto_atTop
      ((tendsto_rpow_atTop (Real.sqrt_pos.mpr (by norm_num))).comp tendsto_natCast_atTop_atTop)
  have hf := (isEquivalent_nat_floor.comp_tendsto hg).trans relaxation_asymptotic
  have he : (fun n : ℕ => (optimum n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (⌊relaxation n⌋₊ : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp [optimum,hn.ne']
  simpa only [one_mul] using he.isEquivalent.trans hf

/-- In particular no sharp single-binomial elimination is possible here. -/
theorem no_binomial_relaxation :
    ¬ Erdos713BinomialRelaxation.HasBinomialRelaxation optimum := by
  intro h
  exact irrational_sqrt_two (Erdos713BinomialRelaxation.rational_of_relaxation
    (Real.sqrt_pos.mpr (by norm_num)) (by norm_num) optimum_asymptotic h)

/-- More generally, no fixed finite polynomial relaxation in just n and m
can be both eventually feasible and constant-factor sharp for this optimum. -/
theorem no_sharp_fixed_relaxation {I : Type*} [Fintype I]
    (s : I → Finset (ℕ × ℕ)) (hs : ∀ i, (s i).Nonempty)
    (a : I → (ℕ × ℕ) → ℝ) (ha : ∀ i p, p ∈ s i → a i p ≠ 0)
    (hfeas : ∀ i, ∀ᶠ n : ℕ in atTop,
      0 ≤ Erdos713PolynomialInequality.eval (s i) (a i) n (optimum n)) :
    ¬ ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (∀ i, 0 ≤ Erdos713PolynomialInequality.eval (s i) (a i) n m) →
        (m : ℝ) ≤ K*optimum n := by
  rintro ⟨K,hsharp⟩
  exact irrational_sqrt_two
    (Erdos713PolynomialInequality.rational_of_finite_sharp_relaxation
      (Real.sqrt_pos.mpr (by norm_num)) (by norm_num) optimum_asymptotic
      s hs a ha hfeas K hsharp)

#print axioms local_quadratic_is_optimum
#print axioms optimum_asymptotic
#print axioms no_binomial_relaxation
#print axioms no_sharp_fixed_relaxation
end Erdos713QuadraticOptimizationDiagnostic
