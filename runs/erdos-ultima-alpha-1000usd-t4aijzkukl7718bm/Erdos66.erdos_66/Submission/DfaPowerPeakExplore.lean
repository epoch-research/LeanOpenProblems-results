import Submission.DfaCountingExplore

/-!
Automatic additive bases have representation peaks of at least a fixed
positive power. This is a restricted-class statement, not a disproof of
Erdős 66. The digit-loop injection is extracted from the existing proof.
-/
namespace Erdos66DfaPowerPeak
open Filter AdditiveCombinatorics Erdos66DigitLoopPeak Erdos66DfaLoopCode
  Erdos66DfaCounting Erdos66Counting
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma digit_loops_exponential_peaks {b : ℕ} (hb : 1 < b) (A : Set ℕ)
    (a u v z : List (Fin b)) (hl : u.length = v.length) (hne : u ≠ v)
    (hA : ∀ xs : List Bool, code (a ++ blocks u v xs ++ z) ∈ A) :
    ∀ k : ℕ, ∃ n : ℕ,
      n ≤ (2 * b ^ (a.length + z.length)) * (b ^ u.length) ^ k ∧
      2 ^ k ≤ sumRep A n := by
  intro k
  let f : (Fin k → Bool) → ℕ := fun t ↦ code (a++blocks u v (List.ofFn t)++z)
  let n := 2*code a+b^a.length*(center u v k+2*(b^u.length)^k*code z)
  have hsum (t : Fin k → Bool) : f t+f (fun i ↦ !(t i))=n := by
    have hc := blocks_complement u v hl (List.ofFn t)
    simp only [List.length_ofFn,List.map_ofFn,Function.comp_def] at hc
    dsimp only [f,n]
    rw [context_code _ _ _ _ hl,context_code _ _ _ _ hl]
    simp only [List.length_ofFn]
    rw [←hc]
    ring
  have hinj : Function.Injective f := by
    intro x y he
    have hh := code_inj hb (by simp [blocks_length _ _ hl]) he
    have hh' : blocks u v (List.ofFn x)=blocks u v (List.ofFn y) := by simpa using hh
    exact List.ofFn_injective (blocks_injective hb u v hl hne hh')
  have hrep : 2^k ≤ sumRep A n := by
    rw [sumRep_def]
    have hi := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin k → Bool)))
      (t := (Finset.antidiagonal n).filter (fun p ↦ p.1∈A ∧ p.2∈A))
      (f := fun t ↦ (f t,f (fun i ↦ !(t i))))
      (by
        intro t ht
        change (f t,f (fun i ↦ !(t i))) ∈ (Finset.antidiagonal n).filter (fun p ↦ p.1∈A ∧ p.2∈A)
        exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (hsum t),hA _,hA _⟩)
      (by intro x hx y hy he; exact hinj (congrArg Prod.fst he))
    simpa using hi
  have hn : n ≤ (2*b^(a.length+z.length))*(b^u.length)^k := by
    have h₁ := code_lt hb (a++blocks u v (List.ofFn (fun _ : Fin k ↦ true))++z)
    have h₂ := code_lt hb (a++blocks u v (List.ofFn (fun _ : Fin k ↦ false))++z)
    have hs := hsum (fun _ : Fin k ↦ true)
    simp only [Bool.not_true] at hs
    have hp : b^(a.length+k*u.length+z.length)=b^(a.length+z.length)*(b^u.length)^k := by
      rw [←pow_mul,←pow_add]; congr 1; ring
    simp only [List.length_append,blocks_length _ _ hl,List.length_ofFn] at h₁ h₂
    rw [hp] at h₁ h₂
    change code (a++blocks u v (List.ofFn (fun _ : Fin k ↦ true))++z)+
      code (a++blocks u v (List.ofFn (fun _ : Fin k ↦ false))++z)=n at hs
    calc
      n ≤ 2*(b^(a.length+z.length)*(b^u.length)^k) := by omega
      _ = _ := by ring
  exact ⟨n,hn,hrep⟩

/-- Exponential peaks in an exponentially bounded region yield a fixed
power lower bound at arbitrarily late targets. -/
lemma power_peaks_of_exponential_peaks (A : Set ℕ) (B D : ℕ)
    (hpeak : ∀ k : ℕ, ∃ n : ℕ, n ≤ D * B ^ k ∧ 2 ^ k ≤ sumRep A n) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ N : ℕ, ∃ n ≥ N, n ≤ sumRep A n ^ e := by
  let K := B + 1
  have hB : B ≤ 2 ^ K := by
    have hK : K ≤ 2 ^ K := Nat.le_of_lt Nat.lt_two_pow_self
    exact (Nat.le_succ B).trans hK
  refine ⟨K + 1, by omega, ?_⟩
  intro N
  let k := max (N + 1) D
  obtain ⟨n, hn, hr⟩ := hpeak k
  have hkpow : k < 2 ^ k := Nat.lt_two_pow_self
  have hN : N ≤ n := by
    have hh := sumRep_le_succ A n
    have hkN : N + 1 ≤ k := le_max_left _ _
    omega
  have hD : D ≤ sumRep A n := by
    have hkD : D ≤ k := le_max_right _ _
    omega
  have hp : B ^ k ≤ sumRep A n ^ K := by
    calc
      B ^ k ≤ (2 ^ K) ^ k := Nat.pow_le_pow_left hB k
      _ = (2 ^ k) ^ K := by rw [← pow_mul, ← pow_mul, Nat.mul_comm K k]
      _ ≤ sumRep A n ^ K := Nat.pow_le_pow_left hr K
  refine ⟨n, hN, ?_⟩
  calc
    n ≤ D * B ^ k := hn
    _ ≤ sumRep A n * sumRep A n ^ K := Nat.mul_le_mul hD hp
    _ = sumRep A n ^ (K + 1) := (pow_succ' (sumRep A n) K).symm

/-- Every zero-padded automatic additive basis has power-size peaks.
No logarithmic asymptotic or upper bound is assumed. -/
theorem automatic_basis_power_peaks {b : ℕ} {σ : Type*} [Fintype σ]
    (hb : 1 < b) (M : DFA (Fin b) σ) (A : Set ℕ)
    (hrec : ∀ w, code w ∈ A ↔ w ∈ M.accepts)
    (N₀ : ℕ) (hbasis : ∀ n ≥ N₀, 1 ≤ sumRep A n) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ N : ℕ, ∃ n ≥ N, n ≤ sumRep A n ^ e := by
  have hnot : ¬ ContextLoopUnique M := by
    intro hu
    exact no_poly_count_basis hb A (Fintype.card σ) (count_bound hb M A hrec hu) N₀ hbasis
  unfold ContextLoopUnique at hnot
  push_neg at hnot
  obtain ⟨a, z, haz, u, v, hl, hu, hv, hne⟩ := hnot
  have hall (xs : List Bool) : code (a ++ blocks u v xs ++ z) ∈ A := by
    apply (hrec _).mpr
    rw [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_of_append,
      eval_blocks M (M.evalFrom M.start a) u v hu hv]
    simpa only [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append] using haz
  exact power_peaks_of_exponential_peaks A _ _
    (digit_loops_exponential_peaks hb A a u v z hl hne hall)

/-- In particular, a uniform subpolynomial representation envelope is
impossible for an automatic additive basis. -/
theorem automatic_basis_not_subpolynomial {b : ℕ} {σ : Type*} [Fintype σ]
    (hb : 1 < b) (M : DFA (Fin b) σ) (A : Set ℕ)
    (hrec : ∀ w, code w ∈ A ↔ w ∈ M.accepts)
    (N₀ : ℕ) (hbasis : ∀ n ≥ N₀, 1 ≤ sumRep A n) :
    ¬ (∀ e : ℕ, Tendsto (fun n ↦ (sumRep A n : ℝ) ^ e / n) atTop (𝓝 0)) := by
  intro hsub
  obtain ⟨e, he, hpeak⟩ := automatic_basis_power_peaks hb M A hrec N₀ hbasis
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hsub e).eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hn, hr⟩ := hpeak (max N 1)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hratio : (1 : ℝ) ≤ (sumRep A n : ℝ) ^ e / n := by
    apply (le_div_iff₀ hn0).mpr
    simpa using (show (n : ℝ) ≤ (sumRep A n : ℝ) ^ e by exact_mod_cast hr)
  have hsmall := hN n (by omega)
  linarith

/-- A precise consequence for the proposed automatic source: no eventual
upper bound by any fixed natural power of log is possible. -/
theorem automatic_basis_no_polylog_envelope {b : ℕ} {σ : Type*} [Fintype σ]
    (hb : 1 < b) (M : DFA (Fin b) σ) (A : Set ℕ)
    (hrec : ∀ w, code w ∈ A ↔ w ∈ M.accepts)
    (N₀ : ℕ) (hbasis : ∀ n ≥ N₀, 1 ≤ sumRep A n) (K : ℝ) (d : ℕ) :
    ¬ (∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ) ≤ K * Real.log ((n : ℝ) + 2) ^ d) := by
  intro hcap
  apply automatic_basis_not_subpolynomial hb M A hrec N₀ hbasis
  intro e
  have hx : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 2) ^ (d * e) / n)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_mul, add_neg_cancel_right] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) (d * e) one_ne_zero).comp hx
  have ht' := ht.const_mul (K ^ e)
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ by positivity)) ?_ ht'
  filter_upwards [hcap] with n hn
  have hp : (sumRep A n : ℝ) ^ e ≤ (K * Real.log ((n : ℝ) + 2) ^ d) ^ e :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hn e
  have hh := div_le_div_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) n)
  simpa only [mul_pow, ← pow_mul, mul_div_assoc] using hh

end Erdos66DfaPowerPeak
