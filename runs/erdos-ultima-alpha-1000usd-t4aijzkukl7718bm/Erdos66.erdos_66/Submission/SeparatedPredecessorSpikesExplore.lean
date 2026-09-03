import Submission.SeparatedPredecessorStateExplore

/-! A count-preserving sparse-spike construction with uniform vanishing
normalized collateral away from its chosen centers. -/
namespace Erdos66SeparatedPredecessorSpikes
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Compactness
  Erdos66SeparatedPredecessorState Erdos66Fractional Erdos66Generating Erdos66Rounding
  Erdos66AnnulusExtension
open scoped Classical Topology
set_option maxHeartbeats 2500000

structure Host where
  A : Set ℕ
  D : ℝ
  K : ℝ
  C : ℝ
  D_nonneg : 0 ≤ D
  K_nonneg : 0 ≤ K
  C_nonneg : 0 ≤ C
  balanced : ∀ N, |(count A N : ℝ)-cumulative profile N| ≤ D
  envelope : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2)

variable (H : Host)

noncomputable def states : ℕ → State H.A
  | 0 => initial H.A
  | k+1 => (step H.D H.K H.C H.D_nonneg H.K_nonneg H.C_nonneg H.balanced H.envelope (states k) k).1

noncomputable def scale (k : ℕ) : ℕ :=
  (step H.D H.K H.C H.D_nonneg H.K_nonneg H.C_nonneg H.balanced H.envelope (states H k) k).2

noncomputable def target (k : ℕ) : ℕ := 16*scale H k

lemma states_step (k : ℕ) : Extension (states H k) k (states H (k+1),scale H k) :=
  step_spec H.D H.K H.C H.D_nonneg H.K_nonneg H.C_nonneg H.balanced H.envelope (states H k) k

lemma cutoff_eq (k : ℕ) : (states H (k+1)).T = target H k+1 := (states_step H k).2.2.2.1

lemma cutoff_increases (k : ℕ) : (states H k).T < (states H (k+1)).T := by
  have h := (states_step H k).1
  rw [cutoff_eq]
  unfold target
  omega

lemma cutoff_mono : Monotone (fun k ↦ (states H k).T) :=
  monotone_nat_of_le_succ (fun k ↦ (cutoff_increases H k).le)

lemma cutoff_ge (k : ℕ) : k ≤ (states H k).T := by
  induction k with
  | zero => omega
  | succ k ih => have hh := cutoff_increases H k; omega

lemma target_strictMono : StrictMono (target H) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hh := (states_step H (k+1)).1
  rw [cutoff_eq] at hh
  unfold target at *
  omega

lemma target_ge (k : ℕ) : (k+1)^4 ≤ target H k := by
  have hh := (states_step H k).2.2.1
  unfold target
  omega

lemma target_large (k : ℕ) : 256 ≤ target H k := by
  have hh := (states_step H k).2.1
  unfold target
  omega

lemma states_mem_stable (j k : ℕ) (hjk : j ≤ k) (i : ℕ) (hi : i < (states H j).T) :
    i ∈ (states H k).A ↔ i ∈ (states H j).A := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih =>
    exact ((states_step H k).2.2.2.2.1 i (hi.trans_le (cutoff_mono H hjk))).trans ih

noncomputable def repaired : Set ℕ := {i | i ∈ (states H (i+1)).A}

lemma repaired_mem (j i : ℕ) (hi : i < (states H j).T) :
    i ∈ repaired H ↔ i ∈ (states H j).A := by
  have hi' : i < (states H (i+1)).T := lt_of_lt_of_le (Nat.lt_succ_self i) (cutoff_ge H (i+1))
  exact (states_mem_stable H (i+1) (max (i+1) j) (le_max_left _ _) i hi').symm.trans
    (states_mem_stable H j (max (i+1) j) (le_max_right _ _) i hi)

lemma repaired_count (N : ℕ) : count (repaired H) N = count (states H N).A N := by
  unfold count
  congr 1
  ext i
  simp only [mem_cutoff]
  apply and_congr_right
  intro hi
  exact repaired_mem H N i (hi.trans_le (cutoff_ge H N))

lemma repaired_rep (j z : ℕ) (hz : z < (states H j).T) :
    sumRep (repaired H) z = sumRep (states H j).A z :=
  sumRep_congr_below (fun i hi ↦ repaired_mem H j i (hi.trans_lt hz))

lemma repaired_count_close (N : ℕ) :
    -1 ≤ (count (repaired H) N : ℝ)-count H.A N ∧
      (count (repaired H) N : ℝ)-count H.A N ≤ 0 := by
  rw [repaired_count]
  exact (states H N).close N

lemma repaired_discrepancy (N : ℕ) :
    |(count (repaired H) N : ℝ)-cumulative profile N| ≤ H.D+1 := by
  rw [repaired_count]
  exact state_discrepancy (states H N) H.D H.balanced N

lemma log_nonneg (z : ℕ) : 0 ≤ Real.log ((z : ℝ)+2) :=
  Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) z; linarith)

lemma finite_collateral (j k : ℕ) (hjk : j ≤ k) (z : ℕ)
    (hoff : ∀ i, j ≤ i → i < k → z ≠ target H i) :
    |(sumRep (states H k).A z : ℝ)-sumRep (states H j).A z| ≤
      (weight j-weight k)*Real.log ((z : ℝ)+2) := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    have hi := ih (fun i hji hik ↦ hoff i hji (by omega))
    have hs := (states_step H k).2.2.2.2.2.2.1 z (hoff k hjk (by omega))
    have ht := abs_sub_le ((sumRep (states H (k+1)).A z : ℝ)) (sumRep (states H k).A z)
      (sumRep (states H j).A z)
    dsimp only at hs
    have hw := congrArg (fun x : ℝ ↦ x*Real.log ((z : ℝ)+2)) (weight_step k)
    nlinarith

lemma outside_collateral (j z : ℕ) (hz : z ∉ Set.range (target H)) :
    |(sumRep (repaired H) z : ℝ)-sumRep (states H j).A z| ≤ weight j*Real.log ((z : ℝ)+2) := by
  let k := max (z+1) j
  have hjk : j ≤ k := le_max_right _ _
  have hzk : z < (states H k).T := lt_of_lt_of_le
    (lt_of_lt_of_le (Nat.lt_succ_self z) (le_max_left _ _)) (cutoff_ge H k)
  rw [repaired_rep H k z hzk]
  have hh := finite_collateral H j k hjk z (fun i _ _ he ↦ hz ⟨i,he.symm⟩)
  have hp := mul_nonneg (weight_pos k).le (log_nonneg z)
  nlinarith

lemma initial_collateral (k z : ℕ) (hoff : ∀ i, i < k → z ≠ target H i) :
    |(sumRep (states H k).A z : ℝ)-sumRep H.A z| ≤ Real.log ((z : ℝ)+2) := by
  have hh := finite_collateral H 0 k (by omega) z (fun i _ hi ↦ hoff i hi)
  rw [weight_zero] at hh
  change |(sumRep (states H k).A z : ℝ)-sumRep H.A z| ≤ _ at hh
  have hp := mul_nonneg (weight_pos k).le (log_nonneg z)
  nlinarith

lemma repaired_envelope (z : ℕ) :
    (sumRep (repaired H) z : ℝ) ≤ H.K+(H.C+9)*Real.log ((z : ℝ)+2) := by
  have hbase := H.envelope z
  by_cases hz : z ∈ Set.range (target H)
  · obtain ⟨k,rfl⟩ := hz
    have hs := (states_step H k).2.2.2.2.2.1
    have hg := (states_step H k).2.2.2.2.2.2.2
    have hi := initial_collateral H k (target H k) (fun i hi he ↦ by
      have hh := target_strictMono H hi
      omega)
    have hr := repaired_rep H (k+1) (target H k) (by rw [cutoff_eq]; omega)
    rw [hr]
    change sumRep (states H (k+1)).A (target H k) = sumRep (states H k).A (target H k)+2*⌈Real.log ((target H k : ℕ) : ℝ)⌉₊ at hs
    rw [hs,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    change 2*(⌈Real.log ((target H k : ℕ) : ℝ)⌉₊ : ℝ) ≤ 8*Real.log (((target H k)+2 : ℕ) : ℝ) at hg
    push_cast at hg
    have hi' := (abs_le.mp hi).2
    nlinarith
  · have hh := outside_collateral H 0 z hz
    rw [weight_zero,one_mul] at hh
    change |(sumRep (repaired H) z : ℝ)-sumRep H.A z| ≤ _ at hh
    have hh' := (abs_le.mp hh).2
    have hl := log_nonneg z
    nlinarith

lemma repaired_peak (k : ℕ) :
    (2 : ℝ) ≤ (sumRep (repaired H) (target H k) : ℝ)/Real.log (target H k) := by
  have hlarge := target_large H k
  have hlog : 0 < Real.log ((target H k : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < target H k by omega))
  have hs := (states_step H k).2.2.2.2.2.1
  rw [repaired_rep H (k+1) (target H k) (by rw [cutoff_eq]; omega)]
  change sumRep (states H (k+1)).A (target H k) = sumRep (states H k).A (target H k)+2*⌈Real.log ((target H k : ℕ) : ℝ)⌉₊ at hs
  rw [hs,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  apply (le_div_iff₀ hlog).mpr
  have hc := Nat.le_ceil (Real.log ((target H k : ℕ) : ℝ))
  have hp := Nat.cast_nonneg (α := ℝ) (sumRep (states H k).A (target H k))
  change 2*Real.log (target H k) ≤ (sumRep (states H k).A (target H k) : ℝ)+2*(⌈Real.log ((target H k : ℕ) : ℝ)⌉₊ : ℝ)
  linarith

lemma logarithm_double (n : ℕ) (hn : 2 ≤ n) :
    Real.log ((n : ℝ)+2) ≤ 2*Real.log (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ)+2)
    (show (n : ℝ)+2 ≤ (n : ℝ)^2 by nlinarith)
  simpa only [Real.log_pow,Nat.cast_ofNat] using hh

 theorem outside_ratio_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, n ∉ Set.range (target H) →
      |(sumRep (repaired H) n : ℝ)/Real.log n-(sumRep H.A n : ℝ)/Real.log n| < ε := by
  obtain ⟨j,hj⟩ := (weight_tendsto.eventually_lt_const (show (0 : ℝ) < ε/8 by positivity)).exists
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := hlog.const_div_atTop (2*((states H j).T : ℝ))
  filter_upwards [eventually_ge_atTop 2,ht.eventually_lt_const (show (0 : ℝ) < ε/2 by positivity)]
    with n hn hsmall
  intro hoff
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hc := outside_collateral H j n hoff
  have hf := sumRep_eq_tail_error (states H j).A H.A (states H j).T n (states H j).tail_mem
  have htri := abs_sub_le ((sumRep (repaired H) n : ℝ)) (sumRep (states H j).A n) (sumRep H.A n)
  have hd := logarithm_double n hn
  have hh := mul_le_mul_of_nonneg_left hd (weight_pos j).le
  have hsmall' := (div_lt_iff₀ hln).mp hsmall
  rw [← sub_div,abs_div,abs_of_pos hln]
  apply (div_lt_iff₀ hln).mpr
  nlinarith

/-- Count discrepancy is uniformly at most one, the logarithmic envelope
persists, and off-center changes vanish after normalization. -/
theorem exists_count_preserving_sparse_spikes :
    ∃ (B : Set ℕ) (t : ℕ → ℕ), StrictMono t ∧
      (∀ k, (k+1)^4 ≤ t k) ∧
      (∀ N, -1 ≤ (count B N : ℝ)-count H.A N ∧ (count B N : ℝ)-count H.A N ≤ 0) ∧
      (∀ n, (sumRep B n : ℝ) ≤ H.K+(H.C+9)*Real.log ((n : ℝ)+2)) ∧
      (∀ k, (2 : ℝ) ≤ (sumRep B (t k) : ℝ)/Real.log (t k)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, n ∉ Set.range t →
        |(sumRep B n : ℝ)/Real.log n-(sumRep H.A n : ℝ)/Real.log n| < ε) :=
  ⟨repaired H,target H,target_strictMono H,target_ge H,repaired_count_close H,
    repaired_envelope H,repaired_peak H,outside_ratio_small H⟩

end Erdos66SeparatedPredecessorSpikes
