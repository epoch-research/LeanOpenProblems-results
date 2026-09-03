import Submission.GlobalPredecessorRepairExplore
import Submission.AnnulusExtensionExplore

/-! Iterating predecessor swaps beyond a frozen prefix, without accumulating
prefix-count error. Centers may be chosen arbitrarily far apart. -/
namespace Erdos66SeparatedPredecessorState
open Filter AdditiveCombinatorics Erdos66Counting Erdos66PredecessorCutoffTransfer
  Erdos66GlobalPredecessorRepair Erdos66Fractional Erdos66Generating Erdos66Rounding
  Erdos66OrderedPartialReplacement Erdos66Compactness Erdos66AnnulusExtension
open scoped Classical Topology
set_option maxHeartbeats 2400000

structure State (base : Set ℕ) where
  A : Set ℕ
  T : ℕ
  close : ∀ X, -1 ≤ (count A X : ℝ)-count base X ∧ (count A X : ℝ)-count base X ≤ 0
  tail_mem : ∀ i, T ≤ i → (i ∈ A ↔ i ∈ base)
  tail_count : ∀ X, T ≤ X → count A X = count base X

noncomputable def initial (base : Set ℕ) : State base :=
  ⟨base,0,fun _ ↦ by simp,fun _ _ ↦ Iff.rfl,fun _ _ ↦ rfl⟩

noncomputable def weight (k : ℕ) : ℝ := (1/2)^k

lemma weight_pos (k : ℕ) : 0 < weight k := by unfold weight; positivity
lemma weight_step (k : ℕ) : weight k-weight (k+1) = weight (k+1) := by unfold weight; rw [pow_succ]; ring
lemma weight_zero : weight 0 = 1 := by norm_num [weight]
lemma weight_tendsto : Tendsto weight atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

variable {base : Set ℕ}

lemma state_discrepancy (s : State base) (D : ℝ)
    (hbase : ∀ X, |(count base X : ℝ)-cumulative profile X| ≤ D) (X : ℕ) :
    |(count s.A X : ℝ)-cumulative profile X| ≤ D+1 := by
  have hc : |(count s.A X : ℝ)-count base X| ≤ 1 := by
    rw [abs_le]
    exact ⟨(s.close X).1,(s.close X).2.trans (by norm_num)⟩
  calc
    _ ≤ |(count s.A X : ℝ)-count base X|+|(count base X : ℝ)-cumulative profile X| := abs_sub_le _ _ _
    _ ≤ D+1 := by linarith [hbase X]

lemma state_envelope (s : State base) (K C : ℝ)
    (hbase : ∀ z, (sumRep base z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2)) (z : ℕ) :
    (sumRep s.A z : ℝ) ≤ (K+2*s.T)+C*Real.log ((z : ℝ)+2) := by
  have hh := sumRep_eq_tail_error s.A base s.T z (s.tail_mem)
  have hu := (abs_le.mp hh).2
  linarith [hbase z]

def Extension (s : State base) (k : ℕ) (q : State base × ℕ) : Prop :=
  s.T < q.2 ∧ 16 ≤ q.2 ∧ (k+1)^4 ≤ q.2 ∧ q.1.T = 16*q.2+1 ∧
    (∀ i, i < s.T → (i ∈ q.1.A ↔ i ∈ s.A)) ∧
    sumRep q.1.A (16*q.2) = sumRep s.A (16*q.2)+2*⌈Real.log ((16*q.2 : ℕ) : ℝ)⌉₊ ∧
    (∀ z, z ≠ 16*q.2 → |(sumRep q.1.A z : ℝ)-sumRep s.A z| ≤
      weight (k+1)*Real.log ((z : ℝ)+2)) ∧
    (2 : ℝ)*⌈Real.log ((16*q.2 : ℕ) : ℝ)⌉₊ ≤ 8*Real.log ((16*q.2 : ℕ)+2 : ℕ)

 theorem exists_extension (D K C : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hbase : ∀ X, |(count base X : ℝ)-cumulative profile X| ≤ D)
    (henv : ∀ z, (sumRep base z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2))
    (s : State base) (k : ℕ) : ∃ q, Extension s k q := by
  have hp := eventually_global_predecessor_repair s.A (D+1) (K+2*s.T) C 4 (weight (k+1))
    (by linarith) (by positivity) hC (by norm_num) (weight_pos _) (state_discrepancy s D hbase)
    (state_envelope s K C henv)
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hall : ∀ᶠ N : ℕ in atTop, 16 ≤ N ∧ s.T < N ∧ (k+1)^4 ≤ N ∧
      1 ≤ Real.log (N : ℝ) ∧ ∀ m : ℕ, (m : ℝ) ≤ 4*Real.log (N : ℝ) →
      ∃ E F : Finset ℕ, (E : Set ℕ) ⊆ s.A ∧ Disjoint (F : Set ℕ) s.A ∧
        E.card = 2*m ∧ F.card = 2*m ∧
        (∀ u ∈ E ∪ F, 3*N ≤ u ∧ u ≤ 12*N) ∧
        (∀ X, -1 ≤ (count (swap s.A E F) X : ℝ)-count s.A X ∧
          (count (swap s.A E F) X : ℝ)-count s.A X ≤ 0) ∧
        sumRep (swap s.A E F) (16*N) = sumRep s.A (16*N)+2*m ∧
        ∀ z, z ≠ 16*N → |(sumRep (swap s.A E F) z : ℝ)-sumRep s.A z| ≤
          weight (k+1)*Real.log ((z : ℝ)+2) := by
    filter_upwards [eventually_ge_atTop 16,eventually_ge_atTop (s.T+1),
      eventually_ge_atTop ((k+1)^4),hlog.eventually_ge_atTop 1,hp] with N hN hT hk hl hp
    exact ⟨hN,by omega,hk,hl,hp⟩
  obtain ⟨N,hN',hNT',hNk',hl',hrepair'⟩ := hall.exists
  let m : ℕ := ⌈Real.log ((16*N : ℕ) : ℝ)⌉₊
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h16 : (16 : ℝ) ≤ N := by exact_mod_cast hN'
  have hln : 0 ≤ Real.log ((16*N : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 16*N by omega)
  have hlog16 : Real.log ((16*N : ℕ) : ℝ) ≤ 2*Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) (ne_of_gt hNp)]
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16) h16
    linarith
  have hmhi : (m : ℝ) ≤ 4*Real.log (N : ℝ) := by
    have hh := Nat.ceil_lt_add_one hln
    change (m : ℝ) < Real.log ((16*N : ℕ) : ℝ)+1 at hh
    linarith
  obtain ⟨E,F,hE,hF,hEc,hFc,hs,hpref,htarget,hcol⟩ := hrepair' m hmhi
  let A' := swap s.A E F
  have hbelow (i : ℕ) (hi : i < 3*N) : i ∈ A' ↔ i ∈ s.A := by
    apply swap_mem_outside
    intro hh
    have ht := (hs i hh).1
    omega
  have habove (i : ℕ) (hi : 16*N+1 ≤ i) : i ∈ A' ↔ i ∈ s.A := by
    apply swap_mem_outside
    intro hh
    have ht := (hs i hh).2
    omega
  have htailcount (X : ℕ) (hX : 16*N+1 ≤ X) : count A' X = count s.A X := by
    apply swap_count_after s.A E F hE hF (hEc.trans hFc.symm) (16*N+1) X _ hX
    intro i hi
    have hh := (hs i hi).2
    exact Finset.mem_range.mpr (by omega)
  have hclose (X : ℕ) : -1 ≤ (count A' X : ℝ)-count base X ∧ (count A' X : ℝ)-count base X ≤ 0 := by
    by_cases hX : X ≤ 3*N
    · have he : count A' X = count s.A X := by
        unfold count
        congr 1
        ext i
        simp only [mem_cutoff]
        apply and_congr_right
        intro hi
        exact hbelow i (by omega)
      rw [he]
      exact s.close X
    · have hh := hpref X
      rw [s.tail_count X (by omega)] at hh
      exact hh
  let s' : State base := {
    A := A'
    T := 16*N+1
    close := hclose
    tail_mem := fun i hi ↦ (habove i hi).trans (s.tail_mem i (by omega))
    tail_count := fun X hX ↦ (htailcount X hX).trans (s.tail_count X (by omega)) }
  refine ⟨(s',N),hNT',hN',hNk',rfl,?_,htarget,hcol,?_⟩
  · intro i hi
    exact hbelow i (by omega)
  · have hlz : Real.log (N : ℝ) ≤ Real.log (((16*N : ℕ)+2 : ℕ) : ℝ) :=
      Real.log_le_log hNp (by exact_mod_cast (show N ≤ 16*N+2 by omega))
    change 2*(m : ℝ) ≤ _
    linarith

noncomputable def step (D K C : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hbase : ∀ X, |(count base X : ℝ)-cumulative profile X| ≤ D)
    (henv : ∀ z, (sumRep base z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2))
    (s : State base) (k : ℕ) : State base × ℕ :=
  Classical.choose (exists_extension D K C hD hK hC hbase henv s k)

lemma step_spec (D K C : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hbase : ∀ X, |(count base X : ℝ)-cumulative profile X| ≤ D)
    (henv : ∀ z, (sumRep base z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2))
    (s : State base) (k : ℕ) : Extension s k (step D K C hD hK hC hbase henv s k) :=
  Classical.choose_spec (exists_extension D K C hD hK hC hbase henv s k)

end Erdos66SeparatedPredecessorState
