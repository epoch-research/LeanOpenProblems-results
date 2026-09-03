import Submission.LineRecoloringPeaksExplore

/-! Exponential self-count peaks in fixed-field recoloring iterations,
even if arbitrary additional points are included at every stage. This is
an obstruction to this particular finite-group iteration, not to Erdős 66. -/
namespace Erdos66LineRecoloringIteration
open Erdos66LineRecoloring Erdos66LineRecoloringPeaks Erdos66OriginRepair
  Erdos66ParabolaRepair
set_option maxHeartbeats 2800000
universe u
variable (G F : Type u)

def Space : ℕ → Type u
  | 0 => G
  | n+1 => Space n × (F×F)

instance spaceAddCommGroup [AddCommGroup G] [Field F] (n : ℕ) : AddCommGroup (Space G F n) :=
  match n with
  | 0 => inferInstanceAs (AddCommGroup G)
  | n+1 => by
    letI := spaceAddCommGroup n
    exact inferInstanceAs (AddCommGroup (Space G F n × (F×F)))

instance spaceDecidableEq [DecidableEq G] [DecidableEq F] (n : ℕ) : DecidableEq (Space G F n) :=
  match n with
  | 0 => inferInstanceAs (DecidableEq G)
  | n+1 => by
    letI := spaceDecidableEq n
    exact inferInstanceAs (DecidableEq (Space G F n × (F×F)))

instance spaceFintype [Fintype G] [Fintype F] (n : ℕ) : Fintype (Space G F n) :=
  match n with
  | 0 => inferInstanceAs (Fintype G)
  | n+1 => by
    letI := spaceFintype n
    exact inferInstanceAs (Fintype (Space G F n × (F×F)))

lemma space_card [Fintype G] [Fintype F] (n : ℕ) :
    Fintype.card (Space G F n)=Fintype.card G*(Fintype.card F)^(2*n) := by
  induction n with
  | zero => simp [Space]
  | succ n ih =>
    change Fintype.card (Space G F n × (F×F))=_
    rw [Fintype.card_prod,Fintype.card_prod,ih]
    simp only [Nat.mul_succ,pow_add,pow_two]
    ring

variable {G F} [AddCommGroup G] [DecidableEq G]
  [Field F] [Fintype F] [DecidableEq F]

lemma recolored_mono {H : Type*} [AddCommGroup H] [DecidableEq H]
    {A B : F → Finset H} (hAB : ∀ u, A u⊆B u) (τ α v : F) :
    recolored A τ α v⊆recolored B τ α v := by
  rintro ⟨a,x,y⟩ ha
  rw [mem_recolored] at ha ⊢
  exact ⟨hAB _ ha.1,ha.2⟩

/-- The next stage may contain much more than the literal lift: only
colorwise inclusion is assumed. Thus additions cannot erase these peaks. -/
theorem two_step_extension_peak
    (B : (n : ℕ) → F → Finset (Space G F n)) (τ α : ℕ → F)
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, recolored (B n) (τ n) (α n) v⊆B (n+1) v)
    (n : ℕ) (v : F) (z : Space G F n) :
    ∃ z' : Space G F (n+2),
      2*pairCount (B n v) (B n v) z≤pairCount (B (n+2) 0) (B (n+2) 0) z' := by
  obtain ⟨z',hz⟩ := two_step_self_amplification (B n) (τ n) (α n) (τ (n+1)) (α (n+1))
    (hα n) (hα (n+1)) v 0 z
  have hsub : recolored (recolored (B n) (τ n) (α n)) (τ (n+1)) (α (n+1)) 0⊆B (n+2) 0 :=
    (recolored_mono (hstep n) _ _ _).trans (hstep (n+1) 0)
  exact ⟨z',hz.trans (pairCount_mono hsub hsub z')⟩

/-- At depth 2k, a self-count at least 2^k survives from any nonzero seed
self-count. No hypotheses about caps or global means are used. -/
theorem even_stage_exponential_peak
    (B : (n : ℕ) → F → Finset (Space G F n)) (τ α : ℕ → F)
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, recolored (B n) (τ n) (α n) v⊆B (n+1) v)
    (v : F) (z : G) (hseed : 1≤pairCount (B 0 v) (B 0 v) z) :
    ∀ k : ℕ, ∃ w : F, ∃ z' : Space G F (2*k),
      2^k≤pairCount (B (2*k) w) (B (2*k) w) z' := by
  intro k
  induction k with
  | zero => exact ⟨v,z,hseed⟩
  | succ k ih =>
    obtain ⟨w,z',hz'⟩ := ih
    obtain ⟨z'',hz''⟩ := two_step_extension_peak B τ α hα hstep (2*k) w z'
    refine ⟨0,z'',?_⟩
    have hh := (Nat.mul_le_mul_left 2 hz').trans hz''
    simpa only [pow_succ,Nat.mul_comm (2^k) 2] using hh

omit [Field F] [Fintype F] [DecidableEq F] in
lemma singleton_seed (B : F → Finset G) (v : F) {a : G} (ha : a∈B v) :
    1≤pairCount (B v) (B v) (a+a) := by
  apply Finset.one_le_card.mpr
  refine ⟨a,Finset.mem_filter.mpr ⟨ha,?_⟩⟩
  simpa only [add_sub_cancel_right] using ha

/-- Every nonempty starting color supplies such an exponential seed. -/
theorem nonempty_seed_exponential_peak
    (B : (n : ℕ) → F → Finset (Space G F n)) (τ α : ℕ → F)
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, recolored (B n) (τ n) (α n) v⊆B (n+1) v)
    (v : F) (hB : (B 0 v).Nonempty) :
    ∀ k : ℕ, ∃ w : F, ∃ z' : Space G F (2*k),
      2^k≤pairCount (B (2*k) w) (B (2*k) w) z' := by
  obtain ⟨a,ha⟩ := hB
  exact even_stage_exponential_peak B τ α hα hstep v (a+a) (singleton_seed (B 0) v ha)

open Filter
open scoped Topology

lemma eventually_linear_lt_two_pow (D C : ℝ) :
    ∀ᶠ k : ℕ in atTop, D+C*k<(2:ℝ)^k := by
  have h0 := (tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)).const_mul D
  have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)).const_mul C
  have hh := h0.add h1
  simp only [pow_zero,pow_one,mul_zero,add_zero] at hh
  filter_upwards [hh.eventually_lt_const (by norm_num : (0:ℝ)<1)] with k hk
  have hpow : (0:ℝ)<2^k := pow_pos (by norm_num) k
  have hnorm : (D+C*k)/(2:ℝ)^k<1 := by
    convert hk using 1; ring
  exact (div_lt_one hpow).mp hnorm

omit [DecidableEq G] [DecidableEq F] in
lemma space_log_even [Fintype G] (k : ℕ) :
    Real.log (Fintype.card (Space G F (2*k)) : ℝ)=
      Real.log (Fintype.card G : ℝ)+4*k*Real.log (Fintype.card F : ℝ) := by
  rw [space_card]
  push_cast
  rw [Real.log_mul (by exact_mod_cast Fintype.card_ne_zero (α := G))
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero (α := F))),Real.log_pow]
  push_cast
  ring

/-- Literal fixed-field recoloring iterations cannot have even an eventual
logarithmic cap in the cardinality of their ambient groups. This remains
true with arbitrary colorwise additions at every stage. -/
theorem iteration_exceeds_logarithmic_cap [Fintype G]
    (B : (n : ℕ) → F → Finset (Space G F n)) (τ α : ℕ → F)
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, recolored (B n) (τ n) (α n) v⊆B (n+1) v)
    (v : F) (hB : (B 0 v).Nonempty) (K C : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∃ z : Space G F (2*k),
      K+C*Real.log (Fintype.card (Space G F (2*k)) : ℝ)<
        (pairCount (Finset.univ.biUnion (B (2*k))) (Finset.univ.biUnion (B (2*k))) z : ℝ) := by
  have hp := nonempty_seed_exponential_peak B τ α hα hstep v hB
  filter_upwards [eventually_linear_lt_two_pow
    (K+C*Real.log (Fintype.card G : ℝ)) (4*C*Real.log (Fintype.card F : ℝ))] with k hk
  obtain ⟨w,z,hz⟩ := hp k
  have hs : B (2*k) w⊆Finset.univ.biUnion (B (2*k)) := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_univ _,ha⟩
  have hle : (2:ℝ)^k≤
      (pairCount (Finset.univ.biUnion (B (2*k))) (Finset.univ.biUnion (B (2*k))) z : ℝ) := by
    exact_mod_cast hz.trans (pairCount_mono hs hs z)
  refine ⟨z,lt_of_lt_of_le ?_ hle⟩
  rw [space_log_even]
  convert hk using 1; ring

end Erdos66LineRecoloringIteration
