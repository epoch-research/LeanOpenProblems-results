import Submission.HybridPrefixPredictionExplore
import Submission.PrefixBalancedUpperLimitExplore
import Submission.BalancedRepVarianceExplore

/-! Fractional continuation preserving all original prefix brackets. -/
namespace Erdos66ClampedPrefixContinuation
open Erdos66Generating Erdos66Rounding Erdos66FiniteBernoulli
  Erdos66FiniteRepBernoulli Erdos66OrderedPipagePrefix
  Erdos66PrefixBalancedUpperLimit Erdos66HybridPrefixPrediction
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def mass (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i∈Finset.range k, p i

lemma mass_zero (p : ℕ → ℝ) : mass p 0=0 := by simp [mass]
lemma mass_succ (p : ℕ → ℝ) (k : ℕ) : mass p (k+1)=mass p k+p k := by
  exact Finset.sum_range_succ p k

lemma mass_mono {p : ℕ → ℝ} (hp : ∀ i, 0≤ p i) : Monotone (mass p) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [mass_succ]
  linarith [hp k]

lemma mass_lipschitz {p : ℕ → ℝ} (hp : ∀ i, p i≤ 1) {N k : ℕ} (hNk : N≤ k) :
    mass p k≤ mass p N+((k:ℝ)-N) := by
  induction k, hNk using Nat.le_induction with
  | base =>  simp
  | succ k hk ih =>  rw [mass_succ]; push_cast; linarith [hp k]

/-- Every old prefix already lies in the original floor/ceiling brackets. -/
def PrefixBrackets (p : ℕ → ℝ) (A : Set ℕ) (N : ℕ) : Prop :=
  ∀ k≤ N, (⌊mass p k⌋:ℝ)≤ mass (indicator A) k ∧
    mass (indicator A) k≤ (⌈mass p k⌉:ℝ)

noncomputable def clampMass (p : ℕ → ℝ) (A : Set ℕ) (N k : ℕ) : ℝ :=
  if k< N then mass (indicator A) k else
    max (mass (indicator A) N)
      (min (mass (indicator A) N+((k:ℝ)-N)) (mass p k))

noncomputable def continuation (p : ℕ → ℝ) (A : Set ℕ) (N i : ℕ) : ℝ :=
  clampMass p A N (i+1)-clampMass p A N i

lemma clampMass_of_ge (p : ℕ → ℝ) (A : Set ℕ) (N k : ℕ) (hk : N≤ k) :
    clampMass p A N k=max (mass (indicator A) N)
      (min (mass (indicator A) N+((k:ℝ)-N)) (mass p k)) := by
  simp [clampMass,not_lt.mpr hk]

lemma clampMass_of_le (p : ℕ → ℝ) (A : Set ℕ) (N k : ℕ) (hk : k≤ N) :
    clampMass p A N k=mass (indicator A) k := by
  rcases lt_or_eq_of_le hk with hk | rfl
  · simp [clampMass,hk]
  · simp [clampMass]

lemma continuation_old (p : ℕ → ℝ) (A : Set ℕ) (N i : ℕ) (hi : i< N) :
    continuation p A N i=indicator A i := by
  rw [continuation,clampMass_of_le p A N (i+1) (by omega),
    clampMass_of_le p A N i (by omega),mass_succ]
  ring

lemma clamp_step {s u v a b : ℝ} (huv : v=u+1) (hab : a≤ b) (hba : b≤ a+1) :
    max s (min u a)≤ max s (min v b) ∧
    max s (min v b)≤ max s (min u a)+1 := by
  constructor
  · apply max_le_max_left
    exact min_le_min (by linarith) hab
  · have h₁ : min v b≤ min u a+1 := by
      rw [←min_add_add_right]
      exact min_le_min (by linarith) hba
    have h₂ : max s (min v b)≤ max (s+1) (min u a+1) :=
      max_le_max (by linarith) h₁
    simpa only [max_add_add_right] using h₂

lemma continuation_bounds (p : ℕ → ℝ) (hp : ∀ i, 0≤ p i ∧ p i≤ 1)
    (A : Set ℕ) (N i : ℕ) :
    0≤ continuation p A N i ∧ continuation p A N i≤ 1 := by
  by_cases hi : i< N
  · rw [continuation_old p A N i hi]
    exact ⟨indicator_nonneg A i,indicator_le_one A i⟩
  · have hiN : N≤ i := by omega
    have hs := clamp_step (s:=mass (indicator A) N)
      (u:=mass (indicator A) N+((i:ℝ)-N))
      (v:=mass (indicator A) N+(((i+1:ℕ):ℝ)-N))
      (a:=mass p i) (b:=mass p (i+1))
      (by push_cast; ring) (by rw [mass_succ]; linarith [(hp i).1])
      (by rw [mass_succ]; linarith [(hp i).2])
    rw [continuation,clampMass_of_ge p A N (i+1) (by omega),clampMass_of_ge p A N i hiN]
    constructor <;>  linarith [hs.1,hs.2]

lemma mass_continuation (p : ℕ → ℝ) (A : Set ℕ) (N k : ℕ) :
    mass (continuation p A N) k=clampMass p A N k := by
  induction k with
  | zero =>  rw [mass_zero,clampMass_of_le p A N 0 (by omega),mass_zero]
  | succ k ih =>  rw [mass_succ,ih,continuation]; ring

lemma old_mass_integer (A : Set ℕ) (N : ℕ) :
    ∃ m : ℕ, mass (indicator A) N=(m:ℝ) := by
  apply sum_binary (Finset.range N)
  intro i hi
  simp only [indicator]
  split_ifs <;>  simp

/-- The correction preserves the original brackets, rather than increasing
an absolute-discrepancy allowance at each extension. -/
theorem continuation_brackets (p : ℕ → ℝ) (hp : ∀ i, 0≤ p i ∧ p i≤ 1)
    (A : Set ℕ) (N : ℕ) (hbr : PrefixBrackets p A N) (k : ℕ) :
    (⌊mass p k⌋:ℝ)≤ mass (continuation p A N) k ∧
      mass (continuation p A N) k≤ (⌈mass p k⌉:ℝ) := by
  rw [mass_continuation]
  by_cases hk : k≤ N
  · rw [clampMass_of_le p A N k hk]
    exact hbr k hk
  · have hNk : N≤ k := by omega
    rw [clampMass_of_ge p A N k hNk]
    obtain ⟨m,hm⟩ := old_mass_integer A N
    have hb := hbr N le_rfl
    have hpk := mass_mono (fun i ↦ (hp i).1) hNk
    have hpl := mass_lipschitz (fun i ↦ (hp i).2) hNk
    have hceil : (⌈mass p N⌉:ℝ)≤ (⌈mass p k⌉:ℝ) := by
      exact_mod_cast Int.ceil_mono hpk
    have hfl : (⌊mass p k⌋:ℝ)≤ mass (indicator A) N+((k:ℝ)-N) := by
      have hfloor := Int.floor_mono hpl
      have hz : mass p N+((k:ℝ)-N)=mass p N+((k-N:ℤ):ℝ) := by push_cast; rfl
      rw [hz,Int.floor_add_intCast] at hfloor
      have hh : (⌊mass p k⌋:ℝ)≤ (⌊mass p N⌋:ℝ)+((k:ℝ)-N) := by exact_mod_cast hfloor
      linarith [hb.1]
    constructor
    · exact le_max_of_le_right (le_min hfl (Int.floor_le _))
    · exact max_le (hb.2.trans hceil) ((min_le_right _ _).trans (Int.le_ceil _))

/-- A balanced old prefix has a balanced continuation for every later cutoff. -/
theorem continuation_finite_brackets (p : ℕ → ℝ) (hp : ∀ i, 0≤ p i ∧ p i≤ 1)
    (A : Set ℕ) (N L : ℕ) (hbr : PrefixBrackets p A N) :
    Brackets (fun i : Fin (L+1) ↦ p i.val)
      (fun i ↦ continuation p A N i.val) := by
  intro k
  have he (f : ℕ → ℝ) : pref (fun i : Fin (L+1) ↦ f i.val) k=mass f (min k (L+1)) := by
    unfold mass
    rw [←pref_fin_sum L (min k (L+1)) (min_le_right _ _) f]
    unfold pref
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,lt_min_iff]
    exact ⟨fun h ↦ ⟨h,i.isLt⟩,And.left⟩
  rw [he,he]
  exact continuation_brackets p hp A N hbr _


noncomputable def rawHybrid (p : ℕ → ℝ) (A : Set ℕ) (N i : ℕ) : ℝ :=
  if i<N then indicator A i else p i

lemma mass_rawHybrid_old (p : ℕ → ℝ) (A : Set ℕ) (N k : ℕ) (hk : k≤ N) :
    mass (rawHybrid p A N) k=mass (indicator A) k := by
  apply Finset.sum_congr rfl
  intro i hi
  have h := Finset.mem_range.mp hi
  simp [rawHybrid,show i<N by omega]

lemma mass_rawHybrid_tail (p : ℕ → ℝ) (A : Set ℕ) (N k : ℕ) (hk : N≤ k) :
    mass (rawHybrid p A N) k=mass (indicator A) N+mass p k-mass p N := by
  induction k, hk using Nat.le_induction with
  | base => rw [mass_rawHybrid_old p A N N le_rfl]; ring
  | succ k hk ih => rw [mass_succ,ih,mass_succ,rawHybrid,if_neg (by omega)]; ring

lemma clampMass_above (p : ℕ → ℝ) (hp : ∀ i, p i≤ 1) (A : Set ℕ) (N k : ℕ)
    (hk : N≤ k) (hs : mass p N≤ mass (indicator A) N) :
    clampMass p A N k=max (mass (indicator A) N) (mass p k) := by
  rw [clampMass_of_ge p A N k hk,min_eq_right]
  linarith [mass_lipschitz hp hk]

lemma clampMass_below (p : ℕ → ℝ) (hp : ∀ i, 0≤ p i) (A : Set ℕ) (N k : ℕ)
    (hk : N≤ k) (hs : mass (indicator A) N≤ mass p N) :
    clampMass p A N k=min (mass (indicator A) N+((k:ℝ)-N)) (mass p k) := by
  rw [clampMass_of_ge p A N k hk,max_eq_right]
  apply le_min
  · have h : (N:ℝ)≤ k := by exact_mod_cast hk
    linarith
  · exact hs.trans (mass_mono hp hk)

lemma continuation_le_raw (p : ℕ → ℝ) (hp : ∀ i, 0≤ p i ∧ p i≤ 1)
    (A : Set ℕ) (N : ℕ) (hs : mass p N≤ mass (indicator A) N) (i : ℕ) :
    continuation p A N i≤ rawHybrid p A N i := by
  by_cases hi : i<N
  · simp [continuation_old p A N i hi,rawHybrid,hi]
  · rw [rawHybrid,if_neg hi,continuation,
      clampMass_above p (fun i ↦ (hp i).2) A N (i+1) (by omega) hs,
      clampMass_above p (fun i ↦ (hp i).2) A N i (by omega) hs,mass_succ]
    have hh : max (mass (indicator A) N) (mass p i+p i)≤
        max (mass (indicator A) N+p i) (mass p i+p i) := by
      apply max_le_max_right
      linarith [(hp i).1]
    rw [max_add_add_right] at hh
    linarith

lemma raw_le_continuation (p : ℕ → ℝ) (hp : ∀ i, 0≤ p i ∧ p i≤ 1)
    (A : Set ℕ) (N : ℕ) (hs : mass (indicator A) N≤ mass p N) (i : ℕ) :
    rawHybrid p A N i≤ continuation p A N i := by
  by_cases hi : i<N
  · simp [continuation_old p A N i hi,rawHybrid,hi]
  · rw [rawHybrid,if_neg hi,continuation,
      clampMass_below p (fun i ↦ (hp i).1) A N (i+1) (by omega) hs,
      clampMass_below p (fun i ↦ (hp i).1) A N i (by omega) hs,mass_succ]
    have hh : min (mass (indicator A) N+((i:ℝ)-N)+p i) (mass p i+p i)≤
        min (mass (indicator A) N+(((i+1:ℕ):ℝ)-N)) (mass p i+p i) := by
      apply min_le_min_right
      push_cast
      linarith [(hp i).2]
    rw [min_add_add_right] at hh
    linarith

/-- The full correction costs at most the old terminal discrepancy in l1,
independently of how far the new cutoff lies. -/
theorem continuation_l1 (p : ℕ → ℝ) (hp : ∀ i, 0≤ p i ∧ p i≤ 1)
    (A : Set ℕ) (N k : ℕ) :
    (∑ i∈Finset.range k, |continuation p A N i-rawHybrid p A N i|)≤
      |mass (indicator A) N-mass p N| := by
  by_cases hk : k≤ N
  · have he : (∑ i∈Finset.range k, |continuation p A N i-rawHybrid p A N i|)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hiN : i<N := by have := Finset.mem_range.mp hi; omega
      simp [continuation_old p A N i hiN,rawHybrid,hiN]
    rw [he]
    exact abs_nonneg _
  · have hNk : N≤ k := by omega
    rcases le_total (mass p N) (mass (indicator A) N) with hs | hs
    · have he (i : ℕ) : |continuation p A N i-rawHybrid p A N i|=
          rawHybrid p A N i-continuation p A N i := by
        rw [abs_of_nonpos (sub_nonpos.mpr (continuation_le_raw p hp A N hs i))]
        ring
      simp_rw [he]
      rw [Finset.sum_sub_distrib]
      change mass (rawHybrid p A N) k-mass (continuation p A N) k≤ _
      rw [mass_rawHybrid_tail p A N k hNk,mass_continuation,
        clampMass_above p (fun i ↦ (hp i).2) A N k hNk hs,
        abs_of_nonneg (sub_nonneg.mpr hs)]
      linarith [le_max_right (mass (indicator A) N) (mass p k)]
    · have he (i : ℕ) : |continuation p A N i-rawHybrid p A N i|=
          continuation p A N i-rawHybrid p A N i :=
        abs_of_nonneg (sub_nonneg.mpr (raw_le_continuation p hp A N hs i))
      simp_rw [he]
      rw [Finset.sum_sub_distrib]
      change mass (continuation p A N) k-mass (rawHybrid p A N) k≤ _
      rw [mass_rawHybrid_tail p A N k hNk,mass_continuation,
        clampMass_below p (fun i ↦ (hp i).1) A N k hNk hs,
        abs_of_nonpos (sub_nonpos.mpr hs)]
      linarith [min_le_right (mass (indicator A) N+((k:ℝ)-N)) (mass p k)]

lemma prefix_discrepancy_bound (p : ℕ → ℝ) (A : Set ℕ) (N : ℕ)
    (hbr : PrefixBrackets p A N) (k : ℕ) (hk : k≤ N) :
    |mass (indicator A) k-mass p k|≤ 1 := by
  have hb := hbr k hk
  have hlo := Int.lt_floor_add_one (mass p k)
  have hhi := Int.ceil_lt_add_one (mass p k)
  rw [abs_le]
  constructor <;> linarith

/-- A bracketed prefix can be continued without increasing its bracket
allowance, at a total fractional adjustment cost at most one. -/
theorem continuation_l1_le_one (p : ℕ → ℝ) (hp : ∀ i, 0≤ p i ∧ p i≤ 1)
    (A : Set ℕ) (N : ℕ) (hbr : PrefixBrackets p A N) (k : ℕ) :
    (∑ i∈Finset.range k, |continuation p A N i-rawHybrid p A N i|)≤ 1 :=
  (continuation_l1 p hp A N k).trans (prefix_discrepancy_bound p A N hbr N le_rfl)

end Erdos66ClampedPrefixContinuation
