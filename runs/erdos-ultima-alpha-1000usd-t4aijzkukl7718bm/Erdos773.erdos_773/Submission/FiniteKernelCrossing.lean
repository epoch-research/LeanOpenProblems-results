import FormalConjecturesUtil

/-!
Finite time-inhomogeneous transition kernels, first-crossing probabilities,
and a nonnegative supermartingale crossing bound. No independence of
successive choices is assumed.
-/
namespace Erdos773.FiniteKernelCrossing
open Finset
set_option maxHeartbeats 2000000
noncomputable section
variable {σ : Type*} [Fintype σ]

structure Kernel (σ : Type*) [Fintype σ] where
  weight : σ → σ → ℝ
  nonneg : ∀ x y, 0 ≤ weight x y
  total : ∀ x, ∑ y, weight x y = 1

namespace Kernel

def avg (K : Kernel σ) (f : σ → ℝ) (x : σ) : ℝ := ∑ y, K.weight x y*f y

lemma avg_nonneg (K : Kernel σ) {f : σ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : σ) :
    0 ≤ K.avg f x := sum_nonneg (fun y _ => mul_nonneg (K.nonneg x y) (hf y))

lemma avg_mono_support (K : Kernel σ) {f g : σ → ℝ} (x : σ)
    (hfg : ∀ y, 0 < K.weight x y → f y ≤ g y) : K.avg f x ≤ K.avg g x := by
  apply sum_le_sum
  intro y hy
  by_cases h : 0 < K.weight x y
  · exact mul_le_mul_of_nonneg_left (hfg y h) (K.nonneg x y)
  · have hz : K.weight x y = 0 := le_antisymm (le_of_not_gt h) (K.nonneg x y)
    simp only [hz,zero_mul,le_refl]

lemma avg_congr_support (K : Kernel σ) {f g : σ → ℝ} (x : σ)
    (hfg : ∀ y, 0 < K.weight x y → f y = g y) : K.avg f x = K.avg g x :=
  le_antisymm (K.avg_mono_support x (fun y hy => (hfg y hy).le))
    (K.avg_mono_support x (fun y hy => (hfg y hy).ge))

lemma avg_mono (K : Kernel σ) {f g : σ → ℝ} (hfg : ∀ y, f y ≤ g y) (x : σ) :
    K.avg f x ≤ K.avg g x := K.avg_mono_support x (fun y _ => hfg y)

@[simp] lemma avg_const (K : Kernel σ) (a : ℝ) (x : σ) : K.avg (fun _ => a) x = a := by
  simp only [avg,← sum_mul,K.total,one_mul]

lemma avg_add (K : Kernel σ) (f g : σ → ℝ) (x : σ) :
    K.avg (fun y => f y+g y) x = K.avg f x+K.avg g x := by
  simp only [avg,mul_add,sum_add_distrib]

lemma avg_mul (K : Kernel σ) (a : ℝ) (f : σ → ℝ) (x : σ) :
    K.avg (fun y => a*f y) x = a*K.avg f x := by
  simp only [avg,mul_sum]
  apply sum_congr rfl
  intro y hy
  ring

lemma avg_div (K : Kernel σ) (a : ℝ) (f : σ → ℝ) (x : σ) :
    K.avg (fun y => f y/a) x = K.avg f x/a := by
  simp only [avg,mul_div_assoc,sum_div]

lemma avg_sum {ι : Type*} (K : Kernel σ) (T : Finset ι) (f : ι → σ → ℝ) (x : σ) :
    K.avg (fun y => ∑ i ∈ T, f i y) x = ∑ i ∈ T, K.avg (f i) x := by
  simp only [avg,mul_sum]
  exact sum_comm

/-- A strict average inequality has a witness in the actual transition support. -/
lemma exists_support_lt (K : Kernel σ) (f : σ → ℝ) (x : σ) (a : ℝ)
    (h : K.avg f x < a) : ∃ y, 0 < K.weight x y ∧ f y < a := by
  by_contra! hn
  have hh := K.avg_mono_support (f := fun _ => a) (g := f) x hn
  rw [K.avg_const] at hh
  linarith

end Kernel

/-- Terminal expectation, starting at time n and making h transitions. -/
def terminal (K : ℕ → Kernel σ) (n h : ℕ) (f : σ → ℝ) (x : σ) : ℝ :=
  match h with
  | 0 => f x
  | h+1 => (K n).avg (terminal K (n+1) h f) x

/-- Probability of hitting P at some time in the inclusive interval
    [n,n+h], starting from x at time n. -/
def hit (K : ℕ → Kernel σ) (P : ℕ → σ → Prop) (n h : ℕ) (x : σ) : ℝ := by
  classical
  exact match h with
  | 0 => if P n x then 1 else 0
  | h+1 => if P n x then 1 else (K n).avg (hit K P (n+1) h) x

lemma hit_bounds (K : ℕ → Kernel σ) (P : ℕ → σ → Prop) (n h : ℕ) (x : σ) :
    0 ≤ hit K P n h x ∧ hit K P n h x ≤ 1 := by
  classical
  induction h generalizing n x with
  | zero => simp only [hit]; split_ifs <;> norm_num
  | succ h ih =>
    simp only [hit]
    split_ifs
    · norm_num
    · refine ⟨(K n).avg_nonneg (fun y => (ih (n+1) y).1) x,?_⟩
      simpa only [Kernel.avg_const] using
        (K n).avg_mono (fun y => (ih (n+1) y).2) x

/-- An actual support-respecting path, with every visited state good. -/
def GoodPath (K : ℕ → Kernel σ) (P : ℕ → σ → Prop) (n h : ℕ) (x : σ) : Prop :=
  match h with
  | 0 => ¬P n x
  | h+1 => ¬P n x ∧ ∃ y, 0 < (K n).weight x y ∧ GoodPath K P (n+1) h y

/-- Probability below one extracts an actual good path, not just a formal
    collection of states satisfying inequalities. -/
theorem goodPath_of_hit_lt_one (K : ℕ → Kernel σ) (P : ℕ → σ → Prop)
    (n h : ℕ) (x : σ) (hhit : hit K P n h x < 1) : GoodPath K P n h x := by
  classical
  induction h generalizing n x with
  | zero =>
    intro hp
    simp only [hit,if_pos hp,lt_self_iff_false] at hhit
  | succ h ih =>
    have hnp : ¬P n x := by
      intro hp
      simp only [hit,if_pos hp,lt_self_iff_false] at hhit
    simp only [hit,if_neg hnp] at hhit
    obtain ⟨y,hy,hh⟩ := (K n).exists_support_lt (hit K P (n+1) h) x 1 hhit
    exact ⟨hnp,y,hy,ih (n+1) y hh⟩

/-- Finite Ville-type bound. F is nonnegative and has nonpositive conditional
    drift; every bad state has F at least A. The hypotheses are needed only
    through the finite horizon T. -/
theorem hit_le_potential (K : ℕ → Kernel σ) (P : ℕ → σ → Prop)
    (F : ℕ → σ → ℝ) (T : ℕ) (A : ℝ) (hA : 0 < A)
    (hF : ∀ n ≤ T, ∀ x, 0 ≤ F n x)
    (hstep : ∀ n < T, ∀ x, (K n).avg (F (n+1)) x ≤ F n x)
    (hdom : ∀ n ≤ T, ∀ x, P n x → A ≤ F n x)
    (n h : ℕ) (hnh : n+h ≤ T) (x : σ) : hit K P n h x ≤ F n x/A := by
  classical
  induction h generalizing n x with
  | zero =>
    simp only [hit]
    by_cases hp : P n x
    · rw [if_pos hp]
      exact (one_le_div hA).mpr (hdom n (by omega) x hp)
    · rw [if_neg hp]
      exact div_nonneg (hF n (by omega) x) hA.le
  | succ h ih =>
    simp only [hit]
    by_cases hp : P n x
    · rw [if_pos hp]
      exact (one_le_div hA).mpr (hdom n (by omega) x hp)
    · rw [if_neg hp]
      calc
        _ ≤ (K n).avg (fun y => F (n+1) y/A) x :=
          (K n).avg_mono (fun y => ih (n+1) (by omega) y) x
        _ = (K n).avg (F (n+1)) x/A := Kernel.avg_div _ _ _ _
        _ ≤ _ := div_le_div_of_nonneg_right (hstep n (by omega) x) hA.le

lemma hit_eq_one_of_now (K : ℕ → Kernel σ) (P : ℕ → σ → Prop)
    (n h : ℕ) (x : σ) (hp : P n x) : hit K P n h x = 1 := by
  classical
  cases h <;> simp only [hit,if_pos hp]

/-- Union bound for first crossings, not only terminal events. -/
theorem hit_union_bound {ι : Type*} (K : ℕ → Kernel σ) (T : Finset ι)
    (P : ι → ℕ → σ → Prop) (n h : ℕ) (x : σ) :
    hit K (fun n x => ∃ i ∈ T, P i n x) n h x ≤ ∑ i ∈ T, hit K (P i) n h x := by
  classical
  induction h generalizing n x with
  | zero =>
    by_cases hp : ∃ i ∈ T, P i n x
    · rw [hit_eq_one_of_now K _ n 0 x hp]
      obtain ⟨i,hi,hp⟩ := hp
      have hh := single_le_sum (fun j _ => (hit_bounds K (P j) n 0 x).1) hi
      simpa only [hit_eq_one_of_now K (P i) n 0 x hp] using hh
    · simp only [hit,if_neg hp]
      exact sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  | succ h ih =>
    by_cases hp : ∃ i ∈ T, P i n x
    · rw [hit_eq_one_of_now K _ n (h+1) x hp]
      obtain ⟨i,hi,hp⟩ := hp
      have hh := single_le_sum (fun j _ => (hit_bounds K (P j) n (h+1) x).1) hi
      simpa only [hit_eq_one_of_now K (P i) n (h+1) x hp] using hh
    · have hnot (i : ι) (hi : i ∈ T) : ¬P i n x := fun h => hp ⟨i,hi,h⟩
      have heq : (∑ i ∈ T, hit K (P i) n (h+1) x) =
          ∑ i ∈ T, (K n).avg (hit K (P i) (n+1) h) x :=
        sum_congr rfl (fun i hi => by simp only [hit,if_neg (hnot i hi)])
      rw [heq,← Kernel.avg_sum]
      simp only [hit,if_neg hp]
      exact (K n).avg_mono (fun y => ih (n+1) y) x

/-- Binary first-crossing union bound, useful for adjoining an auxiliary
    selected-set event to a finite family of degree excursions. -/
theorem hit_or_bound (K : ℕ → Kernel σ) (P Q : ℕ → σ → Prop)
    (n h : ℕ) (x : σ) :
    hit K (fun n x => P n x ∨ Q n x) n h x ≤ hit K P n h x+hit K Q n h x := by
  classical
  have hh := hit_union_bound K (univ : Finset Bool)
    (fun b n x => if b then P n x else Q n x) n h x
  have he : (fun n x => ∃ b ∈ (univ : Finset Bool), if b then P n x else Q n x) =
      (fun n x => P n x ∨ Q n x) := by
    funext n x
    apply propext
    simp only [mem_univ,true_and,Bool.exists_bool,ite_true]
    exact or_comm
  rw [he] at hh
  simpa only [Fintype.sum_bool,ite_false,ite_true,add_comm] using hh

/-- A sum of crossing bounds below one gives one path avoiding every event
    at every time in the interval. -/
theorem simultaneous_goodPath {ι : Type*} (K : ℕ → Kernel σ) (T : Finset ι)
    (P : ι → ℕ → σ → Prop) (b : ι → ℝ) (n h : ℕ) (x : σ)
    (hb : ∀ i ∈ T, hit K (P i) n h x ≤ b i) (hs : (∑ i ∈ T, b i) < 1) :
    GoodPath K (fun n x => ∃ i ∈ T, P i n x) n h x := by
  apply goodPath_of_hit_lt_one
  exact (hit_union_bound K T P n h x).trans_lt ((sum_le_sum hb).trans_lt hs)

/-- For an event preserved by every supported transition, first hitting it
    by the horizon is exactly the terminal event. This lets monotone
    selected-subset certificates use terminal moment bounds. -/
theorem terminal_eq_hit_of_preserved (K : ℕ → Kernel σ) (P : ℕ → σ → Prop) (T : ℕ)
    (hforward : ∀ n < T, ∀ x y, 0 < (K n).weight x y → P n x → P (n+1) y)
    (n h : ℕ) (hnh : n+h ≤ T) (x : σ) :
    terminal K n h (hit K P (n+h) 0) x = hit K P n h x := by
  classical
  induction h generalizing n x with
  | zero => simp only [terminal,Nat.add_zero]
  | succ h ih =>
    rw [terminal]
    have htime : n+(h+1) = (n+1)+h := by omega
    rw [htime]
    have heq : terminal K (n+1) h (hit K P ((n+1)+h) 0) = hit K P (n+1) h :=
      funext (fun y => ih (n+1) (by omega) y)
    rw [heq]
    by_cases hp : P n x
    · rw [hit_eq_one_of_now K P n (h+1) x hp]
      calc
        _ = (K n).avg (fun _ => 1) x := (K n).avg_congr_support x
          (fun y hy => hit_eq_one_of_now K P (n+1) h y (hforward n (by omega) x y hy hp))
        _ = _ := Kernel.avg_const _ _ _
    · simp only [hit,if_neg hp]

#print axioms terminal_eq_hit_of_preserved
#print axioms hit_or_bound
#print axioms hit_union_bound
#print axioms simultaneous_goodPath
#print axioms Kernel.exists_support_lt
#print axioms hit_bounds
#print axioms goodPath_of_hit_lt_one
#print axioms hit_le_potential
end
end Erdos773.FiniteKernelCrossing
