import FormalConjecturesUtil

/-! A finite monotonicity budget does not imply square-root cancellation
of comparison increments. The counterexample below is a model label array,
not the largest-prime-factor function. -/
namespace Erdos371.MonotoneInsertion
open Finset

lemma monotone_coordinate_changes_le (a : ℕ → ℕ) (T : ℕ)
    (h : ∀ t < T, a t ≤ a (t+1)) :
    (∑ t ∈ range T, if a (t+1) ≠ a t then 1 else 0) ≤ a T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ]
    have hi := ih (fun t ht => h t (by omega))
    have hm := h T (by omega)
    by_cases he : a (T+1)=a T
    · simp only [he,ne_eq,not_true_eq_false,if_false,add_zero]
      exact hi
    · rw [if_pos he]
      omega

/-- Quantization and pointwise monotonicity give a linear total-change
budget. No independence or signed cancellation is used. -/
theorem monotone_label_change_budget (a : ℕ → ℕ → ℕ) (T N Q : ℕ)
    (hmono : ∀ t < T, ∀ n < N, a t n ≤ a (t+1) n)
    (hbound : ∀ n < N, a T n ≤ Q) :
    (∑ t ∈ range T, ((range N).filter (fun n => a (t+1) n ≠ a t n)).card) ≤ Q*N := by
  simp_rw [card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  calc
    _ ≤ ∑ n ∈ range N, a T n := by
      apply sum_le_sum
      intro n hn
      exact monotone_coordinate_changes_le (fun t => a t n) T
        (fun t ht => hmono t ht n (mem_range.mp hn))
    _ ≤ ∑ _ ∈ range N, Q := sum_le_sum (fun n hn => hbound n (mem_range.mp hn))
    _ = Q*N := by simp [mul_comm]

def skew (f : ℕ → ℕ) (n : ℕ) : ℤ :=
  if f n < f (n+1) then 1 else if f (n+1) < f n then -1 else 0

def ramp (n : ℕ) : ℕ := n % 3

def raised (n : ℕ) : ℕ := if 5 ∣ n then 3 else ramp n

lemma ramp_le_raised (n : ℕ) : ramp n ≤ raised n ∧ raised n ≤ 3 := by
  have hn : ramp n < 3 := Nat.mod_lt n (by omega)
  unfold raised
  split_ifs <;> omega

lemma raised_eq_off_multiples (n : ℕ) (hn : ¬5 ∣ n) : raised n=ramp n := if_neg hn

lemma ramp_period (k n : ℕ) : ramp (15*k+n)=ramp n := by
  simp [ramp,Nat.add_mod,Nat.mul_mod]

lemma raised_period (k n : ℕ) : raised (15*k+n)=raised n := by
  have hd : 5 ∣ 15*k := ⟨3*k,by ring⟩
  have he : 5 ∣ 15*k+n ↔ 5 ∣ n := (Nat.dvd_add_iff_right hd).symm
  simp only [raised,he,ramp_period]

private lemma skew_period (f : ℕ → ℕ) (h : ∀ k n, f (15*k+n)=f n) (k n : ℕ) :
    skew f (15*k+n)=skew f n := by
  simp only [skew,show 15*k+n+1=15*k+(n+1) by omega,h]

private lemma sum_period (f : ℕ → ℤ) (h : ∀ k n, f (15*k+n)=f n) (K : ℕ) :
    (∑ n ∈ range (15*K), f n) = (K : ℤ)*(∑ n ∈ range 15, f n) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_add,Nat.mul_one,sum_range_add,ih]
    simp_rw [h]
    push_cast
    ring

lemma ramp_skew_sum (K : ℕ) : (∑ n ∈ range (15*K), skew ramp n)=5*K := by
  rw [sum_period _ (skew_period ramp ramp_period)]
  have hs : (∑ n ∈ range 15, skew ramp n) = 5 := by decide +kernel
  rw [hs]
  ring

lemma raised_skew_sum (K : ℕ) : (∑ n ∈ range (15*K), skew raised n)=3*K := by
  rw [sum_period _ (skew_period raised raised_period)]
  have hs : (∑ n ∈ range 15, skew raised n) = 3 := by decide +kernel
  rw [hs]
  ring

/-- Even an update supported on multiples of a prime can have a linear
signed comparison increment for bounded monotone model labels. -/
theorem insertion_increment (K : ℕ) :
    (∑ n ∈ range (15*K), (skew raised n-skew ramp n)) = -2*K := by
  rw [sum_sub_distrib,raised_skew_sum,ramp_skew_sum]
  ring

/-- Thus no uniform square-root-in-N estimate follows from those model
properties alone. This does not assert a counterexample for actual prime
labels, which have additional arithmetic structure. -/
theorem no_square_root_bound_from_monotonicity :
    ¬∃ C : ℕ, ∀ N : ℕ,
      (∑ n ∈ range N, (skew raised n-skew ramp n))^2 ≤ (C : ℤ)*N := by
  rintro ⟨C,hC⟩
  have h := hC (15*(4*C+1))
  rw [insertion_increment] at h
  push_cast at h
  have hnonneg : (0 : ℤ) ≤ C := Int.natCast_nonneg C
  nlinarith [sq_nonneg (C : ℤ)]

#print axioms monotone_label_change_budget
#print axioms insertion_increment
#print axioms no_square_root_bound_from_monotonicity
end Erdos371.MonotoneInsertion
