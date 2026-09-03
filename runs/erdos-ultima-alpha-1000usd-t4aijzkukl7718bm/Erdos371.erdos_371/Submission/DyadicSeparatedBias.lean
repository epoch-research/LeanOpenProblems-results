import Submission.Explore

/-! A finite-label dyadic subdivision model. It is exactly invariant under
multiplication by two, has no adjacent ties past the initial indices, and
has a persistent comparison bias. It is NOT a model of maxPrimeFac and is
NOT a disproof of Erdős 371. -/
namespace Erdos371.DyadicSeparatedBias
open Finset Filter
open scoped Topology

/-- A label different from both endpoints, including equal endpoints. -/
def middle (a b : Fin 4) : Fin 4 :=
  match a.val, b.val with
  | 0, 0 => 1
  | 0, 1 => 2
  | 0, _ => 1
  | 1, 0 => 2
  | 1, 1 => 2
  | 1, 2 => 0
  | 1, _ => 2
  | 2, 0 => 3
  | 2, 1 => 0
  | 2, 2 => 3
  | 2, _ => 0
  | _, 0 => 1
  | _, _ => 0

lemma middle_distinct : ∀ a b : Fin 4, middle a b ≠ a ∧ middle a b ≠ b := by
  decide +kernel

/-- The ordered endpoint labels of the n-th dyadic interval. -/
def edge (n : ℕ) : Fin 4 × Fin 4 :=
  if n ≤ 1 then (0,0) else
    let ab := edge (n/2)
    let c := middle ab.1 ab.2
    if n % 2 = 0 then (ab.1,c) else (c,ab.2)
termination_by n
decreasing_by omega

@[simp] lemma edge_zero : edge 0 = (0,0) := by rw [edge]; simp
@[simp] lemma edge_one : edge 1 = (0,0) := by rw [edge]; simp

lemma edge_two_mul (n : ℕ) (hn : 0 < n) :
    edge (2*n) = ((edge n).1, middle (edge n).1 (edge n).2) := by
  rw [edge]
  simp only [show ¬2*n ≤ 1 by omega, if_false]
  have hd : 2*n/2=n := by omega
  have hm : 2*n%2=0 := by omega
  simp only [hd,hm,if_true]

lemma edge_two_mul_add_one (n : ℕ) (hn : 0 < n) :
    edge (2*n+1) = (middle (edge n).1 (edge n).2, (edge n).2) := by
  rw [edge]
  simp only [show ¬2*n+1 ≤ 1 by omega, if_false]
  have hd : (2*n+1)/2=n := by omega
  have hm : (2*n+1)%2≠0 := by omega
  simp only [hd,hm,if_false]

/-- The recursively defined intervals fit together into a single sequence. -/
lemma edge_compatible (n : ℕ) (hn : 0 < n) :
    (edge n).2 = (edge (n+1)).1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      rw [show 1+1=2*1 by omega,edge_two_mul 1 (by omega),edge_one]
    have hhalf : 0 < n/2 := by omega
    by_cases heven : n%2=0
    · have he : n=2*(n/2) := by omega
      conv_lhs => rw [he]
      conv_rhs => rw [he]
      rw [edge_two_mul _ hhalf,edge_two_mul_add_one _ hhalf]
    · have he : n=2*(n/2)+1 := by omega
      have he' : n+1=2*(n/2+1) := by omega
      rw [he',edge_two_mul _ (by omega)]
      conv_lhs => rw [he]
      rw [edge_two_mul_add_one _ hhalf]
      exact ih (n/2) (by omega) hhalf

def label (n : ℕ) : Fin 4 := (edge n).1

lemma edge_eq_labels (n : ℕ) (hn : 0 < n) :
    edge n = (label n,label (n+1)) := by
  apply Prod.ext
  · rfl
  · exact edge_compatible n hn

theorem label_two_mul (n : ℕ) : label (2*n) = label n := by
  by_cases hn : n=0
  · subst n; rfl
  · change (edge (2*n)).1 = (edge n).1
    rw [edge_two_mul n (by omega)]

lemma label_two_mul_add_one (n : ℕ) (hn : 0 < n) :
    label (2*n+1) = middle (label n) (label (n+1)) := by
  unfold label
  rw [edge_two_mul_add_one n hn]
  exact congrArg (middle (edge n).1) (edge_compatible n hn)

/-- Unlike the mantissa example, this model has no small adjacent gaps:
the labels are distinct members of a fixed four-element ordered set. -/
theorem label_adjacent_ne (n : ℕ) (hn : 2 ≤ n) : label n ≠ label (n+1) := by
  have hh : 0 < n/2 := by omega
  have hd := middle_distinct (edge (n/2)).1 (edge (n/2)).2
  have he : (edge n).1 ≠ (edge n).2 := by
    by_cases hmod : n%2=0
    · have hn' : n=2*(n/2) := by omega
      rw [hn',edge_two_mul _ hh]
      exact hd.1.symm
    · have hn' : n=2*(n/2)+1 := by omega
      rw [hn',edge_two_mul_add_one _ hh]
      exact hd.2
  simpa only [edge_eq_labels n (by omega)] using he

def pairSign (a b : Fin 4) : ℤ := if a < b then 1 else -1

def sign (n : ℕ) : ℤ := pairSign (label n) (label (n+1))

def blockSkew : ℕ → Fin 4 → Fin 4 → ℤ
  | 0, a, b => pairSign a b
  | k+1, a, b => blockSkew k a (middle a b) + blockSkew k (middle a b) b

/-- All twelve distinct endpoint pairs have positive discrepancy after six
subdivisions. This finite certificate is checked in the Lean kernel. -/
lemma six_step_bound : ∀ a b : Fin 4, a ≠ b → 2 ≤ blockSkew 6 a b := by
  decide +kernel

lemma blockSkew_eq_sum (k n : ℕ) (hn : 0 < n) :
    (∑ j ∈ range (2^k), sign (2^k*n+j)) = blockSkew k (label n) (label (n+1)) := by
  induction k generalizing n with
  | zero => simp [blockSkew,sign]
  | succ k ih =>
    have hp : 2^(k+1) = 2^k+2^k := by rw [pow_succ]; omega
    rw [hp,sum_range_add]
    have he : (∑ j ∈ range (2^k), sign ((2^k+2^k)*n+j)) +
        (∑ j ∈ range (2^k), sign ((2^k+2^k)*n+(2^k+j))) =
        (∑ j ∈ range (2^k), sign (2^k*(2*n)+j)) +
        (∑ j ∈ range (2^k), sign (2^k*(2*n+1)+j)) := by
      congr 1 <;> apply sum_congr rfl <;> intro j hj <;> congr 1 <;> ring
    rw [he,ih (2*n) (by omega),ih (2*n+1) (by omega)]
    rw [label_two_mul,label_two_mul_add_one n hn,
      show 2*n+1+1=2*(n+1) by omega,label_two_mul,blockSkew]

lemma block_sixty_four_lower (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ ∑ j ∈ range 64, sign (64*n+j) := by
  have he := blockSkew_eq_sum 6 n (by omega)
  norm_num only [Nat.reducePow] at he
  rw [he]
  exact six_step_bound _ _ (label_adjacent_ne n hn)

lemma sign_lower (n : ℕ) : -1 ≤ sign n := by
  unfold sign pairSign
  split_ifs <;> norm_num

lemma block_sixty_four_trivial_lower (n : ℕ) :
    -64 ≤ ∑ j ∈ range 64, sign (64*n+j) := by
  have h := sum_le_sum (s := range 64) (fun j _ => sign_lower (64*n+j))
  simpa using h

lemma sign_sum_blocks (M : ℕ) :
    (∑ n ∈ range (64*M), sign n) =
      ∑ m ∈ range M, ∑ j ∈ range 64, sign (64*m+j) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ (f := fun m => ∑ j ∈ range 64, sign (64*m+j))]
    rw [Nat.mul_succ,sum_range_add,ih]

/-- A positive signed discrepancy along all endpoints divisible by 64. -/
theorem sign_prefix_block_lower (M : ℕ) :
    2*(M : ℤ)-132 ≤ ∑ n ∈ range (64*M), sign n := by
  rw [sign_sum_blocks]
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [sum_range_succ]
    push_cast
    by_cases hM : 2 ≤ M
    · have hb := block_sixty_four_lower M hM
      linarith
    · have h0 := block_sixty_four_trivial_lower 0
      have h1 := block_sixty_four_trivial_lower 1
      interval_cases M <;> simp only [sum_range_zero, sum_range_one] <;> norm_num only [Int.natCast_zero, Int.natCast_one] <;> linarith

lemma sign_sum_count (N : ℕ) :
    (∑ n ∈ range N, sign n) =
      2 * (((range N).filter (fun n => label n < label (n+1))).card : ℤ) - N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp)]
      simp only [sign, pairSign, if_pos h]
      push_cast
      linarith
    · simp only [sign, pairSign, if_neg h]
      push_cast
      linarith

/-- Exact dyadic invariance and uniform adjacent separation alone do not
force half-density of rises. This statement is only about `label`. -/
theorem not_half_density :
    ¬ {n | label n < label (n+1)}.HasDensity (1/2) := by
  intro h
  rw [Erdos371.density_iff_count] at h
  have he := h.eventually_lt_const (show (1/2 : ℝ) < 65/128 by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.1 he
  let M := K+133
  have hb := sign_prefix_block_lower M
  rw [sign_sum_count] at hb
  have hb' : 2*(M : ℝ)-132 ≤
      2 * (((range (64*M)).filter (fun n => label n < label (n+1))).card : ℝ) -
        (64*M : ℕ) := by exact_mod_cast hb
  have hc := hK (64*M) (by dsimp [M]; omega)
  have hpos : (0 : ℝ) < (64*M : ℕ) := by positivity
  have hc' := (div_lt_iff₀ hpos).1 hc
  have hm : (132 : ℝ) < M := by exact_mod_cast (show 132 < M by dsimp [M]; omega)
  push_cast at hb' hc'
  linarith

/-- This model is deliberately not max-under-multiplication and is not
invariant under multiplication by three. -/
lemma not_arithmetic_max_model :
    label 15 ≠ max (label 3) (label 5) ∧ label (3*5) ≠ label 5 := by
  decide +kernel

#print axioms label_two_mul
#print axioms label_adjacent_ne
#print axioms six_step_bound
#print axioms sign_prefix_block_lower
#print axioms not_half_density
#print axioms not_arithmetic_max_model
end Erdos371.DyadicSeparatedBias
