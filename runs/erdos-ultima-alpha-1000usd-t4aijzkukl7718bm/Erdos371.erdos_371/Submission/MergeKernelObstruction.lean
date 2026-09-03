import FormalConjecturesUtil

/-! An explicit split/merge moment-null construction. Both full and upper-half
largest-part comparisons can be asymmetric under fixed equal marginals and
independent low-mass moments. This finite model is NOT an arithmetic
counterexample and NOT a Lean formalization of Poisson–Dirichlet partitions. -/
namespace Erdos371.MergeKernelObstruction
open Finset
set_option autoImplicit false

def parts : Fin 10 → Finset ℕ
  | 0 => {24,30,36,10}
  | 1 => {24,66,10}
  | 2 => {30,60,10}
  | 3 => {36,54,10}
  | 4 => {90,10}
  | 5 => {25,31,37,7}
  | 6 => {25,68,7}
  | 7 => {31,62,7}
  | 8 => {37,56,7}
  | 9 => {93,7}

def firstWeight : Fin 10 → ℤ
  | 0 => 1 | 1 => -1 | 2 => -1 | 3 => -1 | 4 => 2 | _ => 0

def secondWeight : Fin 10 → ℤ
  | 5 => 1 | 6 => -1 | 7 => -1 | 8 => -1 | 9 => 2 | _ => 0

def largest (i : Fin 10) : ℕ := (parts i).sup id

def observations : Finset (Finset ℕ) := univ.biUnion fun i : Fin 10 => (parts i).powerset

def insertion (a : Fin 10 → ℤ) (s : Finset ℕ) : ℤ :=
  ∑ i : Fin 10, if s ⊆ parts i then a i else 0

def kernel (i j : Fin 10) : ℤ := firstWeight i*secondWeight j-secondWeight i*firstWeight j

def moment (s t : Finset ℕ) : ℤ :=
  ∑ i : Fin 10, ∑ j : Fin 10, if s ⊆ parts i ∧ t ⊆ parts j then kernel i j else 0

lemma mass_fixed : ∀ i : Fin 10, (∑ a ∈ parts i, a) = 100 := by decide +kernel
lemma firstWeight_sum : (∑ i : Fin 10, firstWeight i) = 0 := by decide +kernel
lemma secondWeight_sum : (∑ i : Fin 10, secondWeight i) = 0 := by decide +kernel
lemma kernel_row : ∀ i : Fin 10, (∑ j : Fin 10, kernel i j) = 0 := by decide +kernel
lemma kernel_column : ∀ j : Fin 10, (∑ i : Fin 10, kernel i j) = 0 := by decide +kernel
lemma kernel_abs : ∀ i j : Fin 10, |kernel i j| ≤ 4 := by decide +kernel

lemma insertion_outside (a : Fin 10 → ℤ) (s : Finset ℕ) (hs : s ∉ observations) :
    insertion a s = 0 := by
  have hn (i : Fin 10) : ¬s ⊆ parts i := by
    intro hi
    exact hs (mem_biUnion.mpr ⟨i,mem_univ _,mem_powerset.mpr hi⟩)
  simp [insertion,hn]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma first_small_finite : ∀ s ∈ observations, (∑ a ∈ s, a) < 54 →
    insertion firstWeight s = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma second_small_finite : ∀ s ∈ observations, (∑ a ∈ s, a) < 56 →
    insertion secondWeight s = 0 := by decide +kernel

lemma first_small (s : Finset ℕ) (hs : (∑ a ∈ s, a) < 54) :
    insertion firstWeight s = 0 := by
  by_cases h : s ∈ observations
  · exact first_small_finite s h hs
  · exact insertion_outside _ s h

lemma second_small (s : Finset ℕ) (hs : (∑ a ∈ s, a) < 56) :
    insertion secondWeight s = 0 := by
  by_cases h : s ∈ observations
  · exact second_small_finite s h hs
  · exact insertion_outside _ s h

lemma moment_factorization (s t : Finset ℕ) : moment s t =
    insertion firstWeight s*insertion secondWeight t-
      insertion secondWeight s*insertion firstWeight t := by
  unfold moment insertion
  rw [sum_mul_sum,sum_mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  unfold kernel
  split_ifs <;> simp_all

/-- The null data extend beyond the one-partition mass budget 100. -/
theorem moment_zero (s t : Finset ℕ) (hst : (∑ a ∈ s, a)+(∑ b ∈ t, b) < 110) :
    moment s t = 0 := by
  rw [moment_factorization]
  have h1 : insertion firstWeight s*insertion secondWeight t = 0 := by
    by_cases hs : (∑ a ∈ s, a) < 54
    · rw [first_small s hs,zero_mul]
    · rw [second_small t (by omega),mul_zero]
  have h2 : insertion secondWeight s*insertion firstWeight t = 0 := by
    by_cases hs : (∑ a ∈ s, a) < 56
    · rw [second_small s hs,zero_mul]
    · rw [first_small t (by omega),mul_zero]
  rw [h1,h2,sub_self]

lemma rising_kernel : (∑ i : Fin 10, ∑ j : Fin 10,
    if largest i < largest j then kernel i j else 0) = 8 := by decide +kernel

lemma upper_half_rising_kernel : (∑ i : Fin 10, ∑ j : Fin 10,
    if 50 < largest i ∧ 50 < largest j ∧ largest i < largest j then kernel i j else 0) = 7 := by
  decide +kernel

noncomputable def coupling (i j : Fin 10) : ℝ := 1/100+(kernel i j : ℝ)/1000

lemma coupling_positive (i j : Fin 10) : 0 < coupling i j := by
  have h : |(kernel i j : ℝ)| ≤ 4 := by exact_mod_cast kernel_abs i j
  have hl := (abs_le.mp h).1
  unfold coupling
  linarith

lemma coupling_row (i : Fin 10) : (∑ j : Fin 10, coupling i j) = 1/10 := by
  have h : (∑ j : Fin 10, (kernel i j : ℝ)) = 0 := by exact_mod_cast kernel_row i
  simp only [coupling,sum_add_distrib,← sum_div,h]
  norm_num

lemma coupling_column (j : Fin 10) : (∑ i : Fin 10, coupling i j) = 1/10 := by
  have h : (∑ i : Fin 10, (kernel i j : ℝ)) = 0 := by exact_mod_cast kernel_column j
  simp only [coupling,sum_add_distrib,← sum_div,h]
  norm_num

/-- Every low-mass inclusion moment agrees exactly with the independent
coupling of the same uniform marginals. -/
theorem coupling_low_moments (s t : Finset ℕ)
    (hst : (∑ a ∈ s, a)+(∑ b ∈ t, b) ≤ 100) :
    (∑ i : Fin 10, ∑ j : Fin 10,
      if s ⊆ parts i ∧ t ⊆ parts j then coupling i j else 0) =
    ∑ i : Fin 10, ∑ j : Fin 10,
      if s ⊆ parts i ∧ t ⊆ parts j then (1/10 : ℝ)*(1/10) else 0 := by
  have hz : (∑ i : Fin 10, ∑ j : Fin 10,
      if s ⊆ parts i ∧ t ⊆ parts j then (kernel i j : ℝ) else 0) = 0 := by
    exact_mod_cast moment_zero s t (by omega)
  have he (i j : Fin 10) :
      (if s ⊆ parts i ∧ t ⊆ parts j then coupling i j else 0) =
      (if s ⊆ parts i ∧ t ⊆ parts j then (1/10 : ℝ)*(1/10) else 0)+
      (if s ⊆ parts i ∧ t ⊆ parts j then (kernel i j : ℝ) else 0)/1000 := by
    split_ifs <;> simp [coupling]
    ring
  simp_rw [he,sum_add_distrib,← sum_div,hz,zero_div,add_zero]

lemma coupling_mass_linear (P : Fin 10 → Fin 10 → Prop) [DecidableRel P] :
    (∑ i : Fin 10, ∑ j : Fin 10, if P i j then coupling i j else 0) =
      (∑ i : Fin 10, ∑ j : Fin 10, if P i j then (1 : ℝ) else 0)/100+
      (∑ i : Fin 10, ∑ j : Fin 10, if P i j then (kernel i j : ℝ) else 0)/1000 := by
  have he (i j : Fin 10) : (if P i j then coupling i j else 0) =
      (if P i j then (1 : ℝ) else 0)/100+
      (if P i j then (kernel i j : ℝ) else 0)/1000 := by
    split_ifs <;> simp [coupling]
  simp_rw [he,sum_add_distrib,← sum_div]

theorem coupling_rising_mass :
    (∑ i : Fin 10, ∑ j : Fin 10, if largest i < largest j then coupling i j else 0) =
      229/500 := by
  rw [coupling_mass_linear]
  have h1 : (∑ i : Fin 10, ∑ j : Fin 10, if largest i < largest j then (1 : ℤ) else 0) = 45 := by
    decide +kernel
  have h1' : (∑ i : Fin 10, ∑ j : Fin 10, if largest i < largest j then (1 : ℝ) else 0) = 45 := by
    exact_mod_cast h1
  have h2 : (∑ i : Fin 10, ∑ j : Fin 10, if largest i < largest j then (kernel i j : ℝ) else 0) = 8 := by
    exact_mod_cast rising_kernel
  rw [h1',h2]
  norm_num

theorem coupling_upper_half_rising_mass :
    (∑ i : Fin 10, ∑ j : Fin 10,
      if 50 < largest i ∧ 50 < largest j ∧ largest i < largest j then coupling i j else 0) =
      287/1000 := by
  rw [coupling_mass_linear]
  have h1 : (∑ i : Fin 10, ∑ j : Fin 10,
      if 50 < largest i ∧ 50 < largest j ∧ largest i < largest j then (1 : ℤ) else 0) = 28 := by
    decide +kernel
  have h1' : (∑ i : Fin 10, ∑ j : Fin 10,
      if 50 < largest i ∧ 50 < largest j ∧ largest i < largest j then (1 : ℝ) else 0) = 28 := by
    exact_mod_cast h1
  have h2 : (∑ i : Fin 10, ∑ j : Fin 10,
      if 50 < largest i ∧ 50 < largest j ∧ largest i < largest j then (kernel i j : ℝ) else 0) = 7 := by
    exact_mod_cast upper_half_rising_kernel
  rw [h1',h2]
  norm_num


#print axioms moment_zero
#print axioms upper_half_rising_kernel
#print axioms coupling_positive
#print axioms coupling_low_moments
#print axioms coupling_upper_half_rising_mass
end Erdos371.MergeKernelObstruction
