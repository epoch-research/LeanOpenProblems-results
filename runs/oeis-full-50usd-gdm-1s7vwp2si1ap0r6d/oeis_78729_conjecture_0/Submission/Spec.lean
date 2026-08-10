import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
The product $(k+1)(k+2)\cdots(k+n)$.
-/
def A078729_product (n k : ℕ) : ℕ :=
  (Finset.range n).prod (fun i ↦ k + i + 1)

/--
A078729: $a(n)$ is the least positive integer $k$ such that
$$(k+1)(k+2)\cdots(k+n) + 1$$
is prime, if such $k$ exists; otherwise, $a(n) = 0$.
-/
noncomputable def A078729 (n : ℕ) : ℕ :=
  sInf { k : ℕ | k > 0 ∧ (A078729_product n k + 1).Prime }

lemma A078729_product_4 (k : ℕ) : A078729_product 4 k + 1 = (k^2 + 5 * k + 5) * (k^2 + 5 * k + 5) := by
  unfold A078729_product
  simp only [prod_range_succ, prod_range_zero, one_mul]
  ring

lemma not_prime_mul_self {x : ℕ} (h : Nat.Prime (x * x)) : False := by
  have hd : x ∣ x * x := by use x
  cases h.eq_one_or_self_of_dvd x hd with
  | inl h1 =>
    subst h1
    norm_num at h
  | inr h2 =>
    cases x with
    | zero => norm_num at h
    | succ x =>
      have h1 : (x + 1) * 1 = (x + 1) * (x + 1) := by omega
      have h2 : 1 = x + 1 := Nat.eq_of_mul_eq_mul_left (by omega) h1
      have hx : x = 0 := by omega
      subst hx
      norm_num at h

lemma A078729_product_0 (k : ℕ) : A078729_product 0 k = 1 := by
  unfold A078729_product
  simp only [prod_range_zero]

lemma A078729_zero : A078729 0 = 1 := by
  unfold A078729
  have hS : { k : ℕ | k > 0 ∧ (A078729_product 0 k + 1).Prime } = { k : ℕ | k > 0 } := by
    ext k
    simp only [mem_setOf_eq, A078729_product_0]
    norm_num
  rw [hS]
  have h_nonempty : { k : ℕ | k > 0 }.Nonempty := ⟨1, by simp⟩
  have h_mem : sInf { k : ℕ | k > 0 } ∈ { k : ℕ | k > 0 } := Nat.sInf_mem h_nonempty
  simp only [mem_setOf_eq] at h_mem
  have h_le : sInf { k : ℕ | k > 0 } ≤ 1 := by
    by_contra h_lt
    push_neg at h_lt
    have h_not_mem : 1 ∉ { k : ℕ | k > 0 } := Nat.notMem_of_lt_sInf h_lt
    simp only [mem_setOf_eq] at h_not_mem
    omega
  omega

lemma A078729_product_1 (k : ℕ) : A078729_product 1 k = k + 1 := by
  unfold A078729_product
  simp only [prod_range_one]

lemma A078729_one : A078729 1 = 1 := by
  unfold A078729
  have hS : 1 ∈ { k : ℕ | k > 0 ∧ (A078729_product 1 k + 1).Prime } := by
    simp only [mem_setOf_eq]
    constructor
    · omega
    · rw [A078729_product_1]
      norm_num
  have h_nonempty : { k : ℕ | k > 0 ∧ (A078729_product 1 k + 1).Prime }.Nonempty := ⟨1, hS⟩
  have h_mem : sInf { k : ℕ | k > 0 ∧ (A078729_product 1 k + 1).Prime } ∈ { k : ℕ | k > 0 ∧ (A078729_product 1 k + 1).Prime } := Nat.sInf_mem h_nonempty
  simp only [mem_setOf_eq] at h_mem
  have h_le : sInf { k : ℕ | k > 0 ∧ (A078729_product 1 k + 1).Prime } ≤ 1 := Nat.sInf_le hS
  have h_gt : sInf { k : ℕ | k > 0 ∧ (A078729_product 1 k + 1).Prime } > 0 := h_mem.1
  omega

lemma A078729_product_2 (k : ℕ) : A078729_product 2 k = (k + 1) * (k + 2) := by
  unfold A078729_product
  simp only [prod_range_succ, prod_range_zero, one_mul]

lemma A078729_two : A078729 2 = 1 := by
  unfold A078729
  have hS : 1 ∈ { k : ℕ | k > 0 ∧ (A078729_product 2 k + 1).Prime } := by
    simp only [mem_setOf_eq]
    constructor
    · omega
    · rw [A078729_product_2]
      norm_num
  have h_nonempty : { k : ℕ | k > 0 ∧ (A078729_product 2 k + 1).Prime }.Nonempty := ⟨1, hS⟩
  have h_mem : sInf { k : ℕ | k > 0 ∧ (A078729_product 2 k + 1).Prime } ∈ { k : ℕ | k > 0 ∧ (A078729_product 2 k + 1).Prime } := Nat.sInf_mem h_nonempty
  simp only [mem_setOf_eq] at h_mem
  have h_le : sInf { k : ℕ | k > 0 ∧ (A078729_product 2 k + 1).Prime } ≤ 1 := Nat.sInf_le hS
  have h_gt : sInf { k : ℕ | k > 0 ∧ (A078729_product 2 k + 1).Prime } > 0 := h_mem.1
  omega

lemma A078729_product_3 (k : ℕ) : A078729_product 3 k = (k + 1) * (k + 2) * (k + 3) := by
  unfold A078729_product
  simp only [prod_range_succ, prod_range_zero, one_mul]

lemma A078729_three : A078729 3 = 2 := by
  unfold A078729
  have hS : 2 ∈ { k : ℕ | k > 0 ∧ (A078729_product 3 k + 1).Prime } := by
    simp only [mem_setOf_eq]
    constructor
    · omega
    · rw [A078729_product_3]
      norm_num
  have h_nonempty : { k : ℕ | k > 0 ∧ (A078729_product 3 k + 1).Prime }.Nonempty := ⟨2, hS⟩
  have h_mem : sInf { k : ℕ | k > 0 ∧ (A078729_product 3 k + 1).Prime } ∈ { k : ℕ | k > 0 ∧ (A078729_product 3 k + 1).Prime } := Nat.sInf_mem h_nonempty
  simp only [mem_setOf_eq] at h_mem
  have h_le : sInf { k : ℕ | k > 0 ∧ (A078729_product 3 k + 1).Prime } ≤ 2 := Nat.sInf_le hS
  have h_not_1 : 1 ∉ { k : ℕ | k > 0 ∧ (A078729_product 3 k + 1).Prime } := by
    simp only [mem_setOf_eq, not_and]
    intro _
    rw [A078729_product_3]
    decide
  have h_gt_1 : sInf { k : ℕ | k > 0 ∧ (A078729_product 3 k + 1).Prime } > 1 := by
    by_contra! h_le_1
    have h_eq : sInf { k : ℕ | k > 0 ∧ (A078729_product 3 k + 1).Prime } = 1 := by omega
    rw [h_eq] at h_mem
    exact h_not_1 h_mem
  omega

lemma not_prime_product_4 (k : ℕ) : ¬ (A078729_product 4 k + 1).Prime := by
  intro h
  rw [A078729_product_4] at h
  exact not_prime_mul_self h

lemma A078729_four : A078729 4 = 0 := by
  unfold A078729
  rw [sInf_eq_zero]
  right
  ext k
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨-, hp⟩
  exact not_prime_product_4 k hp


lemma sInf_eq_zero_iff {S : Set ℕ} (hS : ∀ x ∈ S, x > 0) : sInf S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      have h_nonempty : S.Nonempty := ⟨x, hx⟩
      have h_mem : sInf S ∈ S := Nat.sInf_mem h_nonempty
      have h_gt : sInf S > 0 := hS (sInf S) h_mem
      omega
    · intro hx
      exact False.elim hx
  · intro h
    subst h
    exact Nat.sInf_empty

/--
Conjecture: $a(n) = 0$ if and only if $n=4$.
-/
theorem oeis_78729_conjecture_0 : ∀ n : ℕ, A078729 n = 0 ↔ n = 4 := by
  intro n
  constructor
  · intro h
    by_cases h0 : n = 0
    · subst h0; rw [A078729_zero] at h; contradiction
    by_cases h1 : n = 1
    · subst h1; rw [A078729_one] at h; contradiction
    by_cases h2 : n = 2
    · subst h2; rw [A078729_two] at h; contradiction
    by_cases h3 : n = 3
    · subst h3; rw [A078729_three] at h; contradiction
    by_cases h4 : n = 4
    · exact h4
    have hn5 : n ≥ 5 := by omega
    have h_empty : { k : ℕ | k > 0 ∧ (A078729_product n k + 1).Prime } = ∅ := by
      unfold A078729 at h
      rwa [sInf_eq_zero_iff] at h
      rintro x ⟨hx1, -⟩
      exact hx1
    sorry
  · intro h
    subst h
    exact A078729_four

