import FormalConjectures.Util.ProblemImports

open Nat Finset


def powers_of_two_times_four (m : ℕ) : Finset ℕ :=
  if h : m = 0 then
    ∅
  else
    let a := m / 2
    let s_a := powers_of_two_times_four a
    let s' := s_a.image (fun x => 2 * x)
    if m % 2 = 0 then
      s'
    else
      insert 4 s'
termination_by m
decreasing_by
  omega


lemma sum_image_double (s : Finset ℕ) : (s.image (fun x => 2 * x)).sum id = 2 * s.sum id := by
  rw [sum_image]
  · simp
    rw [← mul_sum]
  · intro x _ y _ h
    dsimp at h
    omega


lemma powers_of_two_times_four_ge_four (m : ℕ) : ∀ x ∈ powers_of_two_times_four m, x ≥ 4 := by
  induction' m using Nat.strong_induction_on with m ih
  rw [powers_of_two_times_four]
  split_ifs with h hm
  · simp
  · -- m ≠ 0, m % 2 = 0
    intro x hx
    rcases mem_image.mp hx with ⟨y, hy, rfl⟩
    have hy_ge := ih (m / 2) (by omega) y hy
    omega
  · -- m ≠ 0, m % 2 ≠ 0
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · omega
    · rcases mem_image.mp hx with ⟨y, hy, rfl⟩
      have hy_ge := ih (m / 2) (by omega) y hy
      omega

lemma powers_of_two_times_four_sum (m : ℕ) : (powers_of_two_times_four m).sum id = 4 * m := by
  induction' m using Nat.strong_induction_on with m ih
  rw [powers_of_two_times_four]
  split_ifs with h hm
  · simp [h]
  · rw [sum_image_double]
    rw [ih (m / 2) (by omega)]
    omega
  · have h4 : 4 ∉ (powers_of_two_times_four (m / 2)).image (fun x => 2 * x) := by
      intro hc
      rcases mem_image.mp hc with ⟨y, hy, hy2⟩
      have hy_ge := powers_of_two_times_four_ge_four (m / 2) y hy
      omega
    rw [sum_insert h4]
    rw [sum_image_double]
    rw [ih (m / 2) (by omega)]
    dsimp [id]
    omega


lemma not_squarefree_of_four_dvd (r : ℕ) (h : 4 ∣ r) : ¬ Squarefree r := by
  intro h_sf
  have h2 : 2 * 2 ∣ r := h
  have hu := h_sf 2 h2
  rw [Nat.isUnit_iff] at hu
  omega

lemma not_squarefree_of_nine_dvd (r : ℕ) (h : 9 ∣ r) : ¬ Squarefree r := by
  intro h_sf
  have h2 : 3 * 3 ∣ r := h
  have hu := h_sf 3 h2
  rw [Nat.isUnit_iff] at hu
  omega


lemma powers_of_two_times_four_dvd_four (m : ℕ) : ∀ x ∈ powers_of_two_times_four m, 4 ∣ x := by
  induction' m using Nat.strong_induction_on with m ih
  rw [powers_of_two_times_four]
  split_ifs with h hm
  · simp
  · intro x hx
    rcases mem_image.mp hx with ⟨y, hy, rfl⟩
    have hy_dvd := ih (m / 2) (by omega) y hy
    rcases hy_dvd with ⟨k, rfl⟩
    use 2 * k
    omega
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · use 1
    · rcases mem_image.mp hx with ⟨y, hy, rfl⟩
      have hy_dvd := ih (m / 2) (by omega) y hy
      rcases hy_dvd with ⟨k, rfl⟩
      use 2 * k
      omega

lemma powers_of_two_times_four_not_squarefree (m : ℕ) : ∀ x ∈ powers_of_two_times_four m, ¬ Squarefree x := by
  intro x hx
  apply not_squarefree_of_four_dvd x
  exact powers_of_two_times_four_dvd_four m x hx


def A256012_solution (n : ℕ) : Finset ℕ :=
  match n % 4 with
  | 0 => powers_of_two_times_four (n / 4)
  | 1 => insert 9 (powers_of_two_times_four ((n - 1) / 4 - 2))
  | 2 => insert 18 (powers_of_two_times_four ((n - 2) / 4 - 4))
  | _ => insert 27 (powers_of_two_times_four ((n - 3) / 4 - 6))

lemma A256012_solution_sum (n : ℕ) (hn : n ≥ 24) : (A256012_solution n).sum id = n := by
  have h_lt : n % 4 < 4 := Nat.mod_lt n (by decide)
  rcases show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega with heq | heq | heq | heq
  · unfold A256012_solution
    rw [heq]
    rw [powers_of_two_times_four_sum]
    omega
  · unfold A256012_solution
    rw [heq]
    have h9 : 9 ∉ powers_of_two_times_four ((n - 1) / 4 - 2) := by
      intro hc
      have h_div := powers_of_two_times_four_dvd_four ((n - 1) / 4 - 2) 9 hc
      omega
    rw [sum_insert h9]
    rw [powers_of_two_times_four_sum]
    dsimp [id]
    omega
  · unfold A256012_solution
    rw [heq]
    have h18 : 18 ∉ powers_of_two_times_four ((n - 2) / 4 - 4) := by
      intro hc
      have h_div := powers_of_two_times_four_dvd_four ((n - 2) / 4 - 4) 18 hc
      omega
    rw [sum_insert h18]
    rw [powers_of_two_times_four_sum]
    dsimp [id]
    omega
  · unfold A256012_solution
    rw [heq]
    have h27 : 27 ∉ powers_of_two_times_four ((n - 3) / 4 - 6) := by
      intro hc
      have h_div := powers_of_two_times_four_dvd_four ((n - 3) / 4 - 6) 27 hc
      omega
    rw [sum_insert h27]
    rw [powers_of_two_times_four_sum]
    dsimp [id]
    omega

lemma A256012_solution_not_squarefree (n : ℕ) :
    ∀ x ∈ A256012_solution n, ¬ Squarefree x := by
  have h_lt : n % 4 < 4 := Nat.mod_lt n (by decide)
  rcases show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega with heq | heq | heq | heq
  · unfold A256012_solution
    rw [heq]
    exact powers_of_two_times_four_not_squarefree (n / 4)
  · unfold A256012_solution
    rw [heq]
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · apply not_squarefree_of_nine_dvd 9 (by decide)
    · exact powers_of_two_times_four_not_squarefree ((n - 1) / 4 - 2) x hx
  · unfold A256012_solution
    rw [heq]
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · apply not_squarefree_of_nine_dvd 18 (by decide)
    · exact powers_of_two_times_four_not_squarefree ((n - 2) / 4 - 4) x hx
  · unfold A256012_solution
    rw [heq]
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · apply not_squarefree_of_nine_dvd 27 (by decide)
    · exact powers_of_two_times_four_not_squarefree ((n - 3) / 4 - 6) x hx


lemma le_sum_of_mem {s : Finset ℕ} (x : ℕ) (hx : x ∈ s) : x ≤ s.sum id := by
  have h := single_le_sum (fun (i : ℕ) _ => Nat.zero_le i) hx
  exact h


lemma A256012_solution_pos (n : ℕ) : ∀ x ∈ A256012_solution n, 0 < x := by
  have h_lt : n % 4 < 4 := Nat.mod_lt n (by decide)
  rcases show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega with heq | heq | heq | heq
  · unfold A256012_solution
    rw [heq]
    intro x hx
    have h_ge := powers_of_two_times_four_ge_four (n / 4) x hx
    omega
  · unfold A256012_solution
    rw [heq]
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · omega
    · have h_ge := powers_of_two_times_four_ge_four ((n - 1) / 4 - 2) x hx
      omega
  · unfold A256012_solution
    rw [heq]
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · omega
    · have h_ge := powers_of_two_times_four_ge_four ((n - 2) / 4 - 4) x hx
      omega
  · unfold A256012_solution
    rw [heq]
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · omega
    · have h_ge := powers_of_two_times_four_ge_four ((n - 3) / 4 - 6) x hx
      omega

/--
A256012: Number of partitions of $n$ into distinct parts that are not squarefree.
This is the number of finite subsets of positive integers $P$ such that $\sum_{k \in P} k = n$ and every element $k \in P$ is not squarefree.
-/
def A256012 (n : ℕ) : ℕ :=
  -- The parts must be $\le n$ to sum to $n$.
  -- This is $\{1, 2, \dots, n\}$
  let potential_parts : Finset ℕ := range (n + 1) \ {0}

  -- We count all subsets P of potential_parts that satisfy the sum and the property.
  card <| filter (fun P : Finset ℕ =>
    P.sum id = n ∧
    (∀ k ∈ P, ¬ Squarefree k)
  ) (powerset potential_parts)

/--
Conjecture: a(n) > 0 for n > 23.
-/
theorem oeis_256012_conjecture_0 (n : ℕ) (hn : n > 23) : A256012 n > 0 := by
  unfold A256012
  dsimp
  apply Finset.card_pos.mpr
  use A256012_solution n
  simp only [mem_filter, mem_powerset]
  refine ⟨?_, A256012_solution_sum n (by omega), A256012_solution_not_squarefree n⟩
  intro x hx
  simp only [mem_sdiff, mem_range, mem_singleton]
  constructor
  · have h_le := le_sum_of_mem x hx
    rw [A256012_solution_sum n (by omega)] at h_le
    omega
  · have h_pos := A256012_solution_pos n x hx
    omega
