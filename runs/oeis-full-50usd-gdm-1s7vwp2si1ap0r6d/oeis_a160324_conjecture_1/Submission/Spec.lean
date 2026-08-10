import FormalConjectures.Util.ProblemImports

open Nat

/--
$p_k(x) = \frac{(k-2)x(x-1)}{2} + x$ is the $x$-th $k$-gonal number.
-/
def polygonal_number (k : ℕ) (x : ℕ) : ℕ :=
  (k - 2) * (x * (x - 1) / 2) + x

/--
$p_5(y) = \frac{3y^2 - y}{2}$ is the $y$-th pentagonal number.
-/
def pentagonal (y : ℕ) : ℕ := polygonal_number 5 y

/--
$p_6(z) = 2z^2 - z$ is the $z$-th hexagonal number.
-/
def hexagonal (z : ℕ) : ℕ := polygonal_number 6 z

/--
A160324: Number of ways to express $n$ as the sum of a square, a pentagonal number and a hexagonal number.
$$a(n) = \left| \left\{(x, y, z) \in \mathbb{N}^3 : x^2 + p_5(y) + p_6(z) = n \right\} \right|$$
-/
def a (n : ℕ) : ℕ :=
  let P5 := pentagonal
  let P6 := hexagonal
  -- A practical upper bound for $x, y, z$ is $\lfloor\sqrt{n}\rfloor + 2$.
  -- Since $p_6(z) \approx 2z^2$, $z$ is bounded by approximately $\sqrt{n/2}$.
  let max_coord_bound := n.sqrt + 2

  (Finset.range max_coord_bound).sum fun x =>
  (Finset.range max_coord_bound).sum fun y =>
  (Finset.range max_coord_bound).sum fun z =>
    if x^2 + P5 y + P6 z = n then 1 else 0

/--
%C A160324 On Aug 12 2009, _Zhi-Wei Sun_ made the following general conjecture on diagonal representations by polygonal numbers: For each integer m>2, any natural number n can be written in the form p_{m+1}(x_1)+...+p_{2m}(x_m) with x_1,...,x_m nonnegative integers, where p_k(x)=(k-2)x(x-1)/2+x (x=0,1,2,...) are k-gonal numbers.
-/
theorem polygonal_number_zero (k : ℕ) : polygonal_number k 0 = 0 := by
  rfl

theorem polygonal_number_one (k : ℕ) : polygonal_number k 1 = 1 := by
  rfl

theorem polygonal_number_ge_one (k : ℕ) (x : ℕ) (hx : x ≥ 1) : polygonal_number k x ≥ 1 := by
  unfold polygonal_number
  cases x with
  | zero => omega
  | succ x' =>
    simp
    omega

theorem oeis_a160324_conjecture_1 (m : ℕ) (hm : m > 2) (n : ℕ) :
  ∃ (x : Fin m → ℕ), n = Finset.sum Finset.univ (fun i : Fin m => polygonal_number (m + (i : ℕ) + 1) (x i)) := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases hn : n < m
  · -- Case 1: n < m
    induction n with
    | zero =>
      use (fun _ => 0)
      simp [polygonal_number]
    | succ n' ih' =>
      have hn' : n' < m := by omega
      have ih_n' : ∃ (x : Fin m → ℕ), n' = Finset.sum Finset.univ (fun i : Fin m => polygonal_number (m + (i : ℕ) + 1) (x i)) := by
        apply ih n' (by omega)
      obtain ⟨x, hx⟩ := ih_n'
      have h_exists_zero : ∃ i : Fin m, x i = 0 := by
        by_contra hc
        push_neg at hc
        have h_ge : ∀ i : Fin m, x i ≥ 1 := by
          intro i
          have h_neq : x i ≠ 0 := hc i
          omega
        have h_ge_m : Finset.sum Finset.univ (fun i : Fin m => polygonal_number (m + (i : ℕ) + 1) (x i)) ≥ m := by
          have h_ge_1 : ∀ i : Fin m, polygonal_number (m + (i : ℕ) + 1) (x i) ≥ 1 := by
            intro i
            apply polygonal_number_ge_one
            exact h_ge i
          have h_sum : Finset.sum Finset.univ (fun i : Fin m => polygonal_number (m + (i : ℕ) + 1) (x i)) ≥
                       Finset.sum Finset.univ (fun _ : Fin m => 1) := by
            apply Finset.sum_le_sum
            intro i _
            exact h_ge_1 i
          have h_const : Finset.sum Finset.univ (fun _ : Fin m => 1) = m := by
            simp
          omega
        rw [← hx] at h_ge_m
        omega
      obtain ⟨i, hi⟩ := h_exists_zero
      use (fun j => if j = i then 1 else x j)
      rw [hx]
      rw [← Finset.insert_erase (Finset.mem_univ i)]
      rw [Finset.sum_insert (Finset.notMem_erase i Finset.univ)]
      rw [Finset.sum_insert (Finset.notMem_erase i Finset.univ)]
      have h_sum : ∑ x_1 ∈ Finset.univ.erase i, polygonal_number (m + ↑x_1 + 1) (if x_1 = i then 1 else x x_1) =
                   ∑ x_1 ∈ Finset.univ.erase i, polygonal_number (m + ↑x_1 + 1) (x x_1) := by
        apply Finset.sum_congr rfl
        intro x_1 hx
        have hne : x_1 ≠ i := (Finset.mem_erase.mp hx).left
        simp [hne]
      rw [h_sum]
      simp [polygonal_number, hi]
      omega
  · -- Case 2: n >= m
    by_cases hnm : n = m
    · subst hnm
      use (fun _ => 1)
      simp [polygonal_number]
    · by_cases hn2m : n ≤ 2 * m
      · have hi : n - m - 1 < m := by omega
        let i : Fin m := ⟨n - m - 1, hi⟩
        use (fun j => if j = i then 2 else 0)
        rw [← Finset.insert_erase (Finset.mem_univ i)]
        rw [Finset.sum_insert (Finset.notMem_erase i Finset.univ)]
        have h_sum : ∑ x_1 ∈ Finset.univ.erase i, polygonal_number (m + ↑x_1 + 1) (if x_1 = i then 2 else 0) = 0 := by
          have h_zero : ∀ x_1 ∈ Finset.univ.erase i, polygonal_number (m + ↑x_1 + 1) (if x_1 = i then 2 else 0) = 0 := by
            intro x_1 hx
            have hne : x_1 ≠ i := (Finset.mem_erase.mp hx).left
            simp [hne, polygonal_number]
          rw [Finset.sum_congr rfl h_zero]
          simp
        rw [h_sum]
        simp [polygonal_number, i]
        omega
      · have hn1 : n - 1 < n := by omega
        obtain ⟨y, hy⟩ := ih (n - 1) hn1
        by_cases h0 : ∃ i : Fin m, y i = 0
        · obtain ⟨i, hi0⟩ := h0
          use (fun j => if j = i then 1 else y j)
          have hn_eq : n = (n - 1) + 1 := by omega
          rw [hn_eq]
          rw [hy]
          rw [← Finset.insert_erase (Finset.mem_univ i)]
          rw [Finset.sum_insert (Finset.notMem_erase i Finset.univ)]
          rw [Finset.sum_insert (Finset.notMem_erase i Finset.univ)]
          have h_sum : ∑ x_1 ∈ Finset.univ.erase i, polygonal_number (m + ↑x_1 + 1) (if x_1 = i then 1 else y x_1) =
                       ∑ x_1 ∈ Finset.univ.erase i, polygonal_number (m + ↑x_1 + 1) (y x_1) := by
            apply Finset.sum_congr rfl
            intro x_1 hx
            have hne : x_1 ≠ i := (Finset.mem_erase.mp hx).left
            simp [hne]
          rw [h_sum]
          simp [polygonal_number, hi0]
          omega
        · push_neg at h0
          have h_ge : ∀ i : Fin m, y i ≥ 1 := by
            intro i
            have h_neq : y i ≠ 0 := h0 i
            omega
          have h_exists_ge_2 : ∃ i : Fin m, y i ≥ 2 := by
            by_contra hc
            push_neg at hc
            have h_eq_1 : ∀ i : Fin m, y i = 1 := by
              intro i
              have h1 : y i ≥ 1 := h_ge i
              have h2 : y i < 2 := hc i
              omega
            have h_sum_1 : Finset.sum Finset.univ (fun i : Fin m => polygonal_number (m + (i : ℕ) + 1) (y i)) = m := by
              have h_congr : ∀ (i : Fin m), i ∈ Finset.univ → polygonal_number (m + (i : ℕ) + 1) (y i) = 1 := by
                intro i _
                rw [h_eq_1 i]
                rfl
              rw [Finset.sum_congr rfl h_congr]
              simp
            rw [← hy] at h_sum_1
            omega
          obtain ⟨i, hi_ge_2⟩ := h_exists_ge_2
          obtain ⟨z, hz⟩ := ih (n - (m + (i : ℕ) + 1)) (by omega)
          by_cases h_zi : z i = 0
          · use (fun j => if j = i then 2 else z j)
            have h_eq_n : n = (n - (m + (i : ℕ) + 1)) + (m + (i : ℕ) + 1) := by omega
            rw [h_eq_n]
            rw [hz]
            rw [← Finset.insert_erase (Finset.mem_univ i)]
            rw [Finset.sum_insert (Finset.notMem_erase i Finset.univ)]
            rw [Finset.sum_insert (Finset.notMem_erase i Finset.univ)]
            have h_sum : ∑ x_1 ∈ Finset.univ.erase i, polygonal_number (m + ↑x_1 + 1) (if x_1 = i then 2 else z x_1) =
                         ∑ x_1 ∈ Finset.univ.erase i, polygonal_number (m + ↑x_1 + 1) (z x_1) := by
              apply Finset.sum_congr rfl
              intro x_1 hx
              have hne : x_1 ≠ i := (Finset.mem_erase.mp hx).left
              simp [hne]
            rw [h_sum]
            simp [polygonal_number, h_zi]
            omega
          · sorry




