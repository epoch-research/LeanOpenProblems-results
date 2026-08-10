import FormalConjectures.Util.ProblemImports

/--
A319303: $a(n)$ is the value of the node of the Collatz tree encoded by the number $n$.
For any $n \ge 0$: to find the node corresponding to $n$:
- move to the root of the Collatz tree (that is, to the node with value 1),
- set $r = n$
- while $r > 0$
-       decrement $r$
-       if the current node is a branching node different from 4
-          (that is, the current node has a value $v$ such that $v > 4$ and $v+2$ is a multiple of 6)
-       then
-          if $r$ is even
-          then
-             move to the child corresponding to a halving step ($2v$)
-          else
-             move to the child corresponding to a tripling step ($(v-1)/3$)
-          end
-          divide $r$ by 2 (and round down)
-       else
-          move to the only child (this child corresponds to a halving step) ($2v$)
-       end
-   end
- the value of the ending node corresponds to $a(n)$.
-/
def a (n : ℕ) : ℕ :=
  let rec find_node (r v : ℕ) : ℕ :=
    if r = 0 then v
    else
      let r_prime := r - 1
      -- Branching node condition: v > 4 and v+2 is a multiple of 6.
      let is_branching : Prop := v > 4 ∧ (v + 2) % 6 = 0

      if is_branching then
        -- Branching node logic
        let v_next := if r_prime % 2 = 0 then 2 * v else (v - 1) / 3
        let r_next := r_prime / 2
        find_node r_next v_next
      else
        -- Non-branching node logic
        let v_next := 2 * v
        let r_next := r_prime
        find_node r_next v_next
  termination_by r
  find_node n 1

/-- The Collatz function, $C(n) = n/2$ if $n$ is even, and $C(n) = 3n+1$ if $n$ is odd. -/
def collatz_fun (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2
  else 3 * n + 1

/--
The Collatz conjecture states that for every positive integer $n$,
repeated application of the Collatz function eventually reaches 1.
-/
def collatz_conjecture : Prop :=
  ∀ n : ℕ, n > 0 → ∃ k : ℕ, (collatz_fun^[k]) n = 1

lemma find_node_step (m : ℕ) (r : ℕ) (h_m : m > 1) :
  let p := collatz_fun m
  let is_branching : Prop := p > 4 ∧ (p + 2) % 6 = 0
  let r_p := if is_branching then
               if m % 2 = 0 then 2 * r + 1 else 2 * r + 2
             else
               r + 1
  a.find_node r_p p = a.find_node r m := by
  intro p is_branching r_p
  have h_rp : r_p > 0 := by
    dsimp [r_p]
    split_ifs
    · omega
    · omega
    · omega
  rw [a.find_node.eq_def r_p p]
  have h_rp_ne : r_p ≠ 0 := by
    omega
  simp [h_rp_ne]
  by_cases hb : 4 < p ∧ (p + 2) % 6 = 0
  · simp [hb]
    by_cases hm : m % 2 = 0
    · have h_rp_val : r_p = 2 * r + 1 := by
        dsimp [r_p, is_branching]
        rw [if_pos hb, if_pos hm]
      simp [h_rp_val]
      have hp : p = m / 2 := by
        dsimp [p, collatz_fun]
        rw [if_pos hm]
      rw [hp]
      have h_m_even : 2 * (m / 2) = m := by
        omega
      rw [h_m_even]
    · have h_rp_val : r_p = 2 * r + 2 := by
        dsimp [r_p, is_branching]
        rw [if_pos hb, if_neg hm]
      simp [h_rp_val]
      have hp : p = 3 * m + 1 := by
        dsimp [p, collatz_fun]
        rw [if_neg hm]
      have h_m_odd : (p - 1) / 3 = m := by
        omega
      rw [h_m_odd]
      have h_div : (2 * r + 1) / 2 = r := by
        omega
      rw [h_div]
  · by_cases hm : m % 2 = 0
    · have h_rp_val : r_p = r + 1 := by
        dsimp [r_p, is_branching]
        rw [if_neg hb]
      simp [hb, h_rp_val]
      have hp : p = m / 2 := by
        dsimp [p, collatz_fun]
        rw [if_pos hm]
      rw [hp]
      have h_m_even : 2 * (m / 2) = m := by
        omega
      rw [h_m_even]
    · exfalso
      have hp : p = 3 * m + 1 := by
        dsimp [p, collatz_fun]
        rw [if_neg hm]
      have h_p_prop : 4 < p ∧ (p + 2) % 6 = 0 := by
        constructor
        · omega
        · omega
      exact hb h_p_prop

lemma find_node_exists_of_collatz (k : ℕ) :
  ∀ (m : ℕ) (r : ℕ), m > 0 → (collatz_fun^[k]) m = 1 → ∃ N : ℕ, a.find_node N 1 = a.find_node r m := by
  induction' k with k ih
  · intro m r h_m h_k
    have hm1 : m = 1 := h_k
    rw [hm1]
    use r
  · intro m r h_m h_k
    by_cases hm1 : m = 1
    · rw [hm1]
      use r
    · have hm_gt1 : m > 1 := by omega
      let p := collatz_fun m
      let is_branching : Prop := p > 4 ∧ (p + 2) % 6 = 0
      let r_p := if is_branching then
                   if m % 2 = 0 then 2 * r + 1 else 2 * r + 2
                 else
                   r + 1
      have hp_gt0 : p > 0 := by
        dsimp [p, collatz_fun]
        split_ifs
        · omega
        · omega
      have hk_p : (collatz_fun^[k]) p = 1 := h_k
      obtain ⟨N, hN⟩ := ih p r_p hp_gt0 hk_p
      use N
      rw [hN]
      exact find_node_step m r hm_gt1

theorem oeis_319303_conjecture_0 :
  collatz_conjecture → ∀ m : ℕ, m > 0 → ∃ n : ℕ, a n = m := by
  intro hc m h_m
  obtain ⟨k, hk⟩ := hc m h_m
  obtain ⟨N, hN⟩ := find_node_exists_of_collatz k m 0 h_m hk
  use N
  dsimp [a]
  have h0 : a.find_node 0 m = m := by
    rw [a.find_node.eq_def 0 m]
    rfl
  rw [hN, h0]




