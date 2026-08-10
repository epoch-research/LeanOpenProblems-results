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

lemma find_node_zero (v : ℕ) : a.find_node 0 v = v := by
  rw [a.find_node]
  simp

lemma find_node_pos (r v : ℕ) (hr : r ≠ 0) :
    a.find_node r v =
      if v > 4 ∧ (v + 2) % 6 = 0 then
        if (r - 1) % 2 = 0 then a.find_node ((r - 1) / 2) (2 * v)
        else a.find_node ((r - 1) / 2) ((v - 1) / 3)
      else a.find_node (r - 1) (2 * v) := by
  rw [a.find_node]
  simp [hr]
  by_cases hb : v > 4 ∧ (v + 2) % 6 = 0
  · simp [hb]
    by_cases hp : (r - 1) % 2 = 0 <;> simp [hp]
  · simp [hb]

lemma find_node_one (v : ℕ) : a.find_node 1 v = 2 * v := by
  rw [find_node_pos]
  · by_cases hb : v > 4 ∧ (v + 2) % 6 = 0 <;> simp [hb, find_node_zero]
  · norm_num

lemma find_node_two_of_branch {v : ℕ} (hv : v > 4 ∧ (v + 2) % 6 = 0) :
    a.find_node 2 v = (v - 1) / 3 := by
  rw [find_node_pos]
  · simp [hv, find_node_zero]
  · norm_num

lemma find_node_append_exists :
    ∀ r : ℕ, ∀ v s : ℕ, ∃ R : ℕ, a.find_node R v = a.find_node s (a.find_node r v) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro v s
    by_cases hr : r = 0
    · subst r
      exact ⟨s, by simp [find_node_zero]⟩
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      let r' := r - 1
      have hr'_lt : r' < r := Nat.sub_one_lt_of_lt hrpos
      by_cases hb : v > 4 ∧ (v + 2) % 6 = 0
      · by_cases hpar : r' % 2 = 0
        · have hlt : r' / 2 < r := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hr'_lt
          obtain ⟨T, hT⟩ := ih (r' / 2) hlt (2 * v) s
          refine ⟨2 * T + 1, ?_⟩
          have hpar' : (r - 1) % 2 = 0 := by simpa [r'] using hpar
          rw [find_node_pos (2*T+1) v (by omega), find_node_pos r v hr]
          simp [hb, hpar']
          exact hT
        · have hlt : r' / 2 < r := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hr'_lt
          obtain ⟨T, hT⟩ := ih (r' / 2) hlt ((v - 1) / 3) s
          refine ⟨2 * T + 2, ?_⟩
          have hpar' : ¬ (r - 1) % 2 = 0 := by simpa [r'] using hpar
          have hdivR : (2 * T + 1) / 2 = T := by omega
          rw [find_node_pos (2*T+2) v (by omega), find_node_pos r v hr]
          simp [hb, hpar', hdivR]
          exact hT
      · obtain ⟨T, hT⟩ := ih r' hr'_lt (2 * v) s
        refine ⟨T + 1, ?_⟩
        have hsubR : (T + 1 - 1) = T := by omega
        rw [find_node_pos (T+1) v (by omega), find_node_pos r v hr]
        simp [hb, hsubR]
        exact hT

lemma appears_append_halving {x : ℕ} (hx : ∃ r, a.find_node r 1 = x) :
    ∃ r, a.find_node r 1 = 2 * x := by
  rcases hx with ⟨r, hr⟩
  obtain ⟨R, hR⟩ := find_node_append_exists r 1 1
  refine ⟨R, ?_⟩
  rw [hR, hr, find_node_one]

lemma appears_append_tripling {x : ℕ} (hx : ∃ r, a.find_node r 1 = x)
    (hb : x > 4 ∧ (x + 2) % 6 = 0) :
    ∃ r, a.find_node r 1 = (x - 1) / 3 := by
  rcases hx with ⟨r, hr⟩
  obtain ⟨R, hR⟩ := find_node_append_exists r 1 2
  refine ⟨R, ?_⟩
  rw [hR, hr, find_node_two_of_branch hb]

lemma collatz_fun_pos {n : ℕ} (hn : n > 0) : collatz_fun n > 0 := by
  unfold collatz_fun
  by_cases h : n % 2 = 0
  · simp [h]
    have hn2 : 2 ≤ n := by omega
    exact hn2
  · simp [h]

lemma even_collatz_eq {m : ℕ} (h : m % 2 = 0) : 2 * collatz_fun m = m := by
  unfold collatz_fun
  simp [h]
  omega

lemma odd_branch_parent {m : ℕ} (hmpos : m > 0) (hmod : ¬ m % 2 = 0) (hm1 : m ≠ 1) :
    (3 * m + 1 > 4 ∧ (3 * m + 1 + 2) % 6 = 0) := by
  constructor
  · have : m ≥ 2 := by omega
    omega
  · omega

lemma odd_collatz_parent_branch {m : ℕ} (hmpos : m > 0) (hmod : ¬ m % 2 = 0) (hm1 : m ≠ 1) :
    collatz_fun m > 4 ∧ (collatz_fun m + 2) % 6 = 0 := by
  unfold collatz_fun
  simpa [hmod] using odd_branch_parent hmpos hmod hm1

lemma odd_preimage_value {m : ℕ} (hmod : ¬ m % 2 = 0) :
    (collatz_fun m - 1) / 3 = m := by
  unfold collatz_fun
  simp [hmod]

lemma appears_of_reaches_one :
    ∀ k m : ℕ, m > 0 → (collatz_fun^[k]) m = 1 → ∃ n : ℕ, a.find_node n 1 = m := by
  intro k
  induction k with
  | zero =>
    intro m hm h
    simp at h
    exact ⟨0, by simp [find_node_zero, h]⟩
  | succ k ih =>
    intro m hm hreach
    by_cases hmone : m = 1
    · exact ⟨0, by simp [find_node_zero, hmone]⟩
    · have hreach' : (collatz_fun^[k]) (collatz_fun m) = 1 := by
        simpa [Function.iterate_succ_apply] using hreach
      have hpos' : collatz_fun m > 0 := collatz_fun_pos hm
      have happ_parent : ∃ n : ℕ, a.find_node n 1 = collatz_fun m := ih (collatz_fun m) hpos' hreach'
      by_cases heven : m % 2 = 0
      · obtain ⟨n, hn⟩ := appears_append_halving happ_parent
        refine ⟨n, ?_⟩
        rw [even_collatz_eq heven] at hn
        exact hn
      · obtain ⟨n, hn⟩ := appears_append_tripling happ_parent (odd_collatz_parent_branch hm heven hmone)
        refine ⟨n, ?_⟩
        rw [odd_preimage_value heven] at hn
        exact hn

/--
%C A319303 If the Collatz conjecture is true, then this sequence contains all positive integers.
The claim is that the set of values $\{a(n) \mid n \in \mathbb{N}\}$ equals $\mathbb{N} \setminus \{0\}$.
-/
theorem oeis_319303_conjecture_0 :
  collatz_conjecture → ∀ m : ℕ, m > 0 → ∃ n : ℕ, a n = m :=
by
  intro hcoll m hm
  rcases hcoll m hm with ⟨k, hk⟩
  rcases appears_of_reaches_one k m hm hk with ⟨n, hn⟩
  exact ⟨n, hn⟩
