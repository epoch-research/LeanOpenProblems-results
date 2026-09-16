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


def inv_step (x r : ℕ) : ℕ :=
  let p := collatz_fun x
  if p > 4 ∧ (p + 2) % 6 = 0 then
    if x % 2 = 0 then 2 * r + 1 else 2 * r + 2
  else r + 1

lemma collatz_odd_branching (x : ℕ) (hx : x > 1) (ho : x % 2 = 1) :
    collatz_fun x > 4 ∧ (collatz_fun x + 2) % 6 = 0 := by
  unfold collatz_fun
  rw [if_neg]
  · have h1 : x ≥ 3 := by omega
    constructor
    · omega
    · have : (3 * x + 1 + 2) = 3 * (x + 1) := by omega
      rw [this]
      have h2 : ∃ k, x + 1 = 2 * k := by
        use (x + 1) / 2
        omega
      rcases h2 with ⟨k, hk⟩
      rw [hk]
      have : 3 * (2 * k) = 6 * k := by omega
      rw [this]
      exact Nat.mul_mod_right 6 k
  · omega

lemma collatz_even_val (x : ℕ) (he : x % 2 = 0) : collatz_fun x = x / 2 := by
  unfold collatz_fun
  rw [if_pos he]

lemma collatz_odd_val (x : ℕ) (ho : x % 2 = 1) : collatz_fun x = 3 * x + 1 := by
  unfold collatz_fun
  rw [if_neg (by omega)]

lemma a_inv_step (x r : ℕ) (hx : x > 1) :
    a.find_node (inv_step x r) (collatz_fun x) = a.find_node r x := by
  unfold inv_step
  rw [a.find_node]
  by_cases h_branch : collatz_fun x > 4 ∧ (collatz_fun x + 2) % 6 = 0
  · simp only [h_branch, ite_true, true_and]
    by_cases h_even : x % 2 = 0
    · simp only [h_even, ite_true]
      have h_not_zero : (2 * r + 1 = 0) = False := by simp
      simp only [h_not_zero, ite_false]
      have h_rp : 2 * r + 1 - 1 = 2 * r := by omega
      simp only [h_rp]
      have h_rp2 : (2 * r) % 2 = 0 := by omega
      simp only [h_rp2, ite_true]
      have h_rn : 2 * r / 2 = r := by omega
      simp only [h_rn]
      have h_vn : 2 * collatz_fun x = x := by
        rw [collatz_even_val x h_even]
        omega
      simp only [h_vn]
    · simp only [h_even, ite_false]
      have h_not_zero : (2 * r + 2 = 0) = False := by simp
      simp only [h_not_zero, ite_false]
      have h_rp : 2 * r + 2 - 1 = 2 * r + 1 := by omega
      simp only [h_rp]
      have h_rp2 : ((2 * r + 1) % 2 = 0) = False := by simp [Nat.add_mod]
      simp only [h_rp2, ite_false]
      have h_rn : (2 * r + 1) / 2 = r := by omega
      simp only [h_rn]
      have h_vn : (collatz_fun x - 1) / 3 = x := by
        have ho : x % 2 = 1 := by omega
        rw [collatz_odd_val x ho]
        omega
      simp only [h_vn]
  · simp only [h_branch, ite_false]
    have h_not_zero : (r + 1 = 0) = False := by simp
    simp only [h_not_zero, ite_false]
    have h_rp : r + 1 - 1 = r := by omega
    simp only [h_rp]
    have h_vn : 2 * collatz_fun x = x := by
      have h_even : x % 2 = 0 := by
        by_contra h_odd
        have ho : x % 2 = 1 := by omega
        have h_branch2 := collatz_odd_branching x hx ho
        exact h_branch h_branch2
      rw [collatz_even_val x h_even]
      omega
    simp only [h_vn]

lemma path_exists_gen (m : ℕ) (k : ℕ) (h_all : ∀ j < k, (collatz_fun^[j]) m > 1) :
    ∃ n, a.find_node n ((collatz_fun^[k]) m) = m := by
  induction' k with k ih
  · use 0
    rw [a.find_node]
    simp
  · have hk_lt : ∀ (j : ℕ), j < k → (collatz_fun^[j]) m > 1 := by
      intro j hj
      apply h_all j
      omega
    rcases ih hk_lt with ⟨r, hr⟩
    use inv_step ((collatz_fun^[k]) m) r
    have hx : (collatz_fun^[k]) m > 1 := by
      apply h_all k
      omega
    have h_step := a_inv_step ((collatz_fun^[k]) m) r hx
    have h_iter : (collatz_fun^[k + 1]) m = collatz_fun ((collatz_fun^[k]) m) := by
      exact Function.iterate_succ_apply' collatz_fun k m
    rw [h_iter]
    rw [h_step]
    exact hr

lemma collatz_pos (x : ℕ) (hx : x > 0) : collatz_fun x > 0 := by
  unfold collatz_fun
  by_cases h : x % 2 = 0
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

lemma collatz_iter_pos (m k : ℕ) (hm : m > 0) : (collatz_fun^[k]) m > 0 := by
  induction' k with k ih
  · exact hm
  · rw [Function.iterate_succ_apply']
    exact collatz_pos _ ih

/--
%C A319303 If the Collatz conjecture is true, then this sequence contains all positive integers.
The claim is that the set of values $\{a(n) \mid n \in \mathbb{N}\}$ equals $\mathbb{N} \setminus \{0\}$.
-/
theorem oeis_319303_conjecture_0 :
  collatz_conjecture → ∀ m : ℕ, m > 0 → ∃ n : ℕ, a n = m :=
by
  intro hc m hm
  by_cases h1 : m = 1
  · use 0
    unfold a
    rw [h1, a.find_node]
    simp
  · have hc_m := hc m hm
    let k := Nat.find hc_m
    have hk_eq : (collatz_fun^[k]) m = 1 := Nat.find_spec hc_m
    have hk_min : ∀ j < k, (collatz_fun^[j]) m ≠ 1 := by
      intro j hj
      exact Nat.find_min hc_m hj
    have h_all : ∀ j < k, (collatz_fun^[j]) m > 1 := by
      intro j hj
      have hpos := collatz_iter_pos m j hm
      have hneq := hk_min j hj
      omega
    have h_path := path_exists_gen m k h_all
    rw [hk_eq] at h_path
    unfold a
    exact h_path

theorem oeis_319303_conjecture_0.disproof : ¬ (type_of% @oeis_319303_conjecture_0) := sorry
