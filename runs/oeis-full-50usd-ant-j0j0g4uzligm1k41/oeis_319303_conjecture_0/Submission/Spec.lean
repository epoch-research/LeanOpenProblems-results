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

/-- One-step unfolding of `find_node` at `r = 0`. -/
theorem fn_zero (v : ℕ) : a.find_node 0 v = v := by rw [a.find_node]; simp

/-- One-step unfolding of `find_node` at a non-branching node. -/
theorem fn_nonbranch (r v : ℕ) (hr : r ≠ 0) (hb : ¬ (v > 4 ∧ (v + 2) % 6 = 0)) :
    a.find_node r v = a.find_node (r - 1) (2 * v) := by
  rw [a.find_node]
  simp only [hr, if_false, hb]

/-- One-step unfolding of `find_node` at a branching node. -/
theorem fn_branch (r v : ℕ) (hr : r ≠ 0) (hb : v > 4 ∧ (v + 2) % 6 = 0) :
    a.find_node r v = a.find_node ((r-1)/2) (if (r-1) % 2 = 0 then 2 * v else (v - 1) / 3) := by
  rw [a.find_node]
  simp only [hr, if_false, hb, and_self, if_true]

theorem collatz_pos (n : ℕ) (hn : n > 0) : collatz_fun n > 0 := by
  unfold collatz_fun
  split <;> omega

theorem collatz_iter_pos (i n : ℕ) (hn : n > 0) : collatz_fun^[i] n > 0 := by
  induction i with
  | zero => simpa using hn
  | succ k ih => rw [Function.iterate_succ']; exact collatz_pos _ ih

/-- Key lemma: if the Collatz trajectory of `m` first reaches `1` at step `d`,
then `m` is the node encoded by some number `r` starting from the node `C^[d] m`. -/
theorem collatz_tree_reach : ∀ d m : ℕ, m > 0 → (∀ i < d, collatz_fun^[i] m ≠ 1) →
    ∃ r, a.find_node r (collatz_fun^[d] m) = m := by
  intro d
  induction d with
  | zero => intro m hm _; exact ⟨0, by simpa using fn_zero m⟩
  | succ d' ih =>
    intro m hm hcond
    obtain ⟨r'', hr''⟩ := ih m hm (fun i hi => hcond i (by omega))
    set w := collatz_fun^[d'] m with hw_def
    have hw1 : w ≠ 1 := hcond d' (by omega)
    have hw0 : w > 0 := collatz_iter_pos d' m hm
    have hviter : collatz_fun^[d' + 1] m = collatz_fun w := by
      rw [Function.iterate_succ']; rfl
    rw [hviter]
    set v := collatz_fun w with hv_def
    rcases Nat.even_or_odd w with hpar | hpar
    · -- w even: v = w / 2 is the halving-parent, w = 2 * v is the halving child
      have hmod : w % 2 = 0 := Nat.even_iff.mp hpar
      have hv_eq : v = w / 2 := by rw [hv_def]; unfold collatz_fun; simp [hmod]
      have h2v : 2 * v = w := by omega
      by_cases hb : v > 4 ∧ (v + 2) % 6 = 0
      · refine ⟨2 * r'' + 1, ?_⟩
        rw [fn_branch _ _ (by omega) hb]
        have e1 : (2 * r'' + 1 - 1) % 2 = 0 := by omega
        have e2 : (2 * r'' + 1 - 1) / 2 = r'' := by omega
        rw [e2]
        simp only [e1, if_true]
        rw [h2v]; exact hr''
      · refine ⟨r'' + 1, ?_⟩
        rw [fn_nonbranch _ _ (by omega) hb]
        have e2 : (r'' + 1 - 1) = r'' := by omega
        rw [e2, h2v]; exact hr''
    · -- w odd: v = 3w+1 is branching, w = (v-1)/3 is the tripling child
      have hmod : w % 2 = 1 := Nat.odd_iff.mp hpar
      have hw3 : w ≥ 3 := by omega
      have hv_eq : v = 3 * w + 1 := by rw [hv_def]; unfold collatz_fun; simp [hmod]
      have hb : v > 4 ∧ (v + 2) % 6 = 0 := by
        refine ⟨by omega, ?_⟩
        have : (v + 2) = 3 * (w + 1) := by omega
        rw [this]; omega
      have hodd3 : (v - 1) / 3 = w := by omega
      refine ⟨2 * r'' + 2, ?_⟩
      rw [fn_branch _ _ (by omega) hb]
      have e1 : ¬ ((2 * r'' + 2 - 1) % 2 = 0) := by omega
      have e2 : (2 * r'' + 2 - 1) / 2 = r'' := by omega
      rw [e2, if_neg e1, hodd3]; exact hr''

/--
%C A319303 If the Collatz conjecture is true, then this sequence contains all positive integers.
The claim is that the set of values $\{a(n) \mid n \in \mathbb{N}\}$ equals $\mathbb{N} \setminus \{0\}$.
-/
theorem oeis_319303_conjecture_0 :
  collatz_conjecture → ∀ m : ℕ, m > 0 → ∃ n : ℕ, a n = m := by
  intro hc m hm
  classical
  obtain ⟨k, hk⟩ := hc m hm
  have hex : ∃ k, collatz_fun^[k] m = 1 := ⟨k, hk⟩
  have hd : collatz_fun^[Nat.find hex] m = 1 := Nat.find_spec hex
  have hlt : ∀ i < Nat.find hex, collatz_fun^[i] m ≠ 1 := fun i hi => Nat.find_min hex hi
  obtain ⟨r, hr⟩ := collatz_tree_reach (Nat.find hex) m hm hlt
  rw [hd] at hr
  exact ⟨r, hr⟩
