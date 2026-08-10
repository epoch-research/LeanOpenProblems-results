import FormalConjectures.Util.ProblemImports

open List Nat Function Set

/--
A300997: $a(n)$ is the number of steps needed to reach a stable configuration in the 1D cellular automaton initialized with one cell with mass $n$ and based on the rule "each cell gives half of its mass, rounded down, to its right neighbor".
The stable configuration is $n$ cells with mass 1.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2

  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

  let ca_step (config : List ℕ) : List ℕ :=
    let base_masses := config.map half_ceil ++ [0]
    let received_masses := 0 :: config.map half_floor

    let next_config_long := List.zipWith Nat.add base_masses received_masses

    trim_trailing_zeros next_config_long

  if n = 0 then
    0
  else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1

    -- State after t steps, computed by folding ca_step t times using foldl over a range.
    let S (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config

    -- The set of time steps k at which the configuration is stable.
    let stable_steps : Set ℕ := {k | S k = target_config}

    -- a(n) is the smallest k in this set, defined by the set infimum (sInf).
    sInf stable_steps

namespace FlowProof

/-- The integer-valued flow.  At the left boundary the source has value `N`;
away from the source the next row is obtained by averaging the two entries above,
with integer division. -/
def flow (N : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => N
  | 0, _ + 1 => 0
  | _ + 1, 0 => N
  | t + 1, j + 1 => (flow N t j + flow N t (j + 1)) / 2

/-- The deficit from the formal staircase `N-j`. -/
def H (N t j : ℕ) : ℕ := N - j - flow N t j

/-- First hitting time of value `1` at the penultimate site. -/
noncomputable def b (N : ℕ) : ℕ :=
  sInf {t : ℕ | flow N t (N - 1) = 1}

@[simp] lemma flow_zero_zero (N : ℕ) : flow N 0 0 = N := rfl
@[simp] lemma flow_zero_succ (N j : ℕ) : flow N 0 (j + 1) = 0 := rfl
@[simp] lemma flow_succ_zero (N t : ℕ) : flow N (t + 1) 0 = N := rfl
@[simp] lemma flow_succ_succ (N t j : ℕ) :
    flow N (t + 1) (j + 1) = (flow N t j + flow N t (j + 1)) / 2 := rfl

@[simp] lemma H_def' (N t j : ℕ) : H N t j = N - j - flow N t j := rfl

@[simp] lemma H_at_zero (N t : ℕ) : H N t 0 = 0 := by
  cases t <;> simp [H]

@[simp] lemma H_zero_zero (N : ℕ) : H N 0 0 = 0 := by simp [H]

@[simp] lemma H_zero_succ (N j : ℕ) : H N 0 (j + 1) = N - (j + 1) := by
  simp [H]

/-- No flow can reach a site strictly to the right of the time front. -/
lemma flow_eq_zero_of_t_lt_j (N : ℕ) : ∀ t j : ℕ, t < j → flow N t j = 0 := by
  intro t
  induction t with
  | zero =>
      intro j hj
      cases j with
      | zero => omega
      | succ j => simp
  | succ t ih =>
      intro j hj
      cases j with
      | zero => omega
      | succ j =>
          have htj : t < j := by omega
          have htj1 : t < j + 1 := by omega
          simp [flow, ih j htj, ih (j + 1) htj1]

@[simp] lemma flow_zero_of_lt (N t j : ℕ) (h : t < j) : flow N t j = 0 :=
  flow_eq_zero_of_t_lt_j N t j h

/-- The fundamental upper bound: the flow never exceeds the staircase `N-j`.
This statement is global; when `j ≥ N` the right hand side is zero. -/
lemma flow_le_staircase (N : ℕ) : ∀ t j : ℕ, flow N t j ≤ N - j := by
  intro t
  induction t with
  | zero =>
      intro j
      cases j with
      | zero => simp
      | succ j => simp
  | succ t ih =>
      intro j
      cases j with
      | zero => simp
      | succ j =>
          have h₁ := ih j
          have h₂ := ih (j + 1)
          apply (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)).2
          omega

lemma flow_le_N (N t j : ℕ) : flow N t j ≤ N := by
  exact le_trans (flow_le_staircase N t j) (Nat.sub_le N j)

/-- Deficit recurrence: inside the staircase, the next deficit is the integer
average of the two deficits immediately above it. -/
lemma H_succ_succ (N t j : ℕ) :
    H N (t + 1) (j + 1) = (H N t j + H N t (j + 1)) / 2 := by
  have h₁ : flow N t j ≤ N - j := flow_le_staircase N t j
  have h₂ : flow N t (j + 1) ≤ N - (j + 1) := flow_le_staircase N t (j + 1)
  simp only [H, flow_succ_succ]
  omega

/-- At each time, the flow profile is nonincreasing as the site index moves to
the right. -/
lemma flow_antitone_site (N : ℕ) : ∀ t j : ℕ, flow N t (j + 1) ≤ flow N t j := by
  intro t
  induction t with
  | zero =>
      intro j
      cases j <;> simp [flow]
  | succ t ih =>
      intro j
      cases j with
      | zero =>
          rw [flow_succ_succ, flow_succ_zero]
          have h0 : flow N t 0 = N := by cases t <;> simp [flow]
          rw [h0]
          apply (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)).2
          have h1 : flow N t (0 + 1) ≤ N := by simpa using flow_le_N N t 1
          omega
      | succ j =>
          apply Nat.div_le_div_right
          exact Nat.add_le_add (ih j) (ih (j + 1))

/-- The deficit is 1-Lipschitz in the spatial direction. -/
lemma H_lipschitz_site (N t j : ℕ) : H N t j ≤ H N t (j + 1) + 1 := by
  have hm : flow N t (j + 1) ≤ flow N t j := flow_antitone_site N t j
  simp only [H]
  omega

/-- Flow is nondecreasing in time at each fixed site. -/
lemma flow_mono_time (N : ℕ) : ∀ t j : ℕ, flow N t j ≤ flow N (t + 1) j := by
  intro t j
  cases j with
  | zero =>
      cases t <;> simp [flow]
  | succ j =>
      rw [flow_succ_succ]
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      have h := flow_antitone_site N t j
      omega

/-- Consequently, deficits are nonincreasing in time. -/
lemma H_antitone_time (N t j : ℕ) : H N (t + 1) j ≤ H N t j := by
  have h := flow_mono_time N t j
  simp only [H]
  omega


/-- First clearing time of the deficit at site `j`. -/
noncomputable def tau (N j : ℕ) : ℕ :=
  sInf {t : ℕ | H N t j = 0}

/-- Once a deficit has cleared at a site, it stays cleared at the next time. -/
lemma H_zero_stays_zero {N t j : ℕ} (h : H N t j = 0) : H N (t + 1) j = 0 := by
  have hle := H_antitone_time N t j
  omega

/-- Every deficit site eventually clears. -/
lemma H_eventually_zero (N j : ℕ) : ∃ t, H N t j = 0 := by
  induction j with
  | zero =>
      exact ⟨0, by simp⟩
  | succ j ih =>
      rcases ih with ⟨t₀, ht₀⟩
      let v₀ := H N t₀ (j + 1)
      have hclear : ∀ v : ℕ, ∀ t : ℕ,
          H N t j = 0 → H N t (j + 1) = v → ∃ u, H N u (j + 1) = 0 := by
        intro v
        induction v using Nat.strong_induction_on with
        | h v IH =>
            intro t hleft hright
            by_cases hv : v = 0
            · exact ⟨t, by simpa [hv] using hright⟩
            · have hvpos : 0 < v := Nat.pos_of_ne_zero hv
              have hleft_next : H N (t + 1) j = 0 := H_zero_stays_zero hleft
              have hright_next : H N (t + 1) (j + 1) = v / 2 := by
                rw [H_succ_succ, hleft, hright]
                simp
              have hvhalf_lt : v / 2 < v := Nat.div_lt_self hvpos (by decide : 1 < 2)
              exact IH (v / 2) hvhalf_lt (t + 1) hleft_next hright_next
      exact hclear v₀ t₀ ht₀ rfl

/-- The clearing time itself is a time at which the deficit has cleared. -/
lemma tau_spec (N j : ℕ) : H N (tau N j) j = 0 := by
  exact Nat.sInf_mem (s := {t : ℕ | H N t j = 0}) (H_eventually_zero N j)

/-- Any clearing time is an upper bound for the first clearing time. -/
lemma tau_min {N j t : ℕ} (h : H N t j = 0) : tau N j ≤ t := by
  exact Nat.sInf_le (s := {u : ℕ | H N u j = 0}) h

/-- Before the first clearing time, the deficit is nonzero. -/
lemma H_ne_zero_of_lt_tau {N j t : ℕ} (h : t < tau N j) : H N t j ≠ 0 := by
  exact Nat.notMem_of_lt_sInf (s := {u : ℕ | H N u j = 0}) h

/-- Clearing times advance by at least one step from a site to its right, inside the staircase. -/
lemma tau_step_le {N j : ℕ} (hjN : j + 1 < N) : tau N j + 1 ≤ tau N (j + 1) := by
  have hTpos : 0 < tau N (j + 1) := by
    by_contra hnot
    have hT0 : tau N (j + 1) = 0 := by omega
    have hhit := tau_spec N (j + 1)
    rw [hT0] at hhit
    have hinit_pos : 0 < H N 0 (j + 1) := by
      simp [H]
      omega
    omega
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hTpos) with ⟨s, hs⟩
  have hs_lt : s < tau N (j + 1) := by omega
  have hright_ne : H N s (j + 1) ≠ 0 := H_ne_zero_of_lt_tau hs_lt
  have hchild : H N (s + 1) (j + 1) = 0 := by
    have hspec := tau_spec N (j + 1)
    rwa [hs] at hspec
  have hdiv : (H N s j + H N s (j + 1)) / 2 = 0 := by
    have hrec := H_succ_succ N s j
    rwa [hrec] at hchild
  have hsum_lt : H N s j + H N s (j + 1) < 2 :=
    Nat.lt_of_div_eq_zero (by decide : 0 < 2) hdiv
  have hleft_zero : H N s j = 0 := by
    have hright_pos : 0 < H N s (j + 1) := Nat.pos_of_ne_zero hright_ne
    omega
  have htauj_le_s : tau N j ≤ s := tau_min hleft_zero
  omega

lemma H_nonnegative (N t j : ℕ) : flow N t j ≤ N - j :=
  flow_le_staircase N t j

/-- If a time hits, it is an upper bound for the hitting time. -/
lemma b_le_of_hit {N t : ℕ} (ht : flow N t (N - 1) = 1) : b N ≤ t := by
  exact Nat.sInf_le ht

/-- If the hitting set is nonempty, then `b` itself is a hitting time. -/
lemma hit_at_b {N : ℕ} (hne : ({t : ℕ | flow N t (N - 1) = 1} : Set ℕ).Nonempty) :
    flow N (b N) (N - 1) = 1 := by
  exact Nat.sInf_mem hne

/-- No time strictly before `b N` can be a hitting time. -/
lemma not_hit_of_lt_b {N t : ℕ} (ht : t < b N) : flow N t (N - 1) ≠ 1 := by
  exact Nat.notMem_of_lt_sInf (s := {u : ℕ | flow N u (N - 1) = 1}) ht

/-- Rephrase a hit at the penultimate site as zero deficit. -/
lemma H_target_eq_zero_of_hit {N t : ℕ} (hN : 1 ≤ N)
    (ht : flow N t (N - 1) = 1) : H N t (N - 1) = 0 := by
  simp only [H]
  omega

/-- If the hitting set is nonempty, then the deficit at `b N` and the target site is zero. -/
lemma H_at_b_target_eq_zero {N : ℕ} (hN : 1 ≤ N)
    (hne : ({t : ℕ | flow N t (N - 1) = 1} : Set ℕ).Nonempty) :
    H N (b N) (N - 1) = 0 := by
  exact H_target_eq_zero_of_hit hN (hit_at_b (N := N) hne)

/-- For `N ≥ 2`, the target has not been hit at time zero. -/
lemma flow_target_zero_eq_zero_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    flow N 0 (N - 1) = 0 := by
  cases N with
  | zero => omega
  | succ N =>
      cases N with
      | zero => omega
      | succ N => simp

/-- Consequently, a nonempty hitting set has positive first hit when `N ≥ 2`. -/
lemma b_pos_of_two_le {N : ℕ} (hN : 2 ≤ N)
    (hne : ({t : ℕ | flow N t (N - 1) = 1} : Set ℕ).Nonempty) : 0 < b N := by
  by_contra hb
  have hb0 : b N = 0 := by omega
  have hhit := hit_at_b (N := N) hne
  rw [hb0] at hhit
  have hzero := flow_target_zero_eq_zero_of_two_le hN
  omega


/-- For `N=1`, the target site is the source and is already equal to `1`. -/
@[simp] lemma b_one : b 1 = 0 := by
  apply le_antisymm
  · exact b_le_of_hit (N := 1) (t := 0) (by simp [flow])
  · exact Nat.zero_le _

@[simp] lemma flow_two_at_one_zero : flow 2 0 1 = 0 := rfl
@[simp] lemma flow_two_at_one_one : flow 2 1 1 = 1 := by simp [flow]

/-- The first nontrivial hitting time. -/
@[simp] lemma b_two : b 2 = 1 := by
  apply le_antisymm
  · exact b_le_of_hit (N := 2) (t := 1) (by simp [flow])
  · by_contra h
    have hb0 : b 2 = 0 := by omega
    have hne : ({t : ℕ | flow 2 t (2 - 1) = 1} : Set ℕ).Nonempty :=
      ⟨1, by simp [flow]⟩
    have hhit := hit_at_b (N := 2) hne
    rw [hb0] at hhit
    norm_num [flow] at hhit

/-- The requested finite-difference statement, verified for the base case. -/
theorem b_step_base : b (1 + 1) = b 1 + 1 ∨ b (1 + 1) = b 1 + 2 := by
  left
  simp

/-- A convenient formulation of the one-step deficit identity before simplifying
natural-number subtraction and division.  This is the algebraic recurrence from
which the desired average-of-deficits formula should be derived under the
staircase bounds. -/
lemma H_succ_succ_unfold (N t j : ℕ) :
    H N (t + 1) (j + 1) =
      N - (j + 1) - (flow N t j + flow N t (j + 1)) / 2 := by
  rfl

/-- A difference field used in the intended comparison of sizes `N+1` and `N`. -/
def D (N t j : ℕ) : ℕ := flow (N + 1) t j - flow N t j

@[simp] lemma D_at_zero (N t : ℕ) : D N t 0 = 1 := by
  cases t <;> simp [D, flow]

@[simp] lemma D_zero_succ (N j : ℕ) : D N 0 (j + 1) = 0 := by
  simp [D, flow]

/-- Pointwise monotonicity in the source size by one unit. -/
lemma flow_mono_succ_source (N : ℕ) : ∀ t j : ℕ, flow N t j ≤ flow (N + 1) t j := by
  intro t
  induction t with
  | zero =>
      intro j
      cases j <;> simp [flow]
  | succ t ih =>
      intro j
      cases j with
      | zero => simp [flow]
      | succ j =>
          exact Nat.div_le_div_right (Nat.add_le_add (ih j) (ih (j + 1)))

lemma D_eq_zero_or_pos (N t j : ℕ) : D N t j = 0 ∨ 0 < D N t j := by
  exact Nat.eq_zero_or_pos _


/-- The larger-source flow splits as the smaller-source flow plus `D`. -/
lemma flow_succ_source_eq_flow_add_D (N t j : ℕ) :
    flow (N + 1) t j = flow N t j + D N t j := by
  have h := flow_mono_succ_source N t j
  simp only [D]
  omega

/-- The one-source increment changes each entry by at most one. -/
lemma D_le_one (N : ℕ) : ∀ t j : ℕ, D N t j ≤ 1 := by
  intro t
  induction t with
  | zero =>
      intro j
      cases j <;> simp [D, flow]
  | succ t ih =>
      intro j
      cases j with
      | zero => simp
      | succ j =>
          have hdj : D N t j ≤ 1 := ih j
          have hdj1 : D N t (j + 1) ≤ 1 := ih (j + 1)
          have hsplitj := flow_succ_source_eq_flow_add_D N t j
          have hsplitj1 := flow_succ_source_eq_flow_add_D N t (j + 1)
          simp only [D]
          rw [flow_succ_succ, flow_succ_succ, hsplitj, hsplitj1]
          apply Nat.sub_le_iff_le_add.mpr
          apply (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)).2
          have hmod : (flow N t j + flow N t (j + 1)) % 2 ≤ 1 :=
            Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 2))
          have hdiv := Nat.div_add_mod (flow N t j + flow N t (j + 1)) 2
          omega

/-- The source-size finite difference is Boolean. -/
lemma D_eq_zero_or_one (N t j : ℕ) : D N t j = 0 ∨ D N t j = 1 := by
  have h := D_le_one N t j
  omega

lemma D_pos_iff_eq_one {N t j : ℕ} : 0 < D N t j ↔ D N t j = 1 := by
  constructor
  · intro h
    have hle := D_le_one N t j
    omega
  · intro h
    omega

/-- A useful recurrence inequality for the finite-difference field. -/
lemma D_succ_succ_le_sum (N t j : ℕ) :
    D N (t + 1) (j + 1) ≤ D N t j + D N t (j + 1) := by
  have hsplitj := flow_succ_source_eq_flow_add_D N t j
  have hsplitj1 := flow_succ_source_eq_flow_add_D N t (j + 1)
  rw [D, flow_succ_succ, flow_succ_succ, hsplitj, hsplitj1]
  apply Nat.sub_le_iff_le_add.mpr
  apply (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)).2
  have hmod : (flow N t j + flow N t (j + 1)) % 2 ≤ 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 2))
  have hdiv := Nat.div_add_mod (flow N t j + flow N t (j + 1)) 2
  omega

/-- If both parents have zero finite difference, then so does their child. -/
lemma D_succ_succ_eq_zero_of_zero {N t j : ℕ}
    (h₀ : D N t j = 0) (h₁ : D N t (j + 1) = 0) :
    D N (t + 1) (j + 1) = 0 := by
  have hle := D_succ_succ_le_sum N t j
  omega

/-- If both parents have finite difference one, then so does their child. -/
lemma D_succ_succ_eq_one_of_one {N t j : ℕ}
    (h₀ : D N t j = 1) (h₁ : D N t (j + 1) = 1) :
    D N (t + 1) (j + 1) = 1 := by
  have hsplitj := flow_succ_source_eq_flow_add_D N t j
  have hsplitj1 := flow_succ_source_eq_flow_add_D N t (j + 1)
  rw [D, flow_succ_succ, flow_succ_succ, hsplitj, hsplitj1, h₀, h₁]
  have hadd : flow N t j + 1 + (flow N t (j + 1) + 1) =
      (flow N t j + flow N t (j + 1)) + 2 := by omega
  rw [hadd]
  rw [Nat.add_div_right _ (by decide : 0 < 2)]
  omega

/-- If a child has finite difference one, at least one parent has finite difference one. -/
lemma D_parent_one_of_child_one {N t j : ℕ} (h : D N (t + 1) (j + 1) = 1) :
    D N t j = 1 ∨ D N t (j + 1) = 1 := by
  have hle := D_succ_succ_le_sum N t j
  have h0 := D_eq_zero_or_one N t j
  have h1 := D_eq_zero_or_one N t (j + 1)
  omega

/-- At each time, the finite-difference profile is a prefix of ones followed by zeros. -/
lemma D_antitone_site (N : ℕ) : ∀ t j : ℕ, D N t (j + 1) ≤ D N t j := by
  intro t
  induction t with
  | zero =>
      intro j
      cases j <;> simp [D, flow]
  | succ t ih =>
      intro j
      cases j with
      | zero =>
          simpa using D_le_one N (t + 1) 1
      | succ j =>
          have hright01 := D_eq_zero_or_one N (t + 1) (j + 2)
          cases hright01 with
          | inl hright0 =>
              rw [hright0]
              exact Nat.zero_le _
          | inr hright1 =>
              have hpar := D_parent_one_of_child_one (N := N) (t := t) (j := j + 1) hright1
              have hb : D N t (j + 1) = 1 := by
                cases hpar with
                | inl hb => exact hb
                | inr hc =>
                    have hle := ih (j + 1)
                    have h01 := D_eq_zero_or_one N t (j + 1)
                    omega
              have ha : D N t j = 1 := by
                have hle := ih j
                have h01 := D_eq_zero_or_one N t j
                omega
              have hleft := D_succ_succ_eq_one_of_one (N := N) (t := t) (j := j) ha hb
              rw [hright1, hleft]

/-- Zero finite difference propagates to the right along each row. -/
lemma D_prefix_zero {N t j : ℕ} (h : D N t j = 0) : D N t (j + 1) = 0 := by
  have hle := D_antitone_site N t j
  omega


/-- If the first clearing time is no later than `t`, then the site is clear at `t`. -/
lemma H_eq_zero_of_tau_le {N j t : ℕ} (h : tau N j ≤ t) : H N t j = 0 := by
  induction h with
  | refl => exact tau_spec N j
  | @step t _ ih => exact H_zero_stays_zero ih

/-- The source deficit clears at time zero. -/
@[simp] lemma tau_zero_site (N : ℕ) : tau N 0 = 0 := by
  apply le_antisymm
  · exact tau_min (by simp)
  · exact Nat.zero_le _

/-- Clearing times advance by at least `d` steps over `d` sites. -/
lemma tau_add_le {N j d : ℕ} (h : j + d < N) : tau N j + d ≤ tau N (j + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev : j + d < N := by omega
      have ih' : tau N j + d ≤ tau N (j + d) := ih hprev
      have hstep : tau N (j + d) + 1 ≤ tau N (j + d + 1) := by
        simpa [Nat.add_assoc] using (tau_step_le (N := N) (j := j + d) (by omega))
      have hadd : tau N j + (d + 1) = tau N j + d + 1 := by omega
      have hidx : j + (d + 1) = j + d + 1 := by omega
      rw [hidx]
      omega

/-- The hitting-time definition `b` is the same as the deficit-clearing time at the target. -/
lemma b_eq_tau (N : ℕ) (hN : 1 ≤ N) : b N = tau N (N - 1) := by
  apply le_antisymm
  · have hH : H N (tau N (N - 1)) (N - 1) = 0 := tau_spec N (N - 1)
    have hf : flow N (tau N (N - 1)) (N - 1) = 1 := by
      have hle : flow N (tau N (N - 1)) (N - 1) ≤ 1 := by
        have hs := flow_le_staircase N (tau N (N - 1)) (N - 1)
        omega
      have hNm : N - (N - 1) = 1 := by omega
      rcases (show flow N (tau N (N - 1)) (N - 1) = 0 ∨
          flow N (tau N (N - 1)) (N - 1) = 1 by omega) with hz | hone
      · simp [H, hNm, hz] at hH
      · exact hone
    exact b_le_of_hit hf
  · have hne : ({t : ℕ | flow N t (N - 1) = 1} : Set ℕ).Nonempty := by
      refine ⟨tau N (N - 1), ?_⟩
      have hH : H N (tau N (N - 1)) (N - 1) = 0 := tau_spec N (N - 1)
      have hle : flow N (tau N (N - 1)) (N - 1) ≤ 1 := by
        have hs := flow_le_staircase N (tau N (N - 1)) (N - 1)
        omega
      have hNm : N - (N - 1) = 1 := by omega
      rcases (show flow N (tau N (N - 1)) (N - 1) = 0 ∨
          flow N (tau N (N - 1)) (N - 1) = 1 by omega) with hz | hone
      · simp [H, hNm, hz] at hH
      · exact hone
    have hf : flow N (b N) (N - 1) = 1 := hit_at_b hne
    have hH : H N (b N) (N - 1) = 0 := H_target_eq_zero_of_hit hN hf
    exact tau_min hH

/-- At a saturated adjacent pair with odd staircase sum, a unit source-difference moves diagonally. -/
lemma D_saturated_odd_step {N t k : ℕ} (hk : k + 1 < N)
    (hD : D N t k = 1) (hH0 : H N t k = 0) (hH1 : H N t (k + 1) = 0) :
    D N (t + 1) (k + 1) = 1 := by
  have hsplit0 := flow_succ_source_eq_flow_add_D N t k
  have hsplit1 := flow_succ_source_eq_flow_add_D N t (k + 1)
  have hle0 := flow_le_staircase N t k
  have hle1 := flow_le_staircase N t (k + 1)
  have f0 : flow N t k = N - k := by
    simp [H] at hH0
    omega
  have f1 : flow N t (k + 1) = N - (k + 1) := by
    simp [H] at hH1
    omega
  rcases D_eq_zero_or_one N t (k + 1) with hD1 | hD1
  · rw [D, flow_succ_succ, flow_succ_succ, hsplit0, hsplit1, hD, hD1]
    have hodd : (N - k + (N - (k + 1)) + 1) / 2 = (N - k + (N - (k + 1))) / 2 + 1 := by
      omega
    rw [f0, f1]
    omega
  · exact D_succ_succ_eq_one_of_one hD hD1



/- The full theorem requested in the prompt is intentionally left as a comment,
because the remaining staircase-clearing and diagonal propagation arguments are
not completed in this scratch file with a fully verified proof.

Target statement:
`∀ N : ℕ, 1 ≤ N → b (N + 1) = b N + 1 ∨ b (N + 1) = b N + 2`.
-/

/-- A unit source-difference propagates along the saturated diagonal from the
source to the penultimate site by the time the original `N`-flow clears its
penultimate site. -/
lemma D_diagonal_to_penultimate (N : ℕ) (hN : 2 ≤ N) :
    D N (tau N (N - 1)) (N - 2) = 1 := by
  let T := tau N (N - 1)
  have hdiag : ∀ k : ℕ, k ≤ N - 2 → D N (T - (N - 2) + k) k = 1 := by
    intro k
    induction k with
    | zero =>
        intro _
        simp
    | succ k ih =>
        intro hk_succ
        have hk_prev : k ≤ N - 2 := by omega
        have hDprev : D N (T - (N - 2) + k) k = 1 := ih hk_prev
        have hkN : k + 1 < N := by omega
        have hH0 : H N (T - (N - 2) + k) k = 0 := by
          apply H_eq_zero_of_tau_le
          have hidx : k + (N - 1 - k) < N := by omega
          have hle := tau_add_le (N := N) (j := k) (d := N - 1 - k) hidx
          have hidxeq : k + (N - 1 - k) = N - 1 := by omega
          rw [hidxeq] at hle
          change tau N k ≤ T - (N - 2) + k
          omega
        have hH1 : H N (T - (N - 2) + k) (k + 1) = 0 := by
          apply H_eq_zero_of_tau_le
          have hidx : (k + 1) + (N - 2 - k) < N := by omega
          have hle := tau_add_le (N := N) (j := k + 1) (d := N - 2 - k) hidx
          have hidxeq : (k + 1) + (N - 2 - k) = N - 1 := by omega
          rw [hidxeq] at hle
          change tau N (k + 1) ≤ T - (N - 2) + k
          omega
        have hstep := D_saturated_odd_step (N := N) (t := T - (N - 2) + k)
          (k := k) hkN hDprev hH0 hH1
        have ht : T - (N - 2) + (k + 1) = (T - (N - 2) + k) + 1 := by omega
        simpa [ht] using hstep
  have hfinal := hdiag (N - 2) (by omega)
  have hidx0 : 0 + (N - 1) < N := by omega
  have hTge := tau_add_le (N := N) (j := 0) (d := N - 1) hidx0
  simp at hTge
  have htime : T - (N - 2) + (N - 2) = T := by omega
  simpa [T, htime] using hfinal

/-- The next source size hits its new penultimate site no later than two steps
after the previous source size hits its penultimate site. -/
lemma b_succ_le_add_two (N : ℕ) (hN : 1 ≤ N) : b (N + 1) ≤ b N + 2 := by
  by_cases hN2 : 2 ≤ N
  · let T := tau N (N - 1)
    have hbN : b N = T := by simpa [T] using b_eq_tau N hN
    have hD : D N T (N - 2) = 1 := by simpa [T] using D_diagonal_to_penultimate N hN2
    have hHleft : H N T (N - 2) = 0 := by
      apply H_eq_zero_of_tau_le
      have hidx : (N - 2) + 1 < N := by omega
      have hle := tau_add_le (N := N) (j := N - 2) (d := 1) hidx
      have hidxeq : (N - 2) + 1 = N - 1 := by omega
      rw [hidxeq] at hle
      change tau N (N - 2) ≤ T
      omega
    have hflow_left_small : flow N T (N - 2) = 2 := by
      have hs := flow_le_staircase N T (N - 2)
      simp [H] at hHleft
      omega
    have hflow_left_big : flow (N + 1) T (N - 2) = 3 := by
      have hsplit := flow_succ_source_eq_flow_add_D N T (N - 2)
      rw [hsplit, hflow_left_small, hD]
    have hHtarget : H N T (N - 1) = 0 := by simpa [T] using tau_spec N (N - 1)
    have hflow_target_small : flow N T (N - 1) = 1 := by
      have hs := flow_le_staircase N T (N - 1)
      simp [H] at hHtarget
      omega
    have hflow_target_big_ge : 1 ≤ flow (N + 1) T (N - 1) := by
      have hmono := flow_mono_succ_source N T (N - 1)
      omega
    have hsite_left : N - 1 = (N - 2) + 1 := by omega
    have hmid_ge : 2 ≤ flow (N + 1) (T + 1) (N - 1) := by
      rw [hsite_left, flow_succ_succ]
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      have hparent : 1 ≤ flow (N + 1) T ((N - 2) + 1) := by
        simpa [← hsite_left] using hflow_target_big_ge
      omega
    have hsite_new : N = (N - 1) + 1 := by omega
    have htime_two : T + 2 = (T + 1) + 1 := by omega
    have hfinal_ge : 1 ≤ flow (N + 1) (T + 2) N := by
      have htmp : 1 ≤ flow (N + 1) ((T + 1) + 1) ((N - 1) + 1) := by
        rw [flow_succ_succ]
        apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
        omega
      simpa [← htime_two, ← hsite_new] using htmp
    have hfinal_le : flow (N + 1) (T + 2) N ≤ 1 := by
      have hs := flow_le_staircase (N + 1) (T + 2) N
      omega
    have hhit : flow (N + 1) (T + 2) ((N + 1) - 1) = 1 := by
      have hsite : (N + 1) - 1 = N := by omega
      rw [hsite]
      omega
    have hb_le : b (N + 1) ≤ T + 2 := b_le_of_hit hhit
    simpa [hbN] using hb_le
  · have hN_eq : N = 1 := by omega
    subst N
    simp


/-- Flow is monotone over an arbitrary time interval. -/
lemma flow_mono_time_le {N t u j : ℕ} (h : t ≤ u) : flow N t j ≤ flow N u j := by
  induction h with
  | refl => exact le_rfl
  | @step u _ ih => exact le_trans ih (flow_mono_time N u j)

/-- For positive source size, the hitting set defining `b` is nonempty. -/
lemma hitSet_nonempty (N : ℕ) (hN : 1 ≤ N) :
    ({t : ℕ | flow N t (N - 1) = 1} : Set ℕ).Nonempty := by
  refine ⟨tau N (N - 1), ?_⟩
  have hH : H N (tau N (N - 1)) (N - 1) = 0 := tau_spec N (N - 1)
  have hle : flow N (tau N (N - 1)) (N - 1) ≤ 1 := by
    have hs := flow_le_staircase N (tau N (N - 1)) (N - 1)
    omega
  have hNm : N - (N - 1) = 1 := by omega
  rcases (show flow N (tau N (N - 1)) (N - 1) = 0 ∨
      flow N (tau N (N - 1)) (N - 1) = 1 by omega) with hz | hone
  · simp [H, hNm, hz] at hH
  · exact hone

/-- Up to the old hitting time, the next source has no flow at its new target site. -/
lemma flow_succ_new_target_zero_until_tau (N : ℕ) (hN : 2 ≤ N) :
    ∀ s : ℕ, s ≤ tau N (N - 1) → flow (N + 1) s N = 0 := by
  intro s
  induction s with
  | zero =>
      intro _
      have hNpos : 0 < N := by omega
      cases N with
      | zero => omega
      | succ N => simp [flow]
  | succ s ih =>
      intro hsle
      have hs_lt : s < tau N (N - 1) := by omega
      have hprev_new : flow (N + 1) s N = 0 := ih (by omega)
      have hsmall_old : flow N s (N - 1) = 0 := by
        have hne : H N s (N - 1) ≠ 0 := H_ne_zero_of_lt_tau hs_lt
        have hle : flow N s (N - 1) ≤ 1 := by
          have hs := flow_le_staircase N s (N - 1)
          omega
        have hNm : N - (N - 1) = 1 := by omega
        rcases (show flow N s (N - 1) = 0 ∨ flow N s (N - 1) = 1 by omega) with hz | hone
        · exact hz
        · exfalso
          apply hne
          simp [H, hNm, hone]
      have hbig_left_le : flow (N + 1) s (N - 1) ≤ 1 := by
        have hsplit := flow_succ_source_eq_flow_add_D N s (N - 1)
        have hDle := D_le_one N s (N - 1)
        rw [hsplit, hsmall_old]
        omega
      have hsite : N = (N - 1) + 1 := by omega
      have hnext : flow (N + 1) (s + 1) ((N - 1) + 1) = 0 := by
        have hprev_new' : flow (N + 1) s ((N - 1) + 1) = 0 := by simpa [← hsite] using hprev_new
        rw [flow_succ_succ]
        apply Nat.div_eq_of_lt
        omega
      simpa [← hsite] using hnext

/-- The next hitting time is strictly after the old one. -/
lemma b_lt_succ (N : ℕ) (hN : 1 ≤ N) : b N < b (N + 1) := by
  by_cases hN2 : 2 ≤ N
  · let T := tau N (N - 1)
    have hbN : b N = T := by simpa [T] using b_eq_tau N hN
    have hzeroT : flow (N + 1) T N = 0 := flow_succ_new_target_zero_until_tau N hN2 T le_rfl
    by_contra hnot
    have hle : b (N + 1) ≤ T := by omega
    have hhit : flow (N + 1) (b (N + 1)) ((N + 1) - 1) = 1 :=
      hit_at_b (N := N + 1) (hitSet_nonempty (N + 1) (by omega))
    have hsite : (N + 1) - 1 = N := by omega
    rw [hsite] at hhit
    have hmono := flow_mono_time_le (N := N + 1) (t := b (N + 1)) (u := T) (j := N) hle
    omega
  · have hN_eq : N = 1 := by omega
    subst N
    simp

/-- Abstract finite-difference theorem for the scalar flow hitting time. -/
theorem b_finite_diff : ∀ N : ℕ, 1 ≤ N → b (N + 1) = b N + 1 ∨ b (N + 1) = b N + 2 := by
  intro N hN
  have hlt : b N < b (N + 1) := b_lt_succ N hN
  have hle : b (N + 1) ≤ b N + 2 := b_succ_le_add_two N hN
  omega



end FlowProof


/-- Verified consequence available in this scratch file: the scalar flow hitting time has finite differences 1 or 2. -/
theorem flow_hitting_time_finite_difference :
  ∀ n : ℕ, 1 ≤ n → FlowProof.b (n + 1) = FlowProof.b n + 1 ∨ FlowProof.b (n + 1) = FlowProof.b n + 2 := by
  exact FlowProof.b_finite_diff

/-!
Bridge status (not formalized here): `a` above is the original list cellular automaton.
The intended missing bridge is to prove that, for `n ≥ 1`, its stable-step set
`{k | S k = List.replicate n 1}` equals the scalar hitting set
`{k | FlowProof.flow n k (n - 1) = 1}`.  A natural invariant is that the
untrimmed mass at site `j` after `t` steps is
`FlowProof.flow n t j - FlowProof.flow n t (j+1)`, with trailing zero trimming
matching the local `trim_trailing_zeros`.  Once this is formalized, `a n =
FlowProof.b n` follows by `sInf` congruence, and the original OEIS theorem follows
from `FlowProof.b_finite_diff`.
-/

namespace Bridge
open FlowProof


/-- Rounded-up half, matching the local definition in `a`. -/
def halfCeil (m : ℕ) : ℕ := (m + 1) / 2

/-- Rounded-down half, matching the local definition in `a`. -/
def halfFloor (m : ℕ) : ℕ := m / 2

/-- One untrimmed CA step. -/
def caStepLong (config : List ℕ) : List ℕ :=
  let base_masses := config.map halfCeil ++ [0]
  let received_masses := 0 :: config.map halfFloor
  List.zipWith Nat.add base_masses received_masses


def massList (N t : ℕ) : List ℕ :=
  (List.range (N + 1)).map (fun j => FlowProof.flow N t j - FlowProof.flow N t (j + 1))

def trimZeros (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse


/-- One CA step, including trailing-zero trimming, matching the local definition in `a`. -/
def caStep (config : List ℕ) : List ℕ :=
  trimZeros (caStepLong config)

/-- State after `t` CA steps from initial mass `N`. -/
def caState (N t : ℕ) : List ℕ :=
  (List.range t).foldl (fun acc _ => caStep acc) [N]

/-- Tail sum of a list from site `j` onward. -/
def tailSum (l : List ℕ) (j : ℕ) : ℕ :=
  (l.drop j).sum



lemma halfCeil_add_halfFloor (m : ℕ) : halfCeil m + halfFloor m = m := by
  unfold halfCeil halfFloor
  omega

lemma sum_eq_zero_of_forall_eq_zero {l : List ℕ} (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx : x = 0 := h x (by simp)
      have hxs : ∀ y ∈ xs, y = 0 := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

lemma tailSum_append_zeros (l z : List ℕ) (j : ℕ) (hz : ∀ x ∈ z, x = 0) :
    tailSum (l ++ z) j = tailSum l j := by
  revert j
  induction l with
  | nil =>
      intro j
      unfold tailSum
      have hdrop : ∀ x ∈ z.drop j, x = 0 := by
        intro x hx
        exact hz x (List.mem_of_mem_drop hx)
      simp [sum_eq_zero_of_forall_eq_zero hdrop]
  | cons x xs ih =>
      intro j
      cases j with
      | zero =>
          unfold tailSum
          simp [sum_eq_zero_of_forall_eq_zero hz]
      | succ j =>
          simpa [tailSum] using ih j

lemma trimZeros_eq_rdropWhile (l : List ℕ) :
    trimZeros l = l.rdropWhile (fun x => x = 0) := by
  simp [trimZeros, List.rdropWhile]

lemma tailSum_trimZeros (l : List ℕ) (j : ℕ) :
    tailSum (trimZeros l) j = tailSum l j := by
  have hdecomp : trimZeros l ++ l.rtakeWhile (fun x => x = 0) = l := by
    rw [trimZeros_eq_rdropWhile]
    exact List.rdropWhile_append_rtakeWhile (l := l) (p := fun x : ℕ => x = 0)
  have hz : ∀ x ∈ l.rtakeWhile (fun x => x = 0), x = 0 := by
    intro x hx
    exact of_decide_eq_true (List.mem_rtakeWhile_imp (p := fun y : ℕ => y = 0) hx)
  rw [show tailSum l j = tailSum (trimZeros l ++ l.rtakeWhile (fun x => x = 0)) j by rw [hdecomp]]
  exact (tailSum_append_zeros (trimZeros l) (l.rtakeWhile (fun x => x = 0)) j hz).symm



/-- A version of the untrimmed step with an incoming carry at the left boundary. -/
def caStepCarry (carry : ℕ) (config : List ℕ) : List ℕ :=
  List.zipWith Nat.add (config.map halfCeil ++ [0]) (carry :: config.map halfFloor)

lemma caStepLong_eq_carry (l : List ℕ) : caStepLong l = caStepCarry 0 l := by
  rfl

@[simp] lemma caStepCarry_nil (c : ℕ) : caStepCarry c [] = [c] := by
  simp [caStepCarry]

@[simp] lemma caStepCarry_cons (c x : ℕ) (xs : List ℕ) :
    caStepCarry c (x :: xs) = (halfCeil x + c) :: caStepCarry (halfFloor x) xs := by
  simp [caStepCarry]

lemma tailSum_caStepCarry_zero (c : ℕ) : ∀ l : List ℕ,
    tailSum (caStepCarry c l) 0 = c + tailSum l 0 := by
  intro l
  induction l generalizing c with
  | nil => simp [tailSum]
  | cons x xs ih =>
      rw [caStepCarry_cons]
      simp only [tailSum, List.drop_zero, List.sum_cons]
      have htail : (caStepCarry (halfFloor x) xs).sum = halfFloor x + xs.sum := by
        simpa [tailSum] using ih (halfFloor x)
      rw [htail]
      have hx := halfCeil_add_halfFloor x
      omega

lemma tailSum_caStepCarry_succ_eq_long (c : ℕ) (l : List ℕ) (j : ℕ) :
    tailSum (caStepCarry c l) (j + 1) = tailSum (caStepLong l) (j + 1) := by
  cases l with
  | nil => cases j <;> simp [tailSum, caStepLong]
  | cons x xs => simp [tailSum, caStepLong_eq_carry]

lemma tailSum_caStepLong_zero (l : List ℕ) :
    tailSum (caStepLong l) 0 = tailSum l 0 := by
  rw [caStepLong_eq_carry, tailSum_caStepCarry_zero]
  simp

lemma tailSum_caStepLong_succ : ∀ (l : List ℕ) (j : ℕ),
    tailSum (caStepLong l) (j + 1) = (tailSum l j + tailSum l (j + 1)) / 2 := by
  intro l
  induction l with
  | nil => intro j; cases j <;> simp [tailSum, caStepLong]
  | cons x xs ih =>
      intro j
      cases j with
      | zero =>
          change tailSum (caStepCarry (halfFloor x) xs) 0 =
            (tailSum (x :: xs) 0 + tailSum (x :: xs) 1) / 2
          rw [tailSum_caStepCarry_zero]
          simp [tailSum]
          unfold halfFloor
          rw [show (x + xs.sum + xs.sum) = x + 2 * xs.sum by omega]
          rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
      | succ j =>
          rw [caStepLong_eq_carry]
          change tailSum (caStepCarry (halfFloor x) xs) (j + 1) =
            (tailSum xs j + tailSum xs (j + 1)) / 2
          rw [tailSum_caStepCarry_succ_eq_long]
          exact ih j

lemma tailSum_caStep_zero (l : List ℕ) :
    tailSum (caStep l) 0 = tailSum l 0 := by
  simp [caStep, tailSum_trimZeros, tailSum_caStepLong_zero]

lemma tailSum_caStep_succ (l : List ℕ) (j : ℕ) :
    tailSum (caStep l) (j + 1) = (tailSum l j + tailSum l (j + 1)) / 2 := by
  simp [caStep, tailSum_trimZeros, tailSum_caStepLong_succ]


@[simp] lemma caState_zero (N : ℕ) : caState N 0 = [N] := by
  simp [caState]

lemma caState_succ (N t : ℕ) : caState N (t + 1) = caStep (caState N t) := by
  simp [caState, List.range_succ]

lemma caState_tail_flow (N : ℕ) : ∀ t j : ℕ,
    tailSum (caState N t) j = FlowProof.flow N t j := by
  intro t
  induction t with
  | zero =>
      intro j
      cases j <;> simp [tailSum]
  | succ t ih =>
      intro j
      rw [caState_succ]
      cases j with
      | zero =>
          rw [tailSum_caStep_zero, ih]
          cases t <;> simp [FlowProof.flow]
      | succ j =>
          rw [tailSum_caStep_succ, ih j, ih (j + 1)]
          rfl



lemma forall_eq_zero_of_sum_eq_zero {l : List ℕ} (h : l.sum = 0) : ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a xs ih =>
      simp at h
      rcases h with ⟨ha, hxs⟩
      intro x hx
      have hx' : x = a ∨ x ∈ xs := by simpa using hx
      rcases hx' with rfl | hxmem
      · exact ha
      · exact ih hxs x hxmem

lemma trimZeros_nil_of_sum_eq_zero {l : List ℕ} (h : l.sum = 0) : trimZeros l = [] := by
  rw [trimZeros_eq_rdropWhile]
  rw [List.rdropWhile_eq_nil_iff]
  intro x hx
  exact decide_eq_true ((forall_eq_zero_of_sum_eq_zero h) x hx)

lemma trimZeros_cons_one (xs : List ℕ) : trimZeros (1 :: xs) = 1 :: trimZeros xs := by
  rw [trimZeros_eq_rdropWhile, trimZeros_eq_rdropWhile]
  induction xs using List.reverseRecOn with
  | nil => simp [List.rdropWhile]
  | append_singleton xs x ih =>
      by_cases hx : x = 0
      · subst x
        rw [show 1 :: (xs ++ [0]) = (1 :: xs) ++ [0] by rfl]
        rw [List.rdropWhile_concat_pos]
        rw [List.rdropWhile_concat_pos (l := xs) (x := 0)]
        exact ih
        rfl
        rfl
      · have hdec : ¬ decide (x = 0) := by simpa [Bool.not_eq_true] using hx
        simp [List.rdropWhile_concat_neg, hdec]

lemma eq_replicate_of_trim_tail (l : List ℕ) : ∀ N : ℕ,
    trimZeros l = l → (∀ j : ℕ, tailSum l j = N - j) → l = List.replicate N 1 := by
  induction l with
  | nil =>
      intro N htrim htail
      cases N with
      | zero => simp
      | succ N =>
          have h := htail 0
          simp [tailSum] at h
  | cons x xs ih =>
      intro N htrim htail
      cases N with
      | zero =>
          have h0 : (x :: xs).sum = 0 := by simpa [tailSum] using htail 0
          have htz : trimZeros (x :: xs) = [] := trimZeros_nil_of_sum_eq_zero h0
          rw [htrim] at htz
          simp at htz
      | succ N =>
          have h0 : x + xs.sum = N + 1 := by simpa [tailSum] using htail 0
          have h1 : xs.sum = N := by simpa [tailSum] using htail 1
          have hx : x = 1 := by omega
          subst x
          have htrim_xs : trimZeros xs = xs := by
            have hc := htrim
            rw [trimZeros_cons_one] at hc
            exact (List.cons.inj hc).2
          have htail_xs : ∀ j : ℕ, tailSum xs j = N - j := by
            intro j
            have hj := htail (j + 1)
            simpa [tailSum] using hj
          have hxs := ih N htrim_xs htail_xs
          rw [hxs]
          rfl

lemma caState_trimZeros (N t : ℕ) (hN : 1 ≤ N) : trimZeros (caState N t) = caState N t := by
  cases t with
  | zero =>
      simp [caState, trimZeros]
      omega
  | succ t =>
      rw [caState_succ]
      simp [caStep]
      rw [trimZeros_eq_rdropWhile, trimZeros_eq_rdropWhile]
      exact List.rdropWhile_idempotent (p := fun x : ℕ => x = 0) (l := caStepLong (caState N t))

lemma flow_eq_staircase_of_hit {N t : ℕ} (hN : 1 ≤ N)
    (hhit : FlowProof.flow N t (N - 1) = 1) :
    ∀ j : ℕ, FlowProof.flow N t j = N - j := by
  intro j
  by_cases hj : j < N
  · have htauj_le_target : FlowProof.tau N j + (N - 1 - j) ≤ FlowProof.tau N (N - 1) := by
      have hidx : j + (N - 1 - j) < N := by omega
      have hle := FlowProof.tau_add_le (N := N) (j := j) (d := N - 1 - j) hidx
      have hidxeq : j + (N - 1 - j) = N - 1 := by omega
      simpa [hidxeq] using hle
    have htau_target_le_t : FlowProof.tau N (N - 1) ≤ t := by
      have hH : FlowProof.H N t (N - 1) = 0 := FlowProof.H_target_eq_zero_of_hit hN hhit
      exact FlowProof.tau_min hH
    have hHj : FlowProof.H N t j = 0 := FlowProof.H_eq_zero_of_tau_le (by omega)
    have hleF := FlowProof.flow_le_staircase N t j
    simp [FlowProof.H] at hHj
    omega
  · have hleF := FlowProof.flow_le_staircase N t j
    omega

lemma caState_eq_replicate_iff_hit {N t : ℕ} (hN : 1 ≤ N) :
    caState N t = List.replicate N 1 ↔ FlowProof.flow N t (N - 1) = 1 := by
  constructor
  · intro hstable
    have htail := caState_tail_flow N t (N - 1)
    rw [hstable] at htail
    have hval : FlowProof.flow N t (N - 1) = N - (N - 1) := by
      simpa [tailSum] using htail.symm
    omega
  · intro hhit
    apply eq_replicate_of_trim_tail (caState N t) N
    · exact caState_trimZeros N t hN
    · intro j
      rw [caState_tail_flow]
      exact flow_eq_staircase_of_hit hN hhit j


lemma a_eq_b (N : ℕ) (hN : 1 ≤ N) : a N = FlowProof.b N := by
  unfold a
  have hne : ¬ N = 0 := by omega
  simp [hne]
  change sInf {k : ℕ | caState N k = List.replicate N 1} = FlowProof.b N
  unfold FlowProof.b
  congr
  ext k
  exact caState_eq_replicate_iff_hit hN

/-- The original list CA hitting time agrees with the scalar-flow theorem, so its
finite differences are one or two. -/
theorem original_ca_finite_difference_via_tail_bridge :
    ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  have hb := FlowProof.b_finite_diff n hn
  have hn1 : 1 ≤ n + 1 := by omega
  rw [a_eq_b n hn, a_eq_b (n + 1) hn1]
  exact hb




lemma massList_length (N t : ℕ) : (massList N t).length = N + 1 := by
  simp [massList]

lemma massList_getElem (N t i : ℕ) (h : i < (massList N t).length) :
    (massList N t)[i] = FlowProof.flow N t i - FlowProof.flow N t (i + 1) := by
  simp [massList, List.getElem_range]

lemma massList_eq_replicate_append_zero_of_hit {N t : ℕ} (hN : 1 ≤ N)
    (hhit : FlowProof.flow N t (N - 1) = 1) :
    massList N t = List.replicate N 1 ++ [0] := by
  apply List.ext_getElem
  · simp [massList]
  · intro i hi1 hi2
    have hiN1 : i < N + 1 := by simpa [massList] using hi1
    by_cases hiN : i < N
    · have htauj_le_target : FlowProof.tau N i + (N - 1 - i) ≤ FlowProof.tau N (N - 1) := by
        have hidx : i + (N - 1 - i) < N := by omega
        have hle := FlowProof.tau_add_le (N := N) (j := i) (d := N - 1 - i) hidx
        have hidxeq : i + (N - 1 - i) = N - 1 := by omega
        simpa [hidxeq] using hle
      have htau_target_le_t : FlowProof.tau N (N - 1) ≤ t := by
        have hH : FlowProof.H N t (N - 1) = 0 := FlowProof.H_target_eq_zero_of_hit hN hhit
        exact FlowProof.tau_min hH
      have hHi : FlowProof.H N t i = 0 := FlowProof.H_eq_zero_of_tau_le (by omega)
      have hFi : FlowProof.flow N t i = N - i := by
        have hleFi := FlowProof.flow_le_staircase N t i
        simp [FlowProof.H] at hHi
        omega
      by_cases hiLast : i + 1 = N
      · have hiEqLast : i = N - 1 := by omega
        have hFinext : FlowProof.flow N t (i + 1) = 0 := by
          have hs := FlowProof.flow_le_staircase N t (i + 1)
          omega
        have hR : (List.replicate N 1 ++ [0])[i] = 1 := by
          simp [hiN]
        rw [massList_getElem N t i hi1]
        rw [hR]
        omega
      · have hiNextN : i + 1 < N := by omega
        have htauj1_le_target : FlowProof.tau N (i + 1) + (N - 1 - (i + 1)) ≤ FlowProof.tau N (N - 1) := by
          have hidx : (i + 1) + (N - 1 - (i + 1)) < N := by omega
          have hle := FlowProof.tau_add_le (N := N) (j := i + 1) (d := N - 1 - (i + 1)) hidx
          have hidxeq : (i + 1) + (N - 1 - (i + 1)) = N - 1 := by omega
          simpa [hidxeq] using hle
        have hHi1 : FlowProof.H N t (i + 1) = 0 := FlowProof.H_eq_zero_of_tau_le (by omega)
        have hFi1 : FlowProof.flow N t (i + 1) = N - (i + 1) := by
          have hleFi1 := FlowProof.flow_le_staircase N t (i + 1)
          simp [FlowProof.H] at hHi1
          omega
        have hR : (List.replicate N 1 ++ [0])[i] = 1 := by
          simp [hiN]
        rw [massList_getElem N t i hi1]
        rw [hR]
        omega
    · have hiEq : i = N := by omega
      have hR : (List.replicate N 1 ++ [0])[i] = 0 := by
        subst i
        simp
      rw [massList_getElem N t i hi1]
      rw [hR]
      have hFN : FlowProof.flow N t N = 0 := by
        have hs := FlowProof.flow_le_staircase N t N
        omega
      have hFN1 : FlowProof.flow N t (N + 1) = 0 := by
        have hs := FlowProof.flow_le_staircase N t (N + 1)
        omega
      subst i
      omega

lemma trim_massList_of_hit {N t : ℕ} (hN : 1 ≤ N)
    (hhit : FlowProof.flow N t (N - 1) = 1) :
    trimZeros (massList N t) = List.replicate N 1 := by
  rw [massList_eq_replicate_append_zero_of_hit hN hhit]
  simp [trimZeros]

end Bridge

/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k)$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/
theorem oeis_a300997_finite_difference_is_one_or_two :
  ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  exact Bridge.original_ca_finite_difference_via_tail_bridge
