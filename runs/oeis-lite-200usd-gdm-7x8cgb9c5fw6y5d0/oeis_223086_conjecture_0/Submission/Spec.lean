import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 20000000
set_option maxHeartbeats 10000000

open Nat Classical

/--
A223086: Trajectory of 64 under the map $n \to A006368(n)$.
The map is $f(n)$:
$$f(n) = \begin{cases} 3n/2 & \text{if } n \equiv 0 \pmod 2 \\ (3n+1)/4 & \text{if } n \equiv 1 \pmod 4 \\ (3n-1)/4 & \text{if } n \equiv 3 \pmod 4 \end{cases}$$
-/
def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

/--
A223086: Trajectory of 64 under the map $n \to A006368(n)$.
The sequence $a(n)$ is 1-indexed by $a(1)=64$ and recurrence $a(n+1) = f(a(n))$.
The $n$-th term is $f^{n-1}(64)$.
-/
def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

theorem map_val_cases (k : ℕ) :
  (k % 4 = 0 → A006368_map k = (3 * k) / 2 ∧ A006368_map k % 3 = 0) ∧
  (k % 4 = 1 → A006368_map k = (3 * k + 1) / 4 ∧ A006368_map k % 3 = 1) ∧
  (k % 4 = 2 → A006368_map k = (3 * k) / 2 ∧ A006368_map k % 3 = 0) ∧
  (k % 4 = 3 → A006368_map k = (3 * k - 1) / 4 ∧ A006368_map k % 3 = 2) := by
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · -- k % 4 = 0
    have h2 : k % 2 = 0 := by omega
    unfold A006368_map
    rw [if_pos h2]
    refine ⟨rfl, ?_⟩
    omega
  · -- k % 4 = 1
    have h2 : k % 2 ≠ 0 := by omega
    unfold A006368_map
    rw [if_neg h2, if_pos h1]
    refine ⟨rfl, ?_⟩
    omega
  · -- k % 4 = 2
    have h2 : k % 2 = 0 := by omega
    unfold A006368_map
    rw [if_pos h2]
    refine ⟨rfl, ?_⟩
    omega
  · -- k % 4 = 3
    have h2 : k % 2 ≠ 0 := by omega
    have h4_1 : k % 4 ≠ 1 := by omega
    unfold A006368_map
    rw [if_neg h2, if_neg h4_1]
    refine ⟨rfl, ?_⟩
    omega

theorem A006368_map_injective : Function.Injective A006368_map := by
  intro x y h
  have hx4 : x % 4 < 4 := Nat.mod_lt _ (by decide)
  have hy4 : y % 4 < 4 := Nat.mod_lt _ (by decide)
  have h_mod : A006368_map x % 3 = A006368_map y % 3 := by rw [h]
  have hxc := map_val_cases x
  have hyc := map_val_cases y
  rcases hkx : x % 4 with _ | _ | _ | _ | _ <;> rcases hky : y % 4 with _ | _ | _ | _ | _
  all_goals try omega

theorem iterate_eq_of_injective {α : Type*} {f : α → α} (hf : Function.Injective f) {x : α} {a b : ℕ} (h : a < b) (heq : f^[a] x = f^[b] x) :
    x = f^[b - a] x := by
  have hab : b = a + (b - a) := (Nat.add_sub_of_le (Nat.le_of_lt h)).symm
  rw [hab] at heq
  rw [Function.iterate_add_apply f a (b - a) x] at heq
  have h_inj : Function.Injective (f^[a]) := hf.iterate a
  exact h_inj heq

theorem a_injective_of_no_cycle
    (hnocycle : ∀ k : ℕ, k > 0 → Nat.iterate A006368_map k 64 ≠ 64) :
    ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj heq
  rcases lt_trichotomy i j with hij | hij | hij
  · -- i < j
    have h_lt : i - 1 < j - 1 := by omega
    unfold a at heq
    have h_eq : 64 = A006368_map^[(j - 1) - (i - 1)] 64 := by
      exact iterate_eq_of_injective A006368_map_injective h_lt heq
    have h_sub : (j - 1) - (i - 1) = j - i := by omega
    rw [h_sub] at h_eq
    have h_gt : j - i > 0 := by omega
    have h_contra := hnocycle (j - i) h_gt
    exact False.elim (h_contra h_eq.symm)
  · -- i = j
    exact hij
  · -- j < i
    have h_lt : j - 1 < i - 1 := by omega
    unfold a at heq
    have h_eq : 64 = A006368_map^[(i - 1) - (j - 1)] 64 := by
      exact iterate_eq_of_injective A006368_map_injective h_lt heq.symm
    have h_sub : (i - 1) - (j - 1) = i - j := by omega
    rw [h_sub] at h_eq
    have h_gt : i - j > 0 := by omega
    have h_contra := hnocycle (i - j) h_gt
    exact False.elim (h_contra h_eq.symm)


def S (n : ℕ) : Prop :=
  n ≥ 112 ∧ ∀ k : ℕ, Nat.iterate A006368_map k n ≥ 112

theorem S_closed {n : ℕ} (h : S n) : S (A006368_map n) := by
  rcases h with ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · have h_f := h2 1
    exact h_f
  · intro k
    have h_fk := h2 (k + 1)
    exact h_fk

theorem S_iterate (n : ℕ) (h : S n) (k : ℕ) : S (Nat.iterate A006368_map k n) := by
  induction k generalizing n with
  | zero => exact h
  | succ k ih =>
    exact ih (A006368_map n) (S_closed h)

theorem ge_112_of_S {n : ℕ} (h : S n) (k : ℕ) : Nat.iterate A006368_map k n ≥ 112 := by
  have h_it := S_iterate n h k
  exact h_it.1



def B : List ℕ := [112, 113, 115, 117, 118, 119, 121, 122, 123, 124, 125, 127, 129, 131, 132, 133, 134, 135, 137, 139, 141, 143, 145, 147, 149, 150]

inductive IsBad : ℕ → Prop where
  | below_112 : ∀ x, x < 112 → IsBad x
  | step : ∀ x, IsBad (A006368_map x) → IsBad x

def H (x : ℕ) : Prop :=
  x ≥ 112 ∧ ¬ IsBad x

theorem H_closed {x : ℕ} (hx : H x) : H (A006368_map x) := by
  rcases hx with ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · by_contra h_lt
    push_neg at h_lt
    have h_bad_fx : IsBad (A006368_map x) := IsBad.below_112 (A006368_map x) h_lt
    have h_bad_x : IsBad x := IsBad.step x h_bad_fx
    exact h2 h_bad_x
  · intro h_bad_fx
    have h_bad_x : IsBad x := IsBad.step x h_bad_fx
    exact h2 h_bad_x

theorem H_iterate {x : ℕ} (hx : H x) (k : ℕ) : H (A006368_map^[k] x) := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ']
    exact H_closed ih

theorem ge_112_of_H {x : ℕ} (hx : H x) (k : ℕ) : A006368_map^[k] x ≥ 112 := by
  have h_it := H_iterate hx k
  exact h_it.1

theorem ge_112_of_gt_150 (x : ℕ) (h : x > 150) : A006368_map x ≥ 112 := by
  unfold A006368_map
  split_ifs with h2 h4
  · omega
  · omega
  · omega

theorem mem_B_of_f_lt_112 (y : ℕ) (h1 : y ≥ 112) (h2 : y ≤ 150) (h3 : A006368_map y < 112) : y ∈ B := by
  interval_cases y <;> revert h3 <;> decide

theorem exists_mem_B_of_IsBad {y : ℕ} (h_bad : IsBad y) : y ≥ 112 → ∃ k, A006368_map^[k] y ∈ B := by
  induction h_bad with
  | below_112 z hz =>
    intro hy
    omega
  | step z hz_bad ih =>
    intro hy
    by_cases h_fz : A006368_map z < 112
    · use 0
      simp only [Function.iterate_zero, id_eq]
      have h_le : z ≤ 150 := by
        by_contra h_gt
        push_neg at h_gt
        have h_ge := ge_112_of_gt_150 z h_gt
        omega
      exact mem_B_of_f_lt_112 z hy h_le h_fz
    · have h_fz_ge : A006368_map z ≥ 112 := by omega
      rcases ih h_fz_ge with ⟨k, hk⟩
      use k + 1
      have h_eq : A006368_map^[k + 1] z = A006368_map^[k] (A006368_map z) :=
        congrFun (Function.iterate_succ A006368_map k) z
      rw [h_eq]
      exact hk

theorem B_spec (x : ℕ) (hb : x ∈ B) : ∃ k, A006368_map^[k] x < 112 := by
  simp only [B, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 13; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 3; decide
  · use 1; decide
  · use 1; decide
  · use 3; decide
  · use 1; decide
  · use 8; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 6; decide
  · use 1; decide
  · use 4; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 14; decide
  · use 4; decide

theorem IsBad_of_exists_iterate_lt {x : ℕ} (h : ∃ k, A006368_map^[k] x < 112) : IsBad x := by
  rcases h with ⟨k, hk⟩
  induction k generalizing x with
  | zero =>
    exact IsBad.below_112 x hk
  | succ k ih =>
    have h_eq : A006368_map^[k + 1] x = A006368_map^[k] (A006368_map x) :=
      congrFun (Function.iterate_succ A006368_map k) x
    rw [h_eq] at hk
    have h_bad_fx : IsBad (A006368_map x) := ih hk
    exact IsBad.step x h_bad_fx

theorem IsBad_of_mem_B {x : ℕ} (h : x ∈ B) : IsBad x := by
  exact IsBad_of_exists_iterate_lt (B_spec x h)

def G_list : List ℕ := [114, 116, 120, 126, 128, 130, 136, 138, 140, 142, 144, 146, 148]

theorem disjoint_G_B : ∀ y, y ∈ G_list → y ∈ B → False := by decide

theorem G_list_ge_112 : ∀ x ∈ G_list, A006368_map x ≥ 112 := by decide

theorem not_mem_G_list_imp_mem_B : ∀ y, 112 ≤ y → y ≤ 150 → y ∉ G_list → y ∈ B := by decide

def B_200 : List ℕ := [112, 113, 115, 117, 118, 119, 121, 122, 123, 124, 125, 127, 129, 131, 132, 133, 134, 135, 137, 139, 141, 143, 145, 147, 149, 150, 151, 152, 153, 157, 159, 161, 163, 165, 167, 168, 169, 170, 175, 177, 179, 183, 185, 186, 191, 193, 198, 199]

def get_bad_steps (fuel : ℕ) (x : ℕ) : Option ℕ :=
  match fuel with
  | 0 => none
  | f + 1 =>
    if x < 112 then some 0
    else match get_bad_steps f (A006368_map x) with
         | some s => some (s + 1)
         | none => none

theorem IsBad_of_get_bad_steps {fuel x s : ℕ} (h : get_bad_steps fuel x = some s) : IsBad x := by
  induction fuel generalizing x s with
  | zero => contradiction
  | succ f ih =>
    unfold get_bad_steps at h
    split_ifs at h with h1
    · exact IsBad.below_112 x h1
    · rcases h_eq : get_bad_steps f (A006368_map x) with _ | s'
      · rw [h_eq] at h; contradiction
      · rw [h_eq] at h
        injection h with h_eq2
        have ih_fx := ih h_eq
        exact IsBad.step x ih_fx

theorem IsBad_of_mem_B_200 (y : ℕ) (hy : y ∈ B_200) : IsBad y := by
  have h_all : B_200.all (fun x => (get_bad_steps 100 x).isSome) = true := by decide
  rw [List.all_eq_true] at h_all
  have h_some := h_all y hy
  rcases h_opt : get_bad_steps 100 y with _ | s
  · rw [h_opt] at h_some
    contradiction
  · exact IsBad_of_get_bad_steps h_opt

theorem not_mem_B_of_S {z : ℕ} (hz : S z) : z ∉ B := by
  intro hb
  have h_drop := B_spec z hb
  rcases h_drop with ⟨k, hk⟩
  have h_ge := ge_112_of_S hz k
  omega

theorem not_mem_B_200_of_S {z : ℕ} (hz : S z) : z ∉ B_200 := by
  intro hb
  have h_bad := IsBad_of_mem_B_200 z hb
  have h_ex := exists_mem_B_of_IsBad h_bad hz.1
  rcases h_ex with ⟨m, hm⟩
  have h_drop := B_spec (A006368_map^[m] z) hm
  rcases h_drop with ⟨k, hk⟩
  have h_total : A006368_map^[k + m] z < 112 := by
    rw [Function.iterate_add_apply]
    exact hk
  have h_ge := ge_112_of_S hz (k + m)
  omega


def is_bad_dt_all (x : ℕ) : Bool :=
  if x < 112 then true
  else decide (x ∈ B_200)

theorem IsBad_of_is_bad_dt_all_true {z : ℕ} (h : is_bad_dt_all z = true) : IsBad z := by
  unfold is_bad_dt_all at h
  split_ifs at h with h1
  · exact IsBad.below_112 z h1
  · have h_mem : z ∈ B_200 := by
      rw [decide_eq_true_iff] at h
      exact h
    exact IsBad_of_mem_B_200 z h_mem

theorem is_bad_dt_all_closed : (List.range' 112 (200 - 112 + 1)).all (fun x => decide (is_bad_dt_all x = false → is_bad_dt_all (A006368_map x) = false)) = true := by decide

theorem is_bad_dt_all_closed_range {x : ℕ} (h1 : x ≥ 112) (h2 : x ≤ 200) (hx : is_bad_dt_all x = false) : is_bad_dt_all (A006368_map x) = false := by
  have h_mem : x ∈ List.range' 112 (200 - 112 + 1) := by
    simp only [List.mem_range'_1]
    omega
  have h_all := is_bad_dt_all_closed
  rw [List.all_eq_true] at h_all
  have h_x := h_all x h_mem
  simp only [decide_eq_true_iff] at h_x
  exact h_x hx

theorem B_200_le {z : ℕ} (hz : z ∈ B_200) : z ≤ 200 := by
  have h_all : B_200.all (fun z => decide (z ≤ 200)) = true := by decide
  rw [List.all_eq_true] at h_all
  have hz_dec := h_all z hz
  simp only [decide_eq_true_iff] at hz_dec
  exact hz_dec

theorem step_back_all_decide : (List.range' 0 201).all (fun x => decide (is_bad_dt_all (A006368_map x) = true → is_bad_dt_all x = true)) = true := by decide

theorem is_bad_dt_all_step_back_range {x : ℕ} (hx : is_bad_dt_all (A006368_map x) = true) (h_le : x ≤ 200) : is_bad_dt_all x = true := by
  have h_all := step_back_all_decide
  rw [List.all_eq_true] at h_all
  have h_mem : x ∈ List.range' 0 201 := by
    simp only [List.mem_range'_1]
    omega
  have h_x := h_all x h_mem
  simp only [decide_eq_true_iff] at h_x
  exact h_x hx

theorem B_sub_B_200_all : B.all (fun x => decide (x ∈ B_200)) = true := by decide

theorem B_sub_B_200 {z : ℕ} (hz : z ∈ B) : z ∈ B_200 := by
  have h_all := B_sub_B_200_all
  rw [List.all_eq_true] at h_all
  have h_z := h_all z hz
  simp only [decide_eq_true_iff] at h_z
  exact h_z

theorem y_le_200_of_fy_le_150 {y : ℕ} (_hy_gt : y > 150) (h : A006368_map y ≤ 150) : y ≤ 200 := by
  unfold A006368_map at h
  split_ifs at h with h1 h2
  · omega
  · omega
  · omega



theorem get_bad_steps_of_mem_B {x : ℕ} (hx : x ∈ B) : (get_bad_steps 15 x).isSome = true := by
  have h_all : B.all (fun x => (get_bad_steps 15 x).isSome) = true := by decide
  rw [List.all_eq_true] at h_all
  exact h_all x hx

theorem get_bad_steps_isSome_of_exists_iterate_mem_B (k : ℕ) (y : ℕ) (hk : A006368_map^[k] y ∈ B) : (get_bad_steps (k + 15) y).isSome = true := by
  induction k generalizing y with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hk
    exact get_bad_steps_of_mem_B hk
  | succ k ih =>
    have h_eq : A006368_map^[k + 1] y = A006368_map^[k] (A006368_map y) :=
      congrFun (Function.iterate_succ A006368_map k) y
    rw [h_eq] at hk
    have ih_fy := ih (A006368_map y) hk
    by_cases hy_lt : y < 112
    · unfold get_bad_steps
      rw [if_pos hy_lt]
      rfl
    · unfold get_bad_steps
      rw [if_neg hy_lt]
      cases h_opt : get_bad_steps (k + 15) (A006368_map y) with
      | none =>
        rw [h_opt] at ih_fy
        contradiction
      | some s =>
        rfl

theorem get_bad_steps_mono (f1 : ℕ) (f2 : ℕ) (hle : f1 ≤ f2) (y : ℕ) (s : ℕ) (h : get_bad_steps f1 y = some s) : get_bad_steps f2 y = some s := by
  induction f1 generalizing f2 y s with
  | zero => contradiction
  | succ f1 ih =>
    rcases f2 with _ | f2
    · omega
    · unfold get_bad_steps at h ⊢
      split_ifs at h ⊢ with hy
      · exact h
      · rcases h_eq : get_bad_steps f1 (A006368_map y) with _ | s'
        · rw [h_eq] at h; contradiction
        · rw [h_eq] at h
          have h_le2 : f1 ≤ f2 := by omega
          have ih_rec := ih f2 h_le2 (A006368_map y) s' h_eq
          rw [ih_rec]
          exact h

theorem B_200_step_back_large : (List.range' 112 (200 - 112 + 1)).all (fun x => decide (A006368_map x ≤ 200 ∨ (get_bad_steps 100 (A006368_map x)).isSome = false ∨ x ∈ B_200)) = true := by decide

theorem mem_B_200_of_f_lt_112 (y : ℕ) (h1 : y ≥ 112) (h2 : y ≤ 200) (h3 : A006368_map y < 112) : is_bad_dt_all y = true := by
  have h_le : y ≤ 150 := by
    by_contra h_gt
    push_neg at h_gt
    have h_ge := ge_112_of_gt_150 y h_gt
    omega
  have h_B := mem_B_of_f_lt_112 y h1 h_le h3
  have h_B200 := B_sub_B_200 h_B
  unfold is_bad_dt_all
  rw [if_neg (by omega)]
  exact decide_eq_true_iff.mpr h_B200

theorem is_bad_dt_all_true_of_get_bad_steps (fuel y s : ℕ) (h_fuel : fuel ≤ 100) (h : get_bad_steps fuel y = some s) (hy_ge : y ≥ 112) (hy_le : y ≤ 200) : is_bad_dt_all y = true := by
  induction fuel generalizing y s with
  | zero => contradiction
  | succ f ih =>
    unfold get_bad_steps at h
    split_ifs at h with hy_lt
    · omega
    · rcases h_eq : get_bad_steps f (A006368_map y) with _ | s'
      · rw [h_eq] at h; contradiction
      · rw [h_eq] at h
        injection h with h_s
        have h_f_le : f ≤ 100 := by omega
        by_cases h_fy_lt : A006368_map y < 112
        · exact mem_B_200_of_f_lt_112 y hy_ge hy_le h_fy_lt
        · have h_fy_ge : A006368_map y ≥ 112 := by omega
          by_cases h_fy_le : A006368_map y ≤ 200
          · have h_rec := ih (A006368_map y) s' h_f_le h_eq h_fy_ge h_fy_le
            exact is_bad_dt_all_step_back_range h_rec hy_le
          · push_neg at h_fy_le
            have h_large := B_200_step_back_large
            rw [List.all_eq_true] at h_large
            have h_mem : y ∈ List.range' 112 (200 - 112 + 1) := by
              simp only [List.mem_range'_1]
              omega
            have h_y := h_large y h_mem
            simp only [decide_eq_true_iff] at h_y
            rcases h_y with h_fy_le_200 | h_none | h_B200
            · omega
            · have h_some : (get_bad_steps 100 (A006368_map y)).isSome = true := by
                have h_mono := get_bad_steps_mono f 100 h_f_le (A006368_map y) s' h_eq
                rw [h_mono]
                rfl
              rw [h_some] at h_none
              contradiction
            · unfold is_bad_dt_all
              rw [if_neg (by omega)]
              exact decide_eq_true_iff.mpr h_B200

theorem get_bad_steps_exact (fuel y s : ℕ) (h : get_bad_steps fuel y = some s) : get_bad_steps (s + 1) y = some s := by
  induction fuel generalizing y s with
  | zero => contradiction
  | succ f ih =>
    unfold get_bad_steps at h
    split_ifs at h with hy_lt
    · injection h with h_s
      subst h_s
      unfold get_bad_steps
      rw [if_pos hy_lt]
    · rcases h_eq : get_bad_steps f (A006368_map y) with _ | s'
      · rw [h_eq] at h; contradiction
      · rw [h_eq] at h
        injection h with h_s
        subst h_s
        have ih_rec := ih (A006368_map y) s' h_eq
        unfold get_bad_steps
        rw [if_neg hy_lt, ih_rec]

theorem s_lt_fuel {fuel x s : ℕ} (h : get_bad_steps fuel x = some s) : s < fuel := by
  induction fuel generalizing x s with
  | zero => contradiction
  | succ f ih =>
    unfold get_bad_steps at h
    split_ifs at h with hx
    · injection h with hs
      omega
    · rcases h_eq : get_bad_steps f (A006368_map x) with _ | s'
      · rw [h_eq] at h; contradiction
      · rw [h_eq] at h
        injection h with hs_eq
        have ih_rec := ih h_eq
        omega

theorem is_bad_dt_all_true_of_IsBad (y : ℕ) (h_bad : IsBad y) (hy_ge : y ≥ 112) (hy_le : y ≤ 200) : is_bad_dt_all y = true := by
  induction h_bad with
  | below_112 z hz =>
    omega
  | step z hz_bad ih =>
    revert ih
    interval_cases z
    all_goals intro ih
    all_goals try (unfold is_bad_dt_all; decide)
    all_goals try (
      exact is_bad_dt_all_step_back_range (ih (by decide) (by decide)) (by decide)
    )


theorem s_lt_98_of_get_bad_steps {y s : ℕ} (h : get_bad_steps 100 y = some s) (hy : y > 200) : s < 98 := by
  unfold get_bad_steps at h
  have hy_ge : ¬ y < 112 := by omega
  rw [if_neg hy_ge] at h
  rcases h_eq : get_bad_steps 99 (A006368_map y) with _ | s'
  · rw [h_eq] at h; contradiction
  · rw [h_eq] at h
    injection h with hs_eq
    unfold get_bad_steps at h_eq
    have h_fy_ge : ¬ A006368_map y < 112 := by
      have h_ge := ge_112_of_gt_150 y (by omega)
      omega
    rw [if_neg h_fy_ge] at h_eq
    rcases h_eq2 : get_bad_steps 98 (A006368_map (A006368_map y)) with _ | s''
    · rw [h_eq2] at h_eq; contradiction
    · rw [h_eq2] at h_eq
      injection h_eq with hs_eq2
      have h_lt := s_lt_fuel h_eq2
      omega

def IsGoodState (y : ℕ) : Prop :=
  y ≥ 112 ∧ (y ≤ 200 → is_bad_dt_all y = false) ∧ (y > 200 → (get_bad_steps 100 y).isSome = false)

theorem IsGoodState_of_mem_G_list {z : ℕ} (h_G : z ∈ G_list) : IsGoodState z := by
  refine ⟨?_, ?_, ?_⟩
  · have h_ge : G_list.all (fun x => decide (x ≥ 112)) = true := by decide
    rw [List.all_eq_true] at h_ge
    have h_dec := h_ge z h_G
    simp only [decide_eq_true_iff] at h_dec
    omega
  · intro _
    unfold is_bad_dt_all
    rw [if_neg (by
      have h_ge : G_list.all (fun x => decide (x ≥ 112)) = true := by decide
      rw [List.all_eq_true] at h_ge
      have h_dec := h_ge z h_G
      simp only [decide_eq_true_iff] at h_dec
      omega
    )]
    have h_disj : G_list.all (fun x => decide (x ∉ B_200)) = true := by decide
    rw [List.all_eq_true] at h_disj
    have h_dec := h_disj z h_G
    simp only [decide_eq_true_iff] at h_dec
    exact decide_eq_false h_dec
  · intro h_gt
    have h_le : G_list.all (fun x => decide (x ≤ 150)) = true := by decide
    rw [List.all_eq_true] at h_le
    have h_dec := h_le z h_G
    simp only [decide_eq_true_iff] at h_dec
    omega

theorem IsGoodState_of_H {z : ℕ} (hz : H z) : IsGoodState z := by
  rcases hz with ⟨hz1, hz2⟩
  refine ⟨hz1, ?_, ?_⟩
  · intro _
    unfold is_bad_dt_all
    rw [if_neg (by omega)]
    have h_not_mem : z ∉ B_200 := by
      intro h_mem
      have h_bad := IsBad_of_mem_B_200 z h_mem
      exact hz2 h_bad
    exact decide_eq_false h_not_mem
  · intro _
    simp only [Option.isSome_iff_exists, not_exists]
    intro s hs
    have h_bad := IsBad_of_get_bad_steps hs
    exact hz2 h_bad

theorem IsGoodState_closed (y : ℕ) (hy : IsGoodState y) : IsGoodState (A006368_map y) := by
  rcases hy with ⟨h1, h2, h3⟩
  have h_fy_ge : A006368_map y ≥ 112 := by
    by_cases hy_le : y ≤ 200
    · have h_false := h2 hy_le
      by_contra h_lt
      push_neg at h_lt
      have h_bad : is_bad_dt_all y = true := mem_B_200_of_f_lt_112 y h1 hy_le h_lt
      rw [h_bad] at h_false
      contradiction
    · push_neg at hy_le
      exact ge_112_of_gt_150 y (by omega)
  refine ⟨h_fy_ge, ?_, ?_⟩
  · -- A006368_map y ≤ 200 → is_bad_dt_all (A006368_map y) = false
    intro h_fy_le
    by_cases hy_le : y ≤ 200
    · exact is_bad_dt_all_closed_range h1 hy_le (h2 hy_le)
    · push_neg at hy_le
      have h_some_false := h3 hy_le
      by_contra h_bad
      have h_bad_true : is_bad_dt_all (A006368_map y) = true := by
        cases h_eq : is_bad_dt_all (A006368_map y)
        · contradiction
        · rfl
      have h_mem : A006368_map y ∈ B_200 := by
        unfold is_bad_dt_all at h_bad_true
        rw [if_neg (by omega)] at h_bad_true
        exact decide_eq_true_iff.mp h_bad_true
      have h_opt : (get_bad_steps 100 (A006368_map y)).isSome = true := by
        have h_all : B_200.all (fun x => (get_bad_steps 100 x).isSome) = true := by decide
        rw [List.all_eq_true] at h_all
        exact h_all (A006368_map y) h_mem
      rcases Option.isSome_iff_exists.mp h_opt with ⟨s, hs⟩
      have h_fuel : get_bad_steps 101 y = some (s + 1) := by
        unfold get_bad_steps
        rw [if_neg (by omega), hs]
      have h_exact := get_bad_steps_exact 101 y (s + 1) h_fuel
      have h_s_lt_98 : s + 1 < 98 := s_lt_98_of_get_bad_steps h_exact (by omega)
      have h_mono := get_bad_steps_mono (s + 2) 100 (by omega) y (s + 1) h_exact
      rw [h_mono] at h_some_false
      contradiction
  · -- A006368_map y > 200 → (get_bad_steps 100 (A006368_map y)).isSome = false
    intro h_fy_gt
    by_cases hy_le : y ≤ 200
    · -- y ≤ 200
      have h_false := h2 hy_le
      by_contra h_bad
      have h_large := B_200_step_back_large
      rw [List.all_eq_true] at h_large
      have h_mem_range : y ∈ List.range' 112 (200 - 112 + 1) := by
        simp only [List.mem_range'_1]
        omega
      have h_dec := h_large y h_mem_range
      simp only [decide_eq_true_iff] at h_dec
      rcases h_dec with h_fy_le_200 | h_some_false | h_B200
      · omega
      · exact h_bad h_some_false
      · unfold is_bad_dt_all at h_false
        rw [if_neg (by omega)] at h_false
        simp only [decide_eq_false_iff_not] at h_false
        exact h_false h_B200
    · -- y > 200
      push_neg at hy_le
      have h_some_false := h3 hy_le
      by_contra h_bad
      have h_opt : (get_bad_steps 100 (A006368_map y)).isSome = true := by
        cases h_eq : (get_bad_steps 100 (A006368_map y)).isSome
        · contradiction
        · rfl
      rcases Option.isSome_iff_exists.mp h_opt with ⟨s, hs⟩
      have h_fuel : get_bad_steps 101 y = some (s + 1) := by
        unfold get_bad_steps
        rw [if_neg (by omega), hs]
      have h_exact := get_bad_steps_exact 101 y (s + 1) h_fuel
      have h_s_lt_98 : s + 1 < 98 := s_lt_98_of_get_bad_steps h_exact (by omega)
      have h_mono := get_bad_steps_mono (s + 2) 100 (by omega) y (s + 1) h_exact
      rw [h_mono] at h_some_false
      contradiction

theorem IsGoodState_iterate (y : ℕ) (hy : IsGoodState y) (k : ℕ) : IsGoodState (A006368_map^[k] y) := by
  induction k with
  | zero => exact hy
  | succ k ih =>
    rw [Function.iterate_succ']
    exact IsGoodState_closed (A006368_map^[k] y) ih

theorem S_of_IsGoodState {y : ℕ} (h : IsGoodState y) : S y := by
  refine ⟨h.1, ?_⟩
  intro k
  have h_it := IsGoodState_iterate y h k
  exact h_it.1



theorem IsGoodState_144 : IsGoodState 144 := by
  refine ⟨by decide, by decide, fun h => by omega⟩

theorem S_144 : S 144 := by
  exact S_of_IsGoodState IsGoodState_144

theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  have hnocycle : ∀ k : ℕ, k > 0 → Nat.iterate A006368_map k 64 ≠ 64 := by
    intro k hk
    rcases k with _ | k
    · omega
    · rcases k with _ | k
      · -- k = 1
        decide
      · -- k >= 2
        have h_it : Nat.iterate A006368_map (k + 2) 64 = Nat.iterate A006368_map k 144 := by
          change A006368_map^[k + 2] 64 = A006368_map^[k] 144
          rw [Function.iterate_add_apply]
          rfl
        rw [h_it]
        have h_ge : Nat.iterate A006368_map k 144 ≥ 112 := ge_112_of_S S_144 k
        omega
  exact a_injective_of_no_cycle hnocycle

theorem test_114 (hz_bad : IsBad (A006368_map 114))
  (ih : A006368_map 114 ≥ 112 → A006368_map 114 ≤ 200 → is_bad_dt_all (A006368_map 114) = true) :
  is_bad_dt_all 114 = true := by
  exact is_bad_dt_all_step_back_range (ih (by decide) (by decide)) (by decide)

