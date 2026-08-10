import FormalConjectures.Util.ProblemImports
open List Nat

namespace A381

/-- run-length encoding: list of (value, count) of maximal runs. -/
def runsOf : List ℕ → List (ℕ × ℕ)
  | [] => []
  | h :: t =>
    match runsOf t with
    | [] => [(h, 1)]
    | (v, c) :: rest => if h = v then (v, c + 1) :: rest else (h, 1) :: (v, c) :: rest

/-- decode a run-list back to a flat list. -/
def decode : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (v, c) :: rest => List.replicate c v ++ decode rest

#eval runsOf [1,1,1,3,1]   -- expect [(1,3),(3,1),(1,1)]
#eval decode (runsOf [1,1,1,3,1])
#eval runsOf [2,1,1,1]

/-- `run_lengths_nat` from Spec, copied here for development. -/
def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

-- decode∘runsOf = id
theorem decode_runsOf (l : List ℕ) : decode (runsOf l) = l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [runsOf]
    cases hr : runsOf t with
    | nil =>
      rw [hr] at ih
      simp only [decode] at ih
      simp only [decode, List.replicate_one]
      rw [← ih]; rfl
    | cons p rest =>
      obtain ⟨v, c⟩ := p
      rw [hr] at ih
      simp only [decode] at ih
      by_cases hhv : h = v
      · subst hhv
        simp only [if_true, decode, List.replicate_succ, List.cons_append, ih]
      · simp only [if_neg hhv, decode, List.replicate_one, List.singleton_append, ih]

/-- prepend a single value `h` to a run-list (the head step of `runsOf`). -/
def prependRun (h : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(h, 1)]
  | (v, c) :: rest => if h = v then (v, c + 1) :: rest else (h, 1) :: (v, c) :: rest

theorem runsOf_cons (h : ℕ) (t : List ℕ) :
    runsOf (h :: t) = prependRun h (runsOf t) := by
  simp only [runsOf, prependRun]

/-- concatenate two run-lists, merging the boundary runs if equal value. -/
def mergeConcat : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], B => B
  | [(v, c)], B =>
      match B with
      | [] => [(v, c)]
      | (v', c') :: B' => if v = v' then (v, c + c') :: B' else (v, c) :: (v', c') :: B'
  | (a :: b :: A'), B => a :: mergeConcat (b :: A') B

@[simp] theorem mergeConcat_nil_left (B : List (ℕ × ℕ)) : mergeConcat [] B = B := rfl

@[simp] theorem mergeConcat_single_nil (v c : ℕ) : mergeConcat [(v, c)] [] = [(v, c)] := rfl

theorem mergeConcat_single_cons (v c v' c' : ℕ) (B' : List (ℕ × ℕ)) :
    mergeConcat [(v, c)] ((v', c') :: B') =
      if v = v' then (v, c + c') :: B' else (v, c) :: (v', c') :: B' := rfl

theorem mergeConcat_cons_cons (a b : ℕ × ℕ) (A' B : List (ℕ × ℕ)) :
    mergeConcat (a :: b :: A') B = a :: mergeConcat (b :: A') B := rfl

/-- key commutation lemma. -/
theorem mergeConcat_prependRun (h : ℕ) (R1 R2 : List (ℕ × ℕ)) :
    mergeConcat (prependRun h R1) R2 = prependRun h (mergeConcat R1 R2) := by
  cases R1 with
  | nil =>
    simp only [prependRun, mergeConcat_nil_left]
    cases R2 with
    | nil => rfl
    | cons p B' =>
      obtain ⟨v', c'⟩ := p
      rw [mergeConcat_single_cons]
      by_cases hv : h = v'
      · simp only [if_pos hv, prependRun, hv, Nat.add_comm]
      · simp only [if_neg hv, prependRun, if_neg hv]
  | cons p rest =>
    obtain ⟨v, c⟩ := p
    by_cases hv : h = v
    · simp only [prependRun, if_pos hv]
      cases rest with
      | nil =>
        cases R2 with
        | nil => simp only [mergeConcat_single_nil, prependRun, if_pos hv]
        | cons q B' =>
          obtain ⟨v', c'⟩ := q
          by_cases hv2 : v = v'
          · simp only [mergeConcat_single_cons, if_pos hv2, prependRun, if_pos hv,
              Nat.add_right_comm]
          · simp only [mergeConcat_single_cons, if_neg hv2, prependRun, if_pos hv]
      | cons r rest' =>
        simp only [mergeConcat_cons_cons, prependRun, if_pos hv]
    · simp only [prependRun, if_neg hv]
      cases rest with
      | nil =>
        cases R2 with
        | nil => simp only [mergeConcat_cons_cons, mergeConcat_single_nil, prependRun, if_neg hv]
        | cons q B' =>
          obtain ⟨v', c'⟩ := q
          by_cases hv2 : v = v'
          · simp only [mergeConcat_cons_cons, mergeConcat_single_cons, if_pos hv2, prependRun,
              if_neg hv]
          · simp only [mergeConcat_cons_cons, mergeConcat_single_cons, if_neg hv2, prependRun,
              if_neg hv]
      | cons r rest' =>
        simp only [mergeConcat_cons_cons, prependRun, if_neg hv]

/-- runs of a concatenation. -/
theorem runsOf_append (A B : List ℕ) :
    runsOf (A ++ B) = mergeConcat (runsOf A) (runsOf B) := by
  induction A with
  | nil => simp [runsOf]
  | cons h A' ih =>
    rw [List.cons_append, runsOf_cons, ih, runsOf_cons, mergeConcat_prependRun]

theorem mergeConcat_cons_ne (x : ℕ × ℕ) (rest B : List (ℕ × ℕ)) (h : rest ≠ []) :
    mergeConcat (x :: rest) B = x :: mergeConcat rest B := by
  cases rest with
  | nil => exact absurd rfl h
  | cons b A' => rw [mergeConcat_cons_cons]

/-- mergeConcat only touches the boundary: appending on the left distributes. -/
theorem mergeConcat_append_singleton_left (X : List (ℕ × ℕ)) (a : ℕ × ℕ) (B : List (ℕ × ℕ)) :
    mergeConcat (X ++ [a]) B = X ++ mergeConcat [a] B := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    rw [List.cons_append, mergeConcat_cons_ne _ _ _ (by simp), ih, List.cons_append]

theorem mergeConcat_singleton_right (v c h : ℕ) :
    mergeConcat [(v, c)] [(h, 1)] = if v = h then [(v, c + 1)] else [(v, c), (h, 1)] := by
  rw [mergeConcat_single_cons]

/-- reversal equivariance for run-length encoding. -/
theorem runsOf_reverse (L : List ℕ) : runsOf L.reverse = (runsOf L).reverse := by
  induction L with
  | nil => rfl
  | cons h t ih =>
    rw [List.reverse_cons, runsOf_append, ih, runsOf_cons]
    -- goal: mergeConcat (runsOf t).reverse (runsOf [h]) = (prependRun h (runsOf t)).reverse
    show mergeConcat (runsOf t).reverse [(h, 1)] = (prependRun h (runsOf t)).reverse
    cases hR : runsOf t with
    | nil => simp [prependRun]
    | cons p rest =>
      obtain ⟨v, c⟩ := p
      rw [List.reverse_cons, mergeConcat_append_singleton_left, mergeConcat_singleton_right]
      simp only [prependRun]
      by_cases hhv : h = v
      · rw [if_pos hhv]
        have : v = h := hhv.symm
        rw [if_pos this, List.reverse_cons]
      · rw [if_neg hhv]
        have : ¬ v = h := fun hc => hhv hc.symm
        rw [if_neg this, List.reverse_cons, List.reverse_cons]
        simp

/-- the first run of `runsOf (h :: t)` has value `h`. -/
theorem runsOf_cons_head (h : ℕ) (t : List ℕ) :
    ∃ c rest, runsOf (h :: t) = (h, c) :: rest := by
  rw [runsOf_cons]
  cases runsOf t with
  | nil => exact ⟨1, [], rfl⟩
  | cons p rest =>
    obtain ⟨v, c⟩ := p
    simp only [prependRun]
    by_cases hv : h = v
    · subst hv; rw [if_pos rfl]; exact ⟨c + 1, rest, rfl⟩
    · rw [if_neg hv]; exact ⟨1, (v, c) :: rest, rfl⟩

/-- grouping: `runsOf` of `h :: t` exposes the first whole run. -/
theorem runsOf_group (h : ℕ) (t : List ℕ) :
    runsOf (h :: t) =
      (h, (List.takeWhile (fun x => x = h) (h :: t)).length) ::
        runsOf (List.dropWhile (fun x => x = h) (h :: t)) := by
  induction t with
  | nil => simp [runsOf, List.takeWhile, List.dropWhile]
  | cons h' t' ih =>
    rw [runsOf_cons]
    by_cases hh : h' = h
    · subst hh
      -- both takeWhile of (h'::h'::t')
      rw [ih]
      simp only [prependRun, if_pos rfl]
      rw [List.takeWhile_cons_of_pos (by simp), List.takeWhile_cons_of_pos (by simp),
        List.dropWhile_cons_of_pos (by simp), List.dropWhile_cons_of_pos (by simp)]
      simp [List.length_cons]
    · -- h' ≠ h
      rw [List.takeWhile_cons_of_pos (by simp), List.dropWhile_cons_of_pos (by simp),
        List.takeWhile_cons_of_neg (by simp [hh]), List.dropWhile_cons_of_neg (by simp [hh])]
      simp only [List.length_nil, List.length_cons, Nat.zero_add]
      obtain ⟨c, rest, hcr⟩ := runsOf_cons_head h' t'
      rw [hcr]
      simp only [prependRun]
      rw [if_neg (Ne.symm hh)]

theorem run_lengths_nat_eq (l : List ℕ) : run_lengths_nat l = (runsOf l).map Prod.snd := by
  fun_induction run_lengths_nat l with
  | case1 => rfl
  | case2 h t rp rest ih =>
    have hr : rest = (h :: t).dropWhile (fun x => x = h) := by
      show (h :: t).drop (List.takeWhile (fun x => x = h) (h :: t)).length
          = (h :: t).dropWhile (fun x => x = h)
      nth_rewrite 2 [← List.takeWhile_append_dropWhile (p := fun x => x = h) (l := h :: t)]
      rw [List.drop_left]
    rw [hr] at ih
    rw [runsOf_group h t, List.map_cons, show rp = _ from rfl, hr, ih]

/-! ## Connection to A381587 / A381358 -/

def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

def A381358 (n : ℕ) : ℕ := (A381587_T n).sum

/-- the run-list of `U_n = reverse (T n)`. -/
def RU (n : ℕ) : List (ℕ × ℕ) := runsOf (A381587_T n).reverse

/-- weighted sum of a run-list = sum of the decoded list. -/
def sumRL (R : List (ℕ × ℕ)) : ℕ := (R.map (fun p => p.1 * p.2)).sum

theorem sumRL_eq_decode_sum (R : List (ℕ × ℕ)) : sumRL R = (decode R).sum := by
  induction R with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, c⟩ := p
    simp only [sumRL, decode, List.map_cons, List.sum_cons, List.sum_append, List.sum_replicate,
      smul_eq_mul, sumRL] at *
    rw [ih]; ring

theorem A381358_eq_sumRL (n : ℕ) : A381358 n = sumRL (RU n) := by
  rw [sumRL_eq_decode_sum, RU, decode_runsOf, A381358, List.sum_reverse]

/-- the step map on run-lists. -/
def stepRL (R : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  mergeConcat R ((runsOf (R.map Prod.snd)).reverse)

theorem RU_succ (n : ℕ) : RU (n + 4) = stepRL (RU (n + 3)) := by
  have hT : A381587_T (n + 4) = run_lengths_nat (A381587_T (n + 3)).reverse ++ A381587_T (n + 3) :=
    rfl
  rw [RU, hT, List.reverse_append, runsOf_append]
  rw [RU, stepRL]
  congr 1
  -- runsOf (reverse (run_lengths_nat (reverse (T (n+3))))) = (runsOf ((RU (n+3)).map Prod.snd)).reverse
  rw [runsOf_reverse, run_lengths_nat_eq]

/-! ## PHASE 1 infrastructure: additivity of weighted/count sums -/

/-- decode distributes over `mergeConcat`. -/
theorem decode_mergeConcat (A B : List (ℕ × ℕ)) :
    decode (mergeConcat A B) = decode A ++ decode B := by
  induction A with
  | nil => simp [mergeConcat, decode]
  | cons a A' ih =>
    obtain ⟨v, c⟩ := a
    cases A' with
    | nil =>
      cases B with
      | nil => simp [mergeConcat, decode]
      | cons b B' =>
        obtain ⟨v', c'⟩ := b
        rw [mergeConcat_single_cons]
        by_cases hv : v = v'
        · subst hv
          simp only [if_true, decode, List.replicate_add, List.append_nil, List.append_assoc]
        · simp only [if_neg hv, decode, List.append_nil, List.append_assoc]
    | cons a2 A'' =>
      obtain ⟨v2, c2⟩ := a2
      rw [mergeConcat_cons_cons]
      simp only [decode]
      rw [ih]
      simp only [decode, List.append_assoc]

/-- count (sum of run lengths) = length of decoded list. -/
def countRL (R : List (ℕ × ℕ)) : ℕ := (R.map Prod.snd).sum

theorem countRL_eq_decode_length (R : List (ℕ × ℕ)) : countRL R = (decode R).length := by
  induction R with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, c⟩ := p
    simp only [countRL, decode, List.map_cons, List.sum_cons, List.length_append,
      List.length_replicate] at *
    rw [ih]

theorem sumRL_mergeConcat (A B : List (ℕ × ℕ)) :
    sumRL (mergeConcat A B) = sumRL A + sumRL B := by
  rw [sumRL_eq_decode_sum, sumRL_eq_decode_sum, sumRL_eq_decode_sum, decode_mergeConcat,
    List.sum_append]

theorem countRL_mergeConcat (A B : List (ℕ × ℕ)) :
    countRL (mergeConcat A B) = countRL A + countRL B := by
  rw [countRL_eq_decode_length, countRL_eq_decode_length, countRL_eq_decode_length,
    decode_mergeConcat, List.length_append]

theorem sumRL_reverse (X : List (ℕ × ℕ)) : sumRL X.reverse = sumRL X := by
  simp only [sumRL, List.map_reverse, List.sum_reverse]

theorem countRL_reverse (X : List (ℕ × ℕ)) : countRL X.reverse = countRL X := by
  simp only [countRL, List.map_reverse, List.sum_reverse]

theorem sumRL_runsOf (Y : List ℕ) : sumRL (runsOf Y) = Y.sum := by
  rw [sumRL_eq_decode_sum, decode_runsOf]

theorem countRL_runsOf (Y : List ℕ) : countRL (runsOf Y) = Y.length := by
  rw [countRL_eq_decode_length, decode_runsOf]

/-! ## PHASE 1: the count functions of `n` and their easy recurrences -/

/-- `RU` step for all `n ≥ 3`. -/
theorem RU_step (n : ℕ) (hn : 3 ≤ n) : RU (n + 1) = stepRL (RU n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact RU_succ m

/-- `Sf n = A381358 n = sum of the row`. -/
def Sf (n : ℕ) : ℕ := sumRL (RU n)
/-- `Lf n = length of `U_n` (= number of cells in the row). -/
def Lf (n : ℕ) : ℕ := countRL (RU n)
/-- `Rf n = number of runs in `U_n`. -/
def Rf (n : ℕ) : ℕ := (RU n).length

theorem Sf_eq (n : ℕ) : Sf n = A381358 n := (A381358_eq_sumRL n).symm

/-- `S(n+1) = S(n) + L(n)`. -/
theorem Sf_rec (n : ℕ) (hn : 3 ≤ n) : Sf (n + 1) = Sf n + Lf n := by
  rw [Sf, RU_step n hn, stepRL, sumRL_mergeConcat, sumRL_reverse, sumRL_runsOf]
  rw [Sf, Lf, countRL]

/-- `L(n+1) = L(n) + R(n)`. -/
theorem Lf_rec (n : ℕ) (hn : 3 ≤ n) : Lf (n + 1) = Lf n + Rf n := by
  rw [Lf, RU_step n hn, stepRL, countRL_mergeConcat, countRL_reverse, countRL_runsOf]
  rw [Lf, Rf, List.length_map]

/-! ## PHASE 2: asymptotics -/

open Filter Topology

/-- The growth rate `ρ`: the real root in `(1,2)` of `x^4 (x-1)^3 = 1`. -/
theorem exists_rho : ∃ ρ : ℝ, 1 < ρ ∧ ρ < 2 ∧ ρ ^ 4 * (ρ - 1) ^ 3 = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 4 * (x - 1) ^ 3) (Set.Icc 1 2) :=
    (Continuous.continuousOn (by fun_prop))
  have h1 : (fun x : ℝ => x ^ 4 * (x - 1) ^ 3) 1 = 0 := by norm_num
  have h2 : (fun x : ℝ => x ^ 4 * (x - 1) ^ 3) 2 = 16 := by norm_num
  have hmem : (1 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 4 * (x - 1) ^ 3) 1)
      ((fun x : ℝ => x ^ 4 * (x - 1) ^ 3) 2) := by rw [h1, h2]; constructor <;> norm_num
  obtain ⟨ρ, hρmem, hρ⟩ := intermediate_value_Icc (by norm_num) hcont hmem
  obtain ⟨hρ1, hρ2⟩ := hρmem
  refine ⟨ρ, ?_, ?_, hρ⟩
  · rcases lt_or_eq_of_le hρ1 with h | h
    · exact h
    · exfalso; rw [← h] at hρ; norm_num at hρ
  · rcases lt_or_eq_of_le hρ2 with h | h
    · exact h
    · exfalso; rw [h] at hρ; norm_num at hρ

/-- Left-eigenvector potential for the (k,q,p) system. -/
noncomputable def Psi (k q p : ℕ → ℕ) (ρ : ℝ) (n : ℕ) : ℝ :=
  (ρ - 1) ^ 2 * k (n + 4) + (ρ - 1) * q (n + 4) + p (n + 4)
  + (ρ - 1) ^ 3 * ((k (n + 3) : ℝ) + ρ * k (n + 2) + ρ ^ 2 * k (n + 1) + ρ ^ 3 * k n)

theorem Psi_step (k q p : ℕ → ℕ) (ρ : ℝ) (hρe : ρ ^ 4 * (ρ - 1) ^ 3 = 1) (N : ℕ)
    (hk : ∀ n ≥ N, k (n + 1) = k n + q n)
    (hq : ∀ n ≥ N, q (n + 1) = q n + p n)
    (hp : ∀ n ≥ N, p (n + 5) = p (n + 4) + k n) :
    ∀ n ≥ N, Psi k q p ρ (n + 1) = ρ * Psi k q p ρ n := by
  intro n hn
  have e1 := hk (n + 4) (by omega)
  have e2 := hq (n + 4) (by omega)
  have e3 := hp n hn
  simp only [Psi]
  have e1' : ((k (n + 5) : ℝ)) = (k (n + 4) : ℝ) + (q (n + 4) : ℝ) := by exact_mod_cast e1
  have e2' : ((q (n + 5) : ℝ)) = (q (n + 4) : ℝ) + (p (n + 4) : ℝ) := by exact_mod_cast e2
  have e3' : ((p (n + 5) : ℝ)) = (p (n + 4) : ℝ) + (k n : ℝ) := by exact_mod_cast e3
  show (ρ - 1) ^ 2 * (k (n + 5) : ℝ) + (ρ - 1) * q (n + 5) + p (n + 5)
      + (ρ - 1) ^ 3 * ((k (n + 4) : ℝ) + ρ * k (n + 3) + ρ ^ 2 * k (n + 2) + ρ ^ 3 * k (n + 1))
    = ρ * ((ρ - 1) ^ 2 * (k (n + 4) : ℝ) + (ρ - 1) * q (n + 4) + p (n + 4)
      + (ρ - 1) ^ 3 * ((k (n + 3) : ℝ) + ρ * k (n + 2) + ρ ^ 2 * k (n + 1) + ρ ^ 3 * k n))
  rw [e1', e2', e3']
  linear_combination (-(k n : ℝ)) * hρe

/-- If `c ρ^n ≤ a n ≤ C ρ^n` for large `n` (with `c, ρ > 0`), then `(a n)^(1/n) → ρ`. -/
theorem tendsto_rpow_of_squeeze (a : ℕ → ℕ) (ρ c C : ℝ) (hρ : 0 < ρ) (hc : 0 < c) (N : ℕ)
    (hlb : ∀ n ≥ N, c * ρ ^ n ≤ (a n : ℝ)) (hub : ∀ n ≥ N, (a n : ℝ) ≤ C * ρ ^ n) :
    Tendsto (fun n => (a n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (nhds ρ) := by
  -- positivity of `a n` for large n
  have hapos : ∀ n ≥ N, 0 < (a n : ℝ) := by
    intro n hn
    exact lt_of_lt_of_le (by positivity) (hlb n hn)
  -- log (a n)/n squeezed
  have hg : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (nhds (Real.log ρ)) := by
    have hlow : Tendsto (fun n : ℕ => Real.log c / n + Real.log ρ) atTop (nhds (Real.log ρ)) := by
      have : Tendsto (fun n : ℕ => Real.log c / n) atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      simpa using this.add tendsto_const_nhds
    have hhigh : Tendsto (fun n : ℕ => Real.log C / n + Real.log ρ) atTop (nhds (Real.log ρ)) := by
      have : Tendsto (fun n : ℕ => Real.log C / n) atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      simpa using this.add tendsto_const_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
    · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
      have hnN : n ≥ N := le_of_max_le_left hn
      have hn1 : (1 : ℕ) ≤ n := le_of_max_le_right hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [div_add' _ _ _ (ne_of_gt hnpos), div_le_div_iff_of_pos_right hnpos]
      have h1 : Real.log c + (n : ℝ) * Real.log ρ ≤ Real.log (a n) := by
        have := hlb n hnN
        have hcast : Real.log (c * ρ ^ n) ≤ Real.log (a n) :=
          Real.log_le_log (by positivity) this
        rwa [Real.log_mul (ne_of_gt hc) (by positivity), Real.log_pow] at hcast
      linarith
    · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
      have hnN : n ≥ N := le_of_max_le_left hn
      have hn1 : (1 : ℕ) ≤ n := le_of_max_le_right hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [div_add' _ _ _ (ne_of_gt hnpos), div_le_div_iff_of_pos_right hnpos]
      have h2 : Real.log (a n) ≤ Real.log C + (n : ℝ) * Real.log ρ := by
        have := hub n hnN
        have hcast : Real.log (a n) ≤ Real.log (C * ρ ^ n) :=
          Real.log_le_log (hapos n hnN) this
        rwa [Real.log_mul (by
          rcases lt_or_ge 0 C with hC | hC
          · exact ne_of_gt hC
          · exfalso; have := hub n hnN
            have : (a n : ℝ) ≤ 0 := le_trans this (by nlinarith [pow_pos hρ n])
            linarith [hapos n hnN]) (by positivity), Real.log_pow] at hcast
      linarith
  -- compose with exp
  have hcomp : Tendsto (fun n : ℕ => Real.exp (Real.log (a n) / n)) atTop (nhds ρ) := by
    have := (Real.continuous_exp.tendsto (Real.log ρ)).comp hg
    rwa [Real.exp_log hρ] at this
  apply hcomp.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.rpow_def_of_pos (hapos n hn), mul_comm]
  congr 1
  rw [div_eq_inv_mul]

/-- Upper-bound helper: if `b(n+1)=b(n)+a(n)` and `a(n) ≤ A ρ^n`, then `b(n) ≤ C ρ^n`. -/
theorem geom_upper (a b : ℕ → ℕ) (ρ A : ℝ) (hρ : 1 < ρ) (N : ℕ)
    (hrec : ∀ n ≥ N, b (n + 1) = b n + a n)
    (ha : ∀ n ≥ N, (a n : ℝ) ≤ A * ρ ^ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ≥ N, (b n : ℝ) ≤ C * ρ ^ n := by
  have hρ0 : 0 < ρ := by linarith
  have hAnn : 0 ≤ A := by
    have := ha N (le_refl N)
    have h1 : (0:ℝ) ≤ (a N : ℝ) := by positivity
    have h2 : 0 < ρ ^ N := by positivity
    nlinarith [this, h1, h2]
  set C : ℝ := max (A / (ρ - 1)) ((b N : ℝ) / ρ ^ N) + 1 with hC
  have hCpos : 0 < C := by
    have : (0:ℝ) ≤ max (A / (ρ - 1)) ((b N : ℝ) / ρ ^ N) := by
      apply le_max_of_le_right; positivity
    rw [hC]; linarith
  have hCge1 : A / (ρ - 1) ≤ C := by rw [hC]; exact le_trans (le_max_left _ _) (by linarith)
  have hCgeBase : (b N : ℝ) / ρ ^ N ≤ C := by
    rw [hC]; exact le_trans (le_max_right _ _) (by linarith)
  refine ⟨C, hCpos, ?_⟩
  intro n hn
  induction n with
  | zero =>
    have hN0 : N = 0 := Nat.le_zero.mp hn
    subst hN0
    have hpow : ρ ^ 0 = 1 := by norm_num
    have := hCgeBase
    rw [hpow] at this ⊢; simpa using this
  | succ m ih =>
    rcases Nat.lt_or_ge N (m + 1) with hlt | hge
    · -- N ≤ m, use ih
      have hmN : N ≤ m := Nat.lt_succ_iff.mp hlt
      have ihm := ih hmN
      have hrecm := hrec m hmN
      have ham := ha m hmN
      have hcast : (b (m + 1) : ℝ) = (b m : ℝ) + (a m : ℝ) := by exact_mod_cast hrecm
      rw [hcast]
      have hpm : (0:ℝ) < ρ ^ m := by positivity
      calc (b m : ℝ) + (a m : ℝ) ≤ C * ρ ^ m + A * ρ ^ m := by linarith
        _ = (C + A) * ρ ^ m := by ring
        _ ≤ (C * ρ) * ρ ^ m := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hpm)
            have : A ≤ C * (ρ - 1) := by
              rw [div_le_iff₀ (by linarith)] at hCge1; linarith
            nlinarith
        _ = C * ρ ^ (m + 1) := by ring
    · -- m+1 ≤ N and N ≤ m+1, so N = m+1
      have : N = m + 1 := le_antisymm hn hge
      subst this
      have := hCgeBase
      rw [div_le_iff₀ (by positivity)] at this
      linarith

/-- A sequence satisfying `f(n+1)=ρ f(n)` for `n≥N` is `ρ^(n-N) f(N)`. -/
theorem geom_from_step (f : ℕ → ℝ) (ρ : ℝ) (N : ℕ) (h : ∀ n ≥ N, f (n + 1) = ρ * f n) :
    ∀ n ≥ N, f n = ρ ^ (n - N) * f N := by
  intro n hn
  induction n with
  | zero => simp [Nat.le_zero.mp hn]
  | succ m ih =>
    rcases Nat.lt_or_ge N (m + 1) with hlt | hge
    · have hmN : N ≤ m := Nat.lt_succ_iff.mp hlt
      rw [h m hmN, ih hmN]
      have : m + 1 - N = (m - N) + 1 := by omega
      rw [this, pow_succ]; ring
    · have : N = m + 1 := le_antisymm hn hge
      subst this; simp

/-- Monotonicity of `k` from relation A. -/
theorem k_mono {k q : ℕ → ℕ} {N : ℕ} (hA : ∀ n ≥ N, k (n + 1) = k n + q n) :
    ∀ m, N ≤ m → ∀ n, m ≤ n → k m ≤ k n := by
  intro m hm n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ j hj ih =>
    have hjN : N ≤ j := le_trans hm hj
    have := hA j hjN
    omega

/-- PHASE 2 master theorem: from the linear relations and side facts, the limit holds. -/
theorem phase2 (k q p L S R : ℕ → ℕ) (ρ : ℝ) (N : ℕ)
    (hρ1 : 1 < ρ) (hρe : ρ ^ 4 * (ρ - 1) ^ 3 = 1)
    (hA : ∀ n ≥ N, k (n + 1) = k n + q n)
    (hB : ∀ n ≥ N, q (n + 1) = q n + p n)
    (hC : ∀ n ≥ N, p (n + 5) = p (n + 4) + k n)
    (hqk : ∀ n, q n ≤ k n) (hpk : ∀ n, p n ≤ k n)
    (hRlb : ∀ n, k n ≤ R n) (hRub : ∀ n, R n ≤ 2 * k n)
    (hLrec : ∀ n ≥ N, L (n + 1) = L n + R n)
    (hSrec : ∀ n ≥ N, S (n + 1) = S n + L n)
    (hbase : 0 < k N) :
    Filter.Tendsto (fun n => (S n : ℝ) ^ ((n : ℝ)⁻¹)) Filter.atTop (nhds ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have hρm1 : 0 < ρ - 1 := by linarith
  -- monotonicity of k
  have hkmono := k_mono hA
  -- ψ evolves geometrically
  set ψ : ℕ → ℝ := Psi k q p ρ with hψdef
  have hψstep : ∀ n ≥ N, ψ (n + 1) = ρ * ψ n := Psi_step k q p ρ hρe N hA hB hC
  have hψgeo : ∀ n ≥ N, ψ n = ρ ^ (n - N) * ψ N := geom_from_step ψ ρ N hψstep
  -- ψ N > 0
  have hkN4 : 0 < k (N + 4) := lt_of_lt_of_le hbase (hkmono N (le_refl N) (N + 4) (by omega))
  have hψNpos : 0 < ψ N := by
    rw [hψdef, Psi]
    have h1 : (0:ℝ) < (ρ - 1) ^ 2 * (k (N + 4) : ℝ) := by
      have : (0:ℝ) < (k (N+4):ℝ) := by exact_mod_cast hkN4
      positivity
    have h2 : (0:ℝ) ≤ (ρ - 1) * (q (N+4):ℝ) := by positivity
    have h3 : (0:ℝ) ≤ (p (N+4):ℝ) := by positivity
    have h4 : (0:ℝ) ≤ (ρ-1)^3 * ((k (N+3):ℝ) + ρ * k (N+2) + ρ^2 * k (N+1) + ρ^3 * k N) := by
      positivity
    linarith
  -- key inequalities for ψ in terms of k(n+4)
  have hψlb_k : ∀ n ≥ N, (ρ - 1) ^ 2 * (k (n + 4) : ℝ) ≤ ψ n := by
    intro n hn
    rw [hψdef, Psi]
    have h2 : (0:ℝ) ≤ (ρ - 1) * (q (n+4):ℝ) := by positivity
    have h3 : (0:ℝ) ≤ (p (n+4):ℝ) := by positivity
    have h4 : (0:ℝ) ≤ (ρ-1)^3 * ((k (n+3):ℝ) + ρ * k (n+2) + ρ^2 * k (n+1) + ρ^3 * k n) := by
      positivity
    linarith
  set D : ℝ := (ρ-1)^2 + (ρ-1) + 1 + (ρ-1)^3 * (1 + ρ + ρ^2 + ρ^3) with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hψub_k : ∀ n ≥ N, ψ n ≤ D * (k (n + 4) : ℝ) := by
    intro n hn
    have m0 : (k (n+3):ℝ) ≤ (k (n+4):ℝ) := by
      have := hkmono (n+3) (by omega) (n+4) (by omega); exact_mod_cast this
    have m1 : (k (n+2):ℝ) ≤ (k (n+4):ℝ) := by
      have := hkmono (n+2) (by omega) (n+4) (by omega); exact_mod_cast this
    have m2 : (k (n+1):ℝ) ≤ (k (n+4):ℝ) := by
      have := hkmono (n+1) (by omega) (n+4) (by omega); exact_mod_cast this
    have m3 : (k n:ℝ) ≤ (k (n+4):ℝ) := by
      have := hkmono n (by omega) (n+4) (by omega); exact_mod_cast this
    have hq : (q (n+4):ℝ) ≤ (k (n+4):ℝ) := by exact_mod_cast hqk (n+4)
    have hp : (p (n+4):ℝ) ≤ (k (n+4):ℝ) := by exact_mod_cast hpk (n+4)
    have a2 : ρ*(k (n+2):ℝ) ≤ ρ*(k (n+4):ℝ) := by
      apply mul_le_mul_of_nonneg_left m1 (le_of_lt hρ0)
    have a3 : ρ^2*(k (n+1):ℝ) ≤ ρ^2*(k (n+4):ℝ) := by
      apply mul_le_mul_of_nonneg_left m2 (by positivity)
    have a4 : ρ^3*(k n:ℝ) ≤ ρ^3*(k (n+4):ℝ) := by
      apply mul_le_mul_of_nonneg_left m3 (by positivity)
    have hsum : (k (n+3):ℝ) + ρ*(k (n+2):ℝ) + ρ^2*(k (n+1):ℝ) + ρ^3*(k n:ℝ)
        ≤ (1 + ρ + ρ^2 + ρ^3) * (k (n+4):ℝ) := by nlinarith [m0, a2, a3, a4]
    have t1 : (ρ-1)*(q (n+4):ℝ) ≤ (ρ-1)*(k (n+4):ℝ) := by
      apply mul_le_mul_of_nonneg_left hq (le_of_lt hρm1)
    have t3 : (ρ-1)^3 * ((k (n+3):ℝ) + ρ*(k (n+2):ℝ) + ρ^2*(k (n+1):ℝ) + ρ^3*(k n:ℝ))
        ≤ (ρ-1)^3 * ((1 + ρ + ρ^2 + ρ^3) * (k (n+4):ℝ)) := by
      apply mul_le_mul_of_nonneg_left hsum (by positivity)
    rw [hψdef, Psi, hD]
    nlinarith [t1, hp, t3]
  -- bounds on k(m) for m ≥ N+4
  set Ck : ℝ := ψ N / ((ρ-1)^2 * ρ ^ (N+4)) with hCk
  set ck : ℝ := ψ N / (D * ρ ^ (N+4)) with hck
  have hCkpos : 0 < Ck := by rw [hCk]; positivity
  have hckpos : 0 < ck := by rw [hck]; positivity
  have hne1 : ((ρ-1)^2 : ℝ) ≠ 0 := by positivity
  have hne2 : ((ρ:ℝ) ^ (N+4)) ≠ 0 := by positivity
  have hneD : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  have hk_ub : ∀ m ≥ N + 4, (k m : ℝ) ≤ Ck * ρ ^ m := by
    intro m hm
    have hn : m - 4 ≥ N := by omega
    have e1 := hψlb_k (m - 4) hn
    have e2 := hψgeo (m - 4) hn
    have hm4 : m - 4 + 4 = m := by omega
    rw [hm4, e2] at e1
    have hpoweq : (ρ:ℝ)^m = ρ^(m-4-N) * ρ^(N+4) := by rw [← pow_add]; congr 1; omega
    have hkey : ((ρ-1)^2 : ℝ) * (Ck * ρ^m) = ρ^(m-4-N) * ψ N := by
      rw [hCk, hpoweq]; field_simp
    rw [← hkey] at e1
    exact le_of_mul_le_mul_left e1 (by positivity)
  have hk_lb : ∀ m ≥ N + 4, ck * ρ ^ m ≤ (k m : ℝ) := by
    intro m hm
    have hn : m - 4 ≥ N := by omega
    have e1 := hψub_k (m - 4) hn
    have e2 := hψgeo (m - 4) hn
    have hm4 : m - 4 + 4 = m := by omega
    rw [hm4, e2] at e1
    have hpoweq : (ρ:ℝ)^m = ρ^(m-4-N) * ρ^(N+4) := by rw [← pow_add]; congr 1; omega
    have hkey : (D : ℝ) * (ck * ρ^m) = ρ^(m-4-N) * ψ N := by
      rw [hck, hpoweq]; field_simp
    rw [← hkey] at e1
    exact le_of_mul_le_mul_left e1 hDpos
  -- R bounds
  have hR_ub : ∀ m ≥ N + 4, (R m : ℝ) ≤ (2*Ck) * ρ ^ m := by
    intro m hm
    have hb : (R m : ℝ) ≤ 2 * (k m : ℝ) := by exact_mod_cast hRub m
    have := hk_ub m hm; nlinarith [this, hb]
  have hR_lb : ∀ m ≥ N + 4, ck * ρ ^ m ≤ (R m : ℝ) := by
    intro m hm
    have hb : (k m : ℝ) ≤ (R m : ℝ) := by exact_mod_cast hRlb m
    have := hk_lb m hm; nlinarith [this, hb]
  -- L upper via geom_upper
  obtain ⟨CL, hCLpos, hL_ub⟩ :=
    geom_upper R L ρ (2*Ck) hρ1 (N+4) (fun n hn => hLrec n (by omega)) hR_ub
  -- S upper via geom_upper
  obtain ⟨CS, hCSpos, hS_ub⟩ :=
    geom_upper L S ρ CL hρ1 (N+4) (fun n hn => hSrec n (by omega)) hL_ub
  -- division/power helper
  have rdiv : ∀ (a : ℝ) (d e : ℕ), d ≤ e → a / ρ^d * ρ^e = a * ρ^(e-d) := by
    intro a d e hde
    have hpe : (ρ:ℝ)^e = ρ^d * ρ^(e-d) := by rw [← pow_add]; congr 1; omega
    rw [hpe]; field_simp
  -- L lower: L m ≥ R (m-1) for m ≥ N+5
  have hL_lb : ∀ m ≥ N + 5, (ck/ρ) * ρ ^ m ≤ (L m : ℝ) := by
    intro m hm
    have hrec := hLrec (m-1) (by omega)
    have hm1 : m - 1 + 1 = m := by omega
    rw [hm1] at hrec
    have hcast : (L m : ℝ) = (L (m-1):ℝ) + (R (m-1):ℝ) := by exact_mod_cast hrec
    have hRlb := hR_lb (m-1) (by omega)
    have hLm1 : (0:ℝ) ≤ (L (m-1):ℝ) := by positivity
    have hconv : (ck/ρ) * ρ^m = ck * ρ^(m-1) := by
      have := rdiv ck 1 m (by omega)
      simpa [pow_one] using this
    rw [hcast, hconv]; linarith
  -- S lower: S m ≥ L (m-1) for m ≥ N+6
  have hS_lb : ∀ m ≥ N + 6, (ck/ρ^2) * ρ ^ m ≤ (S m : ℝ) := by
    intro m hm
    have hrec := hSrec (m-1) (by omega)
    have hm1 : m - 1 + 1 = m := by omega
    rw [hm1] at hrec
    have hcast : (S m : ℝ) = (S (m-1):ℝ) + (L (m-1):ℝ) := by exact_mod_cast hrec
    have hLlb := hL_lb (m-1) (by omega)
    have hSm1 : (0:ℝ) ≤ (S (m-1):ℝ) := by positivity
    have hconv : (ck/ρ^2) * ρ^m = (ck/ρ) * ρ^(m-1) := by
      have h1 := rdiv ck 2 m (by omega)
      have h2 := rdiv ck 1 (m-1) (by omega)
      have hee : m - 2 = (m-1) - 1 := by omega
      rw [h1, hee, ← h2, pow_one]
    rw [hcast, hconv]; linarith
  -- assemble squeeze
  apply tendsto_rpow_of_squeeze S ρ (ck/ρ^2) CS hρ0 (by positivity) (N+6)
  · intro n hn; exact hS_lb n hn
  · intro n hn; exact hS_ub n (by omega)


/-! ## rl-tower self-similarity (the hard core) -/

/-- `Uw n = reverse (T n)`, the reversed rows. `RU n = runsOf (Uw n)`. -/
def Uw (n : ℕ) : List ℕ := (A381587_T n).reverse

theorem RU_eq_runsOf (n : ℕ) : RU n = runsOf (Uw n) := rfl

/-- The construction at the `U`-level. -/
theorem Uw_succ (n : ℕ) (hn : 3 ≤ n) :
    Uw (n + 1) = Uw n ++ (run_lengths_nat (Uw n)).reverse := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  show (A381587_T (k + 3 + 1)).reverse
      = (A381587_T (k + 3)).reverse ++ (run_lengths_nat (A381587_T (k + 3)).reverse).reverse
  have : A381587_T (k + 3 + 1)
      = run_lengths_nat (A381587_T (k + 3)).reverse ++ A381587_T (k + 3) := rfl
  rw [this, List.reverse_append]

/-- Length of a merging concatenation (boundary values equal): one run is absorbed. -/
theorem length_mergeConcat_merge (A0 B' : List (ℕ × ℕ)) (v c c' : ℕ) :
    (mergeConcat (A0 ++ [(v, c)]) ((v, c') :: B')).length + 1
      = (A0 ++ [(v, c)]).length + ((v, c') :: B').length := by
  rw [mergeConcat_append_singleton_left, mergeConcat_single_cons, if_pos rfl]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- Length of a non-merging concatenation (boundary values differ): lengths add. -/
theorem length_mergeConcat_nomerge (A0 B : List (ℕ × ℕ)) (v c : ℕ)
    (hB : ∀ w, B.head? = some w → v ≠ w.1) :
    (mergeConcat (A0 ++ [(v, c)]) B).length
      = (A0 ++ [(v, c)]).length + B.length := by
  rw [mergeConcat_append_singleton_left]
  cases B with
  | nil => simp
  | cons w B' =>
    obtain ⟨v', c'⟩ := w
    have hne : v ≠ v' := hB (v', c') rfl
    rw [mergeConcat_single_cons, if_neg hne]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-! ### head / tail structure of `runsOf` -/

/-- If the first two symbols differ, the first run is a singleton. -/
theorem runsOf_cons_cons_ne {a b : ℕ} (rest : List ℕ) (hab : a ≠ b) :
    runsOf (b :: a :: rest) = (b, 1) :: runsOf (a :: rest) := by
  rw [runsOf_cons]
  obtain ⟨c, r, hr⟩ := runsOf_cons_head a rest
  rw [hr]
  simp only [prependRun]
  rw [if_neg (by exact fun h => hab (h.symm ▸ rfl))]

/-- `getLast?` of `runsOf` via reversal. -/
theorem runsOf_getLast? (l : List ℕ) :
    (runsOf l).getLast? = (runsOf l.reverse).head? := by
  rw [runsOf_reverse, List.head?_reverse]

/-- The last run of a word ending in `[a, b]` with `a ≠ b` is the singleton `(b,1)`. -/
theorem runsOf_getLast?_of_ne (p : List ℕ) (a b : ℕ) (hab : a ≠ b) :
    (runsOf (p ++ [a, b])).getLast? = some (b, 1) := by
  rw [runsOf_getLast?]
  have hrev : (p ++ [a, b]).reverse = b :: a :: p.reverse := by
    simp [List.reverse_append]
  rw [hrev, runsOf_cons_cons_ne p.reverse hab]
  rfl

/-- The last run's value equals the last symbol. -/
theorem runsOf_getLast?_value (p : List ℕ) (v : ℕ) :
    ∃ c, (runsOf (p ++ [v])).getLast? = some (v, c) := by
  rw [runsOf_getLast?]
  have hrev : (p ++ [v]).reverse = v :: p.reverse := by simp
  rw [hrev]
  obtain ⟨c, r, hr⟩ := runsOf_cons_head v p.reverse
  rw [hr]; exact ⟨c, rfl⟩

/-! ### prefix monotonicity and head/tail of `Uw` -/

theorem Uw_prefix_succ (n : ℕ) (hn : 3 ≤ n) : ∃ t, Uw (n + 1) = Uw n ++ t :=
  ⟨_, Uw_succ n hn⟩

/-- `Uw 6` concretely. -/
theorem Uw6 : Uw 6 = [2, 1, 1, 1, 3, 1] := by simp [Uw, A381587_T, run_lengths_nat]

/-- Every later row extends `Uw 6` as a prefix. -/
theorem Uw_prefix (n : ℕ) (hn : 6 ≤ n) : ∃ t, Uw n = Uw 6 ++ t := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ m hm ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨t', ht'⟩ := Uw_prefix_succ m (by omega)
    exact ⟨t ++ t', by rw [ht', ht, List.append_assoc]⟩

/-- Head of every row from `n ≥ 6`. -/
theorem Uw_head (n : ℕ) (hn : 6 ≤ n) : ∃ s, Uw n = 2 :: 1 :: 1 :: 1 :: 3 :: s := by
  obtain ⟨t, ht⟩ := Uw_prefix n hn
  exact ⟨1 :: t, by rw [ht, Uw6]; rfl⟩

/-- Runs of a word with the canonical head `2,1,1,1,3,…`. -/
theorem runsOf_head5 (rest : List ℕ) :
    runsOf (2 :: 1 :: 1 :: 1 :: 3 :: rest) = (2, 1) :: (1, 3) :: runsOf (3 :: rest) := by
  obtain ⟨d, r, hr⟩ := runsOf_cons_head 3 rest
  rw [runsOf_cons, runsOf_cons, runsOf_cons, runsOf_cons, hr]
  simp only [prependRun]
  norm_num

/-- The run-length word starts with `1, 3, …` for `n ≥ 6`. -/
theorem rl_Uw_head (n : ℕ) (hn : 6 ≤ n) :
    ∃ s, run_lengths_nat (Uw n) = 1 :: 3 :: s := by
  obtain ⟨rest, hrest⟩ := Uw_head n hn
  refine ⟨(runsOf (3 :: rest)).map Prod.snd, ?_⟩
  rw [run_lengths_nat_eq, hrest, runsOf_head5]
  rfl

/-- Every row from `n ≥ 6` ends in `[3, 1]`. -/
theorem Uw_tail (n : ℕ) (hn : 6 ≤ n) : ∃ p, Uw n = p ++ [3, 1] := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨[2, 1, 1, 1], by rw [Uw6]; rfl⟩
  | succ m hm ih =>
    obtain ⟨s, hs⟩ := rl_Uw_head m hm
    refine ⟨Uw m ++ s.reverse, ?_⟩
    rw [Uw_succ m (by omega), hs]
    have hrev : (1 :: 3 :: s).reverse = s.reverse ++ [3, 1] := by
      simp [List.reverse_cons]
    rw [hrev, List.append_assoc]

/-- decomposition from `getLast?`. -/
theorem eq_dropLast_append {α : Type*} (l : List α) (a : α) (h : l.getLast? = some a) :
    l = l.dropLast ++ [a] := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', a', rfl⟩
  · simp at h
  · have ha : a' = a := by simpa using h
    subst ha
    simp

/-- Length of a merging concatenation, stated via `getLast?` / `head?`. -/
theorem length_mergeConcat_merge' (A B : List (ℕ × ℕ)) (v ca cb : ℕ)
    (hA : A.getLast? = some (v, ca)) (hB : B.head? = some (v, cb)) :
    (mergeConcat A B).length + 1 = A.length + B.length := by
  have hAd : A = A.dropLast ++ [(v, ca)] := eq_dropLast_append A _ hA
  obtain ⟨B', hB'⟩ : ∃ B', B = (v, cb) :: B' := by
    cases B with
    | nil => simp at hB
    | cons x B' => rw [List.head?_cons, Option.some_inj] at hB; exact ⟨B', by rw [hB]⟩
  rw [hAd, hB']
  exact length_mergeConcat_merge A.dropLast B' v ca cb

/-! ### F1 : the level-0 `#runs` recurrence -/

/-- `a₂ n = #runs (rl (Uw n))`. -/
def a2 (n : ℕ) : ℕ := (runsOf (run_lengths_nat (Uw n))).length

/-- The last run of `Uw n` is the singleton `(1,1)`. -/
theorem A_last (n : ℕ) (hn : 6 ≤ n) : (runsOf (Uw n)).getLast? = some (1, 1) := by
  obtain ⟨p, hp⟩ := Uw_tail n hn
  rw [hp]; exact runsOf_getLast?_of_ne p 3 1 (by norm_num)

/-- The run-length word `rl (Uw n)` ends in `1`. -/
theorem rl_Uw_last (n : ℕ) (hn : 6 ≤ n) :
    ∃ q, run_lengths_nat (Uw n) = q ++ [1] := by
  have h := A_last n hn
  rw [run_lengths_nat_eq]
  rw [eq_dropLast_append _ _ h]
  exact ⟨(runsOf (Uw n)).dropLast.map Prod.snd, by simp⟩

/-- The last run of `rl (Uw n)` has value `1`. -/
theorem B_last (n : ℕ) (hn : 6 ≤ n) :
    ∃ c, (runsOf (run_lengths_nat (Uw n))).getLast? = some (1, c) := by
  obtain ⟨q, hq⟩ := rl_Uw_last n hn
  rw [hq]; exact runsOf_getLast?_value q 1

/-- `#runs ≤ length`. -/
theorem length_prependRun_le (h : ℕ) (R : List (ℕ × ℕ)) :
    (prependRun h R).length ≤ R.length + 1 := by
  cases R with
  | nil => simp [prependRun]
  | cons p rest =>
    obtain ⟨v, c⟩ := p
    simp only [prependRun]
    by_cases hv : h = v
    · rw [if_pos hv]; simp
    · rw [if_neg hv]; simp

theorem length_runsOf_le (l : List ℕ) : (runsOf l).length ≤ l.length := by
  induction l with
  | nil => simp [runsOf]
  | cons h t ih =>
    rw [runsOf_cons]
    calc (prependRun h (runsOf t)).length ≤ (runsOf t).length + 1 := length_prependRun_le h _
      _ ≤ t.length + 1 := by omega
      _ = (h :: t).length := by simp

/-- Run-length encoding only modifies the last run of `A` when appending `B`. -/
theorem rl_append_prefix (A B : List ℕ) :
    ∃ t, run_lengths_nat (A ++ B) = (run_lengths_nat A).dropLast ++ t := by
  rw [run_lengths_nat_eq, run_lengths_nat_eq, runsOf_append]
  by_cases hA : runsOf A = []
  · exact ⟨(runsOf B).map Prod.snd, by rw [hA]; simp⟩
  · have hg : runsOf A = (runsOf A).dropLast ++ [(runsOf A).getLast hA] :=
      (List.dropLast_append_getLast hA).symm
    refine ⟨(mergeConcat [(runsOf A).getLast hA] (runsOf B)).map Prod.snd, ?_⟩
    conv_lhs => rw [hg]
    rw [mergeConcat_append_singleton_left, List.map_append]
    congr 1
    rw [List.map_dropLast]

/-- Run-lengths of a concatenation whose boundary runs merge. -/
theorem rl_merge (P Q : List ℕ) (v cp cq : ℕ)
    (hP : (runsOf P).getLast? = some (v, cp)) (hQ : (runsOf Q).head? = some (v, cq)) :
    run_lengths_nat (P ++ Q) =
      (run_lengths_nat P).dropLast ++ (cp + cq) :: (run_lengths_nat Q).tail := by
  simp only [run_lengths_nat_eq]
  rw [runsOf_append]
  have hPd : runsOf P = (runsOf P).dropLast ++ [(v, cp)] := eq_dropLast_append _ _ hP
  obtain ⟨Q', hQ'⟩ : ∃ Q', runsOf Q = (v, cq) :: Q' := by
    cases hQR : runsOf Q with
    | nil => simp [hQR] at hQ
    | cons x Q' =>
      rw [hQR, List.head?_cons, Option.some_inj] at hQ
      exact ⟨Q', by rw [hQ]⟩
  conv_lhs => rw [hPd, hQ']
  rw [mergeConcat_append_singleton_left, mergeConcat_single_cons, if_pos rfl]
  rw [hQ']
  simp only [List.map_append, List.map_cons, List.tail_cons, List.map_dropLast]

theorem F1 (n : ℕ) (hn : 6 ≤ n) : Rf (n + 1) + 1 = Rf n + a2 n := by
  have hstep : RU (n + 1) = mergeConcat (runsOf (Uw n)) ((runsOf (run_lengths_nat (Uw n))).reverse) := by
    rw [RU_eq_runsOf, Uw_succ n (by omega), runsOf_append, runsOf_reverse]
  obtain ⟨cb, hcb⟩ := B_last n hn
  have hhead : ((runsOf (run_lengths_nat (Uw n))).reverse).head? = some (1, cb) := by
    rw [List.head?_reverse]; exact hcb
  have hmerge := length_mergeConcat_merge' (runsOf (Uw n))
    ((runsOf (run_lengths_nat (Uw n))).reverse) 1 1 cb (A_last n hn) hhead
  rw [List.length_reverse] at hmerge
  unfold Rf a2
  rw [hstep, RU_eq_runsOf]
  rw [hmerge]

/-! ### Well-formed run-lists and the `decode`/`runsOf` roundtrip -/

/-- `decode` distributes over append. -/
theorem decode_append (R S : List (ℕ × ℕ)) : decode (R ++ S) = decode R ++ decode S := by
  induction R with
  | nil => simp [decode]
  | cons p R' ih => obtain ⟨v, c⟩ := p; simp [decode, ih, List.append_assoc]

/-- well-formedness of a run-list: positive counts, distinct adjacent values. -/
def WF : List (ℕ × ℕ) → Prop
  | [] => True
  | (v, c) :: rest => 0 < c ∧ (∀ p, rest.head? = some p → v ≠ p.1) ∧ WF rest

theorem runsOf_replicate_append (v : ℕ) : ∀ (c : ℕ) (X : List ℕ), 0 < c →
    (∀ p, (runsOf X).head? = some p → v ≠ p.1) →
    runsOf (List.replicate c v ++ X) = (v, c) :: runsOf X := by
  intro c
  induction c with
  | zero => intro X h; omega
  | succ c ih =>
    intro X hpos hX
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · subst hc0
      rw [Nat.zero_add, List.replicate_one, List.singleton_append, runsOf_cons]
      cases hR : runsOf X with
      | nil => rfl
      | cons p rest =>
        obtain ⟨w, d⟩ := p
        have hvw : v ≠ w := hX (w, d) (by rw [hR]; rfl)
        rw [prependRun, if_neg hvw]
    · rw [List.replicate_succ, List.cons_append, runsOf_cons, ih X hcpos hX, prependRun,
        if_pos rfl]

/-- the roundtrip `runsOf ∘ decode = id` on well-formed run-lists. -/
theorem runsOf_decode (R : List (ℕ × ℕ)) (h : WF R) : runsOf (decode R) = R := by
  induction R with
  | nil => rfl
  | cons p R' ih =>
    obtain ⟨v, c⟩ := p
    obtain ⟨hc, hbd, hWF'⟩ := h
    have ih' := ih hWF'
    simp only [decode]
    rw [runsOf_replicate_append v c (decode R') hc, ih']
    intro q hq
    rw [ih'] at hq
    cases R' with
    | nil => simp at hq
    | cons p2 R'' =>
      obtain ⟨w, d⟩ := p2
      have := hbd (w, d) rfl
      rw [List.head?_cons, Option.some_inj] at hq; rw [← hq]; exact this

/-- `runsOf` always produces a well-formed run-list. -/
theorem WF_runsOf (l : List ℕ) : WF (runsOf l) := by
  induction l with
  | nil => exact True.intro
  | cons h t ih =>
    rw [runsOf_cons]
    cases hR : runsOf t with
    | nil => exact ⟨Nat.one_pos, by simp, True.intro⟩
    | cons p rest =>
      obtain ⟨v, c⟩ := p
      rw [hR] at ih
      simp only [prependRun]
      by_cases hv : h = v
      · subst hv
        rw [if_pos rfl]
        obtain ⟨_, hbd, hWF'⟩ := ih
        exact ⟨Nat.succ_pos c, hbd, hWF'⟩
      · rw [if_neg hv]
        refine ⟨Nat.one_pos, ?_, ih⟩
        intro q hq; rw [List.head?_cons, Option.some_inj] at hq; rw [← hq]; exact hv

/-- well-formedness is preserved by dropping the last run. -/
theorem WF_of_append_singleton : ∀ (R : List (ℕ × ℕ)) (a : ℕ × ℕ),
    WF (R ++ [a]) → WF R := by
  intro R a
  induction R with
  | nil => intro _; exact True.intro
  | cons p R' ih =>
    intro h
    obtain ⟨w, d⟩ := p
    rw [List.cons_append] at h
    obtain ⟨hd, hbd, hWF⟩ := h
    refine ⟨hd, ?_, ih hWF⟩
    intro q hq
    apply hbd q
    rw [List.head?_append, hq]; rfl

theorem WF_dropLast (R : List (ℕ × ℕ)) (h : WF R) : WF R.dropLast := by
  rcases List.eq_nil_or_concat R with rfl | ⟨R', a, rfl⟩
  · exact True.intro
  · simp only [List.concat_eq_append] at h ⊢
    rw [List.dropLast_concat]; exact WF_of_append_singleton R' a h

/-- changing the (positive) count of the last run preserves well-formedness. -/
theorem WF_changeLast : ∀ (R : List (ℕ × ℕ)) (v a b : ℕ), 0 < b →
    WF (R ++ [(v, a)]) → WF (R ++ [(v, b)]) := by
  intro R
  induction R with
  | nil => intro v a b hb h; exact ⟨hb, by simp, True.intro⟩
  | cons p R' ih =>
    intro v a b hb h
    obtain ⟨w, d⟩ := p
    rw [List.cons_append] at h ⊢
    obtain ⟨hd, hbd, hWF⟩ := h
    refine ⟨hd, ?_, ih v a b hb hWF⟩
    intro q hq
    cases R' with
    | nil =>
      rw [List.nil_append, List.head?_cons, Option.some_inj] at hq
      have hh := hbd (v, a) (by rw [List.nil_append, List.head?_cons])
      rw [← hq]; exact hh
    | cons p2 R'' =>
      rw [List.cons_append, List.head?_cons, Option.some_inj] at hq
      have hh := hbd p2 (by rw [List.cons_append, List.head?_cons])
      rw [← hq]; exact hh

/-- dropping the last symbol shortens the last run by one (count ≥ 2 case). -/
theorem runsOf_dropLast_ge (l : List ℕ) (v c : ℕ)
    (h : (runsOf l).getLast? = some (v, c + 2)) :
    runsOf l.dropLast = (runsOf l).dropLast ++ [(v, c + 1)] := by
  set R := runsOf l with hRdef
  have hRd : R = R.dropLast ++ [(v, c + 2)] := eq_dropLast_append R _ h
  have hl : l = decode R := (decode_runsOf l).symm
  have hldec : l = decode R.dropLast ++ List.replicate (c + 2) v := by
    rw [hl]; conv_lhs => rw [hRd]
    rw [decode_append]; simp [decode]
  have hdrop : l.dropLast = decode R.dropLast ++ List.replicate (c + 1) v := by
    rw [hldec, show c + 2 = (c + 1) + 1 from rfl, List.replicate_succ',
      ← List.append_assoc, List.dropLast_concat]
  rw [hdrop]
  have hWF : WF (R.dropLast ++ [(v, c + 1)]) := by
    apply WF_changeLast R.dropLast v (c + 2) (c + 1) (by omega)
    rw [← hRd]; exact WF_runsOf l
  have : decode R.dropLast ++ List.replicate (c + 1) v
      = decode (R.dropLast ++ [(v, c + 1)]) := by
    rw [decode_append]; simp [decode]
  rw [this, runsOf_decode _ hWF]

/-- dropping the last symbol removes the last run entirely (count = 1 case). -/
theorem runsOf_dropLast_one (l : List ℕ) (v : ℕ)
    (h : (runsOf l).getLast? = some (v, 1)) :
    runsOf l.dropLast = (runsOf l).dropLast := by
  set R := runsOf l with hRdef
  have hRd : R = R.dropLast ++ [(v, 1)] := eq_dropLast_append R _ h
  have hl : l = decode R := (decode_runsOf l).symm
  have hdrop : l.dropLast = decode R.dropLast := by
    rw [hl]; conv_lhs => rw [hRd]
    rw [decode_append]; simp [decode]
  rw [hdrop]
  have hWF : WF R.dropLast := WF_dropLast R (by rw [hRdef]; exact WF_runsOf l)
  rw [runsOf_decode _ hWF]

/-! ### tower words and run-length helpers -/

/-- run-length reverses. -/
theorem rl_reverse (l : List ℕ) :
    run_lengths_nat l.reverse = (run_lengths_nat l).reverse := by
  rw [run_lengths_nat_eq, run_lengths_nat_eq, runsOf_reverse, List.map_reverse]

/-- `#runs = length of run-length word`. -/
theorem runsOf_length_eq (l : List ℕ) :
    (runsOf l).length = (run_lengths_nat l).length := by
  rw [run_lengths_nat_eq, List.length_map]

/-- merging concatenation, equational form. -/
theorem mergeConcat_merge_eq (X : List (ℕ × ℕ)) (v cp cq : ℕ) (Q : List (ℕ × ℕ)) :
    mergeConcat (X ++ [(v, cp)]) ((v, cq) :: Q) = X ++ (v, cp + cq) :: Q := by
  rw [mergeConcat_append_singleton_left, mergeConcat_single_cons, if_pos rfl]

/-- non-merging concatenation, equational form. -/
theorem mergeConcat_nomerge_eq (X : List (ℕ × ℕ)) (a b : ℕ × ℕ) (Q : List (ℕ × ℕ))
    (hne : a.1 ≠ b.1) :
    mergeConcat (X ++ [a]) (b :: Q) = X ++ a :: b :: Q := by
  obtain ⟨av, ac⟩ := a; obtain ⟨bv, bc⟩ := b
  rw [mergeConcat_append_singleton_left, mergeConcat_single_cons, if_neg hne]

/-- the reversed tower words. -/
def Yw (n : ℕ) : List ℕ := run_lengths_nat (Uw n)
def Zw (n : ℕ) : List ℕ := run_lengths_nat (Yw n)
def W3w (n : ℕ) : List ℕ := run_lengths_nat (Zw n)

/-- `a₃ n = #runs (rl² (Uw n))`. -/
def a3 (n : ℕ) : ℕ := (runsOf (Zw n)).length

theorem a2_eq (n : ℕ) : a2 n = (runsOf (Yw n)).length := rfl

/-- EQ-Y : the level-1 word recurrence. -/
theorem Yw_succ (n : ℕ) (hn : 6 ≤ n)
    (hTB : (runsOf (Yw n)).getLast? = some (1, 6)) :
    Yw (n + 1) = (Yw n).dropLast ++ 7 :: ((Zw n).dropLast).reverse := by
  have hU : Uw (n + 1) = Uw n ++ (Yw n).reverse := by
    rw [Uw_succ n (by omega)]; rfl
  have hQ : (runsOf ((Yw n).reverse)).head? = some (1, 6) := by
    rw [runsOf_reverse, List.head?_reverse]; exact hTB
  show run_lengths_nat (Uw (n + 1)) = _
  rw [hU, rl_merge (Uw n) ((Yw n).reverse) 1 1 6 (A_last n hn) hQ]
  have hZrev : run_lengths_nat ((Yw n).reverse) = (Zw n).reverse := by
    rw [rl_reverse]; rfl
  rw [hZrev, List.tail_reverse]
  rfl

/-- R-B : the level-1 run-list recurrence. -/
theorem B_succ (n : ℕ) (hn : 6 ≤ n)
    (hTB : (runsOf (Yw n)).getLast? = some (1, 6))
    (hTC : (runsOf (Zw n)).getLast? = some (6, 1))
    (hTC2 : ((runsOf (Zw n)).dropLast).getLast? = some (1, 3)) :
    runsOf (Yw (n + 1)) =
      (runsOf (Yw n)).dropLast ++ (1, 5) :: (7, 1) :: ((runsOf (Zw n)).dropLast).reverse := by
  rw [Yw_succ n hn hTB, runsOf_append]
  have h2a : runsOf ((Yw n).dropLast) = (runsOf (Yw n)).dropLast ++ [(1, 5)] :=
    runsOf_dropLast_ge (Yw n) 1 4 hTB
  have hZd : runsOf ((Zw n).dropLast) = (runsOf (Zw n)).dropLast :=
    runsOf_dropLast_one (Zw n) 6 hTC
  have hrev : runsOf (((Zw n).dropLast).reverse) = ((runsOf (Zw n)).dropLast).reverse := by
    rw [runsOf_reverse, hZd]
  have hhead : (((runsOf (Zw n)).dropLast).reverse).head? = some (1, 3) := by
    rw [List.head?_reverse]; exact hTC2
  obtain ⟨rest, hrest⟩ : ∃ rest, ((runsOf (Zw n)).dropLast).reverse = (1, 3) :: rest := by
    cases hc : ((runsOf (Zw n)).dropLast).reverse with
    | nil => rw [hc] at hhead; simp at hhead
    | cons x rest =>
      rw [hc, List.head?_cons, Option.some_inj] at hhead; exact ⟨rest, by rw [hhead]⟩
  have h2b : runsOf (7 :: ((Zw n).dropLast).reverse)
      = (7, 1) :: ((runsOf (Zw n)).dropLast).reverse := by
    rw [runsOf_cons, hrev, hrest]
    simp only [prependRun, if_neg (show (7 : ℕ) ≠ 1 by norm_num)]
  rw [h2a, h2b, mergeConcat_nomerge_eq _ (1, 5) (7, 1) _ (by norm_num)]

/-- F2 : the level-2 length recurrence `a₂(n+1) = a₂ n + a₃ n`. -/
theorem F2 (n : ℕ) (hn : 6 ≤ n)
    (hTB : (runsOf (Yw n)).getLast? = some (1, 6))
    (hTC : (runsOf (Zw n)).getLast? = some (6, 1))
    (hTC2 : ((runsOf (Zw n)).dropLast).getLast? = some (1, 3)) :
    a2 (n + 1) = a2 n + a3 n := by
  have hb := B_succ n hn hTB hTC hTC2
  have h2pos : 1 ≤ (runsOf (Yw n)).length := by
    rcases List.eq_nil_or_concat (runsOf (Yw n)) with h | ⟨l', a, h⟩
    · rw [h] at hTB; simp at hTB
    · rw [h]; simp [List.concat_eq_append]
  have h3pos : 1 ≤ (runsOf (Zw n)).length := by
    rcases List.eq_nil_or_concat (runsOf (Zw n)) with h | ⟨l', a, h⟩
    · rw [h] at hTC; simp at hTC
    · rw [h]; simp [List.concat_eq_append]
  rw [a2_eq (n + 1), hb, a2_eq n, a3]
  simp only [List.length_append, List.length_cons, List.length_reverse, List.length_dropLast]
  omega

/-- EQ-Z : the level-2 word recurrence, obtained from `B_succ` by reading off counts. -/
theorem Zw_succ (n : ℕ) (hn : 6 ≤ n)
    (hTB : (runsOf (Yw n)).getLast? = some (1, 6))
    (hTC : (runsOf (Zw n)).getLast? = some (6, 1))
    (hTC2 : ((runsOf (Zw n)).dropLast).getLast? = some (1, 3)) :
    Zw (n + 1) = (Zw n).dropLast ++ 5 :: 1 :: ((W3w n).dropLast).reverse := by
  have hb := B_succ n hn hTB hTC hTC2
  show run_lengths_nat (Yw (n + 1)) = _
  rw [run_lengths_nat_eq, hb]
  simp only [List.map_append, List.map_cons, List.map_reverse, List.map_dropLast]
  rw [← run_lengths_nat_eq (Yw n), ← run_lengths_nat_eq (Zw n)]
  rfl

/-! ### strengthened head/tail of `Uw` and the level-3 tail facts -/

theorem Uw_head6 (n : ℕ) (hn : 6 ≤ n) : ∃ s, Uw n = 2 :: 1 :: 1 :: 1 :: 3 :: 1 :: s := by
  obtain ⟨t, ht⟩ := Uw_prefix n hn
  exact ⟨t, by rw [ht, Uw6]; rfl⟩

theorem rl_Uw_head3 (n : ℕ) (hn : 6 ≤ n) :
    ∃ s, run_lengths_nat (Uw n) = 1 :: 3 :: 1 :: s := by
  obtain ⟨rest, hrest⟩ := Uw_head6 n hn
  refine ⟨(runsOf (1 :: rest)).map Prod.snd, ?_⟩
  rw [run_lengths_nat_eq, hrest, runsOf_head5, runsOf_cons_cons_ne rest (by norm_num)]
  rfl

theorem Uw_tail3 (n : ℕ) (hn : 6 ≤ n) : ∃ p, Uw n = p ++ [1, 3, 1] := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨[2, 1, 1], by rw [Uw6]; rfl⟩
  | succ m hm ih =>
    obtain ⟨s, hs⟩ := rl_Uw_head3 m hm
    refine ⟨Uw m ++ s.reverse, ?_⟩
    rw [Uw_succ m (by omega), hs]
    have hrev : (1 :: 3 :: 1 :: s).reverse = s.reverse ++ [1, 3, 1] := by
      simp [List.reverse_cons]
    rw [hrev, List.append_assoc]

/-- From `STAR(n)`, the level-3 word ends in `[1,3,1]`. -/
theorem W3w_tail (n : ℕ) (hn : 10 ≤ n) (hSTAR : W3w n = 6 :: (Uw (n - 4)).tail) :
    ∃ p, W3w n = p ++ [1, 3, 1] := by
  obtain ⟨q, hq⟩ := Uw_tail3 (n - 4) (by omega)
  obtain ⟨s, hs⟩ := Uw_head6 (n - 4) (by omega)
  refine ⟨6 :: q.tail, ?_⟩
  have htl : (Uw (n - 4)).tail = q.tail ++ [1, 3, 1] := by
    rw [hq]
    cases q with
    | nil => rw [hs] at hq; simp at hq
    | cons x q' => rfl
  rw [hSTAR, htl, List.cons_append]

/-- last two runs of the level-3 run-list. -/
theorem D_tail (n : ℕ) (hn : 10 ≤ n) (hSTAR : W3w n = 6 :: (Uw (n - 4)).tail) :
    (runsOf (W3w n)).getLast? = some (1, 1) ∧
    ((runsOf (W3w n)).dropLast).getLast? = some (3, 1) := by
  obtain ⟨p, hp⟩ := W3w_tail n hn hSTAR
  have d1 : (runsOf (W3w n)).getLast? = some (1, 1) := by
    rw [hp]
    have : p ++ [1, 3, 1] = (p ++ [1]) ++ [3, 1] := by simp
    rw [this]; exact runsOf_getLast?_of_ne (p ++ [1]) 3 1 (by norm_num)
  refine ⟨d1, ?_⟩
  rw [← runsOf_dropLast_one (W3w n) 1 d1, hp]
  have hd : (p ++ [1, 3, 1]).dropLast = p ++ [1, 3] := by simp
  rw [hd]; exact runsOf_getLast?_of_ne p 1 3 (by norm_num)

/-- non-merging concatenation via `getLast?` / `head?`. -/
theorem mergeConcat_nomerge_getLast (A B : List (ℕ × ℕ)) (a b : ℕ × ℕ)
    (ha : A.getLast? = some a) (hb : B.head? = some b) (hne : a.1 ≠ b.1) :
    mergeConcat A B = A ++ B := by
  have hAd : A = A.dropLast ++ [a] := eq_dropLast_append A _ ha
  obtain ⟨B', hB'⟩ : ∃ B', B = b :: B' := by
    cases B with
    | nil => simp at hb
    | cons x B' => rw [List.head?_cons, Option.some_inj] at hb; exact ⟨B', by rw [hb]⟩
  conv_lhs => rw [hAd, hB']
  rw [mergeConcat_nomerge_eq _ a b _ hne]
  conv_rhs => rw [hAd, hB']
  simp

/-- R-C : the level-2 run-list recurrence. -/
theorem C_succ (n : ℕ) (hn : 10 ≤ n)
    (hTB : (runsOf (Yw n)).getLast? = some (1, 6))
    (hTC : (runsOf (Zw n)).getLast? = some (6, 1))
    (hTC2 : ((runsOf (Zw n)).dropLast).getLast? = some (1, 3))
    (hSTAR : W3w n = 6 :: (Uw (n - 4)).tail) :
    runsOf (Zw (n + 1)) =
      (runsOf (Zw n)).dropLast ++ (5, 1) :: (1, 1) :: ((runsOf (W3w n)).dropLast).reverse := by
  obtain ⟨d1, d2⟩ := D_tail n hn hSTAR
  rw [Zw_succ n (by omega) hTB hTC hTC2, runsOf_append]
  -- runsOf ((Zw n).dropLast)
  have hZd : runsOf ((Zw n).dropLast) = (runsOf (Zw n)).dropLast :=
    runsOf_dropLast_one (Zw n) 6 hTC
  -- runsOf RW
  have hWd : runsOf ((W3w n).dropLast) = (runsOf (W3w n)).dropLast :=
    runsOf_dropLast_one (W3w n) 1 d1
  have hRW : runsOf (((W3w n).dropLast).reverse) = ((runsOf (W3w n)).dropLast).reverse := by
    rw [runsOf_reverse, hWd]
  -- head of RD
  have hhead : (((runsOf (W3w n)).dropLast).reverse).head? = some (3, 1) := by
    rw [List.head?_reverse]; exact d2
  obtain ⟨rd, hrd⟩ : ∃ rd, ((runsOf (W3w n)).dropLast).reverse = (3, 1) :: rd := by
    cases hc : ((runsOf (W3w n)).dropLast).reverse with
    | nil => rw [hc] at hhead; simp at hhead
    | cons x rd => rw [hc, List.head?_cons, Option.some_inj] at hhead; exact ⟨rd, by rw [hhead]⟩
  have hsb : runsOf (5 :: 1 :: ((W3w n).dropLast).reverse)
      = (5, 1) :: (1, 1) :: ((runsOf (W3w n)).dropLast).reverse := by
    rw [runsOf_cons, runsOf_cons, hRW, hrd]
    simp only [prependRun, if_neg (show (1 : ℕ) ≠ 3 by norm_num),
      if_neg (show (5 : ℕ) ≠ 1 by norm_num)]
  rw [hZd, hsb]
  exact mergeConcat_nomerge_getLast _ _ (1, 3) (5, 1) hTC2 (by rw [List.head?_cons]) (by norm_num)

/-! ### the level-3 self-reading step and `STAR` -/

theorem reverse_cons_getLast {α : Type*} (l : List α) (x : α) (h : l.getLast? = some x) :
    l.reverse = x :: l.dropLast.reverse := by
  conv_lhs => rw [eq_dropLast_append l x h]
  rw [List.reverse_append]; rfl

/-- `rl (a :: x) = 1 :: rl x` when `a` differs from the head of `x`. -/
theorem rl_cons_of_head_ne (a h : ℕ) (x : List ℕ) (hx : x.head? = some h) (ha : a ≠ h) :
    run_lengths_nat (a :: x) = 1 :: run_lengths_nat x := by
  obtain ⟨x', rfl⟩ : ∃ x', x = h :: x' := by
    cases x with
    | nil => simp at hx
    | cons y x' => rw [List.head?_cons, Option.some_inj] at hx; exact ⟨x', by rw [hx]⟩
  rw [run_lengths_nat_eq, run_lengths_nat_eq, runsOf_cons]
  obtain ⟨c, rest, hcr⟩ := runsOf_cons_head h x'
  rw [hcr, prependRun, if_neg ha]
  rfl

/-- EQ-W3 : the level-3 word satisfies the self-reading step. -/
theorem W3w_succ_step (n : ℕ) (hn : 10 ≤ n)
    (hTB : (runsOf (Yw n)).getLast? = some (1, 6))
    (hTC : (runsOf (Zw n)).getLast? = some (6, 1))
    (hTC2 : ((runsOf (Zw n)).dropLast).getLast? = some (1, 3))
    (hSTAR : W3w n = 6 :: (Uw (n - 4)).tail) :
    W3w (n + 1) = W3w n ++ (run_lengths_nat (W3w n)).reverse := by
  have hc := C_succ n hn hTB hTC hTC2 hSTAR
  have hexp : W3w (n + 1)
      = (W3w n).dropLast ++ 1 :: 1 :: ((run_lengths_nat (W3w n)).dropLast).reverse := by
    show run_lengths_nat (Zw (n + 1)) = _
    rw [run_lengths_nat_eq, hc]
    simp only [List.map_append, List.map_cons, List.map_reverse, List.map_dropLast]
    rw [← run_lengths_nat_eq (Zw n), ← run_lengths_nat_eq (W3w n)]
    rfl
  obtain ⟨d1, d2⟩ := D_tail n hn hSTAR
  obtain ⟨p, hp⟩ := W3w_tail n hn hSTAR
  have hW1 : (W3w n).getLast? = some 1 := by rw [hp]; simp
  have hrl1 : (run_lengths_nat (W3w n)).getLast? = some 1 := by
    rw [run_lengths_nat_eq, List.getLast?_map, d1]; rfl
  rw [hexp]
  conv_rhs => rw [reverse_cons_getLast _ 1 hrl1]
  conv_rhs => lhs; rw [eq_dropLast_append (W3w n) 1 hW1]
  rw [List.append_assoc]
  rfl

/-- STAR maintenance : `W3w (n+1) = 6 :: tail (Uw (n+1-4))`. -/
theorem STAR_succ (n : ℕ) (hn : 10 ≤ n)
    (hTB : (runsOf (Yw n)).getLast? = some (1, 6))
    (hTC : (runsOf (Zw n)).getLast? = some (6, 1))
    (hTC2 : ((runsOf (Zw n)).dropLast).getLast? = some (1, 3))
    (hSTAR : W3w n = 6 :: (Uw (n - 4)).tail) :
    W3w (n + 1) = 6 :: (Uw (n + 1 - 4)).tail := by
  have hstep := W3w_succ_step n hn hTB hTC hTC2 hSTAR
  obtain ⟨s, hs⟩ := Uw_head6 (n - 4) (by omega)
  have hUcons : Uw (n - 4) = 2 :: (Uw (n - 4)).tail := by rw [hs]; rfl
  have htu : (Uw (n - 4)).tail.head? = some 1 := by rw [hs]; rfl
  have hrlW3 : run_lengths_nat (W3w n) = Yw (n - 4) := by
    rw [hSTAR, rl_cons_of_head_ne 6 1 _ htu (by norm_num)]
    show 1 :: run_lengths_nat ((Uw (n - 4)).tail) = run_lengths_nat (Uw (n - 4))
    conv_rhs => rw [hUcons]
    rw [rl_cons_of_head_ne 2 1 _ htu (by norm_num)]
  have hu : Uw (n - 3) = Uw (n - 4) ++ (Yw (n - 4)).reverse := by
    have h1 := Uw_succ (n - 4) (by omega)
    rw [show n - 4 + 1 = n - 3 from by omega] at h1
    rw [h1]; rfl
  have htail2 : (Uw (n - 4) ++ (Yw (n - 4)).reverse).tail
      = (Uw (n - 4)).tail ++ (Yw (n - 4)).reverse := by
    conv_lhs => rw [hUcons]
    rw [List.cons_append, List.tail_cons]
  rw [hstep, hrlW3, hSTAR, show n + 1 - 4 = n - 3 from by omega, hu, htail2,
    List.cons_append]

/-- runs of a word with head `a,1,1,1,3,…` for `a ≠ 1`. -/
theorem runsOf_a1113 (a : ℕ) (rest : List ℕ) (ha : a ≠ 1) :
    runsOf (a :: 1 :: 1 :: 1 :: 3 :: rest) = (a, 1) :: (1, 3) :: runsOf (3 :: rest) := by
  obtain ⟨d, r, hr⟩ := runsOf_cons_head 3 rest
  rw [runsOf_cons, runsOf_cons, runsOf_cons, runsOf_cons, hr]
  rw [prependRun, if_neg (show (1 : ℕ) ≠ 3 by norm_num)]
  rw [prependRun, if_pos rfl]
  rw [prependRun, if_pos rfl]
  rw [prependRun, if_neg ha, ← hr]

/-- head two runs of the level-3 run-list, from `STAR`. -/
theorem D_head (n : ℕ) (hn : 10 ≤ n) (hSTAR : W3w n = 6 :: (Uw (n - 4)).tail) :
    ∃ r, runsOf (W3w n) = (6, 1) :: (1, 3) :: r := by
  obtain ⟨s, hs⟩ := Uw_head6 (n - 4) (by omega)
  have hW : W3w n = 6 :: 1 :: 1 :: 1 :: 3 :: 1 :: s := by rw [hSTAR, hs]; rfl
  rw [hW, runsOf_a1113 6 (1 :: s) (by norm_num)]
  exact ⟨runsOf (3 :: 1 :: s), rfl⟩

theorem D_head3 (n : ℕ) (hn : 10 ≤ n) (hSTAR : W3w n = 6 :: (Uw (n - 4)).tail) :
    ∃ r, runsOf (W3w n) = (6, 1) :: (1, 3) :: (3, 1) :: r := by
  obtain ⟨s, hs⟩ := Uw_head6 (n - 4) (by omega)
  have hW : W3w n = 6 :: 1 :: 1 :: 1 :: 3 :: 1 :: s := by rw [hSTAR, hs]; rfl
  rw [hW, runsOf_a1113 6 (1 :: s) (by norm_num), runsOf_cons_cons_ne s (by norm_num)]
  exact ⟨runsOf (1 :: s), rfl⟩

theorem tail2_facts {α : Type*} (L : List α) (a b : α) (h : ∃ M, L = M ++ [a, b]) :
    L.getLast? = some b ∧ L.dropLast.getLast? = some a := by
  obtain ⟨M, hM⟩ := h
  subst hM
  refine ⟨?_, ?_⟩
  · rw [show M ++ [a, b] = (M ++ [a]) ++ [b] from by simp]; exact List.getLast?_concat
  · rw [show M ++ [a, b] = (M ++ [a]) ++ [b] from by simp, List.dropLast_concat]
    exact List.getLast?_concat

/-- The structural invariant maintained for `n ≥ 10`. -/
def Inv (n : ℕ) : Prop :=
  (runsOf (Yw n)).getLast? = some (1, 6) ∧
  (∃ M, runsOf (Zw n) = M ++ [(1, 3), (6, 1)]) ∧
  (∃ x r, runsOf (Zw n) = (1, 6) :: (3, 1) :: x :: r) ∧
  W3w n = 6 :: (Uw (n - 4)).tail

theorem Inv_succ (n : ℕ) (hn : 10 ≤ n) (h : Inv n) : Inv (n + 1) := by
  obtain ⟨hTB, hCtail, ⟨x, r, hHC2⟩, hSTAR⟩ := h
  obtain ⟨hTC, hTC2⟩ := tail2_facts _ (1, 3) (6, 1) hCtail
  -- C(n) drop-last head structure
  have hCdl : (runsOf (Zw n)).dropLast = (1, 6) :: (3, 1) :: (x :: r).dropLast := by
    rw [hHC2, List.dropLast_cons₂, List.dropLast_cons₂]
  -- (1) T_B (n+1)
  have hTBn1 : (runsOf (Yw (n + 1))).getLast? = some (1, 6) := by
    rw [B_succ n (by omega) hTB hTC hTC2]
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    rw [show ((1, 5) :: (7, 1) :: ((runsOf (Zw n)).dropLast).reverse)
          = [(1, 5), (7, 1)] ++ ((runsOf (Zw n)).dropLast).reverse from rfl]
    rw [List.getLast?_append_of_ne_nil _ (by rw [hCdl]; simp), List.getLast?_reverse, hCdl]
    rfl
  -- (2) C tail (n+1)
  obtain ⟨r3, hr3⟩ := D_head3 n hn hSTAR
  have hDdl : (runsOf (W3w n)).dropLast = (6, 1) :: (1, 3) :: ((3, 1) :: r3).dropLast := by
    rw [hr3, List.dropLast_cons₂, List.dropLast_cons₂]
  have hCtailn1 : ∃ M, runsOf (Zw (n + 1)) = M ++ [(1, 3), (6, 1)] := by
    have hc := C_succ n hn hTB hTC hTC2 hSTAR
    rw [hc, hDdl, show ((6, 1) :: (1, 3) :: ((3, 1) :: r3).dropLast).reverse
          = (((3, 1) :: r3).dropLast).reverse ++ [(1, 3), (6, 1)] from by simp [List.reverse_cons]]
    exact ⟨(runsOf (Zw n)).dropLast ++ (5, 1) :: (1, 1) :: (((3, 1) :: r3).dropLast).reverse,
      by simp [List.append_assoc]⟩
  -- (3) C head (n+1)
  have hHC2n1 : ∃ x' r', runsOf (Zw (n + 1)) = (1, 6) :: (3, 1) :: x' :: r' := by
    have hc := C_succ n hn hTB hTC hTC2 hSTAR
    rw [hc, hCdl]
    rw [List.cons_append, List.cons_append]
    cases hd : (x :: r).dropLast with
    | nil => exact ⟨(5, 1), (1, 1) :: ((runsOf (W3w n)).dropLast).reverse, by simp⟩
    | cons y ys =>
      refine ⟨y, ys ++ (5, 1) :: (1, 1) :: ((runsOf (W3w n)).dropLast).reverse, by simp⟩
  -- (4) STAR (n+1)
  have hSTARn1 := STAR_succ n hn hTB hTC hTC2 hSTAR
  exact ⟨hTBn1, hCtailn1, hHC2n1, hSTARn1⟩

/-! ### Base case and propagation of the invariant -/

theorem Inv_base : Inv 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Yw, Uw, A381587_T, run_lengths_nat, runsOf]
  · exact ⟨[(1,6),(3,1),(1,1),(5,1)], by simp [Zw, Yw, Uw, A381587_T, run_lengths_nat, runsOf]⟩
  · exact ⟨(1,1), [(5,1),(1,3),(6,1)], by simp [Zw, Yw, Uw, A381587_T, run_lengths_nat, runsOf]⟩
  · simp [W3w, Zw, Yw, Uw, A381587_T, run_lengths_nat]

theorem Inv_all (n : ℕ) (hn : 10 ≤ n) : Inv n := by
  induction n, hn using Nat.le_induction with
  | base => exact Inv_base
  | succ m hm ih => exact Inv_succ m hm ih

/-! ### Final numeric recurrences and assembly -/

theorem runsOf_length_pos (l : List ℕ) (h : l ≠ []) : 0 < (runsOf l).length := by
  cases l with
  | nil => simp at h
  | cons a t =>
    rw [runsOf_cons]
    cases runsOf t with
    | nil => simp [prependRun]
    | cons p rest =>
      obtain ⟨v, c⟩ := p
      simp only [prependRun]
      by_cases hv : a = v <;> simp [hv]

theorem Lf_eq_length (n : ℕ) : Lf n = (Uw n).length := by
  rw [Lf, RU_eq_runsOf, countRL_runsOf]

/-- `a₂ n ≤ Rf n` for all `n`. -/
theorem a2_le_Rf (n : ℕ) : a2 n ≤ Rf n := by
  rw [a2_eq, Rf, RU_eq_runsOf]
  calc (runsOf (Yw n)).length ≤ (Yw n).length := length_runsOf_le _
    _ = (run_lengths_nat (Uw n)).length := by rw [Yw]
    _ = (runsOf (Uw n)).length := (runsOf_length_eq _).symm

/-- `a₃ n ≤ a₂ n` for all `n`. -/
theorem a3_le_a2 (n : ℕ) : a3 n ≤ a2 n := by
  rw [a3, a2_eq]
  calc (runsOf (Zw n)).length ≤ (Zw n).length := length_runsOf_le _
    _ = (run_lengths_nat (Yw n)).length := by rw [Zw]
    _ = (runsOf (Yw n)).length := (runsOf_length_eq _).symm

/-- `1 ≤ a₂ n` for `n ≥ 10` (from the invariant: `runsOf (Yw n)` is nonempty). -/
theorem a2_pos (n : ℕ) (hn : 10 ≤ n) : 1 ≤ a2 n := by
  have hTB := (Inv_all n hn).1
  rw [a2_eq]
  rcases List.eq_nil_or_concat (runsOf (Yw n)) with h | ⟨l', a, h⟩
  · rw [h] at hTB; simp at hTB
  · rw [h]; simp [List.concat_eq_append]

/-- `a₃ m = Lf (m - 4)` for `m ≥ 10`. -/
theorem a3_eq_Lf (m : ℕ) (hm : 10 ≤ m) : a3 m = Lf (m - 4) := by
  have hStar := (Inv_all m hm).2.2.2
  have hlen : a3 m = (W3w m).length := by rw [a3, runsOf_length_eq]; rfl
  obtain ⟨s, hs⟩ := Uw_head (m - 4) (by omega)
  rw [hlen, hStar, Lf_eq_length, hs]
  simp

open Filter Topology

/-- The conjecture: the limit `lim A381358(n)^(1/n)` exists. -/
theorem A381358_limit_exists' :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ)⁻¹))
      Filter.atTop (nhds L) := by
  obtain ⟨ρ, hρ1, hρ2, hρe⟩ := exists_rho
  refine ⟨ρ, ?_⟩
  have key := phase2 Rf (fun n => a2 n - 1) a3 Lf Sf Rf ρ 10 hρ1 hρe ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- convert `Sf` to `A381358`
    have hfun : (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ)⁻¹))
        = (fun n : ℕ => (Sf n : ℝ) ^ ((n : ℝ)⁻¹)) := by
      funext n; rw [Sf_eq]
    rw [hfun]; exact key
  · -- hA
    intro n hn
    dsimp only
    have hF1 := F1 n (by omega)
    have ha2 := a2_pos n hn
    omega
  · -- hB
    intro n hn
    dsimp only
    obtain ⟨hTB, hCtail, -, -⟩ := Inv_all n hn
    obtain ⟨hTC, hTC2⟩ := tail2_facts _ (1, 3) (6, 1) hCtail
    have hF2 := F2 n (by omega) hTB hTC hTC2
    have ha2 := a2_pos n hn
    omega
  · -- hC
    intro n hn
    have e1 : a3 (n + 5) = Lf (n + 1) := a3_eq_Lf (n + 5) (by omega)
    have e2 : a3 (n + 4) = Lf n := a3_eq_Lf (n + 4) (by omega)
    rw [e1, e2, Lf_rec n (by omega)]
  · -- hqk
    intro n
    dsimp only
    have := a2_le_Rf n; omega
  · -- hpk
    intro n
    have h1 := a3_le_a2 n
    have h2 := a2_le_Rf n
    omega
  · -- hRlb
    intro n; exact le_refl _
  · -- hRub
    intro n; omega
  · -- hLrec
    intro n hn; exact Lf_rec n (by omega)
  · -- hSrec
    intro n hn; exact Sf_rec n (by omega)
  · -- hbase
    show 0 < Rf 10
    rw [Rf, RU_eq_runsOf]
    apply runsOf_length_pos
    simp [Uw, A381587_T, run_lengths_nat]

end A381
