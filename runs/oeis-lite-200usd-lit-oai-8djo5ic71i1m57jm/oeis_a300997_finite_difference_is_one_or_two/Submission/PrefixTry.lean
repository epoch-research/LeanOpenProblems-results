import FormalConjectures.Util.ProblemImports
open List Nat

def halfC (m : ℕ) := (m+1)/2
def halfF (m : ℕ) := m/2
def trimZ (l : List ℕ) := (List.reverse l).dropWhile (fun x => x=0) |>.reverse
def caStep (config : List ℕ) : List ℕ :=
  let base_masses := config.map halfC ++ [0]
  let received_masses := 0 :: config.map halfF
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trimZ next_config_long

def mass (l : List ℕ) (i : ℕ) := l.getD i 0
def pref (l : List ℕ) (j : ℕ) := ∑ i ∈ Finset.range j, mass l i

lemma getD_append_zero (l : List ℕ) (i : ℕ) : (l ++ [0]).getD i 0 = l.getD i 0 := by
  by_cases h : i < l.length
  · rw [List.getD_append _ _ _ _ h]
  · have hle : l.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hle]
    rw [List.getD_eq_default _ _ hle]
    simp

lemma trimZ_getD (l : List ℕ) (i : ℕ) : (trimZ l).getD i 0 = l.getD i 0 := by
  unfold trimZ
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
      by_cases hx : x = 0
      · simp [List.reverse_append, hx]
        change (dropWhile (fun x => decide (x = 0)) xs.reverse).reverse.getD i 0 = (xs ++ [0]).getD i 0
        rw [ih, getD_append_zero]
      · simp [List.reverse_append, hx]

lemma half_sum (m : ℕ) : halfC m + halfF m = m := by
  unfold halfC halfF
  omega

lemma caStep_mass_zero (config : List ℕ) : mass (caStep config) 0 = halfC (mass config 0) := by
  unfold caStep mass
  rw [trimZ_getD]
  cases config <;> simp [halfC, halfF]

lemma caStep_mass_succ (config : List ℕ) (j : ℕ) :
    mass (caStep config) (j+1) = halfC (mass config (j+1)) + halfF (mass config j) := by
  unfold caStep mass
  rw [trimZ_getD]
  by_cases hj : j < config.length
  · by_cases hj1 : j+1 < config.length
    · simp [halfC, halfF, hj, hj1]
    · have hlen : config.length = j+1 := by omega
      simp [halfC, halfF, hlen]
  · have hlenj : config.length ≤ j := by omega
    have hlenj1 : config.length ≤ j+1 := by omega
    simp [halfC, halfF, hj, hlenj1]

lemma pref_succ (l : List ℕ) (j : ℕ) : pref l (j+1) = pref l j + mass l j := by
  unfold pref
  rw [Finset.sum_range_succ]

lemma pref_caStep_succ (config : List ℕ) (j : ℕ) :
    pref (caStep config) (j+1) = pref config j + halfC (mass config j) := by
  induction j with
  | zero =>
      rw [pref_succ]
      simp [pref, caStep_mass_zero]
  | succ j ih =>
      rw [pref_succ, ih, caStep_mass_succ]
      rw [pref_succ]
      have hs := half_sum (mass config j)
      omega

lemma pref_caStep_rec (config : List ℕ) (j : ℕ) :
    pref (caStep config) (j+1) = (pref config j + pref config (j+1) + 1) / 2 := by
  rw [pref_caStep_succ, pref_succ]
  unfold halfC
  omega

def S (N t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => caStep acc) [N]

def C : ℕ → ℕ → ℕ → ℕ
  | N, 0, j => if j = 0 then 0 else N
  | N, t+1, 0 => 0
  | N, t+1, j+1 => (C N t j + C N t (j+1) + 1) / 2

lemma S_succ (N t : ℕ) : S N (t+1) = caStep (S N t) := by
  unfold S
  rw [List.range_succ, List.foldl_append]
  simp

lemma pref_singleton (N j : ℕ) : pref [N] j = if j = 0 then 0 else N := by
  cases j with
  | zero => simp [pref]
  | succ j =>
      induction j with
      | zero => simp [pref, mass]
      | succ j ih =>
          rw [pref_succ, ih]
          simp [mass]

lemma pref_S_eq_C (N t j : ℕ) : pref (S N t) j = C N t j := by
  induction t generalizing j with
  | zero =>
      simp [S, C, pref_singleton]
  | succ t ih =>
      cases j with
      | zero => simp [pref, C]
      | succ j =>
          rw [S_succ, pref_caStep_rec, ih, ih]
          simp [C]

def D : ℕ → ℕ → ℕ → ℕ
  | N, 0, k => if k + 1 < N then 0 else k + 1
  | N, t+1, k => (D N t k + D N t (k+1)) / 2

lemma D_tail (N t k : ℕ) (h : N ≤ k+1) : D N t k = k+1 := by
  induction t generalizing k with
  | zero => simp [D, not_lt.mpr h]
  | succ t ih =>
      simp [D, ih k h, ih (k+1) (by omega)]
      omega

lemma D_bound2 (N t k : ℕ) : D N t k ≤ k+1 := by
  induction t generalizing k with
  | zero => simp [D]; split <;> omega
  | succ t ih =>
      simp [D]
      have h0:=ih k; have h1:=ih (k+1)
      rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
      omega

lemma ceil_sub_identity {N a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) :
    ((N - a) + (N - b) + 1) / 2 = N - (a + b) / 2 := by
  apply le_antisymm
  · rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
    have hq2 : 2 * ((a+b)/2) ≤ a+b := Nat.mul_div_le (a+b) 2
    omega
  · rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
    have hle : a+b ≤ 2 * ((a+b)/2) + 1 := by
      rw [← Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
    omega

lemma C_eq_D (N t j : ℕ) (hj : j < N) : C N t j = N - D N t (N - 1 - j) := by
  induction t generalizing j with
  | zero =>
      by_cases h0 : j = 0
      · subst h0
        have hDN : D N 0 (N-1) = N := by
          convert D_tail N 0 (N-1) (by omega) using 1 <;> omega
        simp [C, hDN]
      · have hlt : N - 1 - j + 1 < N := by omega
        simp [C, D, h0, hlt]
  | succ t ih =>
      cases j with
      | zero =>
          have ht : D N t (N - 1) = N := by
            convert D_tail N t (N-1) (by omega) using 1 <;> omega
          have ht2 : D N t (N - 1 + 1) = N+1 := by
            have harg : N - 1 + 1 = N := by omega
            rw [harg]
            exact D_tail N t N (by omega)
          have hDsucc : D N (t+1) (N-1) = N := by
            simp [D, ht, ht2]
            omega
          simp [C, hDsucc]
      | succ j =>
          have hj' : j < N := by omega
          have hj'' : j+1 < N := by omega
          rw [C, ih j hj', ih (j+1) hj'']
          have hidx : N - 1 - j = (N - 1 - (j+1)) + 1 := by omega
          rw [hidx]
          simp [D]
          let a := D N t (N - 1 - (j + 1))
          let b := D N t (N - 1 - (j + 1) + 1)
          have ha : a ≤ N := by
            have := D_bound2 N t (N - 1 - (j+1)); omega
          have hb : b ≤ N := by
            have := D_bound2 N t (N - 1 - (j+1)+1); omega
          simpa [a, b, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (ceil_sub_identity (N:=N) (a:=b) (b:=a) hb ha)

lemma D_spatial_mono2 (N t k : ℕ) : D N t k ≤ D N t (k+1) := by
  induction t generalizing k with
  | zero =>
      by_cases h : k + 1 < N
      · by_cases hh : k + 1 + 1 < N <;> simp [D, h, hh]
      · have hh : ¬ k + 1 + 1 < N := by omega
        simp [D, h, hh]
  | succ t ih =>
      simp [D]
      exact Nat.div_le_div_right (Nat.add_le_add (ih k) (ih (k+1)))

lemma D_gap_pos2 (N t k : ℕ) (h : 0 < D N t k) : D N t k + 1 ≤ D N t (k+1) := by
  -- copied shorter from Dscratch not now
  induction t generalizing k with
  | zero =>
      simp [D] at h ⊢
      by_cases hk : k + 1 < N
      · simp [hk] at h
      · by_cases hk2 : k + 1 + 1 < N
        · simp [hk, hk2]; omega
        · simp [hk, hk2]
  | succ t ih =>
      simp [D] at h ⊢
      let a := D N t k
      let b := D N t (k+1)
      let c := D N t (k+2)
      have hmono_ab : a ≤ b := D_spatial_mono2 N t k
      by_cases ha : 0 < a
      · have hb : 0 < b := lt_of_lt_of_le ha hmono_ab
        have gab : a + 1 ≤ b := ih k ha
        have gbc : b + 1 ≤ c := ih (k+1) hb
        change (a + b) / 2 < (b + c) / 2
        rw [Nat.lt_iff_add_one_le]
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        have hm : 2 * ((a + b) / 2) ≤ a + b := Nat.mul_div_le (a + b) 2
        omega
      · have ha0 : a = 0 := by omega
        have hb2 : 2 ≤ b := by
          have hsum : 2 ≤ a + b := by simpa [a,b] using h
          omega
        have hbpos : 0 < b := by omega
        have gbc : b + 1 ≤ c := ih (k+1) hbpos
        change (a + b) / 2 < (b + c) / 2
        rw [Nat.lt_iff_add_one_le]
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        have hm : 2 * ((a + b) / 2) ≤ a + b := Nat.mul_div_le (a + b) 2
        omega

lemma D_eq_of_D0_pos (N t k : ℕ) (h : 0 < D N t 0) : D N t k = k+1 := by
  induction k with
  | zero =>
      have hb := D_bound2 N t 0
      omega
  | succ k ih =>
      have hg := D_gap_pos2 N t k (by rw [ih]; omega)
      have hb := D_bound2 N t (k+1)
      omega

lemma stableC_iff_Dpos (N t : ℕ) (hN : 1 ≤ N) : C N t (N-1) = N-1 ↔ 0 < D N t 0 := by
  have hidx : N - 1 < N := by omega
  rw [C_eq_D N t (N-1) hidx]
  have hzero : N - 1 - (N - 1) = 0 := by omega
  simp [hzero]
  have hb := D_bound2 N t 0
  constructor <;> intro h <;> omega

lemma C_le_N (N t j : ℕ) : C N t j ≤ N := by
  induction t generalizing j with
  | zero =>
      simp [C]
      split <;> omega
  | succ t ih =>
      cases j with
      | zero => simp [C]
      | succ j =>
          simp [C]
          have h0 := ih j
          have h1 := ih (j+1)
          rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
          omega

lemma C_ge_j (N t j : ℕ) (hj : j ≤ N) : j ≤ C N t j := by
  induction t generalizing j with
  | zero =>
      simp [C]
      split <;> omega
  | succ t ih =>
      cases j with
      | zero => simp [C]
      | succ j =>
          simp [C]
          have h0 : j ≤ C N t j := ih j (by omega)
          have h1 : j+1 ≤ C N t (j+1) := ih (j+1) (by omega)
          rw [← Nat.succ_le_iff]
          rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
          omega

lemma C_tail (N t j : ℕ) (hj : N ≤ j) : C N t j = N := by
  induction t generalizing j with
  | zero =>
      cases j with
      | zero =>
          have : N = 0 := by omega
          simp [C, this]
      | succ j => simp [C]
  | succ t ih =>
      cases j with
      | zero =>
          have hN0 : N = 0 := by omega
          simp [C, hN0]
      | succ j =>
          simp [C]
          by_cases hjN : N ≤ j
          · rw [ih j hjN, ih (j+1) (by omega)]
            omega
          · have hjeq : j + 1 = N := by omega
            have h0ge : j ≤ C N t j := C_ge_j N t j (by omega)
            have h0le : C N t j ≤ N := C_le_N N t j
            rw [ih (j+1) (by omega)]
            omega

def NoTrail (l : List ℕ) : Prop := ∀ h : l ≠ [], l.getLast h ≠ 0

lemma trimZ_noTrail (l : List ℕ) : NoTrail (trimZ l) := by
  intro h
  unfold trimZ
  change ¬ ((List.rdropWhile (fun x : ℕ => decide (x = 0)) l).getLast h = 0)
  have hn := List.rdropWhile_last_not (p := fun x : ℕ => decide (x = 0)) (l := l) h
  simpa using hn

lemma caStep_noTrail (l : List ℕ) : NoTrail (caStep l) := by
  unfold caStep
  exact trimZ_noTrail _

lemma S_noTrail (N t : ℕ) (hN : 0 < N) : NoTrail (S N t) := by
  induction t with
  | zero =>
      intro h
      simp [S] at h ⊢
      omega
  | succ t ih =>
      rw [S_succ]
      exact caStep_noTrail _

lemma getD_replicate_one (N i : ℕ) : (List.replicate N 1).getD i 0 = if i < N then 1 else 0 := by
  by_cases h : i < N
  · simp [List.getD_replicate, h]
  · have hle : N ≤ i := by omega
    have hle' : (List.replicate N 1).length ≤ i := by simpa using hle
    rw [List.getD_eq_default _ _ hle']
    simp [h]

lemma list_eq_replicate_of_getD (l : List ℕ) (N : ℕ) (hNt : NoTrail l)
    (hget : ∀ i, l.getD i 0 = if i < N then 1 else 0) : l = List.replicate N 1 := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < N
  · have hli : i < l.length := by
      by_contra hnot
      have hle : l.length ≤ i := by omega
      have hz : l.getD i 0 = 0 := List.getD_eq_default _ _ hle
      rw [hget i] at hz
      simp [hi] at hz
    rw [List.getElem?_eq_getElem hli]
    have hrep : i < (List.replicate N 1).length := by simpa using hi
    rw [List.getElem?_eq_getElem hrep]
    have hv : l[i] = 1 := by
      have := hget i
      rw [List.getD_eq_getElem _ _ hli] at this
      simpa [hi] using this
    simp [hv]
  · have hlen : l.length ≤ N := by
      by_contra hnot
      have hlt : N < l.length := by omega
      let idx := l.length - 1
      have hidxlt : idx < l.length := by
        have : 0 < l.length := by omega
        omega
      have hidxge : N ≤ idx := by omega
      have hlast : l.getD idx 0 ≠ 0 := by
        have hne : l ≠ [] := by
          intro hempty
          simp [hempty] at hlt
        have hg := hNt hne
        rw [List.getLast_eq_getElem] at hg
        rw [List.getD_eq_getElem _ _ hidxlt]
        simpa [idx] using hg
      have hz : l.getD idx 0 = 0 := by
        rw [hget idx]
        simp [not_lt.mpr hidxge]
      exact hlast hz
    have hli : l.length ≤ i := by omega
    have hri : (List.replicate N 1).length ≤ i := by simpa using (not_lt.mp hi)
    rw [List.getElem?_eq_none_iff.2 hli, List.getElem?_eq_none_iff.2 hri]

lemma pref_replicate_one (N j : ℕ) (hj : j ≤ N) : pref (List.replicate N 1) j = j := by
  induction j with
  | zero => simp [pref]
  | succ j ih =>
      rw [pref_succ, ih (by omega)]
      simp [mass, getD_replicate_one, Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj]

lemma C_of_Dpos (N t j : ℕ) (h : 0 < D N t 0) : C N t j = if j < N then j else N := by
  by_cases hj : j < N
  · rw [C_eq_D N t j hj]
    rw [D_eq_of_D0_pos N t (N - 1 - j) h]
    simp [hj]
    omega
  · have hle : N ≤ j := by omega
    rw [C_tail N t j hle]
    simp [hj]

lemma S_eq_replicate_iff_Dpos (N t : ℕ) (hN : 1 ≤ N) :
    S N t = List.replicate N 1 ↔ 0 < D N t 0 := by
  constructor
  · intro hs
    have hp : C N t (N-1) = N-1 := by
      rw [← pref_S_eq_C, hs]
      exact pref_replicate_one N (N-1) (by omega)
    exact (stableC_iff_Dpos N t hN).mp hp
  · intro hd
    apply list_eq_replicate_of_getD
    · exact S_noTrail N t (by omega)
    · intro i
      change mass (S N t) i = if i < N then 1 else 0
      have hp1 : pref (S N t) (i+1) = if i+1 < N then i+1 else N := by
        rw [pref_S_eq_C, C_of_Dpos N t (i+1) hd]
      have hp0 : pref (S N t) i = if i < N then i else N := by
        rw [pref_S_eq_C, C_of_Dpos N t i hd]
      have hs := pref_succ (S N t) i
      rw [hp0, hp1] at hs
      by_cases hi : i < N
      · have hi1 : i+1 < N ∨ i+1 = N := by omega
        cases hi1 with
        | inl hlt => simp [hi, hlt] at hs ⊢; omega
        | inr heq => simp [hi, heq] at hs ⊢; omega
      · have hi1 : ¬ i+1 < N := by omega
        simp [hi, hi1] at hs ⊢
        exact hs

lemma div2_mono2 {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) : (a+b)/2 ≤ (c+d)/2 := by
  exact Nat.div_le_div_right (Nat.add_le_add h1 h2)

lemma D_time_mono2 (N t k : ℕ) : D N t k ≤ D N (t+1) k := by
  simp [D]
  have h := D_spatial_mono2 N t k
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
  omega

lemma D_time_mono_le2 (N k : ℕ) : Monotone (fun t => D N t k) :=
  monotone_nat_of_le_succ (fun t => D_time_mono2 N t k)

lemma D_shift_same2 (N t k : ℕ) : D N t k ≤ D (N+1) t (k+1) := by
  induction t generalizing k with
  | zero =>
      by_cases h : k + 1 < N
      · have hR : k + 1 + 1 < N + 1 := by omega
        simp [D, h, hR]
      · have hR : ¬ k + 1 + 1 < N + 1 := by omega
        simp [D, h, hR]
  | succ t ih =>
      simp [D]
      exact div2_mono2 (ih k) (ih (k+1))

lemma D_lower_same2 (N t k : ℕ) : D (N+1) (t+1) k ≤ D N t k := by
  induction t generalizing k with
  | zero =>
      by_cases h : k + 1 < N
      · have h1 : k + 1 < N + 1 := by omega
        have h2 : k + 1 + 1 < N + 1 := by omega
        simp [D, h, h1, h2]
      · have rhs : D N 0 k = k+1 := by simp [D, h]
        rw [rhs]
        simp [D]
        have hA : (if k < N then 0 else k + 1) ≤ k + 1 := by split <;> omega
        have hB : (if k + 1 < N then 0 else k + 1 + 1) ≤ k + 1 + 1 := by split <;> omega
        calc
          ((if k < N then 0 else k + 1) + if k + 1 < N then 0 else k + 1 + 1) / 2
              ≤ ((k+1) + (k+1+1)) / 2 := div2_mono2 hA hB
          _ ≤ k+1 := by
              rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
              omega
  | succ t ih =>
      simp [D]
      exact div2_mono2 (ih k) (ih (k+1))

lemma D_pos_shift_two2 (N t k : ℕ) (h : 0 < D N t k) : D N t k + 2 ≤ D (N+1) t (k+2) := by
  induction t generalizing k with
  | zero =>
      simp [D] at h ⊢
      by_cases hk : k + 1 < N
      · simp [hk] at h
      · have hk2 : ¬ k + 2 < N := by omega
        simp [hk, hk2]
  | succ t ih =>
      simp [D] at h ⊢
      let a := D N t k
      let b := D N t (k+1)
      let y0 := D (N+1) t (k+2)
      let y1 := D (N+1) t (k+3)
      have hmono_ab : a ≤ b := D_spatial_mono2 N t k
      by_cases ha : 0 < a
      · have hb : 0 < b := lt_of_lt_of_le ha hmono_ab
        have hy0 : a + 2 ≤ y0 := ih k ha
        have hy1 : b + 2 ≤ y1 := ih (k+1) hb
        change (a + b) / 2 + 2 ≤ (y0 + y1) / 2
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        have hm : 2 * ((a + b) / 2) ≤ a + b := Nat.mul_div_le (a + b) 2
        omega
      · have ha0 : a = 0 := by omega
        have hb2 : 2 ≤ b := by
          have hsum : 2 ≤ a + b := by simpa [a, b] using h
          omega
        have hbpos : 0 < b := by omega
        have hy0 : b ≤ y0 := D_shift_same2 N t (k+1)
        have hy1 : b + 2 ≤ y1 := ih (k+1) hbpos
        change (a + b) / 2 + 2 ≤ (y0 + y1) / 2
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        have hm : 2 * ((a + b) / 2) ≤ a + b := Nat.mul_div_le (a + b) 2
        omega

lemma D_upper_pos2 (N t : ℕ) (h : 0 < D N t 0) : 0 < D (N+1) (t+2) 0 := by
  have h1 : D N t 0 ≤ D (N+1) t 1 := D_shift_same2 N t 0
  have h2 : D N t 0 + 2 ≤ D (N+1) t 2 := D_pos_shift_two2 N t 0 h
  simp [D]
  have hz1 : 2 ≤ (D (N+1) t 1 + D (N+1) t 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
    omega
  omega

noncomputable def T (N : ℕ) : ℕ := sInf {t : ℕ | 0 < D N t 0}

lemma T_set_nonempty (N : ℕ) : ({t : ℕ | 0 < D N t 0} : Set ℕ).Nonempty := by
  induction N with
  | zero => refine ⟨0, by simp [D]⟩
  | succ N ih =>
      rcases ih with ⟨t, ht⟩
      exact ⟨t+2, by simpa [Nat.succ_eq_add_one, add_assoc] using D_upper_pos2 N t ht⟩

lemma T_mem (N : ℕ) : 0 < D N (T N) 0 := Nat.sInf_mem (T_set_nonempty N)
lemma T_le_of_pos {N t : ℕ} (h : 0 < D N t 0) : T N ≤ t := Nat.sInf_le h

lemma not_pos_before_T {N t : ℕ} (ht : t < T N) : D N t 0 = 0 := by
  by_contra h0
  have hp : 0 < D N t 0 := by omega
  have := T_le_of_pos (N:=N) (t:=t) hp
  omega

lemma T_succ_ge {N : ℕ} (hN : 1 ≤ N) : T N + 1 ≤ T (N+1) := by
  by_contra hnot
  have hle : T (N+1) ≤ T N := by omega
  have hp_at_s : 0 < D (N+1) (T N) 0 :=
    lt_of_lt_of_le (T_mem (N+1)) ((D_time_mono_le2 (N+1) 0) hle)
  cases hs : T N with
  | zero =>
      have hNle : N ≤ 1 := by
        have hpN := T_mem N
        rw [hs] at hpN
        by_contra hle'
        have hgt : 1 < N := by omega
        simp [D, hgt] at hpN
      have hNeq : N = 1 := by omega
      rw [hs] at hp_at_s
      subst hNeq
      simp [D] at hp_at_s
  | succ s =>
      rw [hs] at hp_at_s
      have hprev : D N s 0 = 0 := by
        apply not_pos_before_T
        omega
      have hle0 : D (N+1) (s+1) 0 ≤ D N s 0 := D_lower_same2 N s 0
      omega

lemma T_succ_le (N : ℕ) : T (N+1) ≤ T N + 2 :=
  T_le_of_pos (D_upper_pos2 N (T N) (T_mem N))

lemma T_finite_difference {N : ℕ} (hN : 1 ≤ N) : T (N+1) = T N + 1 ∨ T (N+1) = T N + 2 := by
  have h1 := T_succ_ge (N:=N) hN
  have h2 := T_succ_le N
  omega
