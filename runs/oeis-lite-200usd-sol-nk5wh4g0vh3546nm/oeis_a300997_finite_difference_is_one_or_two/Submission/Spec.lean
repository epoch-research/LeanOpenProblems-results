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

/-- Tail mass in the idealized infinite version of the automaton.  Index zero is
    the total mass, and index `k+1` is updated by averaging adjacent tmass masses. -/
def Q (N : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => N
  | 0, _ + 1 => 0
  | _ + 1, 0 => N
  | t + 1, k + 1 => (Q N t k + Q N t (k+1)) / 2

@[simp] theorem Q_zero (N t) : Q N t 0 = N := by cases t <;> rfl
@[simp] theorem Q_time_zero_succ (N k) : Q N 0 (k+1) = 0 := rfl
@[simp] theorem Q_succ_succ (N t k) :
    Q N (t+1) (k+1) = (Q N t k + Q N t (k+1))/2 := rfl

lemma Q_spatial_mono (N t k : ℕ) : Q N t (k+1) ≤ Q N t k := by
  induction t generalizing k with
  | zero => simp
  | succ t ih =>
    cases k with
    | zero =>
      simp only [Q_succ_succ, Q_zero, Nat.zero_add]
      rw [Nat.div_le_iff_le_mul (by omega)]
      have h : Q N t 1 ≤ N := by simpa using ih 0
      omega
    | succ k =>
      simp only [Q_succ_succ]
      exact Nat.div_le_div_right (Nat.add_le_add (ih k) (ih (k+1)))

lemma Q_le_total (N t k : ℕ) : Q N t k ≤ N := by
  exact (Nat.le_of_eq (Q_zero N t)).trans' (by
    induction k with
    | zero => simp
    | succ k ih => exact (Q_spatial_mono N t k).trans ih)

lemma Q_succ_monotone (N t k : ℕ) : Q N t k ≤ Q (N+1) t k := by
  induction t generalizing k with
  | zero => cases k <;> simp
  | succ t ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [Q_succ_succ]
      exact Nat.div_le_div_right (Nat.add_le_add (ih k) (ih (k+1)))

lemma Q_succ_index_lt (N t k : ℕ) (hN : 0 < N) : Q N t (k+1) < N := by
  induction t with
  | zero => simp [hN]
  | succ t ih =>
    simp only [Q_succ_succ]
    have hle := Q_le_total N t k
    have hlt := ih
    omega

/-- If some mass has reached level `k+1`, increasing the initial mass by one
moves at least two units of tmass mass one level to the left. -/
lemma Q_diagonal (N t k : ℕ) (h : 0 < Q N t (k+1)) :
    Q N t (k+1) + 2 ≤ Q (N+1) t k := by
  induction t generalizing k with
  | zero => simp at h
  | succ t ih =>
    cases k with
    | zero =>
      simp only [Q_succ_succ, Q_zero] at h ⊢
      have hN : 0 < N := by
        by_contra hn
        simp only [Nat.not_lt, Nat.le_zero] at hn
        subst N
        have hz : Q 0 t 1 = 0 := by
          have := Q_le_total 0 t 1
          omega
        simp [hz] at h
      have hb := Q_succ_index_lt N t 0 hN
      omega
    | succ k =>
      simp only [Q_succ_succ] at h ⊢
      have hab : 0 < Q N t (k+1) := by
        have hs := Q_spatial_mono N t (k+1)
        omega
      have hc := ih k hab
      by_cases hb : 0 < Q N t (k+2)
      · have hd := ih (k+1) hb
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
      · have hb0 : Q N t (k+2) = 0 := by omega
        have hd := Q_succ_monotone N t (k+1)
        simp only [hb0, Nat.add_zero, Nat.zero_add] at h ⊢
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega


def trim0 (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

def U (c : List ℕ) : List ℕ :=
  List.zipWith Nat.add (c.map (fun m => (m+1)/2) ++ [0])
    (0 :: c.map (fun m => m/2))

def step (c : List ℕ) : List ℕ := trim0 (U c)

def V (carry : ℕ) (c : List ℕ) : List ℕ :=
  List.zipWith Nat.add (c.map (fun m => (m+1)/2) ++ [0])
    (carry :: c.map (fun m => m/2))


lemma U_nil : U [] = [0] := by rfl
lemma U_cons (x : ℕ) (xs : List ℕ) : U (x::xs) = ((x+1)/2) :: V (x/2) xs := by rfl
lemma V_nil (carry : ℕ) : V carry [] = [carry] := by simp [V]
lemma V_cons (carry x : ℕ) (xs : List ℕ) :
    V carry (x::xs) = ((x+1)/2 + carry) :: V (x/2) xs := by rfl

lemma sum_V (carry : ℕ) (c : List ℕ) : (V carry c).sum = carry + c.sum := by
  induction c generalizing carry with
  | nil => simp [V]
  | cons x xs ih =>
    simp only [V_cons, List.sum_cons, ih]
    have hx : (x+1)/2 + x/2 = x := by omega
    omega

lemma drop_succ_V_eq_U (carry : ℕ) (c : List ℕ) (k : ℕ) :
    (V carry c).drop (k+1) = (U c).drop (k+1) := by
  cases c <;> simp [V, U]


def st (n t : ℕ) : List ℕ :=
  (List.range t).foldl (fun acc _ => step acc) [n]

def tmass (c : List ℕ) (k : ℕ) : ℕ := (c.drop k).sum

lemma tail_append_zero (l : List ℕ) (k : ℕ) : tmass (l ++ [0]) k = tmass l k := by
  induction l generalizing k with
  | nil => cases k <;> simp [tmass]
  | cons x xs ih =>
    cases k with
    | zero => simp [tmass]
    | succ k => simpa [tmass] using ih k


lemma tail_trim0 (l : List ℕ) (k : ℕ) : tmass (trim0 l) k = tmass l k := by
  induction l using List.reverseRecOn generalizing k with
  | nil => simp [trim0, tmass]
  | append_singleton l x ih =>
    by_cases hx : x = 0
    · subst x
      rw [show trim0 (l ++ [0]) = trim0 l by
        simp [trim0, List.rdropWhile, List.dropWhile]]
      rw [ih, tail_append_zero]
    · simp [trim0, List.rdropWhile, List.dropWhile, hx]

lemma sum_trim0 (l : List ℕ) : (trim0 l).sum = l.sum := by
  simpa [tmass] using tail_trim0 l 0


lemma tail_U_succ (c : List ℕ) (k : ℕ) :
    tmass (U c) (k+1) = (tmass c k + tmass c (k+1))/2 := by
  induction k generalizing c with
  | zero =>
    cases c with
    | nil => simp [tmass, U]
    | cons x xs =>
      simp only [tmass, U_cons, List.drop_succ_cons, List.drop_zero,
        List.sum_cons, sum_V]
      have hx : (x+1)/2 + x/2 = x := by omega
      omega
  | succ k ih =>
    cases c with
    | nil => simp [tmass, U]
    | cons x xs =>
      simp only [tmass, U_cons, List.drop_succ_cons]
      rw [drop_succ_V_eq_U]
      simpa [tmass] using ih xs

lemma tail_step_succ (c : List ℕ) (k : ℕ) :
    tmass (step c) (k+1) = (tmass c k + tmass c (k+1))/2 := by
  rw [step, tail_trim0, tail_U_succ]


lemma sum_U (c : List ℕ) : (U c).sum = c.sum := by
  cases c with
  | nil => simp [U]
  | cons x xs =>
    rw [U_cons]
    simp only [List.sum_cons, sum_V]
    have hx : (x+1)/2 + x/2 = x := by omega
    omega

lemma tail_step_zero (c : List ℕ) : tmass (step c) 0 = tmass c 0 := by
  simp [tmass, step, sum_trim0, sum_U]


lemma st_succ (n t : ℕ) : st n (t+1) = step (st n t) := by
  simp [st, List.range_succ, List.foldl_append]

lemma tail_st_eq_Q (n t k : ℕ) : tmass (st n t) k = Q n t k := by
  induction t generalizing k with
  | zero => cases k <;> simp [st, tmass]
  | succ t ih =>
    cases k with
    | zero =>
      rw [st_succ, tail_step_zero, ih]
      simp
    | succ k =>
      rw [st_succ, tail_step_succ, ih, ih]
      rfl


def Pos (l : List ℕ) : Prop := ∀ x ∈ l, 0 < x

lemma trim0_cons (x : ℕ) (l : List ℕ) (hx : x ≠ 0) :
    trim0 (x::l) = x :: trim0 l := by
  induction l using List.reverseRecOn with
  | nil => simp [trim0, hx]
  | append_singleton l y ih =>
    by_cases hy : y = 0
    · subst y
      rw [show trim0 (x :: (l ++ [0])) = trim0 (x::l) by
        change trim0 ((x::l) ++ [0]) = _
        simp [trim0]]
      rw [show trim0 (l ++ [0]) = trim0 l by simp [trim0]]
      exact ih
    · simp [trim0, hx, hy]

lemma Pos_trim0_V (carry : ℕ) (c : List ℕ) (hc : Pos c) :
    Pos (trim0 (V carry c)) := by
  induction c generalizing carry with
  | nil =>
    by_cases h : carry = 0
    · simp [V_nil, trim0, Pos, h]
    · simpa [V_nil, trim0, Pos, h] using Nat.pos_of_ne_zero h
  | cons x xs ih =>
    have hx : 0 < x := hc x (by simp)
    have hhead : 0 < (x+1)/2 + carry := by omega
    rw [V_cons, trim0_cons _ _ (by omega)]
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hhead
    · exact ih (x/2) (fun y hy => hc y (by simp [hy])) y hy

lemma Pos_step (c : List ℕ) (hc : Pos c) : Pos (step c) := by
  cases c with
  | nil => simp [step, U, trim0, Pos]
  | cons x xs =>
    have hx : 0 < x := hc x (by simp)
    have hh : 0 < (x+1)/2 := by omega
    rw [step, U_cons, trim0_cons _ _ (by omega)]
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hh
    · exact Pos_trim0_V (x/2) xs (fun y hy => hc y (by simp [hy])) y hy

lemma Pos_st (n t : ℕ) (hn : 0 < n) : Pos (st n t) := by
  induction t with
  | zero => simpa [st, Pos]
  | succ t ih => rw [st_succ]; exact Pos_step _ ih


lemma all_eq_one_of_Pos_sum (c : List ℕ) (hc : Pos c)
    (hs : c.sum = c.length) : ∀ x ∈ c, x = 1 := by
  induction c with
  | nil => simp
  | cons a l ih =>
    have ha : 1 ≤ a := hc a (by simp)
    have hlpos : Pos l := fun x hx => hc x (by simp [hx])
    have hls := List.length_le_sum_of_one_le l hlpos
    have ha1 : a = 1 := by simp only [List.sum_cons, List.length_cons] at hs; omega
    have hsl : l.sum = l.length := by
      simp only [List.sum_cons, List.length_cons, ha1] at hs
      omega
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha1
    · exact ih hlpos hsl x hx

lemma stable_iff_Q_pos (n t : ℕ) (hn : 0 < n) :
    st n t = List.replicate n 1 ↔ 0 < Q n t (n-1) := by
  constructor
  · intro h
    rw [← tail_st_eq_Q, h]
    simp [tmass]
    omega
  · intro hq
    have hp := Pos_st n t hn
    have hsum : (st n t).sum = n := by
      have h := tail_st_eq_Q n t 0
      simpa [tmass] using h
    have hdrop : (st n t).drop (n-1) ≠ [] := by
      intro he
      rw [← tail_st_eq_Q] at hq
      simp [tmass, he] at hq
    have hlen_lower : n ≤ (st n t).length := by
      have hnot : ¬(st n t).length ≤ n-1 := by
        intro hle
        exact hdrop (List.drop_eq_nil_of_le hle)
      omega
    have hlen_upper : (st n t).length ≤ n :=
      (List.length_le_sum_of_one_le _ hp).trans_eq hsum
    have hlen : (st n t).length = n := by omega
    apply List.eq_replicate_iff.mpr
    refine ⟨hlen, ?_⟩
    apply all_eq_one_of_Pos_sum _ hp
    omega


lemma Q_time_mono (N t k : ℕ) : Q N t k ≤ Q N (t+1) k := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [Q_succ_succ]
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h := Q_spatial_mono N t k
    omega

lemma Q_time_add_mono (N t d k : ℕ) : Q N t k ≤ Q N (t+d) k := by
  induction d with
  | zero => simp
  | succ d ih =>
    exact ih.trans (by simpa [Nat.add_assoc] using Q_time_mono N (t+d) k)

lemma Q_next_eventually (N t k r : ℕ) (h : r+1 ≤ Q N t k) :
    r ≤ Q N (t+r) (k+1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hsmall : r+1 ≤ Q N t k := by omega
    have hi := ih hsmall
    have hup : r+2 ≤ Q N (t+r) k :=
      h.trans (Q_time_add_mono N t r k)
    rw [show t + (r+1) = (t+r)+1 by omega, Q_succ_succ]
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega

lemma Q_eventually_ge (N k r : ℕ) (h : r ≤ N-k) :
    ∃ t, r ≤ Q N t k := by
  induction k generalizing r with
  | zero => exact ⟨0, by simpa using h⟩
  | succ k ih =>
    cases r with
    | zero => exact ⟨0, by simp⟩
    | succ r =>
      have hr : (r+1)+1 ≤ N-k := by omega
      obtain ⟨t, ht⟩ := ih ((r+1)+1) hr
      exact ⟨t+(r+1), Q_next_eventually N t k (r+1) ht⟩

lemma stable_steps_nonempty (n : ℕ) (hn : 0 < n) :
    {t : ℕ | st n t = List.replicate n 1}.Nonempty := by
  have hb : 1 ≤ n-(n-1) := by omega
  obtain ⟨t, ht⟩ := Q_eventually_ge n (n-1) 1 hb
  exact ⟨t, (stable_iff_Q_pos n t hn).mpr (by omega)⟩

lemma stable_persistent (n t u : ℕ) (hn : 0 < n) (htu : t ≤ u)
    (h : st n t = List.replicate n 1) : st n u = List.replicate n 1 := by
  apply (stable_iff_Q_pos n u hn).mpr
  have hp := (stable_iff_Q_pos n t hn).mp h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  exact hp.trans_le (Q_time_add_mono n t d (n-1))

lemma Q_succ_le_add_one (N t k : ℕ) : Q (N+1) t k ≤ Q N t k + 1 := by
  induction t generalizing k with
  | zero => cases k <;> simp
  | succ t ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [Q_succ_succ]
      calc
        (Q (N+1) t k + Q (N+1) t (k+1))/2
            ≤ ((Q N t k + 1) + (Q N t (k+1) + 1))/2 :=
              Nat.div_le_div_right (Nat.add_le_add (ih k) (ih (k+1)))
        _ = (Q N t k + Q N t (k+1))/2 + 1 := by omega

lemma Q_shift_pos (N t k : ℕ) (h : 0 < Q (N+1) t (k+1)) :
    0 < Q N t k := by
  induction t generalizing k with
  | zero => simp at h
  | succ t ih =>
    simp only [Q_succ_succ] at h
    by_cases hb : 0 < Q (N+1) t (k+1)
    · exact (ih k hb).trans_le (Q_time_mono N t k)
    · have hb0 : Q (N+1) t (k+1) = 0 := by omega
      have ha : 2 ≤ Q (N+1) t k := by
        simp only [hb0, Nat.add_zero] at h
        omega
      have hl := Q_succ_le_add_one N t k
      have hp : 0 < Q N t k := by omega
      exact hp.trans_le (Q_time_mono N t k)

lemma Q_shift_pos_previous (N t k : ℕ) (h : 0 < Q (N+1) (t+1) (k+1)) :
    0 < Q N t k := by
  simp only [Q_succ_succ] at h
  by_cases hb : 0 < Q (N+1) t (k+1)
  · exact Q_shift_pos N t k hb
  · have hb0 : Q (N+1) t (k+1) = 0 := by omega
    have ha : 2 ≤ Q (N+1) t k := by
      simp only [hb0, Nat.add_zero] at h
      omega
    have hl := Q_succ_le_add_one N t k
    omega




noncomputable def T (n : ℕ) : ℕ :=
  if n = 0 then 0 else sInf {t : ℕ | st n t = List.replicate n 1}

lemma T_eq_sInf (n : ℕ) (hn : 0 < n) :
    T n = sInf {t : ℕ | st n t = List.replicate n 1} := by
  simp [T, Nat.ne_of_gt hn]

lemma T_stable (n : ℕ) (hn : 0 < n) : st n (T n) = List.replicate n 1 := by
  rw [T_eq_sInf n hn]
  exact Nat.sInf_mem (stable_steps_nonempty n hn)

lemma T_min (n : ℕ) (hn : 0 < n) {t : ℕ}
    (ht : t < T n) : st n t ≠ List.replicate n 1 := by
  rw [T_eq_sInf n hn] at ht
  exact Nat.notMem_of_lt_sInf ht

lemma T_one : T 1 = 0 := by
  have hm : T 1 ≤ 0 := by
    rw [T_eq_sInf 1 (by omega)]
    apply Nat.sInf_le
    simp [st]
  omega

lemma T_two : T 2 = 1 := by
  have hu : T 2 ≤ 1 := by
    rw [T_eq_sInf 2 (by omega)]
    apply Nat.sInf_le
    apply (stable_iff_Q_pos 2 1 (by omega)).mpr
    norm_num [Q]
  have hl : 0 < T 2 := by
    by_contra h
    have hz : T 2 = 0 := by omega
    have hs := T_stable 2 (by omega)
    rw [hz] at hs
    have := (stable_iff_Q_pos 2 0 (by omega)).mp hs
    norm_num [Q] at this
  omega

lemma T_succ (n : ℕ) (hn : 1 ≤ n) :
    T (n+1) = T n + 1 ∨ T (n+1) = T n + 2 := by
  by_cases hn1 : n = 1
  · subst n
    simp [T_one, T_two]
  have hn2 : 2 ≤ n := by omega
  let t := T n
  have hstable : st n t = List.replicate n 1 := T_stable n (by omega)
  have hq : 0 < Q n t (n-1) := (stable_iff_Q_pos n t (by omega)).mp hstable
  have hi : n-2+1 = n-1 := by omega
  have hdiag : 3 ≤ Q (n+1) t (n-2) := by
    have hq' : 0 < Q n t (n-2+1) := by simpa [hi] using hq
    have hd := Q_diagonal n t (n-2) hq'
    omega
  have hnear : 1 ≤ Q (n+1) t (n-1) := by
    have hm := Q_succ_monotone n t (n-1)
    omega
  have hnear' : 1 ≤ Q (n+1) t (n-2+1) := by simpa [hi] using hnear
  have hnext : 2 ≤ Q (n+1) (t+1) (n-1) := by
    have hx : 2 ≤ Q (n+1) (t+1) (n-2+1) := by
      rw [Q_succ_succ, Nat.le_div_iff_mul_le (by omega)]
      omega
    simpa [hi] using hx
  have hupperQ : 0 < Q (n+1) (t+2) n := by
    have hnidx : n-1+1 = n := by omega
    have hx : 0 < Q (n+1) (t+2) (n-1+1) := by
      rw [show t+2 = (t+1)+1 by omega, Q_succ_succ]
      have hd : 1 ≤ (Q (n+1) (t+1) (n-1) + Q (n+1) (t+1) (n-1+1))/2 := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
      omega
    simpa [hnidx] using hx
  have hupperStable : st (n+1) (t+2) = List.replicate (n+1) 1 :=
    (stable_iff_Q_pos (n+1) (t+2) (by omega)).mpr (by
      simpa only [Nat.add_sub_cancel] using hupperQ)
  have hnot : st (n+1) t ≠ List.replicate (n+1) 1 := by
    intro hs
    have ha := (stable_iff_Q_pos (n+1) t (by omega)).mp hs
    cases ht : t with
    | zero =>
      have hz : Q (n+1) t n = 0 := by
        rw [ht]
        have hnpos : n = (n-1)+1 := by omega
        rw [hnpos, Q_time_zero_succ]
      have ha0 : 0 < Q (n+1) t n := by
        simpa only [Nat.add_sub_cancel] using ha
      omega
    | succ s =>
      have ha' : 0 < Q (n+1) (s+1) ((n-1)+1) := by
        simpa [ht, show (n+1)-1 = n by omega, show (n-1)+1 = n by omega] using ha
      have hp := Q_shift_pos_previous n s (n-1) ha'
      have hsold := (stable_iff_Q_pos n s (by omega)).mpr hp
      have hslt : s < T n := by dsimp [t] at ht; omega
      exact T_min n (by omega) hslt hsold
  have hlower : t < T (n+1) := by
    by_contra hle
    have hle' : T (n+1) ≤ t := by omega
    have hTst := T_stable (n+1) (by omega)
    have hp := stable_persistent (n+1) (T (n+1)) t (by omega) hle' hTst
    exact hnot hp
  have hupper : T (n+1) ≤ t+2 := by
    rw [T_eq_sInf (n+1) (by omega)]
    exact Nat.sInf_le hupperStable
  dsimp [t] at hlower hupper ⊢
  omega

lemma a_eq_T (n : ℕ) : a n = T n := by
  rfl

/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k)$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/
theorem oeis_a300997_finite_difference_is_one_or_two :
  ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  simpa only [a_eq_T] using T_succ n hn
