import FormalConjectures.Util.ProblemImports
open List Nat

/-- Computes the run lengths of a list of natural numbers. -/
def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

/--
A381587 $T_n$: The $n$-th row of the irregular triangle, following the recurrence:
$T_1=[1], T_2=[1], T_3=[2]$. For $n \ge 4$, $T_n = \text{Runs}(\text{Reverse}(T_{n-1})) \frown T_{n-1}$.
$n$ is 1-indexed here.
-/
def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 => -- Covers indices >= 4. Recurses on k+3, which is n-1.
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

/--
A381358: Row sums of irregular triangle A381587.
Row $n$ elements are $T_n$. The sequence $a(n)$ is the list sum of $T_n$.
-/
def A381358 (n : ℕ) : ℕ :=
  (A381587_T n).sum

/-! ### Auxiliary development -/

def D' : List ℕ → List ℕ
  | [] => []
  | [_] => [1]
  | a :: b :: t => if a = b then (D' (b :: t)).modifyHead (· + 1) else 1 :: D' (b :: t)

@[simp] lemma D'_nil : D' [] = [] := rfl
@[simp] lemma D'_single (a : ℕ) : D' [a] = [1] := rfl
lemma D'_cons_cons (a b : ℕ) (t : List ℕ) :
    D' (a :: b :: t) = if a = b then (D' (b :: t)).modifyHead (· + 1) else 1 :: D' (b :: t) := rfl
@[simp] lemma D'_cons_cons_eq (a : ℕ) (t : List ℕ) :
    D' (a :: a :: t) = (D' (a :: t)).modifyHead (· + 1) := by simp [D'_cons_cons]
@[simp] lemma D'_cons_cons_ne {a b : ℕ} (h : a ≠ b) (t : List ℕ) :
    D' (a :: b :: t) = 1 :: D' (b :: t) := by simp [D'_cons_cons, h]

/-- head of D' of a nonempty list is positive -/
lemma D'_cons_exists (a : ℕ) (l : List ℕ) : ∃ k Z, D' (a :: l) = (k + 1) :: Z := by
  induction l generalizing a with
  | nil => exact ⟨0, [], rfl⟩
  | cons b t ih =>
    by_cases h : a = b
    · subst h
      obtain ⟨k, Z, hk⟩ := ih a
      exact ⟨k + 1, Z, by rw [D'_cons_cons_eq, hk]; simp⟩
    · exact ⟨0, D' (b :: t), by rw [D'_cons_cons_ne h]⟩

lemma D'_ne_nil {l : List ℕ} (h : l ≠ []) : D' l ≠ [] := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h
  obtain ⟨k, Z, hk⟩ := D'_cons_exists a t
  rw [hk]; exact List.cons_ne_nil _ _

lemma D'_length_pos {l : List ℕ} (h : l ≠ []) : 0 < (D' l).length :=
  List.length_pos_of_ne_nil (D'_ne_nil h)

lemma D'_pos (l : List ℕ) : ∀ x ∈ D' l, 1 ≤ x := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t =>
      by_cases h : a = b
      · subst h
        rw [D'_cons_cons_eq]
        obtain ⟨k, Z, hk⟩ := D'_cons_exists a t
        rw [hk] at ih ⊢
        simp only [List.modifyHead_cons, List.mem_cons, forall_eq_or_imp] at ih ⊢
        exact ⟨by omega, ih.2⟩
      · rw [D'_cons_cons_ne h]
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨le_refl _, ih⟩

lemma D'_sum (l : List ℕ) : (D' l).sum = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t =>
      by_cases h : a = b
      · subst h
        rw [D'_cons_cons_eq]
        obtain ⟨k, Z, hk⟩ := D'_cons_exists a t
        rw [hk] at ih ⊢
        simp only [List.modifyHead_cons, List.sum_cons, List.length_cons] at ih ⊢
        omega
      · rw [D'_cons_cons_ne h]
        simp only [List.sum_cons, List.length_cons] at ih ⊢
        omega

lemma D'_split {a b : ℕ} (h : a ≠ b) (x y : List ℕ) :
    D' (x ++ a :: b :: y) = D' (x ++ [a]) ++ D' (b :: y) := by
  induction x generalizing a with
  | nil => simp [D'_cons_cons_ne h]
  | cons c x ih =>
    cases x with
    | nil =>
      by_cases hc : c = a
      · subst hc
        simp [D'_cons_cons_eq, D'_cons_cons_ne h]
      · simp [D'_cons_cons_ne hc, D'_cons_cons_ne h]
    | cons d x =>
      simp only [List.cons_append] at ih ⊢
      by_cases hc : c = d
      · subst hc
        rw [D'_cons_cons_eq, D'_cons_cons_eq, ih h]
        obtain ⟨k, Z, hk⟩ := D'_cons_exists c (x ++ [a])
        rw [hk]
        simp
      · rw [D'_cons_cons_ne hc, D'_cons_cons_ne hc, ih h]
        simp

lemma D'_replicate (k a : ℕ) : D' (List.replicate (k + 1) a) = [k + 1] := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.replicate_succ, D'_cons_cons_eq, ← List.replicate_succ, ih]; simp

lemma D'_replicate_append {a b : ℕ} (h : a ≠ b) (k : ℕ) (y : List ℕ) :
    D' (List.replicate (k + 1) a ++ b :: y) = (k + 1) :: D' (b :: y) := by
  induction k with
  | zero => simp [D'_cons_cons_ne h]
  | succ k ih => rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append,
      D'_cons_cons_eq, ← List.cons_append, ← List.replicate_succ, ih]; simp

lemma exists_run_decomp (l : List ℕ) (hl : l ≠ []) :
    ∃ k a l', l = List.replicate (k + 1) a ++ l' ∧ (l' = [] ∨ ∃ b y, l' = b :: y ∧ a ≠ b) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    rcases t with _ | ⟨b, t⟩
    · exact ⟨0, a, [], by simp, Or.inl rfl⟩
    · obtain ⟨k, a', l', h1, h2⟩ := ih (List.cons_ne_nil _ _)
      have hb : b = a' := by
        rw [List.replicate_succ, List.cons_append] at h1
        exact (List.cons.inj h1).1
      subst hb
      by_cases hab : a = b
      · subst hab
        exact ⟨k + 1, a, l', by rw [List.replicate_succ, List.cons_append, ← h1], h2⟩
      · exact ⟨0, a, b :: t, by simp, Or.inr ⟨b, t, rfl, hab⟩⟩

lemma D'_reverse (l : List ℕ) : D' l.reverse = (D' l).reverse := by
  induction' hn : l.length using Nat.strong_induction_on with n ih generalizing l
  subst hn
  rcases eq_or_ne l [] with rfl | hl
  · simp
  obtain ⟨k, a, l', rfl, h⟩ := exists_run_decomp l hl
  rcases h with rfl | ⟨b, y, rfl, hab⟩
  · simp only [List.append_nil, List.reverse_replicate, D'_replicate]; simp
  · have h1 := ih (b :: y).length (by simp) (b :: y) rfl
    rw [D'_replicate_append hab, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.replicate_succ, List.append_assoc, List.singleton_append, D'_split hab.symm,
      ← List.reverse_cons, h1, ← List.replicate_succ, D'_replicate]
    simp

lemma D'_tail {a : ℕ} {l : List ℕ} {k : ℕ} {Z : List ℕ} (h : D' (a :: l) = k :: Z) :
    (k = 1 → D' l = Z) ∧ (∀ j, k = j + 2 → D' l = (j + 1) :: Z) := by
  rcases l with _ | ⟨b, t⟩
  · simp at h
    exact ⟨fun _ => by simp [h.2], fun j hj => by omega⟩
  · by_cases hab : a = b
    · subst hab
      obtain ⟨k', Z', hk'⟩ := D'_cons_exists a t
      rw [D'_cons_cons_eq, hk'] at h
      simp at h
      refine ⟨fun h1 => by omega, fun j hj => ?_⟩
      rw [hk', h.2]
      congr 1
      omega
    · rw [D'_cons_cons_ne hab] at h
      simp at h
      exact ⟨fun _ => by rw [h.2], fun j hj => by omega⟩

lemma D'_dropLast_one {l Z : List ℕ} (h : D' l = Z ++ [1]) : D' l.dropLast = Z := by
  have hl : l ≠ [] := by rintro rfl; simp at h
  obtain ⟨a, m, hm⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr hl)
  have h1 : D' (a :: m) = 1 :: Z.reverse := by
    rw [← hm, D'_reverse, h]; simp
  have h2 := (D'_tail h1).1 rfl
  have hm' : m = l.dropLast.reverse := by
    rw [← List.tail_reverse, hm, List.tail_cons]
  rw [hm', D'_reverse] at h2
  simpa using congrArg List.reverse h2

lemma D'_dropLast_succ {l Z : List ℕ} {j : ℕ} (h : D' l = Z ++ [j + 2]) :
    D' l.dropLast = Z ++ [j + 1] := by
  have hl : l ≠ [] := by rintro rfl; simp at h
  obtain ⟨a, m, hm⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr hl)
  have h1 : D' (a :: m) = (j + 2) :: Z.reverse := by
    rw [← hm, D'_reverse, h]; simp
  have h2 := (D'_tail h1).2 j rfl
  have hm' : m = l.dropLast.reverse := by
    rw [← List.tail_reverse, hm, List.tail_cons]
  rw [hm', D'_reverse] at h2
  simpa using congrArg List.reverse h2

lemma run_lengths_nat_cons (h : ℕ) (t : List ℕ) :
    run_lengths_nat (h :: t) = ((h :: t).takeWhile (fun x => x = h)).length ::
      run_lengths_nat ((h :: t).drop ((h :: t).takeWhile (fun x => x = h)).length) := by
  rw [run_lengths_nat]

lemma run_lengths_nat_cons_eq_D' (t : List ℕ) : ∀ h, run_lengths_nat (h :: t) = D' (h :: t) := by
  induction t with
  | nil => intro h; rw [run_lengths_nat_cons]; simp [run_lengths_nat]
  | cons b t ih =>
    intro h
    rw [run_lengths_nat_cons, D'_cons_cons]
    by_cases hb : h = b
    · subst hb
      have := ih h
      rw [run_lengths_nat_cons] at this
      simp only [takeWhile_cons, decide_true] at this ⊢
      rw [← this]
      simp
    · have hb' : ¬ b = h := fun e => hb e.symm
      simp [hb, hb', ih]

lemma run_lengths_nat_eq_D' (l : List ℕ) : run_lengths_nat l = D' l := by
  cases l with
  | nil => simp [run_lengths_nat]
  | cons h t => exact run_lengths_nat_cons_eq_D' t h

def T' : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 => D' (T' (k + 3)).reverse ++ T' (k + 3)

lemma A381587_T_eq_T' : ∀ n, A381587_T n = T' n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | k + 4 => by
    rw [A381587_T, T', run_lengths_nat_eq_D', A381587_T_eq_T' (k + 3)]

def W (n : ℕ) : List ℕ := (T' n).reverse

lemma W_succ (k : ℕ) : W (k + 4) = W (k + 3) ++ (D' (W (k + 3))).reverse := by
  simp [W, T', List.reverse_append]

lemma W_succ' {k : ℕ} (hk : 3 ≤ k) : W (k + 1) = W k ++ (D' (W k)).reverse := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  exact W_succ j

lemma W_shape : ∀ k, 6 ≤ k →
    (∃ t, W k = [2,1,1,1,3,1] ++ t) ∧ (∃ z, W k = 2 :: 1 :: z ++ [3, 1]) ∧
    (∃ w, W k = w ++ [3, 1]) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨⟨[], by decide⟩, ⟨[1,1], by decide⟩, ⟨[2,1,1,1], by decide⟩⟩
  | succ k hk ih =>
    obtain ⟨⟨t, ht⟩, ⟨z, hz⟩, -⟩ := ih
    have hD : D' (W k) = 1 :: 3 :: D' (3 :: 1 :: t) := by
      rw [ht]; simp
    rw [W_succ' (by omega), hD]
    refine ⟨⟨t ++ (D' (3 :: 1 :: t)).reverse ++ [3, 1], ?_⟩,
      ⟨z ++ [3, 1] ++ (D' (3 :: 1 :: t)).reverse, ?_⟩,
      ⟨2 :: 1 :: z ++ [3, 1] ++ (D' (3 :: 1 :: t)).reverse, ?_⟩⟩
    · rw [ht]; simp
    · rw [hz]; simp
    · rw [hz]; simp

/-- The prefix of `Q`. -/
abbrev Pfx : List ℕ := [1,1,1,1,1,1,3,1,5,1,1,1]

def GoodW (m : ℕ) : Prop :=
  (∃ R'', D' (W m) = R'' ++ [5,1,3,1,1,1,1,1,1]) ∧
  (∃ t, D' (D' (W m)) = Pfx ++ t ++ [1,6]) ∧
  D' (D' (D' (W m))) = 6 :: (W (m-4)).tail

set_option maxRecDepth 100000 in
lemma GoodW_11 : GoodW 11 :=
  ⟨⟨[1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 1], by decide⟩,
   ⟨[5, 1, 3, 1, 1], by decide⟩, by decide⟩

lemma GoodW_step {m : ℕ} (hm : 11 ≤ m) (h : GoodW m) :
    GoodW (m + 1) ∧
    D' (W (m + 1)) = (D' (W m)).dropLast ++ 7 :: (D' (D' (W m))).dropLast.reverse ∧
    D' (D' (W (m + 1))) = (D' (D' (W m))).dropLast ++ 5 :: (D' (D' (D' (W m)))).reverse := by
  obtain ⟨⟨R'', hR⟩, ⟨t, hQ⟩, hV⟩ := h
  obtain ⟨-, -, ⟨w, hw⟩⟩ := W_shape m (by omega)
  obtain ⟨-, ⟨z, hz⟩, -⟩ := W_shape (m - 4) (by omega)
  -- notation
  set R := D' (W m) with hRdef
  set Q := D' R with hQdef
  set V := D' Q with hVdef
  have hW1 : W (m + 1) = W m ++ R.reverse := W_succ' (by omega)
  -- Step 1 : R_{m+1}
  have hR1 : R = D' (w ++ [3]) ++ [1] := by
    rw [hRdef, hw]
    have := D'_split (show (3:ℕ) ≠ 1 by norm_num) w []
    simpa using this
  have hRrev : R.reverse = [1,1,1,1,1,1,3,1,5] ++ R''.reverse := by
    rw [hR]; simp
  have hRdrop : R.dropLast = D' (w ++ [3]) := by
    rw [hR1, List.dropLast_concat]
  have hQrev : Q.reverse = 6 :: D' (3 :: 1 :: 5 :: R''.reverse) := by
    rw [hQdef, ← D'_reverse, hRrev]
    simp
  have hQdrop_rev : Q.dropLast.reverse = D' (3 :: 1 :: 5 :: R''.reverse) := by
    rw [← List.tail_reverse, hQrev, List.tail_cons]
  have hRnew : D' (W (m + 1)) = R.dropLast ++ 7 :: Q.dropLast.reverse := by
    rw [hW1, hw, hRrev, hRdrop, hQdrop_rev]
    have := D'_split (show (3:ℕ) ≠ 1 by norm_num) w ([1,1,1,1,1,1,3,1,5] ++ R''.reverse)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    rw [this]
    simp
  -- Step 2 : Q_{m+1}
  have hRdrop' : R.dropLast = R'' ++ [5,1,3,1,1,1,1,1] := by
    rw [hR]
    have : R'' ++ [5,1,3,1,1,1,1,1,1] = (R'' ++ [5,1,3,1,1,1,1,1]) ++ [1] := by simp
    rw [this, List.dropLast_concat]
  have hQdrop : Q.dropLast = Pfx ++ t ++ [1] := by
    rw [hQ]
    have : Pfx ++ t ++ [1, 6] = (Pfx ++ t ++ [1]) ++ [6] := by simp
    rw [this, List.dropLast_concat]
  have hDRdrop : D' R.dropLast = Q.dropLast ++ [5] := by
    rw [hQdrop]
    apply D'_dropLast_succ (j := 4)
    rw [← hQdef, hQ]; simp
  have hVz : V = (6 :: 1 :: z ++ [3]) ++ [1] := by
    rw [hV, hz]; simp
  have hDQdrop : D' Q.dropLast = 6 :: 1 :: z ++ [3] := D'_dropLast_one (by rw [← hVdef, hVz])
  have hVrev : V.reverse = 1 :: 3 :: z.reverse ++ [1, 6] := by
    rw [hVz]; simp
  have hQnew : D' (D' (W (m + 1))) = Q.dropLast ++ 5 :: V.reverse := by
    rw [hRnew, hRdrop', hQdrop, hVrev]
    have := D'_split (show (1:ℕ) ≠ 7 by norm_num) (R'' ++ [5,1,3,1,1,1,1])
      ((Pfx ++ t ++ [1]).reverse)
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.reverse_append, List.reverse_cons, List.reverse_nil] at this ⊢
    rw [this]
    have h2 : D' (1 :: (t.reverse ++ [1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1])) = (D' Q.dropLast).reverse := by
      rw [← D'_reverse, hQdrop]; simp
    rw [D'_cons_cons_ne (show (7:ℕ) ≠ 1 by norm_num), h2, hDQdrop]
    have h3 := hDRdrop
    rw [hRdrop', hQdrop] at h3
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h3
    rw [h3]
    simp
  -- Step 3 : V_{m+1}
  have hDV : D' V = D' (W (m - 4)) := by
    rw [hVz, hz]
    simp
  have hWm3 : W (m - 3) = W (m - 4) ++ (D' (W (m - 4))).reverse := by
    have := W_succ' (k := m - 4) (by omega)
    rwa [show m - 4 + 1 = m - 3 by omega] at this
  have hVnew : D' (D' (D' (W (m + 1)))) = 6 :: (W (m + 1 - 4)).tail := by
    rw [hQnew, hQdrop, hVrev, show m + 1 - 4 = m - 3 by omega, hWm3, ← hDV, hz, hVz]
    have := D'_split (show (1:ℕ) ≠ 5 by norm_num) (Pfx ++ t) (1 :: 3 :: z.reverse ++ [1, 6])
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    rw [this]
    have h2 : D' (1 :: (3 :: (z.reverse ++ [1, 6]))) = (D' ((6 :: 1 :: z ++ [3]) ++ [1])).reverse := by
      rw [← D'_reverse]; simp
    rw [D'_cons_cons_ne (show (5:ℕ) ≠ 1 by norm_num), h2]
    have h3 := hDQdrop
    rw [hQdrop] at h3
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h3
    rw [h3]
    simp
  refine ⟨⟨⟨R.dropLast ++ 7 :: 1 :: t.reverse ++ [1,1,1], ?_⟩, ⟨t ++ [1,5,1,3] ++ z.reverse, ?_⟩, hVnew⟩,
    hRnew, hQnew⟩
  · rw [hRnew, hQdrop]; simp
  · rw [hQnew, hQdrop, hVrev]; simp

lemma GoodW_all : ∀ m, 11 ≤ m → GoodW m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact GoodW_11
  | succ m hm ih => exact (GoodW_step hm ih).1

/-- lengths -/
def ℓ (n : ℕ) : ℕ := (W n).length
def rr (n : ℕ) : ℕ := (D' (W n)).length
def qq (n : ℕ) : ℕ := (D' (D' (W n))).length

lemma W_ne_nil {k : ℕ} (hk : 1 ≤ k) : W k ≠ [] := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rcases lt_or_ge k 3 with h | h
    · interval_cases k <;> decide
    · rw [W_succ' h]
      exact List.append_ne_nil_of_left_ne_nil ih _

lemma ℓ_succ {k : ℕ} (hk : 3 ≤ k) : ℓ (k + 1) = ℓ k + rr k := by
  unfold ℓ rr
  rw [W_succ' hk, List.length_append, List.length_reverse]

lemma rr_qq_succ {m : ℕ} (hm : 11 ≤ m) :
    rr (m + 1) + 1 = rr m + qq m ∧ qq (m + 1) = qq m + ℓ (m - 4) := by
  obtain ⟨-, h1, h2⟩ := GoodW_step hm (GoodW_all m hm)
  have hR : rr m ≠ 0 := by
    unfold rr; simpa using D'_ne_nil (W_ne_nil (by omega : 1 ≤ m))
  have hQ : qq m ≠ 0 := by
    unfold qq; simpa using D'_ne_nil (D'_ne_nil (W_ne_nil (by omega : 1 ≤ m)))
  have hV : (D' (D' (D' (W m)))).length = ℓ (m - 4) := by
    rw [(GoodW_all m hm).2.2]
    have := W_ne_nil (by omega : 1 ≤ m - 4)
    unfold ℓ
    simp [List.length_tail]
    have := List.length_pos_of_ne_nil this
    omega
  unfold rr qq at *
  rw [h2, h1]
  simp only [List.length_append, List.length_cons, List.length_reverse, List.length_dropLast]
  rw [hV]
  omega

lemma exists_lambda : ∃ L : ℝ, 3/2 ≤ L ∧ L ≤ 8/5 ∧ L^4 * (L-1)^3 = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x^4 * (x-1)^3) (Set.Icc (3/2) (8/5)) := by fun_prop
  have := intermediate_value_Icc (by norm_num : (3/2:ℝ) ≤ 8/5) hcont
  have h1 : (1:ℝ) ∈ Set.Icc ((3/2:ℝ)^4 * ((3/2:ℝ)-1)^3) ((8/5:ℝ)^4 * ((8/5:ℝ)-1)^3) := by
    constructor <;> norm_num
  obtain ⟨L, hL, hL1⟩ := this h1
  exact ⟨L, hL.1, hL.2, hL1⟩

/-- the bound predicate -/
def Bnd (L : ℝ) (n : ℕ) : Prop :=
  (1/10 * L^n ≤ (ℓ n : ℝ) ∧ (ℓ n : ℝ) ≤ 10 * L^n) ∧
  (1/10 * L^n * (L-1) ≤ (rr n : ℝ) ∧ (rr n : ℝ) ≤ 10 * L^n * (L-1)) ∧
  (1/10 * L^n * (L-1)^2 ≤ (qq n : ℝ) - 1 ∧ (qq n : ℝ) - 1 ≤ 10 * L^n * (L-1)^2)

lemma base_bounds (L : ℝ) (hL0 : 3/2 ≤ L) (hL1 : L ≤ 8/5) (n a b c : ℕ)
    (ha : ℓ n = a) (hb : rr n = b) (hc : qq n = c)
    (h1 : 1/10 * (8/5:ℝ)^n ≤ a) (h2 : (a:ℝ) ≤ 10 * (3/2:ℝ)^n)
    (h3 : 1/10 * ((8/5:ℝ)^n * (3/5)) ≤ b) (h4 : (b:ℝ) ≤ 10 * ((3/2:ℝ)^n * (1/2)))
    (h5 : 1/10 * ((8/5:ℝ)^n * (9/25)) ≤ (c:ℝ) - 1) (h6 : (c:ℝ) - 1 ≤ 10 * ((3/2:ℝ)^n * (1/4))) :
    Bnd L n := by
  have hL : 0 ≤ L := by linarith
  have hp1 : L^n ≤ (8/5)^n := pow_le_pow_left₀ hL hL1 n
  have hp2 : (3/2)^n ≤ L^n := pow_le_pow_left₀ (by norm_num) hL0 n
  have hu1 : L - 1 ≤ 3/5 := by linarith
  have hu2 : 1/2 ≤ L - 1 := by linarith
  have hu3 : (L-1)^2 ≤ 9/25 := by nlinarith
  have hu4 : 1/4 ≤ (L-1)^2 := by nlinarith
  have hb1 : L^n * (L-1) ≤ (8/5)^n * (3/5) := mul_le_mul hp1 hu1 (by linarith) (by positivity)
  have hb2 : (3/2)^n * (1/2) ≤ L^n * (L-1) := mul_le_mul hp2 hu2 (by norm_num) (by positivity)
  have hc1 : L^n * (L-1)^2 ≤ (8/5)^n * (9/25) := mul_le_mul hp1 hu3 (by positivity) (by positivity)
  have hc2 : (3/2)^n * (1/4) ≤ L^n * (L-1)^2 := mul_le_mul hp2 hu4 (by norm_num) (by positivity)
  unfold Bnd
  rw [ha, hb, hc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

set_option maxRecDepth 100000 in
lemma vals11 : ℓ 11 = 66 ∧ rr 11 = 36 ∧ qq 11 = 19 := by unfold ℓ rr qq; decide
set_option maxRecDepth 100000 in
lemma vals12 : ℓ 12 = 102 ∧ rr 12 = 54 ∧ qq 12 = 29 := by unfold ℓ rr qq; decide
set_option maxRecDepth 100000 in
lemma vals13 : ℓ 13 = 156 ∧ rr 13 = 82 ∧ qq 13 = 45 := by unfold ℓ rr qq; decide
set_option maxRecDepth 100000 in
lemma vals14 : ℓ 14 = 238 ∧ rr 14 = 126 ∧ qq 14 = 71 := by unfold ℓ rr qq; decide
set_option maxRecDepth 100000 in
lemma vals15 : ℓ 15 = 364 ∧ rr 15 = 196 ∧ qq 15 = 113 := by unfold ℓ rr qq; decide

lemma bounds (L : ℝ) (hL0 : 3/2 ≤ L) (hL1 : L ≤ 8/5) (hLeq : L^4 * (L-1)^3 = 1) :
    ∀ n, 11 ≤ n → Bnd L n := by
  have key : ∀ N, ∀ n, 11 ≤ n → n ≤ N → Bnd L n := by
    intro N
    induction N with
    | zero => intro n h1 h2; omega
    | succ N ih =>
      intro n h1 h2
      rcases Nat.lt_or_ge n (N+1) with h | h
      · exact ih n h1 (by omega)
      · have hn : n = N + 1 := by omega
        rcases le_or_gt n 15 with h15 | h15
        · obtain ⟨v1, v2, v3⟩ := vals11
          obtain ⟨v4, v5, v6⟩ := vals12
          obtain ⟨v7, v8, v9⟩ := vals13
          obtain ⟨v10, v11, v12⟩ := vals14
          obtain ⟨v13, v14, v15⟩ := vals15
          interval_cases n
          · exact base_bounds L hL0 hL1 11 _ _ _ v1 v2 v3 (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          · exact base_bounds L hL0 hL1 12 _ _ _ v4 v5 v6 (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          · exact base_bounds L hL0 hL1 13 _ _ _ v7 v8 v9 (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          · exact base_bounds L hL0 hL1 14 _ _ _ v10 v11 v12 (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          · exact base_bounds L hL0 hL1 15 _ _ _ v13 v14 v15 (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
        · subst hn
          have hN : 15 ≤ N := by omega
          obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := ih N (by omega) le_rfl
          obtain ⟨⟨d1, d2⟩, -, -⟩ := ih (N - 4) (by omega) (by omega)
          have e1 : ℓ (N + 1) = ℓ N + rr N := ℓ_succ (by omega)
          obtain ⟨e2, e3⟩ := rr_qq_succ (m := N) (by omega)
          set X := L^(N-4) with hX
          have f1 : L^(N+1) = X * L^5 := by rw [hX, ← pow_add]; congr 1; omega
          have f2 : L^N = X * L^4 := by rw [hX, ← pow_add]; congr 1; omega
          have hid : X * L^5 * (L-1)^2 = X * L^4 * (L-1)^2 + X := by
            linear_combination X * hLeq
          have hpos : 0 ≤ X := by positivity
          unfold Bnd
          rw [e1, e3, f1]
          have e2' : (rr (N+1) : ℝ) = rr N + qq N - 1 := by
            have : ((rr (N + 1) + 1 : ℕ) : ℝ) = ((rr N + qq N : ℕ) : ℝ) := by rw [e2]
            push_cast at this; linarith
          rw [e2']
          push_cast
          rw [f2] at a1 a2 b1 b2 c1 c2
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  intro n hn
  exact key n n hn le_rfl

lemma A381358_eq (n : ℕ) : A381358 n = (T' n).sum := by
  unfold A381358; rw [A381587_T_eq_T']

lemma S_succ {k : ℕ} (hk : 3 ≤ k) : A381358 (k + 1) = A381358 k + ℓ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  rw [A381358_eq, A381358_eq, T', List.sum_append, D'_sum, List.length_reverse]
  unfold ℓ W
  rw [List.length_reverse]
  ring

set_option maxRecDepth 100000 in
lemma S12 : A381358 12 = 175 := by rw [A381358_eq]; decide

lemma S_upper (L : ℝ) (hL0 : 3/2 ≤ L) (hL1 : L ≤ 8/5) (hLeq : L^4 * (L-1)^3 = 1) :
    ∀ n, 12 ≤ n → (A381358 n : ℝ) ≤ 20 * L^n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [S12]
    have : (3/2:ℝ)^12 ≤ L^12 := pow_le_pow_left₀ (by norm_num) hL0 12
    norm_num at this ⊢
    linarith
  | succ n hn ih =>
    rw [S_succ (by omega)]
    push_cast
    have := ((bounds L hL0 hL1 hLeq n (by omega)).1).2
    have hp : 0 ≤ L^n := by positivity
    rw [pow_succ]
    nlinarith

lemma S_lower (L : ℝ) (hL0 : 3/2 ≤ L) (hL1 : L ≤ 8/5) (hLeq : L^4 * (L-1)^3 = 1) :
    ∀ n, 12 ≤ n → 1/16 * L^n ≤ (A381358 n : ℝ) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [S_succ (by omega)]
  push_cast
  have := ((bounds L hL0 hL1 hLeq k (by omega)).1).1
  have hp : 0 ≤ L^k := by positivity
  have h0 : (0:ℝ) ≤ A381358 k := by positivity
  rw [pow_succ]
  nlinarith

theorem A381358_limit_exists' :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) := by
  obtain ⟨L, hL0, hL1, hLeq⟩ := exists_lambda
  refine ⟨L, ?_⟩
  have hLpos : 0 < L := by linarith
  have hg : Filter.Tendsto (fun n : ℕ => ((A381358 n : ℝ) / L^n) ^ ((n:ℝ)⁻¹))
      Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1/16 : ℝ) ^ ((n:ℝ)⁻¹)) Filter.atTop (nhds 1) := by
      have := (Real.continuousAt_const_rpow (a := (1/16:ℝ)) (b := 0) (by norm_num)).tendsto.comp
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Function.comp_def] using this
    have h2 : Filter.Tendsto (fun n : ℕ => (20 : ℝ) ^ ((n:ℝ)⁻¹)) Filter.atTop (nhds 1) := by
      have := (Real.continuousAt_const_rpow (a := (20:ℝ)) (b := 0) (by norm_num)).tendsto.comp
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Function.comp_def] using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2
    · filter_upwards [Filter.eventually_ge_atTop 12] with n hn
      apply Real.rpow_le_rpow (by norm_num) _ (by positivity)
      rw [le_div_iff₀ (by positivity)]
      exact S_lower L hL0 hL1 hLeq n hn
    · filter_upwards [Filter.eventually_ge_atTop 12] with n hn
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      rw [div_le_iff₀ (by positivity)]
      exact S_upper L hL0 hL1 hLeq n hn
  have := hg.const_mul L
  rw [mul_one] at this
  apply this.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h : (A381358 n : ℝ) ^ ((n:ℝ)⁻¹) = (L^n * ((A381358 n : ℝ) / L^n)) ^ ((n:ℝ)⁻¹) := by
    congr 1; field_simp
  rw [h, Real.mul_rpow (by positivity) (by positivity), Real.pow_rpow_inv_natCast hLpos.le (by omega)]

/--
A381358 If it exists, the limit of $\mathrm{A381358}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/
theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) :=
by exact A381358_limit_exists'

theorem A381358_limit_exists.disproof : ¬ (type_of% @A381358_limit_exists) := sorry
