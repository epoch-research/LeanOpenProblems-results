import FormalConjectures.Util.ProblemImports

open Nat Finset

def tri (m : ℕ) : ℕ := m * (m + 1) / 2

lemma tri_succ (m : ℕ) : tri (m + 1) = tri m + (m + 1) := by
  simp only [tri]
  have hdiv : 2 ∣ 2 * (m + 1) := ⟨m + 1, by ring⟩
  calc
    (m + 1) * (m + 2) / 2
        = (m * (m + 1) + 2 * (m + 1)) / 2 := by ring_nf
    _   = m * (m + 1) / 2 + 2 * (m + 1) / 2 :=
          Nat.add_div_of_dvd_left hdiv
    _   = m * (m + 1) / 2 + (m + 1) := by
          rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

lemma tri_eq_pred_add (k : ℕ) (hk : 1 ≤ k) : tri k = tri (k - 1) + k := by
  cases k with
  | zero => omega
  | succ k => rw [tri_succ]; simp

lemma tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b _ ih =>
    rw [tri_succ]
    exact le_trans ih (Nat.le_add_right _ _)

def W : ℕ → ℕ → ℕ
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 =>
    if n < k + 1 then W n k
    else W n k + (k + 1).factorial * W (n - (k + 1)) k

lemma W_succ_of_lt {n k : ℕ} (h : n < k + 1) : W n (k + 1) = W n k := by
  simp [W, h]

lemma W_succ_of_le {n k : ℕ} (h : k + 1 ≤ n) :
    W n (k + 1) = W n k + (k + 1).factorial * W (n - (k + 1)) k := by
  simp [W, Nat.not_lt.mpr h]

def sWeight (S : Finset ℕ) : ℕ := ∏ i ∈ S, i.factorial

lemma sWeight_insert {a : ℕ} {S : Finset ℕ} (h : a ∉ S) :
    sWeight (insert a S) = a.factorial * sWeight S := by
  simp [sWeight, prod_insert h]

lemma Icc_succ_right_one (m : ℕ) :
    Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
  ext x; simp [mem_Icc, mem_insert]; omega

lemma not_mem_Icc_succ (m : ℕ) : m + 1 ∉ Icc 1 m := by
  simp [mem_Icc]

def Wsum (n m : ℕ) : ℕ :=
  ∑ S ∈ (Icc 1 m).powerset, if ∑ i ∈ S, i = n then sWeight S else 0

lemma W_eq_Wsum : ∀ m n, W n m = Wsum n m := by
  intro m
  induction m with
  | zero =>
    intro n
    simp [W, Wsum, sWeight]
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
      exact mt Eq.symm hn
  | succ m ih =>
    intro n
    have hI : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := Icc_succ_right_one m
    have hnotin : m + 1 ∉ Icc 1 m := not_mem_Icc_succ m
    have hsplit :=
      sum_powerset_insert (s := Icc 1 m) (a := m + 1) hnotin
        (fun S : Finset ℕ => if ∑ i ∈ S, i = n then sWeight S else 0)
    simp only [Wsum, hI]
    rw [hsplit]
    have hright :
        ∑ S ∈ (Icc 1 m).powerset,
            (if ∑ i ∈ insert (m + 1) S, i = n then sWeight (insert (m + 1) S) else 0) =
          if m + 1 ≤ n then (m + 1).factorial * Wsum (n - (m + 1)) m else 0 := by
      have hcongr :
          ∑ S ∈ (Icc 1 m).powerset,
              (if ∑ i ∈ insert (m + 1) S, i = n then sWeight (insert (m + 1) S) else 0) =
            ∑ S ∈ (Icc 1 m).powerset,
              (if m + 1 + ∑ i ∈ S, i = n then
                (m + 1).factorial * sWeight S else 0) := by
        apply Finset.sum_congr rfl
        intro S hS
        have hmem : m + 1 ∉ S := by
          have : S ⊆ Icc 1 m := mem_powerset.mp hS
          intro h; exact hnotin (this h)
        rw [sum_insert hmem, sWeight_insert hmem]
      rw [hcongr]
      by_cases hle : m + 1 ≤ n
      · have :
            ∑ S ∈ (Icc 1 m).powerset,
                (if m + 1 + ∑ i ∈ S, i = n then
                  (m + 1).factorial * sWeight S else 0) =
              ∑ S ∈ (Icc 1 m).powerset,
                (if ∑ i ∈ S, i = n - (m + 1) then
                  (m + 1).factorial * sWeight S else 0) := by
          apply Finset.sum_congr rfl
          intro S _
          have : m + 1 + ∑ i ∈ S, i = n ↔ ∑ i ∈ S, i = n - (m + 1) := by omega
          simp [this]
        rw [this, if_pos hle]
        have hfactor :
            ∑ S ∈ (Icc 1 m).powerset,
                (if ∑ i ∈ S, i = n - (m + 1) then
                  (m + 1).factorial * sWeight S else 0) =
              (m + 1).factorial * Wsum (n - (m + 1)) m := by
          unfold Wsum
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          split_ifs <;> ring
        exact hfactor
      · have :
            ∑ S ∈ (Icc 1 m).powerset,
                (if m + 1 + ∑ i ∈ S, i = n then
                  (m + 1).factorial * sWeight S else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro S _
          have : ¬ (m + 1 + ∑ i ∈ S, i = n) := by omega
          simp [this]
        rw [this, if_neg hle]
    rw [hright]
    by_cases hlt : n < m + 1
    · rw [W_succ_of_lt hlt, if_neg (Nat.not_le.mpr hlt), add_zero, ih]
      rfl
    · have hle : m + 1 ≤ n := Nat.le_of_not_lt hlt
      rw [W_succ_of_le hle, if_pos hle, ih n, ih (n - (m + 1))]
      rfl

lemma W_eq_sum (m n : ℕ) :
    W n m = ∑ S ∈ (Icc 1 m).powerset.filter (fun S => ∑ i ∈ S, i = n), sWeight S := by
  rw [W_eq_Wsum]
  simp [Wsum, sum_filter]

/-- Unbalancing increases the product of two factorials. -/
lemma unbalance_prod {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) :
    x.factorial * y.factorial < (x - 1).factorial * (y + 1).factorial := by
  have hxf : x.factorial = x * (x - 1).factorial := by
    cases x with
    | zero => omega
    | succ x => simp [factorial]
  have hyf : (y + 1).factorial = (y + 1) * y.factorial := factorial_succ _
  have hpos : 0 < (x - 1).factorial * y.factorial :=
    Nat.mul_pos (factorial_pos _) (factorial_pos _)
  rw [hxf, hyf]
  have hL : x * (x - 1).factorial * y.factorial =
      (x - 1).factorial * y.factorial * x := by ring
  have hR : (x - 1).factorial * ((y + 1) * y.factorial) =
      (x - 1).factorial * y.factorial * (y + 1) := by ring
  rw [hL, hR]
  exact Nat.mul_lt_mul_of_pos_left (by omega) hpos

lemma fact_pred (n : ℕ) (h : 1 ≤ n) : n.factorial = n * (n - 1).factorial := by
  cases n with
  | zero => omega
  | succ n => simp [factorial]

/-- The greediest 4-set summing to `3k-2` in `[1, k-2]` is `{7, k-4, k-3, k-2}`. -/
lemma four_set_prod_le (k a b c d : ℕ) (hk : 14 ≤ k)
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ k - 2)
    (hsum : a + b + c + d = 3 * k - 2) :
    a.factorial * b.factorial * c.factorial * d.factorial ≤
      (7).factorial * (k - 4).factorial * (k - 3).factorial * (k - 2).factorial := by
  by_cases hd0 : d = k - 2
  · subst hd0
    by_cases hc0 : c = k - 3
    · subst hc0
      by_cases hb0 : b = k - 4
      · subst hb0
        have ha7 : a = 7 := by omega
        subst ha7
        exact le_rfl
      · have hb : b < k - 4 := by omega
        have ha2 : 2 ≤ a := by
          have : a + b = k + 3 := by omega
          omega
        have hlt := unbalance_prod (x := a) (y := b) (by omega) hab
        have ih := four_set_prod_le k (a - 1) (b + 1) (k - 3) (k - 2) hk
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hmul :
            a.factorial * b.factorial * (k - 3).factorial * (k - 2).factorial <
              (a - 1).factorial * (b + 1).factorial * (k - 3).factorial *
                (k - 2).factorial := by
          have hpos : 0 < (k - 3).factorial * (k - 2).factorial :=
            Nat.mul_pos (factorial_pos _) (factorial_pos _)
          have := Nat.mul_lt_mul_of_pos_right hlt hpos
          convert this using 1 <;> ring
        exact le_of_lt (lt_of_lt_of_le hmul ih)
    · have hc : c < k - 3 := by omega
      have ha2 : 2 ≤ a := by
        have hmax : b + c ≤ (k - 5) + (k - 4) := by omega
        have : a + b + c = 2 * k := by omega
        omega
      have hlt := unbalance_prod (x := a) (y := c) (by omega) (by omega)
      have ih := four_set_prod_le k (a - 1) b (c + 1) (k - 2) hk
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hmul :
          a.factorial * b.factorial * c.factorial * (k - 2).factorial <
            (a - 1).factorial * b.factorial * (c + 1).factorial *
              (k - 2).factorial := by
        have hpos : 0 < b.factorial * (k - 2).factorial :=
          Nat.mul_pos (factorial_pos _) (factorial_pos _)
        have := Nat.mul_lt_mul_of_pos_right hlt hpos
        convert this using 1 <;> ring
      exact le_of_lt (lt_of_lt_of_le hmul ih)
  · have hlt_d : d < k - 2 := by omega
    have ha2 : 2 ≤ a := by
      have hmax : b + c + d ≤ (k - 5) + (k - 4) + (k - 3) := by omega
      omega
    have hlt := unbalance_prod (x := a) (y := d) (by omega) (by omega)
    have ih := four_set_prod_le k (a - 1) b c (d + 1) hk
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hmul :
        a.factorial * b.factorial * c.factorial * d.factorial <
          (a - 1).factorial * b.factorial * c.factorial * (d + 1).factorial := by
      have hpos : 0 < b.factorial * c.factorial :=
        Nat.mul_pos (factorial_pos _) (factorial_pos _)
      have := Nat.mul_lt_mul_of_pos_right hlt hpos
      convert this using 1 <;> ring
    exact le_of_lt (lt_of_lt_of_le hmul ih)
termination_by (k - 2 - d) + (k - 3 - c) + (k - 4 - b)

lemma lex5 {A B C D E A' B' C' D' E' : ℕ}
    (h : A < A' ∨ A = A' ∧ (B < B' ∨ B = B' ∧ (C < C' ∨ C = C' ∧
      (D < D' ∨ D = D' ∧ E < E')))) :
    Prod.Lex (fun x1 x2 => x1 < x2)
      (Prod.Lex (fun x1 x2 => x1 < x2)
        (Prod.Lex (fun x1 x2 => x1 < x2)
          (Prod.Lex (fun x1 x2 => x1 < x2) fun x1 x2 => x1 < x2)))
      (A, B, C, D, E) (A', B', C', D', E') := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · apply Prod.Lex.right
    rcases h with h | ⟨rfl, h⟩
    · exact Prod.Lex.left _ _ h
    · apply Prod.Lex.right
      rcases h with h | ⟨rfl, h⟩
      · exact Prod.Lex.left _ _ h
      · apply Prod.Lex.right
        rcases h with h | ⟨rfl, h⟩
        · exact Prod.Lex.left _ _ h
        · apply Prod.Lex.right
          exact h

/-- `{1,2,x,y,z}` cannot sum to `3k-2` with `2 < x < y < z ≤ k-2`. -/
lemma five_not_12 {k x y z : ℕ} (hxy : 2 < x) (hyz : x < y) (hzy : y < z)
    (hz : z ≤ k - 2) : ¬ (1 + 2 + x + y + z = 3 * k - 2) := by
  intro h
  have : x + y + z = 3 * k - 5 := by omega
  have hmax : x + y + z ≤ (k - 4) + (k - 3) + (k - 2) := by omega
  omega

/-- The greediest 5-set summing to `3k-2` in `[1, k-2]` is `{1, 6, k-4, k-3, k-2}`. -/
lemma five_set_prod_le (k a b c d e : ℕ) (hk : 14 ≤ k)
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (he : e ≤ k - 2) (hsum : a + b + c + d + e = 3 * k - 2) :
    a.factorial * b.factorial * c.factorial * d.factorial * e.factorial ≤
      (1).factorial * (6).factorial * (k - 4).factorial * (k - 3).factorial *
        (k - 2).factorial := by
  have hb3 : 3 ≤ b := by
    by_contra hb
    have : a = 1 ∧ b = 2 := by omega
    exact five_not_12 (k := k) (x := c) (y := d) (z := e) (by omega) hcd hde he
      (by omega)
  by_cases he0 : e = k - 2
  · subst he0
    by_cases hd0 : d = k - 3
    · subst hd0
      by_cases hc0 : c = k - 4
      · subst hc0
        by_cases ha1 : a = 1
        · subst ha1
          have hb6 : b = 6 := by omega
          subst hb6
          exact le_rfl
        · have ha2 : 2 ≤ a := by omega
          have hlt := unbalance_prod (x := a) (y := b) (by omega) hab
          have ih := five_set_prod_le k (a - 1) (b + 1) (k - 4) (k - 3) (k - 2) hk
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega)
          have hmul :
              a.factorial * b.factorial * (k - 4).factorial * (k - 3).factorial *
                  (k - 2).factorial <
                (a - 1).factorial * (b + 1).factorial * (k - 4).factorial *
                  (k - 3).factorial * (k - 2).factorial := by
            have hpos : 0 < (k - 4).factorial * (k - 3).factorial * (k - 2).factorial :=
              Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
                (factorial_pos _)
            have := Nat.mul_lt_mul_of_pos_right hlt hpos
            convert this using 1 <;> ring
          exact le_of_lt (lt_of_lt_of_le hmul ih)
      · have hc : c < k - 4 := by omega
        -- Increase `c`. Decrease `a` if `a ≥ 2`, else decrease `b` (`b ≥ 3`).
        by_cases ha1 : a = 1
        · subst ha1
          have hlt := unbalance_prod (x := b) (y := c) (by omega) (by omega)
          have ih := five_set_prod_le k 1 (b - 1) (c + 1) (k - 3) (k - 2) hk
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega)
          have hmul :
              (1).factorial * b.factorial * c.factorial * (k - 3).factorial *
                  (k - 2).factorial <
                (1).factorial * (b - 1).factorial * (c + 1).factorial *
                  (k - 3).factorial * (k - 2).factorial := by
            have hpos : 0 <
                (1).factorial * (k - 3).factorial * (k - 2).factorial :=
              Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
                (factorial_pos _)
            have := Nat.mul_lt_mul_of_pos_right hlt hpos
            convert this using 1 <;> ring
          exact le_of_lt (lt_of_lt_of_le hmul ih)
        · have ha2 : 2 ≤ a := by omega
          have hlt := unbalance_prod (x := a) (y := c) (by omega) (by omega)
          have ih := five_set_prod_le k (a - 1) b (c + 1) (k - 3) (k - 2) hk
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega)
          have hmul :
              a.factorial * b.factorial * c.factorial * (k - 3).factorial *
                  (k - 2).factorial <
                (a - 1).factorial * b.factorial * (c + 1).factorial *
                  (k - 3).factorial * (k - 2).factorial := by
            have hpos : 0 < b.factorial * (k - 3).factorial * (k - 2).factorial :=
              Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
                (factorial_pos _)
            have := Nat.mul_lt_mul_of_pos_right hlt hpos
            convert this using 1 <;> ring
          exact le_of_lt (lt_of_lt_of_le hmul ih)
    · have hd : d < k - 3 := by omega
      by_cases ha1 : a = 1
      · subst ha1
        have hlt := unbalance_prod (x := b) (y := d) (by omega) (by omega)
        have ih := five_set_prod_le k 1 (b - 1) c (d + 1) (k - 2) hk
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)
        have hmul :
            (1).factorial * b.factorial * c.factorial * d.factorial *
                (k - 2).factorial <
              (1).factorial * (b - 1).factorial * c.factorial * (d + 1).factorial *
                (k - 2).factorial := by
          have hpos : 0 <
              (1).factorial * c.factorial * (k - 2).factorial :=
            Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
              (factorial_pos _)
          have := Nat.mul_lt_mul_of_pos_right hlt hpos
          convert this using 1 <;> ring
        exact le_of_lt (lt_of_lt_of_le hmul ih)
      · have ha2 : 2 ≤ a := by omega
        have hlt := unbalance_prod (x := a) (y := d) (by omega) (by omega)
        have ih := five_set_prod_le k (a - 1) b c (d + 1) (k - 2) hk
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)
        have hmul :
            a.factorial * b.factorial * c.factorial * d.factorial *
                (k - 2).factorial <
              (a - 1).factorial * b.factorial * c.factorial * (d + 1).factorial *
                (k - 2).factorial := by
          have hpos : 0 < b.factorial * c.factorial * (k - 2).factorial :=
            Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
              (factorial_pos _)
          have := Nat.mul_lt_mul_of_pos_right hlt hpos
          convert this using 1 <;> ring
        exact le_of_lt (lt_of_lt_of_le hmul ih)
  · have helt : e < k - 2 := by omega
    by_cases ha1 : a = 1
    · subst ha1
      have hlt := unbalance_prod (x := b) (y := e) (by omega) (by omega)
      have ih := five_set_prod_le k 1 (b - 1) c d (e + 1) hk
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
      have hmul :
          (1).factorial * b.factorial * c.factorial * d.factorial * e.factorial <
            (1).factorial * (b - 1).factorial * c.factorial * d.factorial *
              (e + 1).factorial := by
        have hpos : 0 < (1).factorial * c.factorial * d.factorial :=
          Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
            (factorial_pos _)
        have := Nat.mul_lt_mul_of_pos_right hlt hpos
        convert this using 1 <;> ring
      exact le_of_lt (lt_of_lt_of_le hmul ih)
    · have ha2 : 2 ≤ a := by omega
      have hlt := unbalance_prod (x := a) (y := e) (by omega) (by omega)
      have ih := five_set_prod_le k (a - 1) b c d (e + 1) hk
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hmul :
          a.factorial * b.factorial * c.factorial * d.factorial * e.factorial <
            (a - 1).factorial * b.factorial * c.factorial * d.factorial *
              (e + 1).factorial := by
        have hpos : 0 < b.factorial * c.factorial * d.factorial :=
          Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
            (factorial_pos _)
        have := Nat.mul_lt_mul_of_pos_right hlt hpos
        convert this using 1 <;> ring
      exact le_of_lt (lt_of_lt_of_le hmul ih)
termination_by (k - 2 - e, k - 3 - d, k - 4 - c, k - 5 - b, a)
decreasing_by
  all_goals (apply lex5; omega)

lemma lex6 {A B C D E F A' B' C' D' E' F' : ℕ}
    (h : A < A' ∨ A = A' ∧ (B < B' ∨ B = B' ∧ (C < C' ∨ C = C' ∧
      (D < D' ∨ D = D' ∧ (E < E' ∨ E = E' ∧ F < F'))))) :
    Prod.Lex (fun x1 x2 => x1 < x2)
      (Prod.Lex (fun x1 x2 => x1 < x2)
        (Prod.Lex (fun x1 x2 => x1 < x2)
          (Prod.Lex (fun x1 x2 => x1 < x2)
            (Prod.Lex (fun x1 x2 => x1 < x2) fun x1 x2 => x1 < x2))))
      (A, B, C, D, E, F) (A', B', C', D', E', F') := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · apply Prod.Lex.right
    rcases h with h | ⟨rfl, h⟩
    · exact Prod.Lex.left _ _ h
    · apply Prod.Lex.right
      rcases h with h | ⟨rfl, h⟩
      · exact Prod.Lex.left _ _ h
      · apply Prod.Lex.right
        rcases h with h | ⟨rfl, h⟩
        · exact Prod.Lex.left _ _ h
        · apply Prod.Lex.right
          rcases h with h | ⟨rfl, h⟩
          · exact Prod.Lex.left _ _ h
          · apply Prod.Lex.right
            exact h

/-- `{1,2,3,x,y,z}` cannot sum to `3k-2` with `3 < x < y < z ≤ k-2`. -/
lemma six_not_123 {k x y z : ℕ} (hxy : 3 < x) (hyz : x < y) (hzy : y < z)
    (hz : z ≤ k - 2) : ¬ (1 + 2 + 3 + x + y + z = 3 * k - 2) := by
  intro h
  have : x + y + z = 3 * k - 8 := by omega
  have hmax : x + y + z ≤ (k - 4) + (k - 3) + (k - 2) := by omega
  omega

set_option maxHeartbeats 800000

/-- The greediest 6-set summing to `3k-2` in `[1, k-2]` is `{1, 2, 4, k-4, k-3, k-2}`. -/
lemma six_set_prod_le (k a b c d e f : ℕ) (hk : 14 ≤ k)
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hef : e < f) (hf : f ≤ k - 2)
    (hsum : a + b + c + d + e + f = 3 * k - 2) :
    a.factorial * b.factorial * c.factorial * d.factorial * e.factorial *
        f.factorial ≤
      (1).factorial * (2).factorial * (4).factorial * (k - 4).factorial *
        (k - 3).factorial * (k - 2).factorial := by
  have hc4 : ¬ (a = 1 ∧ b = 2 ∧ c = 3) := by
    intro ⟨ha1, hb2, hc3⟩
    subst ha1; subst hb2; subst hc3
    exact six_not_123 (k := k) (x := d) (y := e) (z := f) (by omega) hde hef hf hsum
  by_cases hf0 : f = k - 2
  · subst hf0
    by_cases he0 : e = k - 3
    · subst he0
      by_cases hd0 : d = k - 4
      · subst hd0
        have habc : a + b + c = 7 := by omega
        have ha1 : a = 1 := by omega
        have hb2 : b = 2 := by omega
        have hc4' : c = 4 := by omega
        subst ha1; subst hb2; subst hc4'
        exact le_rfl
      · have hd : d < k - 4 := by omega
        by_cases ha1 : a = 1
        · subst ha1
          by_cases hb2 : b = 2
          · subst hb2
            have hcge : 4 ≤ c := by omega
            have hlt := unbalance_prod (x := c) (y := d) (by omega) (by omega)
            have ih := six_set_prod_le k 1 2 (c - 1) (d + 1) (k - 3) (k - 2) hk
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega)
            have hmul :
                (1).factorial * (2).factorial * c.factorial * d.factorial *
                    (k - 3).factorial * (k - 2).factorial <
                  (1).factorial * (2).factorial * (c - 1).factorial *
                    (d + 1).factorial * (k - 3).factorial * (k - 2).factorial := by
              have hpos : 0 <
                  (1).factorial * (2).factorial * (k - 3).factorial * (k - 2).factorial :=
                Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
                  (factorial_pos _)) (factorial_pos _)
              have := Nat.mul_lt_mul_of_pos_right hlt hpos
              convert this using 1 <;> ring
            exact le_of_lt (lt_of_lt_of_le hmul ih)
          · have hb3 : 3 ≤ b := by omega
            have hlt := unbalance_prod (x := b) (y := d) (by omega) (by omega)
            have ih := six_set_prod_le k 1 (b - 1) c (d + 1) (k - 3) (k - 2) hk
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega)
            have hmul :
                (1).factorial * b.factorial * c.factorial * d.factorial *
                    (k - 3).factorial * (k - 2).factorial <
                  (1).factorial * (b - 1).factorial * c.factorial *
                    (d + 1).factorial * (k - 3).factorial * (k - 2).factorial := by
              have hpos : 0 <
                  (1).factorial * c.factorial * (k - 3).factorial * (k - 2).factorial :=
                Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
                  (factorial_pos _)) (factorial_pos _)
              have := Nat.mul_lt_mul_of_pos_right hlt hpos
              convert this using 1 <;> ring
            exact le_of_lt (lt_of_lt_of_le hmul ih)
        · have ha2 : 2 ≤ a := by omega
          have hlt := unbalance_prod (x := a) (y := d) (by omega) (by omega)
          have ih := six_set_prod_le k (a - 1) b c (d + 1) (k - 3) (k - 2) hk
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega)
          have hmul :
              a.factorial * b.factorial * c.factorial * d.factorial *
                  (k - 3).factorial * (k - 2).factorial <
                (a - 1).factorial * b.factorial * c.factorial *
                  (d + 1).factorial * (k - 3).factorial * (k - 2).factorial := by
            have hpos : 0 <
                b.factorial * c.factorial * (k - 3).factorial * (k - 2).factorial :=
              Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
                (factorial_pos _)) (factorial_pos _)
            have := Nat.mul_lt_mul_of_pos_right hlt hpos
            convert this using 1 <;> ring
          exact le_of_lt (lt_of_lt_of_le hmul ih)
    · have he : e < k - 3 := by omega
      by_cases ha1 : a = 1
      · subst ha1
        by_cases hb2 : b = 2
        · subst hb2
          have hcge : 4 ≤ c := by omega
          have hlt := unbalance_prod (x := c) (y := e) (by omega) (by omega)
          have ih := six_set_prod_le k 1 2 (c - 1) d (e + 1) (k - 2) hk
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega)
          have hmul :
              (1).factorial * (2).factorial * c.factorial * d.factorial * e.factorial *
                  (k - 2).factorial <
                (1).factorial * (2).factorial * (c - 1).factorial * d.factorial *
                  (e + 1).factorial * (k - 2).factorial := by
            have hpos : 0 <
                (1).factorial * (2).factorial * d.factorial * (k - 2).factorial :=
              Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
                (factorial_pos _)) (factorial_pos _)
            have := Nat.mul_lt_mul_of_pos_right hlt hpos
            convert this using 1 <;> ring
          exact le_of_lt (lt_of_lt_of_le hmul ih)
        · have hb3 : 3 ≤ b := by omega
          have hlt := unbalance_prod (x := b) (y := e) (by omega) (by omega)
          have ih := six_set_prod_le k 1 (b - 1) c d (e + 1) (k - 2) hk
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega)
          have hmul :
              (1).factorial * b.factorial * c.factorial * d.factorial * e.factorial *
                  (k - 2).factorial <
                (1).factorial * (b - 1).factorial * c.factorial * d.factorial *
                  (e + 1).factorial * (k - 2).factorial := by
            have hpos : 0 <
                (1).factorial * c.factorial * d.factorial * (k - 2).factorial :=
              Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
                (factorial_pos _)) (factorial_pos _)
            have := Nat.mul_lt_mul_of_pos_right hlt hpos
            convert this using 1 <;> ring
          exact le_of_lt (lt_of_lt_of_le hmul ih)
      · have ha2 : 2 ≤ a := by omega
        have hlt := unbalance_prod (x := a) (y := e) (by omega) (by omega)
        have ih := six_set_prod_le k (a - 1) b c d (e + 1) (k - 2) hk
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        have hmul :
            a.factorial * b.factorial * c.factorial * d.factorial * e.factorial *
                (k - 2).factorial <
              (a - 1).factorial * b.factorial * c.factorial * d.factorial *
                (e + 1).factorial * (k - 2).factorial := by
          have hpos : 0 <
              b.factorial * c.factorial * d.factorial * (k - 2).factorial :=
            Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
              (factorial_pos _)) (factorial_pos _)
          have := Nat.mul_lt_mul_of_pos_right hlt hpos
          convert this using 1 <;> ring
        exact le_of_lt (lt_of_lt_of_le hmul ih)
  · have hflt : f < k - 2 := by omega
    by_cases ha1 : a = 1
    · subst ha1
      by_cases hb2 : b = 2
      · subst hb2
        have hcge : 4 ≤ c := by omega
        have hlt := unbalance_prod (x := c) (y := f) (by omega) (by omega)
        have ih := six_set_prod_le k 1 2 (c - 1) d e (f + 1) hk
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        have hmul :
            (1).factorial * (2).factorial * c.factorial * d.factorial * e.factorial *
                f.factorial <
              (1).factorial * (2).factorial * (c - 1).factorial * d.factorial *
                e.factorial * (f + 1).factorial := by
          have hpos : 0 <
              (1).factorial * (2).factorial * d.factorial * e.factorial :=
            Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
              (factorial_pos _)) (factorial_pos _)
          have := Nat.mul_lt_mul_of_pos_right hlt hpos
          convert this using 1 <;> ring
        exact le_of_lt (lt_of_lt_of_le hmul ih)
      · have hb3 : 3 ≤ b := by omega
        have hlt := unbalance_prod (x := b) (y := f) (by omega) (by omega)
        have ih := six_set_prod_le k 1 (b - 1) c d e (f + 1) hk
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        have hmul :
            (1).factorial * b.factorial * c.factorial * d.factorial * e.factorial *
                f.factorial <
              (1).factorial * (b - 1).factorial * c.factorial * d.factorial *
                e.factorial * (f + 1).factorial := by
          have hpos : 0 <
              (1).factorial * c.factorial * d.factorial * e.factorial :=
            Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
              (factorial_pos _)) (factorial_pos _)
          have := Nat.mul_lt_mul_of_pos_right hlt hpos
          convert this using 1 <;> ring
        exact le_of_lt (lt_of_lt_of_le hmul ih)
    · have ha2 : 2 ≤ a := by omega
      have hlt := unbalance_prod (x := a) (y := f) (by omega) (by omega)
      have ih := six_set_prod_le k (a - 1) b c d e (f + 1) hk
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hmul :
          a.factorial * b.factorial * c.factorial * d.factorial * e.factorial *
              f.factorial <
            (a - 1).factorial * b.factorial * c.factorial * d.factorial *
              e.factorial * (f + 1).factorial := by
        have hpos : 0 <
            b.factorial * c.factorial * d.factorial * e.factorial :=
          Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _))
            (factorial_pos _)) (factorial_pos _)
        have := Nat.mul_lt_mul_of_pos_right hlt hpos
        convert this using 1 <;> ring
      exact le_of_lt (lt_of_lt_of_le hmul ih)
termination_by (k - 2 - f, k - 3 - e, k - 4 - d, k - 5 - c, k - 6 - b, a)
decreasing_by
  all_goals (apply lex6; omega)



lemma list4_of_length {l : List ℕ} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  match l with
  | [a, b, c, d] => exact ⟨a, b, c, d, rfl⟩
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | [_, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ => simp at h

lemma sort_eq_quad {S : Finset ℕ} (hS : S.card = 4) :
    ∃ a b c d, a < b ∧ b < c ∧ c < d ∧ S.sort (· ≤ ·) = [a, b, c, d] := by
  obtain ⟨a, b, c, d, hl⟩ := list4_of_length (by rw [length_sort, hS] : (S.sort (· ≤ ·)).length = 4)
  have hpw : List.Pairwise (· ≤ ·) [a, b, c, d] := by
    rw [← hl]; exact pairwise_sort S (· ≤ ·)
  have hnd : [a, b, c, d].Nodup := by
    rw [← hl]; exact sort_nodup S (· ≤ ·)
  have hab : a < b := by
    have : a ≤ b := by simpa using (List.pairwise_cons.mp hpw).1 b (by simp)
    have : a ≠ b := by intro h; subst h; simp [List.nodup_cons] at hnd
    omega
  have hbc : b < c := by
    have hpw' := (List.pairwise_cons.mp hpw).2
    have : b ≤ c := by simpa using (List.pairwise_cons.mp hpw').1 c (by simp)
    have : b ≠ c := by intro h; subst h; simp [List.nodup_cons] at hnd
    omega
  have hcd : c < d := by
    have hpw' := (List.pairwise_cons.mp hpw).2
    have hpw'' := (List.pairwise_cons.mp hpw').2
    have : c ≤ d := by simpa using (List.pairwise_cons.mp hpw'').1 d (by simp)
    have : c ≠ d := by intro h; subst h; simp [List.nodup_cons] at hnd
    omega
  exact ⟨a, b, c, d, hab, hbc, hcd, hl⟩

lemma four_finset_prod_le (k : ℕ) (hk : 14 ≤ k) (S : Finset ℕ)
    (hS : S ⊆ Icc 1 (k - 2)) (hcard : S.card = 4)
    (hsum : ∑ i ∈ S, i = 3 * k - 2) :
    sWeight S ≤
      (7).factorial * (k - 4).factorial * (k - 3).factorial * (k - 2).factorial := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hsl⟩ := sort_eq_quad hcard
  have hmem : ∀ x, x ∈ S ↔ x = a ∨ x = b ∨ x = c ∨ x = d := by
    intro x
    rw [← mem_sort (s := S) (r := (· ≤ ·)), hsl]
    simp
  have haS : a ∈ S := (hmem a).mpr (Or.inl rfl)
  have hdS : d ∈ S := (hmem d).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have ha1 : 1 ≤ a := (mem_Icc.mp (hS haS)).1
  have hdle : d ≤ k - 2 := (mem_Icc.mp (hS hdS)).2
  have hseq : S = {a, b, c, d} := by
    ext x
    simp [hmem]
  have hsum' : a + b + c + d = 3 * k - 2 := by
    have : ∑ i ∈ ({a, b, c, d} : Finset ℕ), i = a + b + c + d := by
      simp [hab.ne, (hab.trans hbc).ne, (hab.trans (hbc.trans hcd)).ne,
        hbc.ne, (hbc.trans hcd).ne, hcd.ne]
      ring
    rw [← hseq] at this
    omega
  have hw : sWeight S = a.factorial * b.factorial * c.factorial * d.factorial := by
    rw [hseq]
    simp [sWeight, prod_insert, hab.ne, (hab.trans hbc).ne,
      (hab.trans (hbc.trans hcd)).ne, hbc.ne, (hbc.trans hcd).ne, hcd.ne]
    ring
  rw [hw]
  exact four_set_prod_le k a b c d hk ha1 hab hbc hcd hdle hsum'

lemma list5_of_length {l : List ℕ} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  match l with
  | [a, b, c, d, e] => exact ⟨a, b, c, d, e, rfl⟩
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | [_, _, _] => simp at h
  | [_, _, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ => simp at h

lemma sort_eq_five {S : Finset ℕ} (hS : S.card = 5) :
    ∃ a b c d e, a < b ∧ b < c ∧ c < d ∧ d < e ∧
      S.sort (· ≤ ·) = [a, b, c, d, e] := by
  obtain ⟨a, b, c, d, e, hl⟩ :=
    list5_of_length (by rw [length_sort, hS] : (S.sort (· ≤ ·)).length = 5)
  have hpw : List.Pairwise (· ≤ ·) [a, b, c, d, e] := by
    rw [← hl]; exact pairwise_sort S (· ≤ ·)
  have hnd : [a, b, c, d, e].Nodup := by
    rw [← hl]; exact sort_nodup S (· ≤ ·)
  have lt_of_le_nd {x y : ℕ} {rest : List ℕ}
      (hle : x ≤ y) (hnd' : (x :: y :: rest).Nodup) : x < y := by
    have : x ≠ y := by intro h; subst h; simp [List.nodup_cons] at hnd'
    omega
  have hab : a < b := by
    have : a ≤ b := by simpa using (List.pairwise_cons.mp hpw).1 b (by simp)
    exact lt_of_le_nd this hnd
  have hbc : b < c := by
    have hpw' := (List.pairwise_cons.mp hpw).2
    have : b ≤ c := by simpa using (List.pairwise_cons.mp hpw').1 c (by simp)
    exact lt_of_le_nd this (List.Nodup.of_cons hnd)
  have hcd : c < d := by
    have hpw' := (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).2
    have : c ≤ d := by simpa using (List.pairwise_cons.mp hpw').1 d (by simp)
    exact lt_of_le_nd this (List.Nodup.of_cons (List.Nodup.of_cons hnd))
  have hde : d < e := by
    have hpw' :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).2).2
    have : d ≤ e := by simpa using (List.pairwise_cons.mp hpw').1 e (by simp)
    exact lt_of_le_nd this
      (List.Nodup.of_cons (List.Nodup.of_cons (List.Nodup.of_cons hnd)))
  exact ⟨a, b, c, d, e, hab, hbc, hcd, hde, hl⟩

lemma five_finset_prod_le (k : ℕ) (hk : 14 ≤ k) (S : Finset ℕ)
    (hS : S ⊆ Icc 1 (k - 2)) (hcard : S.card = 5)
    (hsum : ∑ i ∈ S, i = 3 * k - 2) :
    sWeight S ≤
      (1).factorial * (6).factorial * (k - 4).factorial * (k - 3).factorial *
        (k - 2).factorial := by
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, hsl⟩ := sort_eq_five hcard
  have hmem : ∀ x, x ∈ S ↔ x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
    intro x
    rw [← mem_sort (s := S) (r := (· ≤ ·)), hsl]; simp
  have haS : a ∈ S := (hmem a).mpr (Or.inl rfl)
  have heS : e ∈ S := (hmem e).mpr (by tauto)
  have ha1 : 1 ≤ a := (mem_Icc.mp (hS haS)).1
  have hele : e ≤ k - 2 := (mem_Icc.mp (hS heS)).2
  have hseq : S = {a, b, c, d, e} := by
    ext x; simp [hmem]
  have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e := by
    refine ⟨hab.ne, (hab.trans hbc).ne, (hab.trans (hbc.trans hcd)).ne,
      (hab.trans (hbc.trans (hcd.trans hde))).ne, hbc.ne, (hbc.trans hcd).ne,
      (hbc.trans (hcd.trans hde)).ne, hcd.ne, (hcd.trans hde).ne, hde.ne⟩
  have hsum' : a + b + c + d + e = 3 * k - 2 := by
    have : ∑ i ∈ ({a, b, c, d, e} : Finset ℕ), i = a + b + c + d + e := by
      simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1,
        hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.2.1,
        hne.2.2.2.2.2.2.2.2.2]
      ring
    rw [← hseq] at this; omega
  have hw : sWeight S =
      a.factorial * b.factorial * c.factorial * d.factorial * e.factorial := by
    rw [hseq]
    simp [sWeight, prod_insert, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1,
      hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.2.1,
      hne.2.2.2.2.2.2.2.2.2]
    ring
  rw [hw]
  exact five_set_prod_le k a b c d e hk ha1 hab hbc hcd hde hele hsum'


lemma list6_of_length {l : List ℕ} (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  match l with
  | [a, b, c, d, e, f] => exact ⟨a, b, c, d, e, f, rfl⟩
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | [_, _, _] => simp at h
  | [_, _, _, _] => simp at h
  | [_, _, _, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => simp at h

lemma pairwise_lt6 {a b c d e f : ℕ}
    (hpw : List.Pairwise (· ≤ ·) [a, b, c, d, e, f])
    (hnd : [a, b, c, d, e, f].Nodup) :
    a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f := by
  have h1 : a ≤ b := by simpa using (List.pairwise_cons.mp hpw).1 b (by simp)
  have n1 : a ≠ b := by intro h; subst h; simp [List.nodup_cons] at hnd
  have hpw2 := (List.pairwise_cons.mp hpw).2
  have hnd2 := List.Nodup.of_cons hnd
  have h2 : b ≤ c := by simpa using (List.pairwise_cons.mp hpw2).1 c (by simp)
  have n2 : b ≠ c := by intro h; subst h; simp [List.nodup_cons] at hnd2
  have hpw3 := (List.pairwise_cons.mp hpw2).2
  have hnd3 := List.Nodup.of_cons hnd2
  have h3 : c ≤ d := by simpa using (List.pairwise_cons.mp hpw3).1 d (by simp)
  have n3 : c ≠ d := by intro h; subst h; simp [List.nodup_cons] at hnd3
  have hpw4 := (List.pairwise_cons.mp hpw3).2
  have hnd4 := List.Nodup.of_cons hnd3
  have h4 : d ≤ e := by simpa using (List.pairwise_cons.mp hpw4).1 e (by simp)
  have n4 : d ≠ e := by intro h; subst h; simp [List.nodup_cons] at hnd4
  have hpw5 := (List.pairwise_cons.mp hpw4).2
  have hnd5 := List.Nodup.of_cons hnd4
  have h5 : e ≤ f := by simpa using (List.pairwise_cons.mp hpw5).1 f (by simp)
  have n5 : e ≠ f := by intro h; subst h; simp [List.nodup_cons] at hnd5
  omega

lemma sort_eq_six {S : Finset ℕ} (hS : S.card = 6) :
    ∃ a b c d e f, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧
      S.sort (· ≤ ·) = [a, b, c, d, e, f] := by
  obtain ⟨a, b, c, d, e, f, hl⟩ :=
    list6_of_length (by rw [length_sort, hS] : (S.sort (· ≤ ·)).length = 6)
  have hpw : List.Pairwise (· ≤ ·) [a, b, c, d, e, f] := by
    rw [← hl]; exact pairwise_sort S (· ≤ ·)
  have hnd : [a, b, c, d, e, f].Nodup := by
    rw [← hl]; exact sort_nodup S (· ≤ ·)
  obtain ⟨hab, hbc, hcd, hde, hef⟩ := pairwise_lt6 hpw hnd
  exact ⟨a, b, c, d, e, f, hab, hbc, hcd, hde, hef, hl⟩

lemma six_finset_prod_le (k : ℕ) (hk : 14 ≤ k) (S : Finset ℕ)
    (hS : S ⊆ Icc 1 (k - 2)) (hcard : S.card = 6)
    (hsum : ∑ i ∈ S, i = 3 * k - 2) :
    sWeight S ≤
      (1).factorial * (2).factorial * (4).factorial * (k - 4).factorial *
        (k - 3).factorial * (k - 2).factorial := by
  obtain ⟨a, b, c, d, e, f, hab, hbc, hcd, hde, hef, hsl⟩ := sort_eq_six hcard
  have hmem : ∀ x, x ∈ S ↔ x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f := by
    intro x
    rw [← mem_sort (s := S) (r := (· ≤ ·)), hsl]; simp
  have haS : a ∈ S := (hmem a).mpr (Or.inl rfl)
  have hfS : f ∈ S := (hmem f).mpr (by tauto)
  have ha1 : 1 ≤ a := (mem_Icc.mp (hS haS)).1
  have hfle : f ≤ k - 2 := (mem_Icc.mp (hS hfS)).2
  have hseq : S = {a, b, c, d, e, f} := by
    ext x; simp [hmem]
  have nAB : a ≠ b := hab.ne
  have nAC : a ≠ c := (hab.trans hbc).ne
  have nAD : a ≠ d := (hab.trans (hbc.trans hcd)).ne
  have nAE : a ≠ e := (hab.trans (hbc.trans (hcd.trans hde))).ne
  have nAF : a ≠ f := (hab.trans (hbc.trans (hcd.trans (hde.trans hef)))).ne
  have nBC : b ≠ c := hbc.ne
  have nBD : b ≠ d := (hbc.trans hcd).ne
  have nBE : b ≠ e := (hbc.trans (hcd.trans hde)).ne
  have nBF : b ≠ f := (hbc.trans (hcd.trans (hde.trans hef))).ne
  have nCD : c ≠ d := hcd.ne
  have nCE : c ≠ e := (hcd.trans hde).ne
  have nCF : c ≠ f := (hcd.trans (hde.trans hef)).ne
  have nDE : d ≠ e := hde.ne
  have nDF : d ≠ f := (hde.trans hef).ne
  have nEF : e ≠ f := hef.ne
  have hsum' : a + b + c + d + e + f = 3 * k - 2 := by
    have : ∑ i ∈ ({a, b, c, d, e, f} : Finset ℕ), i = a + b + c + d + e + f := by
      simp [nAB, nAC, nAD, nAE, nAF, nBC, nBD, nBE, nBF, nCD, nCE, nCF, nDE, nDF, nEF]
      ring
    rw [← hseq] at this; omega
  have hw : sWeight S =
      a.factorial * b.factorial * c.factorial * d.factorial * e.factorial *
        f.factorial := by
    rw [hseq]
    simp [sWeight, prod_insert, nAB, nAC, nAD, nAE, nAF, nBC, nBD, nBE, nBF,
      nCD, nCE, nCF, nDE, nDF, nEF]
    ring
  rw [hw]
  exact six_set_prod_le k a b c d e f hk ha1 hab hbc hcd hde hef hfle hsum'

lemma card_Icc_one (m : ℕ) : #(Icc 1 m) = m := by
  rw [Nat.card_Icc]; omega

lemma W_eq_sum_card (m n : ℕ) :
    W n m =
      ∑ r ∈ range (m + 1),
        ∑ S ∈ ((Icc 1 m).powersetCard r).filter (fun S => ∑ i ∈ S, i = n),
          sWeight S := by
  rw [W_eq_Wsum]
  unfold Wsum
  rw [sum_powerset, card_Icc_one]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [sum_filter]


def remTarget (k : ℕ) : ℕ :=
  k.factorial * (k - 5) * (k - 4).factorial * (k + 1).factorial

lemma choose4_mul (n : ℕ) :
    n.choose 4 * 24 = n.descFactorial 4 := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
  rfl

lemma desc4 (n : ℕ) : n.descFactorial 4 = n * (n - 1) * (n - 2) * (n - 3) := by
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ,
    Nat.descFactorial_succ]
  simp [Nat.descFactorial]
  ring

lemma choose4_prod (n : ℕ) :
    n.choose 4 * 24 = n * (n - 1) * (n - 2) * (n - 3) := by
  rw [choose4_mul, desc4]

lemma fact_succ_eq (n : ℕ) (h : 1 ≤ n) :
    n.factorial = n * (n - 1).factorial := by
  cases n with | zero => omega | succ n => simp [factorial]



lemma poly4_lt (k : ℕ) (hk : 83 ≤ k) :
    40320 * (k - 3) * (k - 4) < 24 * k * k * (k - 1) * (k - 1) * (k + 1) := by
  have hL : 40320 * (k - 3) * (k - 4) ≤ 40320 * k * k := by
    have hmul : (k - 3) * (k - 4) ≤ k * k :=
      Nat.mul_le_mul (Nat.sub_le k 3) (Nat.sub_le k 4)
    have := Nat.mul_le_mul_left 40320 hmul
    convert this using 1 <;> ring
  have h82 : 82 ≤ k - 1 := by omega
  have h84 : 84 ≤ k + 1 := by omega
  have hR : 24 * k * k * 82 * 82 * 84 ≤
      24 * k * k * (k - 1) * (k - 1) * (k + 1) := by
    have hmul : 82 * 82 * 84 ≤ (k - 1) * (k - 1) * (k + 1) :=
      Nat.mul_le_mul h82 (Nat.mul_le_mul h82 h84)
    have := Nat.mul_le_mul_left (24 * k * k) hmul
    convert this using 1 <;> ring
  have hcmp : 40320 * k * k < 24 * k * k * 82 * 82 * 84 := by
    have hkpos : 0 < k * k := Nat.mul_pos (by omega) (by omega)
    have : 40320 < 24 * 82 * 82 * 84 := by native_decide
    have := Nat.mul_lt_mul_of_pos_right this hkpos
    convert this using 1 <;> ring
  exact lt_of_le_of_lt hL (lt_of_lt_of_le hcmp hR)
