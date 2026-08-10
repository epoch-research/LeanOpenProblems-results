import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs

noncomputable def U (n k : ℕ) : ℤ :=
  if k + 2 ≤ n then (k:ℤ) * U n (k+1) - ((k:ℤ)+1) * U n (k+2)
  else if k + 1 = n then 5*(n:ℤ) - 4
  else 4
termination_by n - k
decreasing_by all_goals omega

lemma U_rec {n k : ℕ} (h : k + 2 ≤ n) :
    U n k = (k:ℤ) * U n (k+1) - ((k:ℤ)+1) * U n (k+2) := by
  rw [U]; simp [if_pos h]

lemma U_base1 {n k : ℕ} (h : k + 1 = n) : U n k = 5*(n:ℤ) - 4 := by
  rw [U]
  have : ¬ (k + 2 ≤ n) := by omega
  simp [if_neg this, if_pos h]

lemma U_n {n : ℕ} (hn : 1 ≤ n) : U n n = 4 := by
  rw [U]
  have h1 : ¬ (n + 2 ≤ n) := by omega
  have h2 : ¬ (n + 1 = n) := by omega
  simp [if_neg h1, if_neg h2]

example : U 8 8 = 4 := by rw [U_n]; omega
example : U 8 7 = 36 := by rw [U_base1 (by omega)]; norm_num

-- invariant: (k-1)U_k - k(k-2)U_{k+1} = n^2+2n-4 for 2 ≤ k ≤ n-1
lemma invariant {n : ℕ} (hn : 3 ≤ n) :
    ∀ k, 2 ≤ k → k ≤ n - 1 →
      ((k:ℤ)-1)*U n k - (k:ℤ)*((k:ℤ)-2)*U n (k+1) = (n:ℤ)^2+2*(n:ℤ)-4 := by
  have aux : ∀ m k, n - k = m → 2 ≤ k → k ≤ n - 1 →
      ((k:ℤ)-1)*U n k - (k:ℤ)*((k:ℤ)-2)*U n (k+1) = (n:ℤ)^2+2*(n:ℤ)-4 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hm hk2 hkn
      by_cases hkeq : k = n - 1
      · -- base case k = n-1
        subst hkeq
        have h1 : (n - 1) + 1 = n := by omega
        rw [U_base1 h1, h1, U_n (by omega)]
        have hc : ((n - 1 : ℕ):ℤ) = (n:ℤ) - 1 := by
          rw [Nat.cast_sub (by omega)]; norm_num
        rw [hc]
        ring
      · -- recursive: k < n-1, so k+2 ≤ n
        have hk1 : k ≤ n - 2 := by omega
        have hrec : k + 2 ≤ n := by omega
        -- IH at k+1
        have hihk1 : ((k+1:ℤ)-1)*U n (k+1) - ((k+1:ℤ))*(((k+1:ℤ))-2)*U n (k+2)
            = (n:ℤ)^2+2*(n:ℤ)-4 := by
          have := ih (n - (k+1)) (by omega) (k+1) rfl (by omega) (by omega)
          push_cast at this ⊢
          convert this using 2 <;> ring
        rw [U_rec hrec]
        push_cast at hihk1 ⊢
        ring_nf
        ring_nf at hihk1
        linarith [hihk1]
  intro k hk2 hkn
  exact aux (n - k) k rfl hk2 hkn

lemma u2_pos {n : ℕ} (hn : 3 ≤ n) : 0 < (n:ℤ)^2+2*(n:ℤ)-4 := by
  have : (3:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
  nlinarith

lemma U_pos {n : ℕ} (hn : 3 ≤ n) :
    ∀ k, 2 ≤ k → k ≤ n → 0 < U n k := by
  have aux : ∀ m k, n - k = m → 2 ≤ k → k ≤ n → 0 < U n k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hm hk2 hkn
      by_cases hkeq : k = n
      · subst hkeq; rw [U_n (by omega)]; norm_num
      · -- k < n, so 2 ≤ k ≤ n-1
        have hkn1 : k ≤ n - 1 := by omega
        have hU1 : 0 < U n (k+1) := ih (n - (k+1)) (by omega) (k+1) rfl (by omega) (by omega)
        have hinv := invariant hn k hk2 hkn1
        -- (k-1)U_k = u2 + k(k-2)U_{k+1}
        have hu2 := u2_pos hn
        have hkpos : (1:ℤ) ≤ (k:ℤ) - 1 := by
          have : (2:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk2
          linarith
        have hk2nonneg : (0:ℤ) ≤ (k:ℤ)*((k:ℤ)-2) := by
          have : (2:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk2
          nlinarith
        -- from invariant: (k-1)*U_k = u2 + k(k-2)*U_{k+1}
        have key : ((k:ℤ)-1) * U n k = ((n:ℤ)^2+2*(n:ℤ)-4) + (k:ℤ)*((k:ℤ)-2)*U n (k+1) := by
          linarith [hinv]
        nlinarith [mul_nonneg hk2nonneg (le_of_lt hU1), key, hu2, hkpos]
  intro k hk2 hkn
  exact aux (n - k) k rfl hk2 hkn

lemma U2_eq {n : ℕ} (hn : 3 ≤ n) : U n 2 = (n:ℤ)^2+2*(n:ℤ)-4 := by
  have hinv := invariant hn 2 (by omega) (by omega)
  simp at hinv
  linarith [hinv]


lemma continued_fraction_denominator_eq_U {n : ℕ} (hn : 3 ≤ n) :
    ∀ k, 2 ≤ k → k ≤ n - 1 → continued_fraction_denominator n k = (U n k : ℚ) / (U n (k+1) : ℚ) := by
  have aux : ∀ m k, n - k = m → 2 ≤ k → k ≤ n - 1 →
      continued_fraction_denominator n k = (U n k : ℚ) / (U n (k+1) : ℚ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hm hk2 hkn
      have hnn : ¬ (n ≤ 2) := by omega
      by_cases hkeq : k = n - 1
      · subst hkeq
        rw [continued_fraction_denominator]
        simp only [if_neg hnn, if_pos (show 2 ≤ n - 1 ∧ n - 1 ≤ n - 1 from ⟨hk2, hkn⟩),
          if_pos rfl]
        have h1 : (n - 1) + 1 = n := by omega
        rw [U_base1 h1, h1, U_n (by omega)]
        have hc : ((n - 1 : ℕ):ℤ) = (n:ℤ) - 1 := by
          rw [Nat.cast_sub (by omega)]; norm_num
        push_cast [hc]
        have hcn : ((n - 1 : ℕ):ℚ) = (n:ℚ) - 1 := by
          rw [Nat.cast_sub (by omega)]; norm_num
        rw [hcn]
        ring
      · -- 2 ≤ k < n-1
        have hrec : k + 2 ≤ n := by omega
        have hk1 : k + 1 ≤ n - 1 := by omega
        have hihk1 : continued_fraction_denominator n (k+1) = (U n (k+1) : ℚ) / (U n (k+2) : ℚ) :=
          ih (n - (k+1)) (by omega) (k+1) rfl (by omega) hk1
        rw [continued_fraction_denominator]
        simp only [if_neg hnn, if_pos (show 2 ≤ k ∧ k ≤ n - 1 from ⟨hk2, hkn⟩), if_neg hkeq]
        rw [hihk1]
        have hU1 : 0 < U n (k+1) := U_pos hn (k+1) (by omega) (by omega)
        have hU2 : 0 < U n (k+2) := U_pos hn (k+2) (by omega) (by omega)
        have hU1q : (U n (k+1) : ℚ) ≠ 0 := by exact_mod_cast hU1.ne'
        have hU2q : (U n (k+2) : ℚ) ≠ 0 := by exact_mod_cast hU2.ne'
        rw [U_rec hrec]
        push_cast
        rw [div_div_eq_mul_div]
        field_simp
  intro k hk2 hkn
  exact aux (n - k) k rfl hk2 hkn

noncomputable def Sig (n k : ℕ) : ℤ :=
  if n ≤ k then 0 else (Nat.factorial (k-3) : ℤ) + Sig n (k+1)
termination_by n - k
decreasing_by omega

lemma Sig_rec {n k : ℕ} (h : k < n) : Sig n k = (Nat.factorial (k-3) : ℤ) + Sig n (k+1) := by
  rw [Sig]; simp [if_neg (by omega : ¬ n ≤ k)]

lemma Sig_base {n k : ℕ} (h : n ≤ k) : Sig n k = 0 := by
  rw [Sig]; simp [if_pos h]

lemma factstep {k : ℕ} (h : 3 ≤ k) :
    Nat.factorial (k-1) = (k-1)*((k-2)*Nat.factorial (k-3)) := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 3 := ⟨k-3, by omega⟩
  simp only [Nat.add_sub_cancel, show a+3-1 = a+2 from by omega, show a+3-2 = a+1 from by omega]
  rw [Nat.factorial_succ, Nat.factorial_succ]


lemma factsucc {m : ℕ} (h : 1 ≤ m) : Nat.factorial m = m * Nat.factorial (m-1) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m-1, by omega⟩
  simp [Nat.factorial_succ]

lemma factstepZ {k : ℕ} (h : 3 ≤ k) :
    ((Nat.factorial (k-1)):ℤ) = ((k:ℤ)-1)*(((k:ℤ)-2)*((Nat.factorial (k-3)):ℤ)) := by
  have hb := factstep h
  have e1 : ((k-1:ℕ):ℤ) = (k:ℤ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have e2 : ((k-2:ℕ):ℤ) = (k:ℤ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  calc ((Nat.factorial (k-1)):ℤ)
      = (((k-1)*((k-2)*Nat.factorial (k-3)):ℕ):ℤ) := by rw [hb]
    _ = ((k-1:ℕ):ℤ)*(((k-2:ℕ):ℤ)*((Nat.factorial (k-3)):ℤ)) := by push_cast; ring
    _ = ((k:ℤ)-1)*(((k:ℤ)-2)*((Nat.factorial (k-3)):ℤ)) := by rw [e1,e2]

lemma factsuccZ {m : ℕ} (h : 1 ≤ m) :
    ((Nat.factorial m):ℤ) = (m:ℤ)*((Nat.factorial (m-1)):ℤ) := by
  have hb := factsucc h
  calc ((Nat.factorial m):ℤ) = (((m)*Nat.factorial (m-1):ℕ):ℤ) := by rw [← hb]
    _ = (m:ℤ)*((Nat.factorial (m-1)):ℤ) := by push_cast; ring

lemma Qident {n : ℕ} (hn : 3 ≤ n) :
    ∀ k, 3 ≤ k → k ≤ n →
      ((Nat.factorial (k-1)):ℤ) * U n k
        = ((k:ℤ)-2) * (4*((n:ℤ)-1)*((Nat.factorial (n-3)):ℤ)
            + ((n:ℤ)^2+2*(n:ℤ)-4) * Sig n k) := by
  have aux : ∀ m k, n - k = m → 3 ≤ k → k ≤ n →
      ((Nat.factorial (k-1)):ℤ) * U n k
        = ((k:ℤ)-2) * (4*((n:ℤ)-1)*((Nat.factorial (n-3)):ℤ)
            + ((n:ℤ)^2+2*(n:ℤ)-4) * Sig n k) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hm hk3 hkn
      by_cases hkeq : k = n
      · -- base
        subst hkeq
        rw [Sig_base (le_refl k), U_n (by omega)]
        rw [factstepZ (by omega)]
        push_cast
        ring
      · -- step: k < n
        have hkn1 : k < n := by omega
        have hf3 : ((Nat.factorial (k-3)):ℤ) = ((Nat.factorial (k-3)):ℤ) := rfl
        -- IH at k+1
        have hih : ((Nat.factorial k):ℤ) * U n (k+1)
            = (((k:ℤ)+1)-2) * (4*((n:ℤ)-1)*((Nat.factorial (n-3)):ℤ)
                + ((n:ℤ)^2+2*(n:ℤ)-4) * Sig n (k+1)) := by
          have := ih (n - (k+1)) (by omega) (k+1) rfl (by omega) (by omega)
          simpa using this
        -- factorial relations
        have hfk : ((Nat.factorial k):ℤ) = (k:ℤ)*(((k:ℤ)-1)*(((k:ℤ)-2)*((Nat.factorial (k-3)):ℤ))) := by
          rw [factsuccZ (by omega : 1 ≤ k),
            show ((Nat.factorial (k-1)):ℤ) = ((k:ℤ)-1)*(((k:ℤ)-2)*((Nat.factorial (k-3)):ℤ)) from factstepZ (by omega)]
        -- cancel (k-1)
        have hk1ne : ((k:ℤ)-1) ≠ 0 := by
          have : (3:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk3
          intro hh; linarith
        have hHprime : (k:ℤ)*(((k:ℤ)-2)*((Nat.factorial (k-3)):ℤ)) * U n (k+1)
            = 4*((n:ℤ)-1)*((Nat.factorial (n-3)):ℤ) + ((n:ℤ)^2+2*(n:ℤ)-4) * Sig n (k+1) := by
          apply mul_left_cancel₀ hk1ne
          rw [hfk] at hih
          linear_combination hih
        -- invariant at k
        have hinv := invariant hn k (by omega) (by omega)
        -- expand goal
        rw [Sig_rec hkn1, factstepZ (by omega)]
        linear_combination (U n k) * (0 : ℤ)
          + ((k:ℤ)-2)*((Nat.factorial (k-3)):ℤ) * hinv
          + ((k:ℤ)-2) * hHprime
  intro k hk3 hkn
  exact aux (n - k) k rfl hk3 hkn

lemma Sig_even {n : ℕ} : ∀ k, 5 ≤ k → (2:ℤ) ∣ Sig n k := by
  have aux : ∀ m k, n - k = m → 5 ≤ k → (2:ℤ) ∣ Sig n k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hm hk5
      by_cases hkn : n ≤ k
      · rw [Sig_base hkn]; exact ⟨0, by ring⟩
      · rw [Sig_rec (by omega)]
        have h1 : (2:ℤ) ∣ ((Nat.factorial (k-3)):ℤ) := by
          have : (2:ℕ) ∣ Nat.factorial (k-3) := Nat.dvd_factorial (by omega) (by omega)
          exact_mod_cast this
        have h2 : (2:ℤ) ∣ Sig n (k+1) := ih (n-(k+1)) (by omega) (k+1) rfl (by omega)
        exact dvd_add h1 h2
  intro k hk5; exact aux (n-k) k rfl hk5

lemma Sig3_even {n : ℕ} (hn : 5 ≤ n) : (2:ℤ) ∣ Sig n 3 := by
  rw [Sig_rec (by omega : (3:ℕ) < n), Sig_rec (by omega : (4:ℕ) < n)]
  have h0 : ((Nat.factorial (3-3)):ℤ) = 1 := by norm_num
  have h1 : ((Nat.factorial (4-3)):ℤ) = 1 := by norm_num
  rw [h0, h1]
  have : (2:ℤ) ∣ Sig n 5 := Sig_even 5 (by omega)
  obtain ⟨H, hH⟩ := this
  exact ⟨1 + H, by rw [hH]; ring⟩

lemma U3_form {n : ℕ} (hn : 5 ≤ n) :
    ∃ H : ℤ, U n 3 = ((n:ℤ)^2+2*(n:ℤ)-4)*H + 2*((n:ℤ)-1)*((Nat.factorial (n-3)):ℤ) := by
  have hQ := Qident (n:=n) (by omega) 3 (by omega) (by omega)
  -- (3-1)! = 2 ; (3-2)=1
  have e2 : ((Nat.factorial (3-1)):ℤ) = 2 := by norm_num
  rw [e2] at hQ
  obtain ⟨H, hH⟩ := Sig3_even hn
  refine ⟨H, ?_⟩
  have h2 : (2:ℤ) * U n 3
      = 2 * (((n:ℤ)^2+2*(n:ℤ)-4)*H + 2*((n:ℤ)-1)*((Nat.factorial (n-3)):ℤ)) := by
    rw [hQ, hH]; ring
  linarith [h2]

lemma main_value {n : ℕ} (hn : 7 ≤ n) {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hdvd : (p:ℤ) ∣ ((n:ℤ)^2+2*(n:ℤ)-4)) (hple : n + 1 ≤ p) :
    (continued_fraction_denominator n 2).num.natAbs = p := by
  have hnZ : (7:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
  have hpZ : (n:ℤ) + 1 ≤ (p:ℤ) := by exact_mod_cast hple
  set u2 : ℤ := (n:ℤ)^2+2*(n:ℤ)-4 with hu2def
  have hu2pos : 0 < u2 := by rw [hu2def]; nlinarith
  -- c
  obtain ⟨c, hc⟩ := hdvd
  have hppos : (0:ℤ) < (p:ℤ) := by exact_mod_cast hp.pos
  have hcpos : 0 < c := by
    rcases lt_trichotomy c 0 with h | h | h
    · exfalso; nlinarith [mul_neg_of_pos_of_neg hppos h, hc, hu2pos]
    · exfalso; rw [h, mul_zero] at hc; linarith [hu2pos, hc]
    · exact h
  -- bound c ≤ n
  have hmul : ((n:ℤ)+1)*c ≤ u2 := by
    rw [hc]; exact mul_le_mul_of_nonneg_right hpZ hcpos.le
  have hcle : c ≤ (n:ℤ) := by nlinarith [hmul, hu2def, hcpos]
  -- c ≠ n, n-1, n-2
  have hne1 : c ≠ (n:ℤ) := by
    intro h
    have hdu2 : (n:ℤ) ∣ u2 := ⟨p, by rw [hc, h]; ring⟩
    have hdnn : (n:ℤ) ∣ ((n:ℤ)^2+2*(n:ℤ)) := ⟨(n:ℤ)+2, by ring⟩
    have : (n:ℤ) ∣ 4 := by
      have := dvd_sub hdnn hdu2; simpa [hu2def] using this
    have := Int.le_of_dvd (by norm_num) this
    linarith
  have hne2 : c ≠ (n:ℤ) - 1 := by
    intro h
    have hdu2 : ((n:ℤ)-1) ∣ u2 := ⟨p, by rw [hc, h]; ring⟩
    have hdnn : ((n:ℤ)-1) ∣ ((n:ℤ)^2+2*(n:ℤ)-3) := ⟨(n:ℤ)+3, by ring⟩
    have : ((n:ℤ)-1) ∣ 1 := by
      have := dvd_sub hdnn hdu2; simpa [hu2def] using this
    have := Int.le_of_dvd (by norm_num) this
    linarith
  have hne3 : c ≠ (n:ℤ) - 2 := by
    intro h
    have hdu2 : ((n:ℤ)-2) ∣ u2 := ⟨p, by rw [hc, h]; ring⟩
    have hdnn : ((n:ℤ)-2) ∣ ((n:ℤ)^2+2*(n:ℤ)-8) := ⟨(n:ℤ)+4, by ring⟩
    have : ((n:ℤ)-2) ∣ 4 := by
      have := dvd_sub hdu2 hdnn; simpa [hu2def] using this
    have := Int.le_of_dvd (by norm_num) this
    linarith
  have hcle3 : c ≤ (n:ℤ) - 3 := by omega
  -- c | (n-3)!
  obtain ⟨cN, hcN⟩ : ∃ cN : ℕ, (cN:ℤ) = c := ⟨c.toNat, Int.toNat_of_nonneg (le_of_lt hcpos)⟩
  have hcNle : cN ≤ n - 3 := by
    have : (cN:ℤ) ≤ (n:ℤ) - 3 := by rw [hcN]; exact hcle3
    have h2 : ((n-3:ℕ):ℤ) = (n:ℤ) - 3 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [← h2] at this; exact_mod_cast this
  have hcNpos : 0 < cN := by
    have : (0:ℤ) < (cN:ℤ) := by rw [hcN]; exact hcpos
    exact_mod_cast this
  have hcdvdfact : c ∣ ((Nat.factorial (n-3)):ℤ) := by
    have : cN ∣ Nat.factorial (n-3) := Nat.dvd_factorial hcNpos hcNle
    rw [← hcN]; exact_mod_cast this
  -- U3 form
  obtain ⟨H, hH⟩ := U3_form (n:=n) (by omega)
  -- c | U n 3
  have hcdvdU3 : c ∣ U n 3 := by
    rw [hH]
    refine dvd_add ?_ ?_
    · exact (Dvd.dvd.mul_right (⟨(p:ℤ), by rw [hc]; ring⟩ : c ∣ u2) H)
    · exact Dvd.dvd.mul_left hcdvdfact (2*((n:ℤ)-1))
  -- ¬ p | U n 3
  have hpprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnotp : ¬ (p:ℤ) ∣ U n 3 := by
    intro hpU
    have hpu2H : (p:ℤ) ∣ u2 * H := Dvd.dvd.mul_right ⟨c, hc⟩ H
    have hdvd2 : (p:ℤ) ∣ 2*((n:ℤ)-1)*((Nat.factorial (n-3)):ℤ) := by
      have hkey : 2*((n:ℤ)-1)*((Nat.factorial (n-3)):ℤ) = U n 3 - u2*H := by rw [hH]; ring
      rw [hkey]; exact dvd_sub hpU hpu2H
    rw [mul_assoc] at hdvd2
    rcases (hpprime.dvd_mul.mp hdvd2) with h2 | hrest
    · have hle2 := Int.le_of_dvd (by norm_num) h2
      linarith
    · rcases (hpprime.dvd_mul.mp hrest) with hn1 | hfac
      · have hpos : (0:ℤ) < (n:ℤ) - 1 := by linarith
        have := Int.le_of_dvd hpos hn1
        linarith
      · have hfacN : p ∣ Nat.factorial (n-3) := by
          have : (p:ℤ) ∣ ((Nat.factorial (n-3)):ℤ) := hfac
          exact_mod_cast this
        have := (Nat.Prime.dvd_factorial hp).mp hfacN
        omega
  -- d
  obtain ⟨d, hd⟩ := hcdvdU3
  have hU3pos : 0 < U n 3 := U_pos (by omega) 3 (by omega) (by omega)
  have hdpos : 0 < d := by
    rcases lt_trichotomy d 0 with h | h | h
    · exfalso; nlinarith [hd, hU3pos, hcpos]
    · exfalso; rw [h, mul_zero] at hd; linarith [hU3pos, hd]
    · exact h
  have hcq : (c:ℚ) ≠ 0 := by exact_mod_cast hcpos.ne'
  -- continued_fraction_denominator n 2 = p/d
  have hcontinued_fraction_denominator : continued_fraction_denominator n 2 = ((p:ℤ):ℚ)/((d:ℤ):ℚ) := by
    rw [continued_fraction_denominator_eq_U (by omega) 2 (by omega) (by omega)]
    have hU2 : U n 2 = (p:ℤ)*c := by rw [U2_eq (by omega)]; rw [← hu2def]; exact hc
    rw [hU2, hd]
    push_cast
    rw [mul_comm (p:ℚ) (c:ℚ), mul_div_mul_left _ _ hcq]
  -- coprime
  have hcoprime : Nat.Coprime (p:ℤ).natAbs d.natAbs := by
    rw [Int.natAbs_natCast]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hpd
    have hpZd : (p:ℤ) ∣ d := by
      have h := Int.natCast_dvd_natCast.mpr hpd
      rwa [Int.dvd_natAbs] at h
    have hdU3 : d ∣ U n 3 := ⟨c, by rw [hd]; ring⟩
    exact hnotp (hpZd.trans hdU3)
  rw [hcontinued_fraction_denominator, Rat.num_div_eq_of_coprime (by exact_mod_cast hdpos) hcoprime]
  simp
lemma isSquare5 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hmod5 : p % 5 = 1 ∨ p % 5 = 4) :
    IsSquare (5 : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hiff := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
    (by norm_num) hp2
  rw [show ((5:ℕ) : ZMod p) = (5 : ZMod p) from by norm_num] at hiff
  apply hiff.mp
  have hcast : ((p:ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := by rw [ZMod.natCast_mod]
  rw [hcast]
  rcases hmod5 with h | h
  · rw [h]; exact ⟨1, by norm_num⟩
  · rw [h]; exact ⟨2, by norm_num⟩

lemma exists_root {p : ℕ} (hp : p.Prime) (h19 : 19 ≤ p)
    (hp10 : p % 10 = 1 ∨ p % 10 = 9) :
    ∃ n : ℕ, 7 ≤ n ∧ n + 1 ≤ p ∧ (p:ℤ) ∣ ((n:ℤ)^2+2*(n:ℤ)-4) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hp2 : p ≠ 2 := by omega
  have hmod5 : p % 5 = 1 ∨ p % 5 = 4 := by omega
  obtain ⟨y, hy⟩ := isSquare5 hp hp2 hmod5   -- hy : 5 = y * y
  set r : ℕ := y.val with hrdef
  have hrlt : r < p := ZMod.val_lt y
  have hrcast : (r : ZMod p) = y := ZMod.natCast_zmod_val y
  have hyne : y ≠ 0 := by
    intro h; rw [h, mul_zero] at hy
    have h5 : ((5:ℕ):ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hy
    rw [ZMod.natCast_eq_zero_iff] at h5
    have := Nat.le_of_dvd (by norm_num) h5
    omega
  have hrne : r ≠ 0 := by
    intro h; apply hyne; rw [← hrcast, h]; simp
  set s : ℕ := max r (p - r) with hsdef
  have hsr : r ≤ s := le_max_left _ _
  have hsr2 : p - r ≤ s := le_max_right _ _
  have hsbig : 10 ≤ s := by omega
  have hsle : s ≤ p - 1 := by omega
  -- (s : ZMod p)^2 = 5
  have hsq : (s : ZMod p)^2 = 5 := by
    rcases max_choice r (p - r) with h | h
    · rw [hsdef, h, hrcast]; rw [hy]; ring
    · rw [hsdef, h]
      rw [Nat.cast_sub (le_of_lt hrlt), ZMod.natCast_self, hrcast]
      rw [hy]; ring
  -- p | s*s - 5 in ℕ-mod
  have hmodeq : s * s ≡ 5 [MOD p] := by
    have : ((s*s : ℕ) : ZMod p) = ((5:ℕ) : ZMod p) := by
      push_cast; rw [← sq]; rw [hsq]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  have hdvdZ : (p:ℤ) ∣ ((s:ℤ)^2 - 5) := by
    have h := (Nat.modEq_iff_dvd).mp hmodeq   -- (p:ℤ) ∣ (↑5 - ↑(s*s))
    have e : ((5:ℕ):ℤ) - ((s*s:ℕ):ℤ) = -((s:ℤ)^2 - 5) := by push_cast; ring
    rw [e] at h
    exact dvd_neg.mp h
  refine ⟨s - 1, by omega, by omega, ?_⟩
  have hsn : ((s - 1 : ℕ):ℤ) = (s:ℤ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [hsn]
  have : (s:ℤ)^2 - 5 = ((s:ℤ)-1)^2 + 2*((s:ℤ)-1) - 4 := by ring
  rw [← this]; exact hdvdZ

theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  rintro p ⟨hp, hp10⟩
  have hp10' : p % 10 = 1 ∨ p % 10 = 9 := by
    rcases hp10 with h | h
    · left; unfold Nat.ModEq at h; omega
    · right; unfold Nat.ModEq at h; omega
  by_cases hlt : p < 19
  · -- p = 11
    have hp11 : p = 11 := by
      rcases (by omega : p = 1 ∨ p = 9 ∨ p = 11) with h | h | h
      · exact absurd (h ▸ hp) (by decide)
      · exact absurd (h ▸ hp) (by decide)
      · exact h
    subst hp11
    refine ⟨3, ?_⟩
    have hcfd : continued_fraction_denominator 3 2 = ((11:ℤ):ℚ)/((4:ℤ):ℚ) := by
      rw [continued_fraction_denominator_eq_U (by norm_num) 2 (by norm_num) (by norm_num)]
      rw [U2_eq (by norm_num), U_n (by norm_num)]
      norm_num
    have hA : A363347 3 = (continued_fraction_denominator 3 2).num.natAbs := by
      rw [A363347]; norm_num
    rw [hA, hcfd, Rat.num_div_eq_of_coprime (by norm_num) (by norm_num)]
    rfl
  · -- p ≥ 19
    have h19 : 19 ≤ p := by omega
    obtain ⟨n, hn7, hnp, hdvd⟩ := exists_root hp h19 hp10'
    refine ⟨n, ?_⟩
    have hA : A363347 n = (continued_fraction_denominator n 2).num.natAbs := by
      rw [A363347]; simp only [if_neg (by omega : ¬ n ≤ 2)]
    rw [hA]
    exact main_value hn7 hp (by omega) hdvd hnp
