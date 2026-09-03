import FormalConjecturesUtil

/-! A kernel-level soundness lemma for a possible automaton certificate.
No automaton satisfying the required conditions has been found. -/

namespace Erdos406Certificate

lemma even_exponent {k : ℕ} (h : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) : Even k := by
  have hpos : 0 < 2 ^ k := by positivity
  rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hpos] at h
  have hmod : 2 ^ k % 3 = 0 ∨ 2 ^ k % 3 = 1 := by
    simpa using h (by simp : 2 ^ k % 3 ∈ (2 ^ k % 3 :: Nat.digits 3 (2 ^ k / 3)))
  rcases Nat.even_or_odd k with hk | ⟨j, rfl⟩
  · exact hk
  · simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at hmod


lemma dfa_four_mul_from {σ : Type*} (D : DFA ℕ σ)
    (R : σ → σ → ℕ → Prop)
    (hstep : ∀ s t c d, c < 4 → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3))
    (hend : ∀ s t c d, c < 4 → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((4 * d + c) % 3)) (Nat.digits 3 ((4 * d + c) / 3)) ∈ D.accept) :
    ∀ n : ℕ, 0 < n → ∀ s t c, c < 4 → R s t c →
      D.evalFrom s (Nat.digits 3 n) ∈ D.accept →
      D.evalFrom t (Nat.digits 3 (4 * n + c)) ∈ D.accept := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn s t c hc hR ha
    have hpos : 0 < 4 * n + c := by omega
    have hd : n % 3 < 3 := Nat.mod_lt n (by decide)
    have hm : (4 * n + c) % 3 = (4 * (n % 3) + c) % 3 := by omega
    have hq : (4 * n + c) / 3 = 4 * (n / 3) + (4 * (n % 3) + c) / 3 := by omega
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn] at ha
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hpos, hm, hq]
    simp only [DFA.evalFrom_cons] at ha ⊢
    by_cases hz : n / 3 = 0
    · have hdpos : 0 < n % 3 := by omega
      simp only [hz, Nat.digits_zero, DFA.evalFrom_nil] at ha
      simpa only [hz, mul_zero, zero_add] using hend s t c (n % 3) hc hdpos hd hR ha
    · have hlt : n / 3 < n := Nat.div_lt_self hn (by decide)
      have hc' : (4 * (n % 3) + c) / 3 < 4 := by omega
      exact ih (n / 3) hlt (by omega) _ _ _ hc' (hstep s t c (n % 3) hc hd hR) ha

lemma dfa_four_mul {σ : Type*} (D : DFA ℕ σ)
    (R : σ → σ → ℕ → Prop) (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < 4 → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3))
    (hend : ∀ s t c d, c < 4 → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((4 * d + c) % 3)) (Nat.digits 3 ((4 * d + c) / 3)) ∈ D.accept)
    {n : ℕ} (hn : 0 < n) (ha : D.eval (Nat.digits 3 n) ∈ D.accept) :
    D.eval (Nat.digits 3 (4 * n)) ∈ D.accept := by
  simpa only [DFA.eval, Nat.add_zero] using
    dfa_four_mul_from D R hstep hend n hn D.start D.start 0 (by decide) hstart ha

lemma dfa_all_four_powers {σ : Type*} (D : DFA ℕ σ)
    (R : σ → σ → ℕ → Prop) (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < 4 → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3))
    (hend : ∀ s t c d, c < 4 → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((4 * d + c) % 3)) (Nat.digits 3 ((4 * d + c) / 3)) ∈ D.accept)
    (hone : D.eval [1] ∈ D.accept) :
    ∀ m : ℕ, D.eval (Nat.digits 3 (4 ^ m)) ∈ D.accept := by
  intro m
  induction m with
  | zero => simpa using hone
  | succ m ih =>
    simpa only [pow_succ'] using dfa_four_mul D R hstart hstep hend (by positivity) ih

def knownSuffixes : Fin 8 → List (List ℕ) :=
  ![[[1], [1, 1], [1, 1, 1, 0, 0, 1]],
    [[], [1], [1, 1, 0, 0, 1]], [[], [1, 0, 0, 1]],
    [[0, 0, 1]], [[0, 1]], [[1]], [[]], []]

def knownStep (t : Fin 8) (d : ℕ) : Fin 8 :=
  if d = 0 then ![7, 7, 7, 4, 5, 7, 7, 7] t
  else if d = 1 then ![1, 2, 3, 7, 7, 6, 7, 7] t
  else 7

def knownDFA : DFA ℕ (Fin 8) where
  step := knownStep
  start := 0
  accept := {t | [] ∈ knownSuffixes t}

lemma knownSuffixes_step (t : Fin 8) (d : ℕ) (w : List ℕ) :
    w ∈ knownSuffixes (knownStep t d) ↔ d :: w ∈ knownSuffixes t := by
  fin_cases t <;> by_cases h0 : d = 0 <;> by_cases h1 : d = 1 <;>
    simp_all [knownSuffixes, knownStep]

lemma knownDFA_suffixes (w v : List ℕ) (t : Fin 8) :
    v ∈ knownSuffixes (knownDFA.evalFrom t w) ↔ w ++ v ∈ knownSuffixes t := by
  induction w generalizing t with
  | nil => rfl
  | cons d w ih =>
    rw [DFA.evalFrom_cons, ih]
    exact knownSuffixes_step t d (w ++ v)

lemma knownDFA_accepts (w : List ℕ) :
    knownDFA.eval w ∈ knownDFA.accept ↔
      w = [1] ∨ w = [1, 1] ∨ w = [1, 1, 1, 0, 0, 1] := by
  change [] ∈ knownSuffixes (knownDFA.evalFrom 0 w) ↔ _
  rw [knownDFA_suffixes]
  simp [knownSuffixes]

lemma knownDFA_values {n : ℕ} (h : knownDFA.eval (Nat.digits 3 n) ∈ knownDFA.accept) :
    n = 1 ∨ n = 4 ∨ n = 256 := by
  have hv := Nat.ofDigits_digits 3 n
  rcases (knownDFA_accepts _).mp h with he | he | he
  · rw [he] at hv
    norm_num [Nat.ofDigits] at hv
    omega
  · rw [he] at hv
    norm_num [Nat.ofDigits] at hv
    omega
  · rw [he] at hv
    norm_num [Nat.ofDigits] at hv
    omega

lemma dfa_binary_product_closed {σ τ : Type*} (D : DFA ℕ σ) (E : DFA ℕ τ)
    (G : σ → τ → Prop)
    (hstep : ∀ s t d, d < 2 → G s t → G (D.step s d) (E.step t d))
    (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (s : σ) (t : τ) (hG : G s t) :
    G (D.evalFrom s w) (E.evalFrom t w) := by
  induction w generalizing s t with
  | nil => exact hG
  | cons d w ih =>
    simp only [DFA.evalFrom_cons]
    apply ih (fun e he => hw e (by simp [he]))
    exact hstep s t d (hw d (by simp)) hG

lemma dfa_good_safety {σ : Type*} (D : DFA ℕ σ) (G : σ → Fin 8 → Prop)
    (hstart : G D.start 0)
    (hstep : ∀ s t d, d < 2 → G s t → G (D.step s d) (knownStep t d))
    (hend : ∀ s t, G s t → D.step s 1 ∈ D.accept → knownStep t 1 ∈ knownDFA.accept)
    {n : ℕ} (hn : 0 < n) (hd : Nat.digits 3 n ⊆ [0, 1])
    (ha : D.eval (Nat.digits 3 n) ∈ D.accept) : n = 1 ∨ n = 4 ∨ n = 256 := by
  have hne : Nat.digits 3 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt hn)
  have hlast : (Nat.digits 3 n).getLast hne = 1 := by
    have hm := hd (List.getLast_mem hne)
    have hz := Nat.getLast_digit_ne_zero 3 (ne_of_gt hn)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he := List.dropLast_append_getLast hne
  rw [hlast] at he
  have hp : ∀ d ∈ (Nat.digits 3 n).dropLast, d < 2 := by
    intro d h
    have hh := hd (List.mem_of_mem_dropLast h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    omega
  have hG := dfa_binary_product_closed D knownDFA G hstep
    (Nat.digits 3 n).dropLast hp D.start 0 hstart
  have hA : D.step (D.eval (Nat.digits 3 n).dropLast) 1 ∈ D.accept := by
    rw [← DFA.eval_append_singleton, he]
    exact ha
  have hE := hend _ _ hG hA
  apply knownDFA_values
  rw [← he, DFA.eval_append_singleton]
  exact hE

/-- A valid automaton certificate would prove the classification. The existence
of such a certificate is NOT proved here. -/
lemma dfa_certificate_classification {σ : Type*} (D : DFA ℕ σ)
    (R : σ → σ → ℕ → Prop) (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < 4 → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3))
    (hend : ∀ s t c d, c < 4 → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((4 * d + c) % 3)) (Nat.digits 3 ((4 * d + c) / 3)) ∈ D.accept)
    (hone : D.eval [1] ∈ D.accept)
    (G : σ → Fin 8 → Prop) (hgstart : G D.start 0)
    (hgstep : ∀ s t d, d < 2 → G s t → G (D.step s d) (knownStep t d))
    (hgend : ∀ s t, G s t → D.step s 1 ∈ D.accept → knownStep t 1 ∈ knownDFA.accept)
    {n : ℕ} (hn : n.isPowerOfTwo) (hd : Nat.digits 3 n ⊆ [0, 1]) :
    n = 1 ∨ n = 4 ∨ n = 256 := by
  obtain ⟨k, rfl⟩ := hn
  obtain ⟨m, hm⟩ := even_exponent hd
  have hp : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    norm_num
  rw [hp] at hd ⊢
  exact dfa_good_safety D G hgstart hgstep hgend (by positivity) hd
    (dfa_all_four_powers D R hstart hstep hend hone m)

/-- Backward reachability for a binary word ending in the canonical final digit `1`. -/
lemma dfa_good_coaccessible {σ : Type*} (D : DFA ℕ σ) (C : σ → Prop)
    (hcend : ∀ s, D.step s 1 ∈ D.accept → C s)
    (hcstep : ∀ s d, d < 2 → C (D.step s d) → C s)
    (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (s : σ)
    (ha : D.evalFrom s (w ++ [1]) ∈ D.accept) : C s := by
  induction w generalizing s with
  | nil => exact hcend s (by simpa using ha)
  | cons d w ih =>
    apply hcstep s d (hw d (by simp))
    apply ih (fun e he => hw e (by simp [he]))
    simpa only [List.cons_append, DFA.evalFrom_cons] using ha

/-- A natural-valued rank decreases along every binary path which can still
reach canonical acceptance, so it bounds the length of any such path. -/
lemma dfa_good_rank_bound {σ : Type*} (D : DFA ℕ σ) (G C : σ → Prop) (rank : σ → ℕ)
    (hgstep : ∀ s d, d < 2 → G s → G (D.step s d))
    (hcend : ∀ s, D.step s 1 ∈ D.accept → C s)
    (hcstep : ∀ s d, d < 2 → C (D.step s d) → C s)
    (hrstep : ∀ s d, d < 2 → G s → C (D.step s d) → rank (D.step s d) < rank s)
    (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (s : σ) (hg : G s)
    (ha : D.evalFrom s (w ++ [1]) ∈ D.accept) : w.length ≤ rank s := by
  induction w generalizing s with
  | nil => simp
  | cons d w ih =>
    have hd : d < 2 := hw d (by simp)
    have hw' : ∀ e ∈ w, e < 2 := fun e he => hw e (by simp [he])
    have ha' : D.evalFrom (D.step s d) (w ++ [1]) ∈ D.accept := by
      simpa only [List.cons_append, DFA.evalFrom_cons] using ha
    have hb := ih hw' (D.step s d) (hgstep s d hd hg) ha'
    have hc := dfa_good_coaccessible D C hcend hcstep w hw' (D.step s d) ha'
    have hr := hrstep s d hd hg hc
    simp only [List.length_cons]
    omega

lemma dfa_good_digit_length_bound {σ : Type*} (D : DFA ℕ σ)
    (G C : σ → Prop) (rank : σ → ℕ) (hgstart : G D.start)
    (hgstep : ∀ s d, d < 2 → G s → G (D.step s d))
    (hcend : ∀ s, D.step s 1 ∈ D.accept → C s)
    (hcstep : ∀ s d, d < 2 → C (D.step s d) → C s)
    (hrstep : ∀ s d, d < 2 → G s → C (D.step s d) → rank (D.step s d) < rank s)
    {n : ℕ} (hn : 0 < n) (hd : Nat.digits 3 n ⊆ [0, 1])
    (ha : D.eval (Nat.digits 3 n) ∈ D.accept) :
    (Nat.digits 3 n).length ≤ rank D.start + 1 := by
  have hne : Nat.digits 3 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt hn)
  have hlast : (Nat.digits 3 n).getLast hne = 1 := by
    have hm := hd (List.getLast_mem hne)
    have hz := Nat.getLast_digit_ne_zero 3 (ne_of_gt hn)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he := List.dropLast_append_getLast hne
  rw [hlast] at he
  have hp : ∀ d ∈ (Nat.digits 3 n).dropLast, d < 2 := by
    intro d h
    have hh := hd (List.mem_of_mem_dropLast h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    omega
  have ha' : D.evalFrom D.start ((Nat.digits 3 n).dropLast ++ [1]) ∈ D.accept := by
    simpa only [he, DFA.eval] using ha
  have hb := dfa_good_rank_bound D G C rank hgstep hcend hcstep hrstep
    (Nat.digits 3 n).dropLast hp D.start hgstart ha'
  have hl := congrArg List.length he
  simp only [List.length_append, List.length_singleton] at hl
  omega

/-- This weaker certificate proves the requested finiteness, without specifying
which finitely many binary ternary words the invariant may accept.
No witness for these certificate conditions is supplied. -/
lemma dfa_certificate_finiteness {σ : Type*} (D : DFA ℕ σ)
    (R : σ → σ → ℕ → Prop) (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < 4 → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3))
    (hend : ∀ s t c d, c < 4 → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((4 * d + c) % 3)) (Nat.digits 3 ((4 * d + c) / 3)) ∈ D.accept)
    (hone : D.eval [1] ∈ D.accept)
    (G C : σ → Prop) (rank : σ → ℕ) (hgstart : G D.start)
    (hgstep : ∀ s d, d < 2 → G s → G (D.step s d))
    (hcend : ∀ s, D.step s 1 ∈ D.accept → C s)
    (hcstep : ∀ s d, d < 2 → C (D.step s d) → C s)
    (hrstep : ∀ s d, d < 2 → G s → C (D.step s d) → rank (D.step s d) < rank s) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply (Set.finite_Iio (3 ^ (rank D.start + 1))).subset
  rintro n ⟨⟨k, rfl⟩, hd⟩
  obtain ⟨m, hm⟩ := even_exponent hd
  have hp : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    norm_num
  rw [hp] at hd ⊢
  have ha := dfa_all_four_powers D R hstart hstep hend hone m
  have hlen := dfa_good_digit_length_bound D G C rank hgstart hgstep hcend hcstep hrstep
    (by positivity : 0 < 4 ^ m) hd ha
  exact (Nat.lt_base_pow_length_digits (by decide : 1 < 3)).trans_le
    (Nat.pow_le_pow_right (by decide) hlen)

lemma dfa_four_power_tail {σ : Type*} (D : DFA ℕ σ)
    (R : σ → σ → ℕ → Prop) (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < 4 → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3))
    (hend : ∀ s t c d, c < 4 → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((4 * d + c) % 3)) (Nat.digits 3 ((4 * d + c) / 3)) ∈ D.accept)
    (M : ℕ) (hseed : D.eval (Nat.digits 3 (4 ^ M)) ∈ D.accept) :
    ∀ j : ℕ, D.eval (Nat.digits 3 (4 ^ (M + j))) ∈ D.accept := by
  intro j
  induction j with
  | zero => simpa using hseed
  | succ j ih =>
    have hh := dfa_four_mul D R hstart hstep hend (by positivity : 0 < 4 ^ (M + j)) ih
    simpa only [Nat.add_succ, pow_succ'] using hh

lemma dfa_binary_reachable {σ : Type*} (D : DFA ℕ σ) (G : σ → Prop)
    (hgstep : ∀ s d, d < 2 → G s → G (D.step s d))
    (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (s : σ) (hg : G s) :
    G (D.evalFrom s w) := by
  induction w generalizing s with
  | nil => exact hg
  | cons d w ih =>
    exact ih (fun e he => hw e (by simp [he])) (D.step s d)
      (hgstep s d (hw d (by simp)) hg)

lemma dfa_good_reject {σ : Type*} (D : DFA ℕ σ) (G : σ → Prop)
    (hgstart : G D.start)
    (hgstep : ∀ s d, d < 2 → G s → G (D.step s d))
    (hgend : ∀ s, G s → D.step s 1 ∉ D.accept)
    {n : ℕ} (hn : 0 < n) (hd : Nat.digits 3 n ⊆ [0, 1]) :
    D.eval (Nat.digits 3 n) ∉ D.accept := by
  have hne : Nat.digits 3 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt hn)
  have hlast : (Nat.digits 3 n).getLast hne = 1 := by
    have hm := hd (List.getLast_mem hne)
    have hz := Nat.getLast_digit_ne_zero 3 (ne_of_gt hn)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he := List.dropLast_append_getLast hne
  rw [hlast] at he
  have hp : ∀ d ∈ (Nat.digits 3 n).dropLast, d < 2 := by
    intro d h
    have hh := hd (List.mem_of_mem_dropLast h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    omega
  have hg := dfa_binary_reachable D G hgstep (Nat.digits 3 n).dropLast hp D.start hgstart
  have hh := hgend _ hg
  change D.step (D.eval (Nat.digits 3 n).dropLast) 1 ∉ D.accept at hh
  simpa only [← DFA.eval_append_singleton, he] using hh

/-- An invariant accepting one sufficiently late power of four, closed under
multiplication by four, and rejecting every good word proves finiteness.
No automaton satisfying these hypotheses is provided here. -/
lemma dfa_eventual_certificate_finiteness {σ : Type*} (D : DFA ℕ σ)
    (R : σ → σ → ℕ → Prop) (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < 4 → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3))
    (hend : ∀ s t c d, c < 4 → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((4 * d + c) % 3)) (Nat.digits 3 ((4 * d + c) / 3)) ∈ D.accept)
    (M : ℕ) (hseed : D.eval (Nat.digits 3 (4 ^ M)) ∈ D.accept)
    (G : σ → Prop) (hgstart : G D.start)
    (hgstep : ∀ s d, d < 2 → G s → G (D.step s d))
    (hgend : ∀ s, G s → D.step s 1 ∉ D.accept) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply (Set.finite_Iic (4 ^ M)).subset
  rintro n ⟨⟨k, rfl⟩, hd⟩
  obtain ⟨m, hm⟩ := even_exponent hd
  have hp : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    norm_num
  rw [hp] at hd ⊢
  have hlt : m < M := by
    by_contra hlt
    have hM : M ≤ m := by omega
    have ha := dfa_four_power_tail D R hstart hstep hend M hseed (m - M)
    rw [Nat.add_sub_of_le hM] at ha
    exact dfa_good_reject D G hgstart hgstep hgend (by positivity) hd ha
  exact Nat.pow_le_pow_right (by decide) (by omega)

#print axioms dfa_certificate_finiteness
#print axioms dfa_eventual_certificate_finiteness

/- Strided multiplication certificates; still conditional, with no witness. -/

lemma dfa_mul_from {σ : Type*} (D : DFA ℕ σ) (q : ℕ) (hq : 0 < q)
    (R : σ → σ → ℕ → Prop)
    (hstep : ∀ s t c d, c < q → d < 3 → R s t c →
      R (D.step s d) (D.step t ((q * d + c) % 3)) ((q * d + c) / 3))
    (hend : ∀ s t c d, c < q → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((q * d + c) % 3)) (Nat.digits 3 ((q * d + c) / 3)) ∈ D.accept) :
    ∀ n : ℕ, 0 < n → ∀ s t c, c < q → R s t c →
      D.evalFrom s (Nat.digits 3 n) ∈ D.accept →
      D.evalFrom t (Nat.digits 3 (q * n + c)) ∈ D.accept := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn s t c hc hR ha
    have hpos : 0 < q * n + c := by positivity
    have hd : n % 3 < 3 := Nat.mod_lt n (by decide)
    have hm : (q * n + c) % 3 = (q * (n % 3) + c) % 3 := by
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    have he : q * n + c = (q * (n % 3) + c) + (q * (n / 3)) * 3 := by
      calc
        q * n + c = q * (n % 3 + 3 * (n / 3)) + c := by
          rw [Nat.mod_add_div]
        _ = _ := by ring
    have hdiv : (q * n + c) / 3 = q * (n / 3) + (q * (n % 3) + c) / 3 := by
      rw [he, Nat.add_mul_div_right _ _ (by decide)]
      omega
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn] at ha
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hpos, hm, hdiv]
    simp only [DFA.evalFrom_cons] at ha ⊢
    by_cases hz : n / 3 = 0
    · have hdpos : 0 < n % 3 := by omega
      simp only [hz, Nat.digits_zero, DFA.evalFrom_nil] at ha
      simpa only [hz, mul_zero, zero_add] using hend s t c (n % 3) hc hdpos hd hR ha
    · have hlt : n / 3 < n := Nat.div_lt_self hn (by decide)
      have hc' : (q * (n % 3) + c) / 3 < q := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr
        nlinarith
      exact ih (n / 3) hlt (by omega) _ _ _ hc' (hstep s t c (n % 3) hc hd hR) ha

lemma dfa_mul {σ : Type*} (D : DFA ℕ σ) (q : ℕ) (hq : 0 < q)
    (R : σ → σ → ℕ → Prop) (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < q → d < 3 → R s t c →
      R (D.step s d) (D.step t ((q * d + c) % 3)) ((q * d + c) / 3))
    (hend : ∀ s t c d, c < q → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((q * d + c) % 3)) (Nat.digits 3 ((q * d + c) / 3)) ∈ D.accept)
    {n : ℕ} (hn : 0 < n) (ha : D.eval (Nat.digits 3 n) ∈ D.accept) :
    D.eval (Nat.digits 3 (q * n)) ∈ D.accept := by
  simpa only [DFA.eval, Nat.add_zero] using
    dfa_mul_from D q hq R hstep hend n hn D.start D.start 0 hq hstart ha

lemma dfa_mul_iterate {σ : Type*} (D : DFA ℕ σ) (q : ℕ) (hq : 0 < q)
    (R : σ → σ → ℕ → Prop) (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < q → d < 3 → R s t c →
      R (D.step s d) (D.step t ((q * d + c) % 3)) ((q * d + c) / 3))
    (hend : ∀ s t c d, c < q → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((q * d + c) % 3)) (Nat.digits 3 ((q * d + c) / 3)) ∈ D.accept)
    {n : ℕ} (hn : 0 < n) (ha : D.eval (Nat.digits 3 n) ∈ D.accept) :
    ∀ j : ℕ, D.eval (Nat.digits 3 (q ^ j * n)) ∈ D.accept := by
  intro j
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    have hh := dfa_mul D q hq R hstart hstep hend (by positivity : 0 < q ^ j * n) ih
    simpa only [pow_succ', mul_assoc] using hh

/-- Multiplication by `4^stride` covers the entire tail of powers of four when
one seed in each of the `stride` residue classes is accepted. -/
lemma dfa_strided_power_tail {σ : Type*} (D : DFA ℕ σ) (stride : ℕ) (hs : 0 < stride)
    (R : σ → σ → ℕ → Prop) (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < 4 ^ stride → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 ^ stride * d + c) % 3)) ((4 ^ stride * d + c) / 3))
    (hend : ∀ s t c d, c < 4 ^ stride → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((4 ^ stride * d + c) % 3))
        (Nat.digits 3 ((4 ^ stride * d + c) / 3)) ∈ D.accept)
    (M : ℕ) (hseed : ∀ r < stride, D.eval (Nat.digits 3 (4 ^ (M + r))) ∈ D.accept)
    {m : ℕ} (hm : M ≤ m) : D.eval (Nat.digits 3 (4 ^ m)) ∈ D.accept := by
  have hr : (m - M) % stride < stride := Nat.mod_lt _ hs
  have ha := dfa_mul_iterate D (4 ^ stride) (by positivity) R hstart hstep hend
    (by positivity : 0 < 4 ^ (M + (m - M) % stride)) (hseed _ hr) ((m - M) / stride)
  have he : stride * ((m - M) / stride) + (M + (m - M) % stride) = m := by
    have h := Nat.mod_add_div (m - M) stride
    omega
  simpa only [← pow_mul, ← pow_add, he] using ha

/-- A strided eventual certificate implies the requested finiteness. Existence
of such a certificate is not asserted. -/
lemma dfa_strided_certificate_finiteness {σ : Type*} (D : DFA ℕ σ)
    (stride : ℕ) (hs : 0 < stride)
    (R : σ → σ → ℕ → Prop) (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < 4 ^ stride → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 ^ stride * d + c) % 3)) ((4 ^ stride * d + c) / 3))
    (hend : ∀ s t c d, c < 4 ^ stride → 0 < d → d < 3 → R s t c → D.step s d ∈ D.accept →
      D.evalFrom (D.step t ((4 ^ stride * d + c) % 3))
        (Nat.digits 3 ((4 ^ stride * d + c) / 3)) ∈ D.accept)
    (M : ℕ) (hseed : ∀ r < stride, D.eval (Nat.digits 3 (4 ^ (M + r))) ∈ D.accept)
    (G : σ → Prop) (hgstart : G D.start)
    (hgstep : ∀ s d, d < 2 → G s → G (D.step s d))
    (hgend : ∀ s, G s → D.step s 1 ∉ D.accept) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply (Set.finite_Iic (4 ^ M)).subset
  rintro n ⟨⟨k, rfl⟩, hd⟩
  obtain ⟨m, hm⟩ := even_exponent hd
  have hp : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    norm_num
  rw [hp] at hd ⊢
  have hlt : m < M := by
    by_contra hlt
    have hM : M ≤ m := by omega
    have ha := dfa_strided_power_tail D stride hs R hstart hstep hend M hseed hM
    exact dfa_good_reject D G hgstart hgstep hgend (by positivity) hd ha
  exact Nat.pow_le_pow_right (by decide) (by omega)

#print axioms dfa_strided_certificate_finiteness
end Erdos406Certificate
