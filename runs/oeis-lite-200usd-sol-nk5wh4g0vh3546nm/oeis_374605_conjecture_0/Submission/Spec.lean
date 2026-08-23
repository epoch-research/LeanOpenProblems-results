import FormalConjectures.Util.ProblemImports
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped BigOperators
open Finset

/--
A374605: The sequence $a(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

private def rf (x : ℚ) (n : ℕ) : ℚ := ∏ i ∈ range n, (x + i)

private lemma rf_zero (x : ℚ) : rf x 0 = 1 := by simp [rf]
private lemma rf_succ (x : ℚ) (n : ℕ) : rf x (n+1) = rf x n * (x+n) := by
  simp [rf, prod_range_succ]

private lemma rf_add (x : ℚ) (m n : ℕ) :
    rf x (m+n) = rf x m * rf (x+m) n := by
  induction n with
  | zero => simp [rf]
  | succ n ih =>
    rw [Nat.add_succ, rf_succ, ih, rf_succ]
    push_cast
    ring

private lemma rf_shift (x : ℚ) (n : ℕ) :
    x * rf (x+1) n = rf x n * (x+n) := by
  induction n with
  | zero => simp [rf]
  | succ n ih =>
    rw [rf_succ, rf_succ]
    push_cast
    rw [← ih]
    ring

private lemma rf_neg_nat_choose (n k : ℕ) :
    rf (-(n:ℚ)) k = (-1)^k * k.factorial * n.choose k := by
  induction k with
  | zero => simp [rf]
  | succ k ih =>
    rw [rf_succ, ih, Nat.factorial_succ]
    push_cast
    by_cases h : k < n
    · have hkn : k ≤ n := by omega
      have hrel0 := Nat.choose_succ_right_eq n k
      have hrel : (n.choose (k+1):ℚ) * (k+1) = n.choose k * (n-k) := by
        exact_mod_cast hrel0
      rw [pow_succ]
      linear_combination (-1)^k * k.factorial * hrel
    · have hz : n.choose (k+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz]
      simp
      have hk : n.choose k = 0 ∨ k = n := by
        by_cases hkn : k ≤ n
        · right; omega
        · left; exact Nat.choose_eq_zero_of_lt (by omega)
      rcases hk with hk | rfl
      · simp [hk]
      · simp


private def psTerm (n : ℕ) (aa bb cc : ℚ) (k : ℕ) : ℚ :=
  rf (-(n:ℚ)) k * rf aa k * rf bb k /
    (rf cc k * rf (1 + aa + bb - cc - n) k * k.factorial)

private lemma ps_recurrence_point (n k : ℕ) (aa bb cc : ℚ) (hk : k < n)
    (h₁ : (n+1-k:ℚ) ≠ 0)
    (h₀ : (n-k:ℚ) ≠ 0)
    (hx₀ : aa + bb - cc - n ≠ 0)
    (hxk : aa + bb - cc - n + k ≠ 0)
    (hden : rf cc k * rf (1+aa+bb-cc-n) k * k.factorial ≠ 0)
    (hden' : rf cc k * rf (aa+bb-cc-n) k * k.factorial ≠ 0)
    (hdenk : rf cc (k+1) * rf (1+aa+bb-cc-n) (k+1) * (k+1).factorial ≠ 0) :
    (cc+n) * (cc-aa-bb+n) * psTerm (n+1) aa bb cc k
      - (cc-aa+n) * (cc-bb+n) * psTerm n aa bb cc k =
    psTerm n aa bb cc (k+1) * (k+1) * (cc+k) * (aa+bb-cc-n+k+1) / (n-k)
      - psTerm n aa bb cc k * k * (cc+k-1) * (aa+bb-cc-n+k) / (n+1-k) := by
  have hn : (n+1:ℚ) ≠ 0 := by positivity
  have hnk : (n+1:ℚ) - k ≠ 0 := by exact h₁
  have hneg00 := rf_shift (-(n+1:ℚ)) k
  have hneg0 : -(n+1:ℚ) * rf (-(n:ℚ)) k =
      rf (-(n+1:ℚ)) k * (-(n+1:ℚ)+k) := by
    convert hneg00 using 1 <;> norm_num <;> ring
  have hneg : rf (-(n+1:ℚ)) k = rf (-(n:ℚ)) k * (n+1) / (n+1-k) := by
    apply (eq_div_iff hnk).2
    calc
      rf (-(n+1:ℚ)) k * (n+1-k) = -(rf (-(n+1:ℚ)) k * (-(n+1:ℚ)+k)) := by ring
      _ = - (-(n+1:ℚ) * rf (-(n:ℚ)) k) := by rw [← hneg0]
      _ = rf (-(n:ℚ)) k * (n+1) := by ring
  have hxshift00 := rf_shift (aa+bb-cc-n) k
  have hxshift0 : (aa+bb-cc-n) * rf (1+aa+bb-cc-n) k =
      rf (aa+bb-cc-n) k * (aa+bb-cc-n+k) := by
    convert hxshift00 using 1 <;> ring
  have hxshift : rf (aa+bb-cc-n) k =
      rf (1+aa+bb-cc-n) k * (aa+bb-cc-n) / (aa+bb-cc-n+k) := by
    apply (eq_div_iff hxk).2
    simpa [mul_comm] using hxshift0.symm
  have hfac : (k.factorial:ℚ) ≠ 0 := by positivity
  have hfac1 : ((k+1).factorial:ℚ) ≠ 0 := by positivity
  have hcc : rf cc k ≠ 0 := by
    intro h; apply hden; simp [h]
  have hxx : rf (1+aa+bb-cc-n) k ≠ 0 := by
    intro h; apply hden; simp [h]
  have hcc1 : rf cc (k+1) ≠ 0 := by
    intro h; apply hdenk; simp [h]
  have hxx1 : rf (1+aa+bb-cc-n) (k+1) ≠ 0 := by
    intro h; apply hdenk; simp [h]
  have hck : cc+k ≠ 0 := by
    intro h
    apply hcc1
    rw [rf_succ]
    simp [h]
  have hdk : 1+aa+bb-cc-n+k ≠ 0 := by
    intro h
    apply hxx1
    rw [rf_succ]
    simp [h]


  have hxnorm : 1+aa+bb-cc-(n+1:ℚ) = aa+bb-cc-n := by ring
  have hN : psTerm (n+1) aa bb cc k = psTerm n aa bb cc k *
      ((n+1) / (n+1-k) * ((aa+bb-cc-n+k) / (aa+bb-cc-n))) := by
    simp only [psTerm]
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [hneg, hxnorm, hxshift]
    field_simp [hcc, hxx, hfac, h₁, hx₀, hxk]
  have hK : psTerm n aa bb cc (k+1) = psTerm n aa bb cc k *
      ((-(n:ℚ)+k) * (aa+k) * (bb+k) /
        ((cc+k) * (1+aa+bb-cc-n+k) * (k+1))) := by
    simp only [psTerm, rf_succ, Nat.factorial_succ]
    norm_num only [Nat.cast_add, Nat.cast_one]
    push_cast
    field_simp [hcc, hxx, hcc1, hxx1, hfac, hfac1, hck, hdk]
  have hleft :
      (cc+n) * (cc-aa-bb+n) *
        ((n+1) / (n+1-k) * ((aa+bb-cc-n+k) / (aa+bb-cc-n))) =
      -(cc+n) * (n+1) * (aa+bb-cc-n+k) / (n+1-k) := by
    rw [show cc-aa-bb+(n:ℚ) = -(aa+bb-cc-n) by ring]
    field_simp [hx₀]
  have hright :
      ((-(n:ℚ)+k) * (aa+k) * (bb+k) /
        ((cc+k) * (1+aa+bb-cc-n+k) * (k+1))) *
        (k+1) * (cc+k) * (aa+bb-cc-n+k+1) / (n-k) =
      -(aa+k) * (bb+k) := by
    field_simp [h₀, hck, hdk]
    ring
  have hcore :
      -(cc+n) * (n+1) * (aa+bb-cc-n+k) / (n+1-k) -
        (cc-aa+n) * (cc-bb+n) =
      -(aa+k) * (bb+k) -
        k * (cc+k-1) * (aa+bb-cc-n+k) / (n+1-k) := by
    field_simp [h₁]
    ring
  rw [hN, hK]
  rw [show (cc+n) * (cc-aa-bb+n) *
        (psTerm n aa bb cc k *
          ((n+1) / (n+1-k) * ((aa+bb-cc-n+k) / (aa+bb-cc-n)))) -
        (cc-aa+n) * (cc-bb+n) * psTerm n aa bb cc k =
      psTerm n aa bb cc k *
        ((cc+n) * (cc-aa-bb+n) *
          ((n+1) / (n+1-k) * ((aa+bb-cc-n+k) / (aa+bb-cc-n))) -
          (cc-aa+n) * (cc-bb+n)) by
        conv_rhs => rw [mul_sub]
        simp only [div_eq_mul_inv]
        ac_rfl]
  rw [show psTerm n aa bb cc k *
          ((-(n:ℚ)+k) * (aa+k) * (bb+k) /
            ((cc+k) * (1+aa+bb-cc-n+k) * (k+1))) *
          (k+1) * (cc+k) * (aa+bb-cc-n+k+1) / (n-k) -
        psTerm n aa bb cc k * k * (cc+k-1) * (aa+bb-cc-n+k) / (n+1-k) =
      psTerm n aa bb cc k *
        (((-(n:ℚ)+k) * (aa+k) * (bb+k) /
          ((cc+k) * (1+aa+bb-cc-n+k) * (k+1))) *
          (k+1) * (cc+k) * (aa+bb-cc-n+k+1) / (n-k) -
          k * (cc+k-1) * (aa+bb-cc-n+k) / (n+1-k)) by
        conv_rhs => rw [mul_sub]
        simp only [div_eq_mul_inv]
        ac_rfl]
  rw [hleft, hright, hcore]

private lemma ps_recurrence_boundary (n : ℕ) (aa bb cc : ℚ)
    (hxb : aa+bb-cc-n ≠ 0) (hxe : aa+bb-cc ≠ 0)
    (h0 : rf cc n * rf (1+aa+bb-cc-n) n * n.factorial ≠ 0)
    (h1 : rf cc n * rf (aa+bb-cc-n) n * n.factorial ≠ 0)
    (h2 : rf cc (n+1) * rf (aa+bb-cc-n) (n+1) * (n+1).factorial ≠ 0) :
    psTerm n aa bb cc n * n * (cc+n-1) * (aa+bb-cc) +
      ((cc+n)*(cc-aa-bb+n)*psTerm (n+1) aa bb cc n -
        (cc-aa+n)*(cc-bb+n)*psTerm n aa bb cc n) +
      (cc+n)*(cc-aa-bb+n)*psTerm (n+1) aa bb cc (n+1) = 0 := by
  have hc0 : rf cc n ≠ 0 := by intro h; apply h0; simp [h]
  have hx0 : rf (1+aa+bb-cc-n) n ≠ 0 := by intro h; apply h0; simp [h]
  have hx1 : rf (aa+bb-cc-n) n ≠ 0 := by intro h; apply h1; simp [h]
  have hc2 : rf cc (n+1) ≠ 0 := by intro h; apply h2; simp [h]
  have hx2 : rf (aa+bb-cc-n) (n+1) ≠ 0 := by intro h; apply h2; simp [h]
  have hf0 : (n.factorial:ℚ) ≠ 0 := by positivity
  have hcn : cc+n ≠ 0 := by
    intro h
    apply hc2
    rw [rf_succ]
    simp [h]

  have hf1 : ((n+1).factorial:ℚ) ≠ 0 := by positivity
  simp only [psTerm]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hxnorm : 1+aa+bb-cc-(n+1:ℚ) = aa+bb-cc-n := by ring
  rw [hxnorm]
  have hn1 : rf (-(n+1:ℚ)) n = (-1)^n * n.factorial * (n+1).choose n := by
    convert rf_neg_nat_choose (n+1) n using 1 <;> norm_num
  have hn2 : rf (-(n+1:ℚ)) (n+1) =
      (-1)^(n+1) * (n+1).factorial * (n+1).choose (n+1) := by
    convert rf_neg_nat_choose (n+1) (n+1) using 1 <;> norm_num
  have hxshift0 := rf_shift (aa+bb-cc-n) n
  have hxshift : rf (aa+bb-cc-n) n =
      rf (1+aa+bb-cc-n) n * (aa+bb-cc-n) / (aa+bb-cc) := by
    apply (eq_div_iff hxe).2
    convert hxshift0.symm using 1 <;> norm_num <;> ring
  simp only [hxshift]

  rw [rf_neg_nat_choose n n, hn1, hn2]
  simp only [Nat.choose_self, Nat.choose_succ_self_right, Nat.cast_one, mul_one]
  simp only [rf_succ, Nat.factorial_succ]
  norm_num only [Nat.cast_add, Nat.cast_one]
  simp only [hxshift]
  field_simp [hc0, hx0, hf0, hxb, hxe, hcn]
  push_cast
  ring

private lemma rf_ne_zero (x : ℚ) (n : ℕ) (h : ∀ i < n, x+i ≠ 0) : rf x n ≠ 0 := by
  simp only [rf, prod_ne_zero_iff, mem_range]
  exact h

private def psSum (n : ℕ) (aa bb cc : ℚ) : ℚ :=
  ∑ k ∈ range (n+1), psTerm n aa bb cc k

private lemma pfaffSaalschutz (N : ℕ) (aa bb cc : ℚ)
    (hc : ∀ i ≤ N, cc+i ≠ 0)
    (hd : ∀ i < N, cc-aa-bb+i ≠ 0)
    (hx : ∀ m ≤ N, ∀ i < m, 1+aa+bb-cc-m+i ≠ 0) :
    psSum N aa bb cc = rf (cc-aa) N * rf (cc-bb) N /
      (rf cc N * rf (cc-aa-bb) N) := by
  induction N with
  | zero => simp [psSum, psTerm, rf]
  | succ n ih =>
    have hci : ∀ i ≤ n, cc+i ≠ 0 := fun i hi => hc i (by omega)
    have hdi : ∀ i < n, cc-aa-bb+i ≠ 0 := fun i hi => hd i (by omega)
    have hxi : ∀ m ≤ n, ∀ i < m, 1+aa+bb-cc-m+i ≠ 0 :=
      fun m hm i hi => hx m (by omega) i hi
    have ih' := ih hci hdi hxi
    let A : ℚ := (cc+n) * (cc-aa-bb+n)
    let B : ℚ := (cc-aa+n) * (cc-bb+n)
    let G : ℕ → ℚ := fun k =>
      psTerm n aa bb cc k * k * (cc+k-1) * (aa+bb-cc-n+k) / (n+1-k)
    have hpoint : ∀ k < n,
        A * psTerm (n+1) aa bb cc k - B * psTerm n aa bb cc k = G (k+1) - G k := by
      intro k hk
      have hn1 : (n+1-k:ℚ) ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (show n+1 ≠ k by omega)
      have hn0 : (n-k:ℚ) ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (show n ≠ k by omega)
      have hxb : aa+bb-cc-n ≠ 0 := by
        convert hx (n+1) (by omega) 0 (by omega) using 1 <;> norm_num <;> ring
      have hxk : aa+bb-cc-n+k ≠ 0 := by
        convert hx (n+1) (by omega) k (by omega) using 1 <;> norm_num <;> ring
      have hcck : rf cc k ≠ 0 := rf_ne_zero _ _ (fun i hi => hc i (by omega))
      have hxxk : rf (1+aa+bb-cc-n) k ≠ 0 :=
        rf_ne_zero _ _ (fun i hi => hx n (by omega) i (by omega))
      have hxxk' : rf (aa+bb-cc-n) k ≠ 0 := by
        apply rf_ne_zero
        intro i hi
        convert hx (n+1) (by omega) i (by omega) using 1 <;> norm_num <;> ring
      have hcck1 : rf cc (k+1) ≠ 0 := rf_ne_zero _ _ (fun i hi => hc i (by omega))
      have hxxk1 : rf (1+aa+bb-cc-n) (k+1) ≠ 0 :=
        rf_ne_zero _ _ (fun i hi => hx n (by omega) i (by omega))
      dsimp [A, B, G]
      convert ps_recurrence_point n k aa bb cc hk hn1 hn0 hxb hxk
        (mul_ne_zero (mul_ne_zero hcck hxxk) (by positivity))
        (mul_ne_zero (mul_ne_zero hcck hxxk') (by positivity))
        (mul_ne_zero (mul_ne_zero hcck1 hxxk1) (by positivity)) using 1 <;>
        norm_num <;> ring
    have htel : ∑ k ∈ range n,
        (A * psTerm (n+1) aa bb cc k - B * psTerm n aa bb cc k) = G n := by
      calc
        _ = ∑ k ∈ range n, (G (k+1) - G k) := by
          apply sum_congr rfl
          intro k hk
          exact hpoint k (mem_range.1 hk)
        _ = G n - G 0 := sum_range_sub G n
        _ = G n := by simp [G, psTerm]
    have htel' : (∑ k ∈ range n, A * psTerm (n+1) aa bb cc k) -
        (∑ k ∈ range n, B * psTerm n aa bb cc k) = G n := by
      rw [← sum_sub_distrib, htel]
    have hGn : G n = psTerm n aa bb cc n * n * (cc+n-1) * (aa+bb-cc) := by
      dsimp [G]
      norm_num
    rw [hGn] at htel'


    have hxb : aa+bb-cc-n ≠ 0 := by
      convert hx (n+1) (by omega) 0 (by omega) using 1 <;> norm_num <;> ring
    have hxe : aa+bb-cc ≠ 0 := by
      convert hx (n+1) (by omega) n (by omega) using 1 <;> norm_num <;> ring
    have h0 : rf cc n * rf (1+aa+bb-cc-n) n * n.factorial ≠ 0 :=
      mul_ne_zero (mul_ne_zero (rf_ne_zero _ _ (fun i hi => hc i (by omega)))
        (rf_ne_zero _ _ (fun i hi => hx n (by omega) i hi))) (by positivity)
    have h1 : rf cc n * rf (aa+bb-cc-n) n * n.factorial ≠ 0 :=
      mul_ne_zero (mul_ne_zero (rf_ne_zero _ _ (fun i hi => hc i (by omega)))
        (rf_ne_zero _ _ (fun i hi => by
          convert hx (n+1) (by omega) i (by omega) using 1 <;> norm_num <;> ring))) (by positivity)
    have h2 : rf cc (n+1) * rf (aa+bb-cc-n) (n+1) * (n+1).factorial ≠ 0 :=
      mul_ne_zero (mul_ne_zero (rf_ne_zero _ _ (fun i hi => hc i (by omega)))
        (rf_ne_zero _ _ (fun i hi => by
          convert hx (n+1) (by omega) i (by omega) using 1 <;> norm_num <;> ring))) (by positivity)
    have hb := ps_recurrence_boundary n aa bb cc hxb hxe h0 h1 h2
    have hrec : A * psSum (n+1) aa bb cc - B * psSum n aa bb cc = 0 := by
      simp only [psSum]
      rw [show n+1+1 = (n+1)+1 by omega, sum_range_succ, sum_range_succ,
        sum_range_succ]
      rw [mul_add, mul_add, mul_add]
      rw [mul_sum, mul_sum]
      dsimp [A, B] at hb htel' ⊢
      linarith
    have hA : A ≠ 0 := mul_ne_zero (hc n (by omega)) (hd n (by omega))
    have hformula : psSum (n+1) aa bb cc = B * psSum n aa bb cc / A := by
      apply (eq_div_iff hA).2
      linarith
    rw [hformula, ih']
    dsimp [A, B]
    rw [rf_succ, rf_succ, rf_succ, rf_succ]
    field_simp [hc n (by omega), hd n (by omega)]

private lemma rf_reverse_split (x : ℚ) {m l : ℕ} (hl : l ≤ m) :
    rf x (m-l) * rf (1-x-m) l = (-1)^l * rf x m := by
  induction m generalizing l with
  | zero =>
    have : l = 0 := by omega
    subst l
    simp [rf]
  | succ m ih =>
    cases l with
    | zero => simp [rf]
    | succ l =>
      have hlm : l ≤ m := by omega
      rw [Nat.succ_sub_succ_eq_sub]
      have hs := rf_shift (-(x+(m:ℚ))) l
      have hs' : rf (1-x-(m+1:ℚ)) (l+1) =
          (-(x+(m:ℚ))) * rf (1-x-m) l := by
        rw [rf_succ]
        convert hs.symm using 1 <;> ring
      norm_num only [Nat.cast_add, Nat.cast_one]
      rw [hs', rf_succ, pow_succ]
      have hi := ih hlm
      push_cast
      linear_combination -(x+m) * hi

private lemma conv_of_pfaff (m : ℕ) (A E F : ℚ)
    (hC : ∀ l ≤ m, rf (1+A-E-m) l ≠ 0)
    (hD : ∀ l ≤ m, rf (1+A-F-m) l ≠ 0)
    (hps : psSum m A (1+A-E-F-m) (1+A-E-m) =
      rf (1-E-m) m * rf F m /
        (rf (1+A-E-m) m * rf (F-A) m)) :
    (∑ l ∈ range (m+1), (-1)^l * (m.choose l : ℚ) * rf A l *
      rf (1+A-E-F-m) l * rf (E-A) (m-l) * rf (F-A) (m-l)) =
      rf E m * rf F m := by
  have hterm : ∀ l ≤ m,
      (-1)^l * (m.choose l : ℚ) * rf A l * rf (1+A-E-F-m) l *
          rf (E-A) (m-l) * rf (F-A) (m-l) =
        rf (E-A) m * rf (F-A) m * psTerm m A (1+A-E-F-m) (1+A-E-m) l := by
    intro l hl
    have he0 := rf_reverse_split (E-A) hl
    have hf0 := rf_reverse_split (F-A) hl
    have he : rf (E-A) (m-l) * rf (1+A-E-m) l =
        (-1)^l * rf (E-A) m := by convert he0 using 1 <;> ring
    have hf : rf (F-A) (m-l) * rf (1+A-F-m) l =
        (-1)^l * rf (F-A) m := by convert hf0 using 1 <;> ring
    have hneg := rf_neg_nat_choose m l
    have hfac : (l.factorial:ℚ) ≠ 0 := by positivity
    have hc := hC l hl
    have hd := hD l hl
    have heq : rf (E-A) (m-l) = ((-1)^l * rf (E-A) m) / rf (1+A-E-m) l :=
      (eq_div_iff hc).2 he
    have hfq : rf (F-A) (m-l) = ((-1)^l * rf (F-A) m) / rf (1+A-F-m) l :=
      (eq_div_iff hd).2 hf
    simp only [psTerm]
    have harg : 1+A+(1+A-E-F-m)-(1+A-E-m)-m = 1+A-F-m := by ring
    rw [harg, hneg, heq, hfq]
    field_simp [hc, hd, hfac]
    have hs : ((-1:ℚ)^l)^2 = 1 := by rw [← pow_mul]; norm_num
    rw [hs]
    simp
  calc
    _ = rf (E-A) m * rf (F-A) m * psSum m A (1+A-E-F-m) (1+A-E-m) := by
      simp only [psSum, mul_sum]
      apply sum_congr rfl
      intro l hl
      exact hterm l (by simpa using mem_range.1 hl)
    _ = rf (E-A) m * rf (F-A) m *
        (rf (1-E-m) m * rf F m /
          (rf (1+A-E-m) m * rf (F-A) m)) := by rw [hps]
    _ = rf E m * rf F m := by
      have he0 := rf_reverse_split E (show m ≤ m by rfl)
      have hea0 := rf_reverse_split (E-A) (show m ≤ m by rfl)
      have hf0 := rf_reverse_split (F-A) (show m ≤ m by rfl)
      have he : rf (1-E-m) m = (-1)^m * rf E m := by
        simpa [rf] using he0
      have hea : rf (1+A-E-m) m = (-1)^m * rf (E-A) m := by
        convert (show rf (1-(E-A)-m) m = (-1)^m * rf (E-A) m by simpa [rf] using hea0) using 1 <;> ring
      have hf : rf (1+A-F-m) m = (-1)^m * rf (F-A) m := by
        convert (show rf (1-(F-A)-m) m = (-1)^m * rf (F-A) m by simpa [rf] using hf0) using 1 <;> ring
      have hcm := hC m le_rfl
      have hfm : rf (F-A) m ≠ 0 := by
        intro hz
        apply hD m le_rfl
        rw [hf, hz]
        simp
      field_simp [hcm, hfm]
      rw [he, hea]
      ring

private lemma triangle_sum {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → ℕ → R) :
    (∑ j ∈ range (n+1), ∑ k ∈ range (j+1), f j k) =
      ∑ k ∈ range (n+1), ∑ l ∈ range (n+1-k), f (k+l) k := by
  rw [sum_sigma' (range (n+1)) (fun j => range (j+1)),
    sum_sigma' (range (n+1)) (fun k => range (n+1-k))]
  refine sum_bij'
    (fun x _ => ⟨x.2, x.1-x.2⟩)
    (fun x _ => ⟨x.1+x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j,k⟩ hx
    simp at hx ⊢
    omega
  · rintro ⟨k,l⟩ hx
    simp at hx ⊢
    omega
  · rintro ⟨j,k⟩ hx
    simp at hx ⊢
    omega
  · rintro ⟨k,l⟩ hx
    simp at hx ⊢
  · rintro ⟨j,k⟩ hx
    simp at hx ⊢
    congr 2
    omega

private def leftScaled (n : ℕ) (aa bb cc dd ee ff : ℚ) : ℚ :=
  ∑ k ∈ range (n+1), (-1)^k * (n.choose k : ℚ) * rf aa k * rf bb k * rf cc k /
    rf dd k * rf (ee+k) (n-k) * rf (ff+k) (n-k)

private def rightScaled (n : ℕ) (aa bb cc dd ee ff : ℚ) : ℚ :=
  ∑ j ∈ range (n+1), (-1)^j * (n.choose j : ℚ) * rf aa j * rf (dd-bb) j *
    rf (dd-cc) j / rf dd j * rf (ee-aa) (n-j) * rf (ff-aa) (n-j)

private lemma sears_scaled (n : ℕ) (aa bb cc dd ee ff : ℚ)
    (hbal : dd+ee+ff = 1+aa+bb+cc-n)
    (hdd : ∀ j ≤ n, rf dd j ≠ 0)
    (hdbc : ∀ j ≤ n, rf (dd-bb-cc) j ≠ 0)
    (hps : ∀ j ≤ n, psSum j bb cc dd =
      rf (dd-bb) j * rf (dd-cc) j / (rf dd j * rf (dd-bb-cc) j))
    (hconv : ∀ k ≤ n,
      (∑ l ∈ range (n-k+1), (-1)^l * ((n-k).choose l : ℚ) * rf (aa+k) l *
        rf (dd-bb-cc) l * rf (ee-aa) (n-k-l) * rf (ff-aa) (n-k-l)) =
      rf (ee+k) (n-k) * rf (ff+k) (n-k)) :
    leftScaled n aa bb cc dd ee ff = rightScaled n aa bb cc dd ee ff := by
  let pre : ℕ → ℕ → ℚ := fun j k =>
    (-1)^j * (n.choose j : ℚ) * rf aa j * rf (ee-aa) (n-j) * rf (ff-aa) (n-j) *
      rf (dd-bb-cc) j * psTerm j bb cc dd k
  have hrpre : rightScaled n aa bb cc dd ee ff =
      ∑ j ∈ range (n+1), ∑ k ∈ range (j+1), pre j k := by
    simp only [rightScaled]
    apply sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using mem_range.1 hj
    have hdj := hdd j hjn
    have hbcj := hdbc j hjn
    rw [show (∑ k ∈ range (j+1), pre j k) =
        (-1)^j * (n.choose j : ℚ) * rf aa j * rf (ee-aa) (n-j) * rf (ff-aa) (n-j) *
          rf (dd-bb-cc) j * psSum j bb cc dd by
      simp only [pre, psSum, mul_sum]]
    rw [hps j hjn]
    field_simp [hdj, hbcj]
  have hpre : ∀ k l, k+l ≤ n →
      pre (k+l) k =
        ((-1)^k * (n.choose k : ℚ) * rf aa k * rf bb k * rf cc k / rf dd k) *
        ((-1)^l * ((n-k).choose l : ℚ) * rf (aa+k) l * rf (dd-bb-cc) l *
          rf (ee-aa) (n-k-l) * rf (ff-aa) (n-k-l)) := by
    intro k l hkl
    have hk : k ≤ k+l := Nat.le_add_right _ _
    have hkn : k ≤ n := hk.trans hkl
    have hjn : k+l ≤ n := hkl
    have hchoose0 := Nat.choose_mul (n := n) (k := k+l) (s := k) hk
    have hchoose : (n.choose (k+l) : ℚ) * ((k+l).choose k : ℚ) =
        (n.choose k : ℚ) * ((n-k).choose l : ℚ) := by
      exact_mod_cast (by simpa using hchoose0)
    have ha := rf_add aa k l
    have hx := rf_add (dd-bb-cc) l k
    have hrev0 := rf_reverse_split (dd-bb-cc) (m := k+l) (l := k) hk
    have hrev : rf (dd-bb-cc) l * rf (1-(dd-bb-cc)-(k+l)) k =
        (-1)^k * rf (dd-bb-cc) (k+l) := by
      rw [Nat.add_sub_cancel_left] at hrev0
      simpa only [Nat.cast_add] using hrev0
    have hdenarg : 1+bb+cc-dd-(k+l) = 1-(dd-bb-cc)-(k+l) := by ring
    have hdk := hdd k hkn
    have hrevden : rf (1+bb+cc-dd-(k+l)) k ≠ 0 := by
      rw [hdenarg]
      intro hz
      rw [hz, mul_zero] at hrev
      have hxbc := hdbc (k+l) hjn
      exact hxbc (by
        have hs : ((-1:ℚ)^k) ≠ 0 := by positivity
        exact (mul_eq_zero.mp hrev.symm).resolve_left hs)
    have hrevden2 : rf (1-(dd-bb-cc)-((k:ℚ)+l)) k ≠ 0 := by
      rw [← hdenarg]
      exact hrevden

    simp only [pre, psTerm]
    norm_num only [Nat.cast_add]
    have hneg : rf (-((k:ℚ)+l)) k = (-1)^k * k.factorial * (k+l).choose k := by
      convert rf_neg_nat_choose (k+l) k using 1 <;> norm_num
    rw [hneg, hdenarg]
    have hfac : (k.factorial:ℚ) ≠ 0 := by positivity
    field_simp [hdk, hrevden, hrevden2, hfac]
    rw [ha]
    have hsub : n-(k+l) = n-k-l := by omega
    rw [hsub]
    norm_num only [Nat.cast_add]
    have hp : (-1:ℚ)^(k+l) = (-1)^k * (-1)^l := by rw [pow_add]
    rw [hp]
    linear_combination
      (rf aa k * rf (aa+k) l * rf bb k * rf cc k *
        rf (ee-aa) (n-k-l) * rf (ff-aa) (n-k-l) * (-1)^k * (-1)^l *
        rf (dd-bb-cc) (k+l)) * hchoose -
      ((n.choose k : ℚ) * ((n-k).choose l : ℚ) * rf aa k * rf (aa+k) l *
        rf bb k * rf cc k * rf (ee-aa) (n-k-l) * rf (ff-aa) (n-k-l) *
        (-1)^l) * hrev
  calc
    leftScaled n aa bb cc dd ee ff =
        ∑ k ∈ range (n+1),
          ((-1)^k * (n.choose k : ℚ) * rf aa k * rf bb k * rf cc k / rf dd k) *
          (∑ l ∈ range (n-k+1), (-1)^l * ((n-k).choose l : ℚ) * rf (aa+k) l *
            rf (dd-bb-cc) l * rf (ee-aa) (n-k-l) * rf (ff-aa) (n-k-l)) := by
      simp only [leftScaled]
      apply sum_congr rfl
      intro k hk
      rw [hconv k (by simpa using mem_range.1 hk)]
      ring
    _ = ∑ k ∈ range (n+1), ∑ l ∈ range (n+1-k), pre (k+l) k := by
      apply sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by simpa using mem_range.1 hk
      rw [mul_sum]
      apply sum_congr
      · congr 1; omega
      intro l hl
      have hll : l < n+1-k := mem_range.1 hl
      rw [hpre k l (by omega)]
    _ = ∑ j ∈ range (n+1), ∑ k ∈ range (j+1), pre j k := by
      exact (triangle_sum n pre).symm
    _ = rightScaled n aa bb cc dd ee ff := hrpre.symm






private lemma rf_nat_factorial (m k : ℕ) :
    rf (m+1:ℚ) k = (m+k).factorial / m.factorial := by
  induction k with
  | zero =>
    simp [rf]
    field_simp
  | succ k ih =>
    rw [rf_succ, ih, Nat.add_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

private lemma rf_pair (x : ℚ) (k : ℕ) :
    rf (x/2) k * rf ((x+1)/2) k = rf x (2*k) / 4^k := by
  induction k with
  | zero => simp [rf]
  | succ k ih =>
    rw [rf_succ, rf_succ]
    calc
      _ = (rf (x/2) k * rf ((x+1)/2) k) *
          ((x/2+k) * ((x+1)/2+k)) := by ring
      _ = (rf x (2*k) / 4^k) * ((x/2+k) * ((x+1)/2+k)) := by rw [ih]
      _ = rf x (2*(k+1)) / 4^(k+1) := by
        rw [show 2*(k+1) = 2*k+2 by omega, rf_succ, rf_succ, pow_succ]
        push_cast
        field_simp
        ring

private lemma rf_half_factorial (n k : ℕ) :
    rf ((2*n+1:ℚ)/2) k =
      (2*n+2*k).factorial * n.factorial /
        ((2*n).factorial * (n+k).factorial * 4^k) := by
  induction k with
  | zero =>
    simp [rf]
    field_simp
  | succ k ih =>
    rw [rf_succ, ih]
    rw [show 2*n+2*(k+1) = (2*n+2*k+1)+1 by omega,
      Nat.factorial_succ (2*n+2*k+1), Nat.factorial_succ (2*n+2*k),
      show n+(k+1) = n+k+1 by omega, Nat.factorial_succ (n+k), pow_succ]
    push_cast
    field_simp
    ring



private lemma special_sears_scaled (n : ℕ) (hn : 0 < n) :
    leftScaled n (-(n:ℚ)) ((3*n+1:ℚ)/2) ((3*n+2:ℚ)/2)
        ((2*n+1:ℚ)/2) 1 1 =
      rightScaled n (-(n:ℚ)) ((3*n+1:ℚ)/2) ((3*n+2:ℚ)/2)
        ((2*n+1:ℚ)/2) 1 1 := by
  let aa : ℚ := -(n:ℚ)
  let bb : ℚ := (3*n+1)/2
  let cc : ℚ := (3*n+2)/2
  let dd : ℚ := (2*n+1)/2
  have hdd : ∀ j ≤ n, rf dd j ≠ 0 := by
    intro j hj
    apply rf_ne_zero
    intro i hi
    dsimp [dd]
    positivity
  have hdbc : ∀ j ≤ n, rf (dd-bb-cc) j ≠ 0 := by
    intro j hj
    apply rf_ne_zero
    intro i hi
    dsimp [dd,bb,cc]
    push_cast
    have hin : (i:ℚ) < n := by exact_mod_cast (lt_of_lt_of_le hi hj)
    norm_num
    linarith
  have hps : ∀ j ≤ n, psSum j bb cc dd =
      rf (dd-bb) j * rf (dd-cc) j / (rf dd j * rf (dd-bb-cc) j) := by
    intro j hj
    apply pfaffSaalschutz
    · intro i hi
      dsimp [dd]
      positivity
    · intro i hi
      dsimp [dd,bb,cc]
      push_cast
      have hin : (i:ℚ) < n := by exact_mod_cast (lt_of_lt_of_le hi hj)
      norm_num
      linarith
    · intro m hm i hi
      dsimp [dd,bb,cc]
      push_cast
      have hmn : (m:ℚ) ≤ n := by exact_mod_cast hm.trans hj
      norm_num
      linarith
  have hconv : ∀ k ≤ n,
      (∑ l ∈ range (n-k+1), (-1)^l * ((n-k).choose l : ℚ) * rf (aa+k) l *
        rf (dd-bb-cc) l * rf (1-aa) (n-k-l) * rf (1-aa) (n-k-l)) =
        rf (1+k) (n-k) * rf (1+k) (n-k) := by
    intro k hkn
    let m := n-k
    let A : ℚ := aa+k
    let E : ℚ := 1+k
    have hc : ∀ i ≤ m, (1+A-E-m)+i ≠ 0 := by
      intro i hi
      dsimp [m,A,E,aa]
      rw [Nat.cast_sub hkn]
      push_cast
      have hki : k+i ≤ n := by dsimp [m] at hi; omega
      have hkiq : (k:ℚ)+i ≤ n := by exact_mod_cast hki
      have hnq : (0:ℚ) < n := by exact_mod_cast hn

      norm_num
      linarith
    have hd : ∀ i < m, (1+A-E-m)-A-(1+A-E-E-m)+i ≠ 0 := by
      intro i hi
      dsimp [m,A,E,aa]
      rw [Nat.cast_sub hkn]
      push_cast
      have hnq : (0:ℚ) < n := by exact_mod_cast hn
      norm_num
      linarith
    have hx : ∀ r ≤ m, ∀ i < r,
        1+A+(1+A-E-E-m)-(1+A-E-m)-r+i ≠ 0 := by
      intro r hr i hi
      dsimp [m,A,E,aa]
      rw [Nat.cast_sub hkn]
      push_cast
      have hkr : k+r ≤ n := by dsimp [m] at hr; omega
      have hkrq : (k:ℚ)+r ≤ n := by exact_mod_cast hkr
      have hiq : (i:ℚ) < r := by exact_mod_cast hi
      norm_num
      linarith
    have hpf0 := pfaffSaalschutz m A (1+A-E-E-m) (1+A-E-m) hc hd hx
    have hpf : psSum m A (1+A-E-E-m) (1+A-E-m) =
        rf (1-E-m) m * rf E m / (rf (1+A-E-m) m * rf (E-A) m) := by
      convert hpf0 using 1 <;> ring
    have hrf : ∀ l ≤ m, rf (1+A-E-m) l ≠ 0 := by
      intro l hl
      exact rf_ne_zero _ _ (fun i hi => hc i (by omega))
    have hcv := conv_of_pfaff m A E E hrf hrf hpf
    dsimp [m,A,E,aa,bb,cc,dd] at hcv ⊢
    rw [Nat.cast_sub hkn] at hcv
    convert hcv using 1 <;> norm_num <;> ring
  have hs := sears_scaled n aa bb cc dd 1 1 (by
    dsimp [aa,bb,cc,dd]
    ring) hdd hdbc hps hconv
  simpa [aa,bb,cc,dd] using hs


private lemma left_term_eq (n k : ℕ) (hk : k ≤ n) :
    (-1)^k * (n.choose k : ℚ) * rf (-(n:ℚ)) k *
        rf ((3*n+1:ℚ)/2) k * rf ((3*n+2:ℚ)/2) k /
        rf ((2*n+1:ℚ)/2) k * rf (1+k) (n-k) * rf (1+k) (n-k) =
      (n.factorial:ℚ)^2 / (Nat.choose (3*n) n : ℚ) *
        ((n.choose k : ℚ)^2 * (Nat.choose (n+k) k : ℚ) *
          (Nat.choose (3*n+2*k) n : ℚ)) := by
  have hpair0 := rf_pair (3*n+1:ℚ) k
  have hpair : rf ((3*n+1:ℚ)/2) k * rf ((3*n+2:ℚ)/2) k =
      rf (3*n+1:ℚ) (2*k) / 4^k := by
    convert hpair0 using 1 <;> ring
  have hrfbig := rf_nat_factorial (3*n) (2*k)
  have hrftail := rf_nat_factorial k (n-k)
  have hrfbig' : rf (3*(n:ℚ)+1) (2*k) =
      (3*n+2*k).factorial / (3*n).factorial := by
    simpa only [Nat.cast_mul] using hrfbig
  have hsum : k+(n-k) = n := by omega
  rw [hsum] at hrftail
  have hrftail' : rf (1+(k:ℚ)) (n-k) = (n.factorial:ℚ) / k.factorial := by
    convert hrftail using 1 <;> ring

  have hhalf := rf_half_factorial n k
  have hneg := rf_neg_nat_choose n k
  rw [show (-1)^k * (n.choose k : ℚ) * rf (-(n:ℚ)) k *
      rf ((3*n+1:ℚ)/2) k * rf ((3*n+2:ℚ)/2) k =
      ((-1)^k * (n.choose k : ℚ) * rf (-(n:ℚ)) k) *
        (rf ((3*n+1:ℚ)/2) k * rf ((3*n+2:ℚ)/2) k) by ring]

  rw [hpair, hrfbig', hrftail', hhalf, hneg]
  have h3 : n ≤ 3*n := by omega
  have hnk2 : k ≤ n+k := Nat.le_add_left _ _
  have hb : n ≤ 3*n+2*k := by omega
  rw [Nat.cast_choose ℚ hk, Nat.cast_choose ℚ h3,
    Nat.cast_choose ℚ hnk2, Nat.cast_choose ℚ hb]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  rw [show 3*n-n=2*n by omega,
    show n+k-k=n by omega, show 3*n+2*k-n=2*n+2*k by omega]
  field_simp
  have hs : ((-1:ℚ)^k)^2 = 1 := by rw [← pow_mul]; norm_num
  rw [hs]

private lemma leftScaled_special (n : ℕ) :
    leftScaled n (-(n:ℚ)) ((3*n+1:ℚ)/2) ((3*n+2:ℚ)/2)
        ((2*n+1:ℚ)/2) 1 1 =
      (n.factorial:ℚ)^2 / (Nat.choose (3*n) n : ℚ) * (a n : ℚ) := by
  simp only [leftScaled, a, Nat.cast_sum]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using mem_range.1 hk
  convert left_term_eq n k hkn using 1 <;> norm_num <;> ring

private def qTerm (n k : ℕ) : ℚ :=
  (n.choose k : ℚ)^2 * (Nat.choose (n+1) (2*k) : ℚ) * (Nat.choose (n+k) k : ℚ) /
    ((Nat.choose (2*n) k : ℚ)^2 * (Nat.choose (2*n+2*k) (2*k) : ℚ))

private lemma right_term_eq (n k : ℕ) (hk : k ≤ n) :
    (-1)^k * (n.choose k : ℚ) * rf (-(n:ℚ)) k * rf (-(n:ℚ)/2) k *
        rf (-(n+1:ℚ)/2) k / rf ((2*n+1:ℚ)/2) k *
        rf (n+1:ℚ) (n-k) * rf (n+1:ℚ) (n-k) =
      (n.factorial:ℚ)^2 * (Nat.choose (2*n) n : ℚ)^2 * qTerm n k := by
  have hp0 := rf_pair (-(n+1:ℚ)) k
  have hp : rf (-(n:ℚ)/2) k * rf (-(n+1:ℚ)/2) k =
      rf (-(n+1:ℚ)) (2*k) / 4^k := by
    rw [mul_comm]
    convert hp0 using 1 <;> ring
  rw [show (-1)^k * (n.choose k : ℚ) * rf (-(n:ℚ)) k * rf (-(n:ℚ)/2) k *
      rf (-(n+1:ℚ)/2) k =
      ((-1)^k * (n.choose k : ℚ) * rf (-(n:ℚ)) k) *
        (rf (-(n:ℚ)/2) k * rf (-(n+1:ℚ)/2) k) by ring, hp]
  have hnneg := rf_neg_nat_choose n k
  have hn1neg := rf_neg_nat_choose (n+1) (2*k)
  have hn1neg' : rf (-((n:ℚ)+1)) (2*k) =
      (-1)^(2*k) * (2*k).factorial * (n+1).choose (2*k) := by
    convert hn1neg using 1 <;> norm_num <;> ring

  have hhalf := rf_half_factorial n k
  have htail0 := rf_nat_factorial n (n-k)
  have htail : rf (n+1:ℚ) (n-k) = (2*n-k).factorial / n.factorial := by
    rw [show n+(n-k)=2*n-k by omega] at htail0
    exact htail0
  rw [hnneg, hn1neg', hhalf, htail]
  by_cases h2 : 2*k ≤ n+1
  · have hc0 : n.choose k ≠ 0 := Nat.choose_ne_zero hk
    have hc1 : Nat.choose (n+1) (2*k) ≠ 0 := Nat.choose_ne_zero h2
    have hk2n : k ≤ 2*n := by omega
    have h2big : 2*k ≤ 2*n+2*k := by omega
    have hkn : k ≤ n+k := Nat.le_add_left _ _
    have hn2 : n ≤ 2*n := by omega
    simp only [qTerm]
    rw [Nat.cast_choose ℚ hk, Nat.cast_choose ℚ h2,
      Nat.cast_choose ℚ hk2n, Nat.cast_choose ℚ h2big,
      Nat.cast_choose ℚ hkn, Nat.cast_choose ℚ hn2]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    rw [show 2*n+2*k-2*k=2*n by omega,
      show n+k-k=n by omega, show 2*n-n=n by omega]
    field_simp
    have hs1 : ((-1:ℚ)^k)^2 = 1 := by rw [← pow_mul]; norm_num
    have hs2 : (-1:ℚ)^(2*k) = 1 := by
      rw [show 2*k=k+k by omega, pow_add]
      simpa [pow_two] using hs1
    rw [hs1, hs2]
    norm_num
  · have hz : Nat.choose (n+1) (2*k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [qTerm, hz, Nat.cast_zero, mul_zero, zero_mul, zero_div]

private lemma rightScaled_special (n : ℕ) :
    rightScaled n (-(n:ℚ)) ((3*n+1:ℚ)/2) ((3*n+2:ℚ)/2)
        ((2*n+1:ℚ)/2) 1 1 =
      (n.factorial:ℚ)^2 * (Nat.choose (2*n) n : ℚ)^2 *
        (∑ k ∈ range (n+1), qTerm n k) := by
  simp only [rightScaled]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using mem_range.1 hk
  have ht := right_term_eq n k hkn
  convert ht using 1 <;> norm_num <;> ring



private lemma transformed_identity (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = (Nat.choose (3*n) n : ℚ) * (Nat.choose (2*n) n : ℚ)^2 *
      (∑ k ∈ range (n+1), qTerm n k) := by
  have hs := special_sears_scaled n hn
  rw [leftScaled_special, rightScaled_special] at hs
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  have hc0 : Nat.choose (3*n) n ≠ 0 := Nat.choose_ne_zero (by omega)
  have hc : (Nat.choose (3*n) n : ℚ) ≠ 0 := by exact_mod_cast hc0
  field_simp at hs ⊢
  nlinarith


private lemma padicVal_choose_lt_sq {p N K : ℕ} (hp : Nat.Prime p)
    (hK : K ≤ N) (hN : N < p^2) :
    padicValNat p (N.choose K) = if p ≤ K % p + (N-K) % p then 1 else 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases hN0 : N = 0
  · subst N
    have : K = 0 := by omega
    subst K
    simp [padicValNat.one, hp.ne_zero, hp.ne_one]
  rw [padicValNat_choose hK ((Nat.log_lt_iff_lt_pow hp.one_lt hN0).2 hN)]
  have hi : Finset.Ico 1 2 = {1} := by ext i; simp
  rw [hi]
  rw [Finset.filter_singleton]
  simp only [pow_one]
  by_cases h : p ≤ K % p + (N-K) % p
  · rw [if_pos h]
    simp [h]
  · rw [if_neg h]
    simp [h]


private lemma mod_eq_sub_of_le_of_lt_two_mul {x p : ℕ} (h₁ : p ≤ x) (h₂ : x < 2*p) :
    x % p = x-p := by
  rw [Nat.mod_eq_sub_mod h₁, Nat.mod_eq_of_lt (by omega)]

private lemma qTerm_val_nonneg (p n k : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hnp : n < p) (hlow : 2*p < 3*n) (hk : k ≤ n) (hsupp : 2*k ≤ n+1) :
    0 ≤ padicValRat p (qTerm n k) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp2 : 2*n < p^2 := by nlinarith
  have hp3 : 2*n+2*k < p^2 := by nlinarith
  have hpn : p ≤ 2*n := by omega
  have hkp : k < p := by omega
  have h2kp : 2*k < p := by
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    rcases hpodd with ⟨j, hj⟩
    omega
  have hCnk : n.choose k ≠ 0 := Nat.choose_ne_zero hk
  have hCn1 : (n+1).choose (2*k) ≠ 0 := Nat.choose_ne_zero hsupp
  have hCnk' : (n+k).choose k ≠ 0 := Nat.choose_ne_zero (by omega)
  have hC2 : (2*n).choose k ≠ 0 := Nat.choose_ne_zero (by omega)
  have hCbig : (2*n+2*k).choose (2*k) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hv2 : padicValNat p ((2*n).choose k) = 0 := by
    rw [padicVal_choose_lt_sq hp (by omega) hp2]
    rw [Nat.mod_eq_of_lt hkp]
    have hsub : 2*n-k < 2*p := by omega
    by_cases hh : p ≤ 2*n-k
    · rw [mod_eq_sub_of_le_of_lt_two_mul hh hsub]
      rw [if_neg (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
      rw [if_neg (by omega)]
  have hvbig_le : padicValNat p ((2*n+2*k).choose (2*k)) ≤ 1 := by
    rw [padicVal_choose_lt_sq hp (by omega) hp3]
    split_ifs <;> omega
  have hvcomp : padicValNat p ((2*n+2*k).choose (2*k)) ≤
      padicValNat p ((n+k).choose k) := by
    by_cases hv : padicValNat p ((2*n+2*k).choose (2*k)) = 0
    · omega
    have hvone : padicValNat p ((2*n+2*k).choose (2*k)) = 1 := by omega
    rw [hvone]
    apply one_le_padicValNat_of_dvd hCnk'
    apply hp.dvd_choose
    · exact hkp
    · omega
    · have : 2*p ≤ 2*n+2*k := by
        -- nonzero valuation forces the top to cross the second multiple of p
        by_contra hh
        have htop : 2*n+2*k < 2*p := by omega
        have hvzero : padicValNat p ((2*n+2*k).choose (2*k)) = 0 := by
          rw [padicVal_choose_lt_sq hp (by omega) hp3]
          rw [Nat.mod_eq_of_lt h2kp, show 2*n+2*k-2*k=2*n by omega]
          have hc : 2*n < 2*p := by omega
          rw [mod_eq_sub_of_le_of_lt_two_mul (by omega : p ≤ 2*n) hc]
          rw [if_neg (by omega)]
        exact hv hvzero
      omega
  simp only [qTerm]
  have hA : (n.choose k : ℚ) ≠ 0 := by exact_mod_cast hCnk
  have hB : (Nat.choose (n+1) (2*k) : ℚ) ≠ 0 := by exact_mod_cast hCn1
  have hC : (Nat.choose (n+k) k : ℚ) ≠ 0 := by exact_mod_cast hCnk'
  have hD : (Nat.choose (2*n) k : ℚ) ≠ 0 := by exact_mod_cast hC2
  have hE : (Nat.choose (2*n+2*k) (2*k) : ℚ) ≠ 0 := by exact_mod_cast hCbig
  rw [padicValRat.div (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hA) hB) hC)
      (mul_ne_zero (pow_ne_zero 2 hD) hE),
    padicValRat.mul (mul_ne_zero (pow_ne_zero 2 hA) hB) hC,
    padicValRat.mul (pow_ne_zero 2 hA) hB, padicValRat.pow hA,
    padicValRat.mul (pow_ne_zero 2 hD) hE, padicValRat.pow hD]
  simp only [padicValRat.of_nat]
  omega

private lemma padicVal_sum_nonneg {p : ℕ} (hp : Nat.Prime p) (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ i ∈ s, 0 ≤ padicValRat p (f i)) :
    0 ≤ padicValRat p (∑ i ∈ s, f i) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  classical
  induction s using Finset.induction_on with
  | empty => simp [padicValRat.zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      by_cases hz : f i + ∑ j ∈ s, f j = 0
      · rw [hz, padicValRat.zero]
      · have hm := padicValRat.min_le_padicValRat_add (p := p) hz
        have hfi := hf i (by simp)
        have hsum := ih (fun j hj => hf j (by simp [hj]))
        omega

private lemma a_pos (n : ℕ) : 0 < a n := by
  unfold a
  apply Finset.sum_pos'
  · intro i hi
    positivity
  · refine ⟨0, by simp, ?_⟩
    simp
    exact Nat.choose_pos (by omega)

private lemma main_divisibility (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hnp : n < p) (hlow : 2*p < 3*n) : p^3 ∣ a n := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hn : 0 < n := by omega
  have h3p : 3*p ≤ p*p := Nat.mul_le_mul_right p (by omega)
  have hpSq3 : 3*n < p^2 := by rw [pow_two]; omega
  have hpSq2 : 2*n < p^2 := by rw [pow_two]; omega
  have hpn2 : p ≤ 2*n := by omega
  have hnmod : n % p = n := Nat.mod_eq_of_lt hnp
  have h2nmod : (2*n) % p = 2*n-p :=
    mod_eq_sub_of_le_of_lt_two_mul hpn2 (by omega)
  have hv3 : padicValNat p ((3*n).choose n) = 1 := by
    rw [padicVal_choose_lt_sq hp (by omega) hpSq3, hnmod]
    have hrem : (3*n-n) % p = 2*n-p := by
      rw [show 3*n-n=2*n by omega, h2nmod]
    rw [hrem, if_pos (by omega)]
  have hv2 : padicValNat p ((2*n).choose n) = 1 := by
    rw [padicVal_choose_lt_sq hp (by omega) hpSq2, hnmod]
    have hrem : (2*n-n) % p = n := by
      rw [show 2*n-n=n by omega, hnmod]
    rw [hrem, if_pos (by omega : p ≤ n+n)]
  have hterms : ∀ k ∈ range (n+1), 0 ≤ padicValRat p (qTerm n k) := by
    intro k hk
    have hkn : k ≤ n := by simpa using mem_range.1 hk
    by_cases hs : 2*k ≤ n+1
    · exact qTerm_val_nonneg p n k hp hp5 hnp hlow hkn hs
    · have hz : (n+1).choose (2*k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [qTerm, hz, padicValRat.zero]
  have hvsum : 0 ≤ padicValRat p (∑ k ∈ range (n+1), qTerm n k) :=
    padicVal_sum_nonneg hp _ _ hterms
  have hid := transformed_identity n hn
  have ha0 : (a n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (a_pos n).ne'
  have hc30 : (Nat.choose (3*n) n : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  have hc20 : (Nat.choose (2*n) n : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  have hsum0 : (∑ k ∈ range (n+1), qTerm n k) ≠ 0 := by
    intro hz
    rw [hz] at hid
    simp at hid
    exact (a_pos n).ne' hid
  have hva : (3:ℤ) ≤ padicValRat p (a n : ℚ) := by
    rw [hid, padicValRat.mul (mul_ne_zero hc30 (pow_ne_zero 2 hc20)) hsum0,
      padicValRat.mul hc30 (pow_ne_zero 2 hc20), padicValRat.pow hc20]
    simp only [padicValRat.of_nat]
    omega
  apply (padicValNat_dvd_iff_le (a_pos n).ne').2
  have hva' : (3:ℤ) ≤ (padicValNat p (a n) : ℤ) := by simpa using hva
  exact Int.ofNat_le.mp hva'


/--
Conjecture: for prime $p \ge 5$, $a(n)$ is divisible by $p^3$ for integer $n$ in the interval $[\lceil\frac{2p + 1}{3}\rceil, p - 1]$.
The lower bound $\lceil\frac{2p + 1}{3}\rceil$ for $p \in \mathbb{N}$ is expressed using natural number division as $(2 * p + 1 + 2) / 3 = (2 * p + 3) / 3$.
-/
theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hlo hhi
  have hnp : n < p := by omega
  have hbound : 2*p+3 ≤ n*3+3-1 :=
    (Nat.div_le_iff_le_mul (by omega : 0 < 3)).1 hlo
  have hlow : 2*p < 3*n := by omega
  exact main_divisibility p n hp hp5 hnp hlow
