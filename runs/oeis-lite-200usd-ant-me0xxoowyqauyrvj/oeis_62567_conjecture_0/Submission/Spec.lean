import FormalConjectures.Util.ProblemImports

open Nat Classical

/-- The number whose digits in base 10 are $n$'s digits reversed. -/
def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

/--
A062567: First multiple of $n$ whose reverse is also divisible by $n$, or 0 if no such multiple exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- P(k) is the predicate for the multiplier k: k > 0 and n divides the reverse of (k*n).
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)

    -- We check if a solution exists (using classical reasoning, since P is decidable).
    if h_ex : ∃ k, P k then
      -- Nat.find requires a DecidablePred instance, which holds for this property on ℕ.
      have HP : DecidablePred P := by infer_instance
      -- k_min is the smallest multiplier k >= 1.
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

namespace OEIS62567


/-- Generic cubing step for the valuation induction. -/
theorem cube_step (j A : ℕ) (h1 : 1 ≤ A) (hmod : A % 3 = 1) (hdvd : (3:ℕ)^j ∣ A - 1) :
    (3:ℕ)^(j+1) ∣ A^3 - 1 := by
  obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
  have hfac : (B+1)^3 - 1 = ((B+1) - 1) * ((B+1)^2 + (B+1) + 1) := by
    simp only [Nat.add_sub_cancel]
    have : B * ((B+1)^2 + (B+1) + 1) = (B+1)^3 - 1 := by
      have h0 : (B+1)^3 = B * ((B+1)^2 + (B+1) + 1) + 1 := by ring
      omega
    omega
  have h3dvd : (3:ℕ) ∣ ((B+1)^2 + (B+1) + 1) := by
    have : ((B+1)^2 + (B+1) + 1) % 3 = 0 := by
      rw [Nat.add_mod, Nat.add_mod ((B+1)^2), Nat.pow_mod, hmod]
    omega
  rw [hfac, pow_succ]
  exact Nat.mul_dvd_mul (by simpa using hdvd) h3dvd

/-- v3 lemma: 3^(k+2) divides 10^(3^k) - 1. -/
theorem three_pow_dvd (k : ℕ) : (3:ℕ)^(k+2) ∣ 10^(3^k) - 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hpow : (10:ℕ)^(3^(k+1)) = (10^(3^k))^3 := by
      rw [show (3:ℕ)^(k+1) = 3^k * 3 from by ring, pow_mul]
    have hmod : (10^(3^k)) % 3 = 1 := by
      rw [Nat.pow_mod, show (10:ℕ) % 3 = 1 from by decide, one_pow]; rfl
    have h1 : 1 ≤ (10:ℕ)^(3^k) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [hpow]
    exact cube_step (k+2) _ h1 hmod ih

/-- ofDigits of a repunit-of-9s. -/
theorem ofDigits_replicate_nine (d : ℕ) :
    ofDigits 10 (List.replicate d 9) = 10^d - 1 := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [List.replicate_succ, ofDigits_cons, ih, pow_succ]
    have : 1 ≤ (10:ℕ)^d := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega

/-- digits of a repunit-of-9s. -/
theorem digits_repunit (d : ℕ) :
    digits 10 (10^d - 1) = List.replicate d 9 := by
  rw [← ofDigits_replicate_nine d]
  apply digits_ofDigits 10 (by norm_num)
  · intro l hl
    rw [List.eq_of_mem_replicate hl]; norm_num
  · intro h
    rw [List.getLast_replicate]; norm_num

/-- The repunit is a palindrome under reverse_nat. -/
theorem reverse_nat_repunit (d : ℕ) :
    reverse_nat (10^d - 1) = 10^d - 1 := by
  unfold reverse_nat
  rw [digits_repunit, List.reverse_replicate, ofDigits_replicate_nine]

/- ## Digit-sum lemma (base cases) -/

/-- Weighted index sum: `wsum l = Σ i * l[i]`. -/
def wsum : List ℕ → ℕ
  | [] => 0
  | _ :: l => l.sum + wsum l

@[simp] theorem wsum_nil : wsum [] = 0 := rfl
theorem wsum_cons (a : ℕ) (l : List ℕ) : wsum (a :: l) = l.sum + wsum l := rfl

theorem wsum_append (p q : List ℕ) :
    wsum (p ++ q) = wsum p + p.length * q.sum + wsum q := by
  induction p with
  | nil => simp [wsum]
  | cons a p ih =>
    rw [List.cons_append, wsum_cons, wsum_cons, ih, List.sum_append, List.length_cons]
    ring

theorem wsum_reverse_identity (l : List ℕ) :
    wsum l + wsum l.reverse + l.sum = l.length * l.sum := by
  induction l with
  | nil => simp [wsum]
  | cons a t ih =>
    rw [List.reverse_cons, wsum_cons, wsum_append, List.length_reverse,
      List.sum_cons, List.length_cons]
    simp only [wsum_cons, wsum_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    nlinarith [ih]

/-- Key congruence: `ofDigits 10 l ≡ l.sum + 9 * wsum l (mod M)` when `81 ≡ 0 (mod M)`. -/
theorem key (M : ℕ) (h81 : (81 : ZMod M) = 0) (l : List ℕ) :
    ((ofDigits 10 l : ℕ) : ZMod M) = (l.sum : ZMod M) + 9 * (wsum l : ZMod M) := by
  induction l with
  | nil => simp [wsum]
  | cons a t ih =>
    rw [ofDigits_cons, wsum_cons, List.sum_cons]
    push_cast at ih ⊢
    linear_combination 10 * ih + (wsum t : ZMod M) * h81

/-- If `M ∣ 81`, `M ∣ m` and `M ∣ reverse_nat m`, then `M` divides the digit sum of `m`. -/
theorem digitsum_dvd (M : ℕ) (hM81 : M ∣ 81) (m : ℕ)
    (hm : M ∣ m) (hr : M ∣ reverse_nat m) : M ∣ (digits 10 m).sum := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · simp
  have hLpos : 1 ≤ (digits 10 m).length := by
    rw [Nat.one_le_iff_ne_zero, Ne, List.length_eq_zero_iff]
    exact Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have h81 : (81 : ZMod M) = 0 := by
    rw [← Nat.cast_ofNat]; exact (ZMod.natCast_eq_zero_iff 81 M).mpr hM81
  -- abbreviations
  set S0 := (digits 10 m).sum with hS0
  set L := (digits 10 m).length with hL
  -- congruences in ZMod M
  have hmz : (m : ZMod M) = 0 := (ZMod.natCast_eq_zero_iff m M).mpr hm
  have hrz : ((reverse_nat m : ℕ) : ZMod M) = 0 :=
    (ZMod.natCast_eq_zero_iff _ M).mpr hr
  have km : (m : ZMod M) = (S0 : ZMod M) + 9 * (wsum (digits 10 m) : ZMod M) := by
    have := key M h81 (digits 10 m)
    rwa [ofDigits_digits 10 m] at this
  have kr : (0 : ZMod M)
      = (S0 : ZMod M) + 9 * (wsum (digits 10 m).reverse : ZMod M) := by
    have := key M h81 (digits 10 m).reverse
    rw [List.sum_reverse] at this
    rw [← hrz]
    convert this using 2
  -- identity, cast to ZMod
  have hidz : (wsum (digits 10 m) : ZMod M) + (wsum (digits 10 m).reverse : ZMod M)
      + (S0 : ZMod M) = (L : ZMod M) * (S0 : ZMod M) := by
    have := congrArg (Nat.cast (R := ZMod M)) (wsum_reverse_identity (digits 10 m))
    push_cast at this
    rw [hS0, hL]; push_cast; linear_combination this
  rw [hmz] at km
  -- derive (S0)*(9L - 7) = 0 in ZMod M
  have hfinal : (S0 : ZMod M) * (9 * (L : ZMod M) - 7) = 0 := by
    linear_combination -km - kr - 9 * hidz
  -- transfer to ℕ
  have hdvdmul : M ∣ S0 * (9 * L - 7) := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.sub_add_cancel]
    rw [Nat.cast_sub (by omega : 7 ≤ 9 * L)]
    push_cast
    linear_combination hfinal
  -- coprimality
  have hcop : Nat.Coprime M (9 * L - 7) := by
    apply Nat.Coprime.coprime_dvd_left hM81
    have h3 : ¬ (3 ∣ (9 * L - 7)) := by omega
    have : Nat.Coprime 3 (9 * L - 7) :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3
    simpa using this.pow_left 4
  exact hcop.dvd_of_dvd_mul_right hdvdmul

/-- A list with entries `≤ 9` and digit-sum `≥ 9 * length` is all nines. -/
theorem all_nine (l : List ℕ) (hle : ∀ x ∈ l, x ≤ 9) (hsum : 9 * l.length ≤ l.sum) :
    l = List.replicate l.length 9 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha : a ≤ 9 := hle a (by simp)
    have ht : ∀ x ∈ t, x ≤ 9 := fun x hx => hle x (List.mem_cons_of_mem a hx)
    have htsum : t.sum ≤ t.length * 9 := by
      simpa using List.sum_le_card_nsmul t 9 ht
    simp only [List.length_cons, List.sum_cons] at hsum
    have ha9 : a = 9 := by omega
    have hts : 9 * t.length ≤ t.sum := by omega
    rw [List.length_cons, List.replicate_succ, ha9, ← ih ht hts]

/-- If the digit sum of `m` is at least `9 * D`, then `m ≥ 10^D - 1`. -/
theorem ge_repunit (D m : ℕ) (hm : m ≠ 0) (h : 9 * D ≤ (digits 10 m).sum) :
    10^D - 1 ≤ m := by
  have hdig_lt : ∀ d ∈ digits 10 m, d ≤ 9 := fun d hd => by
    have := Nat.digits_lt_base (by norm_num) hd; omega
  have hSle : (digits 10 m).sum ≤ (digits 10 m).length * 9 := by
    simpa using List.sum_le_card_nsmul (digits 10 m) 9 hdig_lt
  have hDlen : D ≤ (digits 10 m).length := by nlinarith [h, hSle]
  rcases lt_or_eq_of_le hDlen with hlt | heq
  · have hpow := base_pow_length_digits_le 10 m (by norm_num) hm
    have h1 : (10:ℕ)^(D+1) ≤ 10 * m :=
      le_trans (Nat.pow_le_pow_right (by norm_num) hlt) hpow
    rw [pow_succ] at h1
    have : (10:ℕ)^D ≤ m := by omega
    omega
  · -- D = length, all digits nine
    have hsum' : 9 * (digits 10 m).length ≤ (digits 10 m).sum := by rw [← heq]; exact h
    have hrep := all_nine (digits 10 m) hdig_lt hsum'
    have : m = ofDigits 10 (digits 10 m) := (ofDigits_digits 10 m).symm
    rw [hrep, ofDigits_replicate_nine, ← heq] at this
    omega

/- ## The function `a` -/

theorem a_le_of_witness (N : ℕ) (hN : N ≠ 0) (k : ℕ) (hk : k > 0)
    (hkr : N ∣ reverse_nat (k * N)) : a N ≤ k * N := by
  unfold a
  rw [if_neg hN]
  have hex : ∃ k, k > 0 ∧ N ∣ reverse_nat (k * N) := ⟨k, hk, hkr⟩
  rw [dif_pos hex]
  simp only
  apply Nat.mul_le_mul_right
  exact Nat.find_le ⟨hk, hkr⟩

theorem a_spec (N : ℕ) (hN : N ≠ 0)
    (hex : ∃ k, k > 0 ∧ N ∣ reverse_nat (k * N)) :
    0 < a N ∧ N ∣ a N ∧ N ∣ reverse_nat (a N) := by
  unfold a
  rw [if_neg hN, dif_pos hex]
  simp only
  have hfind := Nat.find_spec hex
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.mul_pos hfind.1 (Nat.pos_of_ne_zero hN)
  · exact Dvd.intro_left _ rfl
  · exact hfind.2

theorem digit_sum_pos (m : ℕ) (hm : 0 < m) : 0 < (digits 10 m).sum := by
  have hne : digits 10 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hlast : (digits 10 m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 10 (by omega)
  have hmem : (digits 10 m).getLast hne ∈ digits 10 m := List.getLast_mem hne
  have := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  omega

theorem a_le_value (N : ℕ) (hN : N ≠ 0) (w : ℕ) (hw : 0 < w)
    (hdvd : N ∣ w) (hrev : N ∣ reverse_nat w) : a N ≤ w := by
  have hkN : (w / N) * N = w := Nat.div_mul_cancel hdvd
  have hk : 0 < w / N := by
    rcases Nat.eq_zero_or_pos (w / N) with h | h
    · rw [h, zero_mul] at hkN; omega
    · exact h
  have := a_le_of_witness N hN (w / N) hk (by rw [hkN]; exact hrev)
  rwa [hkN] at this

/- ## Witness construction for n ≥ 5 -/

def ds5 : List ℕ := [2,9,7,9,9,9,9,9,7,9,2]

def rep (m : ℕ) : List ℕ := (List.replicate m ds5).flatten

def W (j : ℕ) : ℕ := ofDigits 10 (rep (3^j))

theorem rep_add (a b : ℕ) : rep (a + b) = rep a ++ rep b := by
  unfold rep
  rw [List.replicate_add, List.flatten_append]

theorem rep_length (m : ℕ) : (rep m).length = 11 * m := by
  unfold rep
  rw [List.length_flatten]
  simp [ds5, List.map_replicate, List.sum_replicate]
  ring

theorem rep_reverse (m : ℕ) : (rep m).reverse = rep m := by
  unfold rep
  rw [List.reverse_flatten, List.map_replicate, show ds5.reverse = ds5 from by decide,
    List.reverse_replicate]

theorem rep_mem_lt (m : ℕ) : ∀ x ∈ rep m, x < 10 := by
  intro x hx
  unfold rep at hx
  rw [List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rw [List.eq_of_mem_replicate hl] at hxl
  fin_cases hxl <;> decide

theorem rep_mem_ne_zero (m : ℕ) : ∀ x ∈ rep m, x ≠ 0 := by
  intro x hx
  unfold rep at hx
  rw [List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rw [List.eq_of_mem_replicate hl] at hxl
  fin_cases hxl <;> decide

theorem rep_getLast_ne_zero (m : ℕ) (h : rep m ≠ []) : (rep m).getLast h ≠ 0 :=
  rep_mem_ne_zero m _ (List.getLast_mem h)

/-- digits of W j is exactly the list rep (3^j). -/
theorem digits_W (j : ℕ) : digits 10 (W j) = rep (3^j) := by
  unfold W
  apply digits_ofDigits 10 (by norm_num) _ (rep_mem_lt _) (rep_getLast_ne_zero _)

theorem reverse_nat_W (j : ℕ) : reverse_nat (W j) = W j := by
  unfold reverse_nat
  rw [digits_W, rep_reverse]
  rfl

theorem W_pos (j : ℕ) : 0 < W j := by
  rcases Nat.eq_zero_or_pos (W j) with h | h
  · exfalso
    have h2 := digits_W j
    rw [h, Nat.digits_zero] at h2
    have hlen := rep_length (3^j)
    rw [show rep (3^j) = [] from h2.symm] at hlen
    simp only [List.length_nil] at hlen
    have : (0:ℕ) < 3^j := by positivity
    omega
  · exact h

/-- ofDigits over a triple concatenation factors. -/
theorem ofDigits_triple (A : List ℕ) :
    ofDigits 10 (A ++ A ++ A) =
      ofDigits 10 A * (1 + 10^A.length + 10^(2 * A.length)) := by
  rw [ofDigits_append, ofDigits_append, List.length_append]
  ring

theorem W_dvd (j : ℕ) : (3:ℕ)^(j+5) ∣ W j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have hrep : rep (3^(j+1)) = rep (3^j) ++ rep (3^j) ++ rep (3^j) := by
      rw [show (3:ℕ)^(j+1) = 3^j + 3^j + 3^j from by ring, rep_add, rep_add]
    have hW : W (j+1) = W j * (1 + 10^(rep (3^j)).length + 10^(2 * (rep (3^j)).length)) := by
      unfold W
      rw [hrep, ofDigits_triple]
    have h3 : (3:ℕ) ∣ (1 + 10^(rep (3^j)).length + 10^(2 * (rep (3^j)).length)) := by
      have e1 : (10:ℕ)^(rep (3^j)).length % 3 = 1 := by
        rw [Nat.pow_mod, show (10:ℕ)%3 = 1 from by decide, one_pow]; rfl
      have e2 : (10:ℕ)^(2 * (rep (3^j)).length) % 3 = 1 := by
        rw [Nat.pow_mod, show (10:ℕ)%3 = 1 from by decide, one_pow]; rfl
      omega
    rw [hW, show j+1+5 = (j+5)+1 from by ring, pow_succ]
    exact Nat.mul_dvd_mul ih h3

theorem W_lt (j : ℕ) : W j < 10^(11 * 3^j) := by
  have := ofDigits_lt_base_pow_length (b := 10) (l := rep (3^j)) (by norm_num) (rep_mem_lt _)
  rwa [rep_length] at this


end OEIS62567

open OEIS62567 in
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  have hN0 : (3:ℕ)^n ≠ 0 := by positivity
  have hRdvd : (3:ℕ)^n ∣ 10^(3^(n-2)) - 1 := by
    have := three_pow_dvd (n-2)
    rwa [Nat.sub_add_cancel hn] at this
  have hRrev : reverse_nat (10^(3^(n-2)) - 1) = 10^(3^(n-2)) - 1 := reverse_nat_repunit _
  have hDpos : 1 ≤ 3^(n-2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hRpos : 0 < 10^(3^(n-2)) - 1 := by
    have : (10:ℕ)^1 ≤ 10^(3^(n-2)) := Nat.pow_le_pow_right (by norm_num) hDpos
    simp only [pow_one] at this; omega
  have hex : ∃ k, k > 0 ∧ (3:ℕ)^n ∣ reverse_nat (k * 3^n) := by
    refine ⟨(10^(3^(n-2))-1) / 3^n, Nat.div_pos (Nat.le_of_dvd hRpos hRdvd) (by positivity), ?_⟩
    rw [Nat.div_mul_cancel hRdvd, hRrev]; exact hRdvd
  have haleR : a (3^n) ≤ 10^(3^(n-2)) - 1 :=
    a_le_value _ hN0 _ hRpos hRdvd (by rw [hRrev]; exact hRdvd)
  constructor
  · intro heq
    by_contra hcon
    push_neg at hcon
    have hn5 : 5 ≤ n := by omega
    have hWdvd : (3:ℕ)^n ∣ W (n-5) := by
      have := W_dvd (n-5); rwa [show n-5+5 = n from by omega] at this
    have hWrev : (3:ℕ)^n ∣ reverse_nat (W (n-5)) := by rw [reverse_nat_W]; exact hWdvd
    have e1 : 11 * 3^(n-5) < 3^(n-2) := by
      have h27 : (3:ℕ)^(n-2) = 27 * 3^(n-5) := by
        rw [show n-2 = (n-5)+3 from by omega, pow_add]; ring
      rw [h27]; nlinarith [pow_pos (show (0:ℕ)<3 from by norm_num) (n-5)]
    have e2 : (10:ℕ)^(11*3^(n-5)) ≤ 10^(3^(n-2)) - 1 := by
      have h3 : (10:ℕ)^(11*3^(n-5)) < 10^(3^(n-2)) := Nat.pow_lt_pow_right (by norm_num) e1
      omega
    have hWlt : W (n-5) < 10^(3^(n-2)) - 1 := lt_of_lt_of_le (W_lt (n-5)) e2
    have hle := a_le_value _ hN0 (W (n-5)) (W_pos (n-5)) hWdvd hWrev
    rw [heq] at hle
    omega
  · intro h
    have hN81 : (3:ℕ)^n ∣ 81 := by rcases h with h|h|h <;> (subst h; decide)
    obtain ⟨hpos, hdvd, hrev⟩ := a_spec (3^n) hN0 hex
    have hds := digitsum_dvd (3^n) hN81 (a (3^n)) hdvd hrev
    have hge : (3:ℕ)^n ≤ (digits 10 (a (3^n))).sum :=
      Nat.le_of_dvd (digit_sum_pos _ hpos) hds
    have h9D : (3:ℕ)^n = 9 * 3^(n-2) := by
      conv_lhs => rw [show n = (n-2)+2 from by omega]
      rw [pow_add]; ring
    have hRle : 10^(3^(n-2)) - 1 ≤ a (3^n) :=
      ge_repunit (3^(n-2)) (a (3^n)) (by omega) (by rw [← h9D]; exact hge)
    omega
