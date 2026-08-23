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
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)
    if h_ex : ∃ k, P k then
      have HP : DecidablePred P := by infer_instance
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

lemma a_eq_find {n : ℕ} (hn : n ≠ 0) (h_ex : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n)) :
    a n = Nat.find h_ex * n := by
  unfold a
  simp [hn]
  split
  · rename_i h
    congr 1
  · rename_i h
    exact (h h_ex).elim

lemma n_le_of_dvd_pos {n m : ℕ} (hm : 0 < m) (hdvd : n ∣ m) : n ≤ m :=
  Nat.le_of_dvd hm hdvd

lemma a_le_of {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hdvd : n ∣ m)
    (hrev : n ∣ reverse_nat m) : a n ≤ m := by
  have hn0 : n ≠ 0 := hn.ne'
  have hmn : n ≤ m := Nat.le_of_dvd hm hdvd
  have h_ex : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n) := by
    refine ⟨m / n, Nat.div_pos hmn hn, ?_⟩
    rwa [Nat.div_mul_cancel hdvd]
  rw [a_eq_find hn0 h_ex]
  have hle : Nat.find h_ex ≤ m / n :=
    Nat.find_min' h_ex ⟨Nat.div_pos hmn hn, by rwa [Nat.div_mul_cancel hdvd]⟩
  calc
    Nat.find h_ex * n ≤ (m / n) * n := Nat.mul_le_mul_right n hle
    _ = m := Nat.div_mul_cancel hdvd

lemma a_eq_of_min {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hdvd : n ∣ m)
    (hrev : n ∣ reverse_nat m)
    (hmin : ∀ m', m' < m → n ∣ m' → n ∣ reverse_nat m' → m' = 0) :
    a n = m := by
  have hn0 : n ≠ 0 := hn.ne'
  have hmn : n ≤ m := Nat.le_of_dvd hm hdvd
  have h_ex : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n) :=
    ⟨m / n, Nat.div_pos hmn hn, by rwa [Nat.div_mul_cancel hdvd]⟩
  rw [a_eq_find hn0 h_ex]
  have hf : Nat.find h_ex = m / n := by
    rw [Nat.find_eq_iff]
    refine ⟨⟨Nat.div_pos hmn hn, by rwa [Nat.div_mul_cancel hdvd]⟩, ?_⟩
    intro k hk hkP
    have : k * n < m := by
      rw [← Nat.div_mul_cancel hdvd]
      exact Nat.mul_lt_mul_of_pos_right hk hn
    have hk0 : k = 0 := by
      have hkn : k * n = 0 := hmin (k * n) this (dvd_mul_left n k) hkP.2
      exact (Nat.mul_eq_zero.mp hkn).resolve_right hn.ne'
    exact hkP.1.ne' hk0
  rw [hf, Nat.div_mul_cancel hdvd]

/- Reverse of small numbers -/

lemma reverse_nat_of_lt_ten {n : ℕ} (hn : n < 10) : reverse_nat n = n := by
  rcases n with (_ | n)
  · simp [reverse_nat, digits_zero]
  · have hpos : n + 1 ≠ 0 := succ_ne_zero n
    have hlt : n + 1 < 10 := hn
    rw [reverse_nat, digits_of_lt 10 (n + 1) hpos hlt]
    simp

lemma reverse_nat_ofDigits {L : List ℕ} (h1 : ∀ x ∈ L, x < 10)
    (h2 : ∀ h : L ≠ [], L.getLast h ≠ 0) :
    reverse_nat (ofDigits 10 L) = ofDigits 10 L.reverse := by
  simp only [reverse_nat]
  rw [digits_ofDigits 10 (by decide : 1 < 10) L h1 h2]

lemma ofDigits_replicate_nine (k : ℕ) :
    ofDigits 10 (List.replicate k 9) = 10 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, ofDigits_cons, ih]
    cases k with
    | zero => simp
    | succ k =>
      have hpos : 1 ≤ 10 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
      rw [Nat.mul_sub_one 10 (10 ^ (k + 1)), pow_succ]
      omega

lemma digits_all_nines (k : ℕ) :
    digits 10 (10 ^ k - 1) = List.replicate k 9 := by
  rw [← ofDigits_replicate_nine]
  refine digits_ofDigits 10 (by decide : 1 < 10) (List.replicate k 9)
    (by intro x hx; rw [List.mem_replicate] at hx; omega) ?_
  intro hne
  rw [List.getLast_replicate hne]
  decide


lemma reverse_nat_all_nines (k : ℕ) : reverse_nat (10 ^ k - 1) = 10 ^ k - 1 := by
  rw [reverse_nat, digits_all_nines, List.reverse_replicate, ofDigits_replicate_nine]

lemma a_nine : a 9 = 9 := by
  refine a_eq_of_min (by decide : 0 < 9) (by decide : 0 < 9) (dvd_refl 9) ?_ ?_
  · rw [reverse_nat_of_lt_ten (by decide)]
  · intro m' hm' hdvd hrev
    rcases eq_or_ne m' 0 with h | h
    · exact h
    · have : 9 ≤ m' := Nat.le_of_dvd (Nat.pos_of_ne_zero h) hdvd
      omega

lemma a_three_pow_two : a (3 ^ 2) = 10 ^ (3 ^ (2 - 2)) - 1 := by
  norm_num [a_nine]

/- Reverse of numbers with at most 3 digits. -/

lemma reverse_nat_one_digit {c : ℕ} (hc : c < 10) : reverse_nat c = c :=
  reverse_nat_of_lt_ten hc

lemma reverse_nat_two_digits {b c : ℕ} (hb : b < 10) (hc : c < 10) (hb0 : b ≠ 0) :
    reverse_nat (10 * b + c) = 10 * c + b := by
  have hL : ofDigits 10 [c, b] = 10 * b + c := by simp [ofDigits]; ring
  have hR : ofDigits 10 [b, c] = 10 * c + b := by simp [ofDigits]; ring
  have h := reverse_nat_ofDigits (L := [c, b])
    (by intro x hx; simp at hx; rcases hx with hx | hx <;> omega)
    (by intro hne; simpa)
  rw [hL] at h
  simpa [hR] using h

lemma reverse_nat_three_digits {a b c : ℕ}
    (ha : a < 10) (hb : b < 10) (hc : c < 10) (ha0 : a ≠ 0) :
    reverse_nat (100 * a + 10 * b + c) = 100 * c + 10 * b + a := by
  have hL : ofDigits 10 [c, b, a] = 100 * a + 10 * b + c := by simp [ofDigits]; ring
  have hR : ofDigits 10 [a, b, c] = 100 * c + 10 * b + a := by simp [ofDigits]; ring
  have h := reverse_nat_ofDigits (L := [c, b, a])
    (by intro x hx; simp at hx; rcases hx with hx | hx | hx <;> omega)
    (by intro hne; simpa)
  rw [hL] at h
  simpa [hR] using h

def padRev3 (n : ℕ) : ℕ := n % 10 * 100 + n / 10 % 10 * 10 + n / 100

lemma exists_pow10_mul_reverse_eq_padRev3 (n : ℕ) (hn : n < 1000) :
    ∃ e, padRev3 n = reverse_nat n * 10 ^ e := by
  set c := n % 10
  set b := n / 10 % 10
  set a := n / 100
  have hc : c < 10 := Nat.mod_lt _ (by decide)
  have hb : b < 10 := Nat.mod_lt _ (by decide)
  have ha : a < 10 := by omega
  have hn_eq : n = 100 * a + 10 * b + c := by
    have h1 : n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
    have h2 : n / 10 = n / 10 % 10 + 10 * (n / 100) := by
      have : n / 10 < 100 := by omega
      calc
        n / 10 = (n / 10) % 10 + 10 * ((n / 10) / 10) := (Nat.mod_add_div (n / 10) 10).symm
        _ = n / 10 % 10 + 10 * (n / 100) := by rw [Nat.div_div_eq_div_mul]
    omega
  have hpad : padRev3 n = 100 * c + 10 * b + a := by
    simp [padRev3, c, b, a]; ring
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · -- 1-digit (or 0)
      have : n = c := by omega
      refine ⟨2, ?_⟩
      rw [hpad, this, reverse_nat_one_digit hc, ha0, hb0]
      ring
    · -- 2-digit
      have : n = 10 * b + c := by omega
      refine ⟨1, ?_⟩
      rw [hpad, this, reverse_nat_two_digits hb hc hb0, ha0]
      ring
  · -- 3-digit
    refine ⟨0, ?_⟩
    rw [hpad, hn_eq, reverse_nat_three_digits ha hb hc ha0]
    ring

lemma coprime_27_ten : Nat.Coprime 27 10 := by decide

lemma twenty_seven_dvd_reverse_iff_padRev3 {n : ℕ} (hn : n < 1000) :
    27 ∣ reverse_nat n ↔ 27 ∣ padRev3 n := by
  obtain ⟨e, he⟩ := exists_pow10_mul_reverse_eq_padRev3 n hn
  constructor
  · intro h
    rw [he]
    exact dvd_mul_of_dvd_left h _
  · intro h
    rw [he] at h
    have hcop : Nat.Coprime 27 (10 ^ e) := coprime_27_ten.pow_right e
    exact hcop.dvd_of_dvd_mul_right h

lemma padRev3_not_dvd_27_of_mem :
    ∀ k, 1 ≤ k → k ≤ 36 → ¬ 27 ∣ padRev3 (27 * k) := by
  intro k h1 h2
  interval_cases k <;> decide

lemma a_twenty_seven : a 27 = 999 := by
  refine a_eq_of_min (by decide : 0 < 27) (by decide : 0 < 999) ?_ ?_ ?_
  · decide
  · have : 999 = 10 ^ 3 - 1 := by decide
    rw [this, reverse_nat_all_nines]
    decide
  · intro m' hm' hdvd hrev
    rcases eq_or_ne m' 0 with h | h
    · exact h
    · obtain ⟨k, rfl⟩ := hdvd
      have hkpos : 0 < k := by
        have : 27 ≠ 0 ∧ k ≠ 0 := Nat.mul_ne_zero_iff.mp h
        exact Nat.pos_of_ne_zero this.2
      have hk : k ≤ 36 := by
        have : 27 * k < 999 := hm'
        omega
      have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkpos
      have hlt : 27 * k < 1000 := by omega
      have : 27 ∣ padRev3 (27 * k) := (twenty_seven_dvd_reverse_iff_padRev3 hlt).1 hrev
      exact (padRev3_not_dvd_27_of_mem k hk1 hk this).elim

lemma a_three_pow_three : a (3 ^ 3) = 10 ^ (3 ^ (3 - 2)) - 1 := by
  norm_num [a_twenty_seven]



/- n = 4: uniqueness below 10^9. -/

lemma ten_pow_modeq81 (i : ℕ) : 10 ^ i ≡ 1 + 9 * i [MOD 81] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ]
    have h := Nat.ModEq.mul ih (Nat.ModEq.refl 10)
    have : (1 + 9 * i) * 10 ≡ 1 + 9 * (i + 1) [MOD 81] := by
      -- 10 + 90 i = 10 + 9 i + 81 i ≡ 1 + 9 (i+1)
      change (1 + 9 * i) * 10 % 81 = (1 + 9 * (i + 1)) % 81
      have : (1 + 9 * i) * 10 = 1 + 9 * (i + 1) + 81 * i := by ring
      rw [this, Nat.add_mul_mod_self_left]
    exact h.trans this

lemma list_sum_modeq {n : ℕ} {L M : List ℕ} (h : L.length = M.length)
    (hLM : ∀ i, (hli : i < L.length) → (hmi : i < M.length) →
      L[i] ≡ M[i] [MOD n]) :
    L.sum ≡ M.sum [MOD n] := by
  induction L generalizing M with
  | nil =>
    have : M = [] := by simpa using h.symm
    subst this
    rfl
  | cons a L ih =>
    match M with
    | [] => simp at h
    | b :: M =>
      simp only [List.length_cons, add_left_inj] at h
      rw [List.sum_cons, List.sum_cons]
      refine Nat.ModEq.add ?_ (ih h ?_)
      · simpa using hLM 0 (by simp) (by simp)
      · intro i hli hmi
        simpa using hLM (i + 1) (by simp [hli]) (by simp [hmi])

lemma mapIdx_sum_modeq81 (L : List ℕ) :
    (L.mapIdx fun i a => a * 10 ^ i).sum ≡
      (L.mapIdx fun i a => a * (1 + 9 * i)).sum [MOD 81] := by
  refine list_sum_modeq (by simp) ?_
  intro i h1 h2
  have hlen : i < L.length := by simpa using h1
  simp only [List.getElem_mapIdx]
  exact Nat.ModEq.mul (Nat.ModEq.refl _) (ten_pow_modeq81 i)

lemma ofDigits_modeq81 (L : List ℕ) :
    ofDigits 10 L ≡ (L.mapIdx fun i a => a * (1 + 9 * i)).sum [MOD 81] := by
  rw [ofDigits_eq_sum_mapIdx]
  exact mapIdx_sum_modeq81 L

lemma mapIdx_sum_add (L : List ℕ) (f g : ℕ → ℕ → ℕ) :
    (L.mapIdx fun i a => f i a + g i a).sum = (L.mapIdx f).sum + (L.mapIdx g).sum := by
  induction L generalizing f g with
  | nil => simp
  | cons d L ih =>
    rw [List.mapIdx_cons, List.mapIdx_cons, List.mapIdx_cons, List.sum_cons, List.sum_cons,
      List.sum_cons, ih]
    ring

lemma mapIdx_sum_const_mul (L : List ℕ) (c : ℕ) (f : ℕ → ℕ → ℕ) :
    (L.mapIdx fun i a => c * f i a).sum = c * (L.mapIdx f).sum := by
  induction L generalizing f with
  | nil => simp
  | cons d L ih =>
    rw [List.mapIdx_cons, List.mapIdx_cons, List.sum_cons, List.sum_cons, ih]
    ring

lemma mapIdx_sum_id (L : List ℕ) :
    (L.mapIdx fun _ a => a).sum = L.sum := by
  induction L with
  | nil => simp
  | cons d L ih =>
    rw [List.mapIdx_cons, List.sum_cons, List.sum_cons, ih]

lemma list_sum_map_add {α : Type*} (L : List α) (f g : α → ℕ) :
    (L.map fun x => f x + g x).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons d L ih =>
    simp [ih]
    ring

lemma list_sum_map_const_mul {α : Type*} (L : List α) (c : ℕ) (f : α → ℕ) :
    (L.map fun x => c * f x).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons d L ih =>
    simp [ih]
    ring

lemma mapIdx_sum_zipIdx (L : List ℕ) (f : ℕ → ℕ → ℕ) :
    (L.mapIdx f).sum = (L.zipIdx.map fun p => f p.2 p.1).sum := by
  simp [List.mapIdx_eq_zipIdx_map]

lemma zipIdx_fst_sum (L : List ℕ) : (L.zipIdx.map Prod.fst).sum = L.sum := by
  simp [List.zipIdx_map_fst]

lemma ofDigits_eq_sum_plus_nine_moment (L : List ℕ) :
    (L.mapIdx fun i a => a * (1 + 9 * i)).sum = L.sum + 9 * (L.mapIdx fun i a => a * i).sum := by
  rw [mapIdx_sum_zipIdx, mapIdx_sum_zipIdx]
  have : (L.zipIdx.map fun p => p.1 * (1 + 9 * p.2)) =
      L.zipIdx.map fun p => p.1 + 9 * (p.1 * p.2) := by
    refine congrArg (fun f => L.zipIdx.map f) ?_
    funext p
    ring
  rw [this, list_sum_map_add, zipIdx_fst_sum, list_sum_map_const_mul]

lemma mapIdx_sum_le (L : List ℕ) {f g : ℕ → ℕ → ℕ}
    (h : ∀ i a, i < L.length → f i a ≤ g i a) :
    (L.mapIdx f).sum ≤ (L.mapIdx g).sum := by
  induction L generalizing f g with
  | nil => simp
  | cons d L ih =>
    rw [List.mapIdx_cons, List.mapIdx_cons, List.sum_cons, List.sum_cons]
    refine Nat.add_le_add (h 0 d (by simp)) (ih ?_)
    intro i a hi
    exact h (i + 1) a (by simp [hi])

lemma moment_le (L : List ℕ) :
    (L.mapIdx fun i a => a * i).sum ≤ (L.length - 1) * L.sum := by
  have h := mapIdx_sum_le (f := fun i a => a * i) (g := fun _ a => (L.length - 1) * a) L ?_
  · rwa [mapIdx_sum_const_mul, mapIdx_sum_id] at h
  · intro i a hi
    have : a * i ≤ (L.length - 1) * a := by
      rw [mul_comm (L.length - 1) a]
      exact Nat.mul_le_mul_left a (Nat.le_sub_one_of_lt hi)
    exact this



lemma mapIdx_eq_of_pointwise (L : List ℕ) {f g : ℕ → ℕ → ℕ}
    (h : ∀ i a, i < L.length → f i a = g i a) :
    L.mapIdx f = L.mapIdx g := by
  induction L generalizing f g with
  | nil => rfl
  | cons d L ih =>
    rw [List.mapIdx_cons, List.mapIdx_cons, h 0 d (by simp), ih]
    intro i a hi
    exact h (i + 1) a (by simp [hi])

lemma reverse_moment_add (L : List ℕ) :
    (L.reverse.mapIdx fun i a => a * i).sum + (L.mapIdx fun i a => a * i).sum =
      (L.length - 1) * L.sum := by
  rw [List.mapIdx_reverse, List.sum_reverse]
  have hsum := (mapIdx_sum_add L (fun i a => a * (L.length - 1 - i)) (fun i a => a * i)).symm
  rw [hsum]
  have heq : (L.mapIdx fun i a => a * (L.length - 1 - i) + a * i) =
      L.mapIdx fun _ a => (L.length - 1) * a := by
    refine mapIdx_eq_of_pointwise L ?_
    intro i a hi
    have : i ≤ L.length - 1 := Nat.le_sub_one_of_lt hi
    rw [← Nat.mul_add, Nat.sub_add_cancel this, mul_comm]
  rw [heq, mapIdx_sum_const_mul, mapIdx_sum_id]

lemma ofDigits_reverse_modeq81 (L : List ℕ) :
    ofDigits 10 L.reverse ≡
      L.sum + 9 * ((L.length - 1) * L.sum - (L.mapIdx fun i a => a * i).sum) [MOD 81] := by
  have h := ofDigits_modeq81 L.reverse
  rw [ofDigits_eq_sum_plus_nine_moment] at h
  have hm := reverse_moment_add L
  have hle : (L.mapIdx fun i a => a * i).sum ≤ (L.length - 1) * L.sum := moment_le L
  have : (L.reverse.mapIdx fun i a => a * i).sum =
      (L.length - 1) * L.sum - (L.mapIdx fun i a => a * i).sum := by
    omega
  rw [this] at h
  simpa [List.sum_reverse] using h

lemma dvd_iff_modeq81 {x : ℕ} : 81 ∣ x ↔ x ≡ 0 [MOD 81] := by
  constructor
  · intro h
    change x % 81 = 0 % 81
    rw [Nat.zero_mod, Nat.dvd_iff_mod_eq_zero.mp h]
  · intro h
    exact Nat.dvd_iff_mod_eq_zero.mpr h

lemma sum_le_nine_mul_length {L : List ℕ} (h : ∀ x ∈ L, x < 10) :
    L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons d L ih =>
    simp only [List.sum_cons, List.length_cons, List.mem_cons, forall_eq_or_imp] at *
    have : d ≤ 9 := by omega
    have : L.sum ≤ 9 * L.length := ih h.2
    omega

lemma nine_mul_mod81 (a : ℕ) : 9 * a % 81 = 9 * (a % 9) := by
  conv_lhs => rw [← Nat.div_add_mod a 9, Nat.mul_add]
  have : 9 * (9 * (a / 9)) = 81 * (a / 9) := by ring
  rw [this, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have : a % 9 < 9 := Nat.mod_lt _ (by decide)
  omega

lemma nine_mul_modeq81 {a b : ℕ} (h : 9 * a ≡ 9 * b [MOD 81]) : a ≡ b [MOD 9] := by
  change 9 * a % 81 = 9 * b % 81 at h
  rw [nine_mul_mod81, nine_mul_mod81] at h
  have : a % 9 = b % 9 := by
    have ha : a % 9 < 9 := Nat.mod_lt _ (by decide)
    have hb : b % 9 < 9 := Nat.mod_lt _ (by decide)
    omega
  exact this

lemma two_mul_modeq9 {t : ℕ} (h : 2 * t ≡ 0 [MOD 9]) : t ≡ 0 [MOD 9] := by
  -- multiply by inverse of 2 mod 9, which is 5
  have : 5 * (2 * t) ≡ 5 * 0 [MOD 9] := Nat.ModEq.mul (Nat.ModEq.refl 5) h
  have h10 : 10 * t ≡ 0 [MOD 9] := by
    have h' : 5 * (2 * t) = 10 * t := by ring
    have h0 : 5 * 0 = 0 := by ring
    rwa [h', h0] at this
  have : t + 9 * t ≡ 0 [MOD 9] := by
    convert h10 using 1
    ring
  have : t ≡ 0 [MOD 9] := by
    have : t + 9 * t ≡ t [MOD 9] := by
      change (t + 9 * t) % 9 = t % 9
      simp [Nat.add_mul_mod_self_left]
    exact this.symm.trans ‹_›
  exact this

lemma ofDigits_eq_zero_of_forall {L : List ℕ} (h : ∀ x ∈ L, x = 0) :
    ofDigits 10 L = 0 := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp [ofDigits_cons, h d (by simp), ih (fun x hx => h x (by simp [hx]))]

lemma eq_replicate_nine_of_sum {L : List ℕ} {n : ℕ} (hdig : ∀ x ∈ L, x < 10)
    (hlen : L.length = n) (hsum : L.sum = 9 * n) : L = List.replicate n 9 := by
  refine List.eq_replicate_iff.2 ⟨hlen, ?_⟩
  induction L generalizing n with
  | nil => simp
  | cons d L ih =>
    have hd : d < 10 := hdig d (by simp)
    have hL : ∀ x ∈ L, x < 10 := fun x hx => hdig x (by simp [hx])
    have hlen' : L.length = n - 1 := by
      have : n = L.length + 1 := by simpa [List.length_cons] using hlen.symm
      omega
    have hsum' : d + L.sum = 9 * n := by simpa [List.sum_cons] using hsum
    have hsumL : L.sum ≤ 9 * L.length := sum_le_nine_mul_length hL
    have hn : n = L.length + 1 := by simpa [List.length_cons] using hlen.symm
    have hd9 : d = 9 := by omega
    intro x hx
    simp at hx
    rcases hx with rfl | hx
    · exact hd9
    · refine ih hL hlen' ?_ x hx
      omega

lemma unique_sol_mod81 {m : ℕ} (hm : m < 10 ^ 9) (h1 : 81 ∣ m) (h2 : 81 ∣ reverse_nat m) :
    m = 0 ∨ m = 999999999 := by
  set L := digits 10 m
  have hlen : L.length ≤ 9 := (digits_length_le_iff (by decide : 1 < 10) m).2 hm
  have hdig : ∀ x ∈ L, x < 10 := fun x hx => digits_lt_base (by decide : 1 < 10) hx
  have hSle : L.sum ≤ 81 := by
    have := sum_le_nine_mul_length hdig
    omega
  have hmL : m = ofDigits 10 L := (ofDigits_digits 10 m).symm
  have hrL : reverse_nat m = ofDigits 10 L.reverse := rfl
  have h1m : ofDigits 10 L ≡ 0 [MOD 81] := by
    rw [← hmL]; exact dvd_iff_modeq81.mp h1
  have h2m : ofDigits 10 L.reverse ≡ 0 [MOD 81] := by
    rw [← hrL]; exact dvd_iff_modeq81.mp h2
  have hST : L.sum + 9 * (L.mapIdx fun i a => a * i).sum ≡ 0 [MOD 81] := by
    have := (ofDigits_modeq81 L).symm.trans h1m
    rwa [ofDigits_eq_sum_plus_nine_moment] at this
  have hSU : L.sum + 9 * ((L.length - 1) * L.sum - (L.mapIdx fun i a => a * i).sum) ≡ 0 [MOD 81] :=
    (ofDigits_reverse_modeq81 L).symm.trans h2m
  set S := L.sum with hSdef
  set T := (L.mapIdx fun i a => a * i).sum with hTdef
  have hU : T ≤ (L.length - 1) * S := by simpa [S, T] using moment_le L
  -- S ≡ 0 [MOD 9]
  have hS9 : S ≡ 0 [MOD 9] := by
    have : S + 9 * T ≡ 0 [MOD 9] := (Nat.ModEq.of_dvd (by decide : 9 ∣ 81) hST)
    have : S + 9 * T ≡ S [MOD 9] := by
      change (S + 9 * T) % 9 = S % 9
      simp [Nat.add_mul_mod_self_left]
    exact this.symm.trans ‹_›
  -- 9T ≡ 9U [MOD 81] hence T ≡ U [MOD 9]
  have hTU : T ≡ (L.length - 1) * S - T [MOD 9] := by
    have : S + 9 * T ≡ S + 9 * ((L.length - 1) * S - T) [MOD 81] := hST.trans hSU.symm
    have : 9 * T ≡ 9 * ((L.length - 1) * S - T) [MOD 81] := Nat.ModEq.add_left_cancel' S this
    exact nine_mul_modeq81 this
  have h2T : 2 * T ≡ (L.length - 1) * S [MOD 9] := by
    have : T + T ≡ ((L.length - 1) * S - T) + T [MOD 9] := Nat.ModEq.add hTU (Nat.ModEq.refl T)
    convert this using 1
    · ring
    · exact (Nat.sub_add_cancel hU).symm
  have hT0 : T ≡ 0 [MOD 9] := by
    have : 2 * T ≡ 0 [MOD 9] := by
      have : (L.length - 1) * S ≡ 0 [MOD 9] := Nat.ModEq.mul (Nat.ModEq.refl _) hS9
      exact h2T.trans this
    exact two_mul_modeq9 this
  -- S + 9T ≡ 0 [MOD 81] and 9 | T ⇒ S ≡ 0 [MOD 81]
  have hS81 : S ≡ 0 [MOD 81] := by
    have hTdiv : 9 ∣ T := Nat.dvd_iff_mod_eq_zero.mpr hT0
    obtain ⟨k, hk⟩ := hTdiv
    have : S + 9 * T ≡ S [MOD 81] := by
      rw [hk]
      change (S + 9 * (9 * k)) % 81 = S % 81
      have : 9 * (9 * k) = 81 * k := by ring
      rw [this, Nat.add_mul_mod_self_left]
    exact this.symm.trans hST
  have hSeq : S = 0 ∨ S = 81 := by
    have : S % 81 = 0 := hS81
    have hdiv : S / 81 ≤ 1 := by omega
    interval_cases S / 81 <;> omega
  rcases hSeq with h0 | h81s
  · left
    have hall0 : ∀ x ∈ L, x = 0 := by
      intro x hx
      have : x ≤ L.sum := List.le_sum_of_mem hx
      omega
    rw [hmL, ofDigits_eq_zero_of_forall hall0]
  · right
    have hsum : L.sum = 81 := h81s
    have hlen9 : L.length = 9 := by
      have : L.sum ≤ 9 * L.length := sum_le_nine_mul_length hdig
      omega
    have hL9 : L = List.replicate 9 9 := eq_replicate_nine_of_sum hdig hlen9 (by omega)
    rw [hmL, hL9, ofDigits_replicate_nine]
    decide


lemma a_eighty_one : a 81 = 999999999 := by
  refine a_eq_of_min (by decide : 0 < 81) (by decide : 0 < 999999999) ?_ ?_ ?_
  · decide
  · have : 999999999 = 10 ^ 9 - 1 := by decide
    rw [this, reverse_nat_all_nines]
    decide
  · intro m' hm' hdvd hrev
    have hm'lt : m' < 10 ^ 9 := by omega
    have h := unique_sol_mod81 hm'lt hdvd hrev
    rcases h with h | h
    · exact h
    · omega

lemma a_three_pow_four : a (3 ^ 4) = 10 ^ (3 ^ (4 - 2)) - 1 := by
  norm_num [a_eighty_one]

/- n ≥ 5: concatenate the 10-digit solution for 243. -/

def block243 : ℕ := 4899999987

lemma block243_digits :
    digits 10 block243 = [7, 8, 9, 9, 9, 9, 9, 9, 8, 4] := by
  have h := digits_ofDigits 10 (by decide : 1 < 10) [7, 8, 9, 9, 9, 9, 9, 9, 8, 4]
    (by decide) (by decide)
  rw [show ofDigits 10 [7, 8, 9, 9, 9, 9, 9, 9, 8, 4] = 4899999987 from rfl] at h
  exact h

lemma block243_length : (digits 10 block243).length = 10 := by
  rw [block243_digits]
  decide

lemma block243_dvd : 243 ∣ block243 :=
  dvd_iff_mod_eq_zero.mpr rfl

lemma reverse_block243 : reverse_nat block243 = 7899999984 := by
  rw [reverse_nat, block243_digits]
  decide

lemma reverse_block243_dvd : 243 ∣ reverse_nat block243 := by
  rw [reverse_block243]
  exact dvd_iff_mod_eq_zero.mpr rfl

lemma padicVal_block243 : padicValNat 3 block243 = 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h5 : 3 ^ 5 ∣ block243 := by
    change 243 ∣ block243
    exact block243_dvd
  have h6 : ¬ 3 ^ 6 ∣ block243 := by
    rw [dvd_iff_mod_eq_zero]
    decide
  have hle : 5 ≤ padicValNat 3 block243 := (padicValNat_dvd_iff_le (by decide)).1 h5
  have hnle : ¬ 6 ≤ padicValNat 3 block243 := fun h =>
    h6 ((padicValNat_dvd_iff_le (by decide)).2 h)
  omega

lemma padicVal_reverse_block243 : padicValNat 3 (reverse_nat block243) = 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h5 : 3 ^ 5 ∣ reverse_nat block243 := by
    change 243 ∣ reverse_nat block243
    exact reverse_block243_dvd
  have h6 : ¬ 3 ^ 6 ∣ reverse_nat block243 := by
    rw [reverse_block243, dvd_iff_mod_eq_zero]
    decide
  have hne : reverse_nat block243 ≠ 0 := by rw [reverse_block243]; decide
  have hle : 5 ≤ padicValNat 3 (reverse_nat block243) :=
    (padicValNat_dvd_iff_le hne).1 h5
  have hnle : ¬ 6 ≤ padicValNat 3 (reverse_nat block243) := fun h =>
    h6 ((padicValNat_dvd_iff_le hne).2 h)
  omega

instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

lemma ten_pow_sub_one_padic (t : ℕ) (ht : t ≠ 0) :
    padicValNat 3 (10 ^ t - 1) = 2 + padicValNat 3 t := by
  have hodd : Odd (3 : ℕ) := by decide
  have hxy : 3 ∣ 10 - 1 := by decide
  have hx : ¬ 3 ∣ 10 := by decide
  have hlt : 1 < 10 := by decide
  have hmain := padicValNat.pow_sub_pow (p := 3) hodd hlt hxy hx ht
  have h9 : padicValNat 3 9 = 2 := by
    have : (9 : ℕ) = 3 ^ 2 := by decide
    rw [this, padicValNat.prime_pow]
  rw [h9, one_pow] at hmain
  exact hmain

/- Concatenation of a digit-block -/

def concatRep (b d r : ℕ) : ℕ :=
  b * ∑ i ∈ Finset.range r, (10 ^ d) ^ i

lemma geom_sum_ten_pow_mul (d r : ℕ) :
    (∑ i ∈ Finset.range r, (10 ^ d) ^ i) * (10 ^ d - 1) + 1 = (10 ^ d) ^ r := by
  have h1 : 1 ≤ 10 ^ d := Nat.one_le_pow d 10 (by decide)
  have heq : 10 ^ d - 1 + 1 = 10 ^ d := Nat.sub_add_cancel h1
  have h := geom_sum_mul_add (10 ^ d - 1) r
  rwa [heq] at h

lemma geom_sum_ten_pow_mul' (d r : ℕ) :
    (∑ i ∈ Finset.range r, (10 ^ d) ^ i) * (10 ^ d - 1) = (10 ^ d) ^ r - 1 := by
  have h := geom_sum_ten_pow_mul d r
  have hpos : 0 < 10 ^ d :=
    Nat.pos_iff_ne_zero.mpr (pow_ne_zero d (by decide : (10 : ℕ) ≠ 0))
  have h1 : 1 ≤ (10 ^ d) ^ r := Nat.one_le_pow r (10 ^ d) hpos
  omega

lemma geom_sum_ten_pow_pos {d r : ℕ} (hr : r ≠ 0) :
    0 < ∑ i ∈ Finset.range r, (10 ^ d) ^ i := by
  have hmem : 0 ∈ Finset.range r := Finset.mem_range.mpr (Nat.pos_of_ne_zero hr)
  have hterm : (10 ^ d) ^ 0 = 1 := by simp
  have : 1 ≤ ∑ i ∈ Finset.range r, (10 ^ d) ^ i := by
    rw [← hterm]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  omega

lemma ofDigits_flatten_replicate (L : List ℕ) (r : ℕ) :
    ofDigits 10 (List.replicate r L).flatten =
      ofDigits 10 L * ∑ i ∈ Finset.range r, (10 ^ L.length) ^ i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons, ofDigits_append, ih, Finset.sum_range_succ]
    set q := 10 ^ L.length
    set S := ∑ i ∈ Finset.range r, q ^ i
    set a := ofDigits 10 L
    have h1le : 1 ≤ q := Nat.one_le_pow L.length 10 (by decide)
    have hS : S * (q - 1) + 1 = q ^ r := by
      simpa [S, q] using geom_sum_ten_pow_mul L.length r
    have hgeom : 1 + q * S = S + q ^ r := by
      calc
        1 + q * S = 1 + S * q := by ring
        _ = 1 + S * (q - 1 + 1) := by rw [Nat.sub_add_cancel h1le]
        _ = 1 + (S * (q - 1) + S * 1) := by rw [Nat.mul_add]
        _ = (S * (q - 1) + 1) + S := by ring
        _ = q ^ r + S := by rw [hS]
        _ = S + q ^ r := by ring
    calc
      a + q * (a * S) = a * (1 + q * S) := by ring
      _ = a * (S + q ^ r) := by rw [hgeom]

lemma flatten_replicate_ne_nil {α : Type*} {n : ℕ} {l : List α}
    (hn : n ≠ 0) (hl : l ≠ []) :
    (List.replicate n l).flatten ≠ [] := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp [List.replicate_succ, List.flatten_cons, hl]

lemma getLast_flatten_replicate {α : Type*} {n : ℕ} (hn : n ≠ 0) (l : List α)
    (hl : l ≠ []) (hf : (List.replicate n l).flatten ≠ []) :
    (List.replicate n l).flatten.getLast hf = l.getLast hl := by
  have h1 := List.getLast?_flatten_replicate (n := n) hn l
  rw [List.getLast?_eq_getLast_of_ne_nil hf, List.getLast?_eq_getLast_of_ne_nil hl] at h1
  exact Option.some.inj h1

lemma digits_concatRep {b r : ℕ} (hr : r ≠ 0) (hb : b ≠ 0) :
    digits 10 (concatRep b (digits 10 b).length r) =
      (List.replicate r (digits 10 b)).flatten := by
  set L := digits 10 b
  have hLne : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr hb
  have heq : ofDigits 10 (List.replicate r L).flatten =
      concatRep b L.length r := by
    rw [ofDigits_flatten_replicate, ofDigits_digits]
    rfl
  rw [← heq]
  refine digits_ofDigits 10 (by decide : 1 < 10) _ ?_ ?_
  · intro x hx
    obtain ⟨l, hl, hx'⟩ := List.mem_flatten.mp hx
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hl
    exact digits_lt_base (by decide : 1 < 10) hx'
  · intro hne
    rw [getLast_flatten_replicate hr L hLne hne]
    exact getLast_digit_ne_zero 10 hb

lemma reverse_flatten_replicate {α : Type*} (r : ℕ) (L : List α) :
    (List.replicate r L).flatten.reverse = (List.replicate r L.reverse).flatten := by
  rw [List.reverse_flatten, List.map_replicate, List.reverse_replicate]

lemma reverse_concatRep {b r : ℕ} (hr : r ≠ 0) (hb : b ≠ 0) :
    reverse_nat (concatRep b (digits 10 b).length r) =
      concatRep (reverse_nat b) (digits 10 b).length r := by
  set L := digits 10 b
  have hdig := digits_concatRep (b := b) (r := r) hr hb
  rw [reverse_nat, hdig, reverse_flatten_replicate, ofDigits_flatten_replicate]
  simp only [List.length_reverse]
  rfl

lemma concatRep_le {b d r : ℕ} (hb : b ≤ 10 ^ d - 1) :
    concatRep b d r ≤ 10 ^ (d * r) - 1 := by
  unfold concatRep
  have hmul := geom_sum_ten_pow_mul' d r
  have : b * ∑ i ∈ Finset.range r, (10 ^ d) ^ i ≤
      (10 ^ d - 1) * ∑ i ∈ Finset.range r, (10 ^ d) ^ i :=
    Nat.mul_le_mul_right _ hb
  calc
    b * ∑ i ∈ Finset.range r, (10 ^ d) ^ i ≤
        (10 ^ d - 1) * ∑ i ∈ Finset.range r, (10 ^ d) ^ i := this
    _ = (∑ i ∈ Finset.range r, (10 ^ d) ^ i) * (10 ^ d - 1) := by ring
    _ = (10 ^ d) ^ r - 1 := hmul
    _ = 10 ^ (d * r) - 1 := by rw [← pow_mul]

lemma padicVal_geom_sum {d r : ℕ} (hd : d ≠ 0) (hr : r ≠ 0) :
    padicValNat 3 (∑ i ∈ Finset.range r, (10 ^ d) ^ i) = padicValNat 3 r := by
  have hsum_ne : ∑ i ∈ Finset.range r, (10 ^ d) ^ i ≠ 0 :=
    (geom_sum_ten_pow_pos hr).ne'
  have hpow : 1 < 10 ^ d := Nat.one_lt_pow hd (by decide)
  have hsub_ne : 10 ^ d - 1 ≠ 0 := (Nat.sub_pos_of_lt hpow).ne'
  have hmul := geom_sum_ten_pow_mul' d r
  have hprod := padicValNat.mul (p := 3) hsum_ne hsub_ne
  rw [hmul, ← pow_mul] at hprod
  have hdr : d * r ≠ 0 := mul_ne_zero hd hr
  have hpow_ne : 10 ^ (d * r) - 1 ≠ 0 := by
    have : 1 < 10 ^ (d * r) := Nat.one_lt_pow hdr (by decide)
    exact (Nat.sub_pos_of_lt this).ne'
  rw [ten_pow_sub_one_padic _ hdr, ten_pow_sub_one_padic _ hd] at hprod
  have hmuldr : padicValNat 3 (d * r) = padicValNat 3 d + padicValNat 3 r :=
    padicValNat.mul hd hr
  omega

lemma padicVal_concatRep {b d r : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) (hr : r ≠ 0) :
    padicValNat 3 (concatRep b d r) = padicValNat 3 b + padicValNat 3 r := by
  unfold concatRep
  have hsum_ne : ∑ i ∈ Finset.range r, (10 ^ d) ^ i ≠ 0 :=
    (geom_sum_ten_pow_pos hr).ne'
  rw [padicValNat.mul hb hsum_ne, padicVal_geom_sum hd hr]

lemma block243_le : block243 ≤ 10 ^ 10 - 1 := by decide

lemma reverse_block243_ne_zero : reverse_nat block243 ≠ 0 := by
  rw [reverse_block243]
  decide

lemma a_three_pow_ge_five {n : ℕ} (hn : 5 ≤ n) :
    a (3 ^ n) < 10 ^ (3 ^ (n - 2)) - 1 := by
  set r := 3 ^ (n - 5) with hrdef
  set d := (digits 10 block243).length
  have hd : d = 10 := block243_length
  have hr0 : r ≠ 0 := pow_ne_zero _ (by decide)
  have hb0 : block243 ≠ 0 := by decide
  set m := concatRep block243 d r
  have hmpos : 0 < m := by
    unfold m concatRep
    exact Nat.mul_pos (Nat.pos_of_ne_zero hb0) (geom_sum_ten_pow_pos hr0)
  have h3pos : 0 < 3 ^ n := pow_pos (by decide) _
  have hval : padicValNat 3 m = n := by
    have hmdef : m = concatRep block243 d r := rfl
    rw [hmdef, padicVal_concatRep hb0 (by rw [hd]; decide) hr0, padicVal_block243]
    have hrval : padicValNat 3 r = n - 5 := by
      rw [hrdef, padicValNat.prime_pow]
    omega
  have hdiv : 3 ^ n ∣ m :=
    (padicValNat_dvd_iff_le hmpos.ne').2 (by omega)
  have hrev_eq : reverse_nat m = concatRep (reverse_nat block243) d r :=
    reverse_concatRep (b := block243) (r := r) hr0 hb0
  have hvalr : padicValNat 3 (reverse_nat m) = n := by
    rw [hrev_eq, padicVal_concatRep reverse_block243_ne_zero (by rw [hd]; decide) hr0,
      padicVal_reverse_block243]
    have hrval : padicValNat 3 r = n - 5 := by
      rw [hrdef, padicValNat.prime_pow]
    omega
  have hrevdiv : 3 ^ n ∣ reverse_nat m :=
    (padicValNat_dvd_iff_le (by
      rw [hrev_eq]
      unfold concatRep
      exact mul_ne_zero reverse_block243_ne_zero (geom_sum_ten_pow_pos hr0).ne')).2 (by omega)
  have hle : a (3 ^ n) ≤ m := a_le_of h3pos hmpos hdiv hrevdiv
  have hmlt : m < 10 ^ (3 ^ (n - 2)) - 1 := by
    have hbound : m ≤ 10 ^ (d * r) - 1 := by
      have : block243 ≤ 10 ^ d - 1 := by
        rw [hd]
        exact block243_le
      exact concatRep_le this
    have hpowlt : d * r < 3 ^ (n - 2) := by
      rw [hd, hrdef]
      have hidx : n - 2 = n - 5 + 3 := by omega
      rw [hidx, pow_add]
      have h27 : 3 ^ 3 = 27 := by decide
      rw [h27, mul_comm (3 ^ (n - 5)) 27]
      exact Nat.mul_lt_mul_of_pos_right (by decide : 10 < 27)
        (Nat.pos_iff_ne_zero.mpr (pow_ne_zero (n - 5) (by decide : (3 : ℕ) ≠ 0)))
    have h1le : 1 ≤ 10 ^ (d * r) := Nat.one_le_pow (d * r) 10 (by decide)
    have : 10 ^ (d * r) - 1 < 10 ^ (3 ^ (n - 2)) - 1 :=
      Nat.sub_lt_sub_right h1le (Nat.pow_lt_pow_right (by decide : 1 < 10) hpowlt)
    omega
  omega

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  constructor
  · intro heq
    have hcases : n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n := by omega
    rcases hcases with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · have hlt := a_three_pow_ge_five h
      omega
  · intro h
    rcases h with h | h | h
    · subst h; exact a_three_pow_two
    · subst h; exact a_three_pow_three
    · subst h; exact a_three_pow_four

