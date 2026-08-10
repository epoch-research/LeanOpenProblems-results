import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/-- The auxiliary integer sequence $F(n) = n! \sum_{k=2}^n \frac{(-1)^k}{k}$, corresponding to OEIS A024168. -/
def F_aux (n : ℕ) : ℤ :=
  if n < 2 then 0 else
  Finset.sum (Icc 2 n) $ fun k : ℕ =>
    let n_fact : ℤ := n.factorial
    let k_int : ℤ := k
    -- Term is $\frac{n!}{k} (-1)^{k}$.
    let quotient : ℤ := n_fact / k_int
    quotient * (if k % 2 = 0 then 1 else -1)

/--
A335023: Ratios of consecutive terms of A334958.
$$a(n) = \frac{A334958(n+1)}{A334958(n)}$$
where $A334958(m) = \gcd(F(m+1), F(m))$.
-/
def a (n : ℕ) : ℕ :=
  let A334958 (m : ℕ) : ℕ := Int.gcd (F_aux (m + 1)) (F_aux m)

  let g_n := A334958 n
  let g_n_plus_1 := A334958 (n + 1)

  -- A334958(n) is non-zero for $n \ge 1$.
  if g_n = 0 then 0 else g_n_plus_1 / g_n

def term (k : ℕ) : ℚ := ((if k % 2 = 0 then (1 : ℚ) else -1) / (k : ℚ))
def S (n : ℕ) : ℚ := ∑ k ∈ (Icc 2 n : Finset ℕ), term k
def B (n : ℕ) : ℚ := ∑ k ∈ (Icc 1 n : Finset ℕ), term k

def pint (p : ℕ) (q : ℚ) : Prop := ¬ p ∣ q.den

lemma pint_add {p : ℕ} (hp : Nat.Prime p) {q r : ℚ} (hq : pint p q) (hr : pint p r) : pint p (q+r) := by
  intro h
  have hdvd : (q+r).den ∣ q.den * r.den := Rat.add_den_dvd q r
  have hp_prod : p ∣ q.den * r.den := h.trans hdvd
  exact (hp.dvd_mul.mp hp_prod).elim hq hr

lemma pint_sum {p : ℕ} (hp : Nat.Prime p) {s : Finset ℕ} {f : ℕ → ℚ}
    (hf : ∀ k ∈ s, pint p (f k)) : pint p (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [sum_empty, pint, Rat.den_zero]
      exact hp.not_dvd_one
  | insert a s has ih =>
      rw [sum_insert has]
      apply pint_add hp
      · exact hf a (by simp)
      · apply ih
        intro k hk
        exact hf k (by simp [hk])

lemma term_den_dvd (k : ℕ) : (term k).den ∣ k := by
  unfold term
  by_cases hk : k = 0
  · simp [hk]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  by_cases h : k % 2 = 0
  · simp [h, div_eq_mul_inv, Rat.inv_natCast_den_of_pos hkpos]
  · have : ((-( (k : ℚ)⁻¹)).den) = k := by simp [Rat.inv_natCast_den_of_pos hkpos]
    simpa [h, div_eq_mul_inv] using dvd_of_eq this

lemma term_pint {p k : ℕ} (hpk : ¬ p ∣ k) : pint p (term k) := by
  intro h
  exact hpk (h.trans (term_den_dvd k))

lemma pint_div_of_num_dvd {p : ℕ} (hp0 : p ≠ 0) {q : ℚ}
    (hpden : pint p q) (hpnum : (p : ℤ) ∣ q.num) : pint p (q / (p : ℚ)) := by
  rcases hpnum with ⟨z, hz⟩
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
  have hzq : q / (p : ℚ) = Rat.divInt z (q.den : ℤ) := by
    conv_lhs => rw [← Rat.num_divInt_den q]
    rw [show ((p : ℚ)) = Rat.divInt (p : ℤ) 1 by exact Rat.intCast_eq_divInt (p : ℤ)]
    rw [Rat.divInt_div_divInt]
    rw [hz]
    rw [show (↑p * z * (1 : ℤ)) = ↑p * z by ring]
    rw [show ((↑q.den : ℤ) * ↑p) = ↑p * ↑q.den by ring]
    rw [Rat.divInt_mul_left hpz]
  have hz_dvd : z.natAbs ∣ q.num.natAbs := by
    rw [hz, Int.natAbs_mul]
    exact Nat.dvd_mul_left _ _
  have hcop : z.natAbs.Coprime q.den := Nat.Coprime.coprime_dvd_left hz_dvd q.reduced
  have hden_cast : (((z : ℚ) / (q.den : ℚ)).den : ℤ) = (q.den : ℤ) := by
    exact Rat.den_div_eq_of_coprime (by exact_mod_cast q.den_pos) hcop
  have hzq' : q / (p : ℚ) = (z : ℚ) / (q.den : ℚ) := by
    simpa [Rat.divInt_eq_div] using hzq
  intro h
  apply hpden
  rw [← hzq'] at hden_cast
  have hden_nat : (q / (p : ℚ)).den = q.den := by exact_mod_cast hden_cast
  simpa [hden_nat] using h

lemma zmod_den_ne {p : ℕ} {q : ℚ} (h : pint p q) : (q.den : ZMod p) ≠ 0 := by
  intro hz
  exact h ((ZMod.natCast_eq_zero_iff q.den p).mp hz)

lemma rat_cast_sum_pint {p : ℕ} [Fact p.Prime] (hp : Nat.Prime p) {s : Finset ℕ} {f : ℕ → ℚ}
    (hf : ∀ k ∈ s, pint p (f k)) :
    (((∑ k ∈ s, f k : ℚ) : ZMod p) = ∑ k ∈ s, (f k : ZMod p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [sum_insert has, sum_insert has]
      have hfa : pint p (f a) := hf a (by simp)
      have hfs : ∀ k ∈ s, pint p (f k) := by intro k hk; exact hf k (by simp [hk])
      have hsum : pint p (∑ k ∈ s, f k) := pint_sum hp hfs
      rw [Rat.cast_add_of_ne_zero (α := ZMod p) (zmod_den_ne hfa) (zmod_den_ne hsum)]
      rw [ih hfs]

local instance : Fact (Nat.Prime 1093) := ⟨by norm_num⟩

lemma term_cast_1093 (k : ℕ) (hk : k ∈ (Icc 1 1092 : Finset ℕ)) :
    (term k : ZMod 1093) = ((if k % 2 = 0 then (1 : ZMod 1093) else -1) * (k : ZMod 1093)⁻¹) := by
  have hkr : 1 ≤ k ∧ k ≤ 1092 := by simpa [Finset.mem_Icc] using hk
  have hkz : (k : ZMod 1093) ≠ 0 := by
    intro hz
    have hdvd : 1093 ∣ k := (ZMod.natCast_eq_zero_iff k 1093).mp hz
    have hp : 1093 ≤ k := Nat.le_of_dvd (by omega) hdvd
    omega
  unfold term
  by_cases h : k % 2 = 0
  · simp [h, div_eq_mul_inv]
  · simp [h, div_eq_mul_inv]

lemma B1092_pint : pint 1093 (B 1092) := by
  unfold B
  apply pint_sum (p := 1093) (by norm_num)
  intro k hk
  apply term_pint
  intro hdvd
  have hkr : 1 ≤ k ∧ k ≤ 1092 := by simpa [Finset.mem_Icc] using hk
  have hp : 1093 ≤ k := Nat.le_of_dvd (by omega) hdvd
  omega

lemma B1092_cast :
    (B 1092 : ZMod 1093) =
      ∑ k ∈ (Icc 1 1092 : Finset ℕ), ((if k % 2 = 0 then (1 : ZMod 1093) else -1) * (k : ZMod 1093)⁻¹) := by
  unfold B
  rw [rat_cast_sum_pint (p := 1093) (by norm_num)]
  apply Finset.sum_congr rfl
  intro k hk
  exact term_cast_1093 k hk
  intro k hk
  apply term_pint
  intro hdvd
  have hkr : 1 ≤ k ∧ k ≤ 1092 := by simpa [Finset.mem_Icc] using hk
  have hp : 1093 ≤ k := Nat.le_of_dvd (by omega) hdvd
  omega

set_option maxRecDepth 20000 in
lemma zmod_sum_1092 :
    (∑ k ∈ (Icc 1 1092 : Finset ℕ), ((if k % 2 = 0 then (1 : ZMod 1093) else -1) * (k : ZMod 1093)⁻¹)) = 0 := by
  decide

lemma B1092_num_dvd : (1093 : ℤ) ∣ (B 1092).num := by
  have hcast : (B 1092 : ZMod 1093) = 0 := by
    rw [B1092_cast, zmod_sum_1092]
  have hden : ((B 1092).den : ZMod 1093) ≠ 0 := zmod_den_ne B1092_pint
  rw [Rat.cast_def] at hcast
  field_simp [hden] at hcast
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (B 1092).num 1093).mp hcast

lemma den_dvd_add_of_dvd {N : ℕ} {q r : ℚ} (hq : q.den ∣ N.factorial) (hr : r.den ∣ N.factorial) : (q+r).den ∣ N.factorial := by
  exact (Rat.add_den_dvd_lcm q r).trans (Nat.lcm_dvd hq hr)

lemma den_dvd_sum {N : ℕ} {s : Finset ℕ} {f : ℕ → ℚ}
    (hf : ∀ k ∈ s, (f k).den ∣ N.factorial) : (∑ k ∈ s, f k).den ∣ N.factorial := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [sum_insert has]
      exact den_dvd_add_of_dvd (hf a (by simp)) (ih (by intro k hk; exact hf k (by simp [hk])))

lemma S_den_dvd_factorial (n : ℕ) : (S n).den ∣ n.factorial := by
  unfold S
  apply den_dvd_sum
  intro k hk
  have hkr : 2 ≤ k ∧ k ≤ n := by simpa [Finset.mem_Icc] using hk
  exact (term_den_dvd k).trans (Nat.dvd_factorial (by omega) hkr.2)

lemma F_aux_rat (n : ℕ) : (F_aux n : ℚ) = S n * (n.factorial : ℚ) := by
  by_cases hn : n < 2
  · have hI : (Icc 2 n : Finset ℕ) = ∅ := by
      ext k
      simp [Finset.mem_Icc]
      omega
    simp [F_aux, S, hn, hI]
  · have hn2 : 2 ≤ n := by omega
    rw [F_aux, if_neg hn, S]
    rw [Finset.sum_mul]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_neg]
    apply Finset.sum_congr rfl
    intro k hk
    have hkr : 2 ≤ k ∧ k ≤ n := by simpa [Finset.mem_Icc] using hk
    have hk_dvd : k ∣ n.factorial := Nat.dvd_factorial (by omega) hkr.2
    have hcastdiv : (((n.factorial : ℤ) / (k : ℤ) : ℤ) : ℚ) = (n.factorial : ℚ) / (k : ℚ) := by
      rw [← Int.natCast_ediv]
      exact Nat.cast_div (K := ℚ) hk_dvd (by exact_mod_cast (by omega : k ≠ 0))
    rw [hcastdiv]
    unfold term
    by_cases hpar : k % 2 = 0
    · simp [hpar, div_eq_mul_inv, mul_comm]
    · simp [hpar, div_eq_mul_inv, mul_comm]

lemma F_aux_eq_num_mul (n : ℕ) :
    F_aux n = (S n).num * ((n.factorial / (S n).den : ℕ) : ℤ) := by
  have hD : (S n).den ∣ n.factorial := S_den_dvd_factorial n
  have hfact_nat : n.factorial = (n.factorial / (S n).den) * (S n).den := by
    exact (Nat.div_mul_cancel hD).symm
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_mul, Int.cast_natCast]
  rw [F_aux_rat n]
  calc
    S n * (n.factorial : ℚ) = S n * (((n.factorial / (S n).den) * (S n).den : ℕ) : ℚ) := by rw [← hfact_nat]
    _ = (S n * (S n).den) * ((n.factorial / (S n).den : ℕ) : ℚ) := by rw [Nat.cast_mul]; ring
    _ = (S n).num * ((n.factorial / (S n).den : ℕ) : ℚ) := by rw [Rat.mul_den_eq_num]

lemma S_succ (n : ℕ) (hn : 1 ≤ n) : S (n+1) = S n + term (n+1) := by
  unfold S
  have hI : (Icc 2 (n+1) : Finset ℕ) = insert (n+1) (Icc 2 n) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [hI]
  have hnot : n+1 ∉ Icc 2 n := by simp [Finset.mem_Icc]
  rw [sum_insert hnot]
  ring

lemma F_aux_succ (n : ℕ) (hn : 1 ≤ n) :
    F_aux (n+1) = (n+1 : ℤ) * F_aux n + ((n.factorial : ℤ) * (if (n+1) % 2 = 0 then 1 else -1)) := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_ite, Int.cast_one, Int.cast_neg]
  rw [F_aux_rat (n+1), F_aux_rat n, S_succ n hn, Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  unfold term
  have hn1q : ((n+1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : n+1 ≠ 0)
  by_cases h : (n+1) % 2 = 0
  · field_simp [hn1q]
    simp [h]
    ring
  · field_simp [hn1q]
    simp [h]
    ring

lemma S_eq_B_add_one (n : ℕ) (hn : 1 ≤ n) : S n = B n + 1 := by
  rw [S, B]
  have hI : (Icc 1 n : Finset ℕ) = insert 1 (Icc 2 n) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [hI]
  have hnot : 1 ∉ Icc 2 n := by simp
  rw [sum_insert hnot]
  unfold term
  norm_num

lemma parity_mul_1093 (j : ℕ) : (1093 * j) % 2 = j % 2 := by
  omega

lemma term_mul_1093 (j : ℕ) (hj : j ∈ (Icc 1 1092 : Finset ℕ)) : term (1093*j) = term j / (1093 : ℚ) := by
  have hjrange : 1 ≤ j ∧ j ≤ 1092 := by simpa [Finset.mem_Icc] using hj
  have hjpos_nat : j ≠ 0 := by omega
  have hjpos : (j : ℚ) ≠ 0 := by exact_mod_cast hjpos_nat
  have hpar : (1093*j)%2 = j%2 := parity_mul_1093 j
  unfold term
  rw [hpar]
  by_cases h : j % 2 = 0
  · simp [h, div_eq_mul_inv, mul_comm, mul_left_comm]
  · simp [h, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma multiples_sum :
    (∑ k ∈ (Icc 1 1194648 : Finset ℕ) with 1093 ∣ k, term k) = B 1092 / (1093 : ℚ) := by
  rw [B, Finset.sum_div]
  symm
  refine Finset.sum_bij (fun j hj => 1093*j) ?hi ?hinj ?hsurj ?hterm
  · intro j hj
    have hjr : 1 ≤ j ∧ j ≤ 1092 := by simpa [Finset.mem_Icc] using hj
    simp only [mem_filter, mem_Icc]
    constructor
    · constructor <;> nlinarith
    · exact ⟨j, rfl⟩
  · intro a ha b hb h
    exact Nat.mul_left_cancel (by norm_num : 0 < 1093) h
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk
    rcases hk with ⟨hkI, hkdiv⟩
    rcases hkdiv with ⟨j, rfl⟩
    refine ⟨j, ?_, rfl⟩
    simp only [mem_Icc]
    constructor <;> nlinarith
  · intro j hj
    exact (term_mul_1093 j hj).symm

lemma nonmult_sum_pint : pint 1093 (∑ k ∈ (Icc 1 1194648 : Finset ℕ) with ¬1093 ∣ k, term k) := by
  apply pint_sum (p := 1093) (by norm_num)
  intro k hk
  simp only [mem_filter] at hk
  exact term_pint hk.2

lemma mult_sum_pint : pint 1093 (B 1092 / (1093 : ℚ)) := by
  exact pint_div_of_num_dvd (by norm_num) B1092_pint B1092_num_dvd

lemma B_big_pint : pint 1093 (B 1194648) := by
  rw [B]
  have hpart := Finset.sum_filter_add_sum_filter_not (Icc 1 1194648 : Finset ℕ) (fun k => 1093 ∣ k) term
  rw [← hpart]
  rw [multiples_sum]
  exact pint_add (by norm_num) mult_sum_pint nonmult_sum_pint

lemma gcd_P_mPD (P D m : ℤ) (hPD : P.gcd D = 1) : (m*P - D).gcd P = 1 := by
  have h : IsCoprime P D := Int.isCoprime_iff_gcd_eq_one.mpr hPD
  have hneg : IsCoprime P (-D) := h.neg_right
  have hx : IsCoprime P ((-D) + m * P) := hneg.add_mul_right_right m
  have hx' : IsCoprime ((-D) + m * P) P := hx.symm
  rw [Int.isCoprime_iff_gcd_eq_one] at hx'
  convert hx' using 2 <;> ring

lemma gcd_mD_mPD (P D m : ℤ) (hPD : P.gcd D = 1) (hmD : m.gcd D = 1) :
    (m*D).gcd (m*P - D) = 1 := by
  have hPDc : IsCoprime P D := Int.isCoprime_iff_gcd_eq_one.mpr hPD
  have hmDc : IsCoprime m D := Int.isCoprime_iff_gcd_eq_one.mpr hmD
  have hDm : IsCoprime D m := hmDc.symm
  have hDP : IsCoprime D P := hPDc.symm
  have hDmp : IsCoprime D (m*P) := hDm.mul_right hDP
  have hDx : IsCoprime D ((m*P) + (-1)*D) := hDmp.add_mul_right_right (-1)
  have hmx0 : IsCoprime m (-D) := hmDc.neg_right
  have hmx : IsCoprime m ((-D) + P*m) := hmx0.add_mul_right_right P
  have hmx' : IsCoprime m (m*P - D) := by
    convert hmx using 1 <;> ring
  have hDx' : IsCoprime D (m*P - D) := by
    convert hDx using 1 <;> ring
  have hall : IsCoprime (m*D) (m*P - D) := hmx'.mul_left hDx'
  rw [Int.isCoprime_iff_gcd_eq_one] at hall
  exact hall



lemma a_eq_one_of_coprime_den (n m : ℕ) (hn : 1 ≤ n) (hm : m = n + 1)
    (hodd : ¬ m % 2 = 0) (heven : (m + 1) % 2 = 0)
    (hcop : Nat.Coprime m (S n).den) : a n = 1 := by
  let P : ℤ := (S n).num
  let D : ℕ := (S n).den
  let Q : ℕ := n.factorial / D
  have hn_succ : n + 1 = m := hm.symm
  have hFN : F_aux n = P * (Q : ℤ) := by
    change F_aux n = (S n).num * ((n.factorial / (S n).den : ℕ) : ℤ)
    exact F_aux_eq_num_mul n
  have hfactN : (n.factorial : ℤ) = (Q : ℤ) * (D : ℤ) := by
    have hDdvd : D ∣ n.factorial := by simpa [D] using S_den_dvd_factorial n
    have hnat := (Nat.div_mul_cancel hDdvd).symm
    change (n.factorial : ℤ) = ((n.factorial / D : ℕ) : ℤ) * (D : ℤ)
    exact_mod_cast hnat
  have hFm : F_aux m = (Q : ℤ) * ((m : ℤ) * P - (D : ℤ)) := by
    rw [hm, F_aux_succ n hn, hFN, hfactN]
    have hoddn : ¬ (n + 1) % 2 = 0 := by simpa [hm] using hodd
    simp only [hoddn, ↓reduceIte, mul_neg, mul_one, Nat.cast_add, Nat.cast_one]
    ring
  have hFmp1_gcd : Int.gcd (F_aux (m+1)) (F_aux m) = Int.gcd ((m.factorial : ℤ)) (F_aux m) := by
    rw [F_aux_succ m (by omega)]
    simp only [heven, ↓reduceIte, mul_one]
    rw [add_comm ((↑m + 1) * F_aux m) (↑m.factorial : ℤ)]
    rw [Int.gcd_add_mul_right_left]
  have hPD : P.gcd (D : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    exact (S n).reduced.gcd_eq_one
  have hmD : (m : ℤ).gcd (D : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hcop.gcd_eq_one
  have hgN : Int.gcd (F_aux m) (F_aux n) = Q := by
    rw [hFm, hFN]
    rw [show P * (Q : ℤ) = (Q : ℤ) * P by ring]
    rw [Int.gcd_mul_left]
    rw [gcd_P_mPD P (D : ℤ) (m : ℤ) hPD]
    simp only [Int.natAbs_natCast, mul_one]
  have hgm : Int.gcd (F_aux (m+1)) (F_aux m) = Q := by
    rw [hFmp1_gcd, hFm]
    have hfactm : (m.factorial : ℤ) = (Q : ℤ) * ((m : ℤ) * (D : ℤ)) := by
      have hmfact : m.factorial = m * n.factorial := by
        rw [hm, Nat.factorial_succ]
      rw [hmfact]
      rw [Nat.cast_mul]
      rw [hfactN]
      ring
    rw [hfactm]
    rw [Int.gcd_mul_left]
    rw [gcd_mD_mPD P (D : ℤ) (m : ℤ) hPD hmD]
    simp only [Int.natAbs_natCast, mul_one]
  have hQpos : Q ≠ 0 := by
    have hDpos : 0 < D := by exact (S n).den_pos
    have hDdvd : D ∣ n.factorial := by simpa [D] using S_den_dvd_factorial n
    have hle : D ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) hDdvd
    have : 0 < Q := by
      change 0 < n.factorial / D
      exact Nat.div_pos hle hDpos
    omega
  unfold a
  dsimp only
  rw [hn_succ]
  change (if Int.gcd (F_aux m) (F_aux n) = 0 then 0 else Int.gcd (F_aux (m+1)) (F_aux m) / Int.gcd (F_aux m) (F_aux n)) = 1
  rw [hgN, hgm]
  rw [if_neg hQpos]
  exact Nat.div_self (Nat.pos_of_ne_zero hQpos)

lemma counter_coprime_den : Nat.Coprime 1194649 (S 1194648).den := by
  have hpD_B : ¬ 1093 ∣ (B 1194648).den := by simpa [pint] using B_big_pint
  have hSden : (S 1194648).den = (B 1194648).den := by
    have hs : S 1194648 = B 1194648 + 1 := by simpa using S_eq_B_add_one 1194648 (by norm_num)
    rw [hs]
    simpa using Rat.add_intCast_den (B 1194648) (1 : ℤ)
  have hpD : ¬ 1093 ∣ (S 1194648).den := by simpa [hSden] using hpD_B
  have hp : Nat.Prime 1093 := by norm_num
  have hc : Nat.Coprime 1093 (S 1194648).den := (hp.coprime_iff_not_dvd).mpr hpD
  have hc2 : Nat.Coprime (1093^2) (S 1194648).den := hc.pow_left 2
  simpa [show 1093 ^ 2 = 1194649 by norm_num] using hc2

lemma a_counterexample : a 1194648 = 1 := by
  apply a_eq_one_of_coprime_den 1194648 1194649
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact counter_coprime_den
theorem oeis_335023_conjecture_0.disproof :
    ¬ (∀ (n : ℕ), n > 0 → (a n = 1 ↔ Nat.Prime (n + 1))) := by
  intro h
  have hp : ¬ Nat.Prime (1194648 + 1) := by
    norm_num [Nat.Prime]
  exact hp ((h 1194648 (by norm_num)).mp a_counterexample)
