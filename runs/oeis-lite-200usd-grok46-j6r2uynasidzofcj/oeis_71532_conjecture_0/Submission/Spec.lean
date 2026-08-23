import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

/-!
Cloitre's positivity conjecture for OEIS A071532 is false.
-/

/--
A071532: $a(n) = (-1) \cdot \sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$.
The sequence is defined over $\mathbb{Z}$, and empirically non-negative.
-/
noncomputable def a (n : ℕ) : ℤ :=
  -- Summing over k=1 to n is equivalent to summing over k'=0 to n-1, where term index is k'+1.
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      -- Since k ≥ 1, exponent_int is non-negative. We use Int.toNat for the exponent of Int^Nat power.
      (-1 : ℤ) ^ exponent_int.toNat

def u (n : ℕ) : ℕ := 3 ^ n / 2 ^ n

lemma three_div_two_pow (n : ℕ) :
    ((3 : ℝ) / 2) ^ n = (3 : ℝ) ^ n / (2 : ℝ) ^ n :=
  div_pow (3 : ℝ) (2 : ℝ) n

lemma u_eq_floor (n : ℕ) : (u n : ℤ) = ⌊((3 : ℝ) / 2) ^ n⌋ := by
  unfold u
  rw [three_div_two_pow]
  have h3 : (3 : ℝ) ^ n = ((3 ^ n : ℕ) : ℝ) := by norm_cast
  have h2 : (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by norm_cast
  rw [h3, h2, Int.floor_div_natCast, Int.floor_natCast]
  norm_cast

lemma toNat_floor_u {n : ℕ} (_hn : 1 ≤ n) :
    ⌊((3 : ℝ) / 2) ^ n⌋.toNat = u n := by
  rw [← u_eq_floor, Int.toNat_natCast]

lemma a_eq_sum_u (n : ℕ) :
    a n = - ∑ k ∈ Finset.range n, ((-1 : ℤ) ^ u (k + 1)) := by
  unfold a
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _hk
  change (-1 : ℤ) ^ ⌊((3 : ℝ) / 2) ^ (k + 1)⌋.toNat = (-1 : ℤ) ^ u (k + 1)
  rw [toNat_floor_u (n := k + 1) (Nat.succ_le_succ (Nat.zero_le _))]

lemma neg_one_pow_nat (m : ℕ) :
    (-1 : ℤ) ^ m = if Even m then (1 : ℤ) else -1 := by
  rcases Nat.even_or_odd m with h | h
  · rw [if_pos h, Even.neg_one_pow h]
  · rw [if_neg (Nat.not_even_iff_odd.mpr h), Odd.neg_one_pow h]

lemma a_eq_two_odds_sub_n (n : ℕ) :
    a n = 2 * ((Finset.range n).filter (fun k => Odd (u (k + 1)))).card - n := by
  rw [a_eq_sum_u]
  classical
  simp_rw [neg_one_pow_nat]
  have hs :
      (∑ k ∈ Finset.range n, (if Even (u (k + 1)) then (1 : ℤ) else -1)) =
        ((Finset.range n).filter (fun k => Even (u (k + 1)))).card -
        ((Finset.range n).filter (fun k => Odd (u (k + 1)))).card := by
    have := Finset.sum_ite (s := Finset.range n)
      (p := fun k => Even (u (k + 1)))
      (f := fun _ => (1 : ℤ)) (g := fun _ => (-1 : ℤ))
    rw [this]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
    have : ((Finset.range n).filter (fun k => ¬ Even (u (k + 1)))).card =
        ((Finset.range n).filter (fun k => Odd (u (k + 1)))).card := by
      simp [Nat.not_even_iff_odd]
    rw [this]
    ring
  rw [hs]
  have hOE :
      ((Finset.range n).filter (fun k => Even (u (k + 1)))).card +
      ((Finset.range n).filter (fun k => Odd (u (k + 1)))).card = n := by
    have := Finset.card_filter_add_card_filter_not
      (s := Finset.range n) (p := fun k => Even (u (k + 1)))
    simpa [Finset.card_range, Nat.not_even_iff_odd] using this
  set O := ((Finset.range n).filter (fun k => Odd (u (k + 1)))).card with hO
  set E := ((Finset.range n).filter (fun k => Even (u (k + 1)))).card with hE
  have hsum : (E : ℤ) + O = n := by exact_mod_cast hOE
  have hE' : (E : ℤ) = n - O := by linarith
  simp [hE']
  ring

lemma u_eq_shift (n : ℕ) : u n = (3 ^ n) >>> n := by
  unfold u
  rw [Nat.shiftRight_eq_div_pow]

/-- Running odd-count of `u (k+1), …, u (k+n)` starting from `p = 3^k`. -/
def go : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _p, _k, acc => acc
  | n + 1, p, k, acc =>
    let p' := p * 3
    let k' := k + 1
    go n p' k' (acc + (p' >>> k') % 2)

lemma go_succ (n p k acc : ℕ) :
    go (n + 1) p k acc =
      go n (p * 3) (k + 1) (acc + ((p * 3) >>> (k + 1)) % 2) :=
  rfl

lemma go_add (n m p k acc : ℕ) :
    go (n + m) p k acc = go m (p * 3 ^ n) (k + n) (go n p k acc) := by
  induction n generalizing p k acc with
  | zero => simp [go]
  | succ n ih =>
    have hnm : n + 1 + m = n + m + 1 := by omega
    rw [hnm, go_succ, ih, go_succ, pow_succ]
    ac_rfl

lemma bit_eq_ite_odd (t : ℕ) :
    ((3 ^ t) >>> t) % 2 = if Odd (u t) then 1 else 0 := by
  rw [← u_eq_shift]
  rcases Nat.even_or_odd (u t) with he | ho
  · rw [if_neg (Nat.not_odd_iff_even.mpr he)]
    exact Nat.even_iff.mp he
  · rw [if_pos ho]
    exact Nat.odd_iff.mp ho

lemma ico_succ_left {a b : ℕ} (h : a < b) :
    Finset.Ico a b = insert a (Finset.Ico (a + 1) b) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Ico]
  omega

lemma filter_ico_succ_left (n t : ℕ) :
    ((Finset.Ico (t + 1) (t + 1 + (n + 1))).filter (fun j => Odd (u j))).card =
      (if Odd (u (t + 1)) then 1 else 0) +
        ((Finset.Ico (t + 2) (t + 2 + n)).filter (fun j => Odd (u j))).card := by
  have hlt : t + 1 < t + 1 + (n + 1) := by omega
  have hset : Finset.Ico (t + 1) (t + 1 + (n + 1)) =
      insert (t + 1) (Finset.Ico (t + 2) (t + 2 + n)) := by
    have : t + 1 + (n + 1) = t + 2 + n := by omega
    rw [this]
    exact ico_succ_left (by omega : t + 1 < t + 2 + n)
  rw [hset, Finset.filter_insert]
  by_cases h : Odd (u (t + 1))
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem]
    · omega
    · simp
  · rw [if_neg h, if_neg h]
    omega

lemma go_general (n t acc : ℕ) :
    go n (3 ^ t) t acc =
      acc + ((Finset.Ico (t + 1) (t + 1 + n)).filter (fun j => Odd (u j))).card := by
  induction n generalizing t acc with
  | zero => simp [go]
  | succ n ih =>
    rw [go_succ]
    have hp : 3 ^ t * 3 = 3 ^ (t + 1) := by rw [pow_succ]
    rw [hp, bit_eq_ite_odd (t + 1), ih]
    have hfilter := filter_ico_succ_left n t
    have : t + 1 + 1 = t + 2 := by omega
    simp [this]
    omega

lemma ico_eq_range_shift (n : ℕ) :
    Finset.Ico 1 (1 + n) = (Finset.range n).image (fun i => i + 1) := by
  ext x
  simp [Finset.mem_Ico, Finset.mem_range]
  constructor
  · intro hx
    refine ⟨x - 1, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨i, hi, rfl⟩
    omega

lemma go_spec (n : ℕ) :
    go n 1 0 0 = ((Finset.range n).filter (fun i => Odd (u (i + 1)))).card := by
  have h := go_general n 0 0
  simp only [pow_zero] at h
  rw [h, zero_add]
  refine (Finset.card_nbij (s := (Finset.range n).filter (fun i => Odd (u (i + 1))))
      (t := (Finset.Ico 1 (1 + n)).filter (fun j => Odd (u j)))
      (fun i => i + 1) ?_ ?_ ?_).symm
  · intro i hi
    have hi' : i ∈ (Finset.range n).filter (fun i => Odd (u (i + 1))) := by
      simpa using hi
    have ⟨hiR, hiO⟩ := Finset.mem_filter.mp hi'
    have hiLt : i < n := Finset.mem_range.mp hiR
    have : i + 1 ∈ (Finset.Ico 1 (1 + n)).filter (fun j => Odd (u j)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hiO⟩
    simpa using this
  · intro i _hi j _hj hij
    exact Nat.add_right_cancel hij
  · intro b hb
    have hb' : b ∈ (Finset.Ico 1 (1 + n)).filter (fun j => Odd (u j)) := by
      simpa using hb
    have ⟨hbI0, hbO⟩ := Finset.mem_filter.mp hb'
    have hbI := Finset.mem_Ico.mp hbI0
    refine ⟨b - 1, ?_, Nat.sub_add_cancel hbI.1⟩
    have : b - 1 ∈ (Finset.range n).filter (fun i => Odd (u (i + 1))) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by
        simpa [Nat.sub_add_cancel hbI.1] using hbO⟩
    simpa using this

lemma a_eq_go (n : ℕ) : a n = 2 * (go n 1 0 0 : ℤ) - n := by
  rw [a_eq_two_odds_sub_n, go_spec]



def step8 (p k acc : ℕ) : ℕ × ℕ × ℕ :=
  let p1 := p * 3; let a1 := acc + (p1 >>> (k + 1)) % 2
  let p2 := p1 * 3; let a2 := a1 + (p2 >>> (k + 2)) % 2
  let p3 := p2 * 3; let a3 := a2 + (p3 >>> (k + 3)) % 2
  let p4 := p3 * 3; let a4 := a3 + (p4 >>> (k + 4)) % 2
  let p5 := p4 * 3; let a5 := a4 + (p5 >>> (k + 5)) % 2
  let p6 := p5 * 3; let a6 := a5 + (p6 >>> (k + 6)) % 2
  let p7 := p6 * 3; let a7 := a6 + (p7 >>> (k + 7)) % 2
  let p8 := p7 * 3; let a8 := a7 + (p8 >>> (k + 8)) % 2
  (p8, k + 8, a8)

def go8 : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _p, _k, acc => acc
  | n + 1, p, k, acc =>
    let s := step8 p k acc
    go8 n s.1 s.2.1 s.2.2

lemma go8_succ (n p k acc : ℕ) :
    go8 (n + 1) p k acc =
      go8 n (step8 p k acc).1 (step8 p k acc).2.1 (step8 p k acc).2.2 :=
  rfl

lemma step8_eq (p k acc : ℕ) :
    step8 p k acc = (p * 3 ^ 8, k + 8, go 8 p k acc) := by
  simp [step8, go]
  ring

lemma go8_eq (n p k acc : ℕ) :
    go8 n p k acc = go (8 * n) p k acc := by
  induction n generalizing p k acc with
  | zero => simp [go8, go]
  | succ n ih =>
    rw [go8_succ, step8_eq]
    simp only
    rw [ih]
    have hmul : 8 * (n + 1) = 8 + 8 * n := by ring
    rw [hmul, go_add]

lemma go8_250 (p k acc : ℕ) : go8 250 p k acc = go 2000 p k acc :=
  go8_eq 250 p k acc

set_option maxRecDepth 10000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 400000
set_option linter.unusedVariables false

lemma chunk_0 : go8 250 (3 ^ 0) 0 0 = 1048 := by decide
lemma chunk_1 : go8 250 (3 ^ 2000) 2000 1048 = 2042 := by decide
lemma chunk_2 : go8 250 (3 ^ 4000) 4000 2042 = 3043 := by decide
lemma chunk_3 : go8 250 (3 ^ 6000) 6000 3043 = 4059 := by decide
lemma chunk_4 : go8 250 (3 ^ 8000) 8000 4059 = 5070 := by decide
lemma chunk_5 : go8 250 (3 ^ 10000) 10000 5070 = 6111 := by decide
lemma chunk_6 : go8 250 (3 ^ 12000) 12000 6111 = 7096 := by decide
lemma chunk_7 : go8 250 (3 ^ 14000) 14000 7096 = 8106 := by decide
lemma chunk_8 : go8 250 (3 ^ 16000) 16000 8106 = 9070 := by decide
lemma chunk_9 : go8 250 (3 ^ 18000) 18000 9070 = 10111 := by decide
lemma chunk_10 : go8 250 (3 ^ 20000) 20000 10111 = 11068 := by decide
lemma chunk_11 : go8 250 (3 ^ 22000) 22000 11068 = 12099 := by decide
lemma chunk_12 : go8 250 (3 ^ 24000) 24000 12099 = 13140 := by decide
lemma chunk_13 : go8 250 (3 ^ 26000) 26000 13140 = 14126 := by decide
lemma chunk_14 : go8 250 (3 ^ 28000) 28000 14126 = 15126 := by decide
lemma chunk_15 : go8 250 (3 ^ 30000) 30000 15126 = 16125 := by decide
lemma chunk_16 : go8 250 (3 ^ 32000) 32000 16125 = 17138 := by decide
lemma chunk_17 : go8 250 (3 ^ 34000) 34000 17138 = 18139 := by decide
lemma chunk_18 : go8 250 (3 ^ 36000) 36000 18139 = 19114 := by decide
lemma chunk_19 : go8 250 (3 ^ 38000) 38000 19114 = 20150 := by decide
lemma chunk_20 : go8 250 (3 ^ 40000) 40000 20150 = 21169 := by decide
lemma chunk_21 : go8 250 (3 ^ 42000) 42000 21169 = 22130 := by decide
lemma chunk_22 : go8 250 (3 ^ 44000) 44000 22130 = 23133 := by decide
lemma chunk_23 : go8 250 (3 ^ 46000) 46000 23133 = 24120 := by decide
lemma chunk_24 : go8 250 (3 ^ 48000) 48000 24120 = 25088 := by decide
lemma chunk_25 : go8 250 (3 ^ 50000) 50000 25088 = 26091 := by decide
lemma chunk_26 : go8 250 (3 ^ 52000) 52000 26091 = 27095 := by decide
lemma chunk_27 : go8 250 (3 ^ 54000) 54000 27095 = 28115 := by decide
lemma chunk_28 : go8 250 (3 ^ 56000) 56000 28115 = 29122 := by decide
lemma chunk_29 : go8 250 (3 ^ 58000) 58000 29122 = 30119 := by decide
lemma chunk_30 : go8 250 (3 ^ 60000) 60000 30119 = 31144 := by decide
lemma chunk_31 : go8 250 (3 ^ 62000) 62000 31144 = 32121 := by decide
lemma chunk_32 : go8 250 (3 ^ 64000) 64000 32121 = 33163 := by decide
lemma chunk_33 : go8 250 (3 ^ 66000) 66000 33163 = 34165 := by decide
lemma chunk_34 : go8 250 (3 ^ 68000) 68000 34165 = 35128 := by decide
lemma chunk_35 : go8 250 (3 ^ 70000) 70000 35128 = 36151 := by decide
lemma chunk_36 : go8 250 (3 ^ 72000) 72000 36151 = 37174 := by decide
lemma chunk_37 : go8 250 (3 ^ 74000) 74000 37174 = 38232 := by decide
lemma chunk_38 : go8 250 (3 ^ 76000) 76000 38232 = 39240 := by decide
lemma chunk_39 : go8 250 (3 ^ 78000) 78000 39240 = 40236 := by decide
lemma chunk_40 : go8 250 (3 ^ 80000) 80000 40236 = 41223 := by decide
lemma chunk_41 : go8 250 (3 ^ 82000) 82000 41223 = 42241 := by decide
lemma chunk_42 : go8 250 (3 ^ 84000) 84000 42241 = 43235 := by decide
lemma chunk_43 : go8 250 (3 ^ 86000) 86000 43235 = 44270 := by decide
lemma chunk_44 : go8 250 (3 ^ 88000) 88000 44270 = 45275 := by decide
lemma chunk_45 : go8 250 (3 ^ 90000) 90000 45275 = 46312 := by decide
lemma chunk_46 : go8 250 (3 ^ 92000) 92000 46312 = 47307 := by decide
lemma chunk_47 : go8 250 (3 ^ 94000) 94000 47307 = 48281 := by decide
lemma chunk_48 : go8 250 (3 ^ 96000) 96000 48281 = 49286 := by decide
lemma chunk_49 : go8 250 (3 ^ 98000) 98000 49286 = 50263 := by decide
lemma chunk_50 : go8 250 (3 ^ 100000) 100000 50263 = 51270 := by decide
lemma chunk_51 : go8 250 (3 ^ 102000) 102000 51270 = 52289 := by decide
lemma chunk_52 : go8 250 (3 ^ 104000) 104000 52289 = 53285 := by decide
lemma chunk_53 : go8 250 (3 ^ 106000) 106000 53285 = 54289 := by decide
lemma chunk_54 : go8 250 (3 ^ 108000) 108000 54289 = 55250 := by decide
lemma chunk_55 : go8 250 (3 ^ 110000) 110000 55250 = 56238 := by decide
lemma chunk_56 : go8 250 (3 ^ 112000) 112000 56238 = 57274 := by decide
lemma chunk_57 : go8 250 (3 ^ 114000) 114000 57274 = 58250 := by decide
lemma chunk_58 : go8 250 (3 ^ 116000) 116000 58250 = 59240 := by decide
lemma chunk_59 : go8 250 (3 ^ 118000) 118000 59240 = 60216 := by decide
lemma chunk_60 : go8 250 (3 ^ 120000) 120000 60216 = 61212 := by decide
lemma chunk_61 : go8 250 (3 ^ 122000) 122000 61212 = 62198 := by decide
lemma chunk_62 : go8 250 (3 ^ 124000) 124000 62198 = 63182 := by decide
lemma chunk_63 : go8 250 (3 ^ 126000) 126000 63182 = 64170 := by decide
lemma chunk_64 : go8 250 (3 ^ 128000) 128000 64170 = 65183 := by decide
lemma chunk_65 : go8 250 (3 ^ 130000) 130000 65183 = 66192 := by decide
lemma chunk_66 : go8 250 (3 ^ 132000) 132000 66192 = 67206 := by decide
lemma chunk_67 : go8 250 (3 ^ 134000) 134000 67206 = 68195 := by decide
lemma chunk_68 : go8 250 (3 ^ 136000) 136000 68195 = 69235 := by decide
lemma chunk_69 : go8 250 (3 ^ 138000) 138000 69235 = 70271 := by decide
lemma chunk_70 : go8 250 (3 ^ 140000) 140000 70271 = 71273 := by decide
lemma chunk_71 : go8 250 (3 ^ 142000) 142000 71273 = 72288 := by decide
lemma chunk_72 : go8 250 (3 ^ 144000) 144000 72288 = 73281 := by decide
lemma chunk_73 : go8 250 (3 ^ 146000) 146000 73281 = 74279 := by decide
lemma chunk_74 : go8 250 (3 ^ 148000) 148000 74279 = 75254 := by decide
lemma chunk_75 : go8 250 (3 ^ 150000) 150000 75254 = 76233 := by decide
lemma chunk_76 : go8 250 (3 ^ 152000) 152000 76233 = 77264 := by decide
lemma chunk_77 : go8 250 (3 ^ 154000) 154000 77264 = 78279 := by decide
lemma chunk_78 : go8 250 (3 ^ 156000) 156000 78279 = 79271 := by decide
lemma chunk_79 : go8 250 (3 ^ 158000) 158000 79271 = 80295 := by decide
lemma chunk_80 : go8 250 (3 ^ 160000) 160000 80295 = 81297 := by decide
lemma chunk_81 : go8 250 (3 ^ 162000) 162000 81297 = 82298 := by decide
lemma chunk_82 : go8 250 (3 ^ 164000) 164000 82298 = 83329 := by decide
lemma chunk_83 : go8 250 (3 ^ 166000) 166000 83329 = 84328 := by decide
lemma chunk_84 : go8 250 (3 ^ 168000) 168000 84328 = 85321 := by decide
lemma chunk_85 : go8 250 (3 ^ 170000) 170000 85321 = 86319 := by decide
lemma chunk_86 : go8 250 (3 ^ 172000) 172000 86319 = 87342 := by decide
lemma chunk_87 : go8 250 (3 ^ 174000) 174000 87342 = 88327 := by decide
lemma chunk_88 : go8 250 (3 ^ 176000) 176000 88327 = 89308 := by decide
lemma chunk_89 : go8 250 (3 ^ 178000) 178000 89308 = 90310 := by decide
lemma chunk_90 : go8 250 (3 ^ 180000) 180000 90310 = 91305 := by decide
lemma chunk_91 : go8 250 (3 ^ 182000) 182000 91305 = 92270 := by decide
lemma chunk_92 : go8 250 (3 ^ 184000) 184000 92270 = 93269 := by decide
lemma chunk_93 : go8 250 (3 ^ 186000) 186000 93269 = 94258 := by decide
lemma chunk_94 : go8 250 (3 ^ 188000) 188000 94258 = 95251 := by decide
lemma chunk_95 : go8 250 (3 ^ 190000) 190000 95251 = 96231 := by decide
lemma chunk_96 : go8 250 (3 ^ 192000) 192000 96231 = 97241 := by decide
lemma chunk_97 : go8 250 (3 ^ 194000) 194000 97241 = 98228 := by decide
lemma chunk_98 : go8 250 (3 ^ 196000) 196000 98228 = 99244 := by decide
lemma chunk_99 : go8 250 (3 ^ 198000) 198000 99244 = 100277 := by decide
lemma chunk_100 : go8 250 (3 ^ 200000) 200000 100277 = 101273 := by decide
lemma chunk_101 : go8 250 (3 ^ 202000) 202000 101273 = 102272 := by decide
lemma chunk_102 : go8 250 (3 ^ 204000) 204000 102272 = 103247 := by decide
lemma chunk_103 : go8 250 (3 ^ 206000) 206000 103247 = 104245 := by decide
lemma chunk_104 : go8 250 (3 ^ 208000) 208000 104245 = 105197 := by decide
lemma chunk_105 : go8 250 (3 ^ 210000) 210000 105197 = 106196 := by decide
lemma chunk_106 : go8 250 (3 ^ 212000) 212000 106196 = 107190 := by decide
lemma chunk_107 : go8 250 (3 ^ 214000) 214000 107190 = 108181 := by decide
lemma chunk_108 : go8 250 (3 ^ 216000) 216000 108181 = 109176 := by decide
lemma chunk_109 : go8 250 (3 ^ 218000) 218000 109176 = 110215 := by decide
lemma chunk_110 : go8 250 (3 ^ 220000) 220000 110215 = 111234 := by decide
lemma chunk_111 : go8 250 (3 ^ 222000) 222000 111234 = 112252 := by decide
lemma chunk_112 : go8 250 (3 ^ 224000) 224000 112252 = 113270 := by decide
lemma chunk_113 : go8 250 (3 ^ 226000) 226000 113270 = 114276 := by decide
lemma chunk_114 : go8 250 (3 ^ 228000) 228000 114276 = 115279 := by decide
lemma chunk_115 : go8 250 (3 ^ 230000) 230000 115279 = 116293 := by decide
lemma chunk_116 : go8 250 (3 ^ 232000) 232000 116293 = 117289 := by decide
lemma chunk_117 : go8 250 (3 ^ 234000) 234000 117289 = 118261 := by decide
lemma chunk_118 : go8 250 (3 ^ 236000) 236000 118261 = 119271 := by decide
lemma chunk_119 : go8 250 (3 ^ 238000) 238000 119271 = 120283 := by decide
lemma chunk_120 : go8 250 (3 ^ 240000) 240000 120283 = 121296 := by decide
lemma chunk_121 : go8 250 (3 ^ 242000) 242000 121296 = 122269 := by decide
lemma chunk_122 : go8 250 (3 ^ 244000) 244000 122269 = 123269 := by decide
lemma chunk_123 : go8 250 (3 ^ 246000) 246000 123269 = 124280 := by decide
lemma chunk_124 : go8 250 (3 ^ 248000) 248000 124280 = 125225 := by decide
lemma chunk_125 : go8 250 (3 ^ 250000) 250000 125225 = 126229 := by decide
lemma chunk_126 : go8 250 (3 ^ 252000) 252000 126229 = 127207 := by decide
lemma chunk_127 : go8 250 (3 ^ 254000) 254000 127207 = 128177 := by decide
lemma chunk_128 : go8 250 (3 ^ 256000) 256000 128177 = 129149 := by decide
lemma chunk_129 : go8 250 (3 ^ 258000) 258000 129149 = 130149 := by decide
lemma chunk_130 : go8 250 (3 ^ 260000) 260000 130149 = 131132 := by decide
lemma chunk_131 : go8 250 (3 ^ 262000) 262000 131132 = 132103 := by decide
lemma chunk_132 : go8 250 (3 ^ 264000) 264000 132103 = 133128 := by decide
lemma chunk_133 : go8 250 (3 ^ 266000) 266000 133128 = 134122 := by decide
lemma chunk_134 : go8 250 (3 ^ 268000) 268000 134122 = 135034 := by decide
lemma chunk_135 : go8 250 (3 ^ 270000) 270000 135034 = 136039 := by decide
lemma chunk_136 : go8 250 (3 ^ 272000) 272000 136039 = 137077 := by decide
lemma chunk_137 : go8 250 (3 ^ 274000) 274000 137077 = 138132 := by decide
lemma chunk_138 : go8 250 (3 ^ 276000) 276000 138132 = 139131 := by decide
lemma chunk_139 : go8 250 (3 ^ 278000) 278000 139131 = 140128 := by decide
lemma chunk_140 : go8 250 (3 ^ 280000) 280000 140128 = 141130 := by decide
lemma chunk_141 : go8 250 (3 ^ 282000) 282000 141130 = 142103 := by decide
lemma chunk_142 : go8 250 (3 ^ 284000) 284000 142103 = 143105 := by decide
lemma chunk_143 : go8 250 (3 ^ 286000) 286000 143105 = 144109 := by decide
lemma chunk_144 : go8 250 (3 ^ 288000) 288000 144109 = 145097 := by decide
lemma chunk_145 : go8 250 (3 ^ 290000) 290000 145097 = 146079 := by decide
lemma chunk_146 : go8 250 (3 ^ 292000) 292000 146079 = 147056 := by decide
lemma chunk_147 : go8 250 (3 ^ 294000) 294000 147056 = 148056 := by decide
lemma chunk_148 : go8 250 (3 ^ 296000) 296000 148056 = 149025 := by decide
lemma chunk_149 : go8 250 (3 ^ 298000) 298000 149025 = 150059 := by decide
lemma chunk_150 : go8 250 (3 ^ 300000) 300000 150059 = 151054 := by decide
lemma chunk_151 : go8 250 (3 ^ 302000) 302000 151054 = 152103 := by decide
lemma chunk_152 : go8 250 (3 ^ 304000) 304000 152103 = 153096 := by decide
lemma chunk_153 : go8 250 (3 ^ 306000) 306000 153096 = 154110 := by decide
lemma chunk_154 : go8 250 (3 ^ 308000) 308000 154110 = 155098 := by decide
lemma chunk_155 : go8 250 (3 ^ 310000) 310000 155098 = 156060 := by decide
lemma chunk_156 : go8 250 (3 ^ 312000) 312000 156060 = 157077 := by decide
lemma chunk_157 : go8 250 (3 ^ 314000) 314000 157077 = 158111 := by decide
lemma chunk_158 : go8 250 (3 ^ 316000) 316000 158111 = 159072 := by decide
lemma chunk_159 : go8 250 (3 ^ 318000) 318000 159072 = 160089 := by decide
lemma chunk_160 : go8 250 (3 ^ 320000) 320000 160089 = 161046 := by decide
lemma chunk_161 : go8 250 (3 ^ 322000) 322000 161046 = 162028 := by decide
lemma chunk_162 : go8 250 (3 ^ 324000) 324000 162028 = 163034 := by decide
lemma chunk_163 : go8 250 (3 ^ 326000) 326000 163034 = 164089 := by decide
lemma chunk_164 : go8 250 (3 ^ 328000) 328000 164089 = 165058 := by decide

lemma chunk_rem : go 1523 (3 ^ 330000) 330000 165058 = 165761 := by decide

lemma acc_at_0 : go 0 1 0 0 = 0 := rfl

lemma acc_at_2000 : go 2000 1 0 0 = 1048 := by
  rw [← go8_250]
  simpa using chunk_0

lemma acc_at_4000 : go 4000 1 0 0 = 2042 := by
  have hsplit := go_add 2000 2000 1 0 0
  have hsum : 4000 = 2000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_2000]
  rw [← go8_250]
  exact chunk_1

lemma acc_at_6000 : go 6000 1 0 0 = 3043 := by
  have hsplit := go_add 4000 2000 1 0 0
  have hsum : 6000 = 4000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_4000]
  rw [← go8_250]
  exact chunk_2

lemma acc_at_8000 : go 8000 1 0 0 = 4059 := by
  have hsplit := go_add 6000 2000 1 0 0
  have hsum : 8000 = 6000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_6000]
  rw [← go8_250]
  exact chunk_3

lemma acc_at_10000 : go 10000 1 0 0 = 5070 := by
  have hsplit := go_add 8000 2000 1 0 0
  have hsum : 10000 = 8000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_8000]
  rw [← go8_250]
  exact chunk_4

lemma acc_at_12000 : go 12000 1 0 0 = 6111 := by
  have hsplit := go_add 10000 2000 1 0 0
  have hsum : 12000 = 10000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_10000]
  rw [← go8_250]
  exact chunk_5

lemma acc_at_14000 : go 14000 1 0 0 = 7096 := by
  have hsplit := go_add 12000 2000 1 0 0
  have hsum : 14000 = 12000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_12000]
  rw [← go8_250]
  exact chunk_6

lemma acc_at_16000 : go 16000 1 0 0 = 8106 := by
  have hsplit := go_add 14000 2000 1 0 0
  have hsum : 16000 = 14000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_14000]
  rw [← go8_250]
  exact chunk_7

lemma acc_at_18000 : go 18000 1 0 0 = 9070 := by
  have hsplit := go_add 16000 2000 1 0 0
  have hsum : 18000 = 16000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_16000]
  rw [← go8_250]
  exact chunk_8

lemma acc_at_20000 : go 20000 1 0 0 = 10111 := by
  have hsplit := go_add 18000 2000 1 0 0
  have hsum : 20000 = 18000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_18000]
  rw [← go8_250]
  exact chunk_9

lemma acc_at_22000 : go 22000 1 0 0 = 11068 := by
  have hsplit := go_add 20000 2000 1 0 0
  have hsum : 22000 = 20000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_20000]
  rw [← go8_250]
  exact chunk_10

lemma acc_at_24000 : go 24000 1 0 0 = 12099 := by
  have hsplit := go_add 22000 2000 1 0 0
  have hsum : 24000 = 22000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_22000]
  rw [← go8_250]
  exact chunk_11

lemma acc_at_26000 : go 26000 1 0 0 = 13140 := by
  have hsplit := go_add 24000 2000 1 0 0
  have hsum : 26000 = 24000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_24000]
  rw [← go8_250]
  exact chunk_12

lemma acc_at_28000 : go 28000 1 0 0 = 14126 := by
  have hsplit := go_add 26000 2000 1 0 0
  have hsum : 28000 = 26000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_26000]
  rw [← go8_250]
  exact chunk_13

lemma acc_at_30000 : go 30000 1 0 0 = 15126 := by
  have hsplit := go_add 28000 2000 1 0 0
  have hsum : 30000 = 28000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_28000]
  rw [← go8_250]
  exact chunk_14

lemma acc_at_32000 : go 32000 1 0 0 = 16125 := by
  have hsplit := go_add 30000 2000 1 0 0
  have hsum : 32000 = 30000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_30000]
  rw [← go8_250]
  exact chunk_15

lemma acc_at_34000 : go 34000 1 0 0 = 17138 := by
  have hsplit := go_add 32000 2000 1 0 0
  have hsum : 34000 = 32000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_32000]
  rw [← go8_250]
  exact chunk_16

lemma acc_at_36000 : go 36000 1 0 0 = 18139 := by
  have hsplit := go_add 34000 2000 1 0 0
  have hsum : 36000 = 34000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_34000]
  rw [← go8_250]
  exact chunk_17

lemma acc_at_38000 : go 38000 1 0 0 = 19114 := by
  have hsplit := go_add 36000 2000 1 0 0
  have hsum : 38000 = 36000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_36000]
  rw [← go8_250]
  exact chunk_18

lemma acc_at_40000 : go 40000 1 0 0 = 20150 := by
  have hsplit := go_add 38000 2000 1 0 0
  have hsum : 40000 = 38000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_38000]
  rw [← go8_250]
  exact chunk_19

lemma acc_at_42000 : go 42000 1 0 0 = 21169 := by
  have hsplit := go_add 40000 2000 1 0 0
  have hsum : 42000 = 40000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_40000]
  rw [← go8_250]
  exact chunk_20

lemma acc_at_44000 : go 44000 1 0 0 = 22130 := by
  have hsplit := go_add 42000 2000 1 0 0
  have hsum : 44000 = 42000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_42000]
  rw [← go8_250]
  exact chunk_21

lemma acc_at_46000 : go 46000 1 0 0 = 23133 := by
  have hsplit := go_add 44000 2000 1 0 0
  have hsum : 46000 = 44000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_44000]
  rw [← go8_250]
  exact chunk_22

lemma acc_at_48000 : go 48000 1 0 0 = 24120 := by
  have hsplit := go_add 46000 2000 1 0 0
  have hsum : 48000 = 46000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_46000]
  rw [← go8_250]
  exact chunk_23

lemma acc_at_50000 : go 50000 1 0 0 = 25088 := by
  have hsplit := go_add 48000 2000 1 0 0
  have hsum : 50000 = 48000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_48000]
  rw [← go8_250]
  exact chunk_24

lemma acc_at_52000 : go 52000 1 0 0 = 26091 := by
  have hsplit := go_add 50000 2000 1 0 0
  have hsum : 52000 = 50000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_50000]
  rw [← go8_250]
  exact chunk_25

lemma acc_at_54000 : go 54000 1 0 0 = 27095 := by
  have hsplit := go_add 52000 2000 1 0 0
  have hsum : 54000 = 52000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_52000]
  rw [← go8_250]
  exact chunk_26

lemma acc_at_56000 : go 56000 1 0 0 = 28115 := by
  have hsplit := go_add 54000 2000 1 0 0
  have hsum : 56000 = 54000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_54000]
  rw [← go8_250]
  exact chunk_27

lemma acc_at_58000 : go 58000 1 0 0 = 29122 := by
  have hsplit := go_add 56000 2000 1 0 0
  have hsum : 58000 = 56000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_56000]
  rw [← go8_250]
  exact chunk_28

lemma acc_at_60000 : go 60000 1 0 0 = 30119 := by
  have hsplit := go_add 58000 2000 1 0 0
  have hsum : 60000 = 58000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_58000]
  rw [← go8_250]
  exact chunk_29

lemma acc_at_62000 : go 62000 1 0 0 = 31144 := by
  have hsplit := go_add 60000 2000 1 0 0
  have hsum : 62000 = 60000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_60000]
  rw [← go8_250]
  exact chunk_30

lemma acc_at_64000 : go 64000 1 0 0 = 32121 := by
  have hsplit := go_add 62000 2000 1 0 0
  have hsum : 64000 = 62000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_62000]
  rw [← go8_250]
  exact chunk_31

lemma acc_at_66000 : go 66000 1 0 0 = 33163 := by
  have hsplit := go_add 64000 2000 1 0 0
  have hsum : 66000 = 64000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_64000]
  rw [← go8_250]
  exact chunk_32

lemma acc_at_68000 : go 68000 1 0 0 = 34165 := by
  have hsplit := go_add 66000 2000 1 0 0
  have hsum : 68000 = 66000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_66000]
  rw [← go8_250]
  exact chunk_33

lemma acc_at_70000 : go 70000 1 0 0 = 35128 := by
  have hsplit := go_add 68000 2000 1 0 0
  have hsum : 70000 = 68000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_68000]
  rw [← go8_250]
  exact chunk_34

lemma acc_at_72000 : go 72000 1 0 0 = 36151 := by
  have hsplit := go_add 70000 2000 1 0 0
  have hsum : 72000 = 70000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_70000]
  rw [← go8_250]
  exact chunk_35

lemma acc_at_74000 : go 74000 1 0 0 = 37174 := by
  have hsplit := go_add 72000 2000 1 0 0
  have hsum : 74000 = 72000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_72000]
  rw [← go8_250]
  exact chunk_36

lemma acc_at_76000 : go 76000 1 0 0 = 38232 := by
  have hsplit := go_add 74000 2000 1 0 0
  have hsum : 76000 = 74000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_74000]
  rw [← go8_250]
  exact chunk_37

lemma acc_at_78000 : go 78000 1 0 0 = 39240 := by
  have hsplit := go_add 76000 2000 1 0 0
  have hsum : 78000 = 76000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_76000]
  rw [← go8_250]
  exact chunk_38

lemma acc_at_80000 : go 80000 1 0 0 = 40236 := by
  have hsplit := go_add 78000 2000 1 0 0
  have hsum : 80000 = 78000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_78000]
  rw [← go8_250]
  exact chunk_39

lemma acc_at_82000 : go 82000 1 0 0 = 41223 := by
  have hsplit := go_add 80000 2000 1 0 0
  have hsum : 82000 = 80000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_80000]
  rw [← go8_250]
  exact chunk_40

lemma acc_at_84000 : go 84000 1 0 0 = 42241 := by
  have hsplit := go_add 82000 2000 1 0 0
  have hsum : 84000 = 82000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_82000]
  rw [← go8_250]
  exact chunk_41

lemma acc_at_86000 : go 86000 1 0 0 = 43235 := by
  have hsplit := go_add 84000 2000 1 0 0
  have hsum : 86000 = 84000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_84000]
  rw [← go8_250]
  exact chunk_42

lemma acc_at_88000 : go 88000 1 0 0 = 44270 := by
  have hsplit := go_add 86000 2000 1 0 0
  have hsum : 88000 = 86000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_86000]
  rw [← go8_250]
  exact chunk_43

lemma acc_at_90000 : go 90000 1 0 0 = 45275 := by
  have hsplit := go_add 88000 2000 1 0 0
  have hsum : 90000 = 88000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_88000]
  rw [← go8_250]
  exact chunk_44

lemma acc_at_92000 : go 92000 1 0 0 = 46312 := by
  have hsplit := go_add 90000 2000 1 0 0
  have hsum : 92000 = 90000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_90000]
  rw [← go8_250]
  exact chunk_45

lemma acc_at_94000 : go 94000 1 0 0 = 47307 := by
  have hsplit := go_add 92000 2000 1 0 0
  have hsum : 94000 = 92000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_92000]
  rw [← go8_250]
  exact chunk_46

lemma acc_at_96000 : go 96000 1 0 0 = 48281 := by
  have hsplit := go_add 94000 2000 1 0 0
  have hsum : 96000 = 94000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_94000]
  rw [← go8_250]
  exact chunk_47

lemma acc_at_98000 : go 98000 1 0 0 = 49286 := by
  have hsplit := go_add 96000 2000 1 0 0
  have hsum : 98000 = 96000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_96000]
  rw [← go8_250]
  exact chunk_48

lemma acc_at_100000 : go 100000 1 0 0 = 50263 := by
  have hsplit := go_add 98000 2000 1 0 0
  have hsum : 100000 = 98000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_98000]
  rw [← go8_250]
  exact chunk_49

lemma acc_at_102000 : go 102000 1 0 0 = 51270 := by
  have hsplit := go_add 100000 2000 1 0 0
  have hsum : 102000 = 100000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_100000]
  rw [← go8_250]
  exact chunk_50

lemma acc_at_104000 : go 104000 1 0 0 = 52289 := by
  have hsplit := go_add 102000 2000 1 0 0
  have hsum : 104000 = 102000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_102000]
  rw [← go8_250]
  exact chunk_51

lemma acc_at_106000 : go 106000 1 0 0 = 53285 := by
  have hsplit := go_add 104000 2000 1 0 0
  have hsum : 106000 = 104000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_104000]
  rw [← go8_250]
  exact chunk_52

lemma acc_at_108000 : go 108000 1 0 0 = 54289 := by
  have hsplit := go_add 106000 2000 1 0 0
  have hsum : 108000 = 106000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_106000]
  rw [← go8_250]
  exact chunk_53

lemma acc_at_110000 : go 110000 1 0 0 = 55250 := by
  have hsplit := go_add 108000 2000 1 0 0
  have hsum : 110000 = 108000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_108000]
  rw [← go8_250]
  exact chunk_54

lemma acc_at_112000 : go 112000 1 0 0 = 56238 := by
  have hsplit := go_add 110000 2000 1 0 0
  have hsum : 112000 = 110000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_110000]
  rw [← go8_250]
  exact chunk_55

lemma acc_at_114000 : go 114000 1 0 0 = 57274 := by
  have hsplit := go_add 112000 2000 1 0 0
  have hsum : 114000 = 112000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_112000]
  rw [← go8_250]
  exact chunk_56

lemma acc_at_116000 : go 116000 1 0 0 = 58250 := by
  have hsplit := go_add 114000 2000 1 0 0
  have hsum : 116000 = 114000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_114000]
  rw [← go8_250]
  exact chunk_57

lemma acc_at_118000 : go 118000 1 0 0 = 59240 := by
  have hsplit := go_add 116000 2000 1 0 0
  have hsum : 118000 = 116000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_116000]
  rw [← go8_250]
  exact chunk_58

lemma acc_at_120000 : go 120000 1 0 0 = 60216 := by
  have hsplit := go_add 118000 2000 1 0 0
  have hsum : 120000 = 118000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_118000]
  rw [← go8_250]
  exact chunk_59

lemma acc_at_122000 : go 122000 1 0 0 = 61212 := by
  have hsplit := go_add 120000 2000 1 0 0
  have hsum : 122000 = 120000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_120000]
  rw [← go8_250]
  exact chunk_60

lemma acc_at_124000 : go 124000 1 0 0 = 62198 := by
  have hsplit := go_add 122000 2000 1 0 0
  have hsum : 124000 = 122000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_122000]
  rw [← go8_250]
  exact chunk_61

lemma acc_at_126000 : go 126000 1 0 0 = 63182 := by
  have hsplit := go_add 124000 2000 1 0 0
  have hsum : 126000 = 124000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_124000]
  rw [← go8_250]
  exact chunk_62

lemma acc_at_128000 : go 128000 1 0 0 = 64170 := by
  have hsplit := go_add 126000 2000 1 0 0
  have hsum : 128000 = 126000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_126000]
  rw [← go8_250]
  exact chunk_63

lemma acc_at_130000 : go 130000 1 0 0 = 65183 := by
  have hsplit := go_add 128000 2000 1 0 0
  have hsum : 130000 = 128000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_128000]
  rw [← go8_250]
  exact chunk_64

lemma acc_at_132000 : go 132000 1 0 0 = 66192 := by
  have hsplit := go_add 130000 2000 1 0 0
  have hsum : 132000 = 130000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_130000]
  rw [← go8_250]
  exact chunk_65

lemma acc_at_134000 : go 134000 1 0 0 = 67206 := by
  have hsplit := go_add 132000 2000 1 0 0
  have hsum : 134000 = 132000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_132000]
  rw [← go8_250]
  exact chunk_66

lemma acc_at_136000 : go 136000 1 0 0 = 68195 := by
  have hsplit := go_add 134000 2000 1 0 0
  have hsum : 136000 = 134000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_134000]
  rw [← go8_250]
  exact chunk_67

lemma acc_at_138000 : go 138000 1 0 0 = 69235 := by
  have hsplit := go_add 136000 2000 1 0 0
  have hsum : 138000 = 136000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_136000]
  rw [← go8_250]
  exact chunk_68

lemma acc_at_140000 : go 140000 1 0 0 = 70271 := by
  have hsplit := go_add 138000 2000 1 0 0
  have hsum : 140000 = 138000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_138000]
  rw [← go8_250]
  exact chunk_69

lemma acc_at_142000 : go 142000 1 0 0 = 71273 := by
  have hsplit := go_add 140000 2000 1 0 0
  have hsum : 142000 = 140000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_140000]
  rw [← go8_250]
  exact chunk_70

lemma acc_at_144000 : go 144000 1 0 0 = 72288 := by
  have hsplit := go_add 142000 2000 1 0 0
  have hsum : 144000 = 142000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_142000]
  rw [← go8_250]
  exact chunk_71

lemma acc_at_146000 : go 146000 1 0 0 = 73281 := by
  have hsplit := go_add 144000 2000 1 0 0
  have hsum : 146000 = 144000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_144000]
  rw [← go8_250]
  exact chunk_72

lemma acc_at_148000 : go 148000 1 0 0 = 74279 := by
  have hsplit := go_add 146000 2000 1 0 0
  have hsum : 148000 = 146000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_146000]
  rw [← go8_250]
  exact chunk_73

lemma acc_at_150000 : go 150000 1 0 0 = 75254 := by
  have hsplit := go_add 148000 2000 1 0 0
  have hsum : 150000 = 148000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_148000]
  rw [← go8_250]
  exact chunk_74

lemma acc_at_152000 : go 152000 1 0 0 = 76233 := by
  have hsplit := go_add 150000 2000 1 0 0
  have hsum : 152000 = 150000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_150000]
  rw [← go8_250]
  exact chunk_75

lemma acc_at_154000 : go 154000 1 0 0 = 77264 := by
  have hsplit := go_add 152000 2000 1 0 0
  have hsum : 154000 = 152000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_152000]
  rw [← go8_250]
  exact chunk_76

lemma acc_at_156000 : go 156000 1 0 0 = 78279 := by
  have hsplit := go_add 154000 2000 1 0 0
  have hsum : 156000 = 154000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_154000]
  rw [← go8_250]
  exact chunk_77

lemma acc_at_158000 : go 158000 1 0 0 = 79271 := by
  have hsplit := go_add 156000 2000 1 0 0
  have hsum : 158000 = 156000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_156000]
  rw [← go8_250]
  exact chunk_78

lemma acc_at_160000 : go 160000 1 0 0 = 80295 := by
  have hsplit := go_add 158000 2000 1 0 0
  have hsum : 160000 = 158000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_158000]
  rw [← go8_250]
  exact chunk_79

lemma acc_at_162000 : go 162000 1 0 0 = 81297 := by
  have hsplit := go_add 160000 2000 1 0 0
  have hsum : 162000 = 160000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_160000]
  rw [← go8_250]
  exact chunk_80

lemma acc_at_164000 : go 164000 1 0 0 = 82298 := by
  have hsplit := go_add 162000 2000 1 0 0
  have hsum : 164000 = 162000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_162000]
  rw [← go8_250]
  exact chunk_81

lemma acc_at_166000 : go 166000 1 0 0 = 83329 := by
  have hsplit := go_add 164000 2000 1 0 0
  have hsum : 166000 = 164000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_164000]
  rw [← go8_250]
  exact chunk_82

lemma acc_at_168000 : go 168000 1 0 0 = 84328 := by
  have hsplit := go_add 166000 2000 1 0 0
  have hsum : 168000 = 166000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_166000]
  rw [← go8_250]
  exact chunk_83

lemma acc_at_170000 : go 170000 1 0 0 = 85321 := by
  have hsplit := go_add 168000 2000 1 0 0
  have hsum : 170000 = 168000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_168000]
  rw [← go8_250]
  exact chunk_84

lemma acc_at_172000 : go 172000 1 0 0 = 86319 := by
  have hsplit := go_add 170000 2000 1 0 0
  have hsum : 172000 = 170000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_170000]
  rw [← go8_250]
  exact chunk_85

lemma acc_at_174000 : go 174000 1 0 0 = 87342 := by
  have hsplit := go_add 172000 2000 1 0 0
  have hsum : 174000 = 172000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_172000]
  rw [← go8_250]
  exact chunk_86

lemma acc_at_176000 : go 176000 1 0 0 = 88327 := by
  have hsplit := go_add 174000 2000 1 0 0
  have hsum : 176000 = 174000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_174000]
  rw [← go8_250]
  exact chunk_87

lemma acc_at_178000 : go 178000 1 0 0 = 89308 := by
  have hsplit := go_add 176000 2000 1 0 0
  have hsum : 178000 = 176000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_176000]
  rw [← go8_250]
  exact chunk_88

lemma acc_at_180000 : go 180000 1 0 0 = 90310 := by
  have hsplit := go_add 178000 2000 1 0 0
  have hsum : 180000 = 178000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_178000]
  rw [← go8_250]
  exact chunk_89

lemma acc_at_182000 : go 182000 1 0 0 = 91305 := by
  have hsplit := go_add 180000 2000 1 0 0
  have hsum : 182000 = 180000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_180000]
  rw [← go8_250]
  exact chunk_90

lemma acc_at_184000 : go 184000 1 0 0 = 92270 := by
  have hsplit := go_add 182000 2000 1 0 0
  have hsum : 184000 = 182000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_182000]
  rw [← go8_250]
  exact chunk_91

lemma acc_at_186000 : go 186000 1 0 0 = 93269 := by
  have hsplit := go_add 184000 2000 1 0 0
  have hsum : 186000 = 184000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_184000]
  rw [← go8_250]
  exact chunk_92

lemma acc_at_188000 : go 188000 1 0 0 = 94258 := by
  have hsplit := go_add 186000 2000 1 0 0
  have hsum : 188000 = 186000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_186000]
  rw [← go8_250]
  exact chunk_93

lemma acc_at_190000 : go 190000 1 0 0 = 95251 := by
  have hsplit := go_add 188000 2000 1 0 0
  have hsum : 190000 = 188000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_188000]
  rw [← go8_250]
  exact chunk_94

lemma acc_at_192000 : go 192000 1 0 0 = 96231 := by
  have hsplit := go_add 190000 2000 1 0 0
  have hsum : 192000 = 190000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_190000]
  rw [← go8_250]
  exact chunk_95

lemma acc_at_194000 : go 194000 1 0 0 = 97241 := by
  have hsplit := go_add 192000 2000 1 0 0
  have hsum : 194000 = 192000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_192000]
  rw [← go8_250]
  exact chunk_96

lemma acc_at_196000 : go 196000 1 0 0 = 98228 := by
  have hsplit := go_add 194000 2000 1 0 0
  have hsum : 196000 = 194000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_194000]
  rw [← go8_250]
  exact chunk_97

lemma acc_at_198000 : go 198000 1 0 0 = 99244 := by
  have hsplit := go_add 196000 2000 1 0 0
  have hsum : 198000 = 196000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_196000]
  rw [← go8_250]
  exact chunk_98

lemma acc_at_200000 : go 200000 1 0 0 = 100277 := by
  have hsplit := go_add 198000 2000 1 0 0
  have hsum : 200000 = 198000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_198000]
  rw [← go8_250]
  exact chunk_99

lemma acc_at_202000 : go 202000 1 0 0 = 101273 := by
  have hsplit := go_add 200000 2000 1 0 0
  have hsum : 202000 = 200000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_200000]
  rw [← go8_250]
  exact chunk_100

lemma acc_at_204000 : go 204000 1 0 0 = 102272 := by
  have hsplit := go_add 202000 2000 1 0 0
  have hsum : 204000 = 202000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_202000]
  rw [← go8_250]
  exact chunk_101

lemma acc_at_206000 : go 206000 1 0 0 = 103247 := by
  have hsplit := go_add 204000 2000 1 0 0
  have hsum : 206000 = 204000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_204000]
  rw [← go8_250]
  exact chunk_102

lemma acc_at_208000 : go 208000 1 0 0 = 104245 := by
  have hsplit := go_add 206000 2000 1 0 0
  have hsum : 208000 = 206000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_206000]
  rw [← go8_250]
  exact chunk_103

lemma acc_at_210000 : go 210000 1 0 0 = 105197 := by
  have hsplit := go_add 208000 2000 1 0 0
  have hsum : 210000 = 208000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_208000]
  rw [← go8_250]
  exact chunk_104

lemma acc_at_212000 : go 212000 1 0 0 = 106196 := by
  have hsplit := go_add 210000 2000 1 0 0
  have hsum : 212000 = 210000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_210000]
  rw [← go8_250]
  exact chunk_105

lemma acc_at_214000 : go 214000 1 0 0 = 107190 := by
  have hsplit := go_add 212000 2000 1 0 0
  have hsum : 214000 = 212000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_212000]
  rw [← go8_250]
  exact chunk_106

lemma acc_at_216000 : go 216000 1 0 0 = 108181 := by
  have hsplit := go_add 214000 2000 1 0 0
  have hsum : 216000 = 214000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_214000]
  rw [← go8_250]
  exact chunk_107

lemma acc_at_218000 : go 218000 1 0 0 = 109176 := by
  have hsplit := go_add 216000 2000 1 0 0
  have hsum : 218000 = 216000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_216000]
  rw [← go8_250]
  exact chunk_108

lemma acc_at_220000 : go 220000 1 0 0 = 110215 := by
  have hsplit := go_add 218000 2000 1 0 0
  have hsum : 220000 = 218000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_218000]
  rw [← go8_250]
  exact chunk_109

lemma acc_at_222000 : go 222000 1 0 0 = 111234 := by
  have hsplit := go_add 220000 2000 1 0 0
  have hsum : 222000 = 220000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_220000]
  rw [← go8_250]
  exact chunk_110

lemma acc_at_224000 : go 224000 1 0 0 = 112252 := by
  have hsplit := go_add 222000 2000 1 0 0
  have hsum : 224000 = 222000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_222000]
  rw [← go8_250]
  exact chunk_111

lemma acc_at_226000 : go 226000 1 0 0 = 113270 := by
  have hsplit := go_add 224000 2000 1 0 0
  have hsum : 226000 = 224000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_224000]
  rw [← go8_250]
  exact chunk_112

lemma acc_at_228000 : go 228000 1 0 0 = 114276 := by
  have hsplit := go_add 226000 2000 1 0 0
  have hsum : 228000 = 226000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_226000]
  rw [← go8_250]
  exact chunk_113

lemma acc_at_230000 : go 230000 1 0 0 = 115279 := by
  have hsplit := go_add 228000 2000 1 0 0
  have hsum : 230000 = 228000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_228000]
  rw [← go8_250]
  exact chunk_114

lemma acc_at_232000 : go 232000 1 0 0 = 116293 := by
  have hsplit := go_add 230000 2000 1 0 0
  have hsum : 232000 = 230000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_230000]
  rw [← go8_250]
  exact chunk_115

lemma acc_at_234000 : go 234000 1 0 0 = 117289 := by
  have hsplit := go_add 232000 2000 1 0 0
  have hsum : 234000 = 232000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_232000]
  rw [← go8_250]
  exact chunk_116

lemma acc_at_236000 : go 236000 1 0 0 = 118261 := by
  have hsplit := go_add 234000 2000 1 0 0
  have hsum : 236000 = 234000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_234000]
  rw [← go8_250]
  exact chunk_117

lemma acc_at_238000 : go 238000 1 0 0 = 119271 := by
  have hsplit := go_add 236000 2000 1 0 0
  have hsum : 238000 = 236000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_236000]
  rw [← go8_250]
  exact chunk_118

lemma acc_at_240000 : go 240000 1 0 0 = 120283 := by
  have hsplit := go_add 238000 2000 1 0 0
  have hsum : 240000 = 238000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_238000]
  rw [← go8_250]
  exact chunk_119

lemma acc_at_242000 : go 242000 1 0 0 = 121296 := by
  have hsplit := go_add 240000 2000 1 0 0
  have hsum : 242000 = 240000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_240000]
  rw [← go8_250]
  exact chunk_120

lemma acc_at_244000 : go 244000 1 0 0 = 122269 := by
  have hsplit := go_add 242000 2000 1 0 0
  have hsum : 244000 = 242000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_242000]
  rw [← go8_250]
  exact chunk_121

lemma acc_at_246000 : go 246000 1 0 0 = 123269 := by
  have hsplit := go_add 244000 2000 1 0 0
  have hsum : 246000 = 244000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_244000]
  rw [← go8_250]
  exact chunk_122

lemma acc_at_248000 : go 248000 1 0 0 = 124280 := by
  have hsplit := go_add 246000 2000 1 0 0
  have hsum : 248000 = 246000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_246000]
  rw [← go8_250]
  exact chunk_123

lemma acc_at_250000 : go 250000 1 0 0 = 125225 := by
  have hsplit := go_add 248000 2000 1 0 0
  have hsum : 250000 = 248000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_248000]
  rw [← go8_250]
  exact chunk_124

lemma acc_at_252000 : go 252000 1 0 0 = 126229 := by
  have hsplit := go_add 250000 2000 1 0 0
  have hsum : 252000 = 250000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_250000]
  rw [← go8_250]
  exact chunk_125

lemma acc_at_254000 : go 254000 1 0 0 = 127207 := by
  have hsplit := go_add 252000 2000 1 0 0
  have hsum : 254000 = 252000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_252000]
  rw [← go8_250]
  exact chunk_126

lemma acc_at_256000 : go 256000 1 0 0 = 128177 := by
  have hsplit := go_add 254000 2000 1 0 0
  have hsum : 256000 = 254000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_254000]
  rw [← go8_250]
  exact chunk_127

lemma acc_at_258000 : go 258000 1 0 0 = 129149 := by
  have hsplit := go_add 256000 2000 1 0 0
  have hsum : 258000 = 256000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_256000]
  rw [← go8_250]
  exact chunk_128

lemma acc_at_260000 : go 260000 1 0 0 = 130149 := by
  have hsplit := go_add 258000 2000 1 0 0
  have hsum : 260000 = 258000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_258000]
  rw [← go8_250]
  exact chunk_129

lemma acc_at_262000 : go 262000 1 0 0 = 131132 := by
  have hsplit := go_add 260000 2000 1 0 0
  have hsum : 262000 = 260000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_260000]
  rw [← go8_250]
  exact chunk_130

lemma acc_at_264000 : go 264000 1 0 0 = 132103 := by
  have hsplit := go_add 262000 2000 1 0 0
  have hsum : 264000 = 262000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_262000]
  rw [← go8_250]
  exact chunk_131

lemma acc_at_266000 : go 266000 1 0 0 = 133128 := by
  have hsplit := go_add 264000 2000 1 0 0
  have hsum : 266000 = 264000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_264000]
  rw [← go8_250]
  exact chunk_132

lemma acc_at_268000 : go 268000 1 0 0 = 134122 := by
  have hsplit := go_add 266000 2000 1 0 0
  have hsum : 268000 = 266000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_266000]
  rw [← go8_250]
  exact chunk_133

lemma acc_at_270000 : go 270000 1 0 0 = 135034 := by
  have hsplit := go_add 268000 2000 1 0 0
  have hsum : 270000 = 268000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_268000]
  rw [← go8_250]
  exact chunk_134

lemma acc_at_272000 : go 272000 1 0 0 = 136039 := by
  have hsplit := go_add 270000 2000 1 0 0
  have hsum : 272000 = 270000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_270000]
  rw [← go8_250]
  exact chunk_135

lemma acc_at_274000 : go 274000 1 0 0 = 137077 := by
  have hsplit := go_add 272000 2000 1 0 0
  have hsum : 274000 = 272000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_272000]
  rw [← go8_250]
  exact chunk_136

lemma acc_at_276000 : go 276000 1 0 0 = 138132 := by
  have hsplit := go_add 274000 2000 1 0 0
  have hsum : 276000 = 274000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_274000]
  rw [← go8_250]
  exact chunk_137

lemma acc_at_278000 : go 278000 1 0 0 = 139131 := by
  have hsplit := go_add 276000 2000 1 0 0
  have hsum : 278000 = 276000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_276000]
  rw [← go8_250]
  exact chunk_138

lemma acc_at_280000 : go 280000 1 0 0 = 140128 := by
  have hsplit := go_add 278000 2000 1 0 0
  have hsum : 280000 = 278000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_278000]
  rw [← go8_250]
  exact chunk_139

lemma acc_at_282000 : go 282000 1 0 0 = 141130 := by
  have hsplit := go_add 280000 2000 1 0 0
  have hsum : 282000 = 280000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_280000]
  rw [← go8_250]
  exact chunk_140

lemma acc_at_284000 : go 284000 1 0 0 = 142103 := by
  have hsplit := go_add 282000 2000 1 0 0
  have hsum : 284000 = 282000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_282000]
  rw [← go8_250]
  exact chunk_141

lemma acc_at_286000 : go 286000 1 0 0 = 143105 := by
  have hsplit := go_add 284000 2000 1 0 0
  have hsum : 286000 = 284000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_284000]
  rw [← go8_250]
  exact chunk_142

lemma acc_at_288000 : go 288000 1 0 0 = 144109 := by
  have hsplit := go_add 286000 2000 1 0 0
  have hsum : 288000 = 286000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_286000]
  rw [← go8_250]
  exact chunk_143

lemma acc_at_290000 : go 290000 1 0 0 = 145097 := by
  have hsplit := go_add 288000 2000 1 0 0
  have hsum : 290000 = 288000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_288000]
  rw [← go8_250]
  exact chunk_144

lemma acc_at_292000 : go 292000 1 0 0 = 146079 := by
  have hsplit := go_add 290000 2000 1 0 0
  have hsum : 292000 = 290000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_290000]
  rw [← go8_250]
  exact chunk_145

lemma acc_at_294000 : go 294000 1 0 0 = 147056 := by
  have hsplit := go_add 292000 2000 1 0 0
  have hsum : 294000 = 292000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_292000]
  rw [← go8_250]
  exact chunk_146

lemma acc_at_296000 : go 296000 1 0 0 = 148056 := by
  have hsplit := go_add 294000 2000 1 0 0
  have hsum : 296000 = 294000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_294000]
  rw [← go8_250]
  exact chunk_147

lemma acc_at_298000 : go 298000 1 0 0 = 149025 := by
  have hsplit := go_add 296000 2000 1 0 0
  have hsum : 298000 = 296000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_296000]
  rw [← go8_250]
  exact chunk_148

lemma acc_at_300000 : go 300000 1 0 0 = 150059 := by
  have hsplit := go_add 298000 2000 1 0 0
  have hsum : 300000 = 298000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_298000]
  rw [← go8_250]
  exact chunk_149

lemma acc_at_302000 : go 302000 1 0 0 = 151054 := by
  have hsplit := go_add 300000 2000 1 0 0
  have hsum : 302000 = 300000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_300000]
  rw [← go8_250]
  exact chunk_150

lemma acc_at_304000 : go 304000 1 0 0 = 152103 := by
  have hsplit := go_add 302000 2000 1 0 0
  have hsum : 304000 = 302000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_302000]
  rw [← go8_250]
  exact chunk_151

lemma acc_at_306000 : go 306000 1 0 0 = 153096 := by
  have hsplit := go_add 304000 2000 1 0 0
  have hsum : 306000 = 304000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_304000]
  rw [← go8_250]
  exact chunk_152

lemma acc_at_308000 : go 308000 1 0 0 = 154110 := by
  have hsplit := go_add 306000 2000 1 0 0
  have hsum : 308000 = 306000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_306000]
  rw [← go8_250]
  exact chunk_153

lemma acc_at_310000 : go 310000 1 0 0 = 155098 := by
  have hsplit := go_add 308000 2000 1 0 0
  have hsum : 310000 = 308000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_308000]
  rw [← go8_250]
  exact chunk_154

lemma acc_at_312000 : go 312000 1 0 0 = 156060 := by
  have hsplit := go_add 310000 2000 1 0 0
  have hsum : 312000 = 310000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_310000]
  rw [← go8_250]
  exact chunk_155

lemma acc_at_314000 : go 314000 1 0 0 = 157077 := by
  have hsplit := go_add 312000 2000 1 0 0
  have hsum : 314000 = 312000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_312000]
  rw [← go8_250]
  exact chunk_156

lemma acc_at_316000 : go 316000 1 0 0 = 158111 := by
  have hsplit := go_add 314000 2000 1 0 0
  have hsum : 316000 = 314000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_314000]
  rw [← go8_250]
  exact chunk_157

lemma acc_at_318000 : go 318000 1 0 0 = 159072 := by
  have hsplit := go_add 316000 2000 1 0 0
  have hsum : 318000 = 316000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_316000]
  rw [← go8_250]
  exact chunk_158

lemma acc_at_320000 : go 320000 1 0 0 = 160089 := by
  have hsplit := go_add 318000 2000 1 0 0
  have hsum : 320000 = 318000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_318000]
  rw [← go8_250]
  exact chunk_159

lemma acc_at_322000 : go 322000 1 0 0 = 161046 := by
  have hsplit := go_add 320000 2000 1 0 0
  have hsum : 322000 = 320000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_320000]
  rw [← go8_250]
  exact chunk_160

lemma acc_at_324000 : go 324000 1 0 0 = 162028 := by
  have hsplit := go_add 322000 2000 1 0 0
  have hsum : 324000 = 322000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_322000]
  rw [← go8_250]
  exact chunk_161

lemma acc_at_326000 : go 326000 1 0 0 = 163034 := by
  have hsplit := go_add 324000 2000 1 0 0
  have hsum : 326000 = 324000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_324000]
  rw [← go8_250]
  exact chunk_162

lemma acc_at_328000 : go 328000 1 0 0 = 164089 := by
  have hsplit := go_add 326000 2000 1 0 0
  have hsum : 328000 = 326000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_326000]
  rw [← go8_250]
  exact chunk_163

lemma acc_at_330000 : go 330000 1 0 0 = 165058 := by
  have hsplit := go_add 328000 2000 1 0 0
  have hsum : 330000 = 328000 + 2000 := rfl
  rw [hsum, hsplit, acc_at_328000]
  rw [← go8_250]
  exact chunk_164

lemma acc_at_331523 : go 331523 1 0 0 = 165761 := by
  have hsplit := go_add 330000 1523 1 0 0
  have hsum : 331523 = 330000 + 1523 := rfl
  rw [hsum, hsplit, acc_at_330000]
  exact chunk_rem

lemma a_neg : a 331523 = -1 := by
  rw [a_eq_go, acc_at_331523]
  norm_num

theorem oeis_71532_conjecture_0 :
    ∃ n : ℕ, a n = -1 :=
  ⟨331523, a_neg⟩
