import FormalConjectures.Util.ProblemImports

open BigOperators Int Real Finset

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

/-!
## Resolution: the conjecture is FALSE.

`a n` is a `±1` walk with `a 0 = 0`.  Although the sequence is non-negative for
all small `n`, it eventually becomes negative: the first counterexample is
`n = 331523`, where `a 331523 = -1 < 0`.  We verify this by an exact, kernel
checked evaluation of the defining sum, split into blocks of length `1000`.

The key identity is `⌊(3/2)^m⌋ = 3^m / 2^m` (integer division), which turns each
summand `(-1)^{⌊(3/2)^m⌋}` into `1 - 2 · (3^m / 2^m mod 2)`, a decidable function
of `m`; `Nat.pow`/`Nat.div` are evaluated efficiently by the kernel.
-/

/-- The computable form of each summand. -/
def g (k : ℕ) : ℤ := 1 - 2 * ((3 ^ (k+1) / 2 ^ (k+1) % 2 : ℕ) : ℤ)

lemma floor_thp (m : ℕ) : (⌊((3 : ℝ) / 2) ^ m⌋ : ℤ) = (3 ^ m : ℤ) / (2 ^ m : ℤ) := by
  have h1 : ((3 : ℝ) / 2) ^ m = (3 : ℝ) ^ m / ((2 ^ m : ℕ) : ℝ) := by push_cast; rw [div_pow]
  rw [h1, Int.floor_div_natCast]
  have h2 : ((3 : ℝ) ^ m) = (((3 ^ m : ℕ)) : ℝ) := by push_cast; ring
  rw [h2, Int.floor_natCast]; push_cast; ring

lemma neg_one_pow_nat (M : ℕ) : (-1 : ℤ) ^ M = 1 - 2 * ((M % 2 : ℕ) : ℤ) := by
  rcases Nat.even_or_odd M with he | ho
  · rw [he.neg_one_pow, Nat.even_iff.mp he]; simp
  · rw [ho.neg_one_pow, Nat.odd_iff.mp ho]; norm_num

lemma a_eq (n : ℕ) : a n = - (Finset.range n).sum g := by
  unfold a; simp only []; congr 1
  apply Finset.sum_congr rfl; intro k _
  show (-1 : ℤ) ^ (⌊((3 : ℝ) / 2) ^ (k+1)⌋).toNat = g k
  unfold g
  have hfloor : (⌊((3 : ℝ) / 2) ^ (k+1)⌋).toNat = 3 ^ (k+1) / 2 ^ (k+1) := by
    rw [floor_thp]
    have : ((3 : ℤ) ^ (k+1)) / ((2 : ℤ) ^ (k+1)) = ((3 ^ (k+1) / 2 ^ (k+1) : ℕ) : ℤ) := by
      rw [Int.natCast_div]; push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [hfloor, neg_one_pow_nat]

set_option maxRecDepth 200000
set_option exponentiation.threshold 100000000

lemma P1000 : (Finset.range 1000).sum g = -102 := by decide
lemma P2000 : (Finset.range 2000).sum g = -96 := by
  rw [show (2000:ℕ) = 1000 + 1000 from rfl, Finset.sum_range_add, P1000]; decide
lemma P3000 : (Finset.range 3000).sum g = -44 := by
  rw [show (3000:ℕ) = 2000 + 1000 from rfl, Finset.sum_range_add, P2000]; decide
lemma P4000 : (Finset.range 4000).sum g = -84 := by
  rw [show (4000:ℕ) = 3000 + 1000 from rfl, Finset.sum_range_add, P3000]; decide
lemma P5000 : (Finset.range 5000).sum g = -72 := by
  rw [show (5000:ℕ) = 4000 + 1000 from rfl, Finset.sum_range_add, P4000]; decide
lemma P6000 : (Finset.range 6000).sum g = -86 := by
  rw [show (6000:ℕ) = 5000 + 1000 from rfl, Finset.sum_range_add, P5000]; decide
lemma P7000 : (Finset.range 7000).sum g = -104 := by
  rw [show (7000:ℕ) = 6000 + 1000 from rfl, Finset.sum_range_add, P6000]; decide
lemma P8000 : (Finset.range 8000).sum g = -118 := by
  rw [show (8000:ℕ) = 7000 + 1000 from rfl, Finset.sum_range_add, P7000]; decide
lemma P9000 : (Finset.range 9000).sum g = -158 := by
  rw [show (9000:ℕ) = 8000 + 1000 from rfl, Finset.sum_range_add, P8000]; decide
lemma P10000 : (Finset.range 10000).sum g = -140 := by
  rw [show (10000:ℕ) = 9000 + 1000 from rfl, Finset.sum_range_add, P9000]; decide
lemma P11000 : (Finset.range 11000).sum g = -148 := by
  rw [show (11000:ℕ) = 10000 + 1000 from rfl, Finset.sum_range_add, P10000]; decide
lemma P12000 : (Finset.range 12000).sum g = -222 := by
  rw [show (12000:ℕ) = 11000 + 1000 from rfl, Finset.sum_range_add, P11000]; decide
lemma P13000 : (Finset.range 13000).sum g = -188 := by
  rw [show (13000:ℕ) = 12000 + 1000 from rfl, Finset.sum_range_add, P12000]; decide
lemma P14000 : (Finset.range 14000).sum g = -192 := by
  rw [show (14000:ℕ) = 13000 + 1000 from rfl, Finset.sum_range_add, P13000]; decide
lemma P15000 : (Finset.range 15000).sum g = -190 := by
  rw [show (15000:ℕ) = 14000 + 1000 from rfl, Finset.sum_range_add, P14000]; decide
lemma P16000 : (Finset.range 16000).sum g = -212 := by
  rw [show (16000:ℕ) = 15000 + 1000 from rfl, Finset.sum_range_add, P15000]; decide
lemma P17000 : (Finset.range 17000).sum g = -214 := by
  rw [show (17000:ℕ) = 16000 + 1000 from rfl, Finset.sum_range_add, P16000]; decide
lemma P18000 : (Finset.range 18000).sum g = -140 := by
  rw [show (18000:ℕ) = 17000 + 1000 from rfl, Finset.sum_range_add, P17000]; decide
lemma P19000 : (Finset.range 19000).sum g = -172 := by
  rw [show (19000:ℕ) = 18000 + 1000 from rfl, Finset.sum_range_add, P18000]; decide
lemma P20000 : (Finset.range 20000).sum g = -222 := by
  rw [show (20000:ℕ) = 19000 + 1000 from rfl, Finset.sum_range_add, P19000]; decide
lemma P21000 : (Finset.range 21000).sum g = -180 := by
  rw [show (21000:ℕ) = 20000 + 1000 from rfl, Finset.sum_range_add, P20000]; decide
lemma P22000 : (Finset.range 22000).sum g = -136 := by
  rw [show (22000:ℕ) = 21000 + 1000 from rfl, Finset.sum_range_add, P21000]; decide
lemma P23000 : (Finset.range 23000).sum g = -178 := by
  rw [show (23000:ℕ) = 22000 + 1000 from rfl, Finset.sum_range_add, P22000]; decide
lemma P24000 : (Finset.range 24000).sum g = -198 := by
  rw [show (24000:ℕ) = 23000 + 1000 from rfl, Finset.sum_range_add, P23000]; decide
lemma P25000 : (Finset.range 25000).sum g = -252 := by
  rw [show (25000:ℕ) = 24000 + 1000 from rfl, Finset.sum_range_add, P24000]; decide
lemma P26000 : (Finset.range 26000).sum g = -280 := by
  rw [show (26000:ℕ) = 25000 + 1000 from rfl, Finset.sum_range_add, P25000]; decide
lemma P27000 : (Finset.range 27000).sum g = -296 := by
  rw [show (27000:ℕ) = 26000 + 1000 from rfl, Finset.sum_range_add, P26000]; decide
lemma P28000 : (Finset.range 28000).sum g = -252 := by
  rw [show (28000:ℕ) = 27000 + 1000 from rfl, Finset.sum_range_add, P27000]; decide
lemma P29000 : (Finset.range 29000).sum g = -228 := by
  rw [show (29000:ℕ) = 28000 + 1000 from rfl, Finset.sum_range_add, P28000]; decide
lemma P30000 : (Finset.range 30000).sum g = -252 := by
  rw [show (30000:ℕ) = 29000 + 1000 from rfl, Finset.sum_range_add, P29000]; decide
lemma P31000 : (Finset.range 31000).sum g = -244 := by
  rw [show (31000:ℕ) = 30000 + 1000 from rfl, Finset.sum_range_add, P30000]; decide
lemma P32000 : (Finset.range 32000).sum g = -250 := by
  rw [show (32000:ℕ) = 31000 + 1000 from rfl, Finset.sum_range_add, P31000]; decide
lemma P33000 : (Finset.range 33000).sum g = -272 := by
  rw [show (33000:ℕ) = 32000 + 1000 from rfl, Finset.sum_range_add, P32000]; decide
lemma P34000 : (Finset.range 34000).sum g = -276 := by
  rw [show (34000:ℕ) = 33000 + 1000 from rfl, Finset.sum_range_add, P33000]; decide
lemma P35000 : (Finset.range 35000).sum g = -264 := by
  rw [show (35000:ℕ) = 34000 + 1000 from rfl, Finset.sum_range_add, P34000]; decide
lemma P36000 : (Finset.range 36000).sum g = -278 := by
  rw [show (36000:ℕ) = 35000 + 1000 from rfl, Finset.sum_range_add, P35000]; decide
lemma P37000 : (Finset.range 37000).sum g = -230 := by
  rw [show (37000:ℕ) = 36000 + 1000 from rfl, Finset.sum_range_add, P36000]; decide
lemma P38000 : (Finset.range 38000).sum g = -228 := by
  rw [show (38000:ℕ) = 37000 + 1000 from rfl, Finset.sum_range_add, P37000]; decide
lemma P39000 : (Finset.range 39000).sum g = -254 := by
  rw [show (39000:ℕ) = 38000 + 1000 from rfl, Finset.sum_range_add, P38000]; decide
lemma P40000 : (Finset.range 40000).sum g = -300 := by
  rw [show (40000:ℕ) = 39000 + 1000 from rfl, Finset.sum_range_add, P39000]; decide
lemma P41000 : (Finset.range 41000).sum g = -326 := by
  rw [show (41000:ℕ) = 40000 + 1000 from rfl, Finset.sum_range_add, P40000]; decide
lemma P42000 : (Finset.range 42000).sum g = -338 := by
  rw [show (42000:ℕ) = 41000 + 1000 from rfl, Finset.sum_range_add, P41000]; decide
lemma P43000 : (Finset.range 43000).sum g = -312 := by
  rw [show (43000:ℕ) = 42000 + 1000 from rfl, Finset.sum_range_add, P42000]; decide
lemma P44000 : (Finset.range 44000).sum g = -260 := by
  rw [show (44000:ℕ) = 43000 + 1000 from rfl, Finset.sum_range_add, P43000]; decide
lemma P45000 : (Finset.range 45000).sum g = -304 := by
  rw [show (45000:ℕ) = 44000 + 1000 from rfl, Finset.sum_range_add, P44000]; decide
lemma P46000 : (Finset.range 46000).sum g = -266 := by
  rw [show (46000:ℕ) = 45000 + 1000 from rfl, Finset.sum_range_add, P45000]; decide
lemma P47000 : (Finset.range 47000).sum g = -266 := by
  rw [show (47000:ℕ) = 46000 + 1000 from rfl, Finset.sum_range_add, P46000]; decide
lemma P48000 : (Finset.range 48000).sum g = -240 := by
  rw [show (48000:ℕ) = 47000 + 1000 from rfl, Finset.sum_range_add, P47000]; decide
lemma P49000 : (Finset.range 49000).sum g = -216 := by
  rw [show (49000:ℕ) = 48000 + 1000 from rfl, Finset.sum_range_add, P48000]; decide
lemma P50000 : (Finset.range 50000).sum g = -176 := by
  rw [show (50000:ℕ) = 49000 + 1000 from rfl, Finset.sum_range_add, P49000]; decide
lemma P51000 : (Finset.range 51000).sum g = -168 := by
  rw [show (51000:ℕ) = 50000 + 1000 from rfl, Finset.sum_range_add, P50000]; decide
lemma P52000 : (Finset.range 52000).sum g = -182 := by
  rw [show (52000:ℕ) = 51000 + 1000 from rfl, Finset.sum_range_add, P51000]; decide
lemma P53000 : (Finset.range 53000).sum g = -164 := by
  rw [show (53000:ℕ) = 52000 + 1000 from rfl, Finset.sum_range_add, P52000]; decide
lemma P54000 : (Finset.range 54000).sum g = -190 := by
  rw [show (54000:ℕ) = 53000 + 1000 from rfl, Finset.sum_range_add, P53000]; decide
lemma P55000 : (Finset.range 55000).sum g = -214 := by
  rw [show (55000:ℕ) = 54000 + 1000 from rfl, Finset.sum_range_add, P54000]; decide
lemma P56000 : (Finset.range 56000).sum g = -230 := by
  rw [show (56000:ℕ) = 55000 + 1000 from rfl, Finset.sum_range_add, P55000]; decide
lemma P57000 : (Finset.range 57000).sum g = -230 := by
  rw [show (57000:ℕ) = 56000 + 1000 from rfl, Finset.sum_range_add, P56000]; decide
lemma P58000 : (Finset.range 58000).sum g = -244 := by
  rw [show (58000:ℕ) = 57000 + 1000 from rfl, Finset.sum_range_add, P57000]; decide
lemma P59000 : (Finset.range 59000).sum g = -228 := by
  rw [show (59000:ℕ) = 58000 + 1000 from rfl, Finset.sum_range_add, P58000]; decide
lemma P60000 : (Finset.range 60000).sum g = -238 := by
  rw [show (60000:ℕ) = 59000 + 1000 from rfl, Finset.sum_range_add, P59000]; decide
lemma P61000 : (Finset.range 61000).sum g = -240 := by
  rw [show (61000:ℕ) = 60000 + 1000 from rfl, Finset.sum_range_add, P60000]; decide
lemma P62000 : (Finset.range 62000).sum g = -288 := by
  rw [show (62000:ℕ) = 61000 + 1000 from rfl, Finset.sum_range_add, P61000]; decide
lemma P63000 : (Finset.range 63000).sum g = -250 := by
  rw [show (63000:ℕ) = 62000 + 1000 from rfl, Finset.sum_range_add, P62000]; decide
lemma P64000 : (Finset.range 64000).sum g = -242 := by
  rw [show (64000:ℕ) = 63000 + 1000 from rfl, Finset.sum_range_add, P63000]; decide
lemma P65000 : (Finset.range 65000).sum g = -258 := by
  rw [show (65000:ℕ) = 64000 + 1000 from rfl, Finset.sum_range_add, P64000]; decide
lemma P66000 : (Finset.range 66000).sum g = -326 := by
  rw [show (66000:ℕ) = 65000 + 1000 from rfl, Finset.sum_range_add, P65000]; decide
lemma P67000 : (Finset.range 67000).sum g = -354 := by
  rw [show (67000:ℕ) = 66000 + 1000 from rfl, Finset.sum_range_add, P66000]; decide
lemma P68000 : (Finset.range 68000).sum g = -330 := by
  rw [show (68000:ℕ) = 67000 + 1000 from rfl, Finset.sum_range_add, P67000]; decide
lemma P69000 : (Finset.range 69000).sum g = -324 := by
  rw [show (69000:ℕ) = 68000 + 1000 from rfl, Finset.sum_range_add, P68000]; decide
lemma P70000 : (Finset.range 70000).sum g = -256 := by
  rw [show (70000:ℕ) = 69000 + 1000 from rfl, Finset.sum_range_add, P69000]; decide
lemma P71000 : (Finset.range 71000).sum g = -278 := by
  rw [show (71000:ℕ) = 70000 + 1000 from rfl, Finset.sum_range_add, P70000]; decide
lemma P72000 : (Finset.range 72000).sum g = -302 := by
  rw [show (72000:ℕ) = 71000 + 1000 from rfl, Finset.sum_range_add, P71000]; decide
lemma P73000 : (Finset.range 73000).sum g = -308 := by
  rw [show (73000:ℕ) = 72000 + 1000 from rfl, Finset.sum_range_add, P72000]; decide
lemma P74000 : (Finset.range 74000).sum g = -348 := by
  rw [show (74000:ℕ) = 73000 + 1000 from rfl, Finset.sum_range_add, P73000]; decide
lemma P75000 : (Finset.range 75000).sum g = -430 := by
  rw [show (75000:ℕ) = 74000 + 1000 from rfl, Finset.sum_range_add, P74000]; decide
lemma P76000 : (Finset.range 76000).sum g = -464 := by
  rw [show (76000:ℕ) = 75000 + 1000 from rfl, Finset.sum_range_add, P75000]; decide
lemma P77000 : (Finset.range 77000).sum g = -442 := by
  rw [show (77000:ℕ) = 76000 + 1000 from rfl, Finset.sum_range_add, P76000]; decide
lemma P78000 : (Finset.range 78000).sum g = -480 := by
  rw [show (78000:ℕ) = 77000 + 1000 from rfl, Finset.sum_range_add, P77000]; decide
lemma P79000 : (Finset.range 79000).sum g = -492 := by
  rw [show (79000:ℕ) = 78000 + 1000 from rfl, Finset.sum_range_add, P78000]; decide
lemma P80000 : (Finset.range 80000).sum g = -472 := by
  rw [show (80000:ℕ) = 79000 + 1000 from rfl, Finset.sum_range_add, P79000]; decide
lemma P81000 : (Finset.range 81000).sum g = -480 := by
  rw [show (81000:ℕ) = 80000 + 1000 from rfl, Finset.sum_range_add, P80000]; decide
lemma P82000 : (Finset.range 82000).sum g = -446 := by
  rw [show (82000:ℕ) = 81000 + 1000 from rfl, Finset.sum_range_add, P81000]; decide
lemma P83000 : (Finset.range 83000).sum g = -466 := by
  rw [show (83000:ℕ) = 82000 + 1000 from rfl, Finset.sum_range_add, P82000]; decide
lemma P84000 : (Finset.range 84000).sum g = -482 := by
  rw [show (84000:ℕ) = 83000 + 1000 from rfl, Finset.sum_range_add, P83000]; decide
lemma P85000 : (Finset.range 85000).sum g = -488 := by
  rw [show (85000:ℕ) = 84000 + 1000 from rfl, Finset.sum_range_add, P84000]; decide
lemma P86000 : (Finset.range 86000).sum g = -470 := by
  rw [show (86000:ℕ) = 85000 + 1000 from rfl, Finset.sum_range_add, P85000]; decide
lemma P87000 : (Finset.range 87000).sum g = -546 := by
  rw [show (87000:ℕ) = 86000 + 1000 from rfl, Finset.sum_range_add, P86000]; decide
lemma P88000 : (Finset.range 88000).sum g = -540 := by
  rw [show (88000:ℕ) = 87000 + 1000 from rfl, Finset.sum_range_add, P87000]; decide
lemma P89000 : (Finset.range 89000).sum g = -532 := by
  rw [show (89000:ℕ) = 88000 + 1000 from rfl, Finset.sum_range_add, P88000]; decide
lemma P90000 : (Finset.range 90000).sum g = -550 := by
  rw [show (90000:ℕ) = 89000 + 1000 from rfl, Finset.sum_range_add, P89000]; decide
lemma P91000 : (Finset.range 91000).sum g = -622 := by
  rw [show (91000:ℕ) = 90000 + 1000 from rfl, Finset.sum_range_add, P90000]; decide
lemma P92000 : (Finset.range 92000).sum g = -624 := by
  rw [show (92000:ℕ) = 91000 + 1000 from rfl, Finset.sum_range_add, P91000]; decide
lemma P93000 : (Finset.range 93000).sum g = -642 := by
  rw [show (93000:ℕ) = 92000 + 1000 from rfl, Finset.sum_range_add, P92000]; decide
lemma P94000 : (Finset.range 94000).sum g = -614 := by
  rw [show (94000:ℕ) = 93000 + 1000 from rfl, Finset.sum_range_add, P93000]; decide
lemma P95000 : (Finset.range 95000).sum g = -624 := by
  rw [show (95000:ℕ) = 94000 + 1000 from rfl, Finset.sum_range_add, P94000]; decide
lemma P96000 : (Finset.range 96000).sum g = -562 := by
  rw [show (96000:ℕ) = 95000 + 1000 from rfl, Finset.sum_range_add, P95000]; decide
lemma P97000 : (Finset.range 97000).sum g = -560 := by
  rw [show (97000:ℕ) = 96000 + 1000 from rfl, Finset.sum_range_add, P96000]; decide
lemma P98000 : (Finset.range 98000).sum g = -572 := by
  rw [show (98000:ℕ) = 97000 + 1000 from rfl, Finset.sum_range_add, P97000]; decide
lemma P99000 : (Finset.range 99000).sum g = -578 := by
  rw [show (99000:ℕ) = 98000 + 1000 from rfl, Finset.sum_range_add, P98000]; decide
lemma P100000 : (Finset.range 100000).sum g = -526 := by
  rw [show (100000:ℕ) = 99000 + 1000 from rfl, Finset.sum_range_add, P99000]; decide
lemma P101000 : (Finset.range 101000).sum g = -534 := by
  rw [show (101000:ℕ) = 100000 + 1000 from rfl, Finset.sum_range_add, P100000]; decide
lemma P102000 : (Finset.range 102000).sum g = -540 := by
  rw [show (102000:ℕ) = 101000 + 1000 from rfl, Finset.sum_range_add, P101000]; decide
lemma P103000 : (Finset.range 103000).sum g = -594 := by
  rw [show (103000:ℕ) = 102000 + 1000 from rfl, Finset.sum_range_add, P102000]; decide
lemma P104000 : (Finset.range 104000).sum g = -578 := by
  rw [show (104000:ℕ) = 103000 + 1000 from rfl, Finset.sum_range_add, P103000]; decide
lemma P105000 : (Finset.range 105000).sum g = -566 := by
  rw [show (105000:ℕ) = 104000 + 1000 from rfl, Finset.sum_range_add, P104000]; decide
lemma P106000 : (Finset.range 106000).sum g = -570 := by
  rw [show (106000:ℕ) = 105000 + 1000 from rfl, Finset.sum_range_add, P105000]; decide
lemma P107000 : (Finset.range 107000).sum g = -554 := by
  rw [show (107000:ℕ) = 106000 + 1000 from rfl, Finset.sum_range_add, P106000]; decide
lemma P108000 : (Finset.range 108000).sum g = -578 := by
  rw [show (108000:ℕ) = 107000 + 1000 from rfl, Finset.sum_range_add, P107000]; decide
lemma P109000 : (Finset.range 109000).sum g = -546 := by
  rw [show (109000:ℕ) = 108000 + 1000 from rfl, Finset.sum_range_add, P108000]; decide
lemma P110000 : (Finset.range 110000).sum g = -500 := by
  rw [show (110000:ℕ) = 109000 + 1000 from rfl, Finset.sum_range_add, P109000]; decide
lemma P111000 : (Finset.range 111000).sum g = -476 := by
  rw [show (111000:ℕ) = 110000 + 1000 from rfl, Finset.sum_range_add, P110000]; decide
lemma P112000 : (Finset.range 112000).sum g = -476 := by
  rw [show (112000:ℕ) = 111000 + 1000 from rfl, Finset.sum_range_add, P111000]; decide
lemma P113000 : (Finset.range 113000).sum g = -518 := by
  rw [show (113000:ℕ) = 112000 + 1000 from rfl, Finset.sum_range_add, P112000]; decide
lemma P114000 : (Finset.range 114000).sum g = -548 := by
  rw [show (114000:ℕ) = 113000 + 1000 from rfl, Finset.sum_range_add, P113000]; decide
lemma P115000 : (Finset.range 115000).sum g = -492 := by
  rw [show (115000:ℕ) = 114000 + 1000 from rfl, Finset.sum_range_add, P114000]; decide
lemma P116000 : (Finset.range 116000).sum g = -500 := by
  rw [show (116000:ℕ) = 115000 + 1000 from rfl, Finset.sum_range_add, P115000]; decide
lemma P117000 : (Finset.range 117000).sum g = -454 := by
  rw [show (117000:ℕ) = 116000 + 1000 from rfl, Finset.sum_range_add, P116000]; decide
lemma P118000 : (Finset.range 118000).sum g = -480 := by
  rw [show (118000:ℕ) = 117000 + 1000 from rfl, Finset.sum_range_add, P117000]; decide
lemma P119000 : (Finset.range 119000).sum g = -472 := by
  rw [show (119000:ℕ) = 118000 + 1000 from rfl, Finset.sum_range_add, P118000]; decide
lemma P120000 : (Finset.range 120000).sum g = -432 := by
  rw [show (120000:ℕ) = 119000 + 1000 from rfl, Finset.sum_range_add, P119000]; decide
lemma P121000 : (Finset.range 121000).sum g = -442 := by
  rw [show (121000:ℕ) = 120000 + 1000 from rfl, Finset.sum_range_add, P120000]; decide
lemma P122000 : (Finset.range 122000).sum g = -424 := by
  rw [show (122000:ℕ) = 121000 + 1000 from rfl, Finset.sum_range_add, P121000]; decide
lemma P123000 : (Finset.range 123000).sum g = -376 := by
  rw [show (123000:ℕ) = 122000 + 1000 from rfl, Finset.sum_range_add, P122000]; decide
lemma P124000 : (Finset.range 124000).sum g = -396 := by
  rw [show (124000:ℕ) = 123000 + 1000 from rfl, Finset.sum_range_add, P123000]; decide
lemma P125000 : (Finset.range 125000).sum g = -386 := by
  rw [show (125000:ℕ) = 124000 + 1000 from rfl, Finset.sum_range_add, P124000]; decide
lemma P126000 : (Finset.range 126000).sum g = -364 := by
  rw [show (126000:ℕ) = 125000 + 1000 from rfl, Finset.sum_range_add, P125000]; decide
lemma P127000 : (Finset.range 127000).sum g = -316 := by
  rw [show (127000:ℕ) = 126000 + 1000 from rfl, Finset.sum_range_add, P126000]; decide
lemma P128000 : (Finset.range 128000).sum g = -340 := by
  rw [show (128000:ℕ) = 127000 + 1000 from rfl, Finset.sum_range_add, P127000]; decide
lemma P129000 : (Finset.range 129000).sum g = -358 := by
  rw [show (129000:ℕ) = 128000 + 1000 from rfl, Finset.sum_range_add, P128000]; decide
lemma P130000 : (Finset.range 130000).sum g = -366 := by
  rw [show (130000:ℕ) = 129000 + 1000 from rfl, Finset.sum_range_add, P129000]; decide
lemma P131000 : (Finset.range 131000).sum g = -372 := by
  rw [show (131000:ℕ) = 130000 + 1000 from rfl, Finset.sum_range_add, P130000]; decide
lemma P132000 : (Finset.range 132000).sum g = -384 := by
  rw [show (132000:ℕ) = 131000 + 1000 from rfl, Finset.sum_range_add, P131000]; decide
lemma P133000 : (Finset.range 133000).sum g = -410 := by
  rw [show (133000:ℕ) = 132000 + 1000 from rfl, Finset.sum_range_add, P132000]; decide
lemma P134000 : (Finset.range 134000).sum g = -412 := by
  rw [show (134000:ℕ) = 133000 + 1000 from rfl, Finset.sum_range_add, P133000]; decide
lemma P135000 : (Finset.range 135000).sum g = -398 := by
  rw [show (135000:ℕ) = 134000 + 1000 from rfl, Finset.sum_range_add, P134000]; decide
lemma P136000 : (Finset.range 136000).sum g = -390 := by
  rw [show (136000:ℕ) = 135000 + 1000 from rfl, Finset.sum_range_add, P135000]; decide
lemma P137000 : (Finset.range 137000).sum g = -436 := by
  rw [show (137000:ℕ) = 136000 + 1000 from rfl, Finset.sum_range_add, P136000]; decide
lemma P138000 : (Finset.range 138000).sum g = -470 := by
  rw [show (138000:ℕ) = 137000 + 1000 from rfl, Finset.sum_range_add, P137000]; decide
lemma P139000 : (Finset.range 139000).sum g = -482 := by
  rw [show (139000:ℕ) = 138000 + 1000 from rfl, Finset.sum_range_add, P138000]; decide
lemma P140000 : (Finset.range 140000).sum g = -542 := by
  rw [show (140000:ℕ) = 139000 + 1000 from rfl, Finset.sum_range_add, P139000]; decide
lemma P141000 : (Finset.range 141000).sum g = -546 := by
  rw [show (141000:ℕ) = 140000 + 1000 from rfl, Finset.sum_range_add, P140000]; decide
lemma P142000 : (Finset.range 142000).sum g = -546 := by
  rw [show (142000:ℕ) = 141000 + 1000 from rfl, Finset.sum_range_add, P141000]; decide
lemma P143000 : (Finset.range 143000).sum g = -576 := by
  rw [show (143000:ℕ) = 142000 + 1000 from rfl, Finset.sum_range_add, P142000]; decide
lemma P144000 : (Finset.range 144000).sum g = -576 := by
  rw [show (144000:ℕ) = 143000 + 1000 from rfl, Finset.sum_range_add, P143000]; decide
lemma P145000 : (Finset.range 145000).sum g = -566 := by
  rw [show (145000:ℕ) = 144000 + 1000 from rfl, Finset.sum_range_add, P144000]; decide
lemma P146000 : (Finset.range 146000).sum g = -562 := by
  rw [show (146000:ℕ) = 145000 + 1000 from rfl, Finset.sum_range_add, P145000]; decide
lemma P147000 : (Finset.range 147000).sum g = -578 := by
  rw [show (147000:ℕ) = 146000 + 1000 from rfl, Finset.sum_range_add, P146000]; decide
lemma P148000 : (Finset.range 148000).sum g = -558 := by
  rw [show (148000:ℕ) = 147000 + 1000 from rfl, Finset.sum_range_add, P147000]; decide
lemma P149000 : (Finset.range 149000).sum g = -552 := by
  rw [show (149000:ℕ) = 148000 + 1000 from rfl, Finset.sum_range_add, P148000]; decide
lemma P150000 : (Finset.range 150000).sum g = -508 := by
  rw [show (150000:ℕ) = 149000 + 1000 from rfl, Finset.sum_range_add, P149000]; decide
lemma P151000 : (Finset.range 151000).sum g = -512 := by
  rw [show (151000:ℕ) = 150000 + 1000 from rfl, Finset.sum_range_add, P150000]; decide
lemma P152000 : (Finset.range 152000).sum g = -466 := by
  rw [show (152000:ℕ) = 151000 + 1000 from rfl, Finset.sum_range_add, P151000]; decide
lemma P153000 : (Finset.range 153000).sum g = -492 := by
  rw [show (153000:ℕ) = 152000 + 1000 from rfl, Finset.sum_range_add, P152000]; decide
lemma P154000 : (Finset.range 154000).sum g = -528 := by
  rw [show (154000:ℕ) = 153000 + 1000 from rfl, Finset.sum_range_add, P153000]; decide
lemma P155000 : (Finset.range 155000).sum g = -514 := by
  rw [show (155000:ℕ) = 154000 + 1000 from rfl, Finset.sum_range_add, P154000]; decide
lemma P156000 : (Finset.range 156000).sum g = -558 := by
  rw [show (156000:ℕ) = 155000 + 1000 from rfl, Finset.sum_range_add, P155000]; decide
lemma P157000 : (Finset.range 157000).sum g = -556 := by
  rw [show (157000:ℕ) = 156000 + 1000 from rfl, Finset.sum_range_add, P156000]; decide
lemma P158000 : (Finset.range 158000).sum g = -542 := by
  rw [show (158000:ℕ) = 157000 + 1000 from rfl, Finset.sum_range_add, P157000]; decide
lemma P159000 : (Finset.range 159000).sum g = -584 := by
  rw [show (159000:ℕ) = 158000 + 1000 from rfl, Finset.sum_range_add, P158000]; decide
lemma P160000 : (Finset.range 160000).sum g = -590 := by
  rw [show (160000:ℕ) = 159000 + 1000 from rfl, Finset.sum_range_add, P159000]; decide
lemma P161000 : (Finset.range 161000).sum g = -542 := by
  rw [show (161000:ℕ) = 160000 + 1000 from rfl, Finset.sum_range_add, P160000]; decide
lemma P162000 : (Finset.range 162000).sum g = -594 := by
  rw [show (162000:ℕ) = 161000 + 1000 from rfl, Finset.sum_range_add, P161000]; decide
lemma P163000 : (Finset.range 163000).sum g = -602 := by
  rw [show (163000:ℕ) = 162000 + 1000 from rfl, Finset.sum_range_add, P162000]; decide
lemma P164000 : (Finset.range 164000).sum g = -596 := by
  rw [show (164000:ℕ) = 163000 + 1000 from rfl, Finset.sum_range_add, P163000]; decide
lemma P165000 : (Finset.range 165000).sum g = -634 := by
  rw [show (165000:ℕ) = 164000 + 1000 from rfl, Finset.sum_range_add, P164000]; decide
lemma P166000 : (Finset.range 166000).sum g = -658 := by
  rw [show (166000:ℕ) = 165000 + 1000 from rfl, Finset.sum_range_add, P165000]; decide
lemma P167000 : (Finset.range 167000).sum g = -678 := by
  rw [show (167000:ℕ) = 166000 + 1000 from rfl, Finset.sum_range_add, P166000]; decide
lemma P168000 : (Finset.range 168000).sum g = -656 := by
  rw [show (168000:ℕ) = 167000 + 1000 from rfl, Finset.sum_range_add, P167000]; decide
lemma P169000 : (Finset.range 169000).sum g = -666 := by
  rw [show (169000:ℕ) = 168000 + 1000 from rfl, Finset.sum_range_add, P168000]; decide
lemma P170000 : (Finset.range 170000).sum g = -642 := by
  rw [show (170000:ℕ) = 169000 + 1000 from rfl, Finset.sum_range_add, P169000]; decide
lemma P171000 : (Finset.range 171000).sum g = -654 := by
  rw [show (171000:ℕ) = 170000 + 1000 from rfl, Finset.sum_range_add, P170000]; decide
lemma P172000 : (Finset.range 172000).sum g = -638 := by
  rw [show (172000:ℕ) = 171000 + 1000 from rfl, Finset.sum_range_add, P171000]; decide
lemma P173000 : (Finset.range 173000).sum g = -658 := by
  rw [show (173000:ℕ) = 172000 + 1000 from rfl, Finset.sum_range_add, P172000]; decide
lemma P174000 : (Finset.range 174000).sum g = -684 := by
  rw [show (174000:ℕ) = 173000 + 1000 from rfl, Finset.sum_range_add, P173000]; decide
lemma P175000 : (Finset.range 175000).sum g = -652 := by
  rw [show (175000:ℕ) = 174000 + 1000 from rfl, Finset.sum_range_add, P174000]; decide
lemma P176000 : (Finset.range 176000).sum g = -654 := by
  rw [show (176000:ℕ) = 175000 + 1000 from rfl, Finset.sum_range_add, P175000]; decide
lemma P177000 : (Finset.range 177000).sum g = -638 := by
  rw [show (177000:ℕ) = 176000 + 1000 from rfl, Finset.sum_range_add, P176000]; decide
lemma P178000 : (Finset.range 178000).sum g = -616 := by
  rw [show (178000:ℕ) = 177000 + 1000 from rfl, Finset.sum_range_add, P177000]; decide
lemma P179000 : (Finset.range 179000).sum g = -630 := by
  rw [show (179000:ℕ) = 178000 + 1000 from rfl, Finset.sum_range_add, P178000]; decide
lemma P180000 : (Finset.range 180000).sum g = -620 := by
  rw [show (180000:ℕ) = 179000 + 1000 from rfl, Finset.sum_range_add, P179000]; decide
lemma P181000 : (Finset.range 181000).sum g = -632 := by
  rw [show (181000:ℕ) = 180000 + 1000 from rfl, Finset.sum_range_add, P180000]; decide
lemma P182000 : (Finset.range 182000).sum g = -610 := by
  rw [show (182000:ℕ) = 181000 + 1000 from rfl, Finset.sum_range_add, P181000]; decide
lemma P183000 : (Finset.range 183000).sum g = -612 := by
  rw [show (183000:ℕ) = 182000 + 1000 from rfl, Finset.sum_range_add, P182000]; decide
lemma P184000 : (Finset.range 184000).sum g = -540 := by
  rw [show (184000:ℕ) = 183000 + 1000 from rfl, Finset.sum_range_add, P183000]; decide
lemma P185000 : (Finset.range 185000).sum g = -586 := by
  rw [show (185000:ℕ) = 184000 + 1000 from rfl, Finset.sum_range_add, P184000]; decide
lemma P186000 : (Finset.range 186000).sum g = -538 := by
  rw [show (186000:ℕ) = 185000 + 1000 from rfl, Finset.sum_range_add, P185000]; decide
lemma P187000 : (Finset.range 187000).sum g = -518 := by
  rw [show (187000:ℕ) = 186000 + 1000 from rfl, Finset.sum_range_add, P186000]; decide
lemma P188000 : (Finset.range 188000).sum g = -516 := by
  rw [show (188000:ℕ) = 187000 + 1000 from rfl, Finset.sum_range_add, P187000]; decide
lemma P189000 : (Finset.range 189000).sum g = -482 := by
  rw [show (189000:ℕ) = 188000 + 1000 from rfl, Finset.sum_range_add, P188000]; decide
lemma P190000 : (Finset.range 190000).sum g = -502 := by
  rw [show (190000:ℕ) = 189000 + 1000 from rfl, Finset.sum_range_add, P189000]; decide
lemma P191000 : (Finset.range 191000).sum g = -460 := by
  rw [show (191000:ℕ) = 190000 + 1000 from rfl, Finset.sum_range_add, P190000]; decide
lemma P192000 : (Finset.range 192000).sum g = -462 := by
  rw [show (192000:ℕ) = 191000 + 1000 from rfl, Finset.sum_range_add, P191000]; decide
lemma P193000 : (Finset.range 193000).sum g = -442 := by
  rw [show (193000:ℕ) = 192000 + 1000 from rfl, Finset.sum_range_add, P192000]; decide
lemma P194000 : (Finset.range 194000).sum g = -482 := by
  rw [show (194000:ℕ) = 193000 + 1000 from rfl, Finset.sum_range_add, P193000]; decide
lemma P195000 : (Finset.range 195000).sum g = -468 := by
  rw [show (195000:ℕ) = 194000 + 1000 from rfl, Finset.sum_range_add, P194000]; decide
lemma P196000 : (Finset.range 196000).sum g = -456 := by
  rw [show (196000:ℕ) = 195000 + 1000 from rfl, Finset.sum_range_add, P195000]; decide
lemma P197000 : (Finset.range 197000).sum g = -486 := by
  rw [show (197000:ℕ) = 196000 + 1000 from rfl, Finset.sum_range_add, P196000]; decide
lemma P198000 : (Finset.range 198000).sum g = -488 := by
  rw [show (198000:ℕ) = 197000 + 1000 from rfl, Finset.sum_range_add, P197000]; decide
lemma P199000 : (Finset.range 199000).sum g = -538 := by
  rw [show (199000:ℕ) = 198000 + 1000 from rfl, Finset.sum_range_add, P198000]; decide
lemma P200000 : (Finset.range 200000).sum g = -554 := by
  rw [show (200000:ℕ) = 199000 + 1000 from rfl, Finset.sum_range_add, P199000]; decide
lemma P201000 : (Finset.range 201000).sum g = -540 := by
  rw [show (201000:ℕ) = 200000 + 1000 from rfl, Finset.sum_range_add, P200000]; decide
lemma P202000 : (Finset.range 202000).sum g = -546 := by
  rw [show (202000:ℕ) = 201000 + 1000 from rfl, Finset.sum_range_add, P201000]; decide
lemma P203000 : (Finset.range 203000).sum g = -540 := by
  rw [show (203000:ℕ) = 202000 + 1000 from rfl, Finset.sum_range_add, P202000]; decide
lemma P204000 : (Finset.range 204000).sum g = -544 := by
  rw [show (204000:ℕ) = 203000 + 1000 from rfl, Finset.sum_range_add, P203000]; decide
lemma P205000 : (Finset.range 205000).sum g = -494 := by
  rw [show (205000:ℕ) = 204000 + 1000 from rfl, Finset.sum_range_add, P204000]; decide
lemma P206000 : (Finset.range 206000).sum g = -494 := by
  rw [show (206000:ℕ) = 205000 + 1000 from rfl, Finset.sum_range_add, P205000]; decide
lemma P207000 : (Finset.range 207000).sum g = -472 := by
  rw [show (207000:ℕ) = 206000 + 1000 from rfl, Finset.sum_range_add, P206000]; decide
lemma P208000 : (Finset.range 208000).sum g = -490 := by
  rw [show (208000:ℕ) = 207000 + 1000 from rfl, Finset.sum_range_add, P207000]; decide
lemma P209000 : (Finset.range 209000).sum g = -470 := by
  rw [show (209000:ℕ) = 208000 + 1000 from rfl, Finset.sum_range_add, P208000]; decide
lemma P210000 : (Finset.range 210000).sum g = -394 := by
  rw [show (210000:ℕ) = 209000 + 1000 from rfl, Finset.sum_range_add, P209000]; decide
lemma P211000 : (Finset.range 211000).sum g = -380 := by
  rw [show (211000:ℕ) = 210000 + 1000 from rfl, Finset.sum_range_add, P210000]; decide
lemma P212000 : (Finset.range 212000).sum g = -392 := by
  rw [show (212000:ℕ) = 211000 + 1000 from rfl, Finset.sum_range_add, P211000]; decide
lemma P213000 : (Finset.range 213000).sum g = -374 := by
  rw [show (213000:ℕ) = 212000 + 1000 from rfl, Finset.sum_range_add, P212000]; decide
lemma P214000 : (Finset.range 214000).sum g = -380 := by
  rw [show (214000:ℕ) = 213000 + 1000 from rfl, Finset.sum_range_add, P213000]; decide
lemma P215000 : (Finset.range 215000).sum g = -424 := by
  rw [show (215000:ℕ) = 214000 + 1000 from rfl, Finset.sum_range_add, P214000]; decide
lemma P216000 : (Finset.range 216000).sum g = -362 := by
  rw [show (216000:ℕ) = 215000 + 1000 from rfl, Finset.sum_range_add, P215000]; decide
lemma P217000 : (Finset.range 217000).sum g = -340 := by
  rw [show (217000:ℕ) = 216000 + 1000 from rfl, Finset.sum_range_add, P216000]; decide
lemma P218000 : (Finset.range 218000).sum g = -352 := by
  rw [show (218000:ℕ) = 217000 + 1000 from rfl, Finset.sum_range_add, P217000]; decide
lemma P219000 : (Finset.range 219000).sum g = -370 := by
  rw [show (219000:ℕ) = 218000 + 1000 from rfl, Finset.sum_range_add, P218000]; decide
lemma P220000 : (Finset.range 220000).sum g = -430 := by
  rw [show (220000:ℕ) = 219000 + 1000 from rfl, Finset.sum_range_add, P219000]; decide
lemma P221000 : (Finset.range 221000).sum g = -418 := by
  rw [show (221000:ℕ) = 220000 + 1000 from rfl, Finset.sum_range_add, P220000]; decide
lemma P222000 : (Finset.range 222000).sum g = -468 := by
  rw [show (222000:ℕ) = 221000 + 1000 from rfl, Finset.sum_range_add, P221000]; decide
lemma P223000 : (Finset.range 223000).sum g = -504 := by
  rw [show (223000:ℕ) = 222000 + 1000 from rfl, Finset.sum_range_add, P222000]; decide
lemma P224000 : (Finset.range 224000).sum g = -504 := by
  rw [show (224000:ℕ) = 223000 + 1000 from rfl, Finset.sum_range_add, P223000]; decide
lemma P225000 : (Finset.range 225000).sum g = -536 := by
  rw [show (225000:ℕ) = 224000 + 1000 from rfl, Finset.sum_range_add, P224000]; decide
lemma P226000 : (Finset.range 226000).sum g = -540 := by
  rw [show (226000:ℕ) = 225000 + 1000 from rfl, Finset.sum_range_add, P225000]; decide
lemma P227000 : (Finset.range 227000).sum g = -532 := by
  rw [show (227000:ℕ) = 226000 + 1000 from rfl, Finset.sum_range_add, P226000]; decide
lemma P228000 : (Finset.range 228000).sum g = -552 := by
  rw [show (228000:ℕ) = 227000 + 1000 from rfl, Finset.sum_range_add, P227000]; decide
lemma P229000 : (Finset.range 229000).sum g = -576 := by
  rw [show (229000:ℕ) = 228000 + 1000 from rfl, Finset.sum_range_add, P228000]; decide
lemma P230000 : (Finset.range 230000).sum g = -558 := by
  rw [show (230000:ℕ) = 229000 + 1000 from rfl, Finset.sum_range_add, P229000]; decide
lemma P231000 : (Finset.range 231000).sum g = -514 := by
  rw [show (231000:ℕ) = 230000 + 1000 from rfl, Finset.sum_range_add, P230000]; decide
lemma P232000 : (Finset.range 232000).sum g = -586 := by
  rw [show (232000:ℕ) = 231000 + 1000 from rfl, Finset.sum_range_add, P231000]; decide
lemma P233000 : (Finset.range 233000).sum g = -590 := by
  rw [show (233000:ℕ) = 232000 + 1000 from rfl, Finset.sum_range_add, P232000]; decide
lemma P234000 : (Finset.range 234000).sum g = -578 := by
  rw [show (234000:ℕ) = 233000 + 1000 from rfl, Finset.sum_range_add, P233000]; decide
lemma P235000 : (Finset.range 235000).sum g = -554 := by
  rw [show (235000:ℕ) = 234000 + 1000 from rfl, Finset.sum_range_add, P234000]; decide
lemma P236000 : (Finset.range 236000).sum g = -522 := by
  rw [show (236000:ℕ) = 235000 + 1000 from rfl, Finset.sum_range_add, P235000]; decide
lemma P237000 : (Finset.range 237000).sum g = -540 := by
  rw [show (237000:ℕ) = 236000 + 1000 from rfl, Finset.sum_range_add, P236000]; decide
lemma P238000 : (Finset.range 238000).sum g = -542 := by
  rw [show (238000:ℕ) = 237000 + 1000 from rfl, Finset.sum_range_add, P237000]; decide
lemma P239000 : (Finset.range 239000).sum g = -532 := by
  rw [show (239000:ℕ) = 238000 + 1000 from rfl, Finset.sum_range_add, P238000]; decide
lemma P240000 : (Finset.range 240000).sum g = -566 := by
  rw [show (240000:ℕ) = 239000 + 1000 from rfl, Finset.sum_range_add, P239000]; decide
lemma P241000 : (Finset.range 241000).sum g = -590 := by
  rw [show (241000:ℕ) = 240000 + 1000 from rfl, Finset.sum_range_add, P240000]; decide
lemma P242000 : (Finset.range 242000).sum g = -592 := by
  rw [show (242000:ℕ) = 241000 + 1000 from rfl, Finset.sum_range_add, P241000]; decide
lemma P243000 : (Finset.range 243000).sum g = -578 := by
  rw [show (243000:ℕ) = 242000 + 1000 from rfl, Finset.sum_range_add, P242000]; decide
lemma P244000 : (Finset.range 244000).sum g = -538 := by
  rw [show (244000:ℕ) = 243000 + 1000 from rfl, Finset.sum_range_add, P243000]; decide
lemma P245000 : (Finset.range 245000).sum g = -538 := by
  rw [show (245000:ℕ) = 244000 + 1000 from rfl, Finset.sum_range_add, P244000]; decide
lemma P246000 : (Finset.range 246000).sum g = -538 := by
  rw [show (246000:ℕ) = 245000 + 1000 from rfl, Finset.sum_range_add, P245000]; decide
lemma P247000 : (Finset.range 247000).sum g = -558 := by
  rw [show (247000:ℕ) = 246000 + 1000 from rfl, Finset.sum_range_add, P246000]; decide
lemma P248000 : (Finset.range 248000).sum g = -560 := by
  rw [show (248000:ℕ) = 247000 + 1000 from rfl, Finset.sum_range_add, P247000]; decide
lemma P249000 : (Finset.range 249000).sum g = -542 := by
  rw [show (249000:ℕ) = 248000 + 1000 from rfl, Finset.sum_range_add, P248000]; decide
lemma P250000 : (Finset.range 250000).sum g = -450 := by
  rw [show (250000:ℕ) = 249000 + 1000 from rfl, Finset.sum_range_add, P249000]; decide
lemma P251000 : (Finset.range 251000).sum g = -448 := by
  rw [show (251000:ℕ) = 250000 + 1000 from rfl, Finset.sum_range_add, P250000]; decide
lemma P252000 : (Finset.range 252000).sum g = -458 := by
  rw [show (252000:ℕ) = 251000 + 1000 from rfl, Finset.sum_range_add, P251000]; decide
lemma P253000 : (Finset.range 253000).sum g = -430 := by
  rw [show (253000:ℕ) = 252000 + 1000 from rfl, Finset.sum_range_add, P252000]; decide
lemma P254000 : (Finset.range 254000).sum g = -414 := by
  rw [show (254000:ℕ) = 253000 + 1000 from rfl, Finset.sum_range_add, P253000]; decide
lemma P255000 : (Finset.range 255000).sum g = -372 := by
  rw [show (255000:ℕ) = 254000 + 1000 from rfl, Finset.sum_range_add, P254000]; decide
lemma P256000 : (Finset.range 256000).sum g = -354 := by
  rw [show (256000:ℕ) = 255000 + 1000 from rfl, Finset.sum_range_add, P255000]; decide
lemma P257000 : (Finset.range 257000).sum g = -332 := by
  rw [show (257000:ℕ) = 256000 + 1000 from rfl, Finset.sum_range_add, P256000]; decide
lemma P258000 : (Finset.range 258000).sum g = -298 := by
  rw [show (258000:ℕ) = 257000 + 1000 from rfl, Finset.sum_range_add, P257000]; decide
lemma P259000 : (Finset.range 259000).sum g = -320 := by
  rw [show (259000:ℕ) = 258000 + 1000 from rfl, Finset.sum_range_add, P258000]; decide
lemma P260000 : (Finset.range 260000).sum g = -298 := by
  rw [show (260000:ℕ) = 259000 + 1000 from rfl, Finset.sum_range_add, P259000]; decide
lemma P261000 : (Finset.range 261000).sum g = -258 := by
  rw [show (261000:ℕ) = 260000 + 1000 from rfl, Finset.sum_range_add, P260000]; decide
lemma P262000 : (Finset.range 262000).sum g = -264 := by
  rw [show (262000:ℕ) = 261000 + 1000 from rfl, Finset.sum_range_add, P261000]; decide
lemma P263000 : (Finset.range 263000).sum g = -238 := by
  rw [show (263000:ℕ) = 262000 + 1000 from rfl, Finset.sum_range_add, P262000]; decide
lemma P264000 : (Finset.range 264000).sum g = -206 := by
  rw [show (264000:ℕ) = 263000 + 1000 from rfl, Finset.sum_range_add, P263000]; decide
lemma P265000 : (Finset.range 265000).sum g = -272 := by
  rw [show (265000:ℕ) = 264000 + 1000 from rfl, Finset.sum_range_add, P264000]; decide
lemma P266000 : (Finset.range 266000).sum g = -256 := by
  rw [show (266000:ℕ) = 265000 + 1000 from rfl, Finset.sum_range_add, P265000]; decide
lemma P267000 : (Finset.range 267000).sum g = -222 := by
  rw [show (267000:ℕ) = 266000 + 1000 from rfl, Finset.sum_range_add, P266000]; decide
lemma P268000 : (Finset.range 268000).sum g = -244 := by
  rw [show (268000:ℕ) = 267000 + 1000 from rfl, Finset.sum_range_add, P267000]; decide
lemma P269000 : (Finset.range 269000).sum g = -140 := by
  rw [show (269000:ℕ) = 268000 + 1000 from rfl, Finset.sum_range_add, P268000]; decide
lemma P270000 : (Finset.range 270000).sum g = -68 := by
  rw [show (270000:ℕ) = 269000 + 1000 from rfl, Finset.sum_range_add, P269000]; decide
lemma P271000 : (Finset.range 271000).sum g = -100 := by
  rw [show (271000:ℕ) = 270000 + 1000 from rfl, Finset.sum_range_add, P270000]; decide
lemma P272000 : (Finset.range 272000).sum g = -78 := by
  rw [show (272000:ℕ) = 271000 + 1000 from rfl, Finset.sum_range_add, P271000]; decide
lemma P273000 : (Finset.range 273000).sum g = -78 := by
  rw [show (273000:ℕ) = 272000 + 1000 from rfl, Finset.sum_range_add, P272000]; decide
lemma P274000 : (Finset.range 274000).sum g = -154 := by
  rw [show (274000:ℕ) = 273000 + 1000 from rfl, Finset.sum_range_add, P273000]; decide
lemma P275000 : (Finset.range 275000).sum g = -206 := by
  rw [show (275000:ℕ) = 274000 + 1000 from rfl, Finset.sum_range_add, P274000]; decide
lemma P276000 : (Finset.range 276000).sum g = -264 := by
  rw [show (276000:ℕ) = 275000 + 1000 from rfl, Finset.sum_range_add, P275000]; decide
lemma P277000 : (Finset.range 277000).sum g = -238 := by
  rw [show (277000:ℕ) = 276000 + 1000 from rfl, Finset.sum_range_add, P276000]; decide
lemma P278000 : (Finset.range 278000).sum g = -262 := by
  rw [show (278000:ℕ) = 277000 + 1000 from rfl, Finset.sum_range_add, P277000]; decide
lemma P279000 : (Finset.range 279000).sum g = -244 := by
  rw [show (279000:ℕ) = 278000 + 1000 from rfl, Finset.sum_range_add, P278000]; decide
lemma P280000 : (Finset.range 280000).sum g = -256 := by
  rw [show (280000:ℕ) = 279000 + 1000 from rfl, Finset.sum_range_add, P279000]; decide
lemma P281000 : (Finset.range 281000).sum g = -242 := by
  rw [show (281000:ℕ) = 280000 + 1000 from rfl, Finset.sum_range_add, P280000]; decide
lemma P282000 : (Finset.range 282000).sum g = -260 := by
  rw [show (282000:ℕ) = 281000 + 1000 from rfl, Finset.sum_range_add, P281000]; decide
lemma P283000 : (Finset.range 283000).sum g = -252 := by
  rw [show (283000:ℕ) = 282000 + 1000 from rfl, Finset.sum_range_add, P282000]; decide
lemma P284000 : (Finset.range 284000).sum g = -206 := by
  rw [show (284000:ℕ) = 283000 + 1000 from rfl, Finset.sum_range_add, P283000]; decide
lemma P285000 : (Finset.range 285000).sum g = -214 := by
  rw [show (285000:ℕ) = 284000 + 1000 from rfl, Finset.sum_range_add, P284000]; decide
lemma P286000 : (Finset.range 286000).sum g = -210 := by
  rw [show (286000:ℕ) = 285000 + 1000 from rfl, Finset.sum_range_add, P285000]; decide
lemma P287000 : (Finset.range 287000).sum g = -196 := by
  rw [show (287000:ℕ) = 286000 + 1000 from rfl, Finset.sum_range_add, P286000]; decide
lemma P288000 : (Finset.range 288000).sum g = -218 := by
  rw [show (288000:ℕ) = 287000 + 1000 from rfl, Finset.sum_range_add, P287000]; decide
lemma P289000 : (Finset.range 289000).sum g = -204 := by
  rw [show (289000:ℕ) = 288000 + 1000 from rfl, Finset.sum_range_add, P288000]; decide
lemma P290000 : (Finset.range 290000).sum g = -194 := by
  rw [show (290000:ℕ) = 289000 + 1000 from rfl, Finset.sum_range_add, P289000]; decide
lemma P291000 : (Finset.range 291000).sum g = -162 := by
  rw [show (291000:ℕ) = 290000 + 1000 from rfl, Finset.sum_range_add, P290000]; decide
lemma P292000 : (Finset.range 292000).sum g = -158 := by
  rw [show (292000:ℕ) = 291000 + 1000 from rfl, Finset.sum_range_add, P291000]; decide
lemma P293000 : (Finset.range 293000).sum g = -120 := by
  rw [show (293000:ℕ) = 292000 + 1000 from rfl, Finset.sum_range_add, P292000]; decide
lemma P294000 : (Finset.range 294000).sum g = -112 := by
  rw [show (294000:ℕ) = 293000 + 1000 from rfl, Finset.sum_range_add, P293000]; decide
lemma P295000 : (Finset.range 295000).sum g = -134 := by
  rw [show (295000:ℕ) = 294000 + 1000 from rfl, Finset.sum_range_add, P294000]; decide
lemma P296000 : (Finset.range 296000).sum g = -112 := by
  rw [show (296000:ℕ) = 295000 + 1000 from rfl, Finset.sum_range_add, P295000]; decide
lemma P297000 : (Finset.range 297000).sum g = -86 := by
  rw [show (297000:ℕ) = 296000 + 1000 from rfl, Finset.sum_range_add, P296000]; decide
lemma P298000 : (Finset.range 298000).sum g = -50 := by
  rw [show (298000:ℕ) = 297000 + 1000 from rfl, Finset.sum_range_add, P297000]; decide
lemma P299000 : (Finset.range 299000).sum g = -112 := by
  rw [show (299000:ℕ) = 298000 + 1000 from rfl, Finset.sum_range_add, P298000]; decide
lemma P300000 : (Finset.range 300000).sum g = -118 := by
  rw [show (300000:ℕ) = 299000 + 1000 from rfl, Finset.sum_range_add, P299000]; decide
lemma P301000 : (Finset.range 301000).sum g = -128 := by
  rw [show (301000:ℕ) = 300000 + 1000 from rfl, Finset.sum_range_add, P300000]; decide
lemma P302000 : (Finset.range 302000).sum g = -108 := by
  rw [show (302000:ℕ) = 301000 + 1000 from rfl, Finset.sum_range_add, P301000]; decide
lemma P303000 : (Finset.range 303000).sum g = -186 := by
  rw [show (303000:ℕ) = 302000 + 1000 from rfl, Finset.sum_range_add, P302000]; decide
lemma P304000 : (Finset.range 304000).sum g = -206 := by
  rw [show (304000:ℕ) = 303000 + 1000 from rfl, Finset.sum_range_add, P303000]; decide
lemma P305000 : (Finset.range 305000).sum g = -192 := by
  rw [show (305000:ℕ) = 304000 + 1000 from rfl, Finset.sum_range_add, P304000]; decide
lemma P306000 : (Finset.range 306000).sum g = -192 := by
  rw [show (306000:ℕ) = 305000 + 1000 from rfl, Finset.sum_range_add, P305000]; decide
lemma P307000 : (Finset.range 307000).sum g = -210 := by
  rw [show (307000:ℕ) = 306000 + 1000 from rfl, Finset.sum_range_add, P306000]; decide
lemma P308000 : (Finset.range 308000).sum g = -220 := by
  rw [show (308000:ℕ) = 307000 + 1000 from rfl, Finset.sum_range_add, P307000]; decide
lemma P309000 : (Finset.range 309000).sum g = -192 := by
  rw [show (309000:ℕ) = 308000 + 1000 from rfl, Finset.sum_range_add, P308000]; decide
lemma P310000 : (Finset.range 310000).sum g = -196 := by
  rw [show (310000:ℕ) = 309000 + 1000 from rfl, Finset.sum_range_add, P309000]; decide
lemma P311000 : (Finset.range 311000).sum g = -132 := by
  rw [show (311000:ℕ) = 310000 + 1000 from rfl, Finset.sum_range_add, P310000]; decide
lemma P312000 : (Finset.range 312000).sum g = -120 := by
  rw [show (312000:ℕ) = 311000 + 1000 from rfl, Finset.sum_range_add, P311000]; decide
lemma P313000 : (Finset.range 313000).sum g = -146 := by
  rw [show (313000:ℕ) = 312000 + 1000 from rfl, Finset.sum_range_add, P312000]; decide
lemma P314000 : (Finset.range 314000).sum g = -154 := by
  rw [show (314000:ℕ) = 313000 + 1000 from rfl, Finset.sum_range_add, P313000]; decide
lemma P315000 : (Finset.range 315000).sum g = -136 := by
  rw [show (315000:ℕ) = 314000 + 1000 from rfl, Finset.sum_range_add, P314000]; decide
lemma P316000 : (Finset.range 316000).sum g = -222 := by
  rw [show (316000:ℕ) = 315000 + 1000 from rfl, Finset.sum_range_add, P315000]; decide
lemma P317000 : (Finset.range 317000).sum g = -214 := by
  rw [show (317000:ℕ) = 316000 + 1000 from rfl, Finset.sum_range_add, P316000]; decide
lemma P318000 : (Finset.range 318000).sum g = -144 := by
  rw [show (318000:ℕ) = 317000 + 1000 from rfl, Finset.sum_range_add, P317000]; decide
lemma P319000 : (Finset.range 319000).sum g = -138 := by
  rw [show (319000:ℕ) = 318000 + 1000 from rfl, Finset.sum_range_add, P318000]; decide
lemma P320000 : (Finset.range 320000).sum g = -178 := by
  rw [show (320000:ℕ) = 319000 + 1000 from rfl, Finset.sum_range_add, P319000]; decide
lemma P321000 : (Finset.range 321000).sum g = -156 := by
  rw [show (321000:ℕ) = 320000 + 1000 from rfl, Finset.sum_range_add, P320000]; decide
lemma P322000 : (Finset.range 322000).sum g = -92 := by
  rw [show (322000:ℕ) = 321000 + 1000 from rfl, Finset.sum_range_add, P321000]; decide
lemma P323000 : (Finset.range 323000).sum g = -104 := by
  rw [show (323000:ℕ) = 322000 + 1000 from rfl, Finset.sum_range_add, P322000]; decide
lemma P324000 : (Finset.range 324000).sum g = -56 := by
  rw [show (324000:ℕ) = 323000 + 1000 from rfl, Finset.sum_range_add, P323000]; decide
lemma P325000 : (Finset.range 325000).sum g = -76 := by
  rw [show (325000:ℕ) = 324000 + 1000 from rfl, Finset.sum_range_add, P324000]; decide
lemma P326000 : (Finset.range 326000).sum g = -68 := by
  rw [show (326000:ℕ) = 325000 + 1000 from rfl, Finset.sum_range_add, P325000]; decide
lemma P327000 : (Finset.range 327000).sum g = -108 := by
  rw [show (327000:ℕ) = 326000 + 1000 from rfl, Finset.sum_range_add, P326000]; decide
lemma P328000 : (Finset.range 328000).sum g = -178 := by
  rw [show (328000:ℕ) = 327000 + 1000 from rfl, Finset.sum_range_add, P327000]; decide
lemma P329000 : (Finset.range 329000).sum g = -134 := by
  rw [show (329000:ℕ) = 328000 + 1000 from rfl, Finset.sum_range_add, P328000]; decide
lemma P330000 : (Finset.range 330000).sum g = -116 := by
  rw [show (330000:ℕ) = 329000 + 1000 from rfl, Finset.sum_range_add, P329000]; decide
lemma P331000 : (Finset.range 331000).sum g = -60 := by
  rw [show (331000:ℕ) = 330000 + 1000 from rfl, Finset.sum_range_add, P330000]; decide
lemma P331523 : (Finset.range 331523).sum g = 1 := by
  rw [show (331523:ℕ) = 331000 + 523 from rfl, Finset.sum_range_add, P331000]; decide
/-- The first counterexample: `a 331523 = -1 < 0`. -/
lemma aval : a 331523 = -1 := by rw [a_eq, P331523]

/-- **Disproof of the OEIS A071532 non-negativity conjecture.** -/
theorem oeis_71532_conjecture_0.disproof : ¬ ∀ n : ℕ, a n ≥ 0 := by
  intro h
  have hx := h 331523
  rw [aval] at hx
  norm_num at hx
