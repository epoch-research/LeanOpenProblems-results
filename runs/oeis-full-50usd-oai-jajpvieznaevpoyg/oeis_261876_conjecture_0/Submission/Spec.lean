import FormalConjectures.Util.ProblemImports
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Nat Finset BigOperators

/--
A261876: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $(5x^2+7y^2+9z^2)yz$ a square, where $x,y,z,w$ are nonnegative integers with $z > 0$.
-/
def a (n : ℕ) : ℕ :=
  let is_square (k : ℕ) : Prop := IsSquare k

  -- Since $x^2 \le n$, a simple and safe iteration bound for all variables is $n+1$.
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if h_z : z > 0 then
      let k := x^2 + y^2 + z^2
      if h_le : k ≤ n then
        let r := n - k
        -- The existence of a natural number $w$ such that $w^2 = r$.
        if is_square r then
          let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
          -- The primary sequence condition: $(5x^2+7y^2+9z^2)yz$ must be a perfect square.
          if is_square condition_expr then 1 else 0
        else 0
      else 0
    else 0

/-- The set of base integers $m$ for which $a(n)=1$. -/
def special_m_set : Set ℕ :=
  {1, 7, 23, 647, 863}

/-- The summand used in `a`, separated out so that finite truncations can be proved. -/
def summand (n x y z : ℕ) : ℕ :=
  if h_z : z > 0 then
    let k := x^2 + y^2 + z^2
    if h_le : k ≤ n then
      let r := n - k
      if IsSquare r then
        let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
        if IsSquare condition_expr then 1 else 0
      else 0
    else 0
  else 0

/-- A bounded version of `a`, useful when the bound squared is bigger than `n`. -/
def aBound (n B : ℕ) : ℕ :=
  (Finset.range B).sum fun x =>
  (Finset.range B).sum fun y =>
  (Finset.range B).sum fun z => summand n x y z

lemma summand_eq_zero_of_large_x {n B x y z : ℕ} (hn : n < B^2) (hx : B ≤ x) :
    summand n x y z = 0 := by
  have hltx : n < x^2 := by nlinarith
  have hlt : n < x^2 + y^2 + z^2 := by nlinarith [Nat.zero_le (y^2 + z^2)]
  unfold summand
  by_cases hz : z > 0
  · simp [hz, not_le.mpr hlt]
  · simp [hz]

lemma summand_eq_zero_of_large_y {n B x y z : ℕ} (hn : n < B^2) (hy : B ≤ y) :
    summand n x y z = 0 := by
  have hlty : n < y^2 := by nlinarith
  have hlt : n < x^2 + y^2 + z^2 := by nlinarith [Nat.zero_le (x^2), Nat.zero_le (z^2)]
  unfold summand
  by_cases hz : z > 0
  · simp [hz, not_le.mpr hlt]
  · simp [hz]

lemma summand_eq_zero_of_large_z {n B x y z : ℕ} (hn : n < B^2) (hzB : B ≤ z) :
    summand n x y z = 0 := by
  have hltz : n < z^2 := by nlinarith
  have hlt : n < x^2 + y^2 + z^2 := by nlinarith [Nat.zero_le (x^2), Nat.zero_le (y^2)]
  unfold summand
  by_cases hz : z > 0
  · simp [hz, not_le.mpr hlt]
  · simp [hz]

lemma a_eq_aBound_of_lt_sq {n B : ℕ} (hn : n < B^2) (hB : B ≤ n + 1) :
    a n = aBound n B := by
  unfold a aBound
  change (∑ x ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1), summand n x y z) =
    ∑ x ∈ Finset.range B, ∑ y ∈ Finset.range B, ∑ z ∈ Finset.range B, summand n x y z
  rw [← Finset.sum_subset
    (by intro x hx; exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hB))
    (by
      intro x hxbig hxsmall
      simp at hxsmall
      apply Finset.sum_eq_zero
      intro y hy
      apply Finset.sum_eq_zero
      intro z hz
      exact summand_eq_zero_of_large_x hn hxsmall)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_subset
    (by intro y hy; exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hy) hB))
    (by
      intro y hybig hysmall
      simp at hysmall
      apply Finset.sum_eq_zero
      intro z hz
      exact summand_eq_zero_of_large_y hn hysmall)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.sum_subset
    (by intro z hz; exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hz) hB))
    (by
      intro z hzbig hzsmall
      simp at hzsmall
      exact summand_eq_zero_of_large_z hn hzsmall)]

def sqRes81 (r : ℕ) : Bool :=
  match r with
  | 0 => true
  | 1 => true
  | 4 => true
  | 7 => true
  | 9 => true
  | 10 => true
  | 13 => true
  | 16 => true
  | 19 => true
  | 22 => true
  | 25 => true
  | 28 => true
  | 31 => true
  | 34 => true
  | 36 => true
  | 37 => true
  | 40 => true
  | 43 => true
  | 46 => true
  | 49 => true
  | 52 => true
  | 55 => true
  | 58 => true
  | 61 => true
  | 63 => true
  | 64 => true
  | 67 => true
  | 70 => true
  | 73 => true
  | 76 => true
  | 79 => true
  | _ => false

def good81 (x y z : ℕ) : Bool :=
  sqRes81 ((69383 - (x*x + y*y + z*z)) % 81) &&
  sqRes81 ((((5*x*x + 7*y*y + 9*z*z) * y * z) % 81) % 81)

def sqRes16 (r : ℕ) : Bool :=
  match r with
  | 0 => true
  | 1 => true
  | 4 => true
  | 9 => true
  | _ => false

def good16 (x y z : ℕ) : Bool :=
  sqRes16 ((69383 - (x*x + y*y + z*z)) % 16) &&
  sqRes16 ((((5*x*x + 7*y*y + 9*z*z) * y * z) % 16) % 16)

def sqRes49 (r : ℕ) : Bool :=
  match r with
  | 0 => true
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | 9 => true
  | 11 => true
  | 15 => true
  | 16 => true
  | 18 => true
  | 22 => true
  | 23 => true
  | 25 => true
  | 29 => true
  | 30 => true
  | 32 => true
  | 36 => true
  | 37 => true
  | 39 => true
  | 43 => true
  | 44 => true
  | 46 => true
  | _ => false

def good49 (x y z : ℕ) : Bool :=
  sqRes49 ((69383 - (x*x + y*y + z*z)) % 49) &&
  sqRes49 ((((5*x*x + 7*y*y + 9*z*z) * y * z) % 49) % 49)

def sqRes121 (r : ℕ) : Bool :=
  match r with
  | 0 => true
  | 1 => true
  | 3 => true
  | 4 => true
  | 5 => true
  | 9 => true
  | 12 => true
  | 14 => true
  | 15 => true
  | 16 => true
  | 20 => true
  | 23 => true
  | 25 => true
  | 26 => true
  | 27 => true
  | 31 => true
  | 34 => true
  | 36 => true
  | 37 => true
  | 38 => true
  | 42 => true
  | 45 => true
  | 47 => true
  | 48 => true
  | 49 => true
  | 53 => true
  | 56 => true
  | 58 => true
  | 59 => true
  | 60 => true
  | 64 => true
  | 67 => true
  | 69 => true
  | 70 => true
  | 71 => true
  | 75 => true
  | 78 => true
  | 80 => true
  | 81 => true
  | 82 => true
  | 86 => true
  | 89 => true
  | 91 => true
  | 92 => true
  | 93 => true
  | 97 => true
  | 100 => true
  | 102 => true
  | 103 => true
  | 104 => true
  | 108 => true
  | 111 => true
  | 113 => true
  | 114 => true
  | 115 => true
  | 119 => true
  | _ => false

def good121 (x y z : ℕ) : Bool :=
  sqRes121 ((69383 - (x*x + y*y + z*z)) % 121) &&
  sqRes121 ((((5*x*x + 7*y*y + 9*z*z) * y * z) % 121) % 121)

def sqRes71 (r : ℕ) : Bool :=
  match r with
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | 8 => true
  | 9 => true
  | 10 => true
  | 12 => true
  | 15 => true
  | 16 => true
  | 18 => true
  | 19 => true
  | 20 => true
  | 24 => true
  | 25 => true
  | 27 => true
  | 29 => true
  | 30 => true
  | 32 => true
  | 36 => true
  | 37 => true
  | 38 => true
  | 40 => true
  | 43 => true
  | 45 => true
  | 48 => true
  | 49 => true
  | 50 => true
  | 54 => true
  | 57 => true
  | 58 => true
  | 60 => true
  | 64 => true
  | _ => false

def good71 (x y z : ℕ) : Bool :=
  sqRes71 ((69383 - (x*x + y*y + z*z)) % 71) &&
  sqRes71 ((((5*x*x + 7*y*y + 9*z*z) * y * z) % 71) % 71)

def sqRes73 (r : ℕ) : Bool :=
  match r with
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 6 => true
  | 8 => true
  | 9 => true
  | 12 => true
  | 16 => true
  | 18 => true
  | 19 => true
  | 23 => true
  | 24 => true
  | 25 => true
  | 27 => true
  | 32 => true
  | 35 => true
  | 36 => true
  | 37 => true
  | 38 => true
  | 41 => true
  | 46 => true
  | 48 => true
  | 49 => true
  | 50 => true
  | 54 => true
  | 55 => true
  | 57 => true
  | 61 => true
  | 64 => true
  | 65 => true
  | 67 => true
  | 69 => true
  | 70 => true
  | 71 => true
  | 72 => true
  | _ => false

def good73 (x y z : ℕ) : Bool :=
  sqRes73 ((69383 - (x*x + y*y + z*z)) % 73) &&
  sqRes73 ((((5*x*x + 7*y*y + 9*z*z) * y * z) % 73) % 73)

def sqRes47 (r : ℕ) : Bool :=
  match r with
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 6 => true
  | 7 => true
  | 8 => true
  | 9 => true
  | 12 => true
  | 14 => true
  | 16 => true
  | 17 => true
  | 18 => true
  | 21 => true
  | 24 => true
  | 25 => true
  | 27 => true
  | 28 => true
  | 32 => true
  | 34 => true
  | 36 => true
  | 37 => true
  | 42 => true
  | _ => false

def good47 (x y z : ℕ) : Bool :=
  sqRes47 ((69383 - (x*x + y*y + z*z)) % 47) &&
  sqRes47 ((((5*x*x + 7*y*y + 9*z*z) * y * z) % 47) % 47)

def sqRes41 (r : ℕ) : Bool :=
  match r with
  | 0 => true
  | 1 => true
  | 2 => true
  | 4 => true
  | 5 => true
  | 8 => true
  | 9 => true
  | 10 => true
  | 16 => true
  | 18 => true
  | 20 => true
  | 21 => true
  | 23 => true
  | 25 => true
  | 31 => true
  | 32 => true
  | 33 => true
  | 36 => true
  | 37 => true
  | 39 => true
  | 40 => true
  | _ => false

def good41 (x y z : ℕ) : Bool :=
  sqRes41 ((69383 - (x*x + y*y + z*z)) % 41) &&
  sqRes41 ((((5*x*x + 7*y*y + 9*z*z) * y * z) % 41) % 41)

def filters (x y z : ℕ) : Bool :=
  ((((((((true && good81 x y z) && good16 x y z) && good49 x y z) && good121 x y z) && good71 x y z) && good73 x y z) && good47 x y z) && good41 x y z)

def inCands (x y z : ℕ) : Bool :=
  (x==3 && y==27 && z==143) || ((x==11 && y==21 && z==186) || ((x==14 && y==61 && z==255) || ((x==15 && y==117 && z==170) || ((x==17 && y==73 && z==246) || ((x==19 && y==15 && z==246) || ((x==19 && y==261 && z==1) || ((x==21 && y==27 && z==118) || ((x==21 && y==31 && z==115) || ((x==21 && y==65 && z==221) || ((x==21 && y==171 && z==199) || ((x==31 && y==189 && z==150) || ((x==39 && y==43 && z==90) || ((x==39 && y==98 && z==233) || ((x==42 && y==173 && z==167) || ((x==42 && y==225 && z==65) || ((x==43 && y==31 && z==258) || ((x==43 && y==203 && z==162) || ((x==43 && y==239 && z==102) || ((x==45 && y==189 && z==94) || ((x==47 && y==30 && z==15) || ((x==54 && y==233 && z==107) || ((x==57 && y==31 && z==178) || ((x==57 && y==54 && z==247) || ((x==57 && y==226 && z==117) || ((x==59 && y==38 && z==147) || ((x==59 && y==81 && z==146) || ((x==73 && y==27 && z==246) || ((x==73 && y==213 && z==102) || ((x==74 && y==203 && z==147) || ((x==78 && y==243 && z==43) || ((x==83 && y==129 && z==213) || ((x==91 && y==37 && z==162) || ((x==94 && y==189 && z==45) || ((x==98 && y==135 && z==141) || ((x==98 && y==141 && z==135) || ((x==99 && y==225 && z==26) || ((x==101 && y==203 && z==102) || ((x==102 && y==81 && z==41) || ((x==105 && y==65 && z==162) || ((x==105 && y==142 && z==63) || ((x==106 && y==189 && z==15) || ((x==113 && y==57 && z==186) || ((x==119 && y==41 && z==54) || ((x==122 && y==195 && z==57) || ((x==123 && y==119 && z==158) || ((x==123 && y==189 && z==25) || ((x==123 && y==218 && z==81) || ((x==125 && y==135 && z==147) || ((x==125 && y==201 && z==114) || ((x==126 && y==103 && z==7) || ((x==129 && y==45 && z==50) || ((x==130 && y==119 && z==189) || ((x==145 && y==54 && z==27) || ((x==147 && y==47 && z==203) || ((x==147 && y==73 && z==82) || ((x==151 && y==27 && z==78) || ((x==154 && y==135 && z==39) || ((x==157 && y==38 && z==99) || ((x==162 && y==23 && z==47) || ((x==174 && y==191 && z==5) || ((x==177 && y==71 && z==98) || ((x==178 && y==185 && z==57) || ((x==183 && y==53 && z==18) || ((x==187 && y==147 && z==6) || ((x==189 && y==45 && z==89) || ((x==194 && y==97 && z==27) || ((x==197 && y==75 && z==135) || ((x==197 && y==123 && z==39) || ((x==207 && y==17 && z==162) || ((x==210 && y==99 && z==121) || ((x==243 && y==19 && z==82) || ((x==249 && y==74 && z==41)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


set_option maxHeartbeats 0
set_option maxRecDepth 1000000
opaque sqRes16_sq_fin : ∀ r : Fin 16, sqRes16 ((r.val * r.val) % 16) = true := by decide +kernel
lemma sqRes16_sq (t : ℕ) : sqRes16 ((t*t) % 16) = true := by
  simpa [Nat.mul_mod] using sqRes16_sq_fin ⟨t % 16, Nat.mod_lt _ (by norm_num)⟩
opaque sqRes41_sq_fin : ∀ r : Fin 41, sqRes41 ((r.val * r.val) % 41) = true := by decide +kernel
lemma sqRes41_sq (t : ℕ) : sqRes41 ((t*t) % 41) = true := by
  simpa [Nat.mul_mod] using sqRes41_sq_fin ⟨t % 41, Nat.mod_lt _ (by norm_num)⟩
opaque sqRes47_sq_fin : ∀ r : Fin 47, sqRes47 ((r.val * r.val) % 47) = true := by decide +kernel
lemma sqRes47_sq (t : ℕ) : sqRes47 ((t*t) % 47) = true := by
  simpa [Nat.mul_mod] using sqRes47_sq_fin ⟨t % 47, Nat.mod_lt _ (by norm_num)⟩
opaque sqRes49_sq_fin : ∀ r : Fin 49, sqRes49 ((r.val * r.val) % 49) = true := by decide +kernel
lemma sqRes49_sq (t : ℕ) : sqRes49 ((t*t) % 49) = true := by
  simpa [Nat.mul_mod] using sqRes49_sq_fin ⟨t % 49, Nat.mod_lt _ (by norm_num)⟩
opaque sqRes71_sq_fin : ∀ r : Fin 71, sqRes71 ((r.val * r.val) % 71) = true := by decide +kernel
lemma sqRes71_sq (t : ℕ) : sqRes71 ((t*t) % 71) = true := by
  simpa [Nat.mul_mod] using sqRes71_sq_fin ⟨t % 71, Nat.mod_lt _ (by norm_num)⟩
opaque sqRes73_sq_fin : ∀ r : Fin 73, sqRes73 ((r.val * r.val) % 73) = true := by decide +kernel
lemma sqRes73_sq (t : ℕ) : sqRes73 ((t*t) % 73) = true := by
  simpa [Nat.mul_mod] using sqRes73_sq_fin ⟨t % 73, Nat.mod_lt _ (by norm_num)⟩
opaque sqRes81_sq_fin : ∀ r : Fin 81, sqRes81 ((r.val * r.val) % 81) = true := by decide +kernel
lemma sqRes81_sq (t : ℕ) : sqRes81 ((t*t) % 81) = true := by
  simpa [Nat.mul_mod] using sqRes81_sq_fin ⟨t % 81, Nat.mod_lt _ (by norm_num)⟩
opaque sqRes121_sq_fin : ∀ r : Fin 121, sqRes121 ((r.val * r.val) % 121) = true := by decide +kernel
lemma sqRes121_sq (t : ℕ) : sqRes121 ((t*t) % 121) = true := by
  simpa [Nat.mul_mod] using sqRes121_sq_fin ⟨t % 121, Nat.mod_lt _ (by norm_num)⟩
lemma filters_of_summand_one {x y z : ℕ} (h : summand 69383 x y z = 1) :
    filters x y z = true := by
  unfold summand at h
  by_cases hz : z > 0
  · simp [hz] at h
    by_cases hk : x ^ 2 + y ^ 2 + z ^ 2 ≤ 69383
    · simp [hk] at h
      by_cases hr : IsSquare (69383 - (x ^ 2 + y ^ 2 + z ^ 2))
      · simp [hr] at h
        by_cases hc : IsSquare ((5 * x ^ 2 + 7 * y ^ 2 + 9 * z ^ 2) * y * z)
        · rcases hr with ⟨w, hw⟩
          rcases hc with ⟨q, hq⟩
          simp only [filters, good81, good16, good49, good121, good71, good73, good47, good41, pow_two] at hw hq ⊢
          have hqe : (5 * x * x + 7 * y * y + 9 * z * z) * y * z = q * q := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hq
          rw [hw, hqe]
          simp [sqRes16_sq, sqRes41_sq, sqRes47_sq, sqRes49_sq, sqRes71_sq, sqRes73_sq, sqRes81_sq, sqRes121_sq, Nat.mod_mod]
        · simp [hc] at h
      · simp [hr] at h
    · simp [hk] at h
  · simp [hz] at h

lemma summand_one_z_pos {x y z : ℕ} (h : summand 69383 x y z = 1) : z > 0 := by
  unfold summand at h
  by_cases hz : z > 0
  · exact hz
  · simp [hz] at h

lemma summand_one_k_le {x y z : ℕ} (h : summand 69383 x y z = 1) :
    x^2 + y^2 + z^2 ≤ 69383 := by
  unfold summand at h
  by_cases hz : z > 0
  · simp [hz] at h
    by_cases hk : x^2 + y^2 + z^2 ≤ 69383
    · exact hk
    · simp [hk] at h
  · simp [hz] at h

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
opaque filt_all : ∀ x y z : Fin 264, z.val > 0 → x.val^2 + y.val^2 + z.val^2 ≤ 69383 → filters x.val y.val z.val = true → inCands x.val y.val z.val = true := by decide +kernel

lemma inCands_of_filters {x y z : ℕ} (hx : x < 264) (hy : y < 264) (hzlt : z < 264)
    (hzpos : z > 0) (hk : x^2 + y^2 + z^2 ≤ 69383) (hf : filters x y z = true) :
    inCands x y z = true := by
  exact filt_all ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hzlt⟩ hzpos hk hf

lemma inCands_true_iff {x y z : ℕ} (h : inCands x y z = true) :
    ((x = 3 ∧ y = 27) ∧ z = 143) ∨
    ((x = 11 ∧ y = 21) ∧ z = 186) ∨
    ((x = 14 ∧ y = 61) ∧ z = 255) ∨
    ((x = 15 ∧ y = 117) ∧ z = 170) ∨
    ((x = 17 ∧ y = 73) ∧ z = 246) ∨
    ((x = 19 ∧ y = 15) ∧ z = 246) ∨
    ((x = 19 ∧ y = 261) ∧ z = 1) ∨
    ((x = 21 ∧ y = 27) ∧ z = 118) ∨
    ((x = 21 ∧ y = 31) ∧ z = 115) ∨
    ((x = 21 ∧ y = 65) ∧ z = 221) ∨
    ((x = 21 ∧ y = 171) ∧ z = 199) ∨
    ((x = 31 ∧ y = 189) ∧ z = 150) ∨
    ((x = 39 ∧ y = 43) ∧ z = 90) ∨
    ((x = 39 ∧ y = 98) ∧ z = 233) ∨
    ((x = 42 ∧ y = 173) ∧ z = 167) ∨
    ((x = 42 ∧ y = 225) ∧ z = 65) ∨
    ((x = 43 ∧ y = 31) ∧ z = 258) ∨
    ((x = 43 ∧ y = 203) ∧ z = 162) ∨
    ((x = 43 ∧ y = 239) ∧ z = 102) ∨
    ((x = 45 ∧ y = 189) ∧ z = 94) ∨
    ((x = 47 ∧ y = 30) ∧ z = 15) ∨
    ((x = 54 ∧ y = 233) ∧ z = 107) ∨
    ((x = 57 ∧ y = 31) ∧ z = 178) ∨
    ((x = 57 ∧ y = 54) ∧ z = 247) ∨
    ((x = 57 ∧ y = 226) ∧ z = 117) ∨
    ((x = 59 ∧ y = 38) ∧ z = 147) ∨
    ((x = 59 ∧ y = 81) ∧ z = 146) ∨
    ((x = 73 ∧ y = 27) ∧ z = 246) ∨
    ((x = 73 ∧ y = 213) ∧ z = 102) ∨
    ((x = 74 ∧ y = 203) ∧ z = 147) ∨
    ((x = 78 ∧ y = 243) ∧ z = 43) ∨
    ((x = 83 ∧ y = 129) ∧ z = 213) ∨
    ((x = 91 ∧ y = 37) ∧ z = 162) ∨
    ((x = 94 ∧ y = 189) ∧ z = 45) ∨
    ((x = 98 ∧ y = 135) ∧ z = 141) ∨
    ((x = 98 ∧ y = 141) ∧ z = 135) ∨
    ((x = 99 ∧ y = 225) ∧ z = 26) ∨
    ((x = 101 ∧ y = 203) ∧ z = 102) ∨
    ((x = 102 ∧ y = 81) ∧ z = 41) ∨
    ((x = 105 ∧ y = 65) ∧ z = 162) ∨
    ((x = 105 ∧ y = 142) ∧ z = 63) ∨
    ((x = 106 ∧ y = 189) ∧ z = 15) ∨
    ((x = 113 ∧ y = 57) ∧ z = 186) ∨
    ((x = 119 ∧ y = 41) ∧ z = 54) ∨
    ((x = 122 ∧ y = 195) ∧ z = 57) ∨
    ((x = 123 ∧ y = 119) ∧ z = 158) ∨
    ((x = 123 ∧ y = 189) ∧ z = 25) ∨
    ((x = 123 ∧ y = 218) ∧ z = 81) ∨
    ((x = 125 ∧ y = 135) ∧ z = 147) ∨
    ((x = 125 ∧ y = 201) ∧ z = 114) ∨
    ((x = 126 ∧ y = 103) ∧ z = 7) ∨
    ((x = 129 ∧ y = 45) ∧ z = 50) ∨
    ((x = 130 ∧ y = 119) ∧ z = 189) ∨
    ((x = 145 ∧ y = 54) ∧ z = 27) ∨
    ((x = 147 ∧ y = 47) ∧ z = 203) ∨
    ((x = 147 ∧ y = 73) ∧ z = 82) ∨
    ((x = 151 ∧ y = 27) ∧ z = 78) ∨
    ((x = 154 ∧ y = 135) ∧ z = 39) ∨
    ((x = 157 ∧ y = 38) ∧ z = 99) ∨
    ((x = 162 ∧ y = 23) ∧ z = 47) ∨
    ((x = 174 ∧ y = 191) ∧ z = 5) ∨
    ((x = 177 ∧ y = 71) ∧ z = 98) ∨
    ((x = 178 ∧ y = 185) ∧ z = 57) ∨
    ((x = 183 ∧ y = 53) ∧ z = 18) ∨
    ((x = 187 ∧ y = 147) ∧ z = 6) ∨
    ((x = 189 ∧ y = 45) ∧ z = 89) ∨
    ((x = 194 ∧ y = 97) ∧ z = 27) ∨
    ((x = 197 ∧ y = 75) ∧ z = 135) ∨
    ((x = 197 ∧ y = 123) ∧ z = 39) ∨
    ((x = 207 ∧ y = 17) ∧ z = 162) ∨
    ((x = 210 ∧ y = 99) ∧ z = 121) ∨
    ((x = 243 ∧ y = 19) ∧ z = 82) ∨
    ((x = 249 ∧ y = 74) ∧ z = 41) := by
  simpa [inCands, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] using h

lemma summand_le_one (n x y z : ℕ) : summand n x y z ≤ 1 := by
  unfold summand
  by_cases hz : z > 0
  · simp [hz]
    by_cases hk : x ^ 2 + y ^ 2 + z ^ 2 ≤ n
    · simp [hk]
      by_cases hr : IsSquare (n - (x ^ 2 + y ^ 2 + z ^ 2))
      · simp [hr]
        by_cases hc : IsSquare ((5 * x ^ 2 + 7 * y ^ 2 + 9 * z ^ 2) * y * z)
        · simp [hc]
        · simp [hc]
      · simp [hr]
    · simp [hk]
  · simp [hz]

lemma summand_one_witness {x y z : ℕ} (hx : x < 264) (hy : y < 264) (hzlt : z < 264)
    (h : summand 69383 x y z = 1) : x = 187 ∧ y = 147 ∧ z = 6 := by
  have hzpos := summand_one_z_pos h
  have hk := summand_one_k_le h
  have hf := filters_of_summand_one h
  have hc := inCands_of_filters hx hy hzlt hzpos hk hf
  rcases inCands_true_iff hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72
  · rcases h0 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h1 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h2 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h3 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h4 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h5 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h6 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h7 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h8 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h9 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h10 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h11 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h12 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h13 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h14 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h15 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h16 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h17 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h18 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h19 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h20 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h21 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h22 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h23 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h24 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h25 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h26 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h27 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h28 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h29 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h30 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h31 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h32 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h33 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h34 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h35 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h36 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h37 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h38 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h39 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h40 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h41 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h42 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h43 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h44 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h45 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h46 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h47 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h48 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h49 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h50 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h51 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h52 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h53 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h54 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h55 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h56 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h57 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h58 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h59 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h60 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h61 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h62 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h63 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h64 with ⟨⟨hx, hy⟩, hz⟩; exact ⟨hx, hy, hz⟩
  · rcases h65 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h66 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h67 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h68 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h69 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h70 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h71 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h
  · rcases h72 with ⟨⟨rfl, rfl⟩, rfl⟩; norm_num [summand] at h


lemma summand_eq_indicator {x y z : ℕ} (hx : x < 264) (hy : y < 264) (hzlt : z < 264) :
    summand 69383 x y z = if x = 187 ∧ y = 147 ∧ z = 6 then 1 else 0 := by
  by_cases hw : x = 187 ∧ y = 147 ∧ z = 6
  · rcases hw with ⟨rfl, rfl, rfl⟩
    norm_num [summand]
  · have hle := summand_le_one 69383 x y z
    by_cases h1 : summand 69383 x y z = 1
    · exact False.elim (hw (summand_one_witness hx hy hzlt h1))
    · have : summand 69383 x y z = 0 := by omega
      simp [hw, this]

lemma sum_indicator_eq_one :
    (∑ x ∈ Finset.range 264, ∑ y ∈ Finset.range 264, ∑ z ∈ Finset.range 264,
      (if x = 187 ∧ y = 147 ∧ z = 6 then 1 else 0 : ℕ)) = 1 := by
  rw [Finset.sum_eq_single 187]
  · rw [Finset.sum_eq_single 147]
    · rw [Finset.sum_eq_single 6]
      · simp
      · intro b hb hbne; simp [hbne]
      · simp
    · intro b hb hbne
      apply Finset.sum_eq_zero
      intro z hz; simp [hbne]
    · simp
  · intro b hb hbne
    apply Finset.sum_eq_zero
    intro y hy
    apply Finset.sum_eq_zero
    intro z hz; simp [hbne]
  · simp

lemma aBound_69383_eq_one : aBound 69383 264 = 1 := by
  unfold aBound
  trans (∑ x ∈ Finset.range 264, ∑ y ∈ Finset.range 264, ∑ z ∈ Finset.range 264,
      (if x = 187 ∧ y = 147 ∧ z = 6 then 1 else 0 : ℕ))
  · apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    exact summand_eq_indicator (Finset.mem_range.mp hx) (Finset.mem_range.mp hy) (Finset.mem_range.mp hz)
  · exact sum_indicator_eq_one

lemma a_69383_eq_one : a 69383 = 1 := by
  rw [a_eq_aBound_of_lt_sq (n:=69383) (B:=264) (by norm_num) (by norm_num)]
  exact aBound_69383_eq_one
lemma not_rhs_69383 : ¬ (∃ k m : ℕ, special_m_set m ∧ 69383 = 4^k * m) := by
  rintro ⟨k, m, hm, hnm⟩
  cases k with
  | zero =>
      simp [special_m_set] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> norm_num at hnm
  | succ k =>
      have hdiv : 4 ∣ 69383 := by
        rw [hnm]
        use 4^k * m
        rw [_root_.pow_succ']
        ring
      norm_num at hdiv

/--
The formalized A261876 conjecture is false: `a 69383 = 1`, but `69383` is not a power of
`4` times one of the five listed base integers.
-/
theorem oeis_261876_conjecture_0.disproof :
  ¬ (∀ n : ℕ,
  (n > 0 → a n > 0) ∧
  (a n = 1 ↔ ∃ k m : ℕ, special_m_set m ∧ n = 4^k * m)) :=
by
  intro h
  exact not_rhs_69383 ((h 69383).2.mp a_69383_eq_one)
