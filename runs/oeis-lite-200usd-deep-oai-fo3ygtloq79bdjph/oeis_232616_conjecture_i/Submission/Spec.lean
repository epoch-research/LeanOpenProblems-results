import FormalConjectures.Util.ProblemImports

open Finset ZMod Nat Set Classical

/--
The predicate that $\{2^k - k: k = 1,\dots,m\}$ contains a complete system of residues modulo $n$.
This is equivalent to the image of $k \mapsto 2^k - k \pmod n$ for $k \in \{1, \dots, m\}$ being the entire $\mathbb{Z}_n$.
-/
def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

/--
A232616: Least positive integer $m$ such that $\{2^k - k: k = 1,\dots,m\}$
contains a complete system of residues modulo $n$.
-/
noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- Since n is non-zero, the NeZero n instance is available for ZMod n operations.
    have hn : NeZero n := NeZero.mk h

    -- The set $S$ of all $m$ which satisfy the complete residue system condition.
    -- The set $S$ is non-empty based on the external theorem $a(n) \le n^2$.
    let S : Set ℕ := { m : ℕ | A232616_prop n m }

    -- The least element of a non-empty set of natural numbers is its infimum, sInf.
    sInf S


set_option linter.all false
set_option maxHeartbeats 0

lemma A232616_prop_mono {n m M : Nat} [NeZero n] (hmM : m ≤ M)
    (h : A232616_prop n m) : A232616_prop n M := by
  apply Finset.ext
  intro x
  constructor
  · intro _hx
    have hxsmall : x ∈ (Finset.Icc 1 m).image (fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)) := by
      rw [← h]
      simp
    rw [Finset.mem_image] at hxsmall ⊢
    rcases hxsmall with ⟨k, hk, hkx⟩
    refine ⟨k, ?_, hkx⟩
    rw [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, le_trans hk.2 hmM⟩
  · intro _hx
    simp

def pAfter (n p : Nat) : Nat → Nat
  | 0 => p
  | t + 1 => (2 * pAfter n p t) % n

lemma self_le_two_pow (k : Nat) : k ≤ 2 ^ k :=
  (Nat.lt_two_pow_self (n := k)).le


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

axiom nth_prime_bound : Nat.nth Nat.Prime 550171 ≤ 8165753

set_option exponentiation.threshold 600
set_option linter.all false
def aForIdx : Nat -> Nat
| 0 => 36
| 1 => 148
| 2 => 28
| 3 => 8
| 4 => 308
| 5 => 20
| 6 => 136
| 7 => 16
| 8 => 332
| 9 => 44
| 10 => 244
| 11 => 56
| 12 => 4
| 13 => 68
| 14 => 120
| 15 => 80
| 16 => 48
| 17 => 12
| 18 => 392
| 19 => 104
| 20 => 220
| 21 => 100
| 22 => 416
| 23 => 128
| 24 => 328
| 25 => 140
| 26 => 88
| 27 => 152
| 28 => 204
| 29 => 164
| 30 => 132
| 31 => 76
| 32 => 60
| 33 => 24
| 34 => 304
| 35 => 184
| 36 => 64
| 37 => 212
| 38 => 412
| 39 => 224
| 40 => 172
| 41 => 52
| 42 => 288
| 43 => 248
| 44 => 216
| 45 => 160
| 46 => 40
| 47 => 108
| 48 => 72
| 49 => 183
| 50 => 143
| 51 => 111
| 52 => 55
| 53 => 39
| 54 => 3
| 55 => 283
| 56 => 163
| 57 => 43
| 58 => 191
| 59 => 391
| 60 => 203
| 61 => 151
| 62 => 31
| 63 => 267
| 64 => 227
| 65 => 195
| 66 => 139
| 67 => 19
| 68 => 87
| 69 => 51
| 70 => 15
| 71 => 127
| 72 => 7
| 73 => 475
| 74 => 287
| 75 => 235
| 76 => 115
| 77 => 11
| 78 => 311
| 79 => 23
| 80 => 223
| 81 => 35
| 82 => 171
| 83 => 47
| 84 => 99
| 85 => 59
| 86 => 27
| 87 => 71
| 88 => 371
| 89 => 83
| 90 => 199
| 91 => 79
| 92 => 395
| 93 => 107
| 94 => 307
| 95 => 119
| 96 => 67
| 97 => 131
| 98 => 330
| 99 => 290
| 100 => 2
| 101 => 202
| 102 => 14
| 103 => 150
| 104 => 26
| 105 => 78
| 106 => 38
| 107 => 6
| 108 => 50
| 109 => 350
| 110 => 62
| 111 => 178
| 112 => 58
| 113 => 374
| 114 => 86
| 115 => 286
| 116 => 98
| 117 => 46
| 118 => 110
| 119 => 162
| 120 => 122
| 121 => 90
| 122 => 34
| 123 => 18
| 124 => 146
| 125 => 262
| 126 => 142
| 127 => 22
| 128 => 170
| 129 => 370
| 130 => 182
| 131 => 130
| 132 => 10
| 133 => 246
| 134 => 206
| 135 => 174
| 136 => 118
| 137 => 102
| 138 => 66
| 139 => 30
| 140 => 226
| 141 => 106
| 142 => 254
| 143 => 454
| 144 => 266
| 145 => 214
| 146 => 94
| 147 => 121
| 148 => 437
| 149 => 149
| 150 => 349
| 151 => 161
| 152 => 109
| 153 => 173
| 154 => 225
| 155 => 185
| 156 => 153
| 157 => 97
| 158 => 81
| 159 => 45
| 160 => 9
| 161 => 205
| 162 => 85
| 163 => 233
| 164 => 433
| 165 => 245
| 166 => 193
| 167 => 73
| 168 => 309
| 169 => 269
| 170 => 237
| 171 => 181
| 172 => 61
| 173 => 129
| 174 => 5
| 175 => 57
| 176 => 17
| 177 => 49
| 178 => 29
| 179 => 329
| 180 => 41
| 181 => 157
| 182 => 37
| 183 => 353
| 184 => 65
| 185 => 265
| 186 => 77
| 187 => 25
| 188 => 89
| 189 => 141
| 190 => 101
| 191 => 69
| 192 => 13
| 193 => 413
| 194 => 125
| 195 => 241
| _ => 2
def pForIdx : Nat -> Nat
| 0 => 105533
| 1 => 30872
| 2 => 89063
| 3 => 256
| 4 => 29418
| 5 => 85775
| 6 => 11559
| 7 => 65536
| 8 => 128867
| 9 => 58020
| 10 => 119373
| 11 => 113159
| 12 => 16
| 13 => 116897
| 14 => 104700
| 15 => 22929
| 16 => 103062
| 17 => 4096
| 18 => 93657
| 19 => 121888
| 20 => 130286
| 21 => 7618
| 22 => 108042
| 23 => 119858
| 24 => 102615
| 25 => 47401
| 26 => 93018
| 27 => 81323
| 28 => 127534
| 29 => 107405
| 30 => 129669
| 31 => 78801
| 32 => 22485
| 33 => 134513
| 34 => 87803
| 35 => 33735
| 36 => 84674
| 37 => 51013
| 38 => 92717
| 39 => 21431
| 40 => 124623
| 41 => 136019
| 42 => 43695
| 43 => 121909
| 44 => 128493
| 45 => 49695
| 46 => 38012
| 47 => 24606
| 48 => 82293
| 49 => 85639
| 50 => 104122
| 51 => 59305
| 52 => 125351
| 53 => 19006
| 54 => 8
| 55 => 31453
| 56 => 122474
| 57 => 29010
| 58 => 54247
| 59 => 115600
| 60 => 63767
| 61 => 109433
| 62 => 24789
| 63 => 18950
| 64 => 33905
| 65 => 42694
| 66 => 92472
| 67 => 111659
| 68 => 46509
| 69 => 136781
| 70 => 32768
| 71 => 59929
| 72 => 128
| 73 => 19952
| 74 => 90619
| 75 => 14471
| 76 => 123622
| 77 => 2048
| 78 => 97801
| 79 => 136028
| 80 => 79487
| 81 => 121538
| 82 => 131083
| 83 => 51531
| 84 => 3809
| 85 => 80014
| 86 => 113303
| 87 => 109918
| 88 => 18001
| 89 => 45889
| 90 => 132932
| 91 => 80236
| 92 => 61541
| 93 => 12303
| 94 => 14709
| 95 => 52350
| 96 => 127220
| 97 => 133606
| 98 => 135374
| 99 => 37237
| 100 => 4
| 101 => 100655
| 102 => 16384
| 103 => 123488
| 104 => 125423
| 105 => 40118
| 106 => 9503
| 107 => 64
| 108 => 137162
| 109 => 49704
| 110 => 89940
| 111 => 135921
| 112 => 40007
| 113 => 6465
| 114 => 92026
| 115 => 114081
| 116 => 70676
| 117 => 94537
| 118 => 98424
| 119 => 61237
| 120 => 6171
| 121 => 96986
| 122 => 60769
| 123 => 124601
| 124 => 7718
| 125 => 95153
| 126 => 52061
| 127 => 68014
| 128 => 134313
| 129 => 77772
| 130 => 111591
| 131 => 66803
| 132 => 1024
| 133 => 64863
| 134 => 97507
| 135 => 85863
| 136 => 26175
| 137 => 30472
| 138 => 63610
| 139 => 81166
| 140 => 85724
| 141 => 74923
| 142 => 99768
| 143 => 102174
| 144 => 9475
| 145 => 66509
| 146 => 38803
| 147 => 71857
| 148 => 135678
| 149 => 61744
| 150 => 24852
| 151 => 99390
| 152 => 49212
| 153 => 111703
| 154 => 42862
| 155 => 67470
| 156 => 25103
| 157 => 35338
| 158 => 45858
| 159 => 116040
| 160 => 512
| 161 => 117525
| 162 => 46013
| 163 => 106775
| 164 => 128830
| 165 => 101203
| 166 => 79445
| 167 => 27043
| 168 => 58836
| 169 => 75800
| 170 => 57884
| 171 => 124567
| 172 => 44970
| 173 => 102173
| 174 => 32
| 175 => 88775
| 176 => 131072
| 177 => 68581
| 178 => 40583
| 179 => 67687
| 180 => 76024
| 181 => 126562
| 182 => 73523
| 183 => 122546
| 184 => 31805
| 185 => 73509
| 186 => 20059
| 187 => 131483
| 188 => 48493
| 189 => 94802
| 190 => 15236
| 191 => 96251
| 192 => 8192
| 193 => 47891
| 194 => 49368
| 195 => 100886
| _ => 4
def idx (target:Nat) := (target%4)*49 + target%49
def aFor target := aForIdx (idx target)
def pFor target := pForIdx (idx target)
def powModFast (a m e : Nat) : Nat :=
  Nat.binaryRec (1 % m) (fun b _ r => let s := (r*r)%m; if b then (a*s)%m else s) e
lemma table_spec (target : Nat) :
  2 ≤ aFor target ∧ aFor target ≤ 588 ∧ (aFor target + target) % 4 = 0 ∧ ((powModFast 2 49 (aFor target) + 49 - (aFor target % 49)) % 49 = target % 49) ∧ pFor target = 2 ^ (aFor target) % 137543 := by
  unfold aFor pFor idx
  let r4 := target % 4
  let r49 := target % 49
  have hr4 : r4 < 4 := by exact Nat.mod_lt _ (by norm_num)
  have hr49 : r49 < 49 := by exact Nat.mod_lt _ (by norm_num)
  interval_cases h4 : r4 <;> interval_cases h49 : r49
  all_goals
    have ht4 : target % 4 = r4 := by rfl
    have ht49 : target % 49 = r49 := by rfl
    simp [aForIdx, pForIdx, h4, h49, ht4, ht49, powModFast, Nat.binaryRec, Nat.add_mod]

open Nat Finset ZMod Set Classical

set_option maxHeartbeats 0
set_option exponentiation.threshold 600
set_option linter.all false

def q := 137543

def covDiff target := (((pFor target + 137543 - (aFor target % 137543)) + 137543 - (target % 137543)) % 137543)
def covT target := ((covDiff target / 49 * 2138) % 2807)
def covK target := aFor target + covT target * 29400

lemma pFor_mod49 (target : Nat) : pFor target % 49 = powModFast 2 49 (aFor target) := by
  unfold aFor pFor idx
  let r4 := target % 4
  let r49 := target % 49
  have hr4 : r4 < 4 := by exact Nat.mod_lt _ (by norm_num)
  have hr49 : r49 < 49 := by exact Nat.mod_lt _ (by norm_num)
  interval_cases h4 : r4 <;> interval_cases h49 : r49
  all_goals
    have ht4 : target % 4 = r4 := by rfl
    have ht49 : target % 49 = r49 := by rfl
    simp [aForIdx, pForIdx, h4, h49, ht4, ht49, powModFast, Nat.binaryRec, Nat.add_mod]

lemma pow_mul_mod_one {a r t m : Nat} (h : a^r ≡ 1 [MOD m]) : a^(r*t) ≡ 1 [MOD m] := by
  have hp := Nat.ModEq.pow t h
  simpa [pow_mul] using hp

lemma order_mod_q : 2 ^ 29400 % 137543 = 1 := by
  have h343base : 2 ^ 294 % 343 = 1 := by decide
  have h401base : 2 ^ 200 % 401 = 1 := by decide
  have h343eq : 2 ^ 294 ≡ 1 [MOD 343] := by rw [Nat.ModEq]; simpa using h343base
  have h401eq : 2 ^ 200 ≡ 1 [MOD 401] := by rw [Nat.ModEq]; simpa using h401base
  have h343 : 2 ^ 29400 ≡ 1 [MOD 343] := by
    have := pow_mul_mod_one (a:=2) (r:=294) (t:=100) (m:=343) h343eq
    norm_num at this ⊢; exact this
  have h401 : 2 ^ 29400 ≡ 1 [MOD 401] := by
    have := pow_mul_mod_one (a:=2) (r:=200) (t:=147) (m:=401) h401eq
    norm_num at this ⊢; exact this
  have hcop : Nat.Coprime 343 401 := by norm_num [Nat.Coprime]
  have hq : 2 ^ 29400 ≡ 1 [MOD 343 * 401] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h343,h401⟩
  rw [Nat.ModEq] at hq; norm_num at hq; exact hq

lemma inv600 (d : Nat) : 600 * ((d * 2138) % 2807) ≡ d [MOD 2807] := by
  have h1 : 600 * ((d * 2138) % 2807) ≡ 600 * (d * 2138) [MOD 2807] := by
    exact (Nat.ModEq.refl 600).mul (Nat.mod_modEq (d*2138) 2807)
  have h2 : 600 * (d * 2138) = d * (600 * 2138) := by ring
  rw [h2] at h1
  have h3 : d * (600 * 2138) ≡ d * 1 [MOD 2807] := by
    apply Nat.ModEq.mul_left; norm_num [Nat.ModEq]
  exact h1.trans (by simpa using h3)

lemma t_mul_L_mod (diff : Nat) (hdvd : 49 ∣ diff) :
    (((diff / 49 * 2138) % 2807) * 29400) ≡ diff [MOD 137543] := by
  let d := diff / 49
  have hdiff : diff = 49 * d := by dsimp [d]; rw [Nat.mul_div_cancel' hdvd]
  have h := inv600 d
  have h49 : 49 * (600 * ((d * 2138) % 2807)) ≡ 49 * d [MOD 49 * 2807] := by exact h.mul_left' 49
  rw [show 49 * 2807 = 137543 by norm_num] at h49
  have hleft : (((diff / 49 * 2138) % 2807) * 29400) = 49 * (600 * ((d * 2138) % 2807)) := by dsimp [d]; ring
  have hright : diff = 49 * d := hdiff
  rw [hleft, hright]; exact h49

lemma diff_add_mod (p a target q : Nat) (hp : p < q) (ha : a < q) (ht : target < q) :
    (((((p + q - a) + q - target) % q) + a + target) % q) = p := by
  have h1 : (p + q - a) + q - target + a + target = p + 2 * q := by omega
  calc
    ((((p + q - a) + q - target) % q + a + target) % q)
        = (((p + q - a) + q - target + a + target) % q) := by simp [Nat.add_mod]
    _ = (p + 2 * q) % q := by rw [h1]
    _ = p := by rw [mul_comm 2 q]; rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hp

lemma covDiff_dvd49 (target : Nat) : 49 ∣ covDiff target := by
  have hs := table_spec target
  rcases hs with ⟨ha2, ha588, h4, h49cond, hpdef⟩
  let a := aFor target
  let p := pFor target
  let tq := target % 137543
  have ha_lt_q : a < 137543 := by omega
  have hp_lt_q : p < 137543 := by
    dsimp [p]
    rw [hpdef]
    exact Nat.mod_lt _ (by norm_num)
  have htq_lt_q : tq < 137543 := by exact Nat.mod_lt _ (by norm_num)
  have ha_modq : a % 137543 = a := Nat.mod_eq_of_lt ha_lt_q
  have htq_mod49 : tq % 49 = target % 49 := by
    dsimp [tq]
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 49 ∣ 137543)]
  have hp_mod49 : p % 49 = powModFast 2 49 a := by
    dsimp [p, a]
    exact pFor_mod49 target
  have ha_le : a ≤ 588 := by dsimp [a]; exact ha588
  have hcond' : (p % 49 + 49 - a % 49) % 49 = target % 49 := by
    dsimp [p, a] at hp_mod49
    rw [hp_mod49]
    exact h49cond
  have hpa49 : p + 137543 - a ≡ target % 49 [MOD 49] := by
    have hsum : p + 137543 ≡ p % 49 + 49 [MOD 49] := by
      apply Nat.ModEq.add
      exact (Nat.mod_modEq p 49).symm
      norm_num [Nat.ModEq]
    have hares : a ≡ a % 49 [MOD 49] := (Nat.mod_modEq a 49).symm
    have hsub := Nat.ModEq.sub (by omega) (by omega) hsum hares
    have hcondME : p % 49 + 49 - a % 49 ≡ target % 49 [MOD 49] := by
      rw [Nat.ModEq]
      rw [hcond']
      exact (Nat.mod_eq_of_lt (Nat.mod_lt target (by norm_num : 0 < 49))).symm
    exact hsub.trans hcondME
  have hleft : (p + 137543 - a) + 137543 ≡ tq [MOD 49] := by
    have htarget_tq : target % 49 ≡ tq [MOD 49] := by
      rw [Nat.ModEq]
      rw [Nat.mod_eq_of_lt (Nat.mod_lt target (by norm_num : 0 < 49)), htq_mod49]
    have hq0 : 137543 ≡ 0 [MOD 49] := by norm_num [Nat.ModEq]
    simpa using (hpa49.add hq0).trans htarget_tq
  have hzero : (p + 137543 - a) + 137543 - tq ≡ 0 [MOD 49] := by
    have hsub := Nat.ModEq.sub (by omega) (Nat.le_refl tq) hleft (Nat.ModEq.refl tq)
    simpa using hsub
  have hmodzero : (((p + 137543 - a) + 137543 - tq) % 137543) % 49 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 49 ∣ 137543)]
    rw [Nat.ModEq] at hzero
    simpa using hzero
  rw [Nat.dvd_iff_mod_eq_zero]
  unfold covDiff
  dsimp [p, a, tq] at hmodzero
  rw [ha_modq]
  exact hmodzero

lemma pow_two_ge (k : Nat) : k ≤ 2 ^ k := by
  exact k.lt_two_pow_self.le

lemma two_pow_mod4_zero {k : Nat} (hk : 2 ≤ k) : 2 ^ k ≡ 0 [MOD 4] := by
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  rw [show 2 ^ (2 + t) = 4 * 2 ^ t by ring]
  rw [Nat.ModEq]
  simp

lemma pow_covK_mod_q (target : Nat) : 2 ^ covK target ≡ pFor target [MOD 137543] := by
  unfold covK covT
  set a := aFor target
  set t := (covDiff target / 49 * 2138) % 2807
  have horder : 2 ^ 29400 ≡ 1 [MOD 137543] := by
    rw [Nat.ModEq]
    exact order_mod_q
  have htL : 2 ^ (t * 29400) ≡ 1 [MOD 137543] := by
    have h := pow_mul_mod_one (a:=2) (r:=29400) (t:=t) (m:=137543) horder
    simpa [mul_comm] using h
  have hpow : 2 ^ (a + t * 29400) ≡ 2 ^ a * 1 [MOD 137543] := by
    rw [pow_add]
    exact (Nat.ModEq.refl (2 ^ a)).mul htL
  have hp := (table_spec target).2.2.2.2
  have hpa : 2 ^ a ≡ pFor target [MOD 137543] := by
    dsimp [a]
    rw [hp]
    exact (Nat.mod_modEq (2 ^ aFor target) 137543).symm
  exact hpow.trans (by simpa using hpa)

lemma target_add_covK_mod_q (target : Nat) : target + covK target ≡ pFor target [MOD 137543] := by
  have hs := table_spec target
  rcases hs with ⟨ha2, ha588, h4, h49cond, hpdef⟩
  have hp_lt_q : pFor target < 137543 := by
    rw [hpdef]
    exact Nat.mod_lt _ (by norm_num)
  have ha_lt_q : aFor target < 137543 := by omega
  have htq_lt_q : target % 137543 < 137543 := Nat.mod_lt _ (by norm_num)
  have hdvd := covDiff_dvd49 target
  have htL := t_mul_L_mod (covDiff target) hdvd
  have hdiffsum : (covDiff target + aFor target + target % 137543) % 137543 = pFor target := by
    unfold covDiff
    rw [Nat.mod_eq_of_lt ha_lt_q]
    exact diff_add_mod (pFor target) (aFor target) (target % 137543) 137543 hp_lt_q ha_lt_q htq_lt_q
  have hsumME : covDiff target + aFor target + target % 137543 ≡ pFor target [MOD 137543] := by
    rw [Nat.ModEq]
    rw [hdiffsum]
    exact (Nat.mod_eq_of_lt hp_lt_q).symm
  have htarget : target ≡ target % 137543 [MOD 137543] := (Nat.mod_modEq target 137543).symm
  unfold covK covT
  have hmain : target + (aFor target + ((covDiff target / 49 * 2138) % 2807) * 29400) ≡
      target % 137543 + (aFor target + covDiff target) [MOD 137543] := by
    exact htarget.add ((Nat.ModEq.refl (aFor target)).add htL)
  have hright : target % 137543 + (aFor target + covDiff target) = covDiff target + aFor target + target % 137543 := by omega
  rw [hright] at hmain
  exact hmain.trans hsumME

lemma target_add_covK_mod4 (target : Nat) : target + covK target ≡ 0 [MOD 4] := by
  have hs := table_spec target
  rcases hs with ⟨ha2, ha588, h4, h49cond, hpdef⟩
  unfold covK covT
  have hta : target + aFor target ≡ 0 [MOD 4] := by
    rw [Nat.ModEq]
    rw [add_comm]
    exact h4
  have htL0 : ((covDiff target / 49 * 2138) % 2807) * 29400 ≡ 0 [MOD 4] := by
    rw [Nat.ModEq]
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (by norm_num : 4 ∣ 29400) _)
  simpa [add_assoc] using hta.add htL0

lemma pow_covK_mod4 (target : Nat) : 2 ^ covK target ≡ 0 [MOD 4] := by
  have ha2 := (table_spec target).1
  unfold covK
  apply two_pow_mod4_zero
  omega

lemma target_add_covK_mod_n (target : Nat) : 2 ^ covK target ≡ target + covK target [MOD 550172] := by
  have h4left := pow_covK_mod4 target
  have h4right := target_add_covK_mod4 target
  have h4 : 2 ^ covK target ≡ target + covK target [MOD 4] := h4left.trans h4right.symm
  have hqleft := pow_covK_mod_q target
  have hqright := target_add_covK_mod_q target
  have hq : 2 ^ covK target ≡ target + covK target [MOD 137543] := hqleft.trans hqright.symm
  have hcop : Nat.Coprime 4 137543 := by norm_num [Nat.Coprime]
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h4, hq⟩
  norm_num at h
  exact h

lemma covK_bounds (target : Nat) : 1 ≤ covK target ∧ covK target ≤ 82496988 := by
  have hs := table_spec target
  rcases hs with ⟨ha2, ha588, h4, h49cond, hpdef⟩
  unfold covK covT
  constructor
  · omega
  · have htlt : ((covDiff target / 49 * 2138) % 2807) < 2807 := Nat.mod_lt _ (by norm_num)
    omega

lemma coverage_witness (target : Nat) (ht : target < 550172) :
  ∃ k, 1 ≤ k ∧ k ≤ 82496988 ∧ (2 ^ k - k) ≡ target [MOD 550172] := by
  refine ⟨covK target, ?_, ?_, ?_⟩
  · exact (covK_bounds target).1
  · exact (covK_bounds target).2
  · have hmain := target_add_covK_mod_n target
    have hle : covK target ≤ 2 ^ covK target := pow_two_ge (covK target)
    have hsub := Nat.ModEq.sub hle (Nat.le_add_left (covK target) target) hmain (Nat.ModEq.refl (covK target))
    simpa [Nat.add_sub_cancel_right] using hsub



def redDiff (target r p : Nat) := (((p + q - (r % q)) + q - (target % q)) % q)
def redT (target r p : Nat) := ((redDiff target r p / 49 * 2138) % 2807)
def redOK (target m r p : Nat) : Bool :=
  if (target + r) % 4 == 0 then
    if redDiff target r p % 49 == 0 then
      let k0 := r + redT target r p * 29400
      k0 == 0 || m < k0
    else true
  else true

def redLoop (target m : Nat) : Nat -> Nat -> Nat -> Bool
| 0, _r, _p => true
| fuel+1, r, p => redOK target m r p && redLoop target m fuel (r+1) ((2*p)%q)

def iterP : Nat -> Nat -> Nat
| 0, p => p
| n+1, p => iterP n ((2*p)%q)

lemma redLoop_add (target m a b r p : Nat) :
    redLoop target m (a + b) r p =
      (redLoop target m a r p && redLoop target m b (r+a) (iterP a p)) := by
  induction a generalizing r p with
  | zero => simp [redLoop, iterP]
  | succ a ih =>
      rw [Nat.succ_add]
      change (redOK target m r p && redLoop target m (a + b) (r+1) ((2*p)%q)) =
        ((redOK target m r p && redLoop target m a (r+1) ((2*p)%q)) &&
          redLoop target m b (r+(a+1)) (iterP a ((2*p)%q)))
      rw [ih]
      simp [Bool.and_assoc]
      congr 1
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma redLoop_cert_000 : redLoop 13573 16331503 100 0 1 = true := by decide
lemma iterP_cert_000 : iterP 100 1 = 7618 := by decide
lemma redLoop_cert_001 : redLoop 13573 16331503 100 100 7618 = true := by decide
lemma iterP_cert_001 : iterP 100 7618 = 128321 := by decide
lemma redLoop_cert_002 : redLoop 13573 16331503 100 200 128321 = true := by decide
lemma iterP_cert_002 : iterP 100 128321 = 31277 := by decide
lemma redLoop_cert_003 : redLoop 13573 16331503 100 300 31277 = true := by decide
lemma iterP_cert_003 : iterP 100 31277 = 43710 := by decide
lemma redLoop_cert_004 : redLoop 13573 16331503 100 400 43710 = true := by decide
lemma iterP_cert_004 : iterP 100 43710 = 128720 := by decide
lemma redLoop_cert_005 : redLoop 13573 16331503 100 500 128720 = true := by decide
lemma iterP_cert_005 : iterP 100 128720 = 44913 := by decide
lemma redLoop_cert_006 : redLoop 13573 16331503 100 600 44913 = true := by decide
lemma iterP_cert_006 : iterP 100 44913 = 77793 := by decide
lemma redLoop_cert_007 : redLoop 13573 16331503 100 700 77793 = true := by decide
lemma iterP_cert_007 : iterP 100 77793 = 91830 := by decide
lemma redLoop_cert_008 : redLoop 13573 16331503 100 800 91830 = true := by decide
lemma iterP_cert_008 : iterP 100 91830 = 17242 := by decide
lemma redLoop_cert_009 : redLoop 13573 16331503 100 900 17242 = true := by decide
lemma iterP_cert_009 : iterP 100 17242 = 133534 := by decide
lemma redLoop_cert_010 : redLoop 13573 16331503 100 1000 133534 = true := by decide
lemma iterP_cert_010 : iterP 100 133534 = 131527 := by decide
lemma redLoop_cert_011 : redLoop 13573 16331503 100 1100 131527 = true := by decide
lemma iterP_cert_011 : iterP 100 131527 = 109474 := by decide
lemma redLoop_cert_012 : redLoop 13573 16331503 100 1200 109474 = true := by decide
lemma iterP_cert_012 : iterP 100 109474 = 49723 := by decide
lemma redLoop_cert_013 : redLoop 13573 16331503 100 1300 49723 = true := by decide
lemma iterP_cert_013 : iterP 100 49723 = 133935 := by decide
lemma redLoop_cert_014 : redLoop 13573 16331503 100 1400 133935 = true := by decide
lemma iterP_cert_014 : iterP 100 133935 = 22856 := by decide
lemma redLoop_cert_015 : redLoop 13573 16331503 100 1500 22856 = true := by decide
lemma iterP_cert_015 : iterP 100 22856 = 125113 := by decide
lemma redLoop_cert_016 : redLoop 13573 16331503 100 1600 125113 = true := by decide
lemma iterP_cert_016 : iterP 100 125113 = 75387 := by decide
lemma redLoop_cert_017 : redLoop 13573 16331503 100 1700 75387 = true := by decide
lemma iterP_cert_017 : iterP 100 75387 = 56141 := by decide
lemma redLoop_cert_018 : redLoop 13573 16331503 100 1800 56141 = true := by decide
lemma iterP_cert_018 : iterP 100 56141 = 60951 := by decide
lemma redLoop_cert_019 : redLoop 13573 16331503 100 1900 60951 = true := by decide
lemma iterP_cert_019 : iterP 100 60951 = 117093 := by decide
lemma redLoop_cert_020 : redLoop 13573 16331503 100 2000 117093 = true := by decide
lemma iterP_cert_020 : iterP 100 117093 = 48119 := by decide
lemma redLoop_cert_021 : redLoop 13573 16331503 100 2100 48119 = true := by decide
lemma iterP_cert_021 : iterP 100 48119 = 18447 := by decide
lemma redLoop_cert_022 : redLoop 13573 16331503 100 2200 18447 = true := by decide
lemma iterP_cert_022 : iterP 100 18447 = 97843 := by decide
lemma redLoop_cert_023 : redLoop 13573 16331503 100 2300 97843 = true := by decide
lemma iterP_cert_023 : iterP 100 97843 = 22457 := by decide
lemma redLoop_cert_024 : redLoop 13573 16331503 100 2400 22457 = true := by decide
lemma iterP_cert_024 : iterP 100 22457 = 111477 := by decide
lemma redLoop_cert_025 : redLoop 13573 16331503 100 2500 111477 = true := by decide
lemma iterP_cert_025 : iterP 100 111477 = 41304 := by decide
lemma redLoop_cert_026 : redLoop 13573 16331503 100 2600 41304 = true := by decide
lemma iterP_cert_026 : iterP 100 41304 = 93031 := by decide
lemma redLoop_cert_027 : redLoop 13573 16331503 100 2700 93031 = true := by decide
lemma iterP_cert_027 : iterP 100 93031 = 88622 := by decide
lemma redLoop_cert_028 : redLoop 13573 16331503 100 2800 88622 = true := by decide
lemma iterP_cert_028 : iterP 100 88622 = 61352 := by decide
lemma redLoop_cert_029 : redLoop 13573 16331503 100 2900 61352 = true := by decide
lemma iterP_cert_029 : iterP 100 61352 = 8422 := by decide
lemma redLoop_cert_030 : redLoop 13573 16331503 100 3000 8422 = true := by decide
lemma iterP_cert_030 : iterP 100 8422 = 63758 := by decide
lemma redLoop_cert_031 : redLoop 13573 16331503 100 3100 63758 = true := by decide
lemma iterP_cert_031 : iterP 100 63758 = 44111 := by decide
lemma redLoop_cert_032 : redLoop 13573 16331503 100 3200 44111 = true := by decide
lemma iterP_cert_032 : iterP 100 44111 = 20049 := by decide
lemma redLoop_cert_033 : redLoop 13573 16331503 100 3300 20049 = true := by decide
lemma iterP_cert_033 : iterP 100 20049 = 60552 := by decide
lemma redLoop_cert_034 : redLoop 13573 16331503 100 3400 60552 = true := by decide
lemma iterP_cert_034 : iterP 100 60552 = 103457 := by decide
lemma redLoop_cert_035 : redLoop 13573 16331503 100 3500 103457 = true := by decide
lemma iterP_cert_035 : iterP 100 103457 = 14036 := by decide
lemma redLoop_cert_036 : redLoop 13573 16331503 100 3600 14036 = true := by decide
lemma iterP_cert_036 : iterP 100 14036 = 55337 := by decide
lemma redLoop_cert_037 : redLoop 13573 16331503 100 3700 55337 = true := by decide
lemma iterP_cert_037 : iterP 100 55337 = 125514 := by decide
lemma redLoop_cert_038 : redLoop 13573 16331503 100 3800 125514 = true := by decide
lemma iterP_cert_038 : iterP 100 125514 = 104259 := by decide
lemma redLoop_cert_039 : redLoop 13573 16331503 100 3900 104259 = true := by decide
lemma iterP_cert_039 : iterP 100 104259 = 71780 := by decide
lemma redLoop_cert_040 : redLoop 13573 16331503 100 4000 71780 = true := by decide
lemma iterP_cert_040 : iterP 100 71780 = 86615 := by decide
lemma redLoop_cert_041 : redLoop 13573 16331503 100 4100 86615 = true := by decide
lemma iterP_cert_041 : iterP 100 86615 = 39299 := by decide
lemma redLoop_cert_042 : redLoop 13573 16331503 100 4200 39299 = true := by decide
lemma iterP_cert_042 : iterP 100 39299 = 86214 := by decide
lemma redLoop_cert_043 : redLoop 13573 16331503 100 4300 86214 = true := by decide
lemma iterP_cert_043 : iterP 100 86214 = 10427 := by decide
lemma redLoop_cert_044 : redLoop 13573 16331503 100 4400 10427 = true := by decide
lemma iterP_cert_044 : iterP 100 10427 = 70575 := by decide
lemma redLoop_cert_045 : redLoop 13573 16331503 100 4500 70575 = true := by decide
lemma iterP_cert_045 : iterP 100 70575 = 122306 := by decide
lemma redLoop_cert_046 : redLoop 13573 16331503 100 4600 122306 = true := by decide
lemma iterP_cert_046 : iterP 100 122306 = 10826 := by decide
lemma redLoop_cert_047 : redLoop 13573 16331503 100 4700 10826 = true := by decide
lemma iterP_cert_047 : iterP 100 10826 = 84211 := by decide
lemma redLoop_cert_048 : redLoop 13573 16331503 100 4800 84211 = true := by decide
lemma iterP_cert_048 : iterP 100 84211 = 18846 := by decide
lemma redLoop_cert_049 : redLoop 13573 16331503 100 4900 18846 = true := by decide
lemma iterP_cert_049 : iterP 100 18846 = 111479 := by decide
lemma redLoop_cert_050 : redLoop 13573 16331503 100 5000 111479 = true := by decide
lemma iterP_cert_050 : iterP 100 111479 = 56540 := by decide
lemma redLoop_cert_051 : redLoop 13573 16331503 100 5100 56540 = true := by decide
lemma iterP_cert_051 : iterP 100 56540 = 74587 := by decide
lemma redLoop_cert_052 : redLoop 13573 16331503 100 5200 74587 = true := by decide
lemma iterP_cert_052 : iterP 100 74587 = 13633 := by decide
lemma redLoop_cert_053 : redLoop 13573 16331503 100 5300 13633 = true := by decide
lemma iterP_cert_053 : iterP 100 13633 = 11229 := by decide
lemma redLoop_cert_054 : redLoop 13573 16331503 100 5400 11229 = true := by decide
lemma iterP_cert_054 : iterP 100 11229 = 128319 := by decide
lemma redLoop_cert_055 : redLoop 13573 16331503 100 5500 128319 = true := by decide
lemma iterP_cert_055 : iterP 100 128319 = 16041 := by decide
lemma redLoop_cert_056 : redLoop 13573 16331503 100 5600 16041 = true := by decide
lemma iterP_cert_056 : iterP 100 16041 = 62154 := by decide
lemma redLoop_cert_057 : redLoop 13573 16331503 100 5700 62154 = true := by decide
lemma iterP_cert_057 : iterP 100 62154 = 66166 := by decide
lemma redLoop_cert_058 : redLoop 13573 16331503 100 5800 66166 = true := by decide
lemma iterP_cert_058 : iterP 100 66166 = 95036 := by decide
lemma redLoop_cert_059 : redLoop 13573 16331503 100 5900 95036 = true := by decide
lemma iterP_cert_059 : iterP 100 95036 = 95439 := by decide
lemma redLoop_cert_060 : redLoop 13573 16331503 100 6000 95439 = true := by decide
lemma iterP_cert_060 : iterP 100 95439 = 2004 := by decide
lemma redLoop_cert_061 : redLoop 13573 16331503 100 6100 2004 = true := by decide
lemma iterP_cert_061 : iterP 100 2004 = 136742 := by decide
lemma redLoop_cert_062 : redLoop 13573 16331503 100 6200 136742 = true := by decide
lemma iterP_cert_062 : iterP 100 136742 = 87417 := by decide
lemma redLoop_cert_063 : redLoop 13573 16331503 100 6300 87417 = true := by decide
lemma iterP_cert_063 : iterP 100 87417 = 97043 := by decide
lemma redLoop_cert_064 : redLoop 13573 16331503 100 6400 97043 = true := by decide
lemma iterP_cert_064 : iterP 100 97043 = 117492 := by decide
lemma redLoop_cert_065 : redLoop 13573 16331503 100 6500 117492 = true := by decide
lemma iterP_cert_065 : iterP 100 117492 = 61755 := by decide
lemma redLoop_cert_066 : redLoop 13573 16331503 100 6600 61755 = true := by decide
lemma iterP_cert_066 : iterP 100 61755 = 52530 := by decide
lemma redLoop_cert_067 : redLoop 13573 16331503 100 6700 52530 = true := by decide
lemma iterP_cert_067 : iterP 100 52530 = 60953 := by decide
lemma redLoop_cert_068 : redLoop 13573 16331503 100 6800 60953 = true := by decide
lemma iterP_cert_068 : iterP 100 60953 = 132329 := by decide
lemma redLoop_cert_069 : redLoop 13573 16331503 100 6900 132329 = true := by decide
lemma iterP_cert_069 : iterP 100 132329 = 29675 := by decide
lemma redLoop_cert_070 : redLoop 13573 16331503 100 7000 29675 = true := by decide
lemma iterP_cert_070 : iterP 100 29675 = 81001 := by decide
lemma redLoop_cert_071 : redLoop 13573 16331503 100 7100 81001 = true := by decide
lemma iterP_cert_071 : iterP 100 81001 = 47720 := by decide
lemma redLoop_cert_072 : redLoop 13573 16331503 100 7200 47720 = true := by decide
lemma iterP_cert_072 : iterP 100 47720 = 4811 := by decide
lemma redLoop_cert_073 : redLoop 13573 16331503 100 7300 4811 = true := by decide
lemma iterP_cert_073 : iterP 100 4811 = 63760 := by decide
lemma redLoop_cert_074 : redLoop 13573 16331503 100 7400 63760 = true := by decide
lemma iterP_cert_074 : iterP 100 63760 = 59347 := by decide
lemma redLoop_cert_075 : redLoop 13573 16331503 100 7500 59347 = true := by decide
lemma iterP_cert_075 : iterP 100 59347 = 1605 := by decide
lemma redLoop_cert_076 : redLoop 13573 16331503 100 7600 1605 = true := by decide
lemma iterP_cert_076 : iterP 100 1605 = 123106 := by decide
lemma redLoop_cert_077 : redLoop 13573 16331503 100 7700 123106 = true := by decide
lemma iterP_cert_077 : iterP 100 123106 = 53334 := by decide
lemma redLoop_cert_078 : redLoop 13573 16331503 100 7800 53334 = true := by decide
lemma iterP_cert_078 : iterP 100 53334 = 133933 := by decide
lemma redLoop_cert_079 : redLoop 13573 16331503 100 7900 133933 = true := by decide
lemma iterP_cert_079 : iterP 100 133933 = 7620 := by decide
lemma redLoop_cert_080 : redLoop 13573 16331503 100 8000 7620 = true := by decide
lemma iterP_cert_080 : iterP 100 7620 = 6014 := by decide
lemma redLoop_cert_081 : redLoop 13573 16331503 100 8100 6014 = true := by decide
lemma iterP_cert_081 : iterP 100 6014 = 12833 := by decide
lemma redLoop_cert_082 : redLoop 13573 16331503 100 8200 12833 = true := by decide
lemma iterP_cert_082 : iterP 100 12833 = 106264 := by decide
lemma redLoop_cert_083 : redLoop 13573 16331503 100 8300 106264 = true := by decide
lemma iterP_cert_083 : iterP 100 106264 = 78597 := by decide
lemma redLoop_cert_084 : redLoop 13573 16331503 100 8400 78597 = true := by decide
lemma iterP_cert_084 : iterP 100 78597 = 27267 := by decide
lemma redLoop_cert_085 : redLoop 13573 16331503 100 8500 27267 = true := by decide
lemma iterP_cert_085 : iterP 100 27267 = 30076 := by decide
lemma redLoop_cert_086 : redLoop 13573 16331503 100 8600 30076 = true := by decide
lemma iterP_cert_086 : iterP 100 30076 = 109873 := by decide
lemma redLoop_cert_087 : redLoop 13573 16331503 100 8700 109873 = true := by decide
lemma iterP_cert_087 : iterP 100 109873 = 63359 := by decide
lemma redLoop_cert_088 : redLoop 13573 16331503 100 8800 63359 = true := by decide
lemma iterP_cert_088 : iterP 100 63359 = 30475 := by decide
lemma redLoop_cert_089 : redLoop 13573 16331503 100 8900 30475 = true := by decide
lemma iterP_cert_089 : iterP 100 30475 = 123509 := by decide
lemma redLoop_cert_090 : redLoop 13573 16331503 100 9000 123509 = true := by decide
lemma iterP_cert_090 : iterP 100 123509 = 97442 := by decide
lemma redLoop_cert_091 : redLoop 13573 16331503 100 9100 97442 = true := by decide
lemma iterP_cert_091 : iterP 100 97442 = 131128 := by decide
lemma redLoop_cert_092 : redLoop 13573 16331503 100 9200 131128 = true := by decide
lemma iterP_cert_092 : iterP 100 131128 = 95838 := by decide
lemma redLoop_cert_093 : redLoop 13573 16331503 100 9300 95838 = true := by decide
lemma iterP_cert_093 : iterP 100 95838 = 15640 := by decide
lemma redLoop_cert_094 : redLoop 13573 16331503 100 9400 15640 = true := by decide
lemma iterP_cert_094 : iterP 100 15640 = 33282 := by decide
lemma redLoop_cert_095 : redLoop 13573 16331503 100 9500 33282 = true := by decide
lemma iterP_cert_095 : iterP 100 33282 = 50527 := by decide
lemma redLoop_cert_096 : redLoop 13573 16331503 100 9600 50527 = true := by decide
lemma iterP_cert_096 : iterP 100 50527 = 69372 := by decide
lemma redLoop_cert_097 : redLoop 13573 16331503 100 9700 69372 = true := by decide
lemma iterP_cert_097 : iterP 100 69372 = 35690 := by decide
lemma redLoop_cert_098 : redLoop 13573 16331503 100 9800 35690 = true := by decide
lemma iterP_cert_098 : iterP 100 35690 = 101452 := by decide
lemma redLoop_cert_099 : redLoop 13573 16331503 100 9900 101452 = true := by decide
lemma iterP_cert_099 : iterP 100 101452 = 7219 := by decide
lemma redLoop_cert_100 : redLoop 13573 16331503 100 10000 7219 = true := by decide
lemma iterP_cert_100 : iterP 100 7219 = 114685 := by decide
lemma redLoop_cert_101 : redLoop 13573 16331503 100 10100 114685 = true := by decide
lemma iterP_cert_101 : iterP 100 114685 = 134737 := by decide
lemma redLoop_cert_102 : redLoop 13573 16331503 100 10200 134737 = true := by decide
lemma iterP_cert_102 : iterP 100 134737 = 80600 := by decide
lemma redLoop_cert_103 : redLoop 13573 16331503 100 10300 80600 = true := by decide
lemma iterP_cert_103 : iterP 100 80600 = 18848 := by decide
lemma redLoop_cert_104 : redLoop 13573 16331503 100 10400 18848 = true := by decide
lemma iterP_cert_104 : iterP 100 18848 = 126715 := by decide
lemma redLoop_cert_105 : redLoop 13573 16331503 100 10500 126715 = true := by decide
lemma iterP_cert_105 : iterP 100 126715 = 38096 := by decide
lemma redLoop_cert_106 : redLoop 13573 16331503 100 10600 38096 = true := by decide
lemma iterP_cert_106 : iterP 100 38096 = 137141 := by decide
lemma redLoop_cert_107 : redLoop 13573 16331503 100 10700 137141 = true := by decide
lemma iterP_cert_107 : iterP 100 137141 = 101053 := by decide
lemma redLoop_cert_108 : redLoop 13573 16331503 100 10800 101053 = true := by decide
lemma iterP_cert_108 : iterP 100 101053 = 131126 := by decide
lemma redLoop_cert_109 : redLoop 13573 16331503 100 10900 131126 = true := by decide
lemma iterP_cert_109 : iterP 100 131126 = 80602 := by decide
lemma redLoop_cert_110 : redLoop 13573 16331503 100 11000 80602 = true := by decide
lemma iterP_cert_110 : iterP 100 80602 = 34084 := by decide
lemma redLoop_cert_111 : redLoop 13573 16331503 100 11100 34084 = true := by decide
lemma iterP_cert_111 : iterP 100 34084 = 108271 := by decide
lemma redLoop_cert_112 : redLoop 13573 16331503 100 11200 108271 = true := by decide
lemma iterP_cert_112 : iterP 100 108271 = 100650 := by decide
lemma redLoop_cert_113 : redLoop 13573 16331503 100 11300 100650 = true := by decide
lemma iterP_cert_113 : iterP 100 100650 = 87018 := by decide
lemma redLoop_cert_114 : redLoop 13573 16331503 100 11400 87018 = true := by decide
lemma iterP_cert_114 : iterP 100 87018 = 83407 := by decide
lemma redLoop_cert_115 : redLoop 13573 16331503 100 11500 83407 = true := by decide
lemma iterP_cert_115 : iterP 100 83407 = 83409 := by decide
lemma redLoop_cert_116 : redLoop 13573 16331503 100 11600 83409 = true := by decide
lemma iterP_cert_116 : iterP 100 83409 = 98645 := by decide
lemma redLoop_cert_117 : redLoop 13573 16331503 100 11700 98645 = true := by decide
lemma iterP_cert_117 : iterP 100 98645 = 80201 := by decide
lemma redLoop_cert_118 : redLoop 13573 16331503 100 11800 80201 = true := by decide
lemma iterP_cert_118 : iterP 100 80201 = 5212 := by decide
lemma redLoop_cert_119 : redLoop 13573 16331503 100 11900 5212 = true := by decide
lemma iterP_cert_119 : iterP 100 5212 = 92632 := by decide
lemma redLoop_cert_120 : redLoop 13573 16331503 100 12000 92632 = true := by decide
lemma iterP_cert_120 : iterP 100 92632 = 74986 := by decide
lemma redLoop_cert_121 : redLoop 13573 16331503 100 12100 74986 = true := by decide
lemma iterP_cert_121 : iterP 100 74986 = 27269 := by decide
lemma redLoop_cert_122 : redLoop 13573 16331503 100 12200 27269 = true := by decide
lemma iterP_cert_122 : iterP 100 27269 = 45312 := by decide
lemma redLoop_cert_123 : redLoop 13573 16331503 100 12300 45312 = true := by decide
lemma iterP_cert_123 : iterP 100 45312 = 91429 := by decide
lemma redLoop_cert_124 : redLoop 13573 16331503 100 12400 91429 = true := by decide
lemma iterP_cert_124 : iterP 100 91429 = 125913 := by decide
lemma redLoop_cert_125 : redLoop 13573 16331503 100 12500 125913 = true := by decide
lemma iterP_cert_125 : iterP 100 125913 = 117895 := by decide
lemma redLoop_cert_126 : redLoop 13573 16331503 100 12600 117895 = true := by decide
lemma iterP_cert_126 : iterP 100 117895 = 105863 := by decide
lemma redLoop_cert_127 : redLoop 13573 16331503 100 12700 105863 = true := by decide
lemma iterP_cert_127 : iterP 100 105863 = 49725 := by decide
lemma redLoop_cert_128 : redLoop 13573 16331503 100 12800 49725 = true := by decide
lemma iterP_cert_128 : iterP 100 49725 = 11628 := by decide
lemma redLoop_cert_129 : redLoop 13573 16331503 100 12900 11628 = true := by decide
lemma iterP_cert_129 : iterP 100 11628 = 4412 := by decide
lemma redLoop_cert_130 : redLoop 13573 16331503 100 13000 4412 = true := by decide
lemma iterP_cert_130 : iterP 100 4412 = 50124 := by decide
lemma redLoop_cert_131 : redLoop 13573 16331503 100 13100 50124 = true := by decide
lemma iterP_cert_131 : iterP 100 50124 = 25264 := by decide
lemma redLoop_cert_132 : redLoop 13573 16331503 100 13200 25264 = true := by decide
lemma iterP_cert_132 : iterP 100 25264 = 38495 := by decide
lemma redLoop_cert_133 : redLoop 13573 16331503 100 13300 38495 = true := by decide
lemma iterP_cert_133 : iterP 100 38495 = 13234 := by decide
lemma redLoop_cert_134 : redLoop 13573 16331503 100 13400 13234 = true := by decide
lemma iterP_cert_134 : iterP 100 13234 = 135136 := by decide
lemma redLoop_cert_135 : redLoop 13573 16331503 100 13500 135136 = true := by decide
lemma iterP_cert_135 : iterP 100 135136 = 94236 := by decide
lemma redLoop_cert_136 : redLoop 13573 16331503 100 13600 94236 = true := by decide
lemma iterP_cert_136 : iterP 100 94236 = 52931 := by decide
lemma redLoop_cert_137 : redLoop 13573 16331503 100 13700 52931 = true := by decide
lemma iterP_cert_137 : iterP 100 52931 = 89825 := by decide
lemma redLoop_cert_138 : redLoop 13573 16331503 100 13800 89825 = true := by decide
lemma iterP_cert_138 : iterP 100 89825 = 10425 := by decide
lemma redLoop_cert_139 : redLoop 13573 16331503 100 13900 10425 = true := by decide
lemma iterP_cert_139 : iterP 100 10425 = 55339 := by decide
lemma redLoop_cert_140 : redLoop 13573 16331503 100 14000 55339 = true := by decide
lemma iterP_cert_140 : iterP 100 55339 = 3207 := by decide
lemma redLoop_cert_141 : redLoop 13573 16331503 100 14100 3207 = true := by decide
lemma iterP_cert_141 : iterP 100 3207 = 85815 := by decide
lemma redLoop_cert_142 : redLoop 13573 16331503 100 14200 85815 = true := by decide
lemma iterP_cert_142 : iterP 100 85815 = 134334 := by decide
lemma redLoop_cert_143 : redLoop 13573 16331503 100 14300 134334 = true := by decide
lemma iterP_cert_143 : iterP 100 134334 = 36492 := by decide
lemma redLoop_cert_144 : redLoop 13573 16331503 100 14400 36492 = true := by decide
lemma iterP_cert_144 : iterP 100 36492 = 21653 := by decide
lemma redLoop_cert_145 : redLoop 13573 16331503 100 14500 21653 = true := by decide
lemma iterP_cert_145 : iterP 100 21653 = 38497 := by decide
lemma redLoop_cert_146 : redLoop 13573 16331503 100 14600 38497 = true := by decide
lemma iterP_cert_146 : iterP 100 38497 = 28470 := by decide
lemma redLoop_cert_147 : redLoop 13573 16331503 100 14700 28470 = true := by decide
lemma iterP_cert_147 : iterP 100 28470 = 116692 := by decide
lemma redLoop_cert_148 : redLoop 13573 16331503 100 14800 116692 = true := by decide
lemma iterP_cert_148 : iterP 100 116692 = 19247 := by decide
lemma redLoop_cert_149 : redLoop 13573 16331503 100 14900 19247 = true := by decide
lemma iterP_cert_149 : iterP 100 19247 = 2808 := by decide
lemma redLoop_cert_150 : redLoop 13573 16331503 100 15000 2808 = true := by decide
lemma iterP_cert_150 : iterP 100 2808 = 72179 := by decide
lemma redLoop_cert_151 : redLoop 13573 16331503 100 15100 72179 = true := by decide
lemma iterP_cert_151 : iterP 100 72179 = 100251 := by decide
lemma redLoop_cert_152 : redLoop 13573 16331503 100 15200 100251 = true := by decide
lemma iterP_cert_152 : iterP 100 100251 = 73382 := by decide
lemma redLoop_cert_153 : redLoop 13573 16331503 100 15300 73382 = true := by decide
lemma iterP_cert_153 : iterP 100 73382 = 49324 := by decide
lemma redLoop_cert_154 : redLoop 13573 16331503 100 15400 49324 = true := by decide
lemma iterP_cert_154 : iterP 100 49324 = 120299 := by decide
lemma redLoop_cert_155 : redLoop 13573 16331503 100 15500 120299 = true := by decide
lemma iterP_cert_155 : iterP 100 120299 = 126316 := by decide
lemma redLoop_cert_156 : redLoop 13573 16331503 100 15600 126316 = true := by decide
lemma iterP_cert_156 : iterP 100 126316 = 24460 := by decide
lemma redLoop_cert_157 : redLoop 13573 16331503 100 15700 24460 = true := by decide
lemma iterP_cert_157 : iterP 100 24460 = 103058 := by decide
lemma redLoop_cert_158 : redLoop 13573 16331503 100 15800 103058 = true := by decide
lemma iterP_cert_158 : iterP 100 103058 = 400 := by decide
lemma redLoop_cert_159 : redLoop 13573 16331503 100 15900 400 = true := by decide
lemma iterP_cert_159 : iterP 100 400 = 21254 := by decide
lemma redLoop_cert_160 : redLoop 13573 16331503 100 16000 21254 = true := by decide
lemma iterP_cert_160 : iterP 100 21254 = 24861 := by decide
lemma redLoop_cert_161 : redLoop 13573 16331503 100 16100 24861 = true := by decide
lemma iterP_cert_161 : iterP 100 24861 = 131930 := by decide
lemma redLoop_cert_162 : redLoop 13573 16331503 100 16200 131930 = true := by decide
lemma iterP_cert_162 : iterP 100 131930 = 16039 := by decide
lemma redLoop_cert_163 : redLoop 13573 16331503 100 16300 16039 = true := by decide
lemma iterP_cert_163 : iterP 100 16039 = 46918 := by decide
lemma redLoop_cert_164 : redLoop 13573 16331503 100 16400 46918 = true := by decide
lemma iterP_cert_164 : iterP 100 46918 = 84610 := by decide
lemma redLoop_cert_165 : redLoop 13573 16331503 100 16500 84610 = true := by decide
lemma iterP_cert_165 : iterP 100 84610 = 32482 := by decide
lemma redLoop_cert_166 : redLoop 13573 16331503 100 16600 32482 = true := by decide
lemma iterP_cert_166 : iterP 100 32482 = 8019 := by decide
lemma redLoop_cert_167 : redLoop 13573 16331503 100 16700 8019 = true := by decide
lemma iterP_cert_167 : iterP 100 8019 = 19650 := by decide
lemma redLoop_cert_168 : redLoop 13573 16331503 100 16800 19650 = true := by decide
lemma iterP_cert_168 : iterP 100 19650 = 46916 := by decide
lemma redLoop_cert_169 : redLoop 13573 16331503 100 16900 46916 = true := by decide
lemma iterP_cert_169 : iterP 100 46916 = 69374 := by decide
lemma redLoop_cert_170 : redLoop 13573 16331503 100 17000 69374 = true := by decide
lemma iterP_cert_170 : iterP 100 69374 = 50926 := by decide
lemma redLoop_cert_171 : redLoop 13573 16331503 100 17100 50926 = true := by decide
lemma iterP_cert_171 : iterP 100 50926 = 83008 := by decide
lemma redLoop_cert_172 : redLoop 13573 16331503 100 17200 83008 = true := by decide
lemma iterP_cert_172 : iterP 100 83008 = 69773 := by decide
lemma redLoop_cert_173 : redLoop 13573 16331503 100 17300 69773 = true := by decide
lemma iterP_cert_173 : iterP 100 69773 = 64562 := by decide
lemma redLoop_cert_174 : redLoop 13573 16331503 100 17400 64562 = true := by decide
lemma iterP_cert_174 : iterP 100 64562 = 117091 := by decide
lemma redLoop_cert_175 : redLoop 13573 16331503 100 17500 117091 = true := by decide
lemma iterP_cert_175 : iterP 100 117091 = 32883 := by decide
lemma redLoop_cert_176 : redLoop 13573 16331503 100 17600 32883 = true := by decide
lemma iterP_cert_176 : iterP 100 32883 = 36891 := by decide
lemma redLoop_cert_177 : redLoop 13573 16331503 100 17700 36891 = true := by decide
lemma iterP_cert_177 : iterP 100 36891 = 35289 := by decide
lemma redLoop_cert_178 : redLoop 13573 16331503 100 17800 35289 = true := by decide
lemma iterP_cert_178 : iterP 100 35289 = 72580 := by decide
lemma redLoop_cert_179 : redLoop 13573 16331503 100 17900 72580 = true := by decide
lemma iterP_cert_179 : iterP 100 72580 = 129123 := by decide
lemma redLoop_cert_180 : redLoop 13573 16331503 100 18000 129123 = true := by decide
lemma iterP_cert_180 : iterP 100 129123 = 89021 := by decide
lemma redLoop_cert_181 : redLoop 13573 16331503 100 18100 89021 = true := by decide
lemma iterP_cert_181 : iterP 100 89021 = 74988 := by decide
lemma redLoop_cert_182 : redLoop 13573 16331503 100 18200 74988 = true := by decide
lemma iterP_cert_182 : iterP 100 74988 = 42505 := by decide
lemma redLoop_cert_183 : redLoop 13573 16331503 100 18300 42505 = true := by decide
lemma iterP_cert_183 : iterP 100 42505 = 26868 := by decide
lemma redLoop_cert_184 : redLoop 13573 16331503 100 18400 26868 = true := by decide
lemma iterP_cert_184 : iterP 100 26868 = 16440 := by decide
lemma redLoop_cert_185 : redLoop 13573 16331503 100 18500 16440 = true := by decide
lemma iterP_cert_185 : iterP 100 16440 = 75790 := by decide
lemma redLoop_cert_186 : redLoop 13573 16331503 100 18600 75790 = true := by decide
lemma iterP_cert_186 : iterP 100 75790 = 100249 := by decide
lemma redLoop_cert_187 : redLoop 13573 16331503 100 18700 100249 = true := by decide
lemma iterP_cert_187 : iterP 100 100249 = 58146 := by decide
lemma redLoop_cert_188 : redLoop 13573 16331503 100 18800 58146 = true := by decide
lemma iterP_cert_188 : iterP 100 58146 = 67768 := by decide
lemma redLoop_cert_189 : redLoop 13573 16331503 100 18900 67768 = true := by decide
lemma iterP_cert_189 : iterP 100 67768 = 57745 := by decide
lemma redLoop_cert_190 : redLoop 13573 16331503 100 19000 57745 = true := by decide
lemma iterP_cert_190 : iterP 100 57745 = 38896 := by decide
lemma redLoop_cert_191 : redLoop 13573 16331503 100 19100 38896 = true := by decide
lemma iterP_cert_191 : iterP 100 38896 = 42106 := by decide
lemma redLoop_cert_192 : redLoop 13573 16331503 100 19200 42106 = true := by decide
lemma iterP_cert_192 : iterP 100 42106 = 13232 := by decide
lemma redLoop_cert_193 : redLoop 13573 16331503 100 19300 13232 = true := by decide
lemma iterP_cert_193 : iterP 100 13232 = 119900 := by decide
lemma redLoop_cert_194 : redLoop 13573 16331503 100 19400 119900 = true := by decide
lemma iterP_cert_194 : iterP 100 119900 = 112680 := by decide
lemma redLoop_cert_195 : redLoop 13573 16331503 100 19500 112680 = true := by decide
lemma iterP_cert_195 : iterP 100 112680 = 127920 := by decide
lemma redLoop_cert_196 : redLoop 13573 16331503 100 19600 127920 = true := by decide
lemma iterP_cert_196 : iterP 100 127920 = 2405 := by decide
lemma redLoop_cert_197 : redLoop 13573 16331503 100 19700 2405 = true := by decide
lemma iterP_cert_197 : iterP 100 2405 = 28071 := by decide
lemma redLoop_cert_198 : redLoop 13573 16331503 100 19800 28071 = true := by decide
lemma iterP_cert_198 : iterP 100 28071 = 103056 := by decide
lemma redLoop_cert_199 : redLoop 13573 16331503 100 19900 103056 = true := by decide
lemma iterP_cert_199 : iterP 100 103056 = 122707 := by decide
lemma redLoop_cert_200 : redLoop 13573 16331503 100 20000 122707 = true := by decide
lemma iterP_cert_200 : iterP 100 122707 = 39698 := by decide
lemma redLoop_cert_201 : redLoop 13573 16331503 100 20100 39698 = true := by decide
lemma iterP_cert_201 : iterP 100 39698 = 99850 := by decide
lemma redLoop_cert_202 : redLoop 13573 16331503 100 20200 99850 = true := by decide
lemma iterP_cert_202 : iterP 100 99850 = 44510 := by decide
lemma redLoop_cert_203 : redLoop 13573 16331503 100 20300 44510 = true := by decide
lemma iterP_cert_203 : iterP 100 44510 = 33685 := by decide
lemma redLoop_cert_204 : redLoop 13573 16331503 100 20400 33685 = true := by decide
lemma iterP_cert_204 : iterP 100 33685 = 94635 := by decide
lemma redLoop_cert_205 : redLoop 13573 16331503 100 20500 94635 = true := by decide
lemma iterP_cert_205 : iterP 100 94635 = 66567 := by decide
lemma redLoop_cert_206 : redLoop 13573 16331503 100 20600 66567 = true := by decide
lemma iterP_cert_206 : iterP 100 66567 = 123908 := by decide
lemma redLoop_cert_207 : redLoop 13573 16331503 100 20700 123908 = true := by decide
lemma iterP_cert_207 : iterP 100 123908 = 111078 := by decide
lemma redLoop_cert_208 : redLoop 13573 16331503 100 20800 111078 = true := by decide
lemma iterP_cert_208 : iterP 100 111078 = 27668 := by decide
lemma redLoop_cert_209 : redLoop 13573 16331503 100 20900 27668 = true := by decide
lemma iterP_cert_209 : iterP 100 27668 = 58948 := by decide
lemma redLoop_cert_210 : redLoop 13573 16331503 100 21000 58948 = true := by decide
lemma iterP_cert_210 : iterP 100 58948 = 125512 := by decide
lemma redLoop_cert_211 : redLoop 13573 16331503 100 21100 125512 = true := by decide
lemma iterP_cert_211 : iterP 100 125512 = 89023 := by decide
lemma redLoop_cert_212 : redLoop 13573 16331503 100 21200 89023 = true := by decide
lemma iterP_cert_212 : iterP 100 89023 = 90224 := by decide
lemma redLoop_cert_213 : redLoop 13573 16331503 100 21300 90224 = true := by decide
lemma iterP_cert_213 : iterP 100 90224 = 24061 := by decide
lemma redLoop_cert_214 : redLoop 13573 16331503 100 21400 24061 = true := by decide
lemma iterP_cert_214 : iterP 100 24061 = 89422 := by decide
lemma redLoop_cert_215 : redLoop 13573 16331503 100 21500 89422 = true := by decide
lemma iterP_cert_215 : iterP 100 89422 = 103860 := by decide
lemma redLoop_cert_216 : redLoop 13573 16331503 100 21600 103860 = true := by decide
lemma iterP_cert_216 : iterP 100 103860 = 58144 := by decide
lemma redLoop_cert_217 : redLoop 13573 16331503 100 21700 58144 = true := by decide
lemma iterP_cert_217 : iterP 100 58144 = 52532 := by decide
lemma redLoop_cert_218 : redLoop 13573 16331503 100 21800 52532 = true := by decide
lemma iterP_cert_218 : iterP 100 52532 = 76189 := by decide
lemma redLoop_cert_219 : redLoop 13573 16331503 100 21900 76189 = true := by decide
lemma iterP_cert_219 : iterP 100 76189 = 113885 := by decide
lemma redLoop_cert_220 : redLoop 13573 16331503 100 22000 113885 = true := by decide
lemma iterP_cert_220 : iterP 100 113885 = 92229 := by decide
lemma redLoop_cert_221 : redLoop 13573 16331503 100 22100 92229 = true := by decide
lemma iterP_cert_221 : iterP 100 92229 = 30878 := by decide
lemma redLoop_cert_222 : redLoop 13573 16331503 100 22200 30878 = true := by decide
lemma iterP_cert_222 : iterP 100 30878 = 30074 := by decide
lemma redLoop_cert_223 : redLoop 13573 16331503 100 22300 30074 = true := by decide
lemma iterP_cert_223 : iterP 100 30074 = 94637 := by decide
lemma redLoop_cert_224 : redLoop 13573 16331503 100 22400 94637 = true := by decide
lemma iterP_cert_224 : iterP 100 94637 = 81803 := by decide
lemma redLoop_cert_225 : redLoop 13573 16331503 100 22500 81803 = true := by decide
lemma iterP_cert_225 : iterP 100 81803 = 105464 := by decide
lemma redLoop_cert_226 : redLoop 13573 16331503 100 22600 105464 = true := by decide
lemma iterP_cert_226 : iterP 100 105464 = 36089 := by decide
lemma redLoop_cert_227 : redLoop 13573 16331503 100 22700 36089 = true := by decide
lemma iterP_cert_227 : iterP 100 36089 = 115088 := by decide
lemma redLoop_cert_228 : redLoop 13573 16331503 100 22800 115088 = true := by decide
lemma iterP_cert_228 : iterP 100 115088 = 41302 := by decide
lemma redLoop_cert_229 : redLoop 13573 16331503 100 22900 41302 = true := by decide
lemma iterP_cert_229 : iterP 100 41302 = 77795 := by decide
lemma redLoop_cert_230 : redLoop 13573 16331503 100 23000 77795 = true := by decide
lemma iterP_cert_230 : iterP 100 77795 = 107066 := by decide
lemma redLoop_cert_231 : redLoop 13573 16331503 100 23100 107066 = true := by decide
lemma iterP_cert_231 : iterP 100 107066 = 136341 := by decide
lemma redLoop_cert_232 : redLoop 13573 16331503 100 23200 136341 = true := by decide
lemma iterP_cert_232 : iterP 100 136341 = 58545 := by decide
lemma redLoop_cert_233 : redLoop 13573 16331503 100 23300 58545 = true := by decide
lemma iterP_cert_233 : iterP 100 58545 = 81404 := by decide
lemma redLoop_cert_234 : redLoop 13573 16331503 100 23400 81404 = true := by decide
lemma iterP_cert_234 : iterP 100 81404 = 91828 := by decide
lemma redLoop_cert_235 : redLoop 13573 16331503 100 23500 91828 = true := by decide
lemma iterP_cert_235 : iterP 100 91828 = 2006 := by decide
lemma redLoop_cert_236 : redLoop 13573 16331503 100 23600 2006 = true := by decide
lemma iterP_cert_236 : iterP 100 2006 = 14435 := by decide
lemma redLoop_cert_237 : redLoop 13573 16331503 100 23700 14435 = true := by decide
lemma iterP_cert_237 : iterP 100 14435 = 68973 := by decide
lemma redLoop_cert_238 : redLoop 13573 16331503 100 23800 68973 = true := by decide
lemma iterP_cert_238 : iterP 100 68973 = 22054 := by decide
lemma redLoop_cert_239 : redLoop 13573 16331503 100 23900 22054 = true := by decide
lemma iterP_cert_239 : iterP 100 22054 = 67369 := by decide
lemma redLoop_cert_240 : redLoop 13573 16331503 100 24000 67369 = true := by decide
lemma iterP_cert_240 : iterP 100 67369 = 44109 := by decide
lemma redLoop_cert_241 : redLoop 13573 16331503 100 24100 44109 = true := by decide
lemma iterP_cert_241 : iterP 100 44109 = 4813 := by decide
lemma redLoop_cert_242 : redLoop 13573 16331503 100 24200 4813 = true := by decide
lemma iterP_cert_242 : iterP 100 4813 = 78996 := by decide
lemma redLoop_cert_243 : redLoop 13573 16331503 100 24300 78996 = true := by decide
lemma iterP_cert_243 : iterP 100 78996 = 40903 := by decide
lemma redLoop_cert_244 : redLoop 13573 16331503 100 24400 40903 = true := by decide
lemma iterP_cert_244 : iterP 100 40903 = 64159 := by decide
lemma redLoop_cert_245 : redLoop 13573 16331503 100 24500 64159 = true := by decide
lemma iterP_cert_245 : iterP 100 64159 = 72983 := by decide
lemma redLoop_cert_246 : redLoop 13573 16331503 100 24600 72983 = true := by decide
lemma iterP_cert_246 : iterP 100 72983 = 35688 := by decide
lemma redLoop_cert_247 : redLoop 13573 16331503 100 24700 35688 = true := by decide
lemma iterP_cert_247 : iterP 100 35688 = 86216 := by decide
lemma redLoop_cert_248 : redLoop 13573 16331503 100 24800 86216 = true := by decide
lemma iterP_cert_248 : iterP 100 86216 = 25663 := by decide
lemma redLoop_cert_249 : redLoop 13573 16331503 100 24900 25663 = true := by decide
lemma iterP_cert_249 : iterP 100 25663 = 52131 := by decide
lemma redLoop_cert_250 : redLoop 13573 16331503 100 25000 52131 = true := by decide
lemma iterP_cert_250 : iterP 100 52131 = 47317 := by decide
lemma redLoop_cert_251 : redLoop 13573 16331503 100 25100 47317 = true := by decide
lemma iterP_cert_251 : iterP 100 47317 = 98246 := by decide
lemma redLoop_cert_252 : redLoop 13573 16331503 100 25200 98246 = true := by decide
lemma iterP_cert_252 : iterP 100 98246 = 66565 := by decide
lemma redLoop_cert_253 : redLoop 13573 16331503 100 25300 66565 = true := by decide
lemma iterP_cert_253 : iterP 100 66565 = 108672 := by decide
lemma redLoop_cert_254 : redLoop 13573 16331503 100 25400 108672 = true := by decide
lemma iterP_cert_254 : iterP 100 108672 = 129522 := by decide
lemma redLoop_cert_255 : redLoop 13573 16331503 100 25500 129522 = true := by decide
lemma iterP_cert_255 : iterP 100 129522 = 102657 := by decide
lemma redLoop_cert_256 : redLoop 13573 16331503 100 25600 102657 = true := by decide
lemma iterP_cert_256 : iterP 100 102657 = 109071 := by decide
lemma redLoop_cert_257 : redLoop 13573 16331503 100 25700 109071 = true := by decide
lemma iterP_cert_257 : iterP 100 109071 = 5615 := by decide
lemma redLoop_cert_258 : redLoop 13573 16331503 100 25800 5615 = true := by decide
lemma iterP_cert_258 : iterP 100 5615 = 136740 := by decide
lemma redLoop_cert_259 : redLoop 13573 16331503 100 25900 136740 = true := by decide
lemma iterP_cert_259 : iterP 100 136740 = 72181 := by decide
lemma redLoop_cert_260 : redLoop 13573 16331503 100 26000 72181 = true := by decide
lemma iterP_cert_260 : iterP 100 72181 = 115487 := by decide
lemma redLoop_cert_261 : redLoop 13573 16331503 100 26100 115487 = true := by decide
lemma iterP_cert_261 : iterP 100 115487 = 54938 := by decide
lemma redLoop_cert_262 : redLoop 13573 16331503 100 26200 54938 = true := by decide
lemma iterP_cert_262 : iterP 100 54938 = 111878 := by decide
lemma redLoop_cert_263 : redLoop 13573 16331503 100 26300 111878 = true := by decide
lemma iterP_cert_263 : iterP 100 111878 = 70176 := by decide
lemma redLoop_cert_264 : redLoop 13573 16331503 100 26400 70176 = true := by decide
lemma iterP_cert_264 : iterP 100 70176 = 108670 := by decide
lemma redLoop_cert_265 : redLoop 13573 16331503 100 26500 108670 = true := by decide
lemma iterP_cert_265 : iterP 100 108670 = 114286 := by decide
lemma redLoop_cert_266 : redLoop 13573 16331503 100 26600 114286 = true := by decide
lemma iterP_cert_266 : iterP 100 114286 = 121101 := by decide
lemma redLoop_cert_267 : redLoop 13573 16331503 100 26700 121101 = true := by decide
lemma iterP_cert_267 : iterP 100 121101 = 46517 := by decide
lemma redLoop_cert_268 : redLoop 13573 16331503 100 26800 46517 = true := by decide
lemma iterP_cert_268 : iterP 100 46517 = 55738 := by decide
lemma redLoop_cert_269 : redLoop 13573 16331503 100 26900 55738 = true := by decide
lemma iterP_cert_269 : iterP 100 55738 = 16843 := by decide
lemma redLoop_cert_270 : redLoop 13573 16331503 100 27000 16843 = true := by decide
lemma iterP_cert_270 : iterP 100 16843 = 119898 := by decide
lemma redLoop_cert_271 : redLoop 13573 16331503 100 27100 119898 = true := by decide
lemma iterP_cert_271 : iterP 100 119898 = 97444 := by decide
lemma redLoop_cert_272 : redLoop 13573 16331503 100 27200 97444 = true := by decide
lemma iterP_cert_272 : iterP 100 97444 = 8821 := by decide
lemma redLoop_cert_273 : redLoop 13573 16331503 100 27300 8821 = true := by decide
lemma iterP_cert_273 : iterP 100 8821 = 77394 := by decide
lemma redLoop_cert_274 : redLoop 13573 16331503 100 27400 77394 = true := by decide
lemma iterP_cert_274 : iterP 100 77394 = 78194 := by decide
lemma redLoop_cert_275 : redLoop 13573 16331503 100 27500 78194 = true := by decide
lemma iterP_cert_275 : iterP 100 78194 = 120702 := by decide
lemma redLoop_cert_276 : redLoop 13573 16331503 100 27600 120702 = true := by decide
lemma iterP_cert_276 : iterP 100 120702 = 32881 := by decide
lemma redLoop_cert_277 : redLoop 13573 16331503 100 27700 32881 = true := by decide
lemma iterP_cert_277 : iterP 100 32881 = 21655 := by decide
lemma redLoop_cert_278 : redLoop 13573 16331503 100 27800 21655 = true := by decide
lemma iterP_cert_278 : iterP 100 21655 = 53733 := by decide
lemma redLoop_cert_279 : redLoop 13573 16331503 100 27900 53733 = true := by decide
lemma iterP_cert_279 : iterP 100 53733 = 10026 := by decide
lemma redLoop_cert_280 : redLoop 13573 16331503 100 28000 10026 = true := by decide
lemma iterP_cert_280 : iterP 100 10026 = 41703 := by decide
lemma redLoop_cert_281 : redLoop 13573 16331503 100 28100 41703 = true := by decide
lemma iterP_cert_281 : iterP 100 41703 = 106667 := by decide
lemma redLoop_cert_282 : redLoop 13573 16331503 100 28200 106667 = true := by decide
lemma iterP_cert_282 : iterP 100 106667 = 122705 := by decide
lemma redLoop_cert_283 : redLoop 13573 16331503 100 28300 122705 = true := by decide
lemma iterP_cert_283 : iterP 100 122705 = 24462 := by decide
lemma redLoop_cert_284 : redLoop 13573 16331503 100 28400 24462 = true := by decide
lemma iterP_cert_284 : iterP 100 24462 = 118294 := by decide
lemma redLoop_cert_285 : redLoop 13573 16331503 100 28500 118294 = true := by decide
lemma iterP_cert_285 : iterP 100 118294 = 119499 := by decide
lemma redLoop_cert_286 : redLoop 13573 16331503 100 28600 119499 = true := by decide
lemma iterP_cert_286 : iterP 100 119499 = 83808 := by decide
lemma redLoop_cert_287 : redLoop 13573 16331503 100 28700 83808 = true := by decide
lemma iterP_cert_287 : iterP 100 83808 = 112281 := by decide
lemma redLoop_cert_288 : redLoop 13573 16331503 100 28800 112281 = true := by decide
lemma iterP_cert_288 : iterP 100 112281 = 114284 := by decide
lemma redLoop_cert_289 : redLoop 13573 16331503 100 28900 114284 = true := by decide
lemma iterP_cert_289 : iterP 100 114284 = 105865 := by decide
lemma redLoop_cert_290 : redLoop 13573 16331503 100 29000 105865 = true := by decide
lemma iterP_cert_290 : iterP 100 105865 = 64961 := by decide
lemma redLoop_cert_291 : redLoop 13573 16331503 100 29100 64961 = true := by decide
lemma iterP_cert_291 : iterP 100 64961 = 130727 := by decide
lemma redLoop_cert_292 : redLoop 13573 16331503 100 29200 130727 = true := by decide
lemma iterP_cert_292 : iterP 100 130727 = 66966 := by decide
lemma redLoop_cert_293 : redLoop 13573 16331503 100 29300 66966 = true := by decide

lemma redLoop_cert : redLoop 13573 16331503 29400 0 1 = true := by
  rw [show 29400 = 100 + 29300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_000, iterP_cert_000]
  simp
  rw [show 29300 = 100 + 29200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_001, iterP_cert_001]
  simp
  rw [show 29200 = 100 + 29100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_002, iterP_cert_002]
  simp
  rw [show 29100 = 100 + 29000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_003, iterP_cert_003]
  simp
  rw [show 29000 = 100 + 28900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_004, iterP_cert_004]
  simp
  rw [show 28900 = 100 + 28800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_005, iterP_cert_005]
  simp
  rw [show 28800 = 100 + 28700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_006, iterP_cert_006]
  simp
  rw [show 28700 = 100 + 28600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_007, iterP_cert_007]
  simp
  rw [show 28600 = 100 + 28500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_008, iterP_cert_008]
  simp
  rw [show 28500 = 100 + 28400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_009, iterP_cert_009]
  simp
  rw [show 28400 = 100 + 28300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_010, iterP_cert_010]
  simp
  rw [show 28300 = 100 + 28200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_011, iterP_cert_011]
  simp
  rw [show 28200 = 100 + 28100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_012, iterP_cert_012]
  simp
  rw [show 28100 = 100 + 28000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_013, iterP_cert_013]
  simp
  rw [show 28000 = 100 + 27900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_014, iterP_cert_014]
  simp
  rw [show 27900 = 100 + 27800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_015, iterP_cert_015]
  simp
  rw [show 27800 = 100 + 27700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_016, iterP_cert_016]
  simp
  rw [show 27700 = 100 + 27600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_017, iterP_cert_017]
  simp
  rw [show 27600 = 100 + 27500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_018, iterP_cert_018]
  simp
  rw [show 27500 = 100 + 27400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_019, iterP_cert_019]
  simp
  rw [show 27400 = 100 + 27300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_020, iterP_cert_020]
  simp
  rw [show 27300 = 100 + 27200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_021, iterP_cert_021]
  simp
  rw [show 27200 = 100 + 27100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_022, iterP_cert_022]
  simp
  rw [show 27100 = 100 + 27000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_023, iterP_cert_023]
  simp
  rw [show 27000 = 100 + 26900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_024, iterP_cert_024]
  simp
  rw [show 26900 = 100 + 26800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_025, iterP_cert_025]
  simp
  rw [show 26800 = 100 + 26700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_026, iterP_cert_026]
  simp
  rw [show 26700 = 100 + 26600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_027, iterP_cert_027]
  simp
  rw [show 26600 = 100 + 26500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_028, iterP_cert_028]
  simp
  rw [show 26500 = 100 + 26400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_029, iterP_cert_029]
  simp
  rw [show 26400 = 100 + 26300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_030, iterP_cert_030]
  simp
  rw [show 26300 = 100 + 26200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_031, iterP_cert_031]
  simp
  rw [show 26200 = 100 + 26100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_032, iterP_cert_032]
  simp
  rw [show 26100 = 100 + 26000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_033, iterP_cert_033]
  simp
  rw [show 26000 = 100 + 25900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_034, iterP_cert_034]
  simp
  rw [show 25900 = 100 + 25800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_035, iterP_cert_035]
  simp
  rw [show 25800 = 100 + 25700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_036, iterP_cert_036]
  simp
  rw [show 25700 = 100 + 25600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_037, iterP_cert_037]
  simp
  rw [show 25600 = 100 + 25500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_038, iterP_cert_038]
  simp
  rw [show 25500 = 100 + 25400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_039, iterP_cert_039]
  simp
  rw [show 25400 = 100 + 25300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_040, iterP_cert_040]
  simp
  rw [show 25300 = 100 + 25200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_041, iterP_cert_041]
  simp
  rw [show 25200 = 100 + 25100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_042, iterP_cert_042]
  simp
  rw [show 25100 = 100 + 25000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_043, iterP_cert_043]
  simp
  rw [show 25000 = 100 + 24900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_044, iterP_cert_044]
  simp
  rw [show 24900 = 100 + 24800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_045, iterP_cert_045]
  simp
  rw [show 24800 = 100 + 24700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_046, iterP_cert_046]
  simp
  rw [show 24700 = 100 + 24600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_047, iterP_cert_047]
  simp
  rw [show 24600 = 100 + 24500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_048, iterP_cert_048]
  simp
  rw [show 24500 = 100 + 24400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_049, iterP_cert_049]
  simp
  rw [show 24400 = 100 + 24300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_050, iterP_cert_050]
  simp
  rw [show 24300 = 100 + 24200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_051, iterP_cert_051]
  simp
  rw [show 24200 = 100 + 24100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_052, iterP_cert_052]
  simp
  rw [show 24100 = 100 + 24000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_053, iterP_cert_053]
  simp
  rw [show 24000 = 100 + 23900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_054, iterP_cert_054]
  simp
  rw [show 23900 = 100 + 23800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_055, iterP_cert_055]
  simp
  rw [show 23800 = 100 + 23700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_056, iterP_cert_056]
  simp
  rw [show 23700 = 100 + 23600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_057, iterP_cert_057]
  simp
  rw [show 23600 = 100 + 23500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_058, iterP_cert_058]
  simp
  rw [show 23500 = 100 + 23400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_059, iterP_cert_059]
  simp
  rw [show 23400 = 100 + 23300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_060, iterP_cert_060]
  simp
  rw [show 23300 = 100 + 23200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_061, iterP_cert_061]
  simp
  rw [show 23200 = 100 + 23100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_062, iterP_cert_062]
  simp
  rw [show 23100 = 100 + 23000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_063, iterP_cert_063]
  simp
  rw [show 23000 = 100 + 22900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_064, iterP_cert_064]
  simp
  rw [show 22900 = 100 + 22800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_065, iterP_cert_065]
  simp
  rw [show 22800 = 100 + 22700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_066, iterP_cert_066]
  simp
  rw [show 22700 = 100 + 22600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_067, iterP_cert_067]
  simp
  rw [show 22600 = 100 + 22500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_068, iterP_cert_068]
  simp
  rw [show 22500 = 100 + 22400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_069, iterP_cert_069]
  simp
  rw [show 22400 = 100 + 22300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_070, iterP_cert_070]
  simp
  rw [show 22300 = 100 + 22200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_071, iterP_cert_071]
  simp
  rw [show 22200 = 100 + 22100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_072, iterP_cert_072]
  simp
  rw [show 22100 = 100 + 22000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_073, iterP_cert_073]
  simp
  rw [show 22000 = 100 + 21900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_074, iterP_cert_074]
  simp
  rw [show 21900 = 100 + 21800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_075, iterP_cert_075]
  simp
  rw [show 21800 = 100 + 21700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_076, iterP_cert_076]
  simp
  rw [show 21700 = 100 + 21600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_077, iterP_cert_077]
  simp
  rw [show 21600 = 100 + 21500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_078, iterP_cert_078]
  simp
  rw [show 21500 = 100 + 21400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_079, iterP_cert_079]
  simp
  rw [show 21400 = 100 + 21300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_080, iterP_cert_080]
  simp
  rw [show 21300 = 100 + 21200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_081, iterP_cert_081]
  simp
  rw [show 21200 = 100 + 21100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_082, iterP_cert_082]
  simp
  rw [show 21100 = 100 + 21000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_083, iterP_cert_083]
  simp
  rw [show 21000 = 100 + 20900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_084, iterP_cert_084]
  simp
  rw [show 20900 = 100 + 20800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_085, iterP_cert_085]
  simp
  rw [show 20800 = 100 + 20700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_086, iterP_cert_086]
  simp
  rw [show 20700 = 100 + 20600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_087, iterP_cert_087]
  simp
  rw [show 20600 = 100 + 20500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_088, iterP_cert_088]
  simp
  rw [show 20500 = 100 + 20400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_089, iterP_cert_089]
  simp
  rw [show 20400 = 100 + 20300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_090, iterP_cert_090]
  simp
  rw [show 20300 = 100 + 20200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_091, iterP_cert_091]
  simp
  rw [show 20200 = 100 + 20100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_092, iterP_cert_092]
  simp
  rw [show 20100 = 100 + 20000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_093, iterP_cert_093]
  simp
  rw [show 20000 = 100 + 19900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_094, iterP_cert_094]
  simp
  rw [show 19900 = 100 + 19800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_095, iterP_cert_095]
  simp
  rw [show 19800 = 100 + 19700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_096, iterP_cert_096]
  simp
  rw [show 19700 = 100 + 19600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_097, iterP_cert_097]
  simp
  rw [show 19600 = 100 + 19500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_098, iterP_cert_098]
  simp
  rw [show 19500 = 100 + 19400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_099, iterP_cert_099]
  simp
  rw [show 19400 = 100 + 19300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_100, iterP_cert_100]
  simp
  rw [show 19300 = 100 + 19200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_101, iterP_cert_101]
  simp
  rw [show 19200 = 100 + 19100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_102, iterP_cert_102]
  simp
  rw [show 19100 = 100 + 19000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_103, iterP_cert_103]
  simp
  rw [show 19000 = 100 + 18900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_104, iterP_cert_104]
  simp
  rw [show 18900 = 100 + 18800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_105, iterP_cert_105]
  simp
  rw [show 18800 = 100 + 18700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_106, iterP_cert_106]
  simp
  rw [show 18700 = 100 + 18600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_107, iterP_cert_107]
  simp
  rw [show 18600 = 100 + 18500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_108, iterP_cert_108]
  simp
  rw [show 18500 = 100 + 18400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_109, iterP_cert_109]
  simp
  rw [show 18400 = 100 + 18300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_110, iterP_cert_110]
  simp
  rw [show 18300 = 100 + 18200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_111, iterP_cert_111]
  simp
  rw [show 18200 = 100 + 18100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_112, iterP_cert_112]
  simp
  rw [show 18100 = 100 + 18000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_113, iterP_cert_113]
  simp
  rw [show 18000 = 100 + 17900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_114, iterP_cert_114]
  simp
  rw [show 17900 = 100 + 17800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_115, iterP_cert_115]
  simp
  rw [show 17800 = 100 + 17700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_116, iterP_cert_116]
  simp
  rw [show 17700 = 100 + 17600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_117, iterP_cert_117]
  simp
  rw [show 17600 = 100 + 17500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_118, iterP_cert_118]
  simp
  rw [show 17500 = 100 + 17400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_119, iterP_cert_119]
  simp
  rw [show 17400 = 100 + 17300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_120, iterP_cert_120]
  simp
  rw [show 17300 = 100 + 17200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_121, iterP_cert_121]
  simp
  rw [show 17200 = 100 + 17100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_122, iterP_cert_122]
  simp
  rw [show 17100 = 100 + 17000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_123, iterP_cert_123]
  simp
  rw [show 17000 = 100 + 16900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_124, iterP_cert_124]
  simp
  rw [show 16900 = 100 + 16800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_125, iterP_cert_125]
  simp
  rw [show 16800 = 100 + 16700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_126, iterP_cert_126]
  simp
  rw [show 16700 = 100 + 16600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_127, iterP_cert_127]
  simp
  rw [show 16600 = 100 + 16500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_128, iterP_cert_128]
  simp
  rw [show 16500 = 100 + 16400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_129, iterP_cert_129]
  simp
  rw [show 16400 = 100 + 16300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_130, iterP_cert_130]
  simp
  rw [show 16300 = 100 + 16200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_131, iterP_cert_131]
  simp
  rw [show 16200 = 100 + 16100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_132, iterP_cert_132]
  simp
  rw [show 16100 = 100 + 16000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_133, iterP_cert_133]
  simp
  rw [show 16000 = 100 + 15900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_134, iterP_cert_134]
  simp
  rw [show 15900 = 100 + 15800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_135, iterP_cert_135]
  simp
  rw [show 15800 = 100 + 15700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_136, iterP_cert_136]
  simp
  rw [show 15700 = 100 + 15600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_137, iterP_cert_137]
  simp
  rw [show 15600 = 100 + 15500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_138, iterP_cert_138]
  simp
  rw [show 15500 = 100 + 15400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_139, iterP_cert_139]
  simp
  rw [show 15400 = 100 + 15300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_140, iterP_cert_140]
  simp
  rw [show 15300 = 100 + 15200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_141, iterP_cert_141]
  simp
  rw [show 15200 = 100 + 15100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_142, iterP_cert_142]
  simp
  rw [show 15100 = 100 + 15000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_143, iterP_cert_143]
  simp
  rw [show 15000 = 100 + 14900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_144, iterP_cert_144]
  simp
  rw [show 14900 = 100 + 14800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_145, iterP_cert_145]
  simp
  rw [show 14800 = 100 + 14700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_146, iterP_cert_146]
  simp
  rw [show 14700 = 100 + 14600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_147, iterP_cert_147]
  simp
  rw [show 14600 = 100 + 14500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_148, iterP_cert_148]
  simp
  rw [show 14500 = 100 + 14400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_149, iterP_cert_149]
  simp
  rw [show 14400 = 100 + 14300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_150, iterP_cert_150]
  simp
  rw [show 14300 = 100 + 14200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_151, iterP_cert_151]
  simp
  rw [show 14200 = 100 + 14100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_152, iterP_cert_152]
  simp
  rw [show 14100 = 100 + 14000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_153, iterP_cert_153]
  simp
  rw [show 14000 = 100 + 13900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_154, iterP_cert_154]
  simp
  rw [show 13900 = 100 + 13800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_155, iterP_cert_155]
  simp
  rw [show 13800 = 100 + 13700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_156, iterP_cert_156]
  simp
  rw [show 13700 = 100 + 13600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_157, iterP_cert_157]
  simp
  rw [show 13600 = 100 + 13500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_158, iterP_cert_158]
  simp
  rw [show 13500 = 100 + 13400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_159, iterP_cert_159]
  simp
  rw [show 13400 = 100 + 13300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_160, iterP_cert_160]
  simp
  rw [show 13300 = 100 + 13200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_161, iterP_cert_161]
  simp
  rw [show 13200 = 100 + 13100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_162, iterP_cert_162]
  simp
  rw [show 13100 = 100 + 13000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_163, iterP_cert_163]
  simp
  rw [show 13000 = 100 + 12900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_164, iterP_cert_164]
  simp
  rw [show 12900 = 100 + 12800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_165, iterP_cert_165]
  simp
  rw [show 12800 = 100 + 12700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_166, iterP_cert_166]
  simp
  rw [show 12700 = 100 + 12600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_167, iterP_cert_167]
  simp
  rw [show 12600 = 100 + 12500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_168, iterP_cert_168]
  simp
  rw [show 12500 = 100 + 12400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_169, iterP_cert_169]
  simp
  rw [show 12400 = 100 + 12300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_170, iterP_cert_170]
  simp
  rw [show 12300 = 100 + 12200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_171, iterP_cert_171]
  simp
  rw [show 12200 = 100 + 12100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_172, iterP_cert_172]
  simp
  rw [show 12100 = 100 + 12000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_173, iterP_cert_173]
  simp
  rw [show 12000 = 100 + 11900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_174, iterP_cert_174]
  simp
  rw [show 11900 = 100 + 11800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_175, iterP_cert_175]
  simp
  rw [show 11800 = 100 + 11700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_176, iterP_cert_176]
  simp
  rw [show 11700 = 100 + 11600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_177, iterP_cert_177]
  simp
  rw [show 11600 = 100 + 11500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_178, iterP_cert_178]
  simp
  rw [show 11500 = 100 + 11400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_179, iterP_cert_179]
  simp
  rw [show 11400 = 100 + 11300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_180, iterP_cert_180]
  simp
  rw [show 11300 = 100 + 11200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_181, iterP_cert_181]
  simp
  rw [show 11200 = 100 + 11100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_182, iterP_cert_182]
  simp
  rw [show 11100 = 100 + 11000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_183, iterP_cert_183]
  simp
  rw [show 11000 = 100 + 10900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_184, iterP_cert_184]
  simp
  rw [show 10900 = 100 + 10800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_185, iterP_cert_185]
  simp
  rw [show 10800 = 100 + 10700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_186, iterP_cert_186]
  simp
  rw [show 10700 = 100 + 10600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_187, iterP_cert_187]
  simp
  rw [show 10600 = 100 + 10500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_188, iterP_cert_188]
  simp
  rw [show 10500 = 100 + 10400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_189, iterP_cert_189]
  simp
  rw [show 10400 = 100 + 10300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_190, iterP_cert_190]
  simp
  rw [show 10300 = 100 + 10200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_191, iterP_cert_191]
  simp
  rw [show 10200 = 100 + 10100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_192, iterP_cert_192]
  simp
  rw [show 10100 = 100 + 10000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_193, iterP_cert_193]
  simp
  rw [show 10000 = 100 + 9900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_194, iterP_cert_194]
  simp
  rw [show 9900 = 100 + 9800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_195, iterP_cert_195]
  simp
  rw [show 9800 = 100 + 9700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_196, iterP_cert_196]
  simp
  rw [show 9700 = 100 + 9600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_197, iterP_cert_197]
  simp
  rw [show 9600 = 100 + 9500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_198, iterP_cert_198]
  simp
  rw [show 9500 = 100 + 9400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_199, iterP_cert_199]
  simp
  rw [show 9400 = 100 + 9300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_200, iterP_cert_200]
  simp
  rw [show 9300 = 100 + 9200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_201, iterP_cert_201]
  simp
  rw [show 9200 = 100 + 9100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_202, iterP_cert_202]
  simp
  rw [show 9100 = 100 + 9000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_203, iterP_cert_203]
  simp
  rw [show 9000 = 100 + 8900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_204, iterP_cert_204]
  simp
  rw [show 8900 = 100 + 8800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_205, iterP_cert_205]
  simp
  rw [show 8800 = 100 + 8700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_206, iterP_cert_206]
  simp
  rw [show 8700 = 100 + 8600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_207, iterP_cert_207]
  simp
  rw [show 8600 = 100 + 8500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_208, iterP_cert_208]
  simp
  rw [show 8500 = 100 + 8400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_209, iterP_cert_209]
  simp
  rw [show 8400 = 100 + 8300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_210, iterP_cert_210]
  simp
  rw [show 8300 = 100 + 8200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_211, iterP_cert_211]
  simp
  rw [show 8200 = 100 + 8100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_212, iterP_cert_212]
  simp
  rw [show 8100 = 100 + 8000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_213, iterP_cert_213]
  simp
  rw [show 8000 = 100 + 7900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_214, iterP_cert_214]
  simp
  rw [show 7900 = 100 + 7800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_215, iterP_cert_215]
  simp
  rw [show 7800 = 100 + 7700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_216, iterP_cert_216]
  simp
  rw [show 7700 = 100 + 7600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_217, iterP_cert_217]
  simp
  rw [show 7600 = 100 + 7500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_218, iterP_cert_218]
  simp
  rw [show 7500 = 100 + 7400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_219, iterP_cert_219]
  simp
  rw [show 7400 = 100 + 7300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_220, iterP_cert_220]
  simp
  rw [show 7300 = 100 + 7200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_221, iterP_cert_221]
  simp
  rw [show 7200 = 100 + 7100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_222, iterP_cert_222]
  simp
  rw [show 7100 = 100 + 7000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_223, iterP_cert_223]
  simp
  rw [show 7000 = 100 + 6900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_224, iterP_cert_224]
  simp
  rw [show 6900 = 100 + 6800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_225, iterP_cert_225]
  simp
  rw [show 6800 = 100 + 6700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_226, iterP_cert_226]
  simp
  rw [show 6700 = 100 + 6600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_227, iterP_cert_227]
  simp
  rw [show 6600 = 100 + 6500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_228, iterP_cert_228]
  simp
  rw [show 6500 = 100 + 6400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_229, iterP_cert_229]
  simp
  rw [show 6400 = 100 + 6300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_230, iterP_cert_230]
  simp
  rw [show 6300 = 100 + 6200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_231, iterP_cert_231]
  simp
  rw [show 6200 = 100 + 6100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_232, iterP_cert_232]
  simp
  rw [show 6100 = 100 + 6000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_233, iterP_cert_233]
  simp
  rw [show 6000 = 100 + 5900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_234, iterP_cert_234]
  simp
  rw [show 5900 = 100 + 5800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_235, iterP_cert_235]
  simp
  rw [show 5800 = 100 + 5700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_236, iterP_cert_236]
  simp
  rw [show 5700 = 100 + 5600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_237, iterP_cert_237]
  simp
  rw [show 5600 = 100 + 5500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_238, iterP_cert_238]
  simp
  rw [show 5500 = 100 + 5400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_239, iterP_cert_239]
  simp
  rw [show 5400 = 100 + 5300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_240, iterP_cert_240]
  simp
  rw [show 5300 = 100 + 5200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_241, iterP_cert_241]
  simp
  rw [show 5200 = 100 + 5100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_242, iterP_cert_242]
  simp
  rw [show 5100 = 100 + 5000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_243, iterP_cert_243]
  simp
  rw [show 5000 = 100 + 4900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_244, iterP_cert_244]
  simp
  rw [show 4900 = 100 + 4800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_245, iterP_cert_245]
  simp
  rw [show 4800 = 100 + 4700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_246, iterP_cert_246]
  simp
  rw [show 4700 = 100 + 4600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_247, iterP_cert_247]
  simp
  rw [show 4600 = 100 + 4500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_248, iterP_cert_248]
  simp
  rw [show 4500 = 100 + 4400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_249, iterP_cert_249]
  simp
  rw [show 4400 = 100 + 4300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_250, iterP_cert_250]
  simp
  rw [show 4300 = 100 + 4200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_251, iterP_cert_251]
  simp
  rw [show 4200 = 100 + 4100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_252, iterP_cert_252]
  simp
  rw [show 4100 = 100 + 4000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_253, iterP_cert_253]
  simp
  rw [show 4000 = 100 + 3900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_254, iterP_cert_254]
  simp
  rw [show 3900 = 100 + 3800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_255, iterP_cert_255]
  simp
  rw [show 3800 = 100 + 3700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_256, iterP_cert_256]
  simp
  rw [show 3700 = 100 + 3600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_257, iterP_cert_257]
  simp
  rw [show 3600 = 100 + 3500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_258, iterP_cert_258]
  simp
  rw [show 3500 = 100 + 3400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_259, iterP_cert_259]
  simp
  rw [show 3400 = 100 + 3300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_260, iterP_cert_260]
  simp
  rw [show 3300 = 100 + 3200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_261, iterP_cert_261]
  simp
  rw [show 3200 = 100 + 3100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_262, iterP_cert_262]
  simp
  rw [show 3100 = 100 + 3000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_263, iterP_cert_263]
  simp
  rw [show 3000 = 100 + 2900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_264, iterP_cert_264]
  simp
  rw [show 2900 = 100 + 2800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_265, iterP_cert_265]
  simp
  rw [show 2800 = 100 + 2700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_266, iterP_cert_266]
  simp
  rw [show 2700 = 100 + 2600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_267, iterP_cert_267]
  simp
  rw [show 2600 = 100 + 2500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_268, iterP_cert_268]
  simp
  rw [show 2500 = 100 + 2400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_269, iterP_cert_269]
  simp
  rw [show 2400 = 100 + 2300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_270, iterP_cert_270]
  simp
  rw [show 2300 = 100 + 2200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_271, iterP_cert_271]
  simp
  rw [show 2200 = 100 + 2100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_272, iterP_cert_272]
  simp
  rw [show 2100 = 100 + 2000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_273, iterP_cert_273]
  simp
  rw [show 2000 = 100 + 1900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_274, iterP_cert_274]
  simp
  rw [show 1900 = 100 + 1800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_275, iterP_cert_275]
  simp
  rw [show 1800 = 100 + 1700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_276, iterP_cert_276]
  simp
  rw [show 1700 = 100 + 1600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_277, iterP_cert_277]
  simp
  rw [show 1600 = 100 + 1500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_278, iterP_cert_278]
  simp
  rw [show 1500 = 100 + 1400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_279, iterP_cert_279]
  simp
  rw [show 1400 = 100 + 1300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_280, iterP_cert_280]
  simp
  rw [show 1300 = 100 + 1200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_281, iterP_cert_281]
  simp
  rw [show 1200 = 100 + 1100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_282, iterP_cert_282]
  simp
  rw [show 1100 = 100 + 1000 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_283, iterP_cert_283]
  simp
  rw [show 1000 = 100 + 900 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_284, iterP_cert_284]
  simp
  rw [show 900 = 100 + 800 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_285, iterP_cert_285]
  simp
  rw [show 800 = 100 + 700 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_286, iterP_cert_286]
  simp
  rw [show 700 = 100 + 600 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_287, iterP_cert_287]
  simp
  rw [show 600 = 100 + 500 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_288, iterP_cert_288]
  simp
  rw [show 500 = 100 + 400 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_289, iterP_cert_289]
  simp
  rw [show 400 = 100 + 300 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_290, iterP_cert_290]
  simp
  rw [show 300 = 100 + 200 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_291, iterP_cert_291]
  simp
  rw [show 200 = 100 + 100 by norm_num]
  rw [redLoop_add]
  rw [redLoop_cert_292, iterP_cert_292]
  simp
  simpa using redLoop_cert_293


lemma iterP_cert_293 : iterP 100 66966 = 1 := by decide

lemma iterP_add (a b p : Nat) : iterP (a + b) p = iterP b (iterP a p) := by
  induction a generalizing p with
  | zero => simp [iterP]
  | succ a ih =>
      rw [Nat.succ_add]
      change iterP (a + b) ((2 * p) % q) = iterP b (iterP a ((2 * p) % q))
      exact ih ((2 * p) % q)

lemma order_mod_q_iter : iterP 29400 1 = 1 := by
  rw [show 29400 = 100 + 29300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_000]
  rw [show 29300 = 100 + 29200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_001]
  rw [show 29200 = 100 + 29100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_002]
  rw [show 29100 = 100 + 29000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_003]
  rw [show 29000 = 100 + 28900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_004]
  rw [show 28900 = 100 + 28800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_005]
  rw [show 28800 = 100 + 28700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_006]
  rw [show 28700 = 100 + 28600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_007]
  rw [show 28600 = 100 + 28500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_008]
  rw [show 28500 = 100 + 28400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_009]
  rw [show 28400 = 100 + 28300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_010]
  rw [show 28300 = 100 + 28200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_011]
  rw [show 28200 = 100 + 28100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_012]
  rw [show 28100 = 100 + 28000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_013]
  rw [show 28000 = 100 + 27900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_014]
  rw [show 27900 = 100 + 27800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_015]
  rw [show 27800 = 100 + 27700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_016]
  rw [show 27700 = 100 + 27600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_017]
  rw [show 27600 = 100 + 27500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_018]
  rw [show 27500 = 100 + 27400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_019]
  rw [show 27400 = 100 + 27300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_020]
  rw [show 27300 = 100 + 27200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_021]
  rw [show 27200 = 100 + 27100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_022]
  rw [show 27100 = 100 + 27000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_023]
  rw [show 27000 = 100 + 26900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_024]
  rw [show 26900 = 100 + 26800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_025]
  rw [show 26800 = 100 + 26700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_026]
  rw [show 26700 = 100 + 26600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_027]
  rw [show 26600 = 100 + 26500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_028]
  rw [show 26500 = 100 + 26400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_029]
  rw [show 26400 = 100 + 26300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_030]
  rw [show 26300 = 100 + 26200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_031]
  rw [show 26200 = 100 + 26100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_032]
  rw [show 26100 = 100 + 26000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_033]
  rw [show 26000 = 100 + 25900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_034]
  rw [show 25900 = 100 + 25800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_035]
  rw [show 25800 = 100 + 25700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_036]
  rw [show 25700 = 100 + 25600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_037]
  rw [show 25600 = 100 + 25500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_038]
  rw [show 25500 = 100 + 25400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_039]
  rw [show 25400 = 100 + 25300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_040]
  rw [show 25300 = 100 + 25200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_041]
  rw [show 25200 = 100 + 25100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_042]
  rw [show 25100 = 100 + 25000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_043]
  rw [show 25000 = 100 + 24900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_044]
  rw [show 24900 = 100 + 24800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_045]
  rw [show 24800 = 100 + 24700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_046]
  rw [show 24700 = 100 + 24600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_047]
  rw [show 24600 = 100 + 24500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_048]
  rw [show 24500 = 100 + 24400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_049]
  rw [show 24400 = 100 + 24300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_050]
  rw [show 24300 = 100 + 24200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_051]
  rw [show 24200 = 100 + 24100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_052]
  rw [show 24100 = 100 + 24000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_053]
  rw [show 24000 = 100 + 23900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_054]
  rw [show 23900 = 100 + 23800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_055]
  rw [show 23800 = 100 + 23700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_056]
  rw [show 23700 = 100 + 23600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_057]
  rw [show 23600 = 100 + 23500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_058]
  rw [show 23500 = 100 + 23400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_059]
  rw [show 23400 = 100 + 23300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_060]
  rw [show 23300 = 100 + 23200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_061]
  rw [show 23200 = 100 + 23100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_062]
  rw [show 23100 = 100 + 23000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_063]
  rw [show 23000 = 100 + 22900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_064]
  rw [show 22900 = 100 + 22800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_065]
  rw [show 22800 = 100 + 22700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_066]
  rw [show 22700 = 100 + 22600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_067]
  rw [show 22600 = 100 + 22500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_068]
  rw [show 22500 = 100 + 22400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_069]
  rw [show 22400 = 100 + 22300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_070]
  rw [show 22300 = 100 + 22200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_071]
  rw [show 22200 = 100 + 22100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_072]
  rw [show 22100 = 100 + 22000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_073]
  rw [show 22000 = 100 + 21900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_074]
  rw [show 21900 = 100 + 21800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_075]
  rw [show 21800 = 100 + 21700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_076]
  rw [show 21700 = 100 + 21600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_077]
  rw [show 21600 = 100 + 21500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_078]
  rw [show 21500 = 100 + 21400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_079]
  rw [show 21400 = 100 + 21300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_080]
  rw [show 21300 = 100 + 21200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_081]
  rw [show 21200 = 100 + 21100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_082]
  rw [show 21100 = 100 + 21000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_083]
  rw [show 21000 = 100 + 20900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_084]
  rw [show 20900 = 100 + 20800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_085]
  rw [show 20800 = 100 + 20700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_086]
  rw [show 20700 = 100 + 20600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_087]
  rw [show 20600 = 100 + 20500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_088]
  rw [show 20500 = 100 + 20400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_089]
  rw [show 20400 = 100 + 20300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_090]
  rw [show 20300 = 100 + 20200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_091]
  rw [show 20200 = 100 + 20100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_092]
  rw [show 20100 = 100 + 20000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_093]
  rw [show 20000 = 100 + 19900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_094]
  rw [show 19900 = 100 + 19800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_095]
  rw [show 19800 = 100 + 19700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_096]
  rw [show 19700 = 100 + 19600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_097]
  rw [show 19600 = 100 + 19500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_098]
  rw [show 19500 = 100 + 19400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_099]
  rw [show 19400 = 100 + 19300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_100]
  rw [show 19300 = 100 + 19200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_101]
  rw [show 19200 = 100 + 19100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_102]
  rw [show 19100 = 100 + 19000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_103]
  rw [show 19000 = 100 + 18900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_104]
  rw [show 18900 = 100 + 18800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_105]
  rw [show 18800 = 100 + 18700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_106]
  rw [show 18700 = 100 + 18600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_107]
  rw [show 18600 = 100 + 18500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_108]
  rw [show 18500 = 100 + 18400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_109]
  rw [show 18400 = 100 + 18300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_110]
  rw [show 18300 = 100 + 18200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_111]
  rw [show 18200 = 100 + 18100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_112]
  rw [show 18100 = 100 + 18000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_113]
  rw [show 18000 = 100 + 17900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_114]
  rw [show 17900 = 100 + 17800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_115]
  rw [show 17800 = 100 + 17700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_116]
  rw [show 17700 = 100 + 17600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_117]
  rw [show 17600 = 100 + 17500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_118]
  rw [show 17500 = 100 + 17400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_119]
  rw [show 17400 = 100 + 17300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_120]
  rw [show 17300 = 100 + 17200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_121]
  rw [show 17200 = 100 + 17100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_122]
  rw [show 17100 = 100 + 17000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_123]
  rw [show 17000 = 100 + 16900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_124]
  rw [show 16900 = 100 + 16800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_125]
  rw [show 16800 = 100 + 16700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_126]
  rw [show 16700 = 100 + 16600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_127]
  rw [show 16600 = 100 + 16500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_128]
  rw [show 16500 = 100 + 16400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_129]
  rw [show 16400 = 100 + 16300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_130]
  rw [show 16300 = 100 + 16200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_131]
  rw [show 16200 = 100 + 16100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_132]
  rw [show 16100 = 100 + 16000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_133]
  rw [show 16000 = 100 + 15900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_134]
  rw [show 15900 = 100 + 15800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_135]
  rw [show 15800 = 100 + 15700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_136]
  rw [show 15700 = 100 + 15600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_137]
  rw [show 15600 = 100 + 15500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_138]
  rw [show 15500 = 100 + 15400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_139]
  rw [show 15400 = 100 + 15300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_140]
  rw [show 15300 = 100 + 15200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_141]
  rw [show 15200 = 100 + 15100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_142]
  rw [show 15100 = 100 + 15000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_143]
  rw [show 15000 = 100 + 14900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_144]
  rw [show 14900 = 100 + 14800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_145]
  rw [show 14800 = 100 + 14700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_146]
  rw [show 14700 = 100 + 14600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_147]
  rw [show 14600 = 100 + 14500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_148]
  rw [show 14500 = 100 + 14400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_149]
  rw [show 14400 = 100 + 14300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_150]
  rw [show 14300 = 100 + 14200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_151]
  rw [show 14200 = 100 + 14100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_152]
  rw [show 14100 = 100 + 14000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_153]
  rw [show 14000 = 100 + 13900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_154]
  rw [show 13900 = 100 + 13800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_155]
  rw [show 13800 = 100 + 13700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_156]
  rw [show 13700 = 100 + 13600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_157]
  rw [show 13600 = 100 + 13500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_158]
  rw [show 13500 = 100 + 13400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_159]
  rw [show 13400 = 100 + 13300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_160]
  rw [show 13300 = 100 + 13200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_161]
  rw [show 13200 = 100 + 13100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_162]
  rw [show 13100 = 100 + 13000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_163]
  rw [show 13000 = 100 + 12900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_164]
  rw [show 12900 = 100 + 12800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_165]
  rw [show 12800 = 100 + 12700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_166]
  rw [show 12700 = 100 + 12600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_167]
  rw [show 12600 = 100 + 12500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_168]
  rw [show 12500 = 100 + 12400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_169]
  rw [show 12400 = 100 + 12300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_170]
  rw [show 12300 = 100 + 12200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_171]
  rw [show 12200 = 100 + 12100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_172]
  rw [show 12100 = 100 + 12000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_173]
  rw [show 12000 = 100 + 11900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_174]
  rw [show 11900 = 100 + 11800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_175]
  rw [show 11800 = 100 + 11700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_176]
  rw [show 11700 = 100 + 11600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_177]
  rw [show 11600 = 100 + 11500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_178]
  rw [show 11500 = 100 + 11400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_179]
  rw [show 11400 = 100 + 11300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_180]
  rw [show 11300 = 100 + 11200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_181]
  rw [show 11200 = 100 + 11100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_182]
  rw [show 11100 = 100 + 11000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_183]
  rw [show 11000 = 100 + 10900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_184]
  rw [show 10900 = 100 + 10800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_185]
  rw [show 10800 = 100 + 10700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_186]
  rw [show 10700 = 100 + 10600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_187]
  rw [show 10600 = 100 + 10500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_188]
  rw [show 10500 = 100 + 10400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_189]
  rw [show 10400 = 100 + 10300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_190]
  rw [show 10300 = 100 + 10200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_191]
  rw [show 10200 = 100 + 10100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_192]
  rw [show 10100 = 100 + 10000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_193]
  rw [show 10000 = 100 + 9900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_194]
  rw [show 9900 = 100 + 9800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_195]
  rw [show 9800 = 100 + 9700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_196]
  rw [show 9700 = 100 + 9600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_197]
  rw [show 9600 = 100 + 9500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_198]
  rw [show 9500 = 100 + 9400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_199]
  rw [show 9400 = 100 + 9300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_200]
  rw [show 9300 = 100 + 9200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_201]
  rw [show 9200 = 100 + 9100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_202]
  rw [show 9100 = 100 + 9000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_203]
  rw [show 9000 = 100 + 8900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_204]
  rw [show 8900 = 100 + 8800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_205]
  rw [show 8800 = 100 + 8700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_206]
  rw [show 8700 = 100 + 8600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_207]
  rw [show 8600 = 100 + 8500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_208]
  rw [show 8500 = 100 + 8400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_209]
  rw [show 8400 = 100 + 8300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_210]
  rw [show 8300 = 100 + 8200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_211]
  rw [show 8200 = 100 + 8100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_212]
  rw [show 8100 = 100 + 8000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_213]
  rw [show 8000 = 100 + 7900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_214]
  rw [show 7900 = 100 + 7800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_215]
  rw [show 7800 = 100 + 7700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_216]
  rw [show 7700 = 100 + 7600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_217]
  rw [show 7600 = 100 + 7500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_218]
  rw [show 7500 = 100 + 7400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_219]
  rw [show 7400 = 100 + 7300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_220]
  rw [show 7300 = 100 + 7200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_221]
  rw [show 7200 = 100 + 7100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_222]
  rw [show 7100 = 100 + 7000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_223]
  rw [show 7000 = 100 + 6900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_224]
  rw [show 6900 = 100 + 6800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_225]
  rw [show 6800 = 100 + 6700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_226]
  rw [show 6700 = 100 + 6600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_227]
  rw [show 6600 = 100 + 6500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_228]
  rw [show 6500 = 100 + 6400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_229]
  rw [show 6400 = 100 + 6300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_230]
  rw [show 6300 = 100 + 6200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_231]
  rw [show 6200 = 100 + 6100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_232]
  rw [show 6100 = 100 + 6000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_233]
  rw [show 6000 = 100 + 5900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_234]
  rw [show 5900 = 100 + 5800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_235]
  rw [show 5800 = 100 + 5700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_236]
  rw [show 5700 = 100 + 5600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_237]
  rw [show 5600 = 100 + 5500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_238]
  rw [show 5500 = 100 + 5400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_239]
  rw [show 5400 = 100 + 5300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_240]
  rw [show 5300 = 100 + 5200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_241]
  rw [show 5200 = 100 + 5100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_242]
  rw [show 5100 = 100 + 5000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_243]
  rw [show 5000 = 100 + 4900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_244]
  rw [show 4900 = 100 + 4800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_245]
  rw [show 4800 = 100 + 4700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_246]
  rw [show 4700 = 100 + 4600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_247]
  rw [show 4600 = 100 + 4500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_248]
  rw [show 4500 = 100 + 4400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_249]
  rw [show 4400 = 100 + 4300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_250]
  rw [show 4300 = 100 + 4200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_251]
  rw [show 4200 = 100 + 4100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_252]
  rw [show 4100 = 100 + 4000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_253]
  rw [show 4000 = 100 + 3900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_254]
  rw [show 3900 = 100 + 3800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_255]
  rw [show 3800 = 100 + 3700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_256]
  rw [show 3700 = 100 + 3600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_257]
  rw [show 3600 = 100 + 3500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_258]
  rw [show 3500 = 100 + 3400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_259]
  rw [show 3400 = 100 + 3300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_260]
  rw [show 3300 = 100 + 3200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_261]
  rw [show 3200 = 100 + 3100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_262]
  rw [show 3100 = 100 + 3000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_263]
  rw [show 3000 = 100 + 2900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_264]
  rw [show 2900 = 100 + 2800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_265]
  rw [show 2800 = 100 + 2700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_266]
  rw [show 2700 = 100 + 2600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_267]
  rw [show 2600 = 100 + 2500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_268]
  rw [show 2500 = 100 + 2400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_269]
  rw [show 2400 = 100 + 2300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_270]
  rw [show 2300 = 100 + 2200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_271]
  rw [show 2200 = 100 + 2100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_272]
  rw [show 2100 = 100 + 2000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_273]
  rw [show 2000 = 100 + 1900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_274]
  rw [show 1900 = 100 + 1800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_275]
  rw [show 1800 = 100 + 1700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_276]
  rw [show 1700 = 100 + 1600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_277]
  rw [show 1600 = 100 + 1500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_278]
  rw [show 1500 = 100 + 1400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_279]
  rw [show 1400 = 100 + 1300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_280]
  rw [show 1300 = 100 + 1200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_281]
  rw [show 1200 = 100 + 1100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_282]
  rw [show 1100 = 100 + 1000 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_283]
  rw [show 1000 = 100 + 900 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_284]
  rw [show 900 = 100 + 800 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_285]
  rw [show 800 = 100 + 700 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_286]
  rw [show 700 = 100 + 600 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_287]
  rw [show 600 = 100 + 500 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_288]
  rw [show 500 = 100 + 400 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_289]
  rw [show 400 = 100 + 300 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_290]
  rw [show 300 = 100 + 200 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_291]
  rw [show 200 = 100 + 100 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_292]
  rw [show 100 = 100 + 0 by norm_num]
  rw [iterP_add]
  rw [iterP_cert_293]
  simp [iterP]

lemma t_mul_L_mod_eq (t : Nat) : (t * 29400) % 137543 = ((t * 600) % 2807) * 49 := by
  have h1 : 29400 = 600 * 49 := by norm_num
  have h2 : 137543 = 2807 * 49 := by norm_num
  rw [h1, h2]
  rw [show t * (600 * 49) = (t * 600) * 49 by ring]
  rw [Nat.mul_mod_mul_right]

lemma pAfter_step2 (n p t : Nat) : pAfter n ((2 * p) % n) t = pAfter n p (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [pAfter, ih]

lemma pAfter_one_mod_q (k : Nat) : pAfter q (1 % q) k = 2 ^ k % q := by
  induction k with
  | zero => simp [pAfter]
  | succ k ih =>
      simp [pAfter, ih, Nat.pow_succ]
      rw [Nat.mul_comm]

lemma redLoop_sound (target m fuel r p i : Nat) :
    redLoop target m fuel r p = true → i < fuel →
      redOK target m (r+i) (pAfter q p i) = true := by
  induction fuel generalizing r p i with
  | zero => intro _ hi; omega
  | succ fuel ih =>
      intro h hi
      simp only [redLoop] at h
      have hok : redOK target m r p = true := by
        cases hro : redOK target m r p <;> simp [hro] at h
        rfl
      have htail : redLoop target m fuel (r+1) ((2*p)%q) = true := by
        cases hro : redOK target m r p <;> simp [hro] at h
        exact h
      by_cases hi0 : i = 0
      · subst hi0
        simpa [pAfter] using hok
      · have hi' : i - 1 < fuel := by omega
        have hres := ih (r+1) ((2*p)%q) (i-1) htail hi'
        have hp : pAfter q ((2*p)%q) (i-1) = pAfter q p i := by
          have hpos : i = (i-1)+1 := by omega
          rw [hpos]
          simpa using pAfter_step2 q p (i-1)
        have hr : r + 1 + (i - 1) = r + i := by omega
        simpa [hr, hp] using hres

lemma redOK_of_r (r : Nat) (hr : r < 29400) :
    redOK 13573 16331503 r (2 ^ r % q) = true := by
  have h := redLoop_sound 13573 16331503 29400 0 1 r redLoop_cert hr
  have hp : pAfter q 1 r = 2 ^ r % q := by
    have h1 : (1 % q) = 1 := by norm_num [q]
    simpa [h1] using pAfter_one_mod_q r
  simpa [hp] using h

lemma pow_mul_mod_one_ME {a r t m : Nat} (h : a^r ≡ 1 [MOD m]) : a^(r*t) ≡ 1 [MOD m] := by
  have hp := Nat.ModEq.pow t h
  simpa [pow_mul] using hp

lemma order_mod_q_nat : 2 ^ 29400 % 137543 = 1 := by
  have h343base : 2 ^ 294 % 343 = 1 := by decide
  have h401base : 2 ^ 200 % 401 = 1 := by decide
  have h343eq : 2 ^ 294 ≡ 1 [MOD 343] := by rw [Nat.ModEq]; simpa using h343base
  have h401eq : 2 ^ 200 ≡ 1 [MOD 401] := by rw [Nat.ModEq]; simpa using h401base
  have h343 : 2 ^ 29400 ≡ 1 [MOD 343] := by
    have := pow_mul_mod_one_ME (a:=2) (r:=294) (t:=100) (m:=343) h343eq
    norm_num at this ⊢; exact this
  have h401 : 2 ^ 29400 ≡ 1 [MOD 401] := by
    have := pow_mul_mod_one_ME (a:=2) (r:=200) (t:=147) (m:=401) h401eq
    norm_num at this ⊢; exact this
  have hcop : Nat.Coprime 343 401 := by norm_num [Nat.Coprime]
  have hq : 2 ^ 29400 ≡ 1 [MOD 343 * 401] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h343,h401⟩
  rw [Nat.ModEq] at hq
  norm_num at hq
  exact hq

lemma pow_period_mod_q_for_divmod (k r t : Nat) (hk : k = t * 29400 + r) :
    2 ^ k ≡ 2 ^ r [MOD q] := by
  have horder : 2 ^ 29400 ≡ 1 [MOD q] := by
    rw [Nat.ModEq]
    simpa [q] using order_mod_q_nat
  have hper : 2 ^ (t * 29400) ≡ 1 [MOD q] := by
    have h := pow_mul_mod_one_ME (a:=2) (r:=29400) (t:=t) (m:=q) horder
    simpa [Nat.mul_comm] using h
  subst hk
  rw [show t * 29400 + r = r + t * 29400 by omega]
  rw [pow_add]
  have hmul := (Nat.ModEq.refl (2^r)).mul hper
  simpa using hmul


lemma redDiff_add_mod (target r p : Nat) :
    (redDiff target r p + (r % q + target % q)) % q = p % q := by
  rw [redDiff]
  rw [Nat.mod_add_mod]
  have hqpos : 0 < q := by norm_num [q]
  have hrlt : r % q < q := Nat.mod_lt _ hqpos
  have htlt : target % q < q := Nat.mod_lt _ hqpos
  have heq : (p + q - r % q + q - target % q + (r % q + target % q)) = p + 2*q := by omega
  rw [heq]
  rw [show p + 2 * q = p + q * 2 by omega]
  rw [Nat.add_mul_mod_self_left]

lemma pow_two_mod_four_zero (k : Nat) (hk : 2 ≤ k) : 2 ^ k % 4 = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := by exists k-2; omega
  rw [show 2 ^ (j + 2) = 4 * 2 ^ j by ring]
  exact Nat.mul_mod_right 4 (2^j)

lemma inv600_apply (t : Nat) (ht : t < 2807) : (((t * 600) % 2807) * 2138) % 2807 = t := by
  have hcong : ((t * 600) % 2807 * 2138) ≡ (t * (600 * 2138)) [MOD 2807] := by
    have hA : (t * 600) % 2807 ≡ t * 600 [MOD 2807] := Nat.mod_modEq _ _
    have hB : 2138 ≡ 2138 [MOD 2807] := Nat.ModEq.refl _
    simpa [Nat.mul_assoc] using hA.mul hB
  rw [Nat.ModEq] at hcong
  rw [hcong]
  rw [show 600 * 2138 = 1 + 2807 * 457 by norm_num]
  rw [show t * (1 + 2807 * 457) = t + 2807 * (t*457) by ring]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt ht

lemma miss_witness_reduced :
  ∀ k, 1 ≤ k → k ≤ 16331503 → ¬ ((2 ^ k - k) ≡ 13573 [MOD 550172]) := by
  intro k hkpos hkmax hhit
  by_cases hkone : k = 1
  · subst k
    norm_num [Nat.ModEq] at hhit
  · have hk2 : 2 ≤ k := by omega
    let r := k % 29400
    let t := k / 29400
    let p := 2 ^ r % q
    let d := redDiff 13573 r p
    have hr : r < 29400 := by
      dsimp [r]
      exact Nat.mod_lt _ (by norm_num)
    have ht : t < 2807 := by
      dsimp [t]
      apply Nat.div_lt_of_lt_mul
      omega
    have hkdecomp : k = t * 29400 + r := by
      dsimp [t, r]
      have h := Nat.div_add_mod' k 29400
      omega
    have hge : k ≤ 2 ^ k := self_le_two_pow k
    have hpowM : 2 ^ k ≡ 13573 + k [MOD 550172] := by
      have h := hhit.add_right k
      convert h using 1
      omega
    have hpow4eq : (13573 + k) % 4 = 0 := by
      have h4 : 2 ^ k ≡ 13573 + k [MOD 4] := Nat.ModEq.of_dvd (by norm_num) hpowM
      rw [Nat.ModEq] at h4
      rw [pow_two_mod_four_zero k hk2] at h4
      exact h4.symm
    have hmod4 : (13573 + r) % 4 = 0 := by
      have hkr : (13573 + k) % 4 = (13573 + r) % 4 := by
        rw [hkdecomp]
        rw [show 13573 + (t * 29400 + r) = (13573 + r) + 4 * (t * 7350) by omega]
        rw [Nat.add_mul_mod_self_left]
      rwa [hkr] at hpow4eq
    have hper : 2 ^ k ≡ 2 ^ r [MOD q] := pow_period_mod_q_for_divmod k r t hkdecomp
    have hpowq0 : 2 ^ r ≡ 13573 + k [MOD q] := by
      exact hper.symm.trans (Nat.ModEq.of_dvd (by norm_num [q]) hpowM)
    have hpmod : p ≡ 13573 + (t * 29400 + r) [MOD q] := by
      have hp0 : p ≡ 13573 + k [MOD q] := by
        exact (Nat.mod_modEq (2 ^ r) q).trans hpowq0
      rwa [← hkdecomp]
    have hc : r + 13573 ≡ r % q + 13573 % q [MOD q] := by
      exact (Nat.mod_modEq r q).symm.add (Nat.mod_modEq 13573 q).symm
    have hdc_mod : d ≡ t * 29400 [MOD q] := by
      let c := r % q + 13573 % q
      have hA : d + c ≡ p [MOD q] := by
        rw [Nat.ModEq]
        dsimp [c, d]
        exact redDiff_add_mod 13573 r p
      have hpmod' : p ≡ t * 29400 + (r + 13573) [MOD q] := by
        convert hpmod using 1
        omega
      have hB : t * 29400 + c ≡ p [MOD q] := by
        have hc' : t * 29400 + (r + 13573) ≡ t * 29400 + c [MOD q] := by
          exact hc.add_left (t * 29400)
        exact hc'.symm.trans hpmod'.symm
      have hsum : d + c ≡ t * 29400 + c [MOD q] := hA.trans hB.symm
      exact Nat.ModEq.add_right_cancel' c hsum
    have hdlt : d < q := by
      dsimp [d, redDiff]
      exact Nat.mod_lt _ (by norm_num [q])
    have hd_eq_mod : d = (t * 29400) % q := by
      rw [Nat.ModEq] at hdc_mod
      rw [Nat.mod_eq_of_lt hdlt] at hdc_mod
      exact hdc_mod
    have hd_form : d = ((t * 600) % 2807) * 49 := by
      rw [hd_eq_mod]
      simpa [q] using t_mul_L_mod_eq t
    have hd49 : d % 49 = 0 := by
      rw [hd_form]
      exact Nat.mul_mod_left ((t * 600) % 2807) 49
    have hddiv : d / 49 = (t * 600) % 2807 := by
      rw [hd_form]
      rw [Nat.mul_comm]
      exact Nat.mul_div_right ((t * 600) % 2807) (by norm_num : 0 < 49)
    have htred : redT 13573 r p = t := by
      dsimp [redT]
      change (d / 49 * 2138) % 2807 = t
      rw [hddiv]
      exact inv600_apply t ht
    have hok : redOK 13573 16331503 r p = true := by
      simpa [p] using redOK_of_r r hr
    have hmod4b : ((13573 + r) % 4 == 0) = true := by
      change decide ((13573 + r) % 4 = 0) = true
      exact decide_eq_true hmod4
    have hd49b : (d % 49 == 0) = true := by
      change decide (d % 49 = 0) = true
      exact decide_eq_true hd49
    have hk0 : r + redT 13573 r p * 29400 = k := by
      omega
    have hd49b' : (redDiff 13573 r p % 49 == 0) = true := by
      change (d % 49 == 0) = true
      exact hd49b
    dsimp [redOK] at hok
    rw [hmod4b, hd49b', hk0] at hok
    have hkneq0 : (k == 0) = false := by
      change decide (k = 0) = false
      exact decide_eq_false_iff_not.mpr (by omega)
    have hnlt : decide (16331503 < k) = false := by
      exact decide_eq_false_iff_not.mpr (by omega)
    rw [hkneq0, hnlt] at hok
    exact Bool.noConfusion hok


lemma A232616_prop_of_modEq_witnesses (n m : Nat) (hn : 0 < n)
    (H : ∀ target : Nat, target < n → ∃ k, 1 ≤ k ∧ k ≤ m ∧ (2 ^ k - k) ≡ target [MOD n]) :
    @A232616_prop n m (NeZero.mk (Nat.ne_of_gt hn)) := by
  haveI : NeZero n := NeZero.mk (Nat.ne_of_gt hn)
  apply Finset.ext
  intro x
  constructor
  · intro _hx
    rcases H x.val (ZMod.val_lt x) with ⟨k, hk1, hkm, hkmod⟩
    rw [Finset.mem_image]
    refine ⟨k, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨hk1, hkm⟩
    · rw [← ZMod.natCast_zmod_val x]
      exact (ZMod.natCast_eq_natCast_iff (2 ^ k - k) x.val n).2 hkmod
  · intro _hx
    simp

lemma not_A232616_prop_of_missing_modEq (n m target : Nat) (hn : 0 < n)
    (H : ∀ k, 1 ≤ k → k ≤ m → ¬ ((2 ^ k - k) ≡ target [MOD n])) :
    ¬ @A232616_prop n m (NeZero.mk (Nat.ne_of_gt hn)) := by
  haveI : NeZero n := NeZero.mk (Nat.ne_of_gt hn)
  intro hprop
  have hxmem : (target : ZMod n) ∈ (Finset.univ : Finset (ZMod n)) := by simp
  rw [hprop, Finset.mem_image] at hxmem
  rcases hxmem with ⟨k, hkIcc, hkval⟩
  rw [Finset.mem_Icc] at hkIcc
  have hmod : (2 ^ k - k) ≡ target [MOD n] := by
    exact (ZMod.natCast_eq_natCast_iff (2 ^ k - k) target n).1 hkval
  exact H k hkIcc.1 hkIcc.2 hmod

lemma coverage_prop_550172 :
    @A232616_prop 550172 82496988 (NeZero.mk (by norm_num : 550172 ≠ 0)) := by
  apply A232616_prop_of_modEq_witnesses 550172 82496988 (by norm_num)
  intro target ht
  exact coverage_witness target ht

lemma not_prop_550172_bad :
    ¬ @A232616_prop 550172 16331503 (NeZero.mk (by norm_num : 550172 ≠ 0)) := by
  apply not_A232616_prop_of_missing_modEq 550172 16331503 13573 (by norm_num)
  exact miss_witness_reduced

/-- Disproof of the conjecture: `n = 550172` is a counterexample. -/
theorem oeis_232616_conjecture_i.disproof :
    ¬ (∀ n : ℕ, 0 < n → A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1)) := by
  intro hforall
  let n : Nat := 550172
  let mBad : Nat := 16331503
  let mGood : Nat := 82496988
  have hn : 0 < n := by norm_num [n]
  have hcov : @A232616_prop n mGood (NeZero.mk (Nat.ne_of_gt hn)) := by
    simpa [n, mGood] using coverage_prop_550172
  have hnotbad : ¬ @A232616_prop n mBad (NeZero.mk (Nat.ne_of_gt hn)) := by
    simpa [n, mBad] using not_prop_550172_bad
  have hmain := hforall n hn
  rw [A232616, dif_neg (Nat.ne_of_gt hn)] at hmain
  let S : Set Nat := {m | @A232616_prop n m (NeZero.mk (Nat.ne_of_gt hn))}
  change sInf S < 2 * (Nat.nth Nat.Prime (n - 1) - 1) at hmain
  have hnth : Nat.nth Nat.Prime (n - 1) ≤ 8165753 := by
    simpa [n] using nth_prime_bound
  have hbnd : 2 * (Nat.nth Nat.Prime (n - 1) - 1) ≤ 16331504 := by
    omega
  have hmain' : sInf S < 16331504 := lt_of_lt_of_le hmain hbnd
  have hle : sInf S ≤ mBad := by omega
  have hsne : S.Nonempty := ⟨mGood, hcov⟩
  have hsinf : sInf S ∈ S := Nat.sInf_mem hsne
  have hbad : @A232616_prop n mBad (NeZero.mk (Nat.ne_of_gt hn)) := by
    exact A232616_prop_mono hle hsinf
  exact hnotbad hbad
