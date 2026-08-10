import FormalConjectures.Util.ProblemImports

open Finset ZMod Nat Set Classical

set_option maxRecDepth 1000000
set_option maxHeartbeats 0



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

/--
Conjecture (i): $a(n) < 2 \cdot (\text{prime}(n) - 1)$ for all $n > 0$,
where $\text{prime}(n)$ is the $n$-th prime number (1-indexed).
-/
private lemma A232616_prop_mono (n : ℕ) [NeZero n] {m M : ℕ} (hmM : m ≤ M)
    (hm : A232616_prop n m) : A232616_prop n M := by
  unfold A232616_prop at hm ⊢
  ext x
  constructor
  · intro hx
    have hx' : x ∈ (Finset.Icc 1 m).image (fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)) := by
      simpa [← hm] using hx
    rcases Finset.mem_image.mp hx' with ⟨k, hk, rfl⟩
    have hkI := Finset.mem_Icc.mp hk
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hkI.1, hkI.2.trans hmM⟩, rfl⟩
  · intro _
    simp

private def A232616_aTable : List ℕ :=
  [36, 143, 2, 349, 308, 3, 26, 225, 332, 191, 50, 81, 4, 31, 58, 85, 48,
    139, 98, 193, 220, 15, 122, 237, 328, 287, 146, 5, 204, 311, 170, 29,
    60, 171, 10, 37, 64, 27, 118, 77, 172, 199, 226, 101, 216, 307, 266,
    125, 72, 183, 290, 149, 8, 39, 150, 173, 16, 43, 6, 97, 56, 151, 178,
    205, 80, 195, 286, 245, 104, 51, 162, 269, 128, 475, 18, 129, 152, 11,
    22, 49, 76, 35, 130, 157, 184, 59, 174, 265, 224, 83, 30, 141, 248,
    107, 454, 413, 108, 131, 330, 437, 28, 55, 14, 109, 136, 163, 38, 153,
    244, 203, 62, 9, 120, 227, 86, 433, 392, 87, 110, 309, 416, 7, 34, 61,
    88, 115, 142, 17, 132, 223, 182, 41, 304, 99, 206, 65, 412, 371, 66,
    89, 288, 395, 254, 13, 40, 67, 94, 121, 148, 111, 202, 161, 20, 283,
    78, 185, 44, 391, 350, 45, 68, 267, 374, 233, 12, 19, 46, 73, 100,
    127, 90, 181, 140, 235, 262, 57, 164, 23, 370, 329, 24, 47, 246, 353,
    212, 71, 102, 25, 52, 79, 106, 69, 160, 119, 214, 241]

private def A232616_aFor (r : ℕ) : ℕ := A232616_aTable.getD (r % 196) 0

private def A232616_kFor (r : ℕ) : ℕ :=
  let a := A232616_aFor r
  let base := (((2 : ZMod 550172) ^ a - (a : ZMod 550172))).val
  let delta := (base + 550172 - r) % 550172
  let t := ((delta / 196) * 131) % 2807
  a + 29400 * t

private lemma A232616_pow29400_modEq_343 : 2 ^ 29400 ≡ 1 [MOD 343] := by
  rw [show 29400 = 147 * 200 by norm_num, pow_mul]
  have h : 2 ^ 147 ≡ 1 [MOD 343] := by
    rw [Nat.ModEq]
    norm_num
  simpa using h.pow 200

private lemma A232616_pow29400_modEq_401 : 2 ^ 29400 ≡ 1 [MOD 401] := by
  rw [show 29400 = 200 * 147 by norm_num, pow_mul]
  have h : 2 ^ 200 ≡ 1 [MOD 401] := by
    rw [Nat.ModEq]
    norm_num
  simpa using h.pow 147

private lemma A232616_pow29400_modEq_137543 : 2 ^ 29400 ≡ 1 [MOD 137543] := by
  have hcop : Nat.Coprime 343 401 := by norm_num
  rw [show 137543 = 343 * 401 by norm_num, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  exact ⟨A232616_pow29400_modEq_343, A232616_pow29400_modEq_401⟩

private lemma A232616_four_dvd_pow_two {e : ℕ} (he : 2 ≤ e) : 4 ∣ 2 ^ e := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le he
  use 2 ^ c
  ring_nf

private lemma A232616_period (a t : ℕ) (ha : 2 ≤ a) :
    2 ^ (a + 29400 * t) ≡ 2 ^ a [MOD 550172] := by
  have hcop : Nat.Coprime 4 137543 := by norm_num
  rw [show 550172 = 4 * 137543 by norm_num, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  constructor
  · have h1 : 2 ^ (a + 29400 * t) ≡ 0 [MOD 4] :=
      Nat.modEq_zero_iff_dvd.mpr (A232616_four_dvd_pow_two (by omega))
    have h2 : 2 ^ a ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr (A232616_four_dvd_pow_two ha)
    exact h1.trans h2.symm
  · have h : 2 ^ (29400 * t) ≡ 1 [MOD 137543] := by
      rw [pow_mul]
      simpa using A232616_pow29400_modEq_137543.pow t
    rw [pow_add]
    simpa using h.mul_left (2^a)

private lemma A232616_delta_divisible {base r : ℕ} (hbr : base % 196 = r % 196) :
    ((base + 550172 - r) % 550172) % 196 = 0 := by
  omega

private lemma A232616_base_mod_delta {base r delta : ℕ} (hrle : r ≤ base + 550172)
    (hdelta : delta = (base + 550172 - r) % 550172) :
    base ≡ r + delta [MOD 550172] := by
  have h1 : base + 550172 = r + (base + 550172 - r) := by omega
  have h2 : base + 550172 ≡ base [MOD 550172] := by
    rw [Nat.ModEq]
    omega
  have h3 : r + (base + 550172 - r) ≡ r + delta [MOD 550172] := by
    apply Nat.ModEq.add_left
    rw [hdelta]
    exact (Nat.mod_modEq (base + 550172 - r) 550172).symm
  calc
    base ≡ base + 550172 [MOD 550172] := h2.symm
    _ = r + (base + 550172 - r) := h1
    _ ≡ r + delta [MOD 550172] := h3

private lemma A232616_inv150 (q : ℕ) : 150 * (((q * 131) % 2807)) ≡ q [MOD 2807] := by
  have h : 150 * 131 ≡ 1 [MOD 2807] := by norm_num [Nat.ModEq]
  calc
    150 * ((q * 131) % 2807) ≡ 150 * (q * 131) [MOD 2807] :=
      (Nat.mod_modEq (q*131) 2807).mul_left 150
    _ = q * (150*131) := by ring
    _ ≡ q * 1 [MOD 2807] := h.mul_left q
    _ = q := by ring

private lemma A232616_crt_core {base r : ℕ} (hb : base < 550172) (hr : r < 550172)
    (hbr : base % 196 = r % 196) :
    let delta := (base + 550172 - r) % 550172
    let t := ((delta / 196) * 131) % 2807
    base ≡ r + 29400 * t [MOD 550172] := by
  intro delta t
  have hdelta : delta = (base + 550172 - r) % 550172 := rfl
  have hdiv0 : delta % 196 = 0 := by
    rw [hdelta]
    exact A232616_delta_divisible hbr
  have hdiv : 196 ∣ delta := Nat.dvd_iff_mod_eq_zero.mpr hdiv0
  have hq : 196 * (delta / 196) = delta := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdiv
  have hqt : 150 * t ≡ delta / 196 [MOD 2807] := by
    subst t
    exact A232616_inv150 (delta/196)
  have hmul : 29400 * t ≡ delta [MOD 550172] := by
    have h := hqt.mul_left' 196
    rw [show 196 * 2807 = 550172 by norm_num] at h
    convert h using 1 <;> ring_nf <;> omega
  exact (A232616_base_mod_delta (by omega : r ≤ base + 550172) hdelta).trans
    ((Nat.ModEq.refl r).add hmul.symm)

private def A232616_tableBool : Bool :=
  (List.range 196).all fun s =>
    decide (2 ≤ A232616_aFor s ∧ A232616_aFor s ≤ 475 ∧
      ((2 : ZMod 196) ^ A232616_aFor s - (A232616_aFor s : ZMod 196) = (s : ZMod 196)))

private lemma A232616_tableBool_true : A232616_tableBool = true := by
  decide

private lemma A232616_aFor_spec (r : ℕ) :
    2 ≤ A232616_aFor r ∧ A232616_aFor r ≤ 475 ∧
      ((2 : ZMod 196) ^ A232616_aFor r - (A232616_aFor r : ZMod 196) = (r : ZMod 196)) := by
  have hmem : r % 196 ∈ List.range 196 := by
    simpa [List.mem_range] using Nat.mod_lt r (by norm_num : 0 < 196)
  have hb := List.all_eq_true.mp A232616_tableBool_true (r % 196) hmem
  have hs := of_decide_eq_true hb
  have haf : A232616_aFor (r % 196) = A232616_aFor r := by
    unfold A232616_aFor
    rw [Nat.mod_mod]
  have hcast : ((r % 196 : ℕ) : ZMod 196) = (r : ZMod 196) := by
    exact (ZMod.natCast_eq_natCast_iff (r%196) r 196).2 (Nat.mod_modEq r 196)
  simpa [haf, hcast] using hs

private lemma A232616_base_mod196 (r : ℕ) :
    let a := A232616_aFor r
    let base := (((2 : ZMod 550172) ^ a - (a : ZMod 550172))).val
    base % 196 = r % 196 := by
  intro a base
  have htab := (A232616_aFor_spec r).2.2
  have hdiv : 196 ∣ 550172 := by norm_num
  let f := ZMod.castHom hdiv (ZMod 196)
  have hval : (base : ZMod 550172) = (2 : ZMod 550172)^a - (a : ZMod 550172) := by
    dsimp [base]
    exact ZMod.natCast_zmod_val _
  have hcast0 := congrArg f hval
  have hcast : (base : ZMod 196) = (2 : ZMod 196)^a - (a : ZMod 196) := by
    dsimp [f] at hcast0
    simpa [ZMod.castHom_apply, a] using hcast0
  have hz : (base : ZMod 196) = (r : ZMod 196) := by
    simpa [a] using hcast.trans htab
  exact (ZMod.natCast_eq_natCast_iff base r 196).1 hz

private lemma A232616_kFor_spec (r : ℕ) (hr : r < 550172) :
    1 ≤ A232616_kFor r ∧ A232616_kFor r ≤ 82496875 ∧
      ((2 : ZMod 550172) ^ A232616_kFor r -
          (A232616_kFor r : ZMod 550172) = (r : ZMod 550172)) := by
  unfold A232616_kFor
  let a := A232616_aFor r
  let base := (((2 : ZMod 550172) ^ a - (a : ZMod 550172))).val
  let delta := (base + 550172 - r) % 550172
  let t := ((delta / 196) * 131) % 2807
  have haspec := A232616_aFor_spec r
  have ha2 : 2 ≤ a := by simpa [a] using haspec.1
  have ha475 : a ≤ 475 := by simpa [a] using haspec.2.1
  have htlt : t < 2807 := by simpa [t] using Nat.mod_lt ((delta/196)*131) (by norm_num : 0 < 2807)
  constructor
  · change 1 ≤ a + 29400 * t
    omega
  constructor
  · change a + 29400 * t ≤ 82496875
    omega
  · have hb_lt : base < 550172 := by simpa [base] using ZMod.val_lt (((2 : ZMod 550172) ^ a - (a : ZMod 550172)))
    have hbr : base % 196 = r % 196 := by simpa [a, base] using A232616_base_mod196 r
    have hcrt : base ≡ r + 29400 * t [MOD 550172] := by
      simpa [delta, t] using (A232616_crt_core (base:=base) (r:=r) hb_lt hr hbr)
    have hbasez : (base : ZMod 550172) = (r + 29400 * t : ℕ) :=
      (ZMod.natCast_eq_natCast_iff base (r + 29400*t) 550172).2 hcrt
    have hperiod : (2 : ZMod 550172) ^ (a + 29400 * t) = (2 : ZMod 550172) ^ a := by
      have hm := A232616_period a t ha2
      simpa [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff (2^(a+29400*t)) (2^a) 550172).2 hm
    have hval : (base : ZMod 550172) = (2 : ZMod 550172)^a - (a : ZMod 550172) := by
      dsimp [base]
      exact ZMod.natCast_zmod_val _
    calc
      (2 : ZMod 550172) ^ (a + 29400 * t) - ((a + 29400 * t : ℕ) : ZMod 550172)
          = (2 : ZMod 550172)^a - ((a : ZMod 550172) + (29400 * t : ℕ)) := by
            rw [hperiod, Nat.cast_add]
      _ = ((2 : ZMod 550172)^a - (a : ZMod 550172)) - (29400 * t : ℕ) := by ring
      _ = (base : ZMod 550172) - (29400 * t : ℕ) := by rw [← hval]
      _ = (r : ZMod 550172) := by
        have : (base : ZMod 550172) = (r : ZMod 550172) + (29400 * t : ℕ) := by
          simpa [Nat.cast_add] using hbasez
        rw [this]
        ring

private lemma A232616_counter_complete : A232616_prop 550172 82496875 := by
  unfold A232616_prop
  ext x
  constructor
  · intro _
    let r : ℕ := x.val
    have hr : r < 550172 := by simpa [r] using ZMod.val_lt x
    have hp : 1 ≤ A232616_kFor r ∧ A232616_kFor r ≤ 82496875 ∧
        ((2 : ZMod 550172) ^ A232616_kFor r -
            (A232616_kFor r : ZMod 550172) = (r : ZMod 550172)) :=
      A232616_kFor_spec r hr
    refine Finset.mem_image.mpr ⟨A232616_kFor r, Finset.mem_Icc.mpr ⟨hp.1, hp.2.1⟩, ?_⟩
    calc
      (Nat.cast (2 ^ A232616_kFor r - A232616_kFor r) : ZMod 550172)
          = (2 : ZMod 550172) ^ A232616_kFor r -
              (A232616_kFor r : ZMod 550172) := by
            rw [Nat.cast_sub (le_of_lt (A232616_kFor r).lt_two_pow_self)]
            simp
      _ = (r : ZMod 550172) := hp.2.2
      _ = x := by simpa [r] using (ZMod.natCast_zmod_val x)
  · intro _
    simp

private def pow2NVal (a : ℕ) : ℕ :=
  let u := (2 ^ (a % 147)) % 343
  let v := (2 ^ (a % 200)) % 401
  let y := (u * 401 * 207 + v * 343 * 159) % 137543
  (4 * ((34386 * y) % 137543)) % 550172

lemma pow147 : 2 ^ 147 ≡ 1 [MOD 343] := by rw [Nat.ModEq]; norm_num
lemma pow200 : 2 ^ 200 ≡ 1 [MOD 401] := by rw [Nat.ModEq]; norm_num

lemma pow_mod_period (a P m : ℕ) (hP : 2^P ≡ 1 [MOD m]) : 2^a ≡ 2^(a%P) [MOD m] := by
  have hdecomp : a = P*(a/P) + a%P := (Nat.div_add_mod a P).symm
  rw [hdecomp, pow_add, pow_mul]
  have hpow : (2^P)^(a/P) ≡ 1^(a/P) [MOD m] := hP.pow _
  simpa [mul_comm] using hpow.mul_right (2^(a%P))

lemma pow2NVal_modEq (a : ℕ) (ha : 2 ≤ a) : pow2NVal a ≡ 2^a [MOD 550172] := by
  unfold pow2NVal
  let u := (2 ^ (a % 147)) % 343
  let v := (2 ^ (a % 200)) % 401
  let y := (u * 401 * 207 + v * 343 * 159) % 137543
  have hu : u ≡ 2^a [MOD 343] := by
    calc
      u ≡ 2^(a%147) [MOD 343] := Nat.mod_modEq _ _
      _ ≡ 2^a [MOD 343] := (pow_mod_period a 147 343 pow147).symm
  have hv : v ≡ 2^a [MOD 401] := by
    calc
      v ≡ 2^(a%200) [MOD 401] := Nat.mod_modEq _ _
      _ ≡ 2^a [MOD 401] := (pow_mod_period a 200 401 pow200).symm
  have hy343 : y ≡ 2^a [MOD 343] := by
    dsimp [y]
    calc
      (u * 401 * 207 + v * 343 * 159) % 137543 ≡ u * 401 * 207 + v * 343 * 159 [MOD 343] := Nat.mod_modEq _ _ |>.of_dvd (by norm_num : 343 ∣ 137543)
      _ ≡ (2^a) * 1 + 0 [MOD 343] := by
        apply Nat.ModEq.add
        · have hc : 401 * 207 ≡ 1 [MOD 343] := by norm_num [Nat.ModEq]
          simpa [mul_assoc] using hu.mul hc
        · have hz : v * 343 * 159 ≡ 0 [MOD 343] := by
            rw [Nat.ModEq]
            omega
          exact hz
      _ = 2^a := by ring
  have hy401 : y ≡ 2^a [MOD 401] := by
    dsimp [y]
    calc
      (u * 401 * 207 + v * 343 * 159) % 137543 ≡ u * 401 * 207 + v * 343 * 159 [MOD 401] := Nat.mod_modEq _ _ |>.of_dvd (by norm_num : 401 ∣ 137543)
      _ ≡ 0 + (2^a) * 1 [MOD 401] := by
        apply Nat.ModEq.add
        · have hz : u * 401 * 207 ≡ 0 [MOD 401] := by rw [Nat.ModEq]; omega
          exact hz
        · have hc : 343 * 159 ≡ 1 [MOD 401] := by norm_num [Nat.ModEq]
          simpa [mul_assoc] using hv.mul hc
      _ = 2^a := by ring
  have hy : y ≡ 2^a [MOD 137543] := by
    have hcop : Nat.Coprime 343 401 := by norm_num
    rw [show 137543 = 343*401 by norm_num, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    exact ⟨hy343, hy401⟩
  have hx4 : (4 * ((34386 * y) % 137543)) % 550172 ≡ 2^a [MOD 4] := by
    have hleft0 : (4 * ((34386*y)%137543)) % 550172 ≡ 4 * ((34386*y)%137543) [MOD 4] :=
      (Nat.mod_modEq _ _).of_dvd (by norm_num : 4 ∣ 550172)
    have hleft : (4 * ((34386*y)%137543)) % 550172 ≡ 0 [MOD 4] := by
      refine hleft0.trans ?_
      rw [Nat.ModEq]
      omega
    have hright : 2^a ≡ 0 [MOD 4] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le ha
      use 2^c
      ring_nf
    exact hleft.trans hright.symm
  have hxM : (4 * ((34386 * y) % 137543)) % 550172 ≡ 2^a [MOD 137543] := by
    have hleft0 : (4 * ((34386*y)%137543)) % 550172 ≡ 4 * ((34386*y)%137543) [MOD 137543] :=
      (Nat.mod_modEq _ _).of_dvd (by norm_num : 137543 ∣ 550172)
    have hleft1 : 4 * ((34386*y)%137543) ≡ 4 * (34386*y) [MOD 137543] :=
      (Nat.mod_modEq (34386*y) 137543).mul_left 4
    have hinv : 4 * 34386 ≡ 1 [MOD 137543] := by norm_num [Nat.ModEq]
    have hleft2 : 4 * (34386*y) ≡ y [MOD 137543] := by
      calc
        4 * (34386*y) = (4*34386)*y := by ring
        _ ≡ 1*y [MOD 137543] := hinv.mul_right y
        _ = y := by ring
    exact hleft0.trans (hleft1.trans (hleft2.trans hy))
  have hcop : Nat.Coprime 4 137543 := by norm_num
  rw [show 550172 = 4 * 137543 by norm_num, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  exact ⟨hx4, hxM⟩

private def baseFast (a : ℕ) : ℕ := (pow2NVal a + 550172 - (a % 550172)) % 550172
private def firstHitFast (a : ℕ) : ℕ :=
  let base := baseFast a
  let delta := (base + 550172 - 13573) % 550172
  let t := ((delta / 196) * 131) % 2807
  a + 29400 * t
private def firstHit (a : ℕ) : ℕ :=
  let base := (((2 : ZMod 550172) ^ a - (a : ZMod 550172))).val
  let delta := (base + 550172 - 13573) % 550172
  let t := ((delta / 196) * 131) % 2807
  a + 29400 * t

lemma baseFast_eq (a : ℕ) (ha : 2 ≤ a) :
    baseFast a = (((2 : ZMod 550172)^a - (a : ZMod 550172))).val := by
  unfold baseFast
  let expr : ZMod 550172 := (2 : ZMod 550172)^a - (a : ZMod 550172)
  have hbf_lt : (pow2NVal a + 550172 - a % 550172) % 550172 < 550172 := Nat.mod_lt _ (by norm_num : 0 < 550172)
  have hcast1 : (((pow2NVal a + 550172 - a % 550172) % 550172 : ℕ) : ZMod 550172) = expr := by
    calc
      (((pow2NVal a + 550172 - a % 550172) % 550172 : ℕ) : ZMod 550172)
          = ((pow2NVal a + 550172 - a % 550172 : ℕ) : ZMod 550172) := by
            exact (ZMod.natCast_eq_natCast_iff ((pow2NVal a + 550172 - a % 550172) % 550172) (pow2NVal a + 550172 - a % 550172) 550172).2 (Nat.mod_modEq _ _)
      _ = expr := by
        have hp : (pow2NVal a : ZMod 550172) = ((2^a : ℕ) : ZMod 550172) :=
          (ZMod.natCast_eq_natCast_iff (pow2NVal a) (2^a) 550172).2 (pow2NVal_modEq a ha)
        have hamod : ((a % 550172 : ℕ) : ZMod 550172) = (a : ZMod 550172) :=
          (ZMod.natCast_eq_natCast_iff (a%550172) a 550172).2 (Nat.mod_modEq a 550172)
        rw [Nat.cast_sub (by omega : a % 550172 ≤ pow2NVal a + 550172), Nat.cast_add, hp, hamod]
        change (((2^a : ℕ) : ZMod 550172) + ((550172 : ℕ) : ZMod 550172) - (a : ZMod 550172)) = expr
        have hzero : ((550172 : ℕ) : ZMod 550172) = 0 := ZMod.natCast_self 550172
        rw [hzero]
        simp [expr, Nat.cast_pow]
  have hcast2 : ((((2 : ZMod 550172)^a - (a : ZMod 550172))).val : ZMod 550172) = expr := by
    exact ZMod.natCast_zmod_val _
  have hmod := (ZMod.natCast_eq_natCast_iff ((pow2NVal a + 550172 - a % 550172) % 550172)
    (((2 : ZMod 550172)^a - (a : ZMod 550172))).val 550172).1 (hcast1.trans hcast2.symm)
  exact Nat.ModEq.eq_of_lt_of_lt hmod hbf_lt (ZMod.val_lt _)



-- include period and crt core

lemma pow29400_modEq_343 : 2 ^ 29400 ≡ 1 [MOD 343] := by
  rw [show 29400 = 147 * 200 by norm_num, pow_mul]
  have h : 2 ^ 147 ≡ 1 [MOD 343] := by
    rw [Nat.ModEq]
    norm_num
  simpa using h.pow 200

lemma pow29400_modEq_401 : 2 ^ 29400 ≡ 1 [MOD 401] := by
  rw [show 29400 = 200 * 147 by norm_num, pow_mul]
  have h : 2 ^ 200 ≡ 1 [MOD 401] := by
    rw [Nat.ModEq]
    norm_num
  simpa using h.pow 147

lemma pow29400_modEq_137543 : 2 ^ 29400 ≡ 1 [MOD 137543] := by
  have hcop : Nat.Coprime 343 401 := by norm_num
  rw [show 137543 = 343 * 401 by norm_num, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  exact ⟨pow29400_modEq_343, pow29400_modEq_401⟩

lemma four_dvd_pow_two {e : ℕ} (he : 2 ≤ e) : 4 ∣ 2 ^ e := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le he
  use 2 ^ c
  ring_nf

lemma period (a t : ℕ) (ha : 2 ≤ a) : 2 ^ (a + 29400 * t) ≡ 2 ^ a [MOD 550172] := by
  have hcop : Nat.Coprime 4 137543 := by norm_num
  rw [show 550172 = 4 * 137543 by norm_num, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  constructor
  · have h1 : 2 ^ (a + 29400 * t) ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr (four_dvd_pow_two (by omega))
    have h2 : 2 ^ a ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr (four_dvd_pow_two ha)
    exact h1.trans h2.symm
  · have h : 2 ^ (29400 * t) ≡ 1 [MOD 137543] := by
      rw [pow_mul]
      simpa using pow29400_modEq_137543.pow t
    rw [pow_add]
    simpa using h.mul_left (2^a)

lemma delta_divisible {base r : ℕ} (hb : base < 550172) (hr : r < 550172)
    (hbr : base % 196 = r % 196) :
    ((base + 550172 - r) % 550172) % 196 = 0 := by
  omega

lemma base_mod_delta {base r delta : ℕ} (hrle : r ≤ base + 550172)
    (hdelta : delta = (base + 550172 - r) % 550172) :
    base ≡ r + delta [MOD 550172] := by
  have h1 : base + 550172 = r + (base + 550172 - r) := by omega
  have h2 : base + 550172 ≡ base [MOD 550172] := by
    rw [Nat.ModEq]
    omega
  have h3 : r + (base + 550172 - r) ≡ r + delta [MOD 550172] := by
    apply Nat.ModEq.add_left
    rw [hdelta]
    exact (Nat.mod_modEq (base + 550172 - r) 550172).symm
  calc
    base ≡ base + 550172 [MOD 550172] := h2.symm
    _ = r + (base + 550172 - r) := h1
    _ ≡ r + delta [MOD 550172] := h3

lemma inv150 (q : ℕ) : 150 * (((q * 131) % 2807)) ≡ q [MOD 2807] := by
  have h : 150 * 131 ≡ 1 [MOD 2807] := by norm_num [Nat.ModEq]
  calc
    150 * ((q * 131) % 2807) ≡ 150 * (q * 131) [MOD 2807] := (Nat.mod_modEq (q*131) 2807).mul_left 150
    _ = q * (150*131) := by ring
    _ ≡ q * 1 [MOD 2807] := h.mul_left q
    _ = q := by ring

lemma crt_core {base r : ℕ} (hb : base < 550172) (hr : r < 550172)
    (hbr : base % 196 = r % 196) :
    let delta := (base + 550172 - r) % 550172
    let t := ((delta / 196) * 131) % 2807
    base ≡ r + 29400 * t [MOD 550172] := by
  intro delta t
  have hdelta : delta = (base + 550172 - r) % 550172 := rfl
  have hdiv0 : delta % 196 = 0 := by
    rw [hdelta]
    exact delta_divisible hb hr hbr
  have hdiv : 196 ∣ delta := Nat.dvd_iff_mod_eq_zero.mpr hdiv0
  have hq : 196 * (delta / 196) = delta := by rw [mul_comm]; exact Nat.div_mul_cancel hdiv
  have hqt : 150 * t ≡ delta / 196 [MOD 2807] := by
    subst t
    exact inv150 (delta/196)
  have hmul : 29400 * t ≡ delta [MOD 550172] := by
    have h := hqt.mul_left' 196
    -- h : 196 * (150*t) ≡ 196*(delta/196) [MOD 196*2807]
    rw [show 196 * 2807 = 550172 by norm_num] at h
    convert h using 1 <;> ring_nf <;> omega
  exact (base_mod_delta (by omega : r ≤ base + 550172) hdelta).trans ((Nat.ModEq.refl r).add hmul.symm)

private lemma firstHit_eq_of_hit {a q : ℕ} (ha2 : 2 ≤ a) (haB : a ≤ 29401) (hkB : a + 29400*q ≤ 16331503)
    (hhit : (2 : ZMod 550172) ^ (a + 29400*q) - ((a + 29400*q : ℕ) : ZMod 550172) = (13573 : ZMod 550172)) :
    firstHit a = a + 29400*q := by
  unfold firstHit
  let base := (((2 : ZMod 550172) ^ a - (a : ZMod 550172))).val
  let delta := (base + 550172 - 13573) % 550172
  let t := ((delta / 196) * 131) % 2807
  have hq_lt : q < 2807 := by nlinarith
  have ht_lt : t < 2807 := by simpa [t] using Nat.mod_lt ((delta/196)*131) (by norm_num : 0 < 2807)
  have hperiod : (2 : ZMod 550172) ^ (a + 29400*q) = (2 : ZMod 550172)^a := by
    have hm := period a q ha2
    simpa [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff (2^(a+29400*q)) (2^a) 550172).2 hm
  have hbaseval : (base : ZMod 550172) = (2 : ZMod 550172)^a - (a : ZMod 550172) := by
    dsimp [base]
    exact ZMod.natCast_zmod_val _
  have hbase_cong : base ≡ 13573 + 29400*q [MOD 550172] := by
    have hz : (base : ZMod 550172) = (13573 + 29400*q : ℕ) := by
      rw [hbaseval]
      have htmp : (2 : ZMod 550172)^a - (a : ZMod 550172) - (29400*q : ℕ) = (13573 : ZMod 550172) := by
        have hadd : ((a + 29400*q : ℕ) : ZMod 550172) = (a : ZMod 550172) + (29400*q : ℕ) := by
          rw [Nat.cast_add]
        calc
          (2 : ZMod 550172)^a - (a : ZMod 550172) - (29400*q : ℕ)
              = (2 : ZMod 550172)^a - ((a : ZMod 550172) + (29400*q : ℕ)) := by ring
          _ = (2 : ZMod 550172)^(a+29400*q) - ((a + 29400*q : ℕ) : ZMod 550172) := by
                  rw [hperiod, hadd]
          _ = (13573 : ZMod 550172) := hhit
      -- from base - Pq = target => base = target + Pq
      have := congrArg (fun x : ZMod 550172 => x + (29400*q : ℕ)) htmp
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, Nat.cast_add] using this
    exact (ZMod.natCast_eq_natCast_iff base (13573+29400*q) 550172).1 hz
  have hb_lt : base < 550172 := by simpa [base] using ZMod.val_lt (((2 : ZMod 550172)^a - (a : ZMod 550172)))
  have hbr : base % 196 = 13573 % 196 := by
    -- follows by reducing hbase_cong modulo 196; rhs has 29400*q multiple of 196
    have hsmall := Nat.ModEq.of_dvd (by norm_num : 196 ∣ 550172) hbase_cong
    have hmul : 13573 + 29400*q ≡ 13573 [MOD 196] := by
      rw [Nat.ModEq]
      have : 196 ∣ 29400*q := by exact dvd_mul_of_dvd_left (by norm_num : 196 ∣ 29400) q
      omega
    exact hsmall.trans hmul
  have hcrt := crt_core (base:=base) (r:=13573) hb_lt (by norm_num) hbr
  -- hcrt: base ≡ target + P*t. combine with base ≡ target+P*q, cancel target and factor 196 to get t≡q mod2807
  have h1 : 13573 + 29400*t ≡ 13573 + 29400*q [MOD 550172] := hcrt.symm.trans hbase_cong
  have hcancel : 29400*t ≡ 29400*q [MOD 550172] := Nat.ModEq.add_left_cancel (Nat.ModEq.refl 13573) h1
  have htq : t ≡ q [MOD 2807] := by
    have h196 : 196 * (150*t) ≡ 196 * (150*q) [MOD 196*2807] := by
      convert hcancel using 1 <;> ring_nf
    rw [Nat.ModEq] at h196 ⊢
    rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h196
    have h150eq : (150*t) % 2807 = (150*q) % 2807 := Nat.mul_left_cancel (by norm_num : 0 < 196) h196
    have h150 : 150*t ≡ 150*q [MOD 2807] := h150eq
    have hinv : 131 * (150*t) ≡ 131 * (150*q) [MOD 2807] := h150.mul_left 131
    rw [Nat.ModEq] at hinv
    have hleft : (131 * (150*t)) % 2807 = t % 2807 := by
      rw [← Nat.ModEq]
      calc
        131 * (150*t) = (131*150)*t := by ring
        _ ≡ 1*t [MOD 2807] := by
          exact (by norm_num [Nat.ModEq] : 131*150 ≡ 1 [MOD 2807]).mul_right t
        _ = t := by ring
    have hright : (131 * (150*q)) % 2807 = q % 2807 := by
      rw [← Nat.ModEq]
      calc
        131 * (150*q) = (131*150)*q := by ring
        _ ≡ 1*q [MOD 2807] := by
          exact (by norm_num [Nat.ModEq] : 131*150 ≡ 1 [MOD 2807]).mul_right q
        _ = q := by ring
    rwa [hleft, hright] at hinv
  have htqeq : t = q := Nat.ModEq.eq_of_lt_of_lt htq ht_lt hq_lt
  change a + 29400 * t = a + 29400 * q
  rw [htqeq]



private lemma firstHitFast_eq_firstHit (a : ℕ) (ha : 2 ≤ a) : firstHitFast a = firstHit a := by
  unfold firstHitFast firstHit
  rw [baseFast_eq a ha]

private def missCertBlockFast (start len : ℕ) : Bool :=
  (List.range len).all fun i =>
    let a := start + i
    let ap := (a - 2) % 21 + 2
    let al := (a - 2) % 196 + 2
    decide (((2 : ZMod 196) ^ ap - (al : ZMod 196) ≠ (13573 : ZMod 196)) ∨
      16331503 < firstHitFast a)
private lemma missFastBlock_0 : missCertBlockFast 2 5000 = true := by
  decide
private lemma missFastBlock_1 : missCertBlockFast 5002 5000 = true := by
  decide
private lemma missFastBlock_2 : missCertBlockFast 10002 5000 = true := by
  decide
private lemma missFastBlock_3 : missCertBlockFast 15002 5000 = true := by
  decide
private lemma missFastBlock_4 : missCertBlockFast 20002 5000 = true := by
  decide
private lemma missFastBlock_5 : missCertBlockFast 25002 4400 = true := by
  decide

private lemma missCertFast_for {a : ℕ} (ha2 : 2 ≤ a) (haB : a ≤ 29401) :
    ((2 : ZMod 196) ^ ((a - 2) % 21 + 2) - (((a - 2) % 196 + 2 : ℕ) : ZMod 196) ≠ (13573 : ZMod 196)) ∨
      16331503 < firstHitFast a := by
  have hrange : a < 5002 ∨ 5002 ≤ a ∧ a < 10002 ∨ 10002 ≤ a ∧ a < 15002 ∨ 15002 ≤ a ∧ a < 20002 ∨ 20002 ≤ a ∧ a < 25002 ∨ 25002 ≤ a ∧ a < 29402 := by omega
  rcases hrange with h0 | h1 | h2 | h3 | h4 | h5
  · have hi : a - 2 ∈ List.range 5000 := by
      simp [List.mem_range]
      omega
    have hb := List.all_eq_true.mp missFastBlock_0 (a - 2) hi
    have haseq : 2 + (a - 2) = a := by omega
    have hcert : ((2 : ZMod 196) ^ (((2 + (a - 2)) - 2) % 21 + 2) - (((((2 + (a - 2)) - 2) % 196 + 2 : ℕ) : ZMod 196)) ≠ (13573 : ZMod 196)) ∨
        16331503 < firstHitFast (2 + (a - 2)) := of_decide_eq_true hb
    simpa [haseq] using hcert
  · have hi : a - 5002 ∈ List.range 5000 := by
      simp [List.mem_range]
      omega
    have hb := List.all_eq_true.mp missFastBlock_1 (a - 5002) hi
    have haseq : 5002 + (a - 5002) = a := by omega
    have hcert : ((2 : ZMod 196) ^ (((5002 + (a - 5002)) - 2) % 21 + 2) - (((((5002 + (a - 5002)) - 2) % 196 + 2 : ℕ) : ZMod 196)) ≠ (13573 : ZMod 196)) ∨
        16331503 < firstHitFast (5002 + (a - 5002)) := of_decide_eq_true hb
    simpa [haseq] using hcert
  · have hi : a - 10002 ∈ List.range 5000 := by
      simp [List.mem_range]
      omega
    have hb := List.all_eq_true.mp missFastBlock_2 (a - 10002) hi
    have haseq : 10002 + (a - 10002) = a := by omega
    have hcert : ((2 : ZMod 196) ^ (((10002 + (a - 10002)) - 2) % 21 + 2) - (((((10002 + (a - 10002)) - 2) % 196 + 2 : ℕ) : ZMod 196)) ≠ (13573 : ZMod 196)) ∨
        16331503 < firstHitFast (10002 + (a - 10002)) := of_decide_eq_true hb
    simpa [haseq] using hcert
  · have hi : a - 15002 ∈ List.range 5000 := by
      simp [List.mem_range]
      omega
    have hb := List.all_eq_true.mp missFastBlock_3 (a - 15002) hi
    have haseq : 15002 + (a - 15002) = a := by omega
    have hcert : ((2 : ZMod 196) ^ (((15002 + (a - 15002)) - 2) % 21 + 2) - (((((15002 + (a - 15002)) - 2) % 196 + 2 : ℕ) : ZMod 196)) ≠ (13573 : ZMod 196)) ∨
        16331503 < firstHitFast (15002 + (a - 15002)) := of_decide_eq_true hb
    simpa [haseq] using hcert
  · have hi : a - 20002 ∈ List.range 5000 := by
      simp [List.mem_range]
      omega
    have hb := List.all_eq_true.mp missFastBlock_4 (a - 20002) hi
    have haseq : 20002 + (a - 20002) = a := by omega
    have hcert : ((2 : ZMod 196) ^ (((20002 + (a - 20002)) - 2) % 21 + 2) - (((((20002 + (a - 20002)) - 2) % 196 + 2 : ℕ) : ZMod 196)) ≠ (13573 : ZMod 196)) ∨
        16331503 < firstHitFast (20002 + (a - 20002)) := of_decide_eq_true hb
    simpa [haseq] using hcert
  · have hi : a - 25002 ∈ List.range 4400 := by
      simp [List.mem_range]
      omega
    have hb := List.all_eq_true.mp missFastBlock_5 (a - 25002) hi
    have haseq : 25002 + (a - 25002) = a := by omega
    have hcert : ((2 : ZMod 196) ^ (((25002 + (a - 25002)) - 2) % 21 + 2) - (((((25002 + (a - 25002)) - 2) % 196 + 2 : ℕ) : ZMod 196)) ≠ (13573 : ZMod 196)) ∨
        16331503 < firstHitFast (25002 + (a - 25002)) := of_decide_eq_true hb
    simpa [haseq] using hcert


private lemma zmod196_pow_period (a t : ℕ) (ha : 2 ≤ a) :
    2 ^ (a + 21 * t) ≡ 2^a [MOD 196] := by
  have hcop : Nat.Coprime 4 49 := by norm_num
  rw [show 196 = 4*49 by norm_num, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  constructor
  · have h1 : 2 ^ (a + 21*t) ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr (four_dvd_pow_two (by omega : 2 ≤ a + 21*t))
    have h2 : 2 ^ a ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr (four_dvd_pow_two ha)
    exact h1.trans h2.symm
  · have h21 : 2 ^ 21 ≡ 1 [MOD 49] := by rw [Nat.ModEq]; norm_num
    rw [pow_add, pow_mul]
    have hp := h21.pow t
    simpa [mul_comm] using hp.mul_right (2^a)

private lemma zmod196_period_expr (a : ℕ) (ha : 2 ≤ a) :
    (2 : ZMod 196) ^ ((a - 2) % 21 + 2) - ((((a - 2) % 196 + 2 : ℕ)) : ZMod 196)
      = (2 : ZMod 196)^a - (a : ZMod 196) := by
  have hpow : (2 : ZMod 196) ^ ((a - 2) % 21 + 2) = (2 : ZMod 196)^a := by
    let ar := (a-2)%21+2
    let q := (a-2)/21
    have har : 2 ≤ ar := by omega
    have hdecomp : a = ar + 21*q := by
      dsimp [ar, q]
      have hdm := Nat.div_add_mod (a-2) 21
      omega
    have hm := zmod196_pow_period ar q har
    calc
      (2 : ZMod 196) ^ ((a - 2) % 21 + 2) = (2 : ZMod 196)^ar := by rfl
      _ = (2 : ZMod 196)^(ar+21*q) := by
        have heq : (2 : ZMod 196)^(ar+21*q) = (2 : ZMod 196)^ar := by
          simpa [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff (2^(ar+21*q)) (2^ar) 196).2 hm
        exact heq.symm
      _ = (2 : ZMod 196)^a := by rw [hdecomp]
  have hlin : (((a - 2) % 196 + 2 : ℕ) : ZMod 196) = (a : ZMod 196) := by
    rw [ZMod.natCast_eq_natCast_iff]
    have hdecomp : a = 196 * ((a-2)/196) + ((a-2)%196 + 2) := by
      have hdm := Nat.div_add_mod (a-2) 196
      omega
    rw [hdecomp]
    rw [Nat.ModEq]
    omega
  rw [hpow, hlin]

private lemma miss_residue_of_le {k : ℕ} (hk1 : 1 ≤ k) (hkB : k ≤ 16331503) :
    (2 : ZMod 550172) ^ k - (k : ZMod 550172) ≠ (13573 : ZMod 550172) := by
  intro hhit
  by_cases hk2 : k = 1
  · subst k
    change (1 : ZMod 550172) = (13573 : ZMod 550172) at hhit
    have hneq : (1 : ZMod 550172) ≠ (13573 : ZMod 550172) := by
      intro hbad
      have hm := (ZMod.natCast_eq_natCast_iff 1 13573 550172).1 hbad
      norm_num [Nat.ModEq] at hm
    exact hneq hhit
  · have hkge2 : 2 ≤ k := by omega
    let a := (k - 2) % 29400 + 2
    let q := (k - 2) / 29400
    have ha2 : 2 ≤ a := by omega
    have haB : a ≤ 29401 := by
      have hmodlt : (k - 2) % 29400 < 29400 := Nat.mod_lt _ (by norm_num : 0 < 29400)
      omega
    have hk_eq : k = a + 29400*q := by
      dsimp [a, q]
      have h := Nat.div_add_mod (k-2) 29400
      omega
    rw [hk_eq] at hkB hhit
    have hcert := missCertFast_for ha2 haB
    rcases hcert with hne | hfirst
    · have hne' : (2 : ZMod 196)^a - (a : ZMod 196) ≠ (13573 : ZMod 196) := by
        intro hx
        exact hne (by rwa [zmod196_period_expr a ha2])
      apply hne'
      have hperiod : (2 : ZMod 550172) ^ (a + 29400*q) = (2 : ZMod 550172)^a := by
        have hm := period a q ha2
        simpa [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff (2^(a+29400*q)) (2^a) 550172).2 hm
      have htmp : (2 : ZMod 550172)^a - (a : ZMod 550172) - (29400*q : ℕ) = (13573 : ZMod 550172) := by
        have hadd : ((a + 29400*q : ℕ) : ZMod 550172) = (a : ZMod 550172) + (29400*q : ℕ) := by
          rw [Nat.cast_add]
        calc
          (2 : ZMod 550172)^a - (a : ZMod 550172) - (29400*q : ℕ)
              = (2 : ZMod 550172)^a - ((a : ZMod 550172) + (29400*q : ℕ)) := by ring
          _ = (2 : ZMod 550172)^(a+29400*q) - ((a + 29400*q : ℕ) : ZMod 550172) := by
                  rw [hperiod, hadd]
          _ = (13573 : ZMod 550172) := hhit
      have hdiv : 196 ∣ 550172 := by norm_num
      let f := ZMod.castHom hdiv (ZMod 196)
      have hcast := congrArg f htmp
      dsimp [f] at hcast
      have hzero : ((29400*q : ℕ) : ZMod 196) = 0 := by
        rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff]
        exact (dvd_mul_of_dvd_left (by norm_num : 196 ∣ 29400) q).modEq_zero_nat
      have hcast' : (2 : ZMod 196)^a - (a : ZMod 196) - ((29400*q : ℕ) : ZMod 196) = (13573 : ZMod 196) := by
        simpa [ZMod.castHom_apply] using hcast
      simpa [hzero] using hcast'
    · have hfh := firstHit_eq_of_hit ha2 haB hkB hhit
      have hff := firstHitFast_eq_firstHit a ha2
      omega



private lemma A232616_counter_not_bound : ¬ A232616_prop 550172 16331503 := by
  intro hprop
  unfold A232616_prop at hprop
  have hx : (13573 : ZMod 550172) ∈
      (Finset.Icc 1 16331503).image
        (fun k ↦ (Nat.cast (2 ^ k - k) : ZMod 550172)) := by
    simpa [← hprop]
  rcases Finset.mem_image.mp hx with ⟨k, hk, hkval⟩
  have hkI := Finset.mem_Icc.mp hk
  have hcast : (Nat.cast (2 ^ k - k) : ZMod 550172) =
      (2 : ZMod 550172) ^ k - (k : ZMod 550172) := by
    rw [Nat.cast_sub (le_of_lt k.lt_two_pow_self)]
    simp
  rw [hcast] at hkval
  exact (miss_residue_of_le hkI.1 hkI.2) hkval


set_option maxHeartbeats 0
set_option maxRecDepth 10000000
set_option Elab.async false


private def phiList (x : Nat) : List Nat -> Nat
| [] => x
| p::ps => if x = 0 then 0 else if x = 1 then 1 else if x < p then phiList x ps else phiList x ps - phiList (x / p) ps

private def noDivBy : List Nat -> Nat -> Prop
| [], _ => True
| p::ps, m => ¬ p ∣ m ∧ noDivBy ps m

private instance noDivBy_decidable (L : List Nat) (m : Nat) : Decidable (noDivBy L m) := by
  induction L with
  | nil => exact isTrue trivial
  | cons p ps ih => exact inferInstanceAs (Decidable (¬ p ∣ m ∧ noDivBy ps m))

private lemma noDivBy_cons {p m : Nat} {ps : List Nat} :
    noDivBy (p::ps) m ↔ ¬ p ∣ m ∧ noDivBy ps m := Iff.rfl

private lemma noDivBy_of_mem {L : List Nat} {m p : Nat} (h : noDivBy L m) (hp : p ∈ L) : ¬ p ∣ m := by
  induction L with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.mem_cons] at hp
    simp only [noDivBy] at h
    rcases h with ⟨hq, hqs⟩
    rcases hp with rfl | hp
    · exact hq
    · exact ih hqs hp

private lemma noDivBy_of_subset {L K : List Nat} {m : Nat}
    (hK : noDivBy K m) (hsub : ∀ p ∈ L, p ∈ K) : noDivBy L m := by
  induction L with
  | nil => trivial
  | cons p ps ih =>
    simp only [noDivBy]
    constructor
    · exact noDivBy_of_mem hK (hsub p (by simp))
    · exact ih (fun q hq => hsub q (by simp [hq]))

private lemma noDivBy_cons_of_not_mem {p m : Nat} {ps : List Nat} (hp : ¬ p ∣ m) (hps : noDivBy ps m) :
    noDivBy (p::ps) m := ⟨hp, hps⟩

private lemma noDivBy_div_of_dvd {ps : List Nat} {n p : Nat}
    (hps : noDivBy ps n) (hpdvd : p ∣ n) (hc : ∀ q ∈ ps, Nat.Coprime p q) :
    noDivBy ps (n / p) := by
  induction ps with
  | nil => trivial
  | cons q qs ih =>
    simp only [noDivBy] at hps ⊢
    rcases hps with ⟨hnq, hnqs⟩
    constructor
    · intro hqdiv
      have hqdn : q ∣ n := by
        rw [← Nat.div_mul_cancel hpdvd]
        exact dvd_mul_of_dvd_left hqdiv p
      exact hnq hqdn
    · exact ih hnqs (fun r hr => hc r (by simp [hr]))

private lemma noDivBy_mul_left_of_coprime {ps : List Nat} {k p : Nat}
    (hps : noDivBy ps k) (hc : ∀ q ∈ ps, Nat.Coprime p q) :
    noDivBy ps (p * k) := by
  induction ps with
  | nil => trivial
  | cons q qs ih =>
    simp only [noDivBy] at hps ⊢
    rcases hps with ⟨hkq, hkqs⟩
    constructor
    · intro hqdiv
      exact hkq ((hc q (by simp)).symm.dvd_of_dvd_mul_left hqdiv)
    · exact ih hkqs (fun r hr => hc r (by simp [hr]))

private lemma noDivBy_one_of_gt_one {L : List Nat} (hpos : ∀ p ∈ L, 1 < p) : noDivBy L 1 := by
  induction L with
  | nil => trivial
  | cons p ps ih =>
    simp only [noDivBy]
    constructor
    · intro hd
      have : p ≤ 1 := Nat.le_of_dvd (by norm_num) hd
      have hp := hpos p (by simp)
      omega
    · exact ih (fun q hq => hpos q (by simp [hq]))

private lemma noDivBy_of_prime_gt_all {L : List Nat} {p : Nat}
    (hp : Nat.Prime p) (hpos : ∀ r ∈ L, 1 < r) (hgt : ∀ r ∈ L, r < p) : noDivBy L p := by
  induction L with
  | nil => trivial
  | cons r rs ih =>
    simp only [noDivBy]
    constructor
    · intro hrdvd
      rcases hp.eq_one_or_self_of_dvd r hrdvd with hr1 | hrp
      · have hrpos := hpos r (by simp)
        omega
      · have hrlt := hgt r (by simp)
        omega
    · exact ih (fun q hq => hpos q (by simp [hq])) (fun q hq => hgt q (by simp [hq]))

private noncomputable def surv (x : Nat) (L : List Nat) : Finset Nat :=
  (Finset.Icc 1 x).filter (fun m => noDivBy L m)
private noncomputable def bad (x p : Nat) (ps : List Nat) : Finset Nat :=
  (surv x ps).filter (fun m => p ∣ m)
private lemma mem_surv_iff {x m : Nat} {L : List Nat} :
    m ∈ surv x L ↔ 1 ≤ m ∧ m ≤ x ∧ noDivBy L m := by
  unfold surv
  simp [and_assoc]


private lemma bad_card_eq (x p : Nat) (ps : List Nat)
    (hp : 0 < p) (hc : ∀ q ∈ ps, Nat.Coprime p q) :
    (bad x p ps).card = (surv (x / p) ps).card := by
  classical
  unfold bad
  refine Finset.card_bij (fun n _ => n / p) ?hmem ?hinj ?hsurj
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rcases hn with ⟨hnS, hpdvd⟩
    simp only [surv, Finset.mem_filter, Finset.mem_Icc] at hnS ⊢
    rcases hnS with ⟨⟨hn1, hnx⟩, hndiv⟩
    refine ⟨⟨?_, Nat.div_le_div_right hnx⟩, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd hn1 hpdvd) hp
    · exact noDivBy_div_of_dvd hndiv hpdvd hc
  · intro a ha b hb hEq
    simp only [Finset.mem_filter] at ha hb
    rcases ha with ⟨haS, hap⟩; rcases hb with ⟨hbS, hbp⟩
    change a / p = b / p at hEq
    calc
      a = p * (a / p) := by rw [Nat.mul_comm, Nat.div_mul_cancel hap]
      _ = p * (b / p) := by rw [hEq]
      _ = b := by rw [Nat.mul_comm, Nat.div_mul_cancel hbp]
  · intro k hk
    refine ⟨p*k, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      simp only [surv, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      rcases hk with ⟨⟨hk1, hkx⟩, hkdiv⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right p k⟩
      · exact Nat.mul_pos hp hk1
      · have hmul : k * p ≤ x := Nat.mul_le_of_le_div p k x hkx
        rwa [Nat.mul_comm] at hmul
      · exact noDivBy_mul_left_of_coprime hkdiv hc
    · exact Nat.mul_div_right k hp

private lemma surv_cons_card (x p : Nat) (ps : List Nat)
    (hp : 0 < p) (hc : ∀ q ∈ ps, Nat.Coprime p q) :
    (surv x (p::ps)).card = (surv x ps).card - (surv (x / p) ps).card := by
  classical
  have hpart : (surv x ps).filter (fun m => ¬ p ∣ m) = surv x (p::ps) := by
    ext m
    simp only [surv, Finset.mem_filter, Finset.mem_Icc, noDivBy]
    tauto
  have hbad : (surv x ps).filter (fun m => p ∣ m) = bad x p ps := rfl
  have hsum := Finset.card_filter_add_card_filter_not (s := surv x ps) (p := fun m => p ∣ m)
  rw [hbad, bad_card_eq x p ps hp hc, hpart] at hsum
  omega

private theorem phiList_card (x : Nat) (L : List Nat)
    (hpos : ∀ p ∈ L, 1 < p)
    (hcop : L.Pairwise Nat.Coprime) :
    phiList x L = (surv x L).card := by
  classical
  induction L generalizing x with
  | nil => simp [phiList, surv, noDivBy, Nat.card_Icc]
  | cons p ps ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hpos
    rw [List.pairwise_cons] at hcop
    rcases hcop with ⟨hcp, hcps⟩
    have hp1 := hpos.1
    have hp : 0 < p := by omega
    have hposps := hpos.2
    unfold phiList
    split
    · subst x; simp [surv]
    split
    · subst x
      have hs : surv 1 (p :: ps) = {1} := by
        ext m
        simp only [surv, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
        constructor
        · intro hm; omega
        · intro hm
          subst hm
          refine ⟨⟨le_rfl, le_rfl⟩, ?_⟩
          simp only [noDivBy]
          constructor
          · intro hd
            have : p ≤ 1 := Nat.le_of_dvd (by norm_num) hd
            omega
          · exact noDivBy_one_of_gt_one hposps
      rw [hs]
      simp
    split
    · rename_i hxlt
      have hsame : surv x (p::ps) = surv x ps := by
        ext m
        simp only [surv, Finset.mem_filter, Finset.mem_Icc, noDivBy]
        constructor
        · intro h; exact ⟨h.1, h.2.2⟩
        · intro h
          refine ⟨h.1, ?_, h.2⟩
          intro hpd
          have hmp : p ≤ m := Nat.le_of_dvd (by omega) hpd
          omega
      rw [ih x hposps hcps, hsame]
    · rw [ih x hposps hcps, ih (x/p) hposps hcps]
      exact (surv_cons_card x p ps hp hcp).symm
private def small46Asc : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]
private def small46Desc : List Nat := [199,197,193,191,181,179,173,167,163,157,151,149,139,137,131,127,113,109,107,103,101,97,89,83,79,73,71,67,61,59,53,47,43,41,37,31,29,23,19,17,13,11,7,5,3,2]
private def small44Desc : List Nat := [193,191,181,179,173,167,163,157,151,149,139,137,131,127,113,109,107,103,101,97,89,83,79,73,71,67,61,59,53,47,43,41,37,31,29,23,19,17,13,11,7,5,3,2]
private def bigAsc : List Nat := [211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857]
private def compPhiSum (X : Nat) (small big : List Nat) : Nat :=
  big.foldl (fun s p => s + (phiList (X / p) small - phiList (p - 1) small)) 0
private def compBlock_0 : List Nat := [211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353]
private lemma compBlock_val_0 : compPhiSum 8165753 small44Desc compBlock_0 = 79205 := by
  decide
private def compBlock_1 : List Nat := [359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503]
private lemma compBlock_val_1 : compPhiSum 8165753 small44Desc compBlock_1 = 52224 := by
  decide
private def compBlock_2 : List Nat := [509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661]
private lemma compBlock_val_2 : compPhiSum 8165753 small44Desc compBlock_2 = 38104 := by
  decide
private def compBlock_3 : List Nat := [673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839]
private lemma compBlock_val_3 : compPhiSum 8165753 small44Desc compBlock_3 = 29564 := by
  decide
private def compBlock_4 : List Nat := [853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019]
private lemma compBlock_val_4 : compPhiSum 8165753 small44Desc compBlock_4 = 23379 := by
  decide
private def compBlock_5 : List Nat := [1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193]
private lemma compBlock_val_5 : compPhiSum 8165753 small44Desc compBlock_5 = 19027 := by
  decide
private def compBlock_6 : List Nat := [1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381]
private lemma compBlock_val_6 : compPhiSum 8165753 small44Desc compBlock_6 = 15449 := by
  decide
private def compBlock_7 : List Nat := [1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559]
private lemma compBlock_val_7 : compPhiSum 8165753 small44Desc compBlock_7 = 12409 := by
  decide
private def compBlock_8 : List Nat := [1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741]
private lemma compBlock_val_8 : compPhiSum 8165753 small44Desc compBlock_8 = 10148 := by
  decide
private def compBlock_9 : List Nat := [1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949]
private lemma compBlock_val_9 : compPhiSum 8165753 small44Desc compBlock_9 = 7983 := by
  decide
private def compBlock_10 : List Nat := [1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131]
private lemma compBlock_val_10 : compPhiSum 8165753 small44Desc compBlock_10 = 6091 := by
  decide
private def compBlock_11 : List Nat := [2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339]
private lemma compBlock_val_11 : compPhiSum 8165753 small44Desc compBlock_11 = 4400 := by
  decide
private def compBlock_12 : List Nat := [2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539]
private lemma compBlock_val_12 : compPhiSum 8165753 small44Desc compBlock_12 = 2880 := by
  decide
private def compBlock_13 : List Nat := [2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713]
private lemma compBlock_val_13 : compPhiSum 8165753 small44Desc compBlock_13 = 1448 := by
  decide
private def compBlock_14 : List Nat := [2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857]
private lemma compBlock_val_14 : compPhiSum 8165753 small44Desc compBlock_14 = 333 := by
  decide

private lemma phi_main_val : phiList 8165753 small46Desc = 852771 := by
  decide
private lemma small46_pairwise : small46Desc.Pairwise Nat.Coprime := by decide
private lemma small46_gt_one : ∀ p ∈ small46Desc, 1 < p := by decide
private lemma small44_pairwise : small44Desc.Pairwise Nat.Coprime := by decide
private lemma small44_gt_one : ∀ p ∈ small44Desc, 1 < p := by decide
private lemma small46_card : small46Asc.toFinset.card = 46 := by decide
private lemma small46Asc_prime : ∀ {p}, p ∈ small46Asc → Nat.Prime p := by decide
private lemma small46Asc_le199 : ∀ {p}, p ∈ small46Asc → p ≤ 199 := by decide
private lemma small46_subset_primeRange : small46Asc.toFinset ⊆ (Finset.range 8165754).filter Nat.Prime := by
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range]
  have hpList : p ∈ small46Asc := by simpa using hp
  have hle := small46Asc_le199 hpList
  exact ⟨by omega, small46Asc_prime hpList⟩
private lemma small46Asc_subset_small46Desc : ∀ {p}, p ∈ small46Asc → p ∈ small46Desc := by decide
private lemma small44Desc_subset_small46Desc : ∀ {p}, p ∈ small44Desc → p ∈ small46Desc := by decide
private lemma small44_le_193 : ∀ {p}, p ∈ small44Desc → p ≤ 193 := by decide
private lemma bigAsc_nodup : bigAsc.Nodup := by decide
private lemma bigAsc_sq_le : ∀ {p}, p ∈ bigAsc → p * p ≤ 8165753 := by decide
private lemma bigAsc_ge200 : ∀ {p}, p ∈ bigAsc → 200 ≤ p := by decide
private lemma bigAsc_le2857 : ∀ {p}, p ∈ bigAsc → p ≤ 2857 := by decide

private noncomputable def pFinset : Finset Nat := bigAsc.toFinset

private lemma mem_small46Desc_of_prime_le199 {p : Nat} (hp : Nat.Prime p) (hle : p ≤ 199) : p ∈ small46Desc := by
  have h2 : 2 ≤ p := hp.two_le
  interval_cases p <;> first | contradiction | norm_num [small46Desc] at hp ⊢

private noncomputable def S : Finset Nat := surv 8165753 small46Desc
private noncomputable def Pgt : Finset Nat := S.filter Nat.Prime
private noncomputable def Csurv : Finset Nat := S.filter (fun m => m ≠ 1 ∧ ¬ Nat.Prime m)
private noncomputable def qFinset (p : Nat) : Finset Nat :=
  (Finset.Icc p (8165753 / p)).filter (fun q => noDivBy small44Desc q)
private noncomputable def compPairs : Finset (Sigma (fun _p : Nat => Nat)) :=
  pFinset.sigma (fun p => qFinset p)

private lemma S_card : S.card = 852771 := by
  unfold S
  rw [← phiList_card 8165753 small46Desc small46_gt_one small46_pairwise]
  exact phi_main_val.symm

private lemma pFinset_sq_le {p : Nat} (hp : p ∈ pFinset) : p * p ≤ 8165753 := by
  exact bigAsc_sq_le (by simpa [pFinset] using hp)

private lemma qFinset_card (p : Nat) (hp : p ∈ pFinset) :
    (qFinset p).card = phiList (8165753 / p) small44Desc - phiList (p - 1) small44Desc := by
  classical
  have hpList : p ∈ bigAsc := by simpa [pFinset] using hp
  have hp200 : 200 ≤ p := bigAsc_ge200 hpList
  have hp2 : 0 < p := by omega
  have hp_le_div : p - 1 ≤ 8165753 / p := by
    have hsq := pFinset_sq_le hp
    have hmul : (p - 1) * p ≤ 8165753 := by
      exact (Nat.mul_le_mul_right p (Nat.pred_le p)).trans hsq
    exact (Nat.le_div_iff_mul_le hp2).2 hmul
  have hqeq : qFinset p = surv (8165753 / p) small44Desc \ surv (p - 1) small44Desc := by
    ext q
    simp only [qFinset, surv, Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff]
    constructor
    · intro h
      rcases h with ⟨⟨hqp, hqhi⟩, hnd⟩
      refine ⟨⟨⟨by omega, hqhi⟩, hnd⟩, ?_⟩
      intro hs
      exact (not_lt_of_ge hqp) (by omega)
    · intro h
      rcases h with ⟨⟨⟨hq1, hqhi⟩, hnd⟩, hnot⟩
      refine ⟨⟨?_, hqhi⟩, hnd⟩
      by_contra hlt
      have hle : q ≤ p - 1 := by omega
      exact hnot ⟨⟨hq1, hle⟩, hnd⟩
  rw [hqeq]
  have hsub : surv (p - 1) small44Desc ⊆ surv (8165753 / p) small44Desc := by
    intro q hq
    simp only [surv, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.trans hp_le_div⟩, hq.2⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [← phiList_card (8165753 / p) small44Desc small44_gt_one small44_pairwise,
      ← phiList_card (p - 1) small44Desc small44_gt_one small44_pairwise] at hcard
  omega

private lemma foldl_add_zero (f : Nat → Nat) (L : List Nat) (t : Nat) :
    L.foldl (fun s p => s + f p) t = t + L.foldl (fun s p => s + f p) 0 := by
  induction L generalizing t with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih (t + f p)]
    rw [show 0 + f p = f p by omega]
    rw [ih (f p)]
    exact Nat.add_assoc t (f p) _

private lemma compPhiSum_append (X : Nat) (small a b : List Nat) :
    compPhiSum X small (a ++ b) = compPhiSum X small a + compPhiSum X small b := by
  unfold compPhiSum
  rw [List.foldl_append]
  exact foldl_add_zero (fun p => phiList (X / p) small - phiList (p - 1) small) b _

private lemma compPhiSum_big_val : compPhiSum 8165753 small44Desc bigAsc = 302644 := by
  rw [show bigAsc = compBlock_0 ++ compBlock_1 ++ compBlock_2 ++ compBlock_3 ++ compBlock_4 ++ compBlock_5 ++ compBlock_6 ++ compBlock_7 ++ compBlock_8 ++ compBlock_9 ++ compBlock_10 ++ compBlock_11 ++ compBlock_12 ++ compBlock_13 ++ compBlock_14 by decide]
  repeat rw [compPhiSum_append]
  rw [compBlock_val_0, compBlock_val_1, compBlock_val_2, compBlock_val_3, compBlock_val_4,
    compBlock_val_5, compBlock_val_6, compBlock_val_7, compBlock_val_8, compBlock_val_9,
    compBlock_val_10, compBlock_val_11, compBlock_val_12, compBlock_val_13, compBlock_val_14]

private lemma sum_toFinset_eq_compPhiSum (L : List Nat) (hL : L.Nodup) :
    (∑ p ∈ L.toFinset, (phiList (8165753 / p) small44Desc - phiList (p - 1) small44Desc)) =
      compPhiSum 8165753 small44Desc L := by
  induction L with
  | nil => simp [compPhiSum]
  | cons p ps ih =>
    simp only [List.nodup_cons] at hL
    rw [List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hL.1)]
    rw [ih hL.2]
    unfold compPhiSum
    simp only [List.foldl_cons]
    rw [show 0 + (phiList (8165753 / p) small44Desc - phiList (p - 1) small44Desc) =
        (phiList (8165753 / p) small44Desc - phiList (p - 1) small44Desc) by omega]
    rw [← foldl_add_zero (fun p => phiList (8165753 / p) small44Desc - phiList (p - 1) small44Desc) ps
      (phiList (8165753 / p) small44Desc - phiList (p - 1) small44Desc)]


private lemma compPairs_card : compPairs.card = 302644 := by
  classical
  unfold compPairs pFinset
  rw [Finset.card_sigma]
  change (∑ x ∈ bigAsc.toFinset, (qFinset x).card) = 302644
  rw [show (∑ x ∈ bigAsc.toFinset, (qFinset x).card) =
      (∑ x ∈ bigAsc.toFinset, (phiList (8165753 / x) small44Desc - phiList (x - 1) small44Desc)) by
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [qFinset_card p (by simpa [pFinset] using hp)]]
  rw [sum_toFinset_eq_compPhiSum bigAsc bigAsc_nodup, compPhiSum_big_val]
private lemma mem_bigAsc_block_0 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 200 200) := by
  decide

private lemma mem_bigAsc_block_1 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 400 200) := by
  decide

private lemma mem_bigAsc_block_2 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 600 200) := by
  decide

private lemma mem_bigAsc_block_3 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 800 200) := by
  decide

private lemma mem_bigAsc_block_4 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 1000 200) := by
  decide

private lemma mem_bigAsc_block_5 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 1200 200) := by
  decide

private lemma mem_bigAsc_block_6 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 1400 200) := by
  decide

private lemma mem_bigAsc_block_7 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 1600 200) := by
  decide

private lemma mem_bigAsc_block_8 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 1800 200) := by
  decide

private lemma mem_bigAsc_block_9 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 2000 200) := by
  decide

private lemma mem_bigAsc_block_10 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 2200 200) := by
  decide

private lemma mem_bigAsc_block_11 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 2400 200) := by
  decide

private lemma mem_bigAsc_block_12 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 2600 200) := by
  decide

private lemma mem_bigAsc_block_13 :
    List.Forall (fun p => noDivBy small44Desc p → p ∈ bigAsc) (List.range' 2800 58) := by
  decide

private lemma mem_bigAsc_of_range_noDiv {p : Nat} (hlo : 200 ≤ p) (hhi : p ≤ 2857)
    (hnd : noDivBy small44Desc p) : p ∈ bigAsc := by
  by_cases h0 : p ≤ 399
  · have hpI : p ∈ List.range' 200 200 := by
                              refine List.mem_range'.2 ⟨p - 200, ?_, ?_⟩
                              · omega
                              · omega
    exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_0) p hpI hnd
  · by_cases h1 : p ≤ 599
    · have hpI : p ∈ List.range' 400 200 := by
                              refine List.mem_range'.2 ⟨p - 400, ?_, ?_⟩
                              · omega
                              · omega
      exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_1) p hpI hnd
    · by_cases h2 : p ≤ 799
      · have hpI : p ∈ List.range' 600 200 := by
                              refine List.mem_range'.2 ⟨p - 600, ?_, ?_⟩
                              · omega
                              · omega
        exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_2) p hpI hnd
      · by_cases h3 : p ≤ 999
        · have hpI : p ∈ List.range' 800 200 := by
                              refine List.mem_range'.2 ⟨p - 800, ?_, ?_⟩
                              · omega
                              · omega
          exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_3) p hpI hnd
        · by_cases h4 : p ≤ 1199
          · have hpI : p ∈ List.range' 1000 200 := by
                              refine List.mem_range'.2 ⟨p - 1000, ?_, ?_⟩
                              · omega
                              · omega
            exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_4) p hpI hnd
          · by_cases h5 : p ≤ 1399
            · have hpI : p ∈ List.range' 1200 200 := by
                              refine List.mem_range'.2 ⟨p - 1200, ?_, ?_⟩
                              · omega
                              · omega
              exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_5) p hpI hnd
            · by_cases h6 : p ≤ 1599
              · have hpI : p ∈ List.range' 1400 200 := by
                              refine List.mem_range'.2 ⟨p - 1400, ?_, ?_⟩
                              · omega
                              · omega
                exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_6) p hpI hnd
              · by_cases h7 : p ≤ 1799
                · have hpI : p ∈ List.range' 1600 200 := by
                              refine List.mem_range'.2 ⟨p - 1600, ?_, ?_⟩
                              · omega
                              · omega
                  exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_7) p hpI hnd
                · by_cases h8 : p ≤ 1999
                  · have hpI : p ∈ List.range' 1800 200 := by
                              refine List.mem_range'.2 ⟨p - 1800, ?_, ?_⟩
                              · omega
                              · omega
                    exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_8) p hpI hnd
                  · by_cases h9 : p ≤ 2199
                    · have hpI : p ∈ List.range' 2000 200 := by
                              refine List.mem_range'.2 ⟨p - 2000, ?_, ?_⟩
                              · omega
                              · omega
                      exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_9) p hpI hnd
                    · by_cases h10 : p ≤ 2399
                      · have hpI : p ∈ List.range' 2200 200 := by
                              refine List.mem_range'.2 ⟨p - 2200, ?_, ?_⟩
                              · omega
                              · omega
                        exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_10) p hpI hnd
                      · by_cases h11 : p ≤ 2599
                        · have hpI : p ∈ List.range' 2400 200 := by
                              refine List.mem_range'.2 ⟨p - 2400, ?_, ?_⟩
                              · omega
                              · omega
                          exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_11) p hpI hnd
                        · by_cases h12 : p ≤ 2799
                          · have hpI : p ∈ List.range' 2600 200 := by
                              refine List.mem_range'.2 ⟨p - 2600, ?_, ?_⟩
                              · omega
                              · omega
                            exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_12) p hpI hnd
                          · have hpI : p ∈ List.range' 2800 58 := by
                              refine List.mem_range'.2 ⟨p - 2800, ?_, ?_⟩
                              · omega
                              · omega
                            exact (List.forall_iff_forall_mem.mp mem_bigAsc_block_13) p hpI hnd

private lemma prime_count_lower_from (T : Finset Nat)
    (hTcard : T.card = 852771)
    (hTmem : ∀ m, m ∈ T ↔ 1 ≤ m ∧ m ≤ 8165753 ∧ noDivBy small46Desc m) :
    550172 ≤ Nat.count Nat.Prime 8165754 := by
  classical
  let Pgt : Finset Nat := T.filter Nat.Prime
  let C : Finset Nat := T.filter (fun m => m ≠ 1 ∧ ¬ Nat.Prime m)
  have hC_le : C.card ≤ compPairs.card := by
    refine Finset.card_le_card_of_injOn (fun m => Sigma.mk (Nat.minFac m) (m / Nat.minFac m)) ?maps ?inj
    · intro m hm
      change m ∈ T.filter (fun m => m ≠ 1 ∧ ¬ Nat.Prime m) at hm
      have hmf : m ∈ T ∧ (m ≠ 1 ∧ ¬ Nat.Prime m) := by exact Finset.mem_filter.mp hm
      have hmT : m ∈ T := by exact hmf.1
      have hmne1 : m ≠ 1 := by exact hmf.2.1
      have hmnp : ¬ Nat.Prime m := by exact hmf.2.2
      have hmS := (hTmem m).1 hmT
      rcases hmS with ⟨hm1, hmX, hmnd⟩
      have hpos : 0 < m := by omega
      let p := Nat.minFac m
      have hpprime : Nat.Prime p := Nat.minFac_prime hmne1
      have hpdvd : p ∣ m := Nat.minFac_dvd m
      have hpgt199 : 199 < p := by
        by_contra hnot
        have hple : p ≤ 199 := by omega
        have hpsmall : p ∈ small46Desc := mem_small46Desc_of_prime_le199 hpprime hple
        exact noDivBy_of_mem hmnd hpsmall hpdvd
      have hple2857 : p ≤ 2857 := by
        have hsq := Nat.minFac_sq_le_self hpos hmnp
        change p ^ 2 ≤ m at hsq
        by_contra hnot
        have hpge : 2858 ≤ p := by omega
        have hsq2 : 2858 * 2858 ≤ p * p := Nat.mul_le_mul hpge hpge
        have hp2eq : p * p = p ^ 2 := by ring
        rw [hp2eq] at hsq2
        norm_num at hsq2
        omega
      have hpNoDiv44 : noDivBy small44Desc p := by
        refine noDivBy_of_prime_gt_all hpprime small44_gt_one ?_
        intro r hr
        have hrle : r ≤ 193 := small44_le_193 hr
        omega
      have hpFin : p ∈ pFinset := by
        have hp200 : 200 ≤ p := by omega
        exact (by simpa [pFinset] using mem_bigAsc_of_range_noDiv hp200 hple2857 hpNoDiv44)
      change Sigma.mk p (m / p) ∈ compPairs
      refine Finset.mem_sigma.mpr ⟨hpFin, ?_⟩
      simp only [qFinset, Finset.mem_filter, Finset.mem_Icc]
      have hqlo : p ≤ m / p := Nat.minFac_le_div hpos hmnp
      have hqhi : m / p ≤ 8165753 / p := Nat.div_le_div_right hmX
      refine ⟨⟨hqlo, hqhi⟩, ?_⟩
      have hmnd44 : noDivBy small44Desc m :=
        noDivBy_of_subset hmnd (fun q hq => small44Desc_subset_small46Desc hq)
      exact noDivBy_div_of_dvd hmnd44 hpdvd (fun q hq => (hpprime.coprime_iff_not_dvd).2 (by
        intro hpq
        have qpos : 0 < q := by
          have qgt : 1 < q := small44_gt_one q hq
          omega
        have qltp : q < p := by
          have qle : q ≤ 193 := small44_le_193 hq
          omega
        have pleq : p ≤ q := Nat.le_of_dvd qpos hpq
        omega))
    · intro a ha b hb hEq
      injection hEq with hpEq hqEq
      have hqEq' : a / Nat.minFac b = b / Nat.minFac b := by
        rwa [hpEq] at hqEq
      calc
        a = Nat.minFac a * (a / Nat.minFac a) := by rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.minFac_dvd a)]
        _ = Nat.minFac b * (b / Nat.minFac b) := by rw [hpEq, hqEq']
        _ = b := by rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.minFac_dvd b)]
  have hpart : T.card ≤ 1 + Pgt.card + C.card := by
    let U : Finset Nat := ({1} : Finset Nat) ∪ Pgt ∪ C
    have hsub : T ⊆ U := by
      intro m hm
      by_cases h1 : m = 1
      · simp [U, h1]
      · by_cases hp : Nat.Prime m
        · simp [U, Pgt, hm, hp]
        · simp [U, C, hm, h1, hp]
    have hcard := Finset.card_le_card hsub
    have hU : U.card ≤ 1 + Pgt.card + C.card := by
      calc
        U.card ≤ (({1} : Finset Nat) ∪ Pgt).card + C.card := by
          unfold U
          exact Finset.card_union_le _ _
        _ ≤ (({1} : Finset Nat).card + Pgt.card) + C.card := by
          exact Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ = 1 + Pgt.card + C.card := by simp [add_assoc]
    exact hcard.trans hU
  have hdis : Disjoint small46Asc.toFinset Pgt := by
    rw [Finset.disjoint_left]
    intro p hpSmall hpP
    simp only [Pgt, Finset.mem_filter] at hpP
    have hpT := (hTmem p).1 hpP.1
    exact noDivBy_of_mem hpT.2.2 (small46Asc_subset_small46Desc hpSmall) (dvd_refl p)
  let primeFin : Finset Nat := (Finset.range 8165754).filter Nat.Prime
  have hPrimeCard : primeFin.card = Nat.count Nat.Prime 8165754 := by
    simp [primeFin, Nat.count_eq_card_filter_range]
  have hUnionSub : small46Asc.toFinset ∪ Pgt ⊆ primeFin := by
    intro p hp
    simp only [Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact small46_subset_primeRange hp
    · simp only [primeFin, Finset.mem_filter, Finset.mem_range]
      simp only [Pgt, Finset.mem_filter] at hp
      have hpT := (hTmem p).1 hp.1
      exact ⟨by omega, hp.2⟩
  have hcardUnion : (small46Asc.toFinset ∪ Pgt).card = 46 + Pgt.card := by
    rw [Finset.card_union_of_disjoint hdis, small46_card]
  have hpc_ge : 46 + Pgt.card ≤ Nat.count Nat.Prime 8165754 := by
    rw [← hPrimeCard, ← hcardUnion]
    exact Finset.card_le_card hUnionSub
  have hC : C.card ≤ 302644 := by simpa [compPairs_card] using hC_le
  omega

private lemma prime_count_lower : 550172 ≤ Nat.count Nat.Prime 8165754 := by
  let T : Finset Nat := surv 8165753 small46Desc
  have hTcard : T.card = 852771 := by
    change (surv 8165753 small46Desc).card = 852771
    rw [← phiList_card 8165753 small46Desc small46_gt_one small46_pairwise]
    exact phi_main_val.symm
  have hTmem : ∀ m, m ∈ T ↔ 1 ≤ m ∧ m ≤ 8165753 ∧ noDivBy small46Desc m := by
    intro m
    change m ∈ surv 8165753 small46Desc ↔ _
    exact mem_surv_iff
  exact prime_count_lower_from T hTcard hTmem

private lemma prime_count_lower_gt : 550171 < Nat.count Nat.Prime 8165754 := by
  have := prime_count_lower
  omega


theorem oeis_232616_conjecture_i.disproof :
    ¬ (∀ (n : ℕ) (hn : 0 < n),
      A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1)) := by
  intro h
  have hn : 0 < 550172 := by norm_num
  have hbad := h 550172 hn
  have hp : Nat.nth Nat.Prime (550172 - 1) < 8165754 := by
    rw [← Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime]
    norm_num
    exact prime_count_lower_gt
  have hA : 16331504 ≤ A232616 550172 := by
    unfold A232616
    rw [dif_neg (by norm_num : ¬ 550172 = 0)]
    let S : Set ℕ := {m | A232616_prop 550172 m}
    change 16331504 ≤ sInf S
    refine le_csInf (s := S) ?hne ?hlb
    · exact ⟨82496875, A232616_counter_complete⟩
    · intro m hm
      by_contra hlt
      have hmle : m ≤ 16331503 := by omega
      exact A232616_counter_not_bound (A232616_prop_mono 550172 hmle hm)
  have hbnd : 2 * (Nat.nth Nat.Prime (550172 - 1) - 1) ≤ 16331504 := by
    omega
  omega
