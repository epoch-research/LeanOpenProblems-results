import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 600

open Finset ZMod Nat Set Classical

abbrev NN : Nat := 550172
abbrev DD : Nat := 29400
abbrev GG : Nat := 196
abbrev QQ : Nat := 2807
abbrev INV : Nat := 131

def baseList : List Nat := [36,143,2,349,308,3,26,225,332,191,50,81,4,31,58,85,48,139,98,193,220,15,122,237,328,287,146,5,204,311,170,29,60,171,10,37,64,27,118,77,172,199,226,101,216,307,266,125,72,183,290,149,8,39,150,173,16,43,6,97,56,151,178,205,80,195,286,245,104,51,162,269,128,475,18,129,152,11,22,49,76,35,130,157,184,59,174,265,224,83,30,141,248,107,454,413,108,131,330,437,28,55,14,109,136,163,38,153,244,203,62,9,120,227,86,433,392,87,110,309,416,7,34,61,88,115,142,17,132,223,182,41,304,99,206,65,412,371,66,89,288,395,254,13,40,67,94,121,148,111,202,161,20,283,78,185,44,391,350,45,68,267,374,233,12,19,46,73,100,127,90,181,140,235,262,57,164,23,370,329,24,47,246,353,212,71,102,25,52,79,106,69,160,119,214,241]

def base (c : Nat) : Nat := baseList.getD c 0

def residueBase (a : Nat) : Nat := (2^a - a) % NN

def wit (r : Nat) : Nat :=
  let a := base (r % GG)
  let b := residueBase a
  let q := ((b + NN - (r % NN)) % NN) / GG
  let t := (q * INV) % QQ
  a + t * DD

lemma two_pow_ge (k : Nat) : k ≤ 2^k := le_of_lt k.lt_two_pow_self

lemma cast_expr (k : Nat) :
    (Nat.cast (2^k - k) : ZMod NN) = (2 : ZMod NN)^k - (k : ZMod NN) := by
  rw [Nat.cast_sub (two_pow_ge k), Nat.cast_pow]
  rfl

lemma pow_period_odd : 2^29400 ≡ 1 [MOD 137543] := by
  have h343 : 2^147 ≡ 1 [MOD 343] := by norm_num [Nat.ModEq]
  have h401 : 2^200 ≡ 1 [MOD 401] := by norm_num [Nat.ModEq]
  have h343D : 2^29400 ≡ 1 [MOD 343] := by
    have h := h343.pow 200
    rw [← pow_mul] at h
    norm_num at h
    exact h
  have h401D : 2^29400 ≡ 1 [MOD 401] := by
    have h := h401.pow 147
    rw [← pow_mul] at h
    norm_num at h
    exact h
  have hc : Nat.Coprime 343 401 := by norm_num
  have := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨h343D, h401D⟩
  norm_num at this ⊢
  exact this

lemma pow_two_mod4_zero {e : Nat} (he : 2 ≤ e) : 2^e ≡ 0 [MOD 4] := by
  rw [Nat.modEq_zero_iff_dvd]
  use 2^(e-2)
  have h : e = 2 + (e - 2) := by omega
  rw [h, pow_add]
  norm_num

lemma pow_period_modEq (a t : Nat) (ha : 2 ≤ a) : 2^(a + t * DD) ≡ 2^a [MOD NN] := by
  have hO0 : (2^29400)^t ≡ 1^t [MOD 137543] := (pow_period_odd.pow t)
  have hO : 2^(a + t * 29400) ≡ 2^a [MOD 137543] := by
    calc
      2^(a + t * 29400) = 2^a * (2^29400)^t := by
        have heq : 2^(t * 29400) = (2^29400)^t := by
          rw [mul_comm t 29400, pow_mul]
        rw [pow_add, heq]
      _ ≡ 2^a * 1^t [MOD 137543] := hO0.mul_left (2^a)
      _ = 2^a := by simp
  have h4 : 2^(a + t * 29400) ≡ 2^a [MOD 4] := by
    exact (pow_two_mod4_zero (by omega : 2 ≤ a + t * 29400)).trans (pow_two_mod4_zero ha).symm
  have h := Nat.mod_lcm h4 hO
  have hlcm : Nat.lcm 4 137543 = 550172 := by norm_num [Nat.lcm, Nat.gcd]
  simpa [hlcm, NN, DD] using h

lemma pow_period_zmod (a t : Nat) (ha : 2 ≤ a) :
    ((2 : ZMod NN)^(a + t * DD)) = (2 : ZMod NN)^a := by
  calc
    ((2 : ZMod NN)^(a + t * DD)) = (Nat.cast (2^(a + t * DD)) : ZMod NN) := by norm_num [Nat.cast_pow]
    _ = (Nat.cast (2^a) : ZMod NN) := (ZMod.natCast_eq_natCast_iff (2^(a + t * DD)) (2^a) NN).mpr (pow_period_modEq a t ha)
    _ = (2 : ZMod NN)^a := by norm_num [Nat.cast_pow]

lemma residue_shift_zmod (a t : Nat) (ha : 2 ≤ a) :
    (Nat.cast (2^(a + t * DD) - (a + t * DD)) : ZMod NN)
      = (Nat.cast (2^a - a) : ZMod NN) - (t * DD : ZMod NN) := by
  rw [cast_expr (a + t * DD), cast_expr a, pow_period_zmod a t ha]
  simp [Nat.cast_add, Nat.cast_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma dvd_x (b r : Nat) (hb : b < NN) (hr : r < NN) (hbr : b % GG = r % GG) :
    GG ∣ ((b + NN - r) % NN) := by
  have hbrm : b ≡ r [MOD GG] := by simpa [Nat.ModEq] using hbr
  have hN : NN ≡ 0 [MOD GG] := by norm_num [NN, GG, Nat.ModEq]
  have hsum : b + NN - r ≡ 0 [MOD GG] := by
    have h1 : b + NN ≡ r + 0 [MOD GG] := hbrm.add hN
    have hsub := Nat.ModEq.sub (by omega : r ≤ b + NN) (by omega : r ≤ r + 0) h1 (Nat.ModEq.rfl (a := r) (n := GG))
    simpa using hsub
  have hxmod : ((b + NN - r) % NN) ≡ (b + NN - r) [MOD GG] :=
    (Nat.mod_modEq _ NN).of_dvd (by norm_num [NN, GG])
  exact Nat.modEq_zero_iff_dvd.mp (hxmod.trans hsum)

lemma divGG_eq (b r : Nat) (hb : b < NN) (hr : r < NN) (hbr : b % GG = r % GG) :
    ((b + NN - r) % NN) = GG * (((b + NN - r) % NN) / GG) := by
  have hd := dvd_x b r hb hr hbr
  exact (Nat.mul_div_cancel' hd).symm

lemma q_lt (b r : Nat) : (((b + NN - r) % NN) / GG) < QQ := by
  have hx : ((b + NN - r) % NN) < NN := by exact Nat.mod_lt _ (by norm_num [NN])
  have hN : NN = GG * QQ := by norm_num [NN, GG, QQ]
  rw [hN] at hx
  exact Nat.div_lt_of_lt_mul hx

lemma t_congr (q : Nat) : (q * INV) % QQ * 150 ≡ q [MOD QQ] := by
  have h : (q * INV) % QQ ≡ q * INV [MOD QQ] := Nat.mod_modEq _ _
  have h2 := h.mul_right 150
  have hinv : INV * 150 ≡ 1 [MOD QQ] := by norm_num [INV, QQ, Nat.ModEq]
  have hq : q * INV * 150 ≡ q * 1 [MOD QQ] := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hinv.mul_left q
  exact h2.trans (by simpa [mul_assoc, mul_comm, mul_left_comm] using hq)

-- generated base spec will be inserted later

lemma base_spec (c : Fin GG) :
    2 ≤ base c.val ∧ base c.val ≤ 475 ∧ residueBase (base c.val) % GG = c.val := by
  fin_cases c <;> norm_num [base, baseList, residueBase, NN, GG]

lemma residueBase_cast (a : Nat) :
    (Nat.cast (residueBase a) : ZMod NN) = (Nat.cast (2^a - a) : ZMod NN) := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

lemma mod_cast_eq (x : Nat) : (Nat.cast (x % NN) : ZMod NN) = (Nat.cast x : ZMod NN) := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

lemma tD_eq_x_zmod (b r : Nat) (hr : r < NN) (hbr : b % GG = r % GG) (hb : b < NN) :
    let q := ((b + NN - r) % NN) / GG
    let t := (q * INV) % QQ
    (Nat.cast (t * DD) : ZMod NN) = (Nat.cast ((b + NN - r) % NN) : ZMod NN) := by
  intro q t
  have hxdiv : ((b + NN - r) % NN) = GG * q := by
    simpa [q] using divGG_eq b r hb hr hbr
  have htq : t * 150 ≡ q [MOD QQ] := by
    simpa [t, mul_comm, mul_left_comm, mul_assoc] using t_congr q
  have hmul : GG * (t * 150) ≡ GG * q [MOD GG * QQ] := htq.mul_left' GG
  have hmul' : t * DD ≡ ((b + NN - r) % NN) [MOD NN] := by
    rw [hxdiv]
    have hNN : GG * QQ = NN := by norm_num [GG, QQ, NN]
    have hDD : DD = GG * 150 := by norm_num [DD, GG]
    simpa [hNN, hDD, mul_assoc, mul_comm, mul_left_comm] using hmul
  exact (ZMod.natCast_eq_natCast_iff (t * DD) ((b + NN - r) % NN) NN).mpr hmul'

lemma sub_x_eq_r_zmod (b r : Nat) (hr : r < NN) :
    (Nat.cast b : ZMod NN) - (Nat.cast ((b + NN - r) % NN) : ZMod NN) = (Nat.cast r : ZMod NN) := by
  rw [mod_cast_eq]
  have hsub : (Nat.cast (b + NN - r) : ZMod NN) = (Nat.cast b : ZMod NN) - (Nat.cast r : ZMod NN) := by
    rw [Nat.cast_sub (by omega : r ≤ b + NN), Nat.cast_add]
    have hN : (Nat.cast NN : ZMod NN) = 0 := by exact ZMod.natCast_self NN
    rw [hN, add_zero]
  rw [hsub]
  ring

lemma wit_bounds (r : Nat) : 1 ≤ wit r ∧ wit r ≤ 82496875 := by
  let a := base (r % GG)
  let q := ((residueBase a + NN - (r % NN)) % NN) / GG
  let t := (q * INV) % QQ
  have hs := base_spec (⟨r % GG, Nat.mod_lt _ (by norm_num [GG])⟩ : Fin GG)
  have ha2 : 2 ≤ a := by simpa [a] using hs.1
  have ha : a ≤ 475 := by simpa [a] using hs.2.1
  have ht : t < QQ := by exact Nat.mod_lt _ (by norm_num [QQ])
  have hw : wit r = a + t * DD := by simp [wit, a, q, t]
  rw [hw]
  norm_num [DD, QQ] at ht ⊢
  constructor <;> omega

lemma witness_hits (r : Nat) (hr : r < NN) :
    (Nat.cast (2^(wit r) - wit r) : ZMod NN) = (Nat.cast r : ZMod NN) := by
  unfold wit
  let c : Fin GG := ⟨r % GG, Nat.mod_lt _ (by norm_num [GG])⟩
  have hs := base_spec c
  have hcval : c.val = r % GG := rfl
  let a := base (r % GG)
  let b := residueBase a
  let q := ((b + NN - (r % NN)) % NN) / GG
  let t := (q * INV) % QQ
  have ha2 : 2 ≤ a := by simpa [a] using hs.1
  have hbNN : b < NN := by exact Nat.mod_lt _ (by norm_num [NN])
  have hbr : b % GG = (r % NN) % GG := by
    have hbase : b % GG = r % GG := by simpa [a, b, c, hcval] using hs.2.2
    have hrmod : (r % NN) % GG = r % GG := by
      have hdiv : GG ∣ NN := by norm_num [GG, NN]
      exact Nat.mod_mod_of_dvd r hdiv
    simpa [hrmod] using hbase
  have hrNN : r % NN < NN := Nat.mod_lt _ (by norm_num [NN])
  have htDx : (Nat.cast (t * DD) : ZMod NN) = (Nat.cast ((b + NN - (r % NN)) % NN) : ZMod NN) := by
    simpa [q, t] using tD_eq_x_zmod b (r % NN) hrNN hbr hbNN
  rw [residue_shift_zmod a t ha2]
  have hbcast : (Nat.cast (2^a - a) : ZMod NN) = (Nat.cast b : ZMod NN) := (residueBase_cast a).symm
  rw [hbcast]
  rw [← Nat.cast_mul, htDx]
  have hsub := sub_x_eq_r_zmod b (r % NN) hrNN
  rw [hsub]
  exact mod_cast_eq r
