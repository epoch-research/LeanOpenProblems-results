import FormalConjectures.Util.ProblemImports

section Defs
open Finset ZMod Nat Set Classical

def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    have hn : NeZero n := NeZero.mk h
    let S : Set ℕ := { m : ℕ | A232616_prop n m }
    sInf S
end Defs

section ComboContent
open Finset
namespace Cmb
set_option maxRecDepth 100000

def Q : ℕ := 6930
def kset : Finset ℕ := {1, 2, 3, 5, 6, 7, 10, 11, 12, 14, 18, 20, 21, 30, 33, 35, 36, 42, 44, 45, 55, 60, 63, 66, 70, 77, 84, 90, 99, 105, 110, 126, 132, 140, 154, 165, 180, 198, 210, 220, 231, 252, 308, 315, 330, 385, 396, 420, 462, 495, 630, 660, 693, 770, 924, 990, 1155, 1260, 1386, 1540, 1980, 2310, 2772, 3465, 4620, 6930, 13860}
def acoef : ℕ → ℤ
  | 1 => 6930
  | 2 => -6930
  | 3 => -6930
  | 5 => -6930
  | 6 => 6930
  | 7 => -6930
  | 10 => 6930
  | 11 => -6930
  | 12 => -6930
  | 14 => 6930
  | 18 => -6930
  | 20 => -2600
  | 21 => 9530
  | 30 => -6930
  | 33 => 6930
  | 35 => 2600
  | 36 => 6930
  | 42 => -16460
  | 44 => 4330
  | 45 => 2600
  | 55 => 6930
  | 60 => 9530
  | 63 => -7365
  | 66 => -2165
  | 70 => -9530
  | 77 => 2600
  | 84 => 9530
  | 90 => 5593
  | 99 => -5593
  | 105 => -5200
  | 110 => -6930
  | 126 => 14295
  | 132 => -4765
  | 140 => 2600
  | 154 => 6760
  | 165 => -11960
  | 180 => -10358
  | 198 => 7758
  | 210 => 17893
  | 220 => 3035
  | 231 => -11398
  | 252 => -15123
  | 308 => -1167
  | 315 => 7365
  | 330 => 16290
  | 385 => -8968
  | 396 => -127
  | 420 => -13563
  | 462 => 7270
  | 495 => 6293
  | 630 => -14391
  | 660 => -5635
  | 693 => 21756
  | 770 => 14730
  | 924 => 3258
  | 990 => -18423
  | 1155 => 13266
  | 1260 => 20620
  | 1386 => -23953
  | 1540 => -7599
  | 1980 => 17341
  | 2310 => -26648
  | 2772 => 15707
  | 3465 => -14072
  | 4620 => 15229
  | 6930 => 32145
  | 13860 => 9999
  | _ => 0

@[inline] def posS (r : Nat) : Nat := 6930*(r/1) + 6930*(r/6) + 6930*(r/10) + 6930*(r/14) + 9530*(r/21) + 6930*(r/33) + 2600*(r/35) + 6930*(r/36) + 4330*(r/44) + 2600*(r/45) + 6930*(r/55) + 9530*(r/60) + 2600*(r/77) + 9530*(r/84) + 5593*(r/90) + 14295*(r/126) + 2600*(r/140) + 6760*(r/154) + 7758*(r/198) + 17893*(r/210) + 3035*(r/220) + 7365*(r/315) + 16290*(r/330) + 7270*(r/462) + 6293*(r/495) + 21756*(r/693) + 14730*(r/770) + 3258*(r/924) + 13266*(r/1155) + 20620*(r/1260) + 17341*(r/1980) + 15707*(r/2772) + 15229*(r/4620) + 32145*(r/6930) + 9999*(r/13860)
@[inline] def negS (r : Nat) : Nat := 6930*(r/2) + 6930*(r/3) + 6930*(r/5) + 6930*(r/7) + 6930*(r/11) + 6930*(r/12) + 6930*(r/18) + 2600*(r/20) + 6930*(r/30) + 16460*(r/42) + 7365*(r/63) + 2165*(r/66) + 9530*(r/70) + 5593*(r/99) + 5200*(r/105) + 6930*(r/110) + 4765*(r/132) + 11960*(r/165) + 10358*(r/180) + 11398*(r/231) + 15123*(r/252) + 1167*(r/308) + 8968*(r/385) + 127*(r/396) + 13563*(r/420) + 14391*(r/630) + 5635*(r/660) + 18423*(r/990) + 23953*(r/1386) + 7599*(r/1540) + 26648*(r/2310) + 14072*(r/3465)
@[inline] def okb (r : Nat) : Bool := Nat.ble ((Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 6930 (Nat.div r 1)) (Nat.mul 6930 (Nat.div r 6))) (Nat.mul 6930 (Nat.div r 10))) (Nat.mul 6930 (Nat.div r 14))) (Nat.mul 9530 (Nat.div r 21))) (Nat.mul 6930 (Nat.div r 33))) (Nat.mul 2600 (Nat.div r 35))) (Nat.mul 6930 (Nat.div r 36))) (Nat.mul 4330 (Nat.div r 44))) (Nat.mul 2600 (Nat.div r 45))) (Nat.mul 6930 (Nat.div r 55))) (Nat.mul 9530 (Nat.div r 60))) (Nat.mul 2600 (Nat.div r 77))) (Nat.mul 9530 (Nat.div r 84))) (Nat.mul 5593 (Nat.div r 90))) (Nat.mul 14295 (Nat.div r 126))) (Nat.mul 2600 (Nat.div r 140))) (Nat.mul 6760 (Nat.div r 154))) (Nat.mul 7758 (Nat.div r 198))) (Nat.mul 17893 (Nat.div r 210))) (Nat.mul 3035 (Nat.div r 220))) (Nat.mul 7365 (Nat.div r 315))) (Nat.mul 16290 (Nat.div r 330))) (Nat.mul 7270 (Nat.div r 462))) (Nat.mul 6293 (Nat.div r 495))) (Nat.mul 21756 (Nat.div r 693))) (Nat.mul 14730 (Nat.div r 770))) (Nat.mul 3258 (Nat.div r 924))) (Nat.mul 13266 (Nat.div r 1155))) (Nat.mul 20620 (Nat.div r 1260))) (Nat.mul 17341 (Nat.div r 1980))) (Nat.mul 15707 (Nat.div r 2772))) (Nat.mul 15229 (Nat.div r 4620))) (Nat.mul 32145 (Nat.div r 6930))) (Nat.mul 9999 (Nat.div r 13860)))) (Nat.add 6930 ((Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 6930 (Nat.div r 2)) (Nat.mul 6930 (Nat.div r 3))) (Nat.mul 6930 (Nat.div r 5))) (Nat.mul 6930 (Nat.div r 7))) (Nat.mul 6930 (Nat.div r 11))) (Nat.mul 6930 (Nat.div r 12))) (Nat.mul 6930 (Nat.div r 18))) (Nat.mul 2600 (Nat.div r 20))) (Nat.mul 6930 (Nat.div r 30))) (Nat.mul 16460 (Nat.div r 42))) (Nat.mul 7365 (Nat.div r 63))) (Nat.mul 2165 (Nat.div r 66))) (Nat.mul 9530 (Nat.div r 70))) (Nat.mul 5593 (Nat.div r 99))) (Nat.mul 5200 (Nat.div r 105))) (Nat.mul 6930 (Nat.div r 110))) (Nat.mul 4765 (Nat.div r 132))) (Nat.mul 11960 (Nat.div r 165))) (Nat.mul 10358 (Nat.div r 180))) (Nat.mul 11398 (Nat.div r 231))) (Nat.mul 15123 (Nat.div r 252))) (Nat.mul 1167 (Nat.div r 308))) (Nat.mul 8968 (Nat.div r 385))) (Nat.mul 127 (Nat.div r 396))) (Nat.mul 13563 (Nat.div r 420))) (Nat.mul 14391 (Nat.div r 630))) (Nat.mul 5635 (Nat.div r 660))) (Nat.mul 18423 (Nat.div r 990))) (Nat.mul 23953 (Nat.div r 1386))) (Nat.mul 7599 (Nat.div r 1540))) (Nat.mul 26648 (Nat.div r 2310))) (Nat.mul 14072 (Nat.div r 3465)))))
theorem okb_iff (r : Nat) : okb r = true ↔ posS r ≤ 6930 + negS r := by
  unfold okb; rw [Nat.ble_eq]; exact Iff.rfl

def scan : Nat -> Nat -> Bool
  | 0, _ => true
  | (fuel+1), r => okb r && scan fuel (r+1)

theorem scan_all : scan 13860 0 = true := by decide +kernel

theorem scan_spec : ∀ fuel r0, scan fuel r0 = true →
    ∀ r, r0 ≤ r → r < r0 + fuel → okb r = true := by
  intro fuel
  induction fuel with
  | zero => intro r0 _ r hlo hr; omega
  | succ fuel ih =>
    intro r0 h r hlo hr
    simp only [scan] at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases Nat.eq_or_lt_of_le hlo with he | he
    · rw [← he]; exact h1
    · exact ih (r0+1) h2 r (by omega) (by omega)

theorem hk0 : ∀ k ∈ kset, 0 < k := by decide

theorem hsum0 : ∑ k ∈ kset, (acoef k : ℝ)/k = 0 := by
  rw [show kset = {1, 2, 3, 5, 6, 7, 10, 11, 12, 14, 18, 20, 21, 30, 33, 35, 36, 42, 44, 45, 55, 60, 63, 66, 70, 77, 84, 90, 99, 105, 110, 126, 132, 140, 154, 165, 180, 198, 210, 220, 231, 252, 308, 315, 330, 385, 396, 420, 462, 495, 630, 660, 693, 770, 924, 990, 1155, 1260, 1386, 1540, 1980, 2310, 2772, 3465, 4620, 6930, 13860} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [acoef]; norm_num

theorem hDk0 : ∑ k ∈ kset, acoef k * ((13860/k : ℕ):ℤ) = 0 := by
  rw [show kset = {1, 2, 3, 5, 6, 7, 10, 11, 12, 14, 18, 20, 21, 30, 33, 35, 36, 42, 44, 45, 55, 60, 63, 66, 70, 77, 84, 90, 99, 105, 110, 126, 132, 140, 154, 165, 180, 198, 210, 220, 231, 252, 308, 315, 330, 385, 396, 420, 462, 495, 630, 660, 693, 770, 924, 990, 1155, 1260, 1386, 1540, 1980, 2310, 2772, 3465, 4620, 6930, 13860} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [acoef]; norm_num

noncomputable def g (M : ℕ) : ℤ := ∑ k ∈ kset, acoef k * ((M / k : ℕ) : ℤ)

theorem g_flat (M : ℕ) : g M = (posS M : ℤ) - (negS M : ℤ) := by
  unfold g
  rw [show kset = {1, 2, 3, 5, 6, 7, 10, 11, 12, 14, 18, 20, 21, 30, 33, 35, 36, 42, 44, 45, 55, 60, 63, 66, 70, 77, 84, 90, 99, 105, 110, 126, 132, 140, 154, 165, 180, 198, 210, 220, 231, 252, 308, 315, 330, 385, 396, 420, 462, 495, 630, 660, 693, 770, 924, 990, 1155, 1260, 1386, 1540, 1980, 2310, 2772, 3465, 4620, 6930, 13860} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [acoef, posS, negS]
  push_cast; ring

theorem div_split (M k : ℕ) (hk : k ∣ 13860) (hk0 : 0 < k) :
    M / k = (M % 13860) / k + (13860 / k) * (M / 13860) := by
  conv_lhs => rw [← Nat.mod_add_div M 13860]
  rw [show (13860 : ℕ) * (M / 13860) = k * ((13860/k) * (M / 13860)) by
        rw [← mul_assoc, Nat.mul_div_cancel' hk]]
  rw [Nat.add_mul_div_left _ _ hk0]

theorem g_period (M : ℕ) : g M = g (M % 13860) := by
  have hkd : ∀ k ∈ kset, k ∣ 13860 := by decide
  unfold g
  have hstep : ∀ k ∈ kset, acoef k * ((M/k:ℕ):ℤ)
      = acoef k * (((M%13860)/k:ℕ):ℤ) + (M/13860 : ℕ) * (acoef k * ((13860/k:ℕ):ℤ)) := by
    intro k hk
    rw [div_split M k (hkd k hk) (hk0 k hk)]
    push_cast; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum, hDk0, mul_zero, add_zero]

theorem hg : ∀ M : ℕ, (∑ k ∈ kset, acoef k * ((M / k : ℕ) : ℤ)) ≤ (Q : ℤ) := by
  intro M
  show g M ≤ (Q:ℤ)
  rw [g_period M, g_flat (M % 13860)]
  have hr : M % 13860 < 13860 := Nat.mod_lt M (by norm_num)
  have hok : okb (M % 13860) = true :=
    scan_spec 13860 0 scan_all (M % 13860) (by omega) (by omega)
  rw [okb_iff] at hok
  show (posS (M%13860) : ℤ) - (negS (M%13860) : ℤ) ≤ (Q:ℤ)
  simp only [Q]
  omega

end Cmb

end ComboContent

section PartAContent
open Finset
namespace PartA
set_option maxRecDepth 10000

/-- Binary modular exponentiation with structural `fuel` recursion (kernel-cheap). -/
def mpow : Nat → Nat → Nat → Nat → Nat
  | 0, _, n, _ => 1 % n
  | (fuel+1), b, n, e =>
    match e with
    | 0 => 1 % n
    | (e+1) =>
      let h := mpow fuel b n ((e+1)/2)
      let h2 := Nat.mod (Nat.mul h h) n
      if (e+1) % 2 = 1 then Nat.mod (Nat.mul h2 b) n else h2

theorem mpow_correct (fuel : ℕ) : ∀ b n e, e < 2^fuel → mpow fuel b n e = b^e % n := by
  induction fuel with
  | zero =>
    intro b n e he
    simp only [pow_zero] at he
    have he0 : e = 0 := by omega
    subst he0; simp [mpow]
  | succ fuel ih =>
    intro b n e he
    match e with
    | 0 => simp [mpow]
    | (e+1) =>
      have hhalf : (e+1)/2 < 2^fuel := by
        have h2 : (e+1) < 2*2^fuel := by rw [pow_succ] at he; omega
        omega
      have hrw : mpow (fuel+1) b n (e+1)
          = (let h := b^((e+1)/2) % n; let h2 := Nat.mod (Nat.mul h h) n;
             if (e+1) % 2 = 1 then Nat.mod (Nat.mul h2 b) n else h2) := by
        rw [mpow, ih b n ((e+1)/2) hhalf]
      rw [hrw]
      simp only
      set p := (e+1)/2 with hp
      rcases Nat.even_or_odd (e+1) with hev | hodd
      · have h0 : (e+1)%2 = 0 := Nat.even_iff.1 hev
        rw [if_neg (by omega)]
        show (b^p % n)*(b^p % n) ≡ b^(e+1) [MOD n]
        calc (b^p % n)*(b^p % n)
            ≡ b^p*b^p [MOD n] := (Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)
          _ = b^(e+1) := by rw [← pow_add]; congr 1; omega
      · have h1 : (e+1)%2 = 1 := Nat.odd_iff.1 hodd
        rw [if_pos h1]
        show ((b^p % n)*(b^p % n) % n) * b ≡ b^(e+1) [MOD n]
        calc ((b^p % n)*(b^p % n) % n) * b
            ≡ (b^p*b^p)*b [MOD n] :=
              Nat.ModEq.mul_right b
                ((Nat.mod_modEq _ _).trans ((Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)))
          _ = b^(e+1) := by rw [← pow_add, ← pow_succ]; congr 1; omega

/-- Per-class check given `pw = 2^k0 mod N`. `c` is the canonical residue of
    `2^k0 - 270024 - k0` mod N. -/
def passesP (pw k0 : ℕ) : Bool :=
  let c := (pw + 833782 - (270024 + k0)) % 833782
  (!(Nat.beq (Nat.mod c 34) 0)) || (Nat.ble 2282 (Nat.mod (Nat.mul 11366 (Nat.div c 34)) 24523))

/-- Iterative scan carrying the running power `pw = 2^k0 mod N` (one multiply per class). -/
def scan : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | (fuel+1), pw, k0 => passesP pw k0 && scan fuel ((pw * 2) % 833782) (k0 + 1)

theorem scan_spec : ∀ fuel pw k0, pw < 833782 → scan fuel pw k0 = true →
    ∀ i, i < fuel → passesP ((pw * 2^i) % 833782) (k0 + i) = true := by
  intro fuel
  induction fuel with
  | zero => intro pw k0 _ h i hi; omega
  | succ fuel ih =>
    intro pw k0 hpw h i hi
    simp only [scan] at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    match i with
    | 0 => rw [pow_zero, mul_one, Nat.mod_eq_of_lt hpw, Nat.add_zero]; exact h1
    | (i+1) =>
      have hkey := ih ((pw * 2) % 833782) (k0 + 1) (Nat.mod_lt _ (by norm_num)) h2 i (by omega)
      have hmod : ((pw * 2 % 833782) * 2^i) % 833782 = (pw * 2^(i+1)) % 833782 := by
        have hm : ((pw * 2) % 833782) * 2^i ≡ (pw * 2) * 2^i [MOD 833782] :=
          (Nat.mod_modEq (pw * 2) 833782).mul_right (2^i)
        calc ((pw * 2 % 833782) * 2^i) % 833782
            = ((pw * 2) * 2^i) % 833782 := hm
          _ = (pw * 2^(i+1)) % 833782 := by rw [pow_succ]; ring_nf
      rw [show k0 + (i+1) = (k0+1) + i by ring, ← hmod]; exact hkey

end PartA

end PartAContent

section CoreAContent
open PartA
namespace PartADev
set_option maxRecDepth 10000

theorem scan_all : scan 12104 2 1 = true := by decide +kernel

-- cancellation of a common factor 34
theorem cancel34 (x y m : ℕ) (h : 34*x ≡ 34*y [MOD 34*m]) : x ≡ y [MOD m] := by
  have h2 : 34*(x%m) = 34*(y%m) := by
    rw [← Nat.mul_mod_mul_left, ← Nat.mul_mod_mul_left]; exact h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

-- 416891 ∣ 2^12104 - 1
theorem dvd_pow_sub_one : (416891 : ℕ) ∣ 2^12104 - 1 := by
  have hmp : mpow 14 2 416891 12104 = 1 := by decide +kernel
  have h2 : 2^12104 % 416891 = 1 := by
    have hc := mpow_correct 14 2 416891 12104 (by norm_num)
    rw [hmp] at hc; exact hc.symm
  have hge : (1:ℕ) ≤ 2^12104 := Nat.one_le_pow _ _ (by norm_num)
  have hmod : 2^12104 ≡ 1 [MOD 416891] := by
    show 2^12104 % 416891 = 1 % 416891
    rw [h2, Nat.mod_eq_of_lt (by norm_num : (1:ℕ) < 416891)]
  exact (Nat.modEq_iff_dvd' hge).1 hmod.symm

-- N ∣ 2^a * (2^12104 - 1) for a ≥ 1
theorem N_dvd (a : ℕ) (ha : 1 ≤ a) : (833782 : ℕ) ∣ 2^a * (2^12104 - 1) := by
  have h2 : (2:ℕ) ∣ 2^a := dvd_pow_self 2 (by omega)
  have hco : Nat.Coprime 2 416891 := by decide
  have : (833782 : ℕ) = 2 * 416891 := by norm_num
  rw [this]
  exact hco.mul_dvd_of_dvd_of_dvd (Dvd.dvd.mul_right h2 _)
    (Dvd.dvd.mul_left dvd_pow_sub_one _)

-- quasiperiod
theorem qp (a : ℕ) (ha : 1 ≤ a) : 2^(a+12104) ≡ 2^a [MOD 833782] := by
  have hle : 2^a ≤ 2^(a+12104) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have he : 2^(a+12104) - 2^a = 2^a * (2^12104 - 1) := by
    rw [pow_add, Nat.mul_sub, mul_one]
  exact ((Nat.modEq_iff_dvd' hle).2 (by rw [he]; exact N_dvd a ha)).symm

theorem qpj (a : ℕ) (ha : 1 ≤ a) (j : ℕ) : 2^(a + j*12104) ≡ 2^a [MOD 833782] := by
  induction j with
  | zero => simpa using Nat.ModEq.refl (2^a)
  | succ j ih =>
    have he : a + (j+1)*12104 = (a + j*12104) + 12104 := by ring
    rw [he]
    exact (qp (a+j*12104) (by omega)).trans ih

-- forward solving lemma
theorem FWD (j c : ℕ) (h : j * 12104 ≡ c [MOD 833782]) :
    34 ∣ c ∧ j % 24523 = (11366 * (c/34)) % 24523 := by
  -- 34 ∣ c
  have h34 : 34 ∣ c := by
    have hm : j*12104 ≡ c [MOD 34] := h.of_dvd (by norm_num)
    have h0 : j*12104 ≡ 0 [MOD 34] := by
      have : j*12104 = 34*(j*356) := by ring
      rw [this]; exact (Nat.modEq_zero_iff_dvd).2 ⟨j*356, rfl⟩
    have : c ≡ 0 [MOD 34] := hm.symm.trans h0
    exact (Nat.modEq_zero_iff_dvd).1 this
  refine ⟨h34, ?_⟩
  set cp := c/34 with hcp
  have hccp : (34:ℕ) * cp = c := Nat.mul_div_cancel' h34
  -- cancel 34
  have e1 : j*356 ≡ cp [MOD 24523] := by
    apply cancel34
    have h1 : 34*(j*356) = j*12104 := by ring
    have h3 : (34:ℕ)*24523 = 833782 := by norm_num
    rw [h1, hccp, h3]; exact h
  have e3 : 356*11366 ≡ 1 [MOD 24523] := by decide
  have e4 : j*(356*11366) ≡ j [MOD 24523] := by
    calc j*(356*11366) ≡ j*1 [MOD 24523] := Nat.ModEq.mul_left j e3
      _ = j := mul_one j
  have e2 : j*356*11366 ≡ cp*11366 [MOD 24523] := e1.mul_right 11366
  have e5 : j ≡ cp*11366 [MOD 24523] := by
    have hassoc : j*356*11366 = j*(356*11366) := by ring
    rw [hassoc] at e2
    exact e4.symm.trans e2
  have : j % 24523 = (cp*11366) % 24523 := e5
  rw [this, Nat.mul_comm cp 11366]

end PartADev

namespace PartADev2
open PartADev
set_option maxRecDepth 10000

theorem core (k : ℕ) (hk : 1 ≤ k) (hf : (2^k - k) % 833782 = 270024) : 27621329 ≤ k := by
  set k0 := (k-1) % 12104 + 1 with hk0def
  set j := (k-1) / 12104 with hjdef
  have hk0_lb : 1 ≤ k0 := by omega
  have hk0_ub : k0 ≤ 12104 := by
    have := Nat.mod_lt (k-1) (show 0 < 12104 by norm_num); omega
  have hkeq : k = k0 + j * 12104 := by
    have hmd := Nat.mod_add_div (k-1) 12104
    omega
  have hkle : k ≤ 2^k := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hc1 : 2^k - k ≡ 270024 [MOD 833782] := by
    show (2^k - k) % 833782 = 270024 % 833782
    rw [hf]
  have hc2 : 2^k ≡ 270024 + k [MOD 833782] := by
    have := hc1.add_right k
    rwa [Nat.sub_add_cancel hkle] at this
  have hc3 : 2^k ≡ 2^k0 [MOD 833782] := by
    conv_lhs => rw [hkeq]
    exact qpj k0 hk0_lb j
  have hc4 : 2^k0 ≡ 270024 + k [MOD 833782] := hc3.symm.trans hc2
  set P0 := 2^k0 % 833782 with hP0def
  have hP0eq : P0 = 2^k0 % 833782 := hP0def
  set c := (P0 + 833782 - (270024 + k0)) % 833782 with hcdef
  have hPlt : P0 < 833782 := by rw [hP0eq]; exact Nat.mod_lt _ (by norm_num)
  have hcadd : c + (270024 + k0) ≡ 2^k0 [MOD 833782] := by
    have hsub : P0 + 833782 - (270024+k0) + (270024+k0) = P0 + 833782 := by omega
    calc c + (270024+k0)
        ≡ (P0 + 833782 - (270024+k0)) + (270024+k0) [MOD 833782] :=
          Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
      _ = P0 + 833782 := hsub
      _ ≡ P0 + 0 [MOD 833782] := Nat.ModEq.add_left P0 (by decide)
      _ = P0 := by rw [Nat.add_zero]
      _ ≡ 2^k0 [MOD 833782] := by rw [hP0eq]; exact Nat.mod_modEq _ _
  have hcomb : c + (270024+k0) ≡ (270024 + k0) + j*12104 [MOD 833782] := by
    have h1 : c + (270024+k0) ≡ 270024 + k [MOD 833782] := hcadd.trans hc4
    have h2 : 270024 + k = (270024+k0) + j*12104 := by omega
    rwa [h2] at h1
  have hcong : c ≡ j*12104 [MOD 833782] := by
    have h := hcomb
    rw [Nat.add_comm c (270024+k0)] at h
    exact Nat.ModEq.add_left_cancel' (270024+k0) h
  obtain ⟨h34, hjeq⟩ := FWD j c hcong.symm
  have hpass : passesP P0 k0 = true := by
    have hs := scan_spec 12104 2 1 (by norm_num) scan_all (k0 - 1) (by omega)
    have e1 : 1 + (k0 - 1) = k0 := by omega
    have e2 : 2 * 2 ^ (k0 - 1) = 2 ^ k0 := by rw [← pow_succ', Nat.sub_add_cancel hk0_lb]
    rw [e1, e2] at hs
    rw [hP0def]; exact hs
  rw [passesP, ← hcdef] at hpass
  have hc34 : c % 34 = 0 := by obtain ⟨t, ht⟩ := h34; omega
  have hc34' : Nat.mod c 34 = 0 := hc34
  rw [hc34'] at hpass
  simp only [show ((0:Nat).beq 0) = true from rfl, Bool.not_true, Bool.false_or,
    Nat.ble_eq] at hpass
  have hpass : 2282 ≤ (11366 * (c / 34)) % 24523 := hpass
  by_contra hcon
  push_neg at hcon
  have hjlt : j < 2282 := by omega
  have hjmod : j % 24523 = j := Nat.mod_eq_of_lt (by omega)
  rw [hjmod] at hjeq
  omega

end PartADev2

namespace PartADev3
open PartADev
set_option maxRecDepth 10000

-- backward solving: the explicit j works
theorem BWD (c : ℕ) (h34 : 34 ∣ c) :
    ((11366*(c/34))%24523) * 12104 ≡ c [MOD 833782] := by
  set j := (11366*(c/34))%24523 with hjdef
  set cp := c/34 with hcpdef
  have hccp : 34 * cp = c := Nat.mul_div_cancel' h34
  have hj1 : j ≡ 11366*cp [MOD 24523] := by rw [hjdef]; exact Nat.mod_modEq _ _
  have e3 : 356*11366 ≡ 1 [MOD 24523] := by decide
  have hj2 : j*356 ≡ cp [MOD 24523] := by
    calc j*356 ≡ (11366*cp)*356 [MOD 24523] := hj1.mul_right 356
      _ = cp*(356*11366) := by ring
      _ ≡ cp*1 [MOD 24523] := Nat.ModEq.mul_left cp e3
      _ = cp := mul_one cp
  have hlift : 34*(j*356) ≡ 34*cp [MOD 34*24523] := Nat.ModEq.mul_left' 34 hj2
  have e1 : 34*(j*356) = j*12104 := by ring
  have e2 : (34:ℕ)*24523 = 833782 := by norm_num
  rw [e1, hccp, e2] at hlift
  exact hlift

def vv (k0 : ℕ) : ℕ := (mpow 20 2 34 k0 + 170 - k0) % 34

theorem vv_eq (k0 : ℕ) (h : k0 ≤ 136) : (2^k0 - k0) % 34 = vv k0 := by
  rw [vv, mpow_correct 20 2 34 k0 (lt_of_le_of_lt h (by norm_num))]
  have hk : k0 ≤ 2^k0 := Nat.le_of_lt Nat.lt_two_pow_self
  have h1 : (2^k0 - k0) + k0 = 2^k0 := Nat.sub_add_cancel hk
  have h2 : (2^k0 % 34 + 170 - k0) + k0 = 2^k0 % 34 + 170 := by omega
  have h3 : 2^k0 ≡ 2^k0 % 34 + 170 [MOD 34] := by
    calc 2^k0 ≡ 2^k0 % 34 [MOD 34] := (Nat.mod_modEq _ _).symm
      _ = 2^k0 % 34 + 0 := (Nat.add_zero _).symm
      _ ≡ 2^k0 % 34 + 170 [MOD 34] := Nat.ModEq.add_left _ (by decide)
  have hg : (2^k0-k0)+k0 ≡ (2^k0%34+170-k0)+k0 [MOD 34] := by rw [h1, h2]; exact h3
  exact Nat.ModEq.add_right_cancel' k0 hg

theorem surj34 : ∀ s, s < 34 → ∃ k0 < 137, 1 ≤ k0 ∧ vv k0 = s := by decide +kernel

theorem hit (r : ℕ) (hr : r < 833782) :
    ∃ k, 1 ≤ k ∧ k ≤ 296814424 ∧ (2^k - k) % 833782 = r := by
  obtain ⟨k0, hk0lt, hk0_1, hvv⟩ := surj34 (r%34) (Nat.mod_lt r (by norm_num))
  have hk0le : k0 ≤ 136 := by omega
  have hmod34 : (2^k0 - k0) % 34 = r % 34 := by rw [vv_eq k0 hk0le, hvv]
  set A0 := (2^k0 - k0) % 833782 with hA0def
  have hAlt : A0 < 833782 := Nat.mod_lt _ (by norm_num)
  set c := (A0 + 833782 - r) % 833782 with hcdef
  -- c + r ≡ A0 [MOD N]
  have hcrA0 : c + r ≡ A0 [MOD 833782] := by
    have hsub : A0 + 833782 - r + r = A0 + 833782 := by omega
    calc c + r ≡ (A0 + 833782 - r) + r [MOD 833782] :=
            Nat.ModEq.add_right r (Nat.mod_modEq _ _)
      _ = A0 + 833782 := hsub
      _ ≡ A0 + 0 [MOD 833782] := Nat.ModEq.add_left A0 (by decide)
      _ = A0 := Nat.add_zero A0
  -- A0 ≡ r [MOD 34]
  have hA0r34 : A0 ≡ r [MOD 34] := by
    have hA0e : A0 ≡ 2^k0 - k0 [MOD 34] := (Nat.mod_modEq _ _).of_dvd (by norm_num)
    have hre : (2^k0 - k0) ≡ r [MOD 34] := hmod34
    exact hA0e.trans hre
  -- 34 ∣ c
  have h34c : 34 ∣ c := by
    have hcr34 : c + r ≡ A0 [MOD 34] := hcrA0.of_dvd (by norm_num)
    have : c + r ≡ r [MOD 34] := hcr34.trans hA0r34
    have hc0 : c ≡ 0 [MOD 34] :=
      Nat.ModEq.add_right_cancel' r (by rw [Nat.zero_add]; exact this)
    exact (Nat.modEq_zero_iff_dvd).1 hc0
  set j := (11366*(c/34))%24523 with hjdef
  have hjlt : j < 24523 := Nat.mod_lt _ (by norm_num)
  have hjd : j*12104 ≡ c [MOD 833782] := BWD c h34c
  clear_value j
  clear hjdef
  have hjb : j * 12104 ≤ 296814288 := by
    have hj : j ≤ 24522 := by omega
    calc j * 12104 ≤ 24522 * 12104 := by gcongr
      _ = 296814288 := by norm_num
  refine ⟨k0 + j*12104, by omega, by omega, ?_⟩
  set K := k0 + j*12104 with hKdef
  have hKle : K ≤ 2^K := Nat.le_of_lt Nat.lt_two_pow_self
  have h2K : 2^K ≡ 2^k0 [MOD 833782] := by rw [hKdef]; exact qpj k0 hk0_1 j
  have hA0k0 : A0 + k0 ≡ 2^k0 [MOD 833782] := by
    have he : (2^k0 - k0) + k0 = 2^k0 := Nat.sub_add_cancel (Nat.le_of_lt Nat.lt_two_pow_self)
    calc A0 + k0 ≡ (2^k0 - k0) + k0 [MOD 833782] := Nat.ModEq.add_right k0 (Nat.mod_modEq _ _)
      _ = 2^k0 := he
  have h2k0 : 2^k0 ≡ r + k0 + j*12104 [MOD 833782] := by
    calc 2^k0 ≡ A0 + k0 [MOD 833782] := hA0k0.symm
      _ ≡ (c + r) + k0 [MOD 833782] := Nat.ModEq.add_right k0 hcrA0.symm
      _ ≡ (j*12104 + r) + k0 [MOD 833782] :=
            Nat.ModEq.add_right k0 (Nat.ModEq.add_right r hjd.symm)
      _ = r + k0 + j*12104 := by ring
  have h2Kfin : 2^K ≡ r + K [MOD 833782] := by
    calc 2^K ≡ 2^k0 [MOD 833782] := h2K
      _ ≡ r + k0 + j*12104 [MOD 833782] := h2k0
      _ = r + K := by rw [hKdef]; ring
  have hfin : (2^K - K) % 833782 = r % 833782 := by
    have e : (2^K - K) + K = 2^K := Nat.sub_add_cancel hKle
    have h : (2^K - K) + K ≡ r + K [MOD 833782] := by rw [e]; exact h2Kfin
    exact Nat.ModEq.add_right_cancel' K h
  rw [hfin, Nat.mod_eq_of_lt hr]

end PartADev3

end CoreAContent

section ChebLBContent

open Finset Nat Real
open scoped Nat.Prime
open ArithmeticFunction hiding log
open scoped ArithmeticFunction

namespace ChebLB

noncomputable section

/-- The Stirling-type upper bound: `log N! ≤ N log N - N + (log N)/2 + 1` for `N ≥ 1`. -/
theorem log_factorial_le_stirling {n : ℕ} (hn : n ≠ 0) :
    Real.log (n !) ≤ n * Real.log n - n + Real.log n / 2 + 1 := by
  -- stirlingSeq n ≤ stirlingSeq 1 = e/√2, so log (stirlingSeq n) ≤ 1 - (log 2)/2.
  have hpos : 0 < Stirling.stirlingSeq n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact Stirling.stirlingSeq'_pos m
  have hanti : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
    simpa [Function.comp] using this
  have h1 : Stirling.stirlingSeq 1 = Real.exp 1 / Real.sqrt 2 := Stirling.stirlingSeq_one
  -- log (stirlingSeq n) = log n! - (1/2) log (2 n) - n * log (n / e)
  have hform := Stirling.log_stirlingSeq_formula n
  -- bound: log (stirlingSeq n) ≤ log (stirlingSeq 1) = 1 - (log 2)/2
  have hlog1 : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [h1, Real.log_div (by positivity) (by positivity), Real.log_exp,
        Real.log_sqrt (by norm_num)]
  have hle : Real.log (Stirling.stirlingSeq n) ≤ 1 - Real.log 2 / 2 := by
    rw [← hlog1]
    exact Real.log_le_log hpos hanti
  rw [hform] at hle
  -- expand: log (2 n) = log 2 + log n, log (n / e) = log n - 1
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e1 : Real.log (2 * (n:ℝ)) = Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hnpos)]
  have e2 : Real.log ((n:ℝ) / Real.exp 1) = Real.log n - 1 := by
    rw [Real.log_div (ne_of_gt hnpos) (by positivity), Real.log_exp]
  rw [e1, e2] at hle
  nlinarith [hle]

/-- `ω u = u log u - u` has derivative `log u` for `u > 0`. -/
theorem hasDerivAt_omega {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun x => x * Real.log x - x) (Real.log u) u := by
  have h1 : HasDerivAt (fun x => x * Real.log x) (Real.log u + 1) u :=
    Real.hasDerivAt_mul_log hu
  have h2 : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
  have := h1.sub h2
  simpa using this

/-- Lower bound of `ω` at the floor: `ω ⌊y⌋ ≥ ω y - log y` for `y ≥ 1`. -/
theorem omega_floor_lower {y : ℝ} (hy : 1 ≤ y) :
    (⌊y⌋₊ : ℝ) * Real.log ⌊y⌋₊ - ⌊y⌋₊ ≥ y * Real.log y - y - Real.log y := by
  set N := (⌊y⌋₊ : ℕ) with hN
  have hNle : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff y |>.mpr hy
  have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  rcases eq_or_lt_of_le hNle with heq | hlt
  · -- y = N : equality up to - log y, and log y ≥ 0
    rw [heq]; have : 0 ≤ Real.log y := Real.log_nonneg hy; linarith
  · -- N < y : MVT on [N, y]
    have hcont : ContinuousOn (fun x => x * Real.log x - x) (Set.Icc (N:ℝ) y) := by
      apply ContinuousOn.sub
      · exact (continuousOn_id.mul (Real.continuousOn_log.mono (by
          intro x hx; simp only [Set.mem_Icc] at hx; simp only [Set.mem_compl_iff,
            Set.mem_singleton_iff]; linarith [hx.1, hN1'])))
      · exact continuousOn_id
    have hderiv : ∀ x ∈ Set.Ioo (N:ℝ) y, HasDerivAt (fun x => x * Real.log x - x) (Real.log x) x := by
      intro x hx; simp only [Set.mem_Ioo] at hx
      exact hasDerivAt_omega (by linarith [hx.1, hN1'])
    obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hderiv
    simp only [Set.mem_Ioo] at hc
    have hyN : (0:ℝ) < y - N := by linarith
    have hlogc : Real.log c ≤ Real.log y := Real.log_le_log (by linarith [hN1', hc.1]) (le_of_lt hc.2)
    have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith [hN1', hc.1])
    have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy
    -- f y - f N = log c * (y - N)
    have hfdiff : (y * Real.log y - y) - ((N:ℝ) * Real.log N - N) = Real.log c * (y - N) := by
      field_simp at hcslope ⊢
      linarith [hcslope]
    have hyN1 : y - (N:ℝ) ≤ 1 := by
      have := Nat.lt_floor_add_one y; rw [← hN] at this; push_cast at this ⊢; linarith
    -- log c * (y - N) ≤ log y * 1 = log y
    have : Real.log c * (y - N) ≤ Real.log y := by
      calc Real.log c * (y - N) ≤ Real.log y * (y - N) := by
            apply mul_le_mul_of_nonneg_right hlogc (le_of_lt hyN)
        _ ≤ Real.log y * 1 := by apply mul_le_mul_of_nonneg_left hyN1 hlogy0
        _ = Real.log y := mul_one _
    linarith [hfdiff, this]

/-- Upper bound of `ω` at the floor: `ω ⌊y⌋ ≤ ω y` for `y ≥ 1`. -/
theorem omega_floor_upper {y : ℝ} (hy : 1 ≤ y) :
    (⌊y⌋₊ : ℝ) * Real.log ⌊y⌋₊ - ⌊y⌋₊ ≤ y * Real.log y - y := by
  set N := (⌊y⌋₊ : ℕ) with hN
  have hNle : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff y |>.mpr hy
  have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  rcases eq_or_lt_of_le hNle with heq | hlt
  · rw [heq]
  · have hcont : ContinuousOn (fun x => x * Real.log x - x) (Set.Icc (N:ℝ) y) := by
      apply ContinuousOn.sub
      · exact (continuousOn_id.mul (Real.continuousOn_log.mono (by
          intro x hx; simp only [Set.mem_Icc] at hx; simp only [Set.mem_compl_iff,
            Set.mem_singleton_iff]; linarith [hx.1, hN1'])))
      · exact continuousOn_id
    have hderiv : ∀ x ∈ Set.Ioo (N:ℝ) y, HasDerivAt (fun x => x * Real.log x - x) (Real.log x) x := by
      intro x hx; simp only [Set.mem_Ioo] at hx
      exact hasDerivAt_omega (by linarith [hx.1, hN1'])
    obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hderiv
    simp only [Set.mem_Ioo] at hc
    have hyN : (0:ℝ) < y - N := by linarith
    have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith [hN1', hc.1])
    have hfdiff : (y * Real.log y - y) - ((N:ℝ) * Real.log N - N) = Real.log c * (y - N) := by
      field_simp at hcslope ⊢
      linarith [hcslope]
    nlinarith [hfdiff, mul_nonneg hlogc0 (le_of_lt hyN)]

/-- Per-term lower bound (used for positive coefficients):
`log ⌊y⌋! ≥ y log y - y - log y + (log 2π)/2` for `y ≥ 1`. -/
theorem term_lower {y : ℝ} (hy : 1 ≤ y) :
    Real.log ((⌊y⌋₊)!) ≥ y * Real.log y - y - Real.log y + Real.log (2 * Real.pi) / 2 := by
  have hN1 : 1 ≤ ⌊y⌋₊ := Nat.one_le_floor_iff y |>.mpr hy
  have hNne : (⌊y⌋₊ : ℕ) ≠ 0 := by omega
  have hstir := Stirling.le_log_factorial_stirling hNne
  have hlogN : (0:ℝ) ≤ Real.log ⌊y⌋₊ := by
    apply Real.log_nonneg; exact_mod_cast hN1
  have homega := omega_floor_lower hy
  -- log ⌊y⌋! ≥ ⌊y⌋ log⌊y⌋ - ⌊y⌋ + log⌊y⌋/2 + log2π/2
  -- and ⌊y⌋log⌊y⌋ - ⌊y⌋ ≥ y log y - y - log y
  linarith [hstir, hlogN, homega]

/-- Per-term upper bound (used for negative coefficients):
`log ⌊y⌋! ≤ y log y - y + (log y)/2 + 1` for `y ≥ 1`. -/
theorem term_upper {y : ℝ} (hy : 1 ≤ y) :
    Real.log ((⌊y⌋₊)!) ≤ y * Real.log y - y + Real.log y / 2 + 1 := by
  have hN1 : 1 ≤ ⌊y⌋₊ := Nat.one_le_floor_iff y |>.mpr hy
  have hNne : (⌊y⌋₊ : ℕ) ≠ 0 := by omega
  have hstir := log_factorial_le_stirling hNne
  have hNle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hlogNle : Real.log ⌊y⌋₊ ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  have homega := omega_floor_upper hy
  linarith [hstir, hlogNle, homega]

/-- The per-term "remainder" function. -/
def rterm (a : ℕ → ℤ) (Q k : ℕ) (x : ℝ) : ℝ :=
  if 0 < a k then ((a k : ℝ)/Q) * (- Real.log (x/k) + Real.log (2 * Real.pi)/2)
  else ((a k : ℝ)/Q) * (Real.log (x/k)/2 + 1)

/-- Per-term lower bound combining Stirling with the `ω` floor bounds. -/
theorem term_bound (a : ℕ → ℤ) (Q k : ℕ) (hQ : 0 < Q) (hk : 0 < k) (x : ℝ)
    (hxk : (1:ℝ) ≤ x/k) :
    ((a k : ℝ)/Q) * Real.log ((⌊x/k⌋₊)!) ≥
      ((a k : ℝ)/Q) * ((x/k) * (Real.log (x/k) - 1)) + rterm a Q k x := by
  set y := x/k with hy
  set c := (a k : ℝ)/Q with hc
  rcases lt_or_ge 0 (a k) with hpos | hnpos
  · -- a k > 0
    have hcpos : 0 ≤ c := by
      rw [hc]; positivity
    have hlow := term_lower hxk
    rw [rterm, if_pos hpos]
    -- log⌊y⌋! ≥ y(log y -1) - log y + log2π/2
    have : Real.log ((⌊y⌋₊)!) ≥ y * (Real.log y - 1) + (- Real.log y + Real.log (2*Real.pi)/2) := by
      nlinarith [hlow]
    nlinarith [mul_le_mul_of_nonneg_left this hcpos]
  · -- a k ≤ 0
    have hcneg : c ≤ 0 := by
      rw [hc]; apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      exact_mod_cast hnpos
    have hup := term_upper hxk
    rw [rterm, if_neg (by omega)]
    have : Real.log ((⌊y⌋₊)!) ≤ y * (Real.log y - 1) + (Real.log y/2 + 1) := by
      nlinarith [hup]
    nlinarith [mul_le_mul_of_nonpos_left this hcneg]

/-- The leading constant `C` of the combination. -/
def Cval (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) : ℝ :=
  - ∑ k ∈ kset, (a k : ℝ) * Real.log k / (Q * k)

/-- The key identity: `∑ (a_k/Q)·(x/k)(log(x/k)-1) = C·x`. -/
theorem sum_M_eq (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hk0 : ∀ k ∈ kset, 0 < k) (hsum0 : ∑ k ∈ kset, (a k : ℝ)/k = 0)
    (x : ℝ) (hx0 : 0 < x) :
    ∑ k ∈ kset, ((a k : ℝ)/Q) * ((x/k) * (Real.log (x/k) - 1)) = Cval kset a Q * x := by
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  -- rewrite each term
  have hMk : ∀ k ∈ kset, ((a k : ℝ)/Q) * ((x/k) * (Real.log (x/k) - 1))
      = x * ((a k : ℝ)/(Q*k) * (Real.log x - Real.log k - 1)) := by
    intro k hk
    have hkpos := hk0 k hk
    have hkne : (k:ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
    rw [Real.log_div hx0.ne' hkne]
    field_simp
  rw [Finset.sum_congr rfl hMk, ← Finset.mul_sum]
  -- inner sum
  have hS0 : ∑ k ∈ kset, (a k : ℝ)/(Q*k) = 0 := by
    have : ∑ k ∈ kset, (a k : ℝ)/(Q*k) = (1/Q) * ∑ k ∈ kset, (a k : ℝ)/k := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk
      rw [mul_comm (Q:ℝ) (k:ℝ)]; field_simp
    rw [this, hsum0, mul_zero]
  have hinner : ∑ k ∈ kset, (a k : ℝ)/(Q*k) * (Real.log x - Real.log k - 1)
      = Cval kset a Q := by
    have expand : ∀ k ∈ kset, (a k : ℝ)/(Q*k) * (Real.log x - Real.log k - 1)
        = (a k : ℝ)/(Q*k) * Real.log x - (a k : ℝ) * Real.log k/(Q*k) - (a k : ℝ)/(Q*k) := by
      intro k hk; field_simp
    have h1 : ∑ k ∈ kset, (a k : ℝ)/(Q*k) * Real.log x = 0 := by
      rw [← Finset.sum_mul, hS0, zero_mul]
    rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, hS0]
    simp [Cval]
  rw [hinner, mul_comm]

/-- Main combined lower bound:
`∑ (a_k/Q)·log⌊x/k⌋! ≥ C·x + ∑ rterm`. -/
theorem A_lb_bound (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hk0 : ∀ k ∈ kset, 0 < k) (hsum0 : ∑ k ∈ kset, (a k : ℝ)/k = 0)
    (x : ℝ) (hx0 : 0 < x) (hxk : ∀ k ∈ kset, (1:ℝ) ≤ x/k) :
    ∑ k ∈ kset, ((a k : ℝ)/Q) * Real.log ((⌊x/k⌋₊)!)
      ≥ Cval kset a Q * x + ∑ k ∈ kset, rterm a Q k x := by
  have hstep : ∑ k ∈ kset, ((a k : ℝ)/Q) * Real.log ((⌊x/k⌋₊)!)
      ≥ ∑ k ∈ kset, (((a k : ℝ)/Q) * ((x/k) * (Real.log (x/k) - 1)) + rterm a Q k x) := by
    apply Finset.sum_le_sum
    intro k hk
    exact term_bound a Q k hQ (hk0 k hk) x (hxk k hk)
  rw [Finset.sum_add_distrib, sum_M_eq kset a Q hQ hk0 hsum0 x hx0] at hstep
  exact hstep

/-- The coefficient of `-log x` in the remainder sum. -/
def Kval (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) : ℝ :=
  ∑ k ∈ kset, (if 0 < a k then (a k : ℝ)/Q else -(a k : ℝ)/(2*Q))

/-- The constant term in the remainder sum. -/
def Lcval (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) : ℝ :=
  ∑ k ∈ kset, (if 0 < a k then (a k : ℝ)/Q * (Real.log k + Real.log (2*Real.pi)/2)
               else (a k : ℝ)/Q * (1 - Real.log k/2))

/-- `∑ rterm = -K·log x + Lc`. -/
theorem sum_rterm_eq (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hk0 : ∀ k ∈ kset, 0 < k) (x : ℝ) (hx0 : 0 < x) :
    ∑ k ∈ kset, rterm a Q k x = - Kval kset a Q * Real.log x + Lcval kset a Q := by
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hper : ∀ k ∈ kset, rterm a Q k x
      = (if 0 < a k then (a k : ℝ)/Q else -(a k : ℝ)/(2*Q)) * (-Real.log x)
        + (if 0 < a k then (a k : ℝ)/Q * (Real.log k + Real.log (2*Real.pi)/2)
           else (a k : ℝ)/Q * (1 - Real.log k/2)) := by
    intro k hk
    have hkne : (k:ℝ) ≠ 0 := by exact_mod_cast (hk0 k hk).ne'
    rw [rterm]
    rcases lt_or_ge 0 (a k) with hpos | hnpos
    · rw [if_pos hpos, if_pos hpos, if_pos hpos, Real.log_div hx0.ne' hkne]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), Real.log_div hx0.ne' hkne]; ring
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [Kval, Lcval]
  ring

theorem log_factorial_eq (N : ℕ) :
    Real.log (N !) = ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  have hIoc : Finset.Ioc 0 N = Finset.Ico 1 (N + 1) := by
    ext x; simp [Nat.succ_le_iff]
  have hfac : (N ! : ℝ) = ∏ m ∈ Finset.Ioc 0 N, (m : ℝ) := by
    rw [hIoc, ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
  rw [hfac, Real.log_prod]
  swap
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    exact_mod_cast hm.1.ne'
  have h1 : ∀ m ∈ Finset.Ioc 0 N, Real.log (m : ℝ) = ∑ d ∈ m.divisors, vonMangoldt d := by
    intro m hm; rw [vonMangoldt_sum]
  rw [Finset.sum_congr rfl h1]
  -- rewrite each inner sum over the common index set Ioc 0 N
  have h2 : ∀ m ∈ Finset.Ioc 0 N, (∑ d ∈ m.divisors, vonMangoldt d)
      = ∑ d ∈ Finset.Ioc 0 N, (if d ∣ m then vonMangoldt d else 0) := by
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    have hset : m.divisors = (Finset.Ioc 0 N).filter (· ∣ m) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨hdvd, hm0⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hm.1, le_trans (Nat.le_of_dvd hm.1 hdvd) hm.2⟩, hdvd⟩
      · rintro ⟨⟨_, _⟩, hdvd⟩
        exact ⟨hdvd, hm.1.ne'⟩
    rw [hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_Ioc] at hd
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]

theorem floor_div_mul (x : ℝ) (hx : 0 ≤ x) (k d : ℕ) :
    ⌊x / (k * d : ℕ)⌋₊ = ⌊x / d⌋₊ / k := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  rw [← Nat.floor_div_natCast (x / d) k]
  congr 1
  push_cast
  rw [div_div, mul_comm]

theorem psi_ge_A (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hk0 : ∀ k ∈ kset, 0 < k)
    (hg : ∀ M : ℕ, (∑ k ∈ kset, a k * ((M / k : ℕ) : ℤ)) ≤ (Q : ℤ))
    (x : ℝ) (hx : 0 ≤ x) :
    (∑ k ∈ kset, ((a k : ℝ) / Q) * Real.log ((⌊x / k⌋₊)!)) ≤ Chebyshev.psi x := by
  set N := ⌊x⌋₊ with hN
  -- rewrite each term and extend the inner sum range to Ioc 0 N
  have key : ∀ k ∈ kset, ((a k : ℝ) / Q) * Real.log ((⌊x / k⌋₊)!)
      = ∑ d ∈ Finset.Ioc 0 N, ((a k : ℝ) / Q) * (vonMangoldt d * ((⌊x / k⌋₊ / d : ℕ) : ℝ)) := by
    intro k hk
    have hkpos := hk0 k hk
    rw [log_factorial_eq, Finset.mul_sum]
    apply Finset.sum_subset
    · intro d hd
      simp only [Finset.mem_Ioc] at hd ⊢
      refine ⟨hd.1, le_trans hd.2 ?_⟩
      rw [hN]
      exact Nat.floor_le_floor (div_le_self hx (by exact_mod_cast hkpos))
    · intro d hd hd'
      simp only [Finset.mem_Ioc] at hd hd'
      have : ⌊x / k⌋₊ / d = 0 := Nat.div_eq_of_lt (by omega)
      rw [this]; simp
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  -- now ∑ d ∈ Ioc 0 N, ∑ k ∈ kset, (a k/Q)*(Λ d * (⌊x/k⌋₊/d))
  have hpsi : Chebyshev.psi x = ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d := rfl
  rw [hpsi]
  apply Finset.sum_le_sum
  intro d hd
  simp only [Finset.mem_Ioc] at hd
  -- inner: ∑ k, (a k/Q)*(Λ d * (⌊x/k⌋₊/d)) = Λ d * (1/Q) * g(⌊x/d⌋₊)
  have hfloor : ∀ k ∈ kset, (⌊x / k⌋₊ / d : ℕ) = (⌊x / d⌋₊ / k : ℕ) := by
    intro k hk
    have h1 := floor_div_mul x hx k d
    have h2 := floor_div_mul x hx d k
    rw [Nat.mul_comm] at h2
    omega
  rw [Finset.sum_congr rfl (fun k hk => by rw [hfloor k hk])]
  have hinner : (∑ k ∈ kset, ((a k : ℝ) / Q) * (vonMangoldt d * ((⌊x / d⌋₊ / k : ℕ) : ℝ)))
      = vonMangoldt d / Q * ((∑ k ∈ kset, a k * ((⌊x / d⌋₊ / k : ℕ) : ℤ) : ℤ) : ℝ) := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k hk; ring
  rw [hinner]
  have hgle := hg (⌊x / d⌋₊)
  have hLd : (0 : ℝ) ≤ vonMangoldt d := vonMangoldt_nonneg
  calc vonMangoldt d / Q * ((∑ k ∈ kset, a k * ((⌊x / d⌋₊ / k : ℕ) : ℤ) : ℤ) : ℝ)
      ≤ vonMangoldt d / Q * (Q : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hgle
    _ = vonMangoldt d := by field_simp

open Chebyshev in
/-- Bound on `ψ - θ`: `ψ t - θ t ≤ log 4 · √t + 2·(log t)·t^(1/3)` for `t ≥ 2`. -/
theorem psi_sub_theta_le (t : ℝ) (ht : 2 ≤ t) :
    Chebyshev.psi t - Chebyshev.theta t
      ≤ Real.log 4 * t ^ ((1:ℝ)/2) + 2 * Real.log t * t ^ ((1:ℝ)/3) := by
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) ≤ t := by linarith
  rw [psi_eq_theta_add_sum_theta ht]
  set M := ⌊Real.log t / Real.log 2⌋₊ with hM
  -- ψ - θ = ∑_{n ∈ Icc 2 M} θ (t^(1/n))
  have hrw : θ t + ∑ n ∈ Finset.Icc 2 M, θ (t ^ ((1:ℝ)/n)) - θ t
      = ∑ n ∈ Finset.Icc 2 M, θ (t ^ ((1:ℝ)/n)) := by ring
  rw [hrw]
  -- each term ≤ log4 * t^(1/n)
  have hterm : ∀ n ∈ Finset.Icc 2 M, θ (t ^ ((1:ℝ)/n)) ≤ Real.log 4 * t ^ ((1:ℝ)/n) := by
    intro n hn
    exact theta_le_log4_mul_x (by positivity)
  have hsum1 : ∑ n ∈ Finset.Icc 2 M, θ (t ^ ((1:ℝ)/n))
      ≤ ∑ n ∈ Finset.Icc 2 M, Real.log 4 * t ^ ((1:ℝ)/n) :=
    Finset.sum_le_sum hterm
  refine le_trans hsum1 ?_
  -- split off n = 2
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · -- M < 2 : sum is empty or just... Icc 2 M empty
    have : Finset.Icc 2 M = ∅ := by
      rw [Finset.Icc_eq_empty]; omega
    rw [this, Finset.sum_empty]
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlt : (0:ℝ) ≤ Real.log t := Real.log_nonneg ht1
    apply add_nonneg (mul_nonneg h4 (by positivity))
      (mul_nonneg (mul_nonneg (by norm_num) hlt) (by positivity))
  · -- M ≥ 2
    rw [show Finset.Icc 2 M = insert 2 (Finset.Icc 3 M) from ?_]
    · rw [Finset.sum_insert (by simp)]
      have hn2 : Real.log 4 * t ^ ((1:ℝ)/(2:ℕ)) = Real.log 4 * t ^ ((1:ℝ)/2) := by norm_num
      rw [hn2]
      -- remaining sum ≤ (card) • log4 * t^(1/3) ≤ 2 log t * t^(1/3)
      have hrest : ∑ n ∈ Finset.Icc 3 M, Real.log 4 * t ^ ((1:ℝ)/n)
          ≤ 2 * Real.log t * t ^ ((1:ℝ)/3) := by
        have hb : ∀ n ∈ Finset.Icc 3 M, Real.log 4 * t ^ ((1:ℝ)/n)
            ≤ Real.log 4 * t ^ ((1:ℝ)/3) := by
          intro n hn
          simp only [Finset.mem_Icc] at hn
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.rpow_le_rpow_of_exponent_le ht1
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          exact_mod_cast hn.1
        refine le_trans (Finset.sum_le_sum hb) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        -- card (Icc 3 M) ≤ M ≤ log t / log 2
        have hcard : (Finset.Icc 3 M).card ≤ M := by
          rw [Nat.card_Icc]; omega
        have hMle : (M : ℝ) ≤ Real.log t / Real.log 2 := by
          rw [hM]; exact Nat.floor_le (div_nonneg (Real.log_nonneg ht1) (Real.log_nonneg (by norm_num)))
        have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have hcard' : ((Finset.Icc 3 M).card : ℝ) ≤ Real.log t / Real.log 2 :=
          le_trans (by exact_mod_cast hcard) hMle
        have hlog4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
        calc ((Finset.Icc 3 M).card : ℝ) * (Real.log 4 * t ^ ((1:ℝ)/3))
            ≤ (Real.log t / Real.log 2) * (Real.log 4 * t ^ ((1:ℝ)/3)) := by
              apply mul_le_mul_of_nonneg_right hcard' (by positivity)
          _ = 2 * Real.log t * t ^ ((1:ℝ)/3) := by rw [hlog4]; field_simp
      linarith [hrest]
    · ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega

/-- The smooth lower bound function for `θ`. -/
def thetaLB (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (x : ℝ) : ℝ :=
  Cval kset a Q * x - Kval kset a Q * Real.log x + Lcval kset a Q
    - (Real.log 4 * x ^ ((1:ℝ)/2) + 2 * Real.log x * x ^ ((1:ℝ)/3))

/-- Main effective Chebyshev lower bound: `θ x ≥ thetaLB x`. -/
theorem theta_lower (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hk0 : ∀ k ∈ kset, 0 < k) (hsum0 : ∑ k ∈ kset, (a k : ℝ)/k = 0)
    (hg : ∀ M : ℕ, (∑ k ∈ kset, a k * ((M / k : ℕ) : ℤ)) ≤ (Q : ℤ))
    (x : ℝ) (hx2 : 2 ≤ x) (hxk : ∀ k ∈ kset, (1:ℝ) ≤ x/k) :
    Chebyshev.theta x ≥ thetaLB kset a Q x := by
  have hx0 : 0 < x := by linarith
  have h1 : Cval kset a Q * x - Kval kset a Q * Real.log x + Lcval kset a Q
      ≤ Chebyshev.psi x := by
    have hA := A_lb_bound kset a Q hQ hk0 hsum0 x hx0 hxk
    have hpsi := psi_ge_A kset a Q hQ hk0 hg x (le_of_lt hx0)
    have hr := sum_rterm_eq kset a Q hQ hk0 x hx0
    rw [hr] at hA
    linarith [hA, hpsi]
  have h2 := psi_sub_theta_le x hx2
  rw [thetaLB]
  linarith [h1, h2]

/-- Antiderivative for the integral lower bound. -/
theorem hasDerivAt_Hgen (A B E F t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => A*s - B*Real.log s - E*s^((1:ℝ)/2) - F*s^((1:ℝ)/3))
      (A - B/t - E*((1:ℝ)/2)*t^((1:ℝ)/2-1) - F*((1:ℝ)/3)*t^((1:ℝ)/3-1)) t := by
  have h1 : HasDerivAt (fun s : ℝ => A*s) A t := by
    simpa using (hasDerivAt_id t).const_mul A
  have h2 : HasDerivAt (fun s : ℝ => B*Real.log s) (B/t) t := by
    have := (Real.hasDerivAt_log (ne_of_gt ht)).const_mul B
    simpa [mul_one_div] using this
  have h3 : HasDerivAt (fun s : ℝ => E*s^((1:ℝ)/2)) (E*((1:ℝ)/2)*t^((1:ℝ)/2-1)) t := by
    have := (Real.hasDerivAt_rpow_const (p := (1:ℝ)/2) (Or.inl (ne_of_gt ht))).const_mul E
    simpa [mul_assoc] using this
  have h4 : HasDerivAt (fun s : ℝ => F*s^((1:ℝ)/3)) (F*((1:ℝ)/3)*t^((1:ℝ)/3-1)) t := by
    have := (Real.hasDerivAt_rpow_const (p := (1:ℝ)/3) (Or.inl (ne_of_gt ht))).const_mul F
    simpa [mul_assoc] using this
  exact ((h1.sub h2).sub h3).sub h4

open Chebyshev in
/-- Integral lower bound via FTC and monotonicity. -/
theorem integral_theta_lower (t0 X : ℝ) (ht0 : 2 ≤ t0) (htX : t0 ≤ X)
    (g : ℝ → ℝ) (hg_le_theta : ∀ t ∈ Set.Icc t0 X, g t ≤ Chebyshev.theta t)
    (A B E F : ℝ)
    (hbound : ∀ t ∈ Set.Icc t0 X,
      A - B/t - E*((1:ℝ)/2)*t^((1:ℝ)/2-1) - F*((1:ℝ)/3)*t^((1:ℝ)/3-1)
        ≤ g t / (t * Real.log t ^ 2)) :
    (A*X - B*Real.log X - E*X^((1:ℝ)/2) - F*X^((1:ℝ)/3))
      - (A*t0 - B*Real.log t0 - E*t0^((1:ℝ)/2) - F*t0^((1:ℝ)/3))
      ≤ ∫ t in t0..X, Chebyshev.theta t / (t * Real.log t ^ 2) := by
  set Hf : ℝ → ℝ := fun s => A*s - B*Real.log s - E*s^((1:ℝ)/2) - F*s^((1:ℝ)/3) with hHf
  set Hd : ℝ → ℝ := fun t => A - B/t - E*((1:ℝ)/2)*t^((1:ℝ)/2-1) - F*((1:ℝ)/3)*t^((1:ℝ)/3-1) with hHd
  -- H' is continuous on [t0, X]
  have hcontHd : ContinuousOn Hd (Set.Icc t0 X) := by
    apply ContinuousOn.sub; apply ContinuousOn.sub; apply ContinuousOn.sub
    · exact continuousOn_const
    · exact (continuousOn_const.div continuousOn_id (fun x hx => by
        simp only [Set.mem_Icc] at hx; exact ne_of_gt (by linarith [hx.1])))
    · exact (continuousOn_const.mul ((continuousOn_id.rpow_const (fun x hx => by
        simp only [Set.mem_Icc, id_eq] at hx ⊢; left; exact ne_of_gt (by linarith [hx.1])))))
    · exact (continuousOn_const.mul ((continuousOn_id.rpow_const (fun x hx => by
        simp only [Set.mem_Icc, id_eq] at hx ⊢; left; exact ne_of_gt (by linarith [hx.1])))))
  have hintHd : IntervalIntegrable Hd MeasureTheory.volume t0 X :=
    hcontHd.intervalIntegrable_of_Icc htX
  -- FTC: ∫ Hd = Hf X - Hf t0
  have hFTC : ∫ t in t0..X, Hd t = Hf X - Hf t0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le htX] at ht
      simp only [Set.mem_Icc] at ht
      exact hasDerivAt_Hgen A B E F t (by linarith [ht.1])
    · exact hintHd
  -- the integrand θ/(t log²t) is integrable on [t0,X]
  have hintTheta : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t ^ 2))
      MeasureTheory.volume t0 X := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le htX]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq X).mono_set
      (Set.Icc_subset_Icc ht0 le_rfl)
  -- monotonicity: ∫ Hd ≤ ∫ θ/(t log²t)
  have hmono : ∫ t in t0..X, Hd t ≤ ∫ t in t0..X, Chebyshev.theta t / (t * Real.log t ^ 2) := by
    apply intervalIntegral.integral_mono_on htX hintHd hintTheta
    intro t ht
    have hht := hbound t ht
    have hgt := hg_le_theta t ht
    simp only [Set.mem_Icc] at ht
    have htpos : (0:ℝ) < t := by linarith [ht.1]
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hden : 0 < t * Real.log t ^ 2 := by positivity
    calc Hd t ≤ g t / (t * Real.log t ^ 2) := hht
      _ ≤ Chebyshev.theta t / (t * Real.log t ^ 2) := by
          gcongr
  rw [hFTC] at hmono
  simpa [hHf] using hmono

end

end ChebLB

end ChebLBContent



section NumericContent
open Finset Real ChebLB
set_option maxRecDepth 8000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem log3_b : ((5493061/5000000 : ℝ) < Real.log 3) ∧ (Real.log 3 < (10986124/10000000:ℝ)) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/2 : ℝ)) (by rw [abs_of_neg] <;> norm_num) 26
  rw [show (1 - (-1/2) : ℝ) = 3/2 by norm_num, Real.log_div (by norm_num) (by norm_num)] at h
  norm_num [Finset.sum_range_succ, abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have a := Real.log_two_gt_d9; have b := Real.log_two_lt_d9
  norm_num at a b
  constructor <;> linarith [a, b, h1, h2]
theorem log5_b : ((8047189/5000000 : ℝ) < Real.log 5) ∧ (Real.log 5 < (16094380/10000000:ℝ)) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/4 : ℝ)) (by rw [abs_of_neg] <;> norm_num) 14
  rw [show (1 - (-1/4) : ℝ) = 5/4 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (4:ℝ) = 2^2 by norm_num, Real.log_pow] at h
  norm_num [Finset.sum_range_succ, abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have a := Real.log_two_gt_d9; have b := Real.log_two_lt_d9
  norm_num at a b
  constructor <;> linarith [a, b, h1, h2]
theorem log7_b : ((194591/100000 : ℝ) < Real.log 7) ∧ (Real.log 7 < (19459102/10000000:ℝ)) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/7 : ℝ)) (by rw [abs_of_neg] <;> norm_num) 11
  rw [show (1 - (-1/7) : ℝ) = 8/7 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (8:ℝ) = 2^3 by norm_num, Real.log_pow] at h
  norm_num [Finset.sum_range_succ, abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have a := Real.log_two_gt_d9; have b := Real.log_two_lt_d9
  norm_num at a b
  constructor <;> linarith [a, b, h1, h2]
theorem log11_b : ((2997369/1250000 : ℝ) < Real.log 11) ∧ (Real.log 11 < (23978954/10000000:ℝ)) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-3/8 : ℝ)) (by rw [abs_of_neg] <;> norm_num) 23
  rw [show (1 - (-3/8) : ℝ) = 11/8 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (8:ℝ) = 2^3 by norm_num, Real.log_pow] at h
  norm_num [Finset.sum_range_succ, abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have a := Real.log_two_gt_d9; have b := Real.log_two_lt_d9
  norm_num at a b
  constructor <;> linarith [a, b, h1, h2]
theorem lk6 : Real.log (6:ℝ) = Real.log 2 + Real.log 3 := by
  rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk10 : Real.log (10:ℝ) = Real.log 2 + Real.log 5 := by
  rw [show (10:ℝ) = 2*5 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk12 : Real.log (12:ℝ) = 2*Real.log 2 + Real.log 3 := by
  rw [show (12:ℝ) = (2^2)*3 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk14 : Real.log (14:ℝ) = Real.log 2 + Real.log 7 := by
  rw [show (14:ℝ) = 2*7 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk18 : Real.log (18:ℝ) = Real.log 2 + 2*Real.log 3 := by
  rw [show (18:ℝ) = 2*(3^2) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk20 : Real.log (20:ℝ) = 2*Real.log 2 + Real.log 5 := by
  rw [show (20:ℝ) = (2^2)*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk21 : Real.log (21:ℝ) = Real.log 3 + Real.log 7 := by
  rw [show (21:ℝ) = 3*7 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk30 : Real.log (30:ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
  rw [show (30:ℝ) = 2*3*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk33 : Real.log (33:ℝ) = Real.log 3 + Real.log 11 := by
  rw [show (33:ℝ) = 3*11 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk35 : Real.log (35:ℝ) = Real.log 5 + Real.log 7 := by
  rw [show (35:ℝ) = 5*7 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk36 : Real.log (36:ℝ) = 2*Real.log 2 + 2*Real.log 3 := by
  rw [show (36:ℝ) = (2^2)*(3^2) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk42 : Real.log (42:ℝ) = Real.log 2 + Real.log 3 + Real.log 7 := by
  rw [show (42:ℝ) = 2*3*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk44 : Real.log (44:ℝ) = 2*Real.log 2 + Real.log 11 := by
  rw [show (44:ℝ) = (2^2)*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk45 : Real.log (45:ℝ) = 2*Real.log 3 + Real.log 5 := by
  rw [show (45:ℝ) = (3^2)*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk55 : Real.log (55:ℝ) = Real.log 5 + Real.log 11 := by
  rw [show (55:ℝ) = 5*11 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk60 : Real.log (60:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 5 := by
  rw [show (60:ℝ) = (2^2)*3*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk63 : Real.log (63:ℝ) = 2*Real.log 3 + Real.log 7 := by
  rw [show (63:ℝ) = (3^2)*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk66 : Real.log (66:ℝ) = Real.log 2 + Real.log 3 + Real.log 11 := by
  rw [show (66:ℝ) = 2*3*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk70 : Real.log (70:ℝ) = Real.log 2 + Real.log 5 + Real.log 7 := by
  rw [show (70:ℝ) = 2*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk77 : Real.log (77:ℝ) = Real.log 7 + Real.log 11 := by
  rw [show (77:ℝ) = 7*11 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk84 : Real.log (84:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 7 := by
  rw [show (84:ℝ) = (2^2)*3*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk90 : Real.log (90:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 5 := by
  rw [show (90:ℝ) = 2*(3^2)*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk99 : Real.log (99:ℝ) = 2*Real.log 3 + Real.log 11 := by
  rw [show (99:ℝ) = (3^2)*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk105 : Real.log (105:ℝ) = Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (105:ℝ) = 3*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk110 : Real.log (110:ℝ) = Real.log 2 + Real.log 5 + Real.log 11 := by
  rw [show (110:ℝ) = 2*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk126 : Real.log (126:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 7 := by
  rw [show (126:ℝ) = 2*(3^2)*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk132 : Real.log (132:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 11 := by
  rw [show (132:ℝ) = (2^2)*3*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk140 : Real.log (140:ℝ) = 2*Real.log 2 + Real.log 5 + Real.log 7 := by
  rw [show (140:ℝ) = (2^2)*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk154 : Real.log (154:ℝ) = Real.log 2 + Real.log 7 + Real.log 11 := by
  rw [show (154:ℝ) = 2*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk165 : Real.log (165:ℝ) = Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (165:ℝ) = 3*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk180 : Real.log (180:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 5 := by
  rw [show (180:ℝ) = (2^2)*(3^2)*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk198 : Real.log (198:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 11 := by
  rw [show (198:ℝ) = 2*(3^2)*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk210 : Real.log (210:ℝ) = Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (210:ℝ) = 2*3*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk220 : Real.log (220:ℝ) = 2*Real.log 2 + Real.log 5 + Real.log 11 := by
  rw [show (220:ℝ) = (2^2)*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk231 : Real.log (231:ℝ) = Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (231:ℝ) = 3*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk252 : Real.log (252:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 7 := by
  rw [show (252:ℝ) = (2^2)*(3^2)*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk308 : Real.log (308:ℝ) = 2*Real.log 2 + Real.log 7 + Real.log 11 := by
  rw [show (308:ℝ) = (2^2)*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk315 : Real.log (315:ℝ) = 2*Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (315:ℝ) = (3^2)*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk330 : Real.log (330:ℝ) = Real.log 2 + Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (330:ℝ) = 2*3*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk385 : Real.log (385:ℝ) = Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (385:ℝ) = 5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk396 : Real.log (396:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 11 := by
  rw [show (396:ℝ) = (2^2)*(3^2)*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk420 : Real.log (420:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (420:ℝ) = (2^2)*3*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk462 : Real.log (462:ℝ) = Real.log 2 + Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (462:ℝ) = 2*3*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk495 : Real.log (495:ℝ) = 2*Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (495:ℝ) = (3^2)*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk630 : Real.log (630:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (630:ℝ) = 2*(3^2)*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk660 : Real.log (660:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (660:ℝ) = (2^2)*3*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk693 : Real.log (693:ℝ) = 2*Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (693:ℝ) = (3^2)*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk770 : Real.log (770:ℝ) = Real.log 2 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (770:ℝ) = 2*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk924 : Real.log (924:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (924:ℝ) = (2^2)*3*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk990 : Real.log (990:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (990:ℝ) = 2*(3^2)*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk1155 : Real.log (1155:ℝ) = Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (1155:ℝ) = 3*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk1260 : Real.log (1260:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (1260:ℝ) = (2^2)*(3^2)*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk1386 : Real.log (1386:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (1386:ℝ) = 2*(3^2)*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk1540 : Real.log (1540:ℝ) = 2*Real.log 2 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (1540:ℝ) = (2^2)*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk1980 : Real.log (1980:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (1980:ℝ) = (2^2)*(3^2)*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk2310 : Real.log (2310:ℝ) = Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (2310:ℝ) = 2*3*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk2772 : Real.log (2772:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (2772:ℝ) = (2^2)*(3^2)*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk3465 : Real.log (3465:ℝ) = 2*Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (3465:ℝ) = (3^2)*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk4620 : Real.log (4620:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (4620:ℝ) = (2^2)*3*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk6930 : Real.log (6930:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (6930:ℝ) = 2*(3^2)*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk13860 : Real.log (13860:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (13860:ℝ) = (2^2)*(3^2)*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)

theorem Cval_eq : Cval Cmb.kset Cmb.acoef Cmb.Q = (4424186/12006225 : ℝ)*Real.log 2 + (4352207/16008300 : ℝ)*Real.log 3 + (2251801/19209960 : ℝ)*Real.log 5 + (119/2376 : ℝ)*Real.log 7 + (63233/1455300 : ℝ)*Real.log 11 := by
  unfold Cval
  rw [show Cmb.kset = {1, 2, 3, 5, 6, 7, 10, 11, 12, 14, 18, 20, 21, 30, 33, 35, 36, 42, 44, 45, 55, 60, 63, 66, 70, 77, 84, 90, 99, 105, 110, 126, 132, 140, 154, 165, 180, 198, 210, 220, 231, 252, 308, 315, 330, 385, 396, 420, 462, 495, 630, 660, 693, 770, 924, 990, 1155, 1260, 1386, 1540, 1980, 2310, 2772, 3465, 4620, 6930, 13860} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [Cmb.acoef, Cmb.Q]
  push_cast
  simp only [Real.log_one]
  rw [lk6, lk10, lk12, lk14, lk18, lk20, lk21, lk30, lk33, lk35, lk36, lk42, lk44, lk45, lk55, lk60, lk63, lk66, lk70, lk77, lk84, lk90, lk99, lk105, lk110, lk126, lk132, lk140, lk154, lk165, lk180, lk198, lk210, lk220, lk231, lk252, lk308, lk315, lk330, lk385, lk396, lk420, lk462, lk495, lk630, lk660, lk693, lk770, lk924, lk990, lk1155, lk1260, lk1386, lk1540, lk1980, lk2310, lk2772, lk3465, lk4620, lk6930, lk13860]
  ring
theorem Kval_eq : Kval Cmb.kset Cmb.acoef Cmb.Q = (996299/13860 : ℝ) := by
  unfold Kval
  rw [show Cmb.kset = {1, 2, 3, 5, 6, 7, 10, 11, 12, 14, 18, 20, 21, 30, 33, 35, 36, 42, 44, 45, 55, 60, 63, 66, 70, 77, 84, 90, 99, 105, 110, 126, 132, 140, 154, 165, 180, 198, 210, 220, 231, 252, 308, 315, 330, 385, 396, 420, 462, 495, 630, 660, 693, 770, 924, 990, 1155, 1260, 1386, 1540, 1980, 2310, 2772, 3465, 4620, 6930, 13860} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [Cmb.acoef, Cmb.Q]
  norm_num
theorem Lcval_eq : Lcval Cmb.kset Cmb.acoef Cmb.Q = (-99811/2310 : ℝ) + (197563/1980 : ℝ)*Real.log 2 + (628087/6930 : ℝ)*Real.log 3 + (118343/2772 : ℝ)*Real.log 5 + (650533/13860 : ℝ)*Real.log 7 + (579587/13860 : ℝ)*Real.log 11 + (348433/13860 : ℝ)*Real.log Real.pi := by
  unfold Lcval
  rw [show Cmb.kset = {1, 2, 3, 5, 6, 7, 10, 11, 12, 14, 18, 20, 21, 30, 33, 35, 36, 42, 44, 45, 55, 60, 63, 66, 70, 77, 84, 90, 99, 105, 110, 126, 132, 140, 154, 165, 180, 198, 210, 220, 231, 252, 308, 315, 330, 385, 396, 420, 462, 495, 630, 660, 693, 770, 924, 990, 1155, 1260, 1386, 1540, 1980, 2310, 2772, 3465, 4620, 6930, 13860} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [Cmb.acoef, Cmb.Q]
  rw [show Real.log (2*Real.pi) = Real.log 2 + Real.log Real.pi from
      Real.log_mul (by norm_num) Real.pi_pos.ne']
  norm_num
  push_cast
  rw [lk6, lk10, lk12, lk14, lk18, lk20, lk21, lk30, lk33, lk35, lk36, lk42, lk44, lk45, lk55, lk60, lk63, lk66, lk70, lk77, lk84, lk90, lk99, lk105, lk110, lk126, lk132, lk140, lk154, lk165, lk180, lk198, lk210, lk220, lk231, lk252, lk308, lk315, lk330, lk385, lk396, lk420, lk462, lk495, lk630, lk660, lk693, lk770, lk924, lk990, lk1155, lk1260, lk1386, lk1540, lk1980, lk2310, lk2772, lk3465, lk4620, lk6930, lk13860]
  push_cast
  ring

theorem Cval_ge : ((7086731246918663/7503890625000000 : ℝ)) ≤ Cval Cmb.kset Cmb.acoef Cmb.Q := by
  rw [Cval_eq]
  have h2 := Real.log_two_gt_d9
  norm_num at h2
  linarith [h2, log3_b.1, log5_b.1, log7_b.1, log11_b.1]
theorem Lcval_ge : ((57305525242160623/138600000000000 : ℝ)) ≤ Lcval Cmb.kset Cmb.acoef Cmb.Q := by
  rw [Lcval_eq]
  have h2 := Real.log_two_gt_d9
  have hpi : Real.log 3 ≤ Real.log Real.pi := Real.log_le_log (by norm_num) (le_of_lt Real.pi_gt_three)
  norm_num at h2
  linarith [h2, log3_b.1, log5_b.1, log7_b.1, log11_b.1, hpi]

end NumericContent

section PiLowerContent
open Real ChebLB Cmb
namespace PiLower
noncomputable section
set_option maxRecDepth 8000
set_option linter.unusedTactic false

-- rpow helpers
theorem rpow_half_le (x c : ℝ) (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ c^2) : x^((1:ℝ)/2) ≤ c := by
  rw [show ((1:ℝ)/2) = ((2:ℕ):ℝ)⁻¹ by norm_num]
  calc x^(((2:ℕ):ℝ)⁻¹) ≤ (c^2)^(((2:ℕ):ℝ)⁻¹) := Real.rpow_le_rpow hx h (by positivity)
    _ = c := Real.pow_rpow_inv_natCast hc (by norm_num)
theorem rpow_third_le (x c : ℝ) (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ c^3) : x^((1:ℝ)/3) ≤ c := by
  rw [show ((1:ℝ)/3) = ((3:ℕ):ℝ)⁻¹ by norm_num]
  calc x^(((3:ℕ):ℝ)⁻¹) ≤ (c^3)^(((3:ℕ):ℝ)⁻¹) := Real.rpow_le_rpow hx h (by positivity)
    _ = c := Real.pow_rpow_inv_natCast hc (by norm_num)

theorem logU_eq : Real.log 13799808 = 7*Real.log 2 + 4*Real.log 3 + 3*Real.log 11 := by
  rw [show (13799808:ℝ) = 2^7*3^4*11^3 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]; push_cast; ring
theorem logt0_eq : Real.log 13860 = 2*Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (13860:ℝ) = 2^2*3^2*5*7*11 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]; push_cast; ring
theorem logU_le : Real.log 13799808 ≤ (10275103791/625000000 : ℝ) := by
  rw [logU_eq]; have b2 := Real.log_two_lt_d9; norm_num at b2
  linarith [b2, log3_b.2, log11_b.2]
theorem logt0_ge : (47683808803/5000000000 : ℝ) ≤ Real.log 13860 := by
  rw [logt0_eq]; have a2 := Real.log_two_gt_d9; norm_num at a2
  linarith [a2, log3_b.1, log5_b.1, log7_b.1, log11_b.1]

theorem hQpos : 0 < Cmb.Q := by norm_num [Cmb.Q]
theorem kset_le : ∀ k ∈ Cmb.kset, k ≤ 13860 := by decide

theorem hxk_t (t : ℝ) (ht : (13860:ℝ) ≤ t) : ∀ k ∈ Cmb.kset, (1:ℝ) ≤ t/k := by
  intro k hk
  have hkpos := Cmb.hk0 k hk
  have hkle := kset_le k hk
  rw [le_div_iff₀ (by exact_mod_cast hkpos)]
  have : (k:ℝ) ≤ 13860 := by exact_mod_cast hkle
  linarith

-- θ at a point t ≥ 13860 dominates thetaLB
theorem thetaLB_le_theta (t : ℝ) (ht : (13860:ℝ) ≤ t) :
    thetaLB Cmb.kset Cmb.acoef Cmb.Q t ≤ Chebyshev.theta t :=
  theta_lower Cmb.kset Cmb.acoef Cmb.Q hQpos Cmb.hk0 Cmb.hsum0 Cmb.hg t (by linarith) (hxk_t t ht)

-- the linear lower bound g(t) = Cl * t - 13805
noncomputable def gfun (t : ℝ) : ℝ := (7086731246918663/7503890625000000 : ℝ) * t - 13805

-- g t ≤ θ t  on [13860, 13799808]
theorem g_le_theta (t : ℝ) (ht : t ∈ Set.Icc (13860:ℝ) 13799808) : gfun t ≤ Chebyshev.theta t := by
  obtain ⟨ht1, ht2⟩ := ht
  have htpos : (0:ℝ) < t := by linarith
  refine le_trans ?_ (thetaLB_le_theta t ht1)
  rw [thetaLB, gfun]
  have hC := Cval_ge
  have hK := Kval_eq
  have hL := Lcval_ge
  have hlogt_le : Real.log t ≤ (10275103791/625000000 : ℝ) :=
    le_trans (Real.log_le_log htpos ht2) logU_le
  have hlogt_pos : (0:ℝ) < Real.log t := by
    have := Real.log_le_log (by norm_num) ht1; have h0 := logt0_ge; linarith
  -- t^(1/2) ≤ sqrtU_hi, t^(1/3) ≤ cbrtU_hi
  have hsq : t^((1:ℝ)/2) ≤ (371481/100 : ℝ) :=
    le_trans (Real.rpow_le_rpow (le_of_lt htpos) ht2 (by norm_num))
      (rpow_half_le _ _ (by norm_num) (by norm_num) (by norm_num))
  have hcb : t^((1:ℝ)/3) ≤ (23986/100 : ℝ) :=
    le_trans (Real.rpow_le_rpow (le_of_lt htpos) ht2 (by norm_num))
      (rpow_third_le _ _ (by norm_num) (by norm_num) (by norm_num))
  have hsqnn : (0:ℝ) ≤ t^((1:ℝ)/2) := Real.rpow_nonneg (le_of_lt htpos) _
  have hcbnn : (0:ℝ) ≤ t^((1:ℝ)/3) := Real.rpow_nonneg (le_of_lt htpos) _
  have hlog4 : Real.log 4 = 2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_lt_d9; norm_num at hl2
  rw [hK, hlog4]
  nlinarith [hC, hL, hlogt_le, hlogt_pos, hsq, hcb, hsqnn, hcbnn, hl2, htpos,
    mul_le_mul hl2.le hsq (by positivity) (by positivity),
    mul_le_mul hlogt_le hcb (by positivity) (by positivity),
    mul_le_mul_of_nonneg_right hC (le_of_lt htpos)]

-- numeric bound for the integrand (E = F = 0)
theorem hbound : ∀ t ∈ Set.Icc (13860:ℝ) 13799808,
    (1747/500000 : ℝ) - (786/5 : ℝ)/t - 0*((1:ℝ)/2)*t^((1:ℝ)/2-1) - 0*((1:ℝ)/3)*t^((1:ℝ)/3-1)
      ≤ gfun t / (t * Real.log t ^ 2) := by
  intro t ht
  obtain ⟨ht1, ht2⟩ := ht
  have htpos : (0:ℝ) < t := by linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have hlogt_le : Real.log t ≤ (10275103791/625000000 : ℝ) :=
    le_trans (Real.log_le_log htpos ht2) logU_le
  have hlogt_ge : (47683808803/5000000000 : ℝ) ≤ Real.log t :=
    le_trans logt0_ge (Real.log_le_log (by norm_num) ht1)
  have hlogpos : (0:ℝ) < Real.log t := by linarith
  have hden : (0:ℝ) < t * Real.log t^2 := by positivity
  have hA2 : (1747/500000:ℝ) * Real.log t^2 ≤ (7086731246918663/7503890625000000:ℝ) := by
    nlinarith [hlogt_le, hlogpos]
  have hB2 : (13805:ℝ) ≤ (786/5:ℝ) * Real.log t^2 := by
    nlinarith [hlogt_ge, hlogpos]
  simp only [zero_mul, sub_zero]
  rw [gfun, le_div_iff₀ hden]
  have hexp : ((1747/500000:ℝ) - (786/5:ℝ)/t)*(t*Real.log t^2)
      = (1747/500000:ℝ)*t*Real.log t^2 - (786/5:ℝ)*Real.log t^2 := by
    field_simp
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_right hA2 htpos.le, hB2]

theorem intInt_2_t0 : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t^2))
    MeasureTheory.volume 2 13860 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq 13799808).mono_set
    (Set.Icc_subset_Icc (le_refl _) (by norm_num))
theorem intInt_t0_U : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t^2))
    MeasureTheory.volume 13860 13799808 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq 13799808).mono_set
    (Set.Icc_subset_Icc (by norm_num) (le_refl _))

theorem int_t0_U : (23541443577627/500000000 : ℝ)
    ≤ ∫ t in (13860:ℝ)..13799808, Chebyshev.theta t / (t * Real.log t^2) := by
  have key := integral_theta_lower 13860 13799808 (by norm_num) (by norm_num) gfun g_le_theta
    (1747/500000) (786/5) 0 0 hbound
  simp only [zero_mul, sub_zero] at key
  refine le_trans ?_ key
  have hlU : Real.log 13799808 ≤ (10275103791/625000000:ℝ) := logU_le
  have hlt0 : (47683808803/5000000000:ℝ) ≤ Real.log 13860 := logt0_ge
  nlinarith [hlU, hlt0]

theorem int_2_U : (23541443577627/500000000 : ℝ)
    ≤ ∫ t in (2:ℝ)..13799808, Chebyshev.theta t / (t * Real.log t^2) := by
  have hadd : (∫ t in (2:ℝ)..13799808, Chebyshev.theta t / (t * Real.log t^2))
      = (∫ t in (2:ℝ)..13860, Chebyshev.theta t / (t * Real.log t^2))
        + (∫ t in (13860:ℝ)..13799808, Chebyshev.theta t / (t * Real.log t^2)) :=
    (intervalIntegral.integral_add_adjacent_intervals intInt_2_t0 intInt_t0_U).symm
  rw [hadd]
  have hnn : (0:ℝ) ≤ ∫ t in (2:ℝ)..13860, Chebyshev.theta t / (t * Real.log t^2) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have htp : (0:ℝ) < t := by simp only [Set.mem_Icc] at ht; linarith [ht.1]
    exact div_nonneg (Chebyshev.theta_nonneg t) (mul_nonneg htp.le (sq_nonneg _))
  linarith [int_t0_U, hnn]

theorem thetaU_ge : (63154385972025463856381/4851000000000000 : ℝ) ≤ Chebyshev.theta 13799808 := by
  refine le_trans ?_ (thetaLB_le_theta 13799808 (by norm_num))
  rw [thetaLB, Kval_eq]
  have hC := Cval_ge
  have hL := Lcval_ge
  have hlU := logU_le
  have hl4 : Real.log 4 ≤ (6931471808/5000000000:ℝ) := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    have hl2 := Real.log_two_lt_d9; push_cast; linarith [hl2]
  have hsq : (13799808:ℝ)^((1:ℝ)/2) ≤ (371481/100:ℝ) :=
    rpow_half_le _ _ (by norm_num) (by norm_num) (by norm_num)
  have hcb : (13799808:ℝ)^((1:ℝ)/3) ≤ (23986/100:ℝ) :=
    rpow_third_le _ _ (by norm_num) (by norm_num) (by norm_num)
  have hsqnn : (0:ℝ) ≤ (13799808:ℝ)^((1:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
  have hcbnn : (0:ℝ) ≤ (13799808:ℝ)^((1:ℝ)/3) := Real.rpow_nonneg (by norm_num) _
  have hl4nn : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlUpos : (0:ℝ) < Real.log 13799808 := Real.log_pos (by norm_num)
  nlinarith [hC, hL, hlU, hl4, hsq, hcb, hsqnn, hcbnn, hl4nn, hlUpos,
    mul_le_mul hl4 hsq hsqnn (by norm_num : (0:ℝ) ≤ 6931471808/5000000000),
    mul_le_mul hlU hcb hcbnn (by norm_num : (0:ℝ) ≤ 10275103791/625000000),
    mul_le_mul_of_nonneg_right hC (by norm_num : (0:ℝ) ≤ 13799808)]

theorem pi_lower : (833782 : ℕ) ≤ Nat.primeCounting 13799808 := by
  have hpc := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := (13799808:ℝ)) (by norm_num)
  rw [show ⌊(13799808:ℝ)⌋₊ = 13799808 by norm_num] at hpc
  have hlUpos : (0:ℝ) < Real.log 13799808 := Real.log_pos (by norm_num)
  have hth := thetaU_ge
  have hint := int_2_U
  have hdiv : (833782 - 23541443577627/500000000 : ℝ)
      ≤ Chebyshev.theta 13799808 / Real.log 13799808 := by
    rw [le_div_iff₀ hlUpos]
    refine le_trans ?_ hth
    have hlU := logU_le
    nlinarith [mul_le_mul_of_nonneg_left hlU
      (by norm_num : (0:ℝ) ≤ 833782 - 23541443577627/500000000)]
  have hfin : (833782:ℝ) ≤ (Nat.primeCounting 13799808 : ℝ) := by
    rw [hpc]; linarith [hdiv, hint]
  exact_mod_cast hfin

theorem nth_prime_le : Nat.nth Nat.Prime 833781 ≤ 13799808 := by
  by_contra h
  push_neg at h
  have hmono : Nat.primeCounting' 13799809 ≤ 833781 := by
    have := Nat.monotone_primeCounting' (show (13799809:ℕ) ≤ Nat.nth Nat.Prime 833781 by omega)
    rwa [Nat.primeCounting'_nth_eq] at this
  have hpc : (833782:ℕ) ≤ Nat.primeCounting' 13799809 := pi_lower
  omega

end
end PiLower

end PiLowerContent


section ConnSec
open Finset ZMod Nat Set Classical

theorem Sne : A232616_prop 833782 296814424 := by
  unfold A232616_prop
  symm
  rw [Finset.eq_univ_iff_forall]
  intro x
  rw [Finset.mem_image]
  obtain ⟨k, hk1, hkle, hkeq⟩ := PartADev3.hit x.val (ZMod.val_lt x)
  refine ⟨k, Finset.mem_Icc.2 ⟨hk1, hkle⟩, ?_⟩
  have hc : ((2^k - k : ℕ) : ZMod 833782) = ((x.val : ℕ) : ZMod 833782) := by
    rw [ZMod.natCast_eq_natCast_iff', hkeq, Nat.mod_eq_of_lt (ZMod.val_lt x)]
  rw [hc, ZMod.natCast_zmod_val]

theorem Slb (m : ℕ) (hm : A232616_prop 833782 m) : 27621329 ≤ m := by
  unfold A232616_prop at hm
  have hr0 : (270024 : ZMod 833782) ∈
      (Finset.Icc 1 m).image (fun k ↦ ((2^k - k : ℕ) : ZMod 833782)) := by
    rw [← hm]; exact Finset.mem_univ _
  rw [Finset.mem_image] at hr0
  obtain ⟨k, hkmem, hkeq⟩ := hr0
  rw [Finset.mem_Icc] at hkmem
  have hmod : (2^k - k) % 833782 = 270024 := by
    have hcc : ((2^k - k : ℕ) : ZMod 833782) = ((270024 : ℕ) : ZMod 833782) := by
      rw [hkeq]; norm_num
    rw [ZMod.natCast_eq_natCast_iff'] at hcc
    rwa [Nat.mod_eq_of_lt (show 270024 < 833782 by norm_num)] at hcc
  have hk := PartADev2.core k hkmem.1 hmod
  omega

theorem oeis_232616_conjecture_i.disproof :
    ¬ ∀ (n : ℕ), 0 < n → A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1) := by
  intro H
  have hconj := H 833782 (by norm_num)
  have hge : 27621329 ≤ A232616 833782 := by
    have hSeq : A232616 833782 = sInf {m | A232616_prop 833782 m} := by
      rw [A232616, dif_neg (by norm_num)]
    rw [hSeq]
    have hmem : sInf {m | A232616_prop 833782 m} ∈ {m | A232616_prop 833782 m} :=
      Nat.sInf_mem ⟨296814424, Sne⟩
    exact Slb _ hmem
  have hle : 2 * (Nat.nth Nat.Prime (833782 - 1) - 1) ≤ 27599614 := by
    have h := PiLower.nth_prime_le
    have h2 : Nat.nth Nat.Prime (833782 - 1) ≤ 13799808 := by
      rwa [show 833782 - 1 = 833781 from rfl]
    omega
  omega

end ConnSec
