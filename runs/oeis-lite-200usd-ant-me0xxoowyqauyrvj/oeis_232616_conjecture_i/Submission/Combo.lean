import FormalConjectures.Util.ProblemImports
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
@[inline] def okb (r : Nat) : Bool := posS r <= 6930 + negS r

def chk : Nat -> Nat -> Nat -> Bool
  | 0, lo, w => match w with | 0 => true | 1 => okb lo | _ => false
  | (fuel+1), lo, w =>
    match w with
    | 0 => true
    | 1 => okb lo
    | (w+2) => let h := (w+2)/2; chk fuel lo h && chk fuel (lo+h) (w+2-h)

theorem chk_c1 : chk 13 0 1733 = true := by decide +kernel
theorem chk_c2 : chk 13 1733 1733 = true := by decide +kernel
theorem chk_c3 : chk 13 3466 1733 = true := by decide +kernel
theorem chk_c4 : chk 13 5199 1733 = true := by decide +kernel
theorem chk_c5 : chk 13 6932 1733 = true := by decide +kernel
theorem chk_c6 : chk 13 8665 1733 = true := by decide +kernel
theorem chk_c7 : chk 13 10398 1733 = true := by decide +kernel
theorem chk_c8 : chk 13 12131 1729 = true := by decide +kernel

theorem chk_spec : ∀ fuel lo w, chk fuel lo w = true →
    ∀ r, lo ≤ r → r < lo + w → okb r = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo w hchk r hlo hr
    match w with
    | 0 => omega
    | 1 => simp only [chk] at hchk
           have : r = lo := by omega
           rw [this]; exact hchk
    | (w+2) => simp only [chk] at hchk; exact absurd hchk (by decide)
  | succ fuel ih =>
    intro lo w hchk r hlo hr
    match w with
    | 0 => omega
    | 1 => simp only [chk] at hchk
           have : r = lo := by omega
           rw [this]; exact hchk
    | (w+2) =>
        simp only [chk] at hchk
        rw [Bool.and_eq_true] at hchk
        obtain ⟨h1, h2⟩ := hchk
        set hh := (w+2)/2 with hhdef
        by_cases hc : r < lo + hh
        · exact ih lo hh h1 r hlo hc
        · exact ih (lo+hh) (w+2-hh) h2 r (by omega) (by omega)

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
  have hok : okb (M % 13860) = true := by
    set r := M % 13860 with hrdef
    rcases lt_or_ge r 6932 with hA | hA
    · rcases lt_or_ge r 3466 with hB | hB
      · rcases lt_or_ge r 1733 with hC | hC
        · exact chk_spec 13 0 1733 chk_c1 r (by omega) (by omega)
        · exact chk_spec 13 1733 1733 chk_c2 r (by omega) (by omega)
      · rcases lt_or_ge r 5199 with hC | hC
        · exact chk_spec 13 3466 1733 chk_c3 r (by omega) (by omega)
        · exact chk_spec 13 5199 1733 chk_c4 r (by omega) (by omega)
    · rcases lt_or_ge r 10398 with hB | hB
      · rcases lt_or_ge r 8665 with hC | hC
        · exact chk_spec 13 6932 1733 chk_c5 r (by omega) (by omega)
        · exact chk_spec 13 8665 1733 chk_c6 r (by omega) (by omega)
      · rcases lt_or_ge r 12131 with hC | hC
        · exact chk_spec 13 10398 1733 chk_c7 r (by omega) (by omega)
        · exact chk_spec 13 12131 1729 chk_c8 r (by omega) (by omega)
  unfold okb at hok
  rw [decide_eq_true_eq] at hok
  show (posS (M%13860) : ℤ) - (negS (M%13860) : ℤ) ≤ (Q:ℤ)
  simp only [Q]
  omega

end Cmb
