import FormalConjectures.Util.ProblemImports

open Nat

/--
A355898: $a(1) = a(2) = 1$; $a(n) = \gcd(a(n-1), a(n-2)) + \frac{a(n-1) + a(n-2)}{\gcd(a(n-1), a(n-2))}$.
-/
def A355898 : ℕ → ℕ
| 0 => 0 -- Sequence starts properly at A355898(1)
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

/--
Conjecture: For n >= 3775 a(n) can also be expressed in the following three ways:
1) a(n) = 1 + a(n-1) + a(n-2).
2) a(n) = 2*a(n-1) - a(n-3).
3) If A = a(3774), B = a(3772) and F = Fibonacci A000045(n),
   a(n) = (A+1)*F(n-3772) - (B+1)*F(n-3774) - 1.
These three formulas only work for n >= 3775.
-/
def A355898Pair : ℕ → ℕ × ℕ
| 0 => (1, 1)
| k + 1 =>
  let p := A355898Pair k
  let g := Nat.gcd p.2 p.1
  (p.2, g + (p.2 + p.1) / g)

lemma A355898Pair_spec (k : ℕ) :
    A355898Pair k = (A355898 (k + 1), A355898 (k + 2)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [A355898Pair, ih]
      rw [show k + 1 + 2 = k + 3 by omega]
      rw [show k + 1 + 1 = k + 2 by omega]
      rw [show k + 2 + 1 = k + 3 by omega]
      rw [A355898]

abbrev pp : ℕ := 195318521017
abbrev badR : ℕ := 249580073233
abbrev badN : ℕ := 249580077008

structure Quad where
  x : ZMod pp
  y : ZMod pp
  deriving DecidableEq, Repr

namespace Quad

def qone : Quad := ⟨1,0⟩
def qmul (a b : Quad) : Quad := ⟨a.x*b.x + a.y*b.y, a.x*b.y + a.y*b.x + a.y*b.y⟩

instance : One Quad := ⟨qone⟩
instance : Mul Quad := ⟨qmul⟩
@[ext] theorem ext {a b : Quad} (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by cases a; cases b; simp_all
instance : CommMonoid Quad where
  mul := qmul
  one := qone
  mul_assoc := by
    intro a b c; change qmul (qmul a b) c = qmul a (qmul b c); unfold qmul; ext <;> ring_nf
  one_mul := by
    intro a; change qmul qone a = a; unfold qmul qone; ext <;> simp
  mul_one := by
    intro a; change qmul a qone = a; unfold qmul qone; ext <;> simp
  mul_comm := by
    intro a b; change qmul a b = qmul b a; unfold qmul; ext <;> ring_nf
  npow := @npowRec Quad ⟨qone⟩ ⟨qmul⟩
  npow_zero := by intro x; rfl
  npow_succ := by intro n x; rfl
end Quad

def mulP (a b : ℕ × ℕ) : ℕ × ℕ :=
  (((a.1*b.1 + a.2*b.2) % pp), ((a.1*b.2 + a.2*b.1 + a.2*b.2) % pp))

def evalP (a : ℕ × ℕ) : Quad := ⟨a.1, a.2⟩

lemma evalP_mulP (a b : ℕ × ℕ) : evalP (mulP a b) = evalP a * evalP b := by
  change evalP (mulP a b) = Quad.qmul (evalP a) (evalP b)
  unfold evalP mulP Quad.qmul
  ext <;> simp [ZMod.natCast_mod]

def powP (a : ℕ × ℕ) : ℕ → ℕ × ℕ
| 0 => (1,0)
| n+1 => if (n+1) % 2 = 0 then let q := powP a ((n+1)/2); mulP q q else mulP a (powP a n)

lemma evalP_powP (a : ℕ × ℕ) (n : ℕ) : evalP (powP a n) = (evalP a) ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [powP]
      change evalP (1,0) = Quad.qone
      rfl
    | succ k =>
      rw [powP]
      by_cases he : (k + 1) % 2 = 0
      · simp [he]
        rw [evalP_mulP, ih ((k + 1) / 2)]
        · rw [← pow_add]
          congr 1
          omega
        · exact Nat.div_lt_self (by omega : 0 < k + 1) (by omega : 1 < 2)
      · simp [he]
        rw [evalP_mulP, ih k]
        · rw [pow_succ]
          rw [mul_comm]
        · omega

def tau : Quad := evalP (0,1)
def qB (t : ℕ) : Quad := ⟨A355898 (3773 + t) + 1, A355898 (3774 + t) + 1⟩

lemma qB_step
    (H : ∀ (n : ℕ), 3775 ≤ n →
      (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
      ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
      ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1))
    (t : ℕ) : qB (t+1) = tau * qB t := by
  unfold qB
  ext
  · change ((A355898 (3773 + (t + 1)) : ZMod pp) + 1) = (Quad.qmul (evalP (0,1)) { x := (↑(A355898 (3773 + t)) + 1), y := (↑(A355898 (3774 + t)) + 1) }).x
    rw [show 3773 + (t + 1) = 3774 + t by omega]
    unfold evalP Quad.qmul
    norm_num
  · change ((A355898 (3774 + (t + 1)) : ZMod pp) + 1) = (Quad.qmul (evalP (0,1)) { x := (↑(A355898 (3773 + t)) + 1), y := (↑(A355898 (3774 + t)) + 1) }).y
    rw [show 3774 + (t + 1) = 3775 + t by omega]
    have h1 : A355898 (3775 + t) = 1 + A355898 (3774 + t) + A355898 (3773 + t) := by
      have h := (H (3775 + t) (by omega)).1
      rwa [show 3775 + t - 1 = 3774 + t by omega, show 3775 + t - 2 = 3773 + t by omega] at h
    rw [h1]
    unfold evalP Quad.qmul
    norm_num
    ring

lemma qB_eq
    (H : ∀ (n : ℕ), 3775 ≤ n →
      (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
      ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
      ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1))
    (t : ℕ) : qB t = tau ^ t * qB 0 := by
  induction t with
  | zero => rw [pow_zero, one_mul]
  | succ t ih =>
    rw [qB_step H t, ih, pow_succ]
    rw [← mul_assoc, mul_comm tau (tau ^ t), mul_assoc]

lemma qB0_res : qB 0 = evalP (77940394259, 99768150822) := by
  unfold qB evalP
  ext
  · have h : (((A355898Pair 3771).2 + 1 : ℕ) : ZMod pp) = (77940394259 : ZMod pp) := by
      set_option maxRecDepth 20000 in
      decide
    rw [A355898Pair_spec] at h
    rw [Nat.cast_add] at h
    have h' : ((A355898 3773 : ZMod pp) + 1 = (77940394259 : ZMod pp)) := h
    change ((A355898 (3773 + 0) : ZMod pp) + 1 = (77940394259 : ZMod pp))
    simpa only [add_zero] using h'
  · have h : (((A355898Pair 3772).2 + 1 : ℕ) : ZMod pp) = (99768150822 : ZMod pp) := by
      set_option maxRecDepth 20000 in
      decide
    rw [A355898Pair_spec] at h
    rw [Nat.cast_add] at h
    have h' : ((A355898 3774 : ZMod pp) + 1 = (99768150822 : ZMod pp)) := h
    change ((A355898 (3774 + 0) : ZMod pp) + 1 = (99768150822 : ZMod pp))
    simpa only [add_zero] using h'

lemma cert : tau ^ badR * qB 0 = evalP (1,1) := by
  rw [qB0_res]
  have hpow0 : powP (0,1) 0 = (1,0) := by
    rw [powP]
  have hpow1 : powP (0,1) 1 = (0,1) := by
    rw [powP]
    norm_num [pp, mulP, hpow0]
  have hpow2 : powP (0,1) 2 = (1,1) := by
    rw [powP]
    norm_num [pp, mulP, hpow1]
  have hpow3 : powP (0,1) 3 = (1,2) := by
    rw [powP]
    norm_num [pp, mulP, hpow2]
  have hpow4 : powP (0,1) 6 = (5,8) := by
    rw [powP]
    norm_num [pp, mulP, hpow3]
  have hpow5 : powP (0,1) 7 = (8,13) := by
    rw [powP]
    norm_num [pp, mulP, hpow4]
  have hpow6 : powP (0,1) 14 = (233,377) := by
    rw [powP]
    norm_num [pp, mulP, hpow5]
  have hpow7 : powP (0,1) 28 = (196418,317811) := by
    rw [powP]
    norm_num [pp, mulP, hpow6]
  have hpow8 : powP (0,1) 29 = (317811,514229) := by
    rw [powP]
    norm_num [pp, mulP, hpow7]
  have hpow9 : powP (0,1) 58 = (170116775145,5331166828) := by
    rw [powP]
    norm_num [pp, mulP, hpow8]
  have hpow10 : powP (0,1) 116 = (49773924280,192440766623) := by
    rw [powP]
    norm_num [pp, mulP, hpow9]
  have hpow11 : powP (0,1) 232 = (155867475481,194305937469) := by
    rw [powP]
    norm_num [pp, mulP, hpow10]
  have hpow12 : powP (0,1) 464 = (1614955175,27770261298) := by
    rw [powP]
    norm_num [pp, mulP, hpow11]
  have hpow13 : powP (0,1) 928 = (185928209965,96254381253) := by
    rw [powP]
    norm_num [pp, mulP, hpow12]
  have hpow14 : powP (0,1) 929 = (96254381253,86864070201) := by
    rw [powP]
    norm_num [pp, mulP, hpow13]
  have hpow15 : powP (0,1) 1858 = (122874171638,38868090280) := by
    rw [powP]
    norm_num [pp, mulP, hpow14]
  have hpow16 : powP (0,1) 1859 = (38868090280,161742261918) := by
    rw [powP]
    norm_num [pp, mulP, hpow15]
  have hpow17 : powP (0,1) 3718 = (131689398187,109362536927) := by
    rw [powP]
    norm_num [pp, mulP, hpow16]
  have hpow18 : powP (0,1) 3719 = (109362536927,45733414097) := by
    rw [powP]
    norm_num [pp, mulP, hpow17]
  have hpow19 : powP (0,1) 7438 = (183298122861,91402293237) := by
    rw [powP]
    norm_num [pp, mulP, hpow18]
  have hpow20 : powP (0,1) 14876 = (25992400769,124511110930) := by
    rw [powP]
    norm_num [pp, mulP, hpow19]
  have hpow21 : powP (0,1) 29752 = (177745180195,131120349488) := by
    rw [powP]
    norm_num [pp, mulP, hpow20]
  have hpow22 : powP (0,1) 59504 = (194001049843,38091898265) := by
    rw [powP]
    norm_num [pp, mulP, hpow21]
  have hpow23 : powP (0,1) 119008 = (26878138653,127215937123) := by
    rw [powP]
    norm_num [pp, mulP, hpow22]
  have hpow24 : powP (0,1) 119009 = (127215937123,154094075776) := by
    rw [powP]
    norm_num [pp, mulP, hpow23]
  have hpow25 : powP (0,1) 238018 = (63462935697,77229582369) := by
    rw [powP]
    norm_num [pp, mulP, hpow24]
  have hpow26 : powP (0,1) 476036 = (38241365584,133112644149) := by
    rw [powP]
    norm_num [pp, mulP, hpow25]
  have hpow27 : powP (0,1) 952072 = (138114740259,112954738797) := by
    rw [powP]
    norm_num [pp, mulP, hpow26]
  have hpow28 : powP (0,1) 1904144 = (154056996875,158795593120) := by
    rw [powP]
    norm_num [pp, mulP, hpow27]
  have hpow29 : powP (0,1) 3808288 = (71172323106,179877156576) := by
    rw [powP]
    norm_num [pp, mulP, hpow28]
  have hpow30 : powP (0,1) 3808289 = (179877156576,55730958665) := by
    rw [powP]
    norm_num [pp, mulP, hpow29]
  have hpow31 : powP (0,1) 7616578 = (49847100571,158541234730) := by
    rw [powP]
    norm_num [pp, mulP, hpow30]
  have hpow32 : powP (0,1) 7616579 = (158541234730,13069814284) := by
    rw [powP]
    norm_num [pp, mulP, hpow31]
  have hpow33 : powP (0,1) 15233158 = (171187543582,38127008062) := by
    rw [powP]
    norm_num [pp, mulP, hpow32]
  have hpow34 : powP (0,1) 30466316 = (172887131028,146193284997) := by
    rw [powP]
    norm_num [pp, mulP, hpow33]
  have hpow35 : powP (0,1) 30466317 = (146193284997,123761895008) := by
    rw [powP]
    norm_num [pp, mulP, hpow34]
  have hpow36 : powP (0,1) 60932634 = (158224746851,62910314271) := by
    rw [powP]
    norm_num [pp, mulP, hpow35]
  have hpow37 : powP (0,1) 60932635 = (62910314271,25816540105) := by
    rw [powP]
    norm_num [pp, mulP, hpow36]
  have hpow38 : powP (0,1) 121865270 = (62835551386,33068008935) := by
    rw [powP]
    norm_num [pp, mulP, hpow37]
  have hpow39 : powP (0,1) 243730540 = (140733322397,176142473281) := by
    rw [powP]
    norm_num [pp, mulP, hpow38]
  have hpow40 : powP (0,1) 487461080 = (99726976518,183150853626) := by
    rw [powP]
    norm_num [pp, mulP, hpow39]
  have hpow41 : powP (0,1) 974922160 = (36687613946,144811362904) := by
    rw [powP]
    norm_num [pp, mulP, hpow40]
  have hpow42 : powP (0,1) 974922161 = (144811362904,181498976850) := by
    rw [powP]
    norm_num [pp, mulP, hpow41]
  have hpow43 : powP (0,1) 1949844322 = (107789511149,194855280932) := by
    rw [powP]
    norm_num [pp, mulP, hpow42]
  have hpow44 : powP (0,1) 3899688644 = (40500134143,92273131568) := by
    rw [powP]
    norm_num [pp, mulP, hpow43]
  have hpow45 : powP (0,1) 7799377288 = (81220899006,16299744117) := by
    rw [powP]
    norm_num [pp, mulP, hpow44]
  have hpow46 : powP (0,1) 15598754576 = (77434719118,36811031866) := by
    rw [powP]
    norm_num [pp, mulP, hpow45]
  have hpow47 : powP (0,1) 15598754577 = (36811031866,114245750984) := by
    rw [powP]
    norm_num [pp, mulP, hpow46]
  have hpow48 : powP (0,1) 31197509154 = (122815009445,161884538056) := by
    rw [powP]
    norm_num [pp, mulP, hpow47]
  have hpow49 : powP (0,1) 62395018308 = (183264428700,124390278326) := by
    rw [powP]
    norm_num [pp, mulP, hpow48]
  have hpow50 : powP (0,1) 124790036616 = (16143421115,161398467405) := by
    rw [powP]
    norm_num [pp, mulP, hpow49]
  have hpow51 : powP (0,1) 249580073232 = (99768150822,117378126758) := by
    rw [powP]
    norm_num [pp, mulP, hpow50]
  have hpow52 : powP (0,1) 249580073233 = (117378126758,21827756563) := by
    rw [powP]
    norm_num [pp, mulP, hpow51]
  have hp : powP (0,1) badR = (117378126758, 21827756563) := by
    change powP (0,1) 249580073233 = (117378126758,21827756563)
    exact hpow52
  have hm : mulP (powP (0,1) badR) (77940394259, 99768150822) = (1,1) := by
    rw [hp]
    norm_num [mulP, pp]
  calc tau ^ badR * evalP (77940394259, 99768150822)
      = evalP (powP (0,1) badR) * evalP (77940394259, 99768150822) := by rw [evalP_powP, tau]
    _ = evalP (mulP (powP (0,1) badR) (77940394259, 99768150822)) := by rw [evalP_mulP]
    _ = evalP (1,1) := by rw [hm]

lemma A355898_pos (n : ℕ) (h : 1 ≤ n) : 0 < A355898 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => simp [A355898]
      | succ n =>
        cases n with
        | zero => simp [A355898]
        | succ k =>
          rw [A355898]
          have hpos1 : 0 < A355898 (k + 2) := ih (k+2) (by omega) (by omega)
          have hpos2 : 0 < A355898 (k + 1) := ih (k+1) (by omega) (by omega)
          have hg : 0 < Nat.gcd (A355898 (k + 2)) (A355898 (k + 1)) := Nat.gcd_pos_of_pos_left _ hpos1
          exact Nat.add_pos_left hg _

lemma A_step_ne_of_common_dvd (m p0 : ℕ) (hp : 2 ≤ p0)
    (h1 : p0 ∣ A355898 (m+2)) (h2 : p0 ∣ A355898 (m+1)) :
    A355898 (m+3) ≠ 1 + A355898 (m+2) + A355898 (m+1) := by
  intro heq
  let a := A355898 (m+2)
  let b := A355898 (m+1)
  let g := Nat.gcd a b
  have hposa : 0 < a := by dsimp [a]; exact A355898_pos _ (by omega)
  have hposb : 0 < b := by dsimp [b]; exact A355898_pos _ (by omega)
  have hgdiva : g ∣ a := Nat.gcd_dvd_left a b
  have hgdivb : g ∣ b := Nat.gcd_dvd_right a b
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgdiva hposa
  have hpg : p0 ∣ g := Nat.dvd_gcd h1 h2
  have hg2 : 2 ≤ g := le_trans hp (Nat.le_of_dvd hgpos hpg)
  have hga : g ≤ a := Nat.le_of_dvd hposa hgdiva
  have hgb : g ≤ b := Nat.le_of_dvd hposb hgdivb
  have hg_half : g ≤ (a+b)/2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    nlinarith
  have hdiv_half : (a+b)/g ≤ (a+b)/2 := Nat.div_le_div_left hg2 (by norm_num : 0 < 2)
  have hsum_le : g + (a+b)/g ≤ a+b := by
    have h := Nat.add_le_add hg_half hdiv_half
    have hhalf : (a+b)/2 + (a+b)/2 ≤ a+b := by omega
    exact le_trans h hhalf
  have hactual : A355898 (m+3) ≤ a+b := by
    rw [A355898]
    change g + (a+b)/g ≤ a+b
    exact hsum_le
  have : 1 + a + b ≤ a + b := by
    rw [← heq]
    exact hactual
  omega

theorem oeis_a355898_conjecture.disproof : ¬ (∀ (n : ℕ), 3775 ≤ n →
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)) := by
  intro H
  have hqr := qB_eq H badR
  rw [cert] at hqr
  have hxraw := congrArg Quad.x hqr
  have hyraw := congrArg Quad.y hqr
  unfold qB evalP at hxraw
  unfold qB evalP at hyraw
  have hx1 : ((A355898 (3773 + badR) : ZMod pp) + 1 = (1 : ZMod pp)) := hxraw
  have hy1 : ((A355898 (3774 + badR) : ZMod pp) + 1 = (1 : ZMod pp)) := hyraw
  have hx0 : ((A355898 (3773 + badR) : ℕ) : ZMod pp) = 0 := by
    exact add_right_cancel hx1
  have hy0 : ((A355898 (3774 + badR) : ℕ) : ZMod pp) = 0 := by
    exact add_right_cancel hy1
  have hdx : pp ∣ A355898 (3773 + badR) := (ZMod.natCast_eq_zero_iff _ _).mp hx0
  have hdy : pp ∣ A355898 (3774 + badR) := (ZMod.natCast_eq_zero_iff _ _).mp hy0
  have hdy' : pp ∣ A355898 (3772 + badR + 2) := by
    rw [show 3772 + badR + 2 = 3774 + badR by omega]
    exact hdy
  have hdx' : pp ∣ A355898 (3772 + badR + 1) := by
    rw [show 3772 + badR + 1 = 3773 + badR by omega]
    exact hdx
  have hne := A_step_ne_of_common_dvd (m := 3772 + badR) (p0 := pp) (by norm_num [pp]) hdy' hdx'
  have heq0 := (H (3775 + badR) (by omega)).1
  have heq : A355898 (3772 + badR + 3) = 1 + A355898 (3772 + badR + 2) + A355898 (3772 + badR + 1) := by
    rw [show 3772 + badR + 3 = 3775 + badR by omega]
    rw [show 3772 + badR + 2 = 3775 + badR - 1 by omega]
    rw [show 3772 + badR + 1 = 3775 + badR - 2 by omega]
    exact heq0
  exact hne heq
