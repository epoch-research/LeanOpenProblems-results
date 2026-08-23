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

def st (q : ℕ × ℕ) : ℕ × ℕ :=
  (q.2, let g := Nat.gcd q.2 q.1; g + (q.2 + q.1) / g)

def fp : ℕ → ℕ × ℕ
| 0 => (1,1)
| n+1 => st (fp n)

lemma fp_eq (k : ℕ) : fp k = (A355898 (k+1), A355898 (k+2)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [fp, st, ih]
    simp only
    congr 1

set_option maxRecDepth 100000 in
lemma fp_3772 : fp 3772 = (7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617, 58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283) := by
  rfl

lemma init_mod : A355898 3773 % 195318521017 = 77940394258 ∧
    A355898 3774 % 195318521017 = 99768150821 := by
  have hh := fp_eq 3772
  rw [fp_3772] at hh
  norm_num at hh ⊢
  omega

open Matrix
open scoped Matrix

abbrev P := 195318521017
abbrev R := ZMod P

def Q : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 1]
def v0 : Fin 2 → R := ![77940394259, 99768150822]


structure M4 where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
deriving DecidableEq

def mm (x y : M4) : M4 :=
 ⟨(x.a*y.a+x.b*y.c)%P, (x.a*y.b+x.b*y.d)%P,
  (x.c*y.a+x.d*y.c)%P, (x.c*y.b+x.d*y.d)%P⟩

def fm (x : M4) (n : ℕ) : M4 :=
 if h:n=0 then ⟨1,0,0,1⟩ else
 let y:=fm x (n/2); if Even n then mm y y else mm (mm y y) x
termination_by n
 decreasing_by omega

def qm : M4 := ⟨0,1,1,1⟩

def tm (m : M4) : Matrix (Fin 2) (Fin 2) R := !![m.a, m.b; m.c, m.d]

lemma tm_mm (x y : M4) : tm (mm x y) = tm x * tm y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tm, mm, Matrix.mul_apply, ZMod.natCast_mod]

lemma tm_qm : tm qm = Q := by rfl

lemma tm_fm (x : M4) (n : ℕ) : tm (fm x n) = tm x ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [fm]
    split_ifs with hn he
    · subst n
      ext i j
      fin_cases i <;> fin_cases j <;> simp [tm]
    · rw [tm_mm, ih (n / 2) (by omega)]
      obtain ⟨k, hk⟩ := he
      subst n
      have hd : (k + k) / 2 = k := by omega
      rw [hd, pow_add]
    · rw [tm_mm, tm_mm, ih (n / 2) (by omega)]
      have ho : Odd n := Nat.not_even_iff_odd.mp he
      obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp ho
      subst n
      rw [show (2 * k + 1) / 2 = k by omega,
          show 2 * k + 1 = k + k + 1 by omega, pow_add, pow_add]
      simp

lemma fm_certificate : fm qm 249580073233 =
    ⟨117378126758, 21827756563, 21827756563, 139205883321⟩ := by
  have h0 : fm qm 0 = ⟨1, 0, 0, 1⟩ := by rw [fm]; norm_num
  have h1 : fm qm 1 = ⟨0, 1, 1, 1⟩ := by
    rw [fm, show 1 / 2 = 0 by norm_num, h0]
    rfl
  have h2 : fm qm 3 = ⟨1, 2, 2, 3⟩ := by
    rw [fm, show 3 / 2 = 1 by norm_num, h1]
    rfl
  have h3 : fm qm 7 = ⟨8, 13, 13, 21⟩ := by
    rw [fm, show 7 / 2 = 3 by norm_num, h2]
    rfl
  have h4 : fm qm 14 = ⟨233, 377, 377, 610⟩ := by
    rw [fm, show 14 / 2 = 7 by norm_num, h3]
    rfl
  have h5 : fm qm 29 = ⟨317811, 514229, 514229, 832040⟩ := by
    rw [fm, show 29 / 2 = 14 by norm_num, h4]
    rfl
  have h6 : fm qm 58 = ⟨170116775145, 5331166828, 5331166828, 175447941973⟩ := by
    rw [fm, show 58 / 2 = 29 by norm_num, h5]
    rfl
  have h7 : fm qm 116 = ⟨49773924280, 192440766623, 192440766623, 46896169886⟩ := by
    rw [fm, show 116 / 2 = 58 by norm_num, h6]
    rfl
  have h8 : fm qm 232 = ⟨155867475481, 194305937469, 194305937469, 154854891933⟩ := by
    rw [fm, show 232 / 2 = 116 by norm_num, h7]
    rfl
  have h9 : fm qm 464 = ⟨1614955175, 27770261298, 27770261298, 29385216473⟩ := by
    rw [fm, show 464 / 2 = 232 by norm_num, h8]
    rfl
  have h10 : fm qm 929 = ⟨96254381253, 86864070201, 86864070201, 183118451454⟩ := by
    rw [fm, show 929 / 2 = 464 by norm_num, h9]
    rfl
  have h11 : fm qm 1859 = ⟨38868090280, 161742261918, 161742261918, 5291831181⟩ := by
    rw [fm, show 1859 / 2 = 929 by norm_num, h10]
    rfl
  have h12 : fm qm 3719 = ⟨109362536927, 45733414097, 45733414097, 155095951024⟩ := by
    rw [fm, show 3719 / 2 = 1859 by norm_num, h11]
    rfl
  have h13 : fm qm 7438 = ⟨183298122861, 91402293237, 91402293237, 79381895081⟩ := by
    rw [fm, show 7438 / 2 = 3719 by norm_num, h12]
    rfl
  have h14 : fm qm 14876 = ⟨25992400769, 124511110930, 124511110930, 150503511699⟩ := by
    rw [fm, show 14876 / 2 = 7438 by norm_num, h13]
    rfl
  have h15 : fm qm 29752 = ⟨177745180195, 131120349488, 131120349488, 113547008666⟩ := by
    rw [fm, show 29752 / 2 = 14876 by norm_num, h14]
    rfl
  have h16 : fm qm 59504 = ⟨194001049843, 38091898265, 38091898265, 36774427091⟩ := by
    rw [fm, show 59504 / 2 = 29752 by norm_num, h15]
    rfl
  have h17 : fm qm 119009 = ⟨127215937123, 154094075776, 154094075776, 85991491882⟩ := by
    rw [fm, show 119009 / 2 = 59504 by norm_num, h16]
    rfl
  have h18 : fm qm 238018 = ⟨63462935697, 77229582369, 77229582369, 140692518066⟩ := by
    rw [fm, show 238018 / 2 = 119009 by norm_num, h17]
    rfl
  have h19 : fm qm 476036 = ⟨38241365584, 133112644149, 133112644149, 171354009733⟩ := by
    rw [fm, show 476036 / 2 = 238018 by norm_num, h18]
    rfl
  have h20 : fm qm 952072 = ⟨138114740259, 112954738797, 112954738797, 55750958039⟩ := by
    rw [fm, show 952072 / 2 = 476036 by norm_num, h19]
    rfl
  have h21 : fm qm 1904144 = ⟨154056996875, 158795593120, 158795593120, 117534068978⟩ := by
    rw [fm, show 1904144 / 2 = 952072 by norm_num, h20]
    rfl
  have h22 : fm qm 3808289 = ⟨179877156576, 55730958665, 55730958665, 40289594224⟩ := by
    rw [fm, show 3808289 / 2 = 1904144 by norm_num, h21]
    rfl
  have h23 : fm qm 7616579 = ⟨158541234730, 13069814284, 13069814284, 171611049014⟩ := by
    rw [fm, show 7616579 / 2 = 3808289 by norm_num, h22]
    rfl
  have h24 : fm qm 15233158 = ⟨171187543582, 38127008062, 38127008062, 13996030627⟩ := by
    rw [fm, show 15233158 / 2 = 7616579 by norm_num, h23]
    rfl
  have h25 : fm qm 30466317 = ⟨146193284997, 123761895008, 123761895008, 74636658988⟩ := by
    rw [fm, show 30466317 / 2 = 15233158 by norm_num, h24]
    rfl
  have h26 : fm qm 60932635 = ⟨62910314271, 25816540105, 25816540105, 88726854376⟩ := by
    rw [fm, show 60932635 / 2 = 30466317 by norm_num, h25]
    rfl
  have h27 : fm qm 121865270 = ⟨62835551386, 33068008935, 33068008935, 95903560321⟩ := by
    rw [fm, show 121865270 / 2 = 60932635 by norm_num, h26]
    rfl
  have h28 : fm qm 243730540 = ⟨140733322397, 176142473281, 176142473281, 121557274661⟩ := by
    rw [fm, show 243730540 / 2 = 121865270 by norm_num, h27]
    rfl
  have h29 : fm qm 487461080 = ⟨99726976518, 183150853626, 183150853626, 87559309127⟩ := by
    rw [fm, show 487461080 / 2 = 243730540 by norm_num, h28]
    rfl
  have h30 : fm qm 974922161 = ⟨144811362904, 181498976850, 181498976850, 130991818737⟩ := by
    rw [fm, show 974922161 / 2 = 487461080 by norm_num, h29]
    rfl
  have h31 : fm qm 1949844322 = ⟨107789511149, 194855280932, 194855280932, 107326271064⟩ := by
    rw [fm, show 1949844322 / 2 = 974922161 by norm_num, h30]
    rfl
  have h32 : fm qm 3899688644 = ⟨40500134143, 92273131568, 92273131568, 132773265711⟩ := by
    rw [fm, show 3899688644 / 2 = 1949844322 by norm_num, h31]
    rfl
  have h33 : fm qm 7799377288 = ⟨81220899006, 16299744117, 16299744117, 97520643123⟩ := by
    rw [fm, show 7799377288 / 2 = 3899688644 by norm_num, h32]
    rfl
  have h34 : fm qm 15598754577 = ⟨36811031866, 114245750984, 114245750984, 151056782850⟩ := by
    rw [fm, show 15598754577 / 2 = 7799377288 by norm_num, h33]
    rfl
  have h35 : fm qm 31197509154 = ⟨122815009445, 161884538056, 161884538056, 89381026484⟩ := by
    rw [fm, show 31197509154 / 2 = 15598754577 by norm_num, h34]
    rfl
  have h36 : fm qm 62395018308 = ⟨183264428700, 124390278326, 124390278326, 112336186009⟩ := by
    rw [fm, show 62395018308 / 2 = 31197509154 by norm_num, h35]
    rfl
  have h37 : fm qm 124790036616 = ⟨16143421115, 161398467405, 161398467405, 177541888520⟩ := by
    rw [fm, show 124790036616 / 2 = 62395018308 by norm_num, h36]
    rfl
  have h38 : fm qm 249580073233 = ⟨117378126758, 21827756563, 21827756563, 139205883321⟩ := by
    rw [fm, show 249580073233 / 2 = 124790036616 by norm_num, h37]
    rfl
  exact h38

lemma matrix_certificate : Q ^ (249580073233 : ℕ) *ᵥ v0 = ![1, 1] := by
  rw [← tm_qm, ← tm_fm, fm_certificate]
  ext i
  fin_cases i <;> decide

set_option maxRecDepth 10000 in
lemma state_of_rec
    (H : ∀ n : ℕ, 3775 ≤ n → A355898 n = 1 + A355898 (n-1) + A355898 (n-2)) (k : ℕ) :
    ![((A355898 (3773+k) + 1 : ℕ) : R), ((A355898 (3774+k) + 1 : ℕ) : R)] =
      Q ^ k *ᵥ v0 := by
  induction k with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec]
    have hi := init_mod
    have h1 : (A355898 3773 : R) = 77940394258 := by
      rw [← ZMod.natCast_mod (A355898 3773), hi.1]
      rfl
    have h2 : (A355898 3774 : R) = 99768150821 := by
      rw [← ZMod.natCast_mod (A355898 3774), hi.2]
      rfl
    have h1p : (((A355898 3773 + 1 : ℕ) : R)) = 77940394259 := by
      push_cast
      rw [h1]
      norm_num
    have h2p : (((A355898 3774 + 1 : ℕ) : R)) = 99768150822 := by
      push_cast
      rw [h2]
      norm_num
    ext i
    fin_cases i
    · exact h1p
    · exact h2p
  | succ k ih =>
    have hr := H (3775+k) (by omega)
    rw [show 3775+k-1=3774+k by omega,
        show 3775+k-2=3773+k by omega] at hr
    have hind :
        ![((A355898 (3774+k) + 1 : ℕ) : R), ((A355898 (3775+k) + 1 : ℕ) : R)] =
        Q *ᵥ ![((A355898 (3773+k) + 1 : ℕ) : R), ((A355898 (3774+k) + 1 : ℕ) : R)] := by
      ext i
      fin_cases i
      · simp [Q]
      · simp [Q]
        rw [hr]
        push_cast
        ring
    rw [show 3773 + (k+1) = 3774+k by omega,
        show 3774 + (k+1) = 3775+k by omega,
        hind, ih, _root_.pow_succ']
    exact Matrix.mulVec_mulVec _ _ _

lemma no_rec_of_matrix (k : ℕ) (hk : 2 ≤ k) (hc : Q ^ k *ᵥ v0 = ![1, 1]) :
    ¬ (∀ n : ℕ, 3775 ≤ n → A355898 n = 1 + A355898 (n-1) + A355898 (n-2)) := by
  intro H
  have hs := state_of_rec H k
  rw [hc] at hs
  have hzlo : ((A355898 (3773+k) : R)) = 0 := by
    have hh := congrFun hs (0 : Fin 2)
    change (((A355898 (3773+k) + 1 : ℕ) : R)) = 1 at hh
    push_cast at hh
    calc
      (A355898 (3773+k) : R) = (A355898 (3773+k) : R) + 1 - 1 := by ring
      _ = 1 - 1 := by rw [hh]
      _ = 0 := by ring
  have hzhi : ((A355898 (3774+k) : R)) = 0 := by
    have hh := congrFun hs (1 : Fin 2)
    change (((A355898 (3774+k) + 1 : ℕ) : R)) = 1 at hh
    push_cast at hh
    calc
      (A355898 (3774+k) : R) = (A355898 (3774+k) : R) + 1 - 1 := by ring
      _ = 1 - 1 := by rw [hh]
      _ = 0 := by ring
  have hdlo : P ∣ A355898 (3773+k) :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzlo
  have hdhi : P ∣ A355898 (3774+k) :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzhi
  let x := A355898 (3773+k)
  let y := A355898 (3774+k)
  let g := Nat.gcd y x
  let s := y + x
  have hx : 0 < x := by
    dsimp [x]
    rw [H (3773+k) (by omega)]
    omega
  have hy : 0 < y := by
    dsimp [y]
    rw [H (3774+k) (by omega)]
    omega
  have hpg : P ∣ g := Nat.dvd_gcd hdhi hdlo
  have hg2 : 2 ≤ g := by
    have hp_le := Nat.le_of_dvd (show 0 < g by
      exact Nat.gcd_pos_of_pos_left x hy) hpg
    have hp : 2 ≤ P := by norm_num [P]
    omega
  have hgs : g ∣ s :=
    Nat.dvd_add (Nat.gcd_dvd_left y x) (Nat.gcd_dvd_right y x)
  have hsg : g < s := by
    have hle := Nat.gcd_le_left x hy
    dsimp [g, s, y, x] at hle ⊢
    omega
  have hdef : A355898 (3775+k) = g + s / g := by
    rw [show 3775+k = (3772+k)+3 by omega, A355898,
        show 3772+k+2=3774+k by omega,
        show 3772+k+1=3773+k by omega]
  have hrec := H (3775+k) (by omega)
  rw [show 3775+k-1=3774+k by omega,
      show 3775+k-2=3773+k by omega] at hrec
  have heq : g + s / g = 1 + s := by
    rw [← hdef, hrec]
    simp only [s, y, x]
    omega
  have hmul : g * (s / g) = s := Nat.mul_div_cancel' hgs
  have hq : 2 ≤ s / g := by
    by_contra hh
    have hsmall : s / g = 0 ∨ s / g = 1 := by omega
    rcases hsmall with hzero | hone
    · rw [hzero] at hmul
      simp at hmul
      omega
    · rw [hone] at hmul
      simp at hmul
      omega
  nlinarith only [hg2, hq, heq, hmul]

/-- The proposed eventual recurrence is false. -/
theorem oeis_a355898_conjecture.disproof : ¬ (∀ (n : ℕ), 3775 ≤ n →
    (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
    ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
    ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) -
        (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)) := by
  intro H
  apply no_rec_of_matrix 249580073233 (by omega) matrix_certificate
  intro n hn
  exact (H n hn).1
