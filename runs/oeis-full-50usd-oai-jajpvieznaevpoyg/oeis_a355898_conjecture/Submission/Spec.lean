import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/--
A355898: $a(1) = a(2) = 1$; $a(n) = \gcd(a(n-1), a(n-2)) + \frac{a(n-1) + a(n-2)}{\gcd(a(n-1), a(n-2)}$.
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

namespace A355898Disproof

abbrev p : ℕ := 195318521017
abbrev m : ℕ := 249580073233
abbrev k : ℕ := 249580077007
abbrev N : ℕ := 249580077008
abbrev R := ZMod p

abbrev M : Matrix (Fin 2) (Fin 2) R := !![1, 1; 1, 0]


structure CMat where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
deriving DecidableEq, Repr

namespace CMat

def one : CMat := ⟨1, 0, 0, 1⟩
def fib : CMat := ⟨1, 1, 1, 0⟩

def mul (X Y : CMat) : CMat :=
  ⟨(X.a * Y.a + X.b * Y.c) % p,
   (X.a * Y.b + X.b * Y.d) % p,
   (X.c * Y.a + X.d * Y.c) % p,
   (X.c * Y.b + X.d * Y.d) % p⟩

def pow : ℕ → CMat :=
  Nat.binaryRec one fun b _ q =>
    let q2 := mul q q
    if b then mul q2 fib else q2

def app (X : CMat) (u v : ℕ) : ℕ × ℕ :=
  (((X.a * u + X.b * v) % p), ((X.c * u + X.d * v) % p))

abbrev toM (X : CMat) : Matrix (Fin 2) (Fin 2) R := !![(X.a : R), (X.b : R); (X.c : R), (X.d : R)]

lemma toM_one : toM one = (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [toM, one]

lemma toM_fib : toM fib = M := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [toM, fib, M]

lemma toM_mul (X Y : CMat) : toM (mul X Y) = toM X * toM Y := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [toM, mul, Matrix.mul_apply, Fin.sum_univ_two, ZMod.natCast_mod] <;> ring

lemma toM_pow (n : ℕ) : toM (pow n) = M ^ n := by
  refine Nat.binaryRec ?_ ?_ n
  · simp [pow, toM_one]
  · intro b n ih
    rw [pow, Nat.binaryRec_eq b n (by cases b <;> simp [pow, one, mul])]
    cases b
    · change toM (mul (pow n) (pow n)) = M ^ Nat.bit false n
      rw [toM_mul, ih]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.bit]
      rw [← pow_add]
      change M ^ (n + n) = M ^ (2 * n)
      congr
      omega
    · change toM (mul (mul (pow n) (pow n)) fib) = M ^ Nat.bit true n
      rw [toM_mul, toM_mul, toM_fib, ih]
      simp only [Bool.true_eq_false, ↓reduceIte, Nat.bit]
      rw [← pow_add, ← pow_succ]
      change M ^ (n + n + 1) = M ^ (2 * n + 1)
      congr
      omega

lemma app_eq_mulVec (X : CMat) (u v : ℕ) :
    ![((app X u v).1 : R), ((app X u v).2 : R)] = Matrix.mulVec (toM X) ![(u : R), (v : R)] := by
  ext i <;> fin_cases i <;> simp [app, toM, Matrix.mulVec, Fin.sum_univ_two, ZMod.natCast_mod]

end CMat

-- Iterative evaluator for the initial finite segment.
def stepA (q : ℕ × ℕ) : ℕ × ℕ :=
  let g := Nat.gcd q.2 q.1
  (q.2, g + (q.2 + q.1) / g)

def iterB : ℕ → ℕ × ℕ
| 0 => (1, 1)
| t + 1 => stepA (iterB t)

lemma iterB_spec (t : ℕ) : (iterB t).1 = A355898 (t + 1) ∧ (iterB t).2 = A355898 (t + 2) := by
  induction t with
  | zero => simp [iterB, A355898]
  | succ t ih =>
      rcases ih with ⟨h1, h2⟩
      constructor
      · simpa [iterB] using h2
      · simp only [iterB, stepA]
        rw [h1, h2]
        change Nat.gcd (A355898 (t + 2)) (A355898 (t + 1)) +
            (A355898 (t + 2) + A355898 (t + 1)) / Nat.gcd (A355898 (t + 2)) (A355898 (t + 1)) =
          A355898 (t + 3)
        rfl

lemma base_mod_cert :
    (((A355898 3774 + 1 : ℕ) : R) = (99768150822 : R)) ∧
    (((A355898 3773 + 1 : ℕ) : R) = (77940394259 : R)) := by
  have h := iterB_spec 3772
  constructor
  · rw [← h.2]
    exact (ZMod.natCast_eq_natCast_iff _ _ p).2 (by decide)
  · rw [← h.1]
    exact (ZMod.natCast_eq_natCast_iff _ _ p).2 (by decide)

lemma CMat_pow_aux_0 : CMat.pow 0 = CMat.one := by
  simp [CMat.pow]
lemma CMat_pow_aux_1 : CMat.pow 1 = ⟨1, 1, 1, 0⟩ := by
  rw [show 1 = Nat.bit true 0 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 0 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 0) (CMat.pow 0)) CMat.fib = ⟨1, 1, 1, 0⟩
  rw [CMat_pow_aux_0]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_2 : CMat.pow 3 = ⟨3, 2, 2, 1⟩ := by
  rw [show 3 = Nat.bit true 1 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 1 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 1) (CMat.pow 1)) CMat.fib = ⟨3, 2, 2, 1⟩
  rw [CMat_pow_aux_1]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_3 : CMat.pow 7 = ⟨21, 13, 13, 8⟩ := by
  rw [show 7 = Nat.bit true 3 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 3 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 3) (CMat.pow 3)) CMat.fib = ⟨21, 13, 13, 8⟩
  rw [CMat_pow_aux_2]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_4 : CMat.pow 14 = ⟨610, 377, 377, 233⟩ := by
  rw [show 14 = Nat.bit false 7 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 7 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 7) (CMat.pow 7) = ⟨610, 377, 377, 233⟩
  rw [CMat_pow_aux_3]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_5 : CMat.pow 29 = ⟨832040, 514229, 514229, 317811⟩ := by
  rw [show 29 = Nat.bit true 14 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 14 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 14) (CMat.pow 14)) CMat.fib = ⟨832040, 514229, 514229, 317811⟩
  rw [CMat_pow_aux_4]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_6 : CMat.pow 58 = ⟨175447941973, 5331166828, 5331166828, 170116775145⟩ := by
  rw [show 58 = Nat.bit false 29 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 29 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 29) (CMat.pow 29) = ⟨175447941973, 5331166828, 5331166828, 170116775145⟩
  rw [CMat_pow_aux_5]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_7 : CMat.pow 116 = ⟨46896169886, 192440766623, 192440766623, 49773924280⟩ := by
  rw [show 116 = Nat.bit false 58 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 58 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 58) (CMat.pow 58) = ⟨46896169886, 192440766623, 192440766623, 49773924280⟩
  rw [CMat_pow_aux_6]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_8 : CMat.pow 232 = ⟨154854891933, 194305937469, 194305937469, 155867475481⟩ := by
  rw [show 232 = Nat.bit false 116 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 116 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 116) (CMat.pow 116) = ⟨154854891933, 194305937469, 194305937469, 155867475481⟩
  rw [CMat_pow_aux_7]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_9 : CMat.pow 464 = ⟨29385216473, 27770261298, 27770261298, 1614955175⟩ := by
  rw [show 464 = Nat.bit false 232 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 232 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 232) (CMat.pow 232) = ⟨29385216473, 27770261298, 27770261298, 1614955175⟩
  rw [CMat_pow_aux_8]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_10 : CMat.pow 929 = ⟨183118451454, 86864070201, 86864070201, 96254381253⟩ := by
  rw [show 929 = Nat.bit true 464 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 464 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 464) (CMat.pow 464)) CMat.fib = ⟨183118451454, 86864070201, 86864070201, 96254381253⟩
  rw [CMat_pow_aux_9]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_11 : CMat.pow 1859 = ⟨5291831181, 161742261918, 161742261918, 38868090280⟩ := by
  rw [show 1859 = Nat.bit true 929 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 929 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 929) (CMat.pow 929)) CMat.fib = ⟨5291831181, 161742261918, 161742261918, 38868090280⟩
  rw [CMat_pow_aux_10]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_12 : CMat.pow 3719 = ⟨155095951024, 45733414097, 45733414097, 109362536927⟩ := by
  rw [show 3719 = Nat.bit true 1859 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 1859 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 1859) (CMat.pow 1859)) CMat.fib = ⟨155095951024, 45733414097, 45733414097, 109362536927⟩
  rw [CMat_pow_aux_11]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_13 : CMat.pow 7438 = ⟨79381895081, 91402293237, 91402293237, 183298122861⟩ := by
  rw [show 7438 = Nat.bit false 3719 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 3719 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 3719) (CMat.pow 3719) = ⟨79381895081, 91402293237, 91402293237, 183298122861⟩
  rw [CMat_pow_aux_12]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_14 : CMat.pow 14876 = ⟨150503511699, 124511110930, 124511110930, 25992400769⟩ := by
  rw [show 14876 = Nat.bit false 7438 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 7438 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 7438) (CMat.pow 7438) = ⟨150503511699, 124511110930, 124511110930, 25992400769⟩
  rw [CMat_pow_aux_13]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_15 : CMat.pow 29752 = ⟨113547008666, 131120349488, 131120349488, 177745180195⟩ := by
  rw [show 29752 = Nat.bit false 14876 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 14876 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 14876) (CMat.pow 14876) = ⟨113547008666, 131120349488, 131120349488, 177745180195⟩
  rw [CMat_pow_aux_14]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_16 : CMat.pow 59504 = ⟨36774427091, 38091898265, 38091898265, 194001049843⟩ := by
  rw [show 59504 = Nat.bit false 29752 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 29752 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 29752) (CMat.pow 29752) = ⟨36774427091, 38091898265, 38091898265, 194001049843⟩
  rw [CMat_pow_aux_15]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_17 : CMat.pow 119009 = ⟨85991491882, 154094075776, 154094075776, 127215937123⟩ := by
  rw [show 119009 = Nat.bit true 59504 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 59504 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 59504) (CMat.pow 59504)) CMat.fib = ⟨85991491882, 154094075776, 154094075776, 127215937123⟩
  rw [CMat_pow_aux_16]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_18 : CMat.pow 238018 = ⟨140692518066, 77229582369, 77229582369, 63462935697⟩ := by
  rw [show 238018 = Nat.bit false 119009 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 119009 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 119009) (CMat.pow 119009) = ⟨140692518066, 77229582369, 77229582369, 63462935697⟩
  rw [CMat_pow_aux_17]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_19 : CMat.pow 476036 = ⟨171354009733, 133112644149, 133112644149, 38241365584⟩ := by
  rw [show 476036 = Nat.bit false 238018 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 238018 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 238018) (CMat.pow 238018) = ⟨171354009733, 133112644149, 133112644149, 38241365584⟩
  rw [CMat_pow_aux_18]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_20 : CMat.pow 952072 = ⟨55750958039, 112954738797, 112954738797, 138114740259⟩ := by
  rw [show 952072 = Nat.bit false 476036 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 476036 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 476036) (CMat.pow 476036) = ⟨55750958039, 112954738797, 112954738797, 138114740259⟩
  rw [CMat_pow_aux_19]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_21 : CMat.pow 1904144 = ⟨117534068978, 158795593120, 158795593120, 154056996875⟩ := by
  rw [show 1904144 = Nat.bit false 952072 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 952072 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 952072) (CMat.pow 952072) = ⟨117534068978, 158795593120, 158795593120, 154056996875⟩
  rw [CMat_pow_aux_20]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_22 : CMat.pow 3808289 = ⟨40289594224, 55730958665, 55730958665, 179877156576⟩ := by
  rw [show 3808289 = Nat.bit true 1904144 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 1904144 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 1904144) (CMat.pow 1904144)) CMat.fib = ⟨40289594224, 55730958665, 55730958665, 179877156576⟩
  rw [CMat_pow_aux_21]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_23 : CMat.pow 7616579 = ⟨171611049014, 13069814284, 13069814284, 158541234730⟩ := by
  rw [show 7616579 = Nat.bit true 3808289 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 3808289 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 3808289) (CMat.pow 3808289)) CMat.fib = ⟨171611049014, 13069814284, 13069814284, 158541234730⟩
  rw [CMat_pow_aux_22]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_24 : CMat.pow 15233158 = ⟨13996030627, 38127008062, 38127008062, 171187543582⟩ := by
  rw [show 15233158 = Nat.bit false 7616579 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 7616579 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 7616579) (CMat.pow 7616579) = ⟨13996030627, 38127008062, 38127008062, 171187543582⟩
  rw [CMat_pow_aux_23]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_25 : CMat.pow 30466317 = ⟨74636658988, 123761895008, 123761895008, 146193284997⟩ := by
  rw [show 30466317 = Nat.bit true 15233158 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 15233158 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 15233158) (CMat.pow 15233158)) CMat.fib = ⟨74636658988, 123761895008, 123761895008, 146193284997⟩
  rw [CMat_pow_aux_24]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_26 : CMat.pow 60932635 = ⟨88726854376, 25816540105, 25816540105, 62910314271⟩ := by
  rw [show 60932635 = Nat.bit true 30466317 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 30466317 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 30466317) (CMat.pow 30466317)) CMat.fib = ⟨88726854376, 25816540105, 25816540105, 62910314271⟩
  rw [CMat_pow_aux_25]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_27 : CMat.pow 121865270 = ⟨95903560321, 33068008935, 33068008935, 62835551386⟩ := by
  rw [show 121865270 = Nat.bit false 60932635 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 60932635 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 60932635) (CMat.pow 60932635) = ⟨95903560321, 33068008935, 33068008935, 62835551386⟩
  rw [CMat_pow_aux_26]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_28 : CMat.pow 243730540 = ⟨121557274661, 176142473281, 176142473281, 140733322397⟩ := by
  rw [show 243730540 = Nat.bit false 121865270 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 121865270 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 121865270) (CMat.pow 121865270) = ⟨121557274661, 176142473281, 176142473281, 140733322397⟩
  rw [CMat_pow_aux_27]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_29 : CMat.pow 487461080 = ⟨87559309127, 183150853626, 183150853626, 99726976518⟩ := by
  rw [show 487461080 = Nat.bit false 243730540 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 243730540 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 243730540) (CMat.pow 243730540) = ⟨87559309127, 183150853626, 183150853626, 99726976518⟩
  rw [CMat_pow_aux_28]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_30 : CMat.pow 974922161 = ⟨130991818737, 181498976850, 181498976850, 144811362904⟩ := by
  rw [show 974922161 = Nat.bit true 487461080 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 487461080 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 487461080) (CMat.pow 487461080)) CMat.fib = ⟨130991818737, 181498976850, 181498976850, 144811362904⟩
  rw [CMat_pow_aux_29]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_31 : CMat.pow 1949844322 = ⟨107326271064, 194855280932, 194855280932, 107789511149⟩ := by
  rw [show 1949844322 = Nat.bit false 974922161 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 974922161 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 974922161) (CMat.pow 974922161) = ⟨107326271064, 194855280932, 194855280932, 107789511149⟩
  rw [CMat_pow_aux_30]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_32 : CMat.pow 3899688644 = ⟨132773265711, 92273131568, 92273131568, 40500134143⟩ := by
  rw [show 3899688644 = Nat.bit false 1949844322 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 1949844322 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 1949844322) (CMat.pow 1949844322) = ⟨132773265711, 92273131568, 92273131568, 40500134143⟩
  rw [CMat_pow_aux_31]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_33 : CMat.pow 7799377288 = ⟨97520643123, 16299744117, 16299744117, 81220899006⟩ := by
  rw [show 7799377288 = Nat.bit false 3899688644 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 3899688644 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 3899688644) (CMat.pow 3899688644) = ⟨97520643123, 16299744117, 16299744117, 81220899006⟩
  rw [CMat_pow_aux_32]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_34 : CMat.pow 15598754577 = ⟨151056782850, 114245750984, 114245750984, 36811031866⟩ := by
  rw [show 15598754577 = Nat.bit true 7799377288 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 7799377288 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 7799377288) (CMat.pow 7799377288)) CMat.fib = ⟨151056782850, 114245750984, 114245750984, 36811031866⟩
  rw [CMat_pow_aux_33]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_35 : CMat.pow 31197509154 = ⟨89381026484, 161884538056, 161884538056, 122815009445⟩ := by
  rw [show 31197509154 = Nat.bit false 15598754577 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 15598754577 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 15598754577) (CMat.pow 15598754577) = ⟨89381026484, 161884538056, 161884538056, 122815009445⟩
  rw [CMat_pow_aux_34]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_36 : CMat.pow 62395018308 = ⟨112336186009, 124390278326, 124390278326, 183264428700⟩ := by
  rw [show 62395018308 = Nat.bit false 31197509154 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 31197509154 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 31197509154) (CMat.pow 31197509154) = ⟨112336186009, 124390278326, 124390278326, 183264428700⟩
  rw [CMat_pow_aux_35]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_37 : CMat.pow 124790036616 = ⟨177541888520, 161398467405, 161398467405, 16143421115⟩ := by
  rw [show 124790036616 = Nat.bit false 62395018308 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq false 62395018308 (by right; intro h; norm_num at h)]
  change CMat.mul (CMat.pow 62395018308) (CMat.pow 62395018308) = ⟨177541888520, 161398467405, 161398467405, 16143421115⟩
  rw [CMat_pow_aux_36]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]
lemma CMat_pow_aux_38 : CMat.pow 249580073233 = ⟨139205883321, 21827756563, 21827756563, 117378126758⟩ := by
  rw [show 249580073233 = Nat.bit true 124790036616 by norm_num [Nat.bit]]
  unfold CMat.pow
  rw [Nat.binaryRec_eq true 124790036616 (by right; intro _; rfl)]
  change CMat.mul (CMat.mul (CMat.pow 124790036616) (CMat.pow 124790036616)) CMat.fib = ⟨139205883321, 21827756563, 21827756563, 117378126758⟩
  rw [CMat_pow_aux_37]
  norm_num [CMat.mul, CMat.fib, CMat.one, p]

lemma pow_cert :
    CMat.app (CMat.pow m) 99768150822 77940394259 = (1, 1) := by
  rw [show m = 249580073233 by norm_num [m], CMat_pow_aux_38]
  norm_num [CMat.app, p]

lemma zmod_eq_zero_of_succ_eq_one {a : ℕ} (h : (((a + 1 : ℕ) : R) = (1 : R))) :
    ((a : R) = 0) := by
  simpa only [Nat.cast_add, Nat.cast_one, add_eq_right] using h

lemma dvd_of_zmod_zero {a : ℕ} (h : ((a : R) = 0)) : p ∣ a := by
  exact (ZMod.natCast_eq_zero_iff a p).1 h

lemma lin_orbit_of_conj
    (H : ∀ (n : ℕ), 3775 ≤ n →
      (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
      ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
      ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)) :
    ∀ t : ℕ,
      Matrix.mulVec (M ^ t) ![((A355898 3774 + 1 : ℕ) : R), ((A355898 3773 + 1 : ℕ) : R)] =
        ![((A355898 (3774 + t) + 1 : ℕ) : R), ((A355898 (3773 + t) + 1 : ℕ) : R)] := by
  intro t
  induction t with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ t ih =>
      have hrec := (H (3775 + t) (by omega)).1
      have hn1 : 3775 + t - 1 = 3774 + t := by omega
      have hn2 : 3775 + t - 2 = 3773 + t := by omega
      rw [_root_.pow_succ', ← Matrix.mulVec_mulVec, ih]
      ext i <;> fin_cases i
      · simp [M, Matrix.mulVec, Fin.sum_univ_two]
        have hrec' : A355898 (3775 + t) = 1 + A355898 (3774 + t) + A355898 (3773 + t) := by
          simpa [hn1, hn2] using hrec
        rw [show 3774 + (t + 1) = 3775 + t by omega, hrec']
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
      · simp [M, Matrix.mulVec, Fin.sum_univ_two]
        rw [show 3773 + (t + 1) = 3774 + t by omega]

lemma bad_step {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hpga : p ∣ a) (hpgb : p ∣ b) :
    let g := Nat.gcd a b
    g + (a + b) / g ≠ 1 + a + b := by
  intro g heq
  have hgdef : g = Nat.gcd a b := rfl
  have hpgt : p ∣ g := by simpa [hgdef] using Nat.dvd_gcd hpga hpgb
  have hp1 : 1 < p := by norm_num [p]
  have hgne1 : g ≠ 1 := by
    intro h1
    have : p ∣ 1 := by simpa [h1] using hpgt
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 1) hp1) this
  have hgpos : 0 < g := by rw [hgdef]; exact Nat.gcd_pos_of_pos_left _ ha
  have hg2 : 2 ≤ g := by omega
  have hga : g ∣ a := by rw [hgdef]; exact Nat.gcd_dvd_left a b
  have hgb : g ∣ b := by rw [hgdef]; exact Nat.gcd_dvd_right a b
  rcases hga with ⟨aa, haa_eq⟩
  rcases hgb with ⟨bb, hbb_eq⟩
  have haa : 0 < aa := by
    rw [haa_eq] at ha
    exact Nat.pos_of_mul_pos_left ha
  have hbb : 0 < bb := by
    rw [hbb_eq] at hb
    exact Nat.pos_of_mul_pos_left hb
  rw [haa_eq, hbb_eq] at heq
  rw [← Nat.mul_add, Nat.mul_div_right _ hgpos] at heq
  nlinarith

lemma A355898_step (q : ℕ) : A355898 (q + 3) =
    let an_minus_1 := A355898 (q + 2)
    let an_minus_2 := A355898 (q + 1)
    let g := Nat.gcd an_minus_1 an_minus_2
    g + (an_minus_1 + an_minus_2) / g := by
  rfl

end A355898Disproof

/--
Conjecture: For n >= 3775 a(n) can also be expressed in the following three ways:
1) a(n) = 1 + a(n-1) + a(n-2).
2) a(n) = 2*a(n-1) - a(n-3).
3) If A = a(3774), B = a(3772) and F = Fibonacci A000045(n),
   a(n) = (A+1)*F(n-3772) - (B+1)*F(n-3774) - 1.
These three formulas only work for n >= 3775.
-/
theorem oeis_a355898_conjecture.disproof :
  ¬ (∀ (n : ℕ), 3775 ≤ n →
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)) := by
  intro H
  open A355898Disproof in
  have horb := lin_orbit_of_conj H m
  have hbase := base_mod_cert
  have hpowNat := pow_cert
  have hpowZ : Matrix.mulVec (M ^ m) ![((A355898 3774 + 1 : ℕ) : R), ((A355898 3773 + 1 : ℕ) : R)] = ![(1 : R), (1 : R)] := by
    have hc := CMat.app_eq_mulVec (CMat.pow m) 99768150822 77940394259
    rw [hpowNat] at hc
    rw [CMat.toM_pow] at hc
    change ![(1 : R), (1 : R)] = Matrix.mulVec (M ^ m) ![(99768150822 : R), (77940394259 : R)] at hc
    rw [← hbase.1, ← hbase.2] at hc
    exact hc.symm
  rw [hpowZ] at horb
  have hk_succ : (((A355898 k + 1 : ℕ) : R) = (1 : R)) := by
    have hc0 := congr_fun horb 0
    change (1 : R) = ((A355898 (3774 + m) + 1 : ℕ) : R) at hc0
    have hk : 3774 + m = k := by norm_num [m, k]
    rw [hk] at hc0
    exact hc0.symm
  have hkm_succ : (((A355898 (k - 1) + 1 : ℕ) : R) = (1 : R)) := by
    have hc1 := congr_fun horb 1
    change (1 : R) = ((A355898 (3773 + m) + 1 : ℕ) : R) at hc1
    have hk1 : 3773 + m = k - 1 := by norm_num [m, k]
    rw [hk1] at hc1
    exact hc1.symm
  have hpk : p ∣ A355898 k := dvd_of_zmod_zero (zmod_eq_zero_of_succ_eq_one hk_succ)
  have hpkm : p ∣ A355898 (k - 1) := dvd_of_zmod_zero (zmod_eq_zero_of_succ_eq_one hkm_succ)
  have hN := (H N (by norm_num [N])).1
  have hNm1 : N - 1 = k := by norm_num [N, k]
  have hNm2 : N - 2 = k - 1 := by norm_num [N, k]
  set kk : ℕ := k - 2 with hkk
  have hdef : A355898 N =
      let g := Nat.gcd (A355898 k) (A355898 (k - 1))
      g + (A355898 k + A355898 (k - 1)) / g := by
    rw [show N = kk + 3 by rw [hkk]; norm_num [N, k]]
    rw [A355898_step kk]
    rw [show kk + 2 = k by rw [hkk]; norm_num [k], show kk + 1 = k - 1 by rw [hkk]; norm_num [k]]
  rw [hNm1, hNm2] at hN
  rw [hdef] at hN
  have hposk : 0 < A355898 k := by
    rw [(H k (by norm_num [k])).1]
    omega
  have hposkm : 0 < A355898 (k - 1) := by
    rw [(H (k - 1) (by norm_num [k])).1]
    omega
  exact bad_step hposk hposkm hpk hpkm hN
