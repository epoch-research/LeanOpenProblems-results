import FormalConjectures.Util.ProblemImports
open Nat

def sqDist (t x : Nat) : Nat := if x ≤ t then (t - x)^2 else (x - t)^2

lemma sqDist_cast (t x : Nat) : ((sqDist t x : Nat) : Int) = ((x : Int) - (t : Int))^2 := by
  unfold sqDist
  by_cases h : x ≤ t
  · simp [h]
    ring
  · simp [h]
    have hxt : t ≤ x := le_of_not_ge h
    have hsub : ((x - t : Nat) : Int) = (x:Int) - (t:Int) := by omega
    rw [hsub]

lemma sqDist_modEq {t x y r : Nat} (hxy : x ≡ y [MOD 2^r])
    (hdiv : (8 : Int) ∣ ((x:Int) + (y:Int) - 2*(t:Int))) :
    sqDist t x ≡ sqDist t y [MOD 2^(r+3)] := by
  rw [← Int.natCast_modEq_iff]
  rw [sqDist_cast, sqDist_cast]
  rw [Int.modEq_iff_dvd]
  have hxy_dvd : ((2^r : Nat) : Int) ∣ ((y:Int) - (x:Int)) := by
    simpa using (Nat.modEq_iff_dvd.mp hxy)
  have hprod : ((2^r : Nat) : Int) * 8 ∣ (((y:Int) - (t:Int))^2 - ((x:Int) - (t:Int))^2) := by
    convert mul_dvd_mul hxy_dvd hdiv using 1 <;> ring
  convert hprod using 1
  norm_num [pow_add]

lemma land_mod_two_pow (a M r : Nat) :
    ((a &&& M) % 2^r) = (((a % 2^r) &&& (M % 2^r))) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < r
  · simp [Nat.testBit_mod_two_pow, hi]
  · simp [Nat.testBit_mod_two_pow, hi]

lemma land_congr_mod_two_pow {a b M r : Nat} (h : a ≡ b [MOD 2^r]) :
    (a &&& M) ≡ (b &&& M) [MOD 2^r] := by
  rw [Nat.ModEq]
  rw [land_mod_two_pow a M r, land_mod_two_pow b M r]
  rw [Nat.ModEq] at h
  rw [h]

def Fmask (M t x : Nat) : Nat := sqDist t x &&& M

def iterF (M t : Nat) : Nat -> Nat
| 0 => 0
| n+1 => Fmask M t (iterF M t n)

lemma Fmask_le (M t x : Nat) : Fmask M t x ≤ M := by
  unfold Fmask
  -- use land_le_right from Reduce; reprove minimal
  induction sqDist t x using Nat.binaryRec generalizing M with
  | zero => simp
  | bit abit a ih =>
      cases M using Nat.bitCasesOn with
      | bit bbit b =>
          specialize ih b
          change (Nat.bit abit a &&& Nat.bit bbit b) ≤ Nat.bit bbit b
          rw [Nat.land_bit]
          cases abit <;> cases bbit <;> simp [Nat.bit] <;> omega

lemma iterF_le (M t n : Nat) : iterF M t (n+1) ≤ M := by
  simp [iterF, Fmask_le]

lemma sqDist_div16_of_t4_x16 {t x : Nat} (ht : 4 ∣ t) (hx : 16 ∣ x) : 16 ∣ sqDist t x := by
  have h4x : 4 ∣ x := Nat.dvd_trans (by norm_num : 4 ∣ 16) hx
  unfold sqDist
  by_cases h : x ≤ t
  · simp [h]
    have hdiff : 4 ∣ t - x := Nat.dvd_sub ht h4x
    obtain ⟨c, hc⟩ := hdiff
    use c*c
    rw [hc]
    ring
  · simp [h]
    have hdiff : 4 ∣ x - t := Nat.dvd_sub h4x ht
    obtain ⟨c, hc⟩ := hdiff
    use c*c
    rw [hc]
    ring

lemma land_div_of_div_pow {a M : Nat} (ha : 16 ∣ a) : 16 ∣ (a &&& M) := by
  have hmod : a ≡ 0 [MOD 16] := by
    rw [Nat.ModEq]
    exact Nat.mod_eq_zero_of_dvd ha
  have h := land_congr_mod_two_pow (M:=M) (r:=4) hmod
  rw [Nat.ModEq] at h
  have h0 : (a &&& M) % 16 = 0 := by simpa using h
  exact Nat.dvd_iff_mod_eq_zero.mpr h0

lemma Fmask_div16 {M t x : Nat} (ht : 4 ∣ t) (hx : 16 ∣ x) : 16 ∣ Fmask M t x := by
  unfold Fmask
  exact land_div_of_div_pow (sqDist_div16_of_t4_x16 ht hx)

lemma iterF_div16 {M t : Nat} (ht : 4 ∣ t) : ∀ n, 16 ∣ iterF M t n
| 0 => by simp [iterF]
| n+1 => by
    simp [iterF]
    exact Fmask_div16 ht (iterF_div16 ht n)

lemma Fmask_contraction {M t x y r : Nat} (ht : 4 ∣ t) (hx : 16 ∣ x) (hy : 16 ∣ y)
    (hxy : x ≡ y [MOD 2^r]) : Fmask M t x ≡ Fmask M t y [MOD 2^(r+3)] := by
  unfold Fmask
  apply land_congr_mod_two_pow
  apply sqDist_modEq hxy
  have hx8 : (8 : Int) ∣ (x:Int) := by
    have : (8:Nat) ∣ x := Nat.dvd_trans (by norm_num : 8 ∣ 16) hx
    exact_mod_cast this
  have hy8 : (8 : Int) ∣ (y:Int) := by
    have : (8:Nat) ∣ y := Nat.dvd_trans (by norm_num : 8 ∣ 16) hy
    exact_mod_cast this
  have ht8 : (8 : Int) ∣ 2*(t:Int) := by
    obtain ⟨c, hc⟩ := ht
    use (c : Int)
    rw [hc]
    norm_num
    ring
  exact dvd_sub (dvd_add hx8 hy8) ht8

lemma iterF_congr_step {M t : Nat} (ht : 4 ∣ t) :
    ∀ n, iterF M t (n+1) ≡ iterF M t n [MOD 2^(4+3*n)] := by
  intro n
  induction n with
  | zero =>
      have hdiv : 16 ∣ iterF M t 1 := iterF_div16 ht 1
      rw [Nat.ModEq]
      have h0 : iterF M t 1 % 16 = 0 := Nat.mod_eq_zero_of_dvd hdiv
      simpa using h0
  | succ n ih =>
      have h := Fmask_contraction (M:=M) (t:=t)
        (ht:=ht) (hx:=iterF_div16 ht (n+1)) (hy:=iterF_div16 ht n) ih
      simpa [iterF, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using h

lemma pow_gt_self_mono (M e : Nat) (he : M+1 ≤ e) : M < 2^e := by
  have h1 : M < 2^(M+1) := by
    exact lt_of_lt_of_le (Nat.lt_succ_self M) (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hpow : 2^(M+1) ≤ 2^e := Nat.pow_le_pow_right (by decide) he
  exact lt_of_lt_of_le h1 hpow

lemma iterF_fixed {M t : Nat} (ht : 4 ∣ t) :
    iterF M t (M+2) = iterF M t (M+1) := by
  let e := 4 + 3*(M+1)
  have h := iterF_congr_step (M:=M) (t:=t) ht (M+1)
  have heqpow : 2^(4+3*(M+1)) = 2^e := rfl
  rw [Nat.ModEq] at h
  have hMlt : M < 2^e := by
    apply pow_gt_self_mono
    unfold e
    omega
  have hxlt : iterF M t (M+2) < 2^e := lt_of_le_of_lt (iterF_le M t (M+1)) hMlt
  have hylt : iterF M t (M+1) < 2^e := lt_of_le_of_lt (iterF_le M t M) hMlt
  rw [show 2^(4+3*(M+1)) = 2^e by rfl] at h
  rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at h
  exact h

theorem xor_add_two_land : ∀ a b : Nat, (a ^^^ b) + 2*(a &&& b) = a + b := by
  intro a
  induction a using Nat.binaryRec with
  | zero => intro b; simp
  | bit abit a ih =>
      intro b
      cases b using Nat.bitCasesOn with
      | bit bbit b =>
          specialize ih b
          cases abit <;> cases bbit
          all_goals
            simp only [Nat.xor_bit, Nat.land_bit, Bool.false_eq_true, Bool.true_eq_false,
              Bool.false_bne, Bool.true_bne, Bool.bne_false, Bool.bne_true]
            simp [Nat.bit, ih]
            omega

lemma fixed_extract {M t x : Nat} (hM : M = 2*t+1) (hxM : x ≤ M)
    (hfix : x = Fmask M t x) :
    ∃ k : Nat, Nat.xor (k^2) ((k+1)^2) = M := by
  by_cases hle : x ≤ t
  · refine ⟨t - x, ?_⟩
    have hland : (t - x)^2 &&& M = x := by
      have hf : Fmask M t x = x := hfix.symm
      simpa [Fmask, sqDist, hle] using hf
    have hsum : (t - x) + ((t - x)^2 &&& M) = t := by
      rw [hland]
      omega
    -- use reduction
    let k := t - x
    have hxid := xor_add_two_land (k^2) M
    have hkmask : k^2 &&& M = x := by simpa [k] using hland
    have hsum2 : (k + 1)^2 + 2*((k^2) &&& M) = k^2 + M := by
      rw [hkmask, hM]
      simp [k]
      nlinarith [hle]
    have hx' : (k^2 ^^^ M) = (k+1)^2 := by
      have hx2 : (k^2 ^^^ M) + 2*((k^2)&&&M) = k^2 + M := xor_add_two_land (k^2) M
      exact Nat.add_right_cancel (hx2.trans hsum2.symm)
    change k^2 ^^^ (k+1)^2 = M
    rw [← hx', ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · have hgt : t < x := lt_of_not_ge hle
    refine ⟨x - t - 1, ?_⟩
    let k := x - t - 1
    have hk1 : k + 1 = x - t := by omega
    have hland : (x - t)^2 &&& M = x := by
      have hf : Fmask M t x = x := hfix.symm
      simpa [Fmask, sqDist, hle] using hf
    have hpM : ((k+1)^2 &&& M) = x := by
      rw [hk1]
      exact hland
    have hrel : (k+1)^2 + M = k^2 + 2*x := by
      have hx_eq : x = t + (k + 1) := by omega
      rw [hx_eq, hM]
      ring
    have hx2 : ((k+1)^2 ^^^ M) + 2*x = (k+1)^2 + M := by
      have hxid := xor_add_two_land ((k+1)^2) M
      rw [hpM] at hxid
      exact hxid
    have hx' : ((k+1)^2 ^^^ M) = k^2 := by
      exact Nat.add_right_cancel (hx2.trans hrel)
    change k^2 ^^^ (k+1)^2 = M
    rw [← hx']
    rw [Nat.xor_assoc, Nat.xor_comm M ((k+1)^2), Nat.xor_xor_cancel_left]

lemma four_dvd_two_mul_mul_succ (n : Nat) : 4 ∣ 2*n*(n+1) := by
  have he : Even (n*(n+1)) := by
    exact Nat.even_mul_succ_self n
  rcases he with ⟨c, hc⟩
  use c
  calc
    2*n*(n+1) = 2*(n*(n+1)) := by ring
    _ = 2*(c+c) := by rw [hc]
    _ = 4*c := by ring

example (n : Nat) : ∃ k : Nat, Nat.xor (k ^ 2) ((k + 1) ^ 2) = (2 * n + 1) ^ 2 := by
  let M := (2*n+1)^2
  let t := 2*n*(n+1)
  let x := iterF M t (M+1)
  have ht : 4 ∣ t := by simpa [t] using four_dvd_two_mul_mul_succ n
  have hfix_iter := iterF_fixed (M:=M) (t:=t) ht
  have hfix : x = Fmask M t x := by
    change iterF M t (M+1) = Fmask M t (iterF M t (M+1))
    simpa [iterF] using hfix_iter.symm
  have hxM : x ≤ M := by
    change iterF M t (M+1) ≤ M
    simpa using iterF_le M t M
  have hM : M = 2*t + 1 := by
    simp [M, t]
    ring
  simpa [M] using fixed_extract (M:=M) (t:=t) (x:=x) hM hxM hfix
