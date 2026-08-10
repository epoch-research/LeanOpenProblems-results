import FormalConjectures.Util.ProblemImports

open Nat Finset Int

noncomputable def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)
  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;
    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )

lemma a_pos_of_witness {n x y z w k : ℕ}
    (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n) (hw : w ≤ n)
    (hsum : x^2 + y^2 + z^2 + w^2 = n^2)
    (hzw : z ≤ w)
    (hk : k ≤ n)
    (hpell : (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ)) : a n > 0 := by
  unfold a
  apply Finset.card_pos.mpr
  refine ⟨((x, y), (z, w)), ?_⟩
  simp [Nat.lt_succ_iff, hx, hy, hz, hw, hsum, hzw]
  exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, hpell⟩

lemma pow2_index_add_three_le_ten_mul_pow2 (s : ℕ) : s + 3 ≤ 10 * 2^s := by
  induction s with
  | zero => norm_num
  | succ s ih =>
      have hmono : 10 * 2^s ≤ 10 * 2^s * 2 := by nlinarith [show 0 ≤ 10 * 2^s by positivity]
      have : s + 1 + 3 ≤ 10 * 2^s + 1 := by omega
      calc
        s + 1 + 3 ≤ 10 * 2^s + 1 := this
        _ ≤ 10 * 2^s * 2 := by
          have hp : 1 ≤ 10 * 2^s := by
            have h2 : 1 ≤ 2^s := by exact Nat.one_le_pow s 2 (by norm_num)
            nlinarith
          nlinarith [hmono, hp]
        _ = 10 * 2^(s+1) := by ring

lemma branch104_raw {n s z w : ℕ}
    (hz : z ≤ n) (hw : w ≤ n)
    (hzw : z ≤ w)
    (hxle : 10 * 2^s ≤ n)
    (hyle : 2 * 2^s ≤ n)
    (hsum : (10 * 2^s)^2 + (2 * 2^s)^2 + z^2 + w^2 = n^2) : a n > 0 := by
  refine a_pos_of_witness (n:=n) (x:=10 * 2^s) (y:=2 * 2^s) (z:=z) (w:=w) (k:=s+3)
    hxle hyle hz hw hsum hzw ?_ ?_
  · exact le_trans (pow2_index_add_three_le_ten_mul_pow2 s) hxle
  · have h4 : (4 : ℤ)^(s+3) = (2 : ℤ)^(2*s) * 64 := by
      rw [pow_add, show (4:ℤ)^3 = 64 by norm_num]
      rw [show (4 : ℤ)^s = (2 : ℤ)^(2*s) by
        rw [show (4:ℤ) = 2^2 by norm_num, ← pow_mul]]
    rw [h4]
    norm_num [Nat.cast_mul, Nat.cast_pow]
    ring


lemma pow2_index_add_four_le_thirtyfour_mul_pow2 (s : ℕ) : s + 4 ≤ 34 * 2^s := by
  induction s with
  | zero => norm_num
  | succ s ih =>
      have hmono : 34 * 2^s ≤ 34 * 2^s * 2 := by nlinarith [show 0 ≤ 34 * 2^s by positivity]
      have : s + 1 + 4 ≤ 34 * 2^s + 1 := by omega
      calc
        s + 1 + 4 ≤ 34 * 2^s + 1 := this
        _ ≤ 34 * 2^s * 2 := by
          have hp : 1 ≤ 34 * 2^s := by
            have h2 : 1 ≤ 2^s := by exact Nat.one_le_pow s 2 (by norm_num)
            nlinarith
          nlinarith [hmono, hp]
        _ = 34 * 2^(s+1) := by ring

lemma branch1256_raw {n s z w : ℕ}
    (hz : z ≤ n) (hw : w ≤ n)
    (hzw : z ≤ w)
    (hxle : 34 * 2^s ≤ n)
    (hyle : 10 * 2^s ≤ n)
    (hsum : (34 * 2^s)^2 + (10 * 2^s)^2 + z^2 + w^2 = n^2) : a n > 0 := by
  refine a_pos_of_witness (n:=n) (x:=34 * 2^s) (y:=10 * 2^s) (z:=z) (w:=w) (k:=s+4)
    hxle hyle hz hw hsum hzw ?_ ?_
  · exact le_trans (pow2_index_add_four_le_thirtyfour_mul_pow2 s) hxle
  · have h4 : (4 : ℤ)^(s+4) = (2 : ℤ)^(2*s) * 256 := by
      rw [pow_add, show (4:ℤ)^4 = 256 by norm_num]
      rw [show (4 : ℤ)^s = (2 : ℤ)^(2*s) by
        rw [show (4:ℤ) = 2^2 by norm_num, ← pow_mul]]
    rw [h4]
    norm_num [Nat.cast_mul, Nat.cast_pow]
    ring


lemma pure_branch_raw {n x z w k : ℕ}
    (hx : x ≤ n) (hz : z ≤ n) (hw : w ≤ n)
    (hzw : z ≤ w)
    (hk : k ≤ n)
    (hsum : x^2 + z^2 + w^2 = n^2)
    (hp : x = 2^k) : a n > 0 := by
  refine a_pos_of_witness (n:=n) (x:=x) (y:=0) (z:=z) (w:=w) (k:=k)
    hx (by omega) hz hw ?_ hzw hk ?_
  · simpa [pow_two] using hsum
  · subst x
    norm_num [Nat.cast_pow]
    rw [show (4 : ℤ)^k = (2 : ℤ)^(2*k) by
      rw [show (4:ℤ) = 2^2 by norm_num, ← pow_mul]]
    ring


lemma branch104_scaled {N r s z w : ℕ}
    (hz : z ≤ N) (hw : w ≤ N) (hzw : z ≤ w)
    (hxle : 10 * 2^s ≤ N)
    (hyle : 2 * 2^s ≤ N)
    (hsum : (10 * 2^s)^2 + (2 * 2^s)^2 + z^2 + w^2 = N^2) :
    a (2^r * N) > 0 := by
  have hz' : z * 2^r ≤ 2^r * N := by
    rw [mul_comm (2^r) N]
    exact Nat.mul_le_mul_right _ hz
  have hw' : w * 2^r ≤ 2^r * N := by
    rw [mul_comm (2^r) N]
    exact Nat.mul_le_mul_right _ hw
  have hx' : 10 * 2^(s+r) ≤ 2^r * N := by
    calc
      10 * 2^(s+r) = 2^r * (10 * 2^s) := by rw [pow_add]; ring
      _ ≤ 2^r * N := Nat.mul_le_mul_left _ hxle
  have hy' : 2 * 2^(s+r) ≤ 2^r * N := by
    calc
      2 * 2^(s+r) = 2^r * (2 * 2^s) := by rw [pow_add]; ring
      _ ≤ 2^r * N := Nat.mul_le_mul_left _ hyle
  apply branch104_raw (n:=2^r * N) (s:=s+r) (z:=z*2^r) (w:=w*2^r)
  · exact hz'
  · exact hw'
  · exact Nat.mul_le_mul_right _ hzw
  · exact hx'
  · exact hy'
  · calc
      (10 * 2^(s+r))^2 + (2 * 2^(s+r))^2 + (z * 2^r)^2 + (w * 2^r)^2
          = ((10 * 2^s)^2 + (2 * 2^s)^2 + z^2 + w^2) * (2^r)^2 := by
            rw [pow_add]
            ring
      _ = N^2 * (2^r)^2 := by rw [hsum]
      _ = (2^r * N)^2 := by ring


lemma branch1256_scaled {N r s z w : ℕ}
    (hz : z ≤ N) (hw : w ≤ N) (hzw : z ≤ w)
    (hxle : 34 * 2^s ≤ N)
    (hyle : 10 * 2^s ≤ N)
    (hsum : (34 * 2^s)^2 + (10 * 2^s)^2 + z^2 + w^2 = N^2) :
    a (2^r * N) > 0 := by
  have hz' : z * 2^r ≤ 2^r * N := by
    rw [mul_comm (2^r) N]
    exact Nat.mul_le_mul_right _ hz
  have hw' : w * 2^r ≤ 2^r * N := by
    rw [mul_comm (2^r) N]
    exact Nat.mul_le_mul_right _ hw
  have hx' : 34 * 2^(s+r) ≤ 2^r * N := by
    calc
      34 * 2^(s+r) = 2^r * (34 * 2^s) := by rw [pow_add]; ring
      _ ≤ 2^r * N := Nat.mul_le_mul_left _ hxle
  have hy' : 10 * 2^(s+r) ≤ 2^r * N := by
    calc
      10 * 2^(s+r) = 2^r * (10 * 2^s) := by rw [pow_add]; ring
      _ ≤ 2^r * N := Nat.mul_le_mul_left _ hyle
  apply branch1256_raw (n:=2^r * N) (s:=s+r) (z:=z*2^r) (w:=w*2^r)
  · exact hz'
  · exact hw'
  · exact Nat.mul_le_mul_right _ hzw
  · exact hx'
  · exact hy'
  · calc
      (34 * 2^(s+r))^2 + (10 * 2^(s+r))^2 + (z * 2^r)^2 + (w * 2^r)^2
          = ((34 * 2^s)^2 + (10 * 2^s)^2 + z^2 + w^2) * (2^r)^2 := by
            rw [pow_add]
            ring
      _ = N^2 * (2^r)^2 := by rw [hsum]
      _ = (2^r * N)^2 := by ring

example : a 1 > 0 := by
  exact a_pos_of_witness (n:=1) (x:=1) (y:=0) (z:=0) (w:=0) (k:=0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : a 3 > 0 := by
  exact a_pos_of_witness (n:=3) (x:=1) (y:=0) (z:=2) (w:=2) (k:=0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : a 5 > 0 := by
  exact a_pos_of_witness (n:=5) (x:=4) (y:=0) (z:=0) (w:=3) (k:=2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : a 7 > 0 := by
  exact a_pos_of_witness (n:=7) (x:=2) (y:=0) (z:=3) (w:=6) (k:=1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : a 9 > 0 := by
  exact a_pos_of_witness (n:=9) (x:=1) (y:=0) (z:=4) (w:=8) (k:=0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
