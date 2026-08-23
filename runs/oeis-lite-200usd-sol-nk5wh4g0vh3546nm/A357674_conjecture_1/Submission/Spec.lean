import FormalConjectures.Util.ProblemImports

set_option linter.all false
set_option Elab.async false

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open Nat Finset BigOperators

/--
A357674: $a(n) = \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k} \right)^4 \cdot \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k}^2 \right)^3$.

The terms $\sum_{k = 0}^{2n} \binom{n+k-1}{k}$ and $\sum_{k = 0}^{2n} \binom{n+k-1}{k}^2$ are the summations required.
For $n \ge 1$, the first sum is equal to $\binom{3n}{n}$. We keep the summation structure for fidelity to the OEIS definition, using Finset.sum and Nat.choose.
-/
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3


noncomputable section

section Harmonic
variable {R : Type*} [CommRing R] [Inv R]

private def iv (k : ℕ) : R := (k : R)⁻¹
private def hs (a n : ℕ) : R := ∑ i ∈ range n, iv (R := R) (i+1) ^ a
private def hh (a b n : ℕ) : R := ∑ j ∈ range n, hs (R := R) a j * iv (R := R) (j+1) ^ b
private def hhh (a b c n : ℕ) : R :=
  ∑ k ∈ range n, hh (R := R) a b k * iv (R := R) (k+1) ^ c
private def hhhh (a b c d n : ℕ) : R :=
  ∑ l ∈ range n, hhh (R := R) a b c l * iv (R := R) (l+1)^d


private lemma hs_succ (a n : ℕ) :
    hs (R := R) a (n+1) = hs (R := R) a n + iv (R := R) (n+1)^a := by
  simp only [hs, sum_range_succ]

private lemma hh_succ (a b n : ℕ) :
    hh (R := R) a b (n+1) = hh (R := R) a b n +
      hs (R := R) a n * iv (R := R) (n+1)^b := by
  simp only [hh, sum_range_succ]

private lemma hhh_succ (a b c n : ℕ) :
    hhh (R := R) a b c (n+1) = hhh (R := R) a b c n +
      hh (R := R) a b n * iv (R := R) (n+1)^c := by
  simp only [hhh, sum_range_succ]

private lemma hhhh_succ (a b c d n : ℕ) :
    hhhh (R := R) a b c d (n+1) = hhhh (R := R) a b c d n +
      hhh (R := R) a b c n * iv (R := R) (n+1)^d := by
  simp only [hhhh, sum_range_succ]


private lemma hs_self_sq (a n : ℕ) :
    hs (R := R) a n ^ 2 = 2 * hh (R := R) a a n + hs (R := R) (a+a) n := by
  induction n with
  | zero => simp [hs, hh]
  | succ n ih =>
    rw [hs_succ, hh_succ, hs_succ, pow_add]
    calc
      (hs (R := R) a n + iv (R := R) (n+1)^a)^2 =
          hs (R := R) a n^2 + 2*hs (R := R) a n*iv (R := R) (n+1)^a +
            iv (R := R) (n+1)^a*iv (R := R) (n+1)^a := by ring
      _ = _ := by rw [ih]; ring

private lemma hs_mul_hh_one_two (n : ℕ) :
    hs (R := R) 1 n * hh (R := R) 1 2 n =
      2*hhh (R := R) 1 1 2 n + hhh (R := R) 1 2 1 n +
        hh (R := R) 2 2 n + hh (R := R) 1 3 n := by
  induction n with
  | zero => simp [hs, hh, hhh]
  | succ n ih =>
    rw [hs_succ, hh_succ, hhh_succ, hhh_succ, hh_succ, hh_succ]
    simp only [pow_one]
    have hsq := hs_self_sq (R := R) 1 n
    calc
      (hs (R := R) 1 n + iv (R := R) (n+1)) *
          (hh (R := R) 1 2 n + hs (R := R) 1 n*iv (R := R) (n+1)^2) =
        hs (R := R) 1 n*hh (R := R) 1 2 n +
          hs (R := R) 1 n^2*iv (R := R) (n+1)^2 +
          iv (R := R) (n+1)*hh (R := R) 1 2 n +
          hs (R := R) 1 n*iv (R := R) (n+1)^3 := by ring
      _ = _ := by rw [ih, hsq]; ring


end Harmonic

private lemma pred_lt_of_succ_lt {n p : ℕ} (h : n + 1 < p) : n < p :=
  Nat.lt_trans (Nat.lt_succ_self n) h

private lemma succ_lt_of_lt_pred {k p : ℕ} (hp0 : 0 < p) (h : k < p - 1) : k + 1 < p :=
  Nat.lt_of_le_of_lt (Nat.succ_le_iff.mpr h) (Nat.sub_lt hp0 Nat.one_pos)

private lemma prime_pred_lt {p : ℕ} (hp : p.Prime) : p - 1 < p :=
  Nat.sub_lt hp.pos Nat.one_pos

private lemma q_pow_five (p : ℕ) : ((p : ZMod (p^5))^5)=0 := by
  rw [← Nat.cast_pow]
  simp

section Lift
variable (p : ℕ) [NeZero p]
local notation "R5" => ZMod (p^5)
local notation "q" => (p : R5)

private def red (x : R5) : ZMod p := ZMod.cast x

private def IsBigO (r : ℕ) (x : R5) : Prop := ∃ y : R5, x = q^r * y

private lemma isBigO_one_of_red_eq_zero (x : R5) (hx : red p x = 0) :
    IsBigO p 1 x := by
  rw [red, ZMod.cast_eq_val] at hx
  have hv : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).mp hx
  obtain ⟨y, hy⟩ := hv
  refine ⟨(y : R5), ?_⟩
  simpa using (show x = q * (y : R5) by
    rw [← ZMod.natCast_zmod_val x, hy, Nat.cast_mul])



end Lift

private lemma mul_pow_three_tail {S : Type*} [CommSemiring S] (t a b : S) :
    t^3*(a+t*b)=t^3*a+t^4*b := by
  rw [mul_add]
  congr 1
  rw [show t^4=t^3*t by exact pow_succ t 3]
  ac_rfl

section FiniteHarmonic
variable (p : ℕ) [Fact p.Prime]
local notation "Fp" => ZMod p

private lemma sum_range_cast (f : Fp → Fp) :
    (∑ k ∈ range p, f (k : Fp)) = ∑ x : Fp, f x := by
  have hp : p.Prime := Fact.out
  have h := (ZMod.finEquiv p).sum_comp f
  cases p with
  | zero => exact (by norm_num at hp)
  | succ p =>
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      (∑ i : Fin (p+1), f ((i.val : ℕ) : ZMod (p+1))) =
          ∑ i : Fin (p+1), f ((ZMod.finEquiv (p+1)) i) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 2
            rw [← ZMod.natCast_zmod_val ((ZMod.finEquiv (p+1)) i)]
            rfl
      _ = _ := h


private lemma hs_eq_zero (a : ℕ) (ha0 : 0 < a) (ha : a < p-1) :
    hs (R := Fp) a (p-1) = 0 := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have heq : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  let e : Fp ≃ Fp :=
    { toFun := fun x => x⁻¹
      invFun := fun x => x⁻¹
      left_inv := fun x => inv_inv x
      right_inv := fun x => inv_inv x }
  have hinv : (∑ x : Fp, x⁻¹ ^ a) = ∑ x : Fp, x^a := e.sum_comp (fun x : Fp => x^a)
  have hpow : (∑ x : Fp, x^a) = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (K := Fp) a (by simpa [ZMod.card] using ha)
  have hz : (∑ k ∈ range p, ((k : Fp)⁻¹)^a) = 0 := by
    calc
      (∑ k ∈ range p, ((k : Fp)⁻¹)^a) = ∑ x : Fp, x⁻¹^a :=
        sum_range_cast p (fun x => x⁻¹^a)
      _ = ∑ x : Fp, x^a := hinv
      _ = 0 := hpow
  have hr : range p = range (p-1+1) := congrArg range heq.symm
  rw [hr, sum_range_succ'] at hz
  simp [ha0.ne'] at hz
  simpa [hs, iv] using hz

end FiniteHarmonic

set_option Elab.async false
private lemma reflect_index {p k : ℕ} (_hp2 : 2 ≤ p) (hk : k < p - 1) :
    p - (k + 1) = (p - 1) - 1 - k + 1 := by
  rw [Nat.add_comm k 1, Nat.sub_add_eq]
  calc
    p - 1 - k = (p - 1 - k - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.sub_pos_of_lt hk)).symm
    _ = (p - 1 - 1 - k) + 1 := by rw [Nat.sub_right_comm]

set_option Elab.async false
section HarmonicLift
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)
local notation "Fp" => ZMod p
local notation "q" => (p : R5)

private def rho : R5 →+* Fp := ZMod.castHom (dvd_pow_self p (by decide)) Fp

private lemma unit_cast5 {k : ℕ} (hk0 : 0 < k) (hkp : k < p) : IsUnit (k : R5) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hk0 hkp)).symm.pow_right 5

private lemma rho_iv {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    rho p (iv (R := R5) k) = iv (R := Fp) k := by
  letI : Fact p.Prime := ⟨hp⟩
  have hk : (k : Fp) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hk0 hkp
  apply (mul_right_cancel₀ hk)
  rw [iv, iv, ← show rho p (k : R5) = (k : Fp) by simp [rho], ← map_mul]
  rw [ZMod.inv_mul_of_unit _ (unit_cast5 p hp hk0 hkp), map_one]
  simpa [rho] using (inv_mul_cancel₀ hk).symm

private lemma rho_hs (a : ℕ) :
    rho p (hs (R := R5) a (p-1)) = hs (R := Fp) a (p-1) := by
  simp only [hs, map_sum, map_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  rw [rho_iv p hp (Nat.zero_lt_succ k) (succ_lt_of_lt_pred hp.pos hk)]

private lemma hs_bigO_one (a : ℕ) (ha0 : 0 < a) (ha : a < p-1) :
    IsBigO p 1 (hs (R := R5) a (p-1)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : NeZero p := ⟨hp.ne_zero⟩
  apply isBigO_one_of_red_eq_zero
  rw [show red p (hs (R := R5) a (p-1)) = rho p (hs (R := R5) a (p-1)) by rfl,
    rho_hs p hp, hs_eq_zero p a ha0 ha]


private lemma hs_reverse (a : ℕ) :
    hs (R := R5) a (p-1) =
      ∑ k ∈ range (p-1), iv (R := R5) (p-(k+1))^a  := by
  have hp2 := hp.two_le
  simp only [hs]
  symm
  calc
    (∑ k ∈ range (p-1), iv (R := R5) (p-(k+1))^a) =
        ∑ k ∈ range (p-1), iv (R := R5) ((p-1)-1-k+1)^a := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [mem_range] at hk
      congr 2
      exact reflect_index hp2 hk
    _ = ∑ k ∈ range (p-1), iv (R := R5) (k+1)^a :=
      Finset.sum_range_reflect (fun k => iv (R := R5) (k+1)^a) (p-1)

private lemma iv_reflect {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    iv (R := R5) (p-k) =
      -(iv (R := R5) k + q * iv (R := R5) k^2 + q^2 * iv (R := R5) k^3 +
        q^3 * iv (R := R5) k^4 + q^4 * iv (R := R5) k^5) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hpk0 : 0 < p-k := Nat.sub_pos_of_lt hkp
  have hpkp : p-k < p := Nat.sub_lt hp.pos hk0
  have hu := unit_cast5 p hp hk0 hkp
  have huv := unit_cast5 p hp hpk0 hpkp
  have hk_inv : iv (R := R5) k * (k : R5) = 1 := by
    exact ZMod.inv_mul_of_unit _ hu
  have hq5 : q^5 = 0 := q_pow_five p
  apply (huv.mul_right_cancel)
  rw [iv, ZMod.inv_mul_of_unit _ huv]
  rw [show ((p-k : ℕ) : R5) = q - (k : R5) by rw [Nat.cast_sub (Nat.le_of_lt hkp)]]
  rw [show (-(iv (R := R5) k + q * iv (R := R5) k ^ 2 + q ^ 2 * iv (R := R5) k ^ 3 +
      q ^ 3 * iv (R := R5) k ^ 4 + q ^ 4 * iv (R := R5) k ^ 5)) *
      (q - (k : R5)) = 1 by
        calc
          _ = iv (R := R5) k * (k : R5) - q^5 * iv (R := R5) k^5 := by
            linear_combination (q * iv (R := R5) k + q^2 * iv (R := R5) k^2 +
              q^3 * iv (R := R5) k^3 + q^4 * iv (R := R5) k^4) * hk_inv
          _ = 1 := by simp [hk_inv, hq5]]


private lemma reflect_hs_one :
    2 * hs (R := R5) 1 (p-1) + q * hs (R := R5) 2 (p-1) +
      q^2 * hs (R := R5) 3 (p-1) + q^3 * hs (R := R5) 4 (p-1) +
      q^4 * hs (R := R5) 5 (p-1) = 0 := by
  have hr := hs_reverse p hp 1
  have ht : (∑ k ∈ range (p-1), iv (R := R5) (p-(k+1))^1) =
      ∑ k ∈ range (p-1), -(iv (R := R5) (k+1) + q * iv (R := R5) (k+1)^2 +
        q^2 * iv (R := R5) (k+1)^3 + q^3 * iv (R := R5) (k+1)^4 +
        q^4 * iv (R := R5) (k+1)^5) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    simp only [pow_one]
    rw [iv_reflect p hp (Nat.zero_lt_succ k) (succ_lt_of_lt_pred hp.pos hk)]
  simp only [sum_neg_distrib, sum_add_distrib, ← mul_sum] at ht
  simp only [hs] at hr ⊢
  simp only [pow_one] at hr ht ⊢
  linear_combination hr + ht


private lemma cube_trunc (t x y : R5) :
    (-(x+t*x^2+t^2*y))^3 = -(x^3+3*t*x^4) + t^2 *
      (-(3*x^5+t*x^6+3*(x+t*x^2)^2*y+3*t^2*(x+t*x^2)*y^2+t^4*y^3)) := by
  ring

private lemma reflect_hs_three_short :
    ∃ y : R5, 2 * hs (R := R5) 3 (p-1) + 3*q * hs (R := R5) 4 (p-1) = q^2*y := by
  have hr := hs_reverse p hp 3
  let rem : ℕ → R5 := fun k =>
    let x := iv (R := R5) (k+1);
    -(3*x^5+q*x^6+3*(x+q*x^2)^2*(x^3+q*x^4+q^2*x^5)+
      3*q^2*(x+q*x^2)*(x^3+q*x^4+q^2*x^5)^2+
      q^4*(x^3+q*x^4+q^2*x^5)^3)
  refine ⟨∑ k ∈ range (p-1), rem k, ?_⟩
  have ht : (∑ k ∈ range (p-1), iv (R := R5) (p-(k+1))^3) =
      ∑ k ∈ range (p-1), (-(iv (R := R5) (k+1)^3 +
        3*q*iv (R := R5) (k+1)^4) + q^2*rem k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [iv_reflect p hp (Nat.zero_lt_succ k) (succ_lt_of_lt_pred hp.pos hk)]
    let x : R5 := iv (R := R5) (k+1)
    change (-(x+q*x^2+q^2*x^3+q^3*x^4+q^4*x^5))^3 =
      -(x^3+3*q*x^4)+q^2*rem k
    rw [show x+q*x^2+q^2*x^3+q^3*x^4+q^4*x^5 =
      x+q*x^2+q^2*(x^3+q*x^4+q^2*x^5) by ring]
    dsimp [rem]

    exact cube_trunc p hp q x (x^3+q*x^4+q^2*x^5)
  simp only [sum_add_distrib, sum_neg_distrib, ← mul_sum] at ht
  simp only [hs] at hr ⊢
  linear_combination hr + ht

end HarmonicLift
set_option Elab.async false
set_option Elab.async false

set_option Elab.async false
set_option Elab.async true
section Alternating
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)

private def alt (r n : ℕ) : R5 :=
  ∑ k ∈ range n, (-1 : R5)^k * (n.choose (k+1) : R5) * iv (R := R5) (k+1)^r

private lemma alternating_choose_tail (n : ℕ) :
    (∑ k ∈ range (n+1), (-1 : R5)^k * ((n+1).choose (k+1) : R5)) = 1 := by
  have hz := Int.alternating_sum_range_choose_eq_choose (n := n) (m := n+1)
  have hz0 : (∑ k ∈ range (n+2), ((-1)^k * (n+1).choose k : ℤ)) = 0 := by
    simpa using hz
  have hm0 := congr_arg (fun z : ℤ => (z : R5)) hz0
  have hm : (∑ k ∈ range (n+2), (-1 : R5)^k * ((n+1).choose k : R5)) = 0 := by
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, Int.cast_zero] using hm0
  rw [show n+2 = (n+1)+1 by simp [Nat.add_assoc], sum_range_succ'] at hm
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul] at hm

  have heq : (∑ x ∈ range (n+1), (-1 : R5)^(x+1) * ((n+1).choose (x+1) : R5)) =
      -(∑ x ∈ range (n+1), (-1 : R5)^x * ((n+1).choose (x+1) : R5)) := by
    rw [← sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      (-1 : R5)^(k+1) * ((n+1).choose (k+1) : R5) =
          ((-1 : R5)^k * (-1)) * ((n+1).choose (k+1) : R5) :=
        congrArg (fun z : R5 => z * ((n+1).choose (k+1) : R5)) (pow_succ (-1 : R5) k)
      _ = _ := by rw [mul_neg_one, neg_mul]
  rw [heq] at hm
  linear_combination -hm


private lemma choose_iv_swap {n k : ℕ} (hk : k ≤ n) (hn : n+1 < p) :
    (n.choose k : R5) * iv (R := R5) (k+1) =
      ((n+1).choose (k+1) : R5) * iv (R := R5) (n+1) := by
  have huk := unit_cast5 p hp (Nat.zero_lt_succ k)
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right hk 1) hn)
  have hun := unit_cast5 p hp (Nat.zero_lt_succ n) hn
  have hik : iv (R := R5) (k+1) * ((k+1 : ℕ) : R5) = 1 := by
    simpa [iv] using ZMod.inv_mul_of_unit ((k+1 : ℕ) : R5) huk
  have hin : iv (R := R5) (n+1) * ((n+1 : ℕ) : R5) = 1 := by
    simpa [iv] using ZMod.inv_mul_of_unit ((n+1 : ℕ) : R5) hun
  have hc := congr_arg (fun x : ℕ => (x : R5)) (Nat.add_one_mul_choose_eq n k)
  push_cast at hc
  push_cast at hik hin

  linear_combination (iv (R := R5) (k+1) * iv (R := R5) (n+1)) * hc -
    ((n.choose k : R5) * iv (R := R5) (k+1)) * hin +
    (((n+1).choose (k+1) : R5) * iv (R := R5) (n+1)) * hik

private lemma alt_succ_expand (r n : ℕ) :
    alt p r (n+1) = alt p r n +
      ∑ k ∈ range (n+1), (-1 : R5)^k * (n.choose k : R5) * iv (R := R5) (k+1)^r := by
  simp only [alt, sum_range_succ, Nat.choose_succ_succ, Nat.cast_add]
  simp_rw [mul_add, add_mul]
  rw [sum_add_distrib]
  simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, zero_add,
    Nat.choose_self, Nat.cast_one, mul_one]
  ring

private lemma alt_one_succ {n : ℕ} (hn : n+1 < p) :
    alt p 1 (n+1) = alt p 1 n + iv (R := R5) (n+1) := by
  rw [alt_succ_expand p hp]
  congr 1
  calc
    (∑ k ∈ range (n+1), (-1 : R5)^k * (n.choose k : R5) *
        iv (R := R5) (k+1)^1) =
      iv (R := R5) (n+1) *
        ∑ k ∈ range (n+1), (-1 : R5)^k * ((n+1).choose (k+1) : R5) := by
          rw [mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [mem_range] at hk
          simp only [pow_one]
          have hc := choose_iv_swap p hp (k := k) (n := n) (Nat.lt_succ_iff.mp hk) hn
          calc
            (-1 : R5)^k * (n.choose k : R5) * iv (R := R5) (k+1) =
                (-1 : R5)^k * ((n.choose k : R5) * iv (R := R5) (k+1)) := by ac_rfl
            _ = (-1 : R5)^k * (((n+1).choose (k+1) : R5) * iv (R := R5) (n+1)) := by rw [hc]
            _ = _ := by ac_rfl
    _ = iv (R := R5) (n+1) := by rw [alternating_choose_tail p hp, mul_one]

private lemma alt_two_succ {n : ℕ} (hn : n+1 < p) :
    alt p 2 (n+1) = alt p 2 n + iv (R := R5) (n+1) * alt p 1 (n+1) := by
  rw [alt_succ_expand p hp]
  congr 1
  rw [alt]
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  simp only [pow_one]
  have hc := choose_iv_swap p hp (k := k) (n := n) (Nat.lt_succ_iff.mp hk) hn
  calc
    (-1 : R5)^k * (n.choose k : R5) * iv (R := R5) (k+1)^2 =
      (-1 : R5)^k * ((n.choose k : R5) * iv (R := R5) (k+1)) *
        iv (R := R5) (k+1) := by
          rw [pow_two]
          ac_rfl
    _ = (-1 : R5)^k * (((n+1).choose (k+1) : R5) * iv (R := R5) (n+1)) *
        iv (R := R5) (k+1) := by rw [hc]
    _ = _ := by ac_rfl

private lemma alt_one_eq_hs {n : ℕ} (hn : n < p) :
    alt p 1 n = hs (R := R5) 1 n := by
  induction n with
  | zero => simp [alt, hs]
  | succ n ih =>
    rw [alt_one_succ p hp hn, ih (pred_lt_of_succ_lt hn), hs_succ]
    simp only [pow_one]

private lemma two_mul_alt_two {n : ℕ} (hn : n < p) :
    2 * alt p 2 n = hs (R := R5) 1 n ^ 2 + hs (R := R5) 2 n := by
  induction n with
  | zero => simp [alt, hs]
  | succ n ih =>
    rw [alt_two_succ p hp hn, alt_one_eq_hs p hp hn, hs_succ, hs_succ]
    simp only [pow_one]
    have hi := ih (pred_lt_of_succ_lt hn)
    calc
      2 * (alt p 2 n + iv (R := R5) (n+1) *
          (hs (R := R5) 1 n + iv (R := R5) (n+1))) =
        2 * alt p 2 n + 2 * iv (R := R5) (n+1) * hs (R := R5) 1 n +
          2 * iv (R := R5) (n+1)^2 := by ring
      _ = _ := by rw [hi]; ring


end Alternating
set_option Elab.async false
set_option Elab.async false


section BinomialExpansion
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)
local notation "q" => (p : R5)

private def pm (n : ℕ) : R5 :=
  ∏ k ∈ range n, (1 - q * iv (R := R5) (k+1))

private lemma pm_succ (n : ℕ) :
    pm p (n+1) = pm p n * (1-q*iv (R := R5) (n+1)) := by
  unfold pm
  rw [prod_range_succ]

set_option Elab.async false
private lemma pm_trunc_step (A E z x : R5) :
    (1-q*A+q^2*E+q^3*z)*(1-q*x) =
      1-q*(A+x)+q^2*(E+A*x)+q^3*(z-E*x-q*z*x) := by ring

private lemma pm_trunc (n : ℕ) :
    ∃ z : R5, pm p n = 1-q*hs (R := R5) 1 n+q^2*hh (R := R5) 1 1 n+q^3*z := by
  induction n with
  | zero => exact ⟨0, by simp [pm, hs, hh]⟩
  | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨z-hh (R := R5) 1 1 n*iv (R := R5) (n+1)-
        q*z*iv (R := R5) (n+1), ?_⟩
      rw [pm_succ p hp, hz, hs_succ, hh_succ]
      simp only [pow_one]
      exact pm_trunc_step p hp (hs (R := R5) 1 n) (hh (R := R5) 1 1 n) z
        (iv (R := R5) (n+1))

private lemma signed_choose_succ {k : ℕ} (hk : k+1 < p) :
    (-1 : R5)^(k+1) * ((p-1).choose (k+1) : R5) =
      (-1 : R5)^k * ((p-1).choose k : R5) *
        (1-q*iv (R := R5) (k+1)) := by
  have hu := unit_cast5 p hp (Nat.zero_lt_succ k) hk
  have hik : iv (R := R5) (k+1) * ((k+1 : ℕ) : R5) = 1 := by
    simpa [iv] using ZMod.inv_mul_of_unit ((k+1 : ℕ) : R5) hu
  have hc0 := Nat.choose_succ_right_eq (p-1) k
  have heq : p-1-k = p-(k+1) := by simpa [Nat.add_comm] using Nat.sub_sub p 1 k
  rw [heq] at hc0
  have hc := congr_arg (fun x : ℕ => (x : R5)) hc0
  push_cast at hc hik
  rw [Nat.cast_sub (Nat.le_of_lt hk)] at hc
  push_cast at hc

  apply hu.mul_right_cancel
  push_cast

  calc
    ((-1 : R5)^(k+1) * ((p-1).choose (k+1) : R5)) * ((k : R5)+1) =
      (-1 : R5)^(k+1) * (((p-1).choose (k+1) : R5) * ((k : R5)+1)) := by ac_rfl
    _ = (-1 : R5)^(k+1) * (((p-1).choose k : R5) * (q-((k : R5)+1))) := by rw [hc]
    _ = ((-1 : R5)^k * ((p-1).choose k : R5) *
        (1-q*iv (R := R5) (k+1))) * ((k : R5)+1) := by
          rw [pow_succ]
          linear_combination ((-1 : R5)^k * ((p-1).choose k : R5) * q) * hik

private lemma signed_choose_eq_pm {k : ℕ} (hk : k < p) :
    (-1 : R5)^k * ((p-1).choose k : R5) = pm p k := by
  induction k with
  | zero => simp [pm]
  | succ k ih =>
    rw [signed_choose_succ p hp hk, ih (pred_lt_of_succ_lt hk), pm_succ p hp]

private lemma sum_prefix_mul (x f g F G : ℕ → R5)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hf : ∀ n, f (n+1) = f n + g n*x n)
    (hF : ∀ n, F (n+1) = F n + f n*x n^2)
    (hG : ∀ n, G (n+1) = G n + g n*x n^3) (n : ℕ) :
    (∑ k ∈ range n, f (k+1)*x k^2) = F n+G n := by
  induction n with
  | zero => simp [hF0, hG0]
  | succ n ih =>
    rw [sum_range_succ, hf, hF, hG, ih]
    ring

private lemma sum_hs_succ_mul (n : ℕ) :
    (∑ k ∈ range n, hs (R := R5) 1 (k+1) * iv (R := R5) (k+1)^2) =
      hh (R := R5) 1 2 n + hs (R := R5) 3 n := by
  apply sum_prefix_mul p hp (fun k => iv (R := R5) (k+1))
    (fun k => hs (R := R5) 1 k) (fun _ => 1)
    (fun k => hh (R := R5) 1 2 k) (fun k => hs (R := R5) 3 k)
  · simp [hh]
  · simp [hs]
  · intro k; simpa only [one_mul, pow_one] using hs_succ (R := R5) 1 k
  · intro k; exact hh_succ (R := R5) 1 2 k
  · intro k; simpa only [one_mul] using hs_succ (R := R5) 3 k

private lemma sum_hh_succ_mul (n : ℕ) :
    (∑ k ∈ range n, hh (R := R5) 1 1 (k+1) * iv (R := R5) (k+1)^2) =
      hhh (R := R5) 1 1 2 n + hh (R := R5) 1 3 n := by
  apply sum_prefix_mul p hp (fun k => iv (R := R5) (k+1))
    (fun k => hh (R := R5) 1 1 k) (fun k => hs (R := R5) 1 k)
    (fun k => hhh (R := R5) 1 1 2 k) (fun k => hh (R := R5) 1 3 k)
  · simp [hhh]
  · simp [hh]
  · intro k; simpa only [pow_one] using hh_succ (R := R5) 1 1 k
  · intro k; exact hhh_succ (R := R5) 1 1 2 k
  · intro k; exact hh_succ (R := R5) 1 3 k

set_option Elab.async false
private lemma alt_two_trunc :
    ∃ T : R5, alt p 2 (p-1) =
      -hs (R := R5) 2 (p-1)+
      q*(hh (R := R5) 1 2 (p-1)+hs (R := R5) 3 (p-1))-
      q^2*(hhh (R := R5) 1 1 2 (p-1)+hh (R := R5) 1 3 (p-1))+q^3*T := by
  let rem : ℕ → R5 := fun k => Classical.choose (pm_trunc p hp (k+1))
  refine ⟨∑ k ∈ range (p-1),
    -(rem k)*iv (R := R5) (k+1)^2, ?_⟩
  rw [alt]
  have ht : (∑ k ∈ range (p-1), (-1 : R5)^k * ((p-1).choose (k+1) : R5) *
      iv (R := R5) (k+1)^2) =
      ∑ k ∈ range (p-1), -(pm p (k+1))*iv (R := R5) (k+1)^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have hc := signed_choose_eq_pm p hp (k := k+1) (succ_lt_of_lt_pred hp.pos hk)
    calc
      (-1 : R5)^k*((p-1).choose (k+1) : R5)*iv (R := R5) (k+1)^2 =
        -((-1 : R5)^(k+1)*((p-1).choose (k+1) : R5))*
          iv (R := R5) (k+1)^2 := by rw [pow_succ]; ring
      _ = _ := by rw [hc]
  rw [ht]
  have he : (∑ k ∈ range (p-1), -(pm p (k+1))*iv (R := R5) (k+1)^2) =
      ∑ k ∈ range (p-1), (-iv (R := R5) (k+1)^2+
        q*(hs (R := R5) 1 (k+1)*iv (R := R5) (k+1)^2)-
        q^2*(hh (R := R5) 1 1 (k+1)*iv (R := R5) (k+1)^2)+
        q^3*(-rem k*iv (R := R5) (k+1)^2)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hz := Classical.choose_spec (pm_trunc p hp (k+1))
    change pm p (k+1) = 1-q*hs (R := R5) 1 (k+1)+
      q^2*hh (R := R5) 1 1 (k+1)+q^3*rem k at hz
    rw [hz]
    ring
  rw [he]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_neg_distrib]
  rw [sum_hs_succ_mul p hp, sum_hh_succ_mul p hp]
  simp only [hs]


end BinomialExpansion



section PositiveProducts
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)
local notation "q" => (p : R5)

private def pp (c : R5) (n : ℕ) : R5 :=
  ∏ k ∈ range n, (1 + c*q*iv (R := R5) (k+1))

omit hp
private lemma pp_succ (c : R5) (n : ℕ) :
    pp p c (n+1) = pp p c n * (1+c*q*iv (R := R5) (n+1)) := by
  unfold pp
  rw [prod_range_succ]

private lemma pp_step (c A E J L x : R5) (hq : q^5=0) :
    (1+c*q*A+c^2*q^2*E+c^3*q^3*J+c^4*q^4*L)*(1+c*q*x) =
      1+c*q*(A+x)+c^2*q^2*(E+A*x)+c^3*q^3*(J+E*x)+c^4*q^4*(L+J*x) := by
  calc
    (1+c*q*A+c^2*q^2*E+c^3*q^3*J+c^4*q^4*L)*(1+c*q*x) =
      (1+c*q*(A+x)+c^2*q^2*(E+A*x)+c^3*q^3*(J+E*x)+c^4*q^4*(L+J*x))+
        c^5*q^5*L*x := by ring
    _ = _ := by simp only [hq, mul_zero, zero_mul, add_zero]

private lemma pp_expansion (c : R5) (n : ℕ) :
    pp p c n = 1 + c*q*hs (R := R5) 1 n + c^2*q^2*hh (R := R5) 1 1 n +
      c^3*q^3*hhh (R := R5) 1 1 1 n + c^4*q^4*hhhh (R := R5) 1 1 1 1 n := by
  induction n with
  | zero => simp [pp, hs, hh, hhh, hhhh]
  | succ n ih =>
    rw [pp_succ p, ih, hs_succ, hh_succ, hhh_succ, hhhh_succ]
    simp only [pow_one]
    have hq5 : q^5 = 0 := q_pow_five p
    exact pp_step p c (hs (R := R5) 1 n) (hh (R := R5) 1 1 n)
      (hhh (R := R5) 1 1 1 n) (hhhh (R := R5) 1 1 1 1 n)
      (iv (R := R5) (n+1)) hq5


include hp
private lemma choose_cp_succ (c k : ℕ) (hk : k+1 < p) :
    ((c*p+k+1).choose (k+1) : R5) =
      ((c*p+k).choose k : R5) * (1+(c:R5)*q*iv (R := R5) (k+1)) := by
  have hu := unit_cast5 p hp (Nat.zero_lt_succ k) hk
  have hik : iv (R := R5) (k+1) * ((k+1 : ℕ) : R5) = 1 := by
    simpa [iv] using ZMod.inv_mul_of_unit ((k+1 : ℕ) : R5) hu
  have hc0 := Nat.add_one_mul_choose_eq (c*p+k) k
  have hc := congr_arg (fun x : ℕ => (x : R5)) hc0
  push_cast at hc hik
  apply hu.mul_right_cancel
  push_cast
  calc
    ((c*p+k+1).choose (k+1) : R5) * ((k:R5)+1) =
        (((c:R5)*q+(k:R5))+1) * ((c*p+k).choose k : R5) := by
          rw [← hc]
    _ = (((c*p+k).choose k : R5) * (1+(c:R5)*q*iv (R := R5) (k+1))) *
        ((k:R5)+1) := by
          linear_combination -(((c*p+k).choose k : R5) * (c:R5) * q) * hik

private lemma choose_cp_eq_pp (c : ℕ) {k : ℕ} (hk : k < p) :
    ((c*p+k).choose k : R5) = pp p (c:R5) k := by
  induction k with
  | zero => simp [pp]
  | succ k ih =>
    rw [show c*p+(k+1) = c*p+k+1 by exact (Nat.add_assoc (c*p) k 1).symm]
    rw [choose_cp_succ p hp c k hk, ih (pred_lt_of_succ_lt hk), pp_succ p]

end PositiveProducts


private lemma pred_succ_eq {r : ℕ} (hr : 0 < r) : r - 1 + 1 = r :=
  Nat.sub_add_cancel hr

private lemma add_pred_eq (a : ℕ) {r : ℕ} (hr : 0 < r) : a + r - 1 = a + (r - 1) :=
  Nat.add_sub_assoc hr a

private lemma add_pred_sub_pred (a : ℕ) {r : ℕ} (hr : 0 < r) :
    a + r - 1 - (r - 1) = a := by
  rw [add_pred_eq a hr, Nat.add_sub_cancel_right]

private lemma add_pred_sub (a r : ℕ) : a + r - 1 - r = a - 1 := by
  cases r with
  | zero => simp
  | succ r =>
    rw [show a + (r+1) - 1 = a+r by
      rw [← Nat.add_assoc, Nat.add_sub_cancel]]
    rw [Nat.add_comm a r]
    exact Nat.add_sub_add_left r a 1

section Terms
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)
local notation "q" => (p : R5)

private lemma first_block {r : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    ((p+r-1).choose r : R5) =
      q * iv (R := R5) r * pp p 1 (r-1) := by
  have hu := unit_cast5 p hp hr0 hrp
  have hir : iv (R := R5) r * (r : R5) = 1 := by
    simpa [iv] using ZMod.inv_mul_of_unit (r : R5) hu
  have hc0 := Nat.choose_succ_right_eq (p+r-1) (r-1)
  have hs1 : r-1+1 = r := pred_succ_eq hr0
  have hs2 : p+r-1-(r-1) = p := add_pred_sub_pred p hr0
  rw [hs1, hs2] at hc0
  have hc := congr_arg (fun x : ℕ => (x : R5)) hc0
  push_cast at hc
  have hlower : (((p+r-1).choose (r-1) : ℕ) : R5) = pp p 1 (r-1) := by
    rw [show p+r-1 = 1*p+(r-1) by simpa using add_pred_eq p hr0]
    simpa using choose_cp_eq_pp p hp 1 (k := r-1) (Nat.lt_of_le_of_lt (Nat.sub_le r 1) hrp)
  apply hu.mul_right_cancel
  push_cast
  calc
    ((p+r-1).choose r : R5) * (r:R5) = q * ((p+r-1).choose (r-1) : R5) := by simpa [mul_comm] using hc
    _ = (q * iv (R := R5) r * pp p 1 (r-1)) * (r:R5) := by
      rw [hlower]
      linear_combination -(q * pp p 1 (r-1)) * hir


omit hp
private lemma pp_isUnit (c : R5) (n : ℕ) : IsUnit (pp p c n) := by
  induction n with
  | zero => simp [pp]
  | succ n ih =>
    rw [pp_succ p]
    apply ih.mul
    apply IsNilpotent.isUnit_one_add
    refine ⟨5, ?_⟩
    have hq5 : q^5 = 0 := q_pow_five p
    rw [mul_assoc, mul_pow, mul_pow, hq5]
    simp



include hp
private def bb (r : ℕ) : R5 := ((2*p+r-1).choose (p+r) : R5)

private def bApprox (r : ℕ) : R5 :=
  let L := hs (R := R5) 1 (p-1) + hs (R := R5) 1 (r-1) - iv (R := R5) r
  4*q^2*iv (R := R5) r^2 * (1+2*q*L+q^2*(2*L^2-hs (R := R5) 2 (p-1)-
    3*hs (R := R5) 2 (r-1)+iv (R := R5) r^2))

set_option Elab.async false
set_option Elab.async true
private lemma bb_mul_pp {r : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    bb p r * pp p 1 r =
      2*q*iv (R := R5) r * pp p 1 (p-1) * pp p 2 (r-1) := by
  have hu := unit_cast5 p hp hr0 hrp
  have hir : iv (R := R5) r * (r : R5) = 1 := by
    simpa [iv] using ZMod.inv_mul_of_unit (r : R5) hu
  have hpr : pp p 1 r = ((p+r).choose r : R5) := by
    simpa using (choose_cp_eq_pp p hp 1 (k := r) hrp).symm
  have hpa : pp p 1 (p-1) = ((2*p-1).choose (p-1) : R5) := by
    have h := (choose_cp_eq_pp p hp 1 (k := p-1) (prime_pred_lt hp)).symm
    rw [show 1*p+(p-1)=2*p-1 by simpa [two_mul] using (add_pred_eq p hp.pos).symm] at h
    simpa only [Nat.cast_one] using h
  have hp2 : pp p 2 (r-1) = ((2*p+r-1).choose (r-1) : R5) := by
    simpa [show 2*p+(r-1)=2*p+r-1 by exact (add_pred_eq (2*p) hr0).symm] using
      (choose_cp_eq_pp p hp 2 (k := r-1) (Nat.lt_of_le_of_lt (Nat.sub_le r 1) hrp)).symm
  have hmul := Nat.choose_mul (n := 2*p+r-1) (k := p+r) (s := r) (Nat.le_add_left r p)
  have hsym : (2*p-1).choose p = (2*p-1).choose (p-1) := by
    have hp_le : p ≤ 2*p-1 := by
      rw [show 2*p-1=p+(p-1) by simpa [two_mul] using add_pred_eq p hp.pos]
      exact Nat.le_add_right p (p-1)
    have h := Nat.choose_symm hp_le
    rw [show 2*p-1-p=p-1 by simpa [two_mul, add_pred_eq p hp.pos] using Nat.add_sub_cancel_left p (p-1)] at h
    exact h.symm
  have hprod : bb p r * ((p+r).choose r : R5) =
      ((2*p+r-1).choose r : R5) * ((2*p-1).choose (p-1) : R5) := by
    have hm := congr_arg (fun n : ℕ => (n : R5)) hmul
    simp only [bb]
    simp only [Nat.cast_mul] at hm
    rw [show 2*p+r-1-r=2*p-1 by exact add_pred_sub (2*p) r,
      show p+r-r=p by exact Nat.add_sub_cancel_right p r, hsym] at hm
    exact hm
  have hratio := Nat.choose_succ_right_eq (2*p+r-1) (r-1)
  have hratio' : ((2*p+r-1).choose r : R5) * (r : R5) =
      ((2*p+r-1).choose (r-1) : R5) * (2*q) := by
    rw [show r-1+1=r by exact pred_succ_eq hr0, show 2*p+r-1-(r-1)=2*p by exact add_pred_sub_pred (2*p) hr0] at hratio
    have h := congr_arg (fun n : ℕ => (n : R5)) hratio
    simp only [Nat.cast_mul] at h
    simpa using h
  apply hu.mul_right_cancel
  rw [hpr, hpa, hp2, hprod]
  rw [show ((2*p+r-1).choose r : R5) * ((2*p-1).choose (p-1) : R5) * (r:R5) =
      (((2*p+r-1).choose r : R5) * (r:R5)) * ((2*p-1).choose (p-1) : R5) by ac_rfl,
    hratio', show (2*q*iv (R := R5) r * ((2*p-1).choose (p-1) : R5) *
      ((2*p+r-1).choose (r-1) : R5)) * (r:R5) =
      2*q*((2*p-1).choose (p-1) : R5)*((2*p+r-1).choose (r-1) : R5) *
        (iv (R := R5) r*(r:R5)) by ac_rfl,
    hir]
  rw [mul_one]
  ac_rfl

omit hp
set_option Elab.async false
private lemma q2_low_mul (A B C D : R5) (hq : q^5 = 0) :
    q^2*(1+q*A+q^2*B)*(1+q*C+q^2*D) =
      q^2*(1+q*(A+C)+q^2*(B+D+A*C)) := by
  calc
    q^2*(1+q*A+q^2*B)*(1+q*C+q^2*D) =
      q^2*(1+q*(A+C)+q^2*(B+D+A*C)) + q^5*(A*D+B*C+q*B*D) := by ring
    _ = q^2*(1+q*(A+C)+q^2*(B+D+A*C)) := by
      rw [hq, zero_mul, add_zero]

set_option Elab.async false
private lemma q2_sq_trunc (A B T : R5) (hq : q^5 = 0) :
    q^2*(1+q*A+q^2*B+q^3*T)^2 = q^2*(1+2*q*A+q^2*(A^2+2*B)) := by
  calc
    q^2*(1+q*A+q^2*B+q^3*T)^2 = q^2*(1+2*q*A+q^2*(A^2+2*B))+
      q^5*(2*A*B+2*A*T*q+B^2*q+2*B*T*q^2+T^2*q^3+2*T) := by ring
    _ = q^2*(1+2*q*A+q^2*(A^2+2*B)) := by rw [hq, zero_mul, add_zero]

private lemma q2_assoc (X Y : R5) : q^2*X*Y = X*(q^2*Y) := by ac_rfl
private lemma q2_swap (X Y : R5) : X*(q^2*Y) = Y*(q^2*X) := by ac_rfl
private lemma q2_plain (X Y : R5) : X*(q^2*Y) = q^2*Y*X := by ac_rfl

set_option Elab.async false
set_option Elab.async true
private lemma three_factor_trunc
    (A1 A2 P1 P2 PT U1 U2 UT V1 V2 VT : R5)
    (hq : q^5=0)
    (h1 : A1+2*P1=2*U1+2*V1)
    (h2 : A2+P1^2+2*P2+2*A1*P1 =
      U1^2+2*U2+V1^2+2*V2+4*U1*V1) :
    q^2*(1+q*A1+q^2*A2)*(1+q*P1+q^2*P2+q^3*PT)^2 =
      q^2*(1+q*U1+q^2*U2+q^3*UT)^2*
        (1+q*V1+q^2*V2+q^3*VT)^2 := by
  have hP := q2_sq_trunc p P1 P2 PT hq
  have hU := q2_sq_trunc p U1 U2 UT hq
  have hV := q2_sq_trunc p V1 V2 VT hq
  have hc : q^2*(1+q*A1+q^2*A2)*(1+2*q*P1+q^2*(P1^2+2*P2)) =
      q^2*(1+2*q*U1+q^2*(U1^2+2*U2))*(1+2*q*V1+q^2*(V1^2+2*V2)) := by
    calc
      q^2*(1+q*A1+q^2*A2)*(1+2*q*P1+q^2*(P1^2+2*P2)) =
        q^2*(1+q*A1+q^2*A2)*(1+q*(2*P1)+q^2*(P1^2+2*P2)) := by
          congr 2
          ac_rfl
      _ = q^2*(1+q*(A1+2*P1)+q^2*(A2+(P1^2+2*P2)+A1*(2*P1))) :=
          q2_low_mul p A1 A2 (2*P1) (P1^2+2*P2) hq
      _ = q^2*(1+q*(2*U1+2*V1)+
          q^2*((U1^2+2*U2)+(V1^2+2*V2)+(2*U1)*(2*V1))) := by
        rw [h1]
        congr 3
        linear_combination h2
      _ = q^2*(1+q*(2*U1)+q^2*(U1^2+2*U2))*
          (1+q*(2*V1)+q^2*(V1^2+2*V2)) :=
        (q2_low_mul p (2*U1) (U1^2+2*U2) (2*V1) (V1^2+2*V2) hq).symm
      _ = q^2*(1+2*q*U1+q^2*(U1^2+2*U2))*(1+2*q*V1+q^2*(V1^2+2*V2)) := by
        rw [show q*(2*U1)=2*q*U1 by ac_rfl, show q*(2*V1)=2*q*V1 by ac_rfl]
  calc
    q^2*(1+q*A1+q^2*A2)*(1+q*P1+q^2*P2+q^3*PT)^2 =
      (1+q*A1+q^2*A2)*(q^2*(1+q*P1+q^2*P2+q^3*PT)^2) :=
        q2_assoc p _ _
    _ = (1+q*A1+q^2*A2)*(q^2*(1+2*q*P1+q^2*(P1^2+2*P2))) := by rw [hP]
    _ = q^2*(1+q*A1+q^2*A2)*(1+2*q*P1+q^2*(P1^2+2*P2)) :=
      (q2_assoc p _ _).symm
    _ = q^2*(1+2*q*U1+q^2*(U1^2+2*U2))*(1+2*q*V1+q^2*(V1^2+2*V2)) := hc
    _ = (1+2*q*U1+q^2*(U1^2+2*U2))*(q^2*(1+2*q*V1+q^2*(V1^2+2*V2))) :=
      q2_assoc p _ _
    _ = (1+2*q*U1+q^2*(U1^2+2*U2))*
        (q^2*(1+q*V1+q^2*V2+q^3*VT)^2) := by rw [← hV]
    _ = (1+q*V1+q^2*V2+q^3*VT)^2*
        (q^2*(1+2*q*U1+q^2*(U1^2+2*U2))) := q2_swap p _ _
    _ = (1+q*V1+q^2*V2+q^3*VT)^2*
        (q^2*(1+q*U1+q^2*U2+q^3*UT)^2) := by rw [← hU]
    _ = q^2*(1+q*U1+q^2*U2+q^3*UT)^2*
        (1+q*V1+q^2*V2+q^3*VT)^2 := q2_plain p _ _

private lemma move_four (x A P : R5) :
    4*q^2*x^2*A*P^2 = 4*x^2*(q^2*A*P^2) := by ac_rfl

private lemma finish_four (x U V : R5) :
    4*x^2*(q^2*U^2*V^2) = (2*q*x*U*V)^2 := by
  simp only [mul_pow]
  norm_num
  ac_rfl

private lemma bb_direct_algebra (H H2 E a b e x u3 u4 v3 v4 w3 w4 : R5)
    (hq : q^5 = 0) (hH : H^2 = 2*E+H2) (ha : a^2 = 2*e+b) :
    4*q^2*x^2*(1+2*q*(H+a-x)+
        q^2*(2*(H+a-x)^2-H2-3*b+x^2)) *
      (1+q*(a+x)+q^2*(e+a*x)+q^3*u3+q^4*u4)^2 =
    (2*q*x*(1+q*H+q^2*E+q^3*v3+q^4*v4)*
      (1+2*q*a+4*q^2*e+8*q^3*w3+16*q^4*w4))^2 := by
  have h1 : 2*(H+a-x)+2*(a+x)=2*H+2*(2*a) := by ring
  have h2 : (2*(H+a-x)^2-H2-3*b+x^2)+(a+x)^2+2*(e+a*x)+
      2*(2*(H+a-x))*(a+x) = H^2+2*E+(2*a)^2+2*(4*e)+4*H*(2*a) := by
    linear_combination hH + 3*ha
  have h := three_factor_trunc p
    (2*(H+a-x)) (2*(H+a-x)^2-H2-3*b+x^2)
    (a+x) (e+a*x) (u3+q*u4) H E (v3+q*v4)
    (2*a) (4*e) (8*w3+q*(16*w4))
    hq h1 h2
  rw [show q^3*(u3+q*u4)=q^3*u3+q^4*u4 by exact mul_pow_three_tail _ _ _,
    show q^3*(v3+q*v4)=q^3*v3+q^4*v4 by exact mul_pow_three_tail _ _ _,
    show q^3*(8*w3+q*(16*w4))=q^3*(8*w3)+q^4*(16*w4) by exact mul_pow_three_tail _ _ _] at h
  have hA : 1+2*q*(H+a-x)+q^2*(2*(H+a-x)^2-H2-3*b+x^2) =
      1+q*(2*(H+a-x))+q^2*(2*(H+a-x)^2-H2-3*b+x^2) := by
    congr 1
    ac_rfl
  have hV : 1+2*q*a+4*q^2*e+8*q^3*w3+16*q^4*w4 =
      1+q*(2*a)+q^2*(4*e)+q^3*(8*w3)+q^4*(16*w4) := by
    rw [show 2*q*a=q*(2*a) by ac_rfl, show 4*q^2*e=q^2*(4*e) by ac_rfl,
      show 8*q^3*w3=q^3*(8*w3) by ac_rfl,
      show 16*q^4*w4=q^4*(16*w4) by ac_rfl]
  rw [hA, hV]
  calc
    4*q^2*x^2*(1+q*(2*(H+a-x))+q^2*(2*(H+a-x)^2-H2-3*b+x^2))*
        (1+q*(a+x)+q^2*(e+a*x)+q^3*u3+q^4*u4)^2 =
      4*x^2*(q^2*(1+q*(2*(H+a-x))+q^2*(2*(H+a-x)^2-H2-3*b+x^2))*
        (1+q*(a+x)+q^2*(e+a*x)+q^3*u3+q^4*u4)^2) :=
          move_four p x _ _
    _ = 4*x^2*(q^2*(1+q*H+q^2*E+q^3*v3+q^4*v4)^2*
        (1+q*(2*a)+q^2*(4*e)+q^3*(8*w3)+q^4*(16*w4))^2) :=
          congrArg (fun z : R5 => 4*x^2*z) (by simpa only [add_assoc] using h)
    _ = (2*q*x*(1+q*H+q^2*E+q^3*v3+q^4*v4)*
        (1+q*(2*a)+q^2*(4*e)+q^3*(8*w3)+q^4*(16*w4)))^2 :=
          finish_four p x _ _

include hp
set_option Elab.async false
private lemma bb_sq_approx {r : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    bb p r ^ 2 = bApprox p r := by
  have hf := bb_mul_pp p hp hr0 hrp
  have hsq := congrArg (fun z : R5 => z^2) hf
  apply ((pp_isUnit p 1 r).pow 2).mul_right_cancel
  symm
  have hq5 : q^5 = 0 := q_pow_five p
  have hH := hs_self_sq (R := R5) 1 (p-1)
  have ha := hs_self_sq (R := R5) 1 (r-1)
  have halg := bb_direct_algebra p
    (hs (R := R5) 1 (p-1)) (hs (R := R5) 2 (p-1))
    (hh (R := R5) 1 1 (p-1))
    (hs (R := R5) 1 (r-1)) (hs (R := R5) 2 (r-1))
    (hh (R := R5) 1 1 (r-1)) (iv (R := R5) r)
    (hhh (R := R5) 1 1 1 r) (hhhh (R := R5) 1 1 1 1 r)
    (hhh (R := R5) 1 1 1 (p-1)) (hhhh (R := R5) 1 1 1 1 (p-1))
    (hhh (R := R5) 1 1 1 (r-1)) (hhhh (R := R5) 1 1 1 1 (r-1))
    hq5 hH ha
  simp only [bApprox]
  rw [pp_expansion p 1 r] at hsq ⊢
  rw [pp_expansion p 1 (p-1), pp_expansion p 2 (r-1)] at hsq
  have hsr := hs_succ (R := R5) 1 (r-1)
  have hhr := hh_succ (R := R5) 1 1 (r-1)
  rw [show r-1+1=r by exact pred_succ_eq hr0] at hsr hhr
  rw [hsr, hhr] at hsq ⊢
  simp only [pow_one, one_pow, one_mul] at hsq ⊢
  norm_num at hsq
  calc
    4*q^2*iv (R := R5) r^2 *
          (1+2*q*(hs (R := R5) 1 (p-1)+hs (R := R5) 1 (r-1)-iv (R := R5) r)+
            q^2*(2*(hs (R := R5) 1 (p-1)+hs (R := R5) 1 (r-1)-iv (R := R5) r)^2-
              hs (R := R5) 2 (p-1)-3*hs (R := R5) 2 (r-1)+iv (R := R5) r^2)) *
        (1+q*(hs (R := R5) 1 (r-1)+iv (R := R5) r)+
          q^2*(hh (R := R5) 1 1 (r-1)+hs (R := R5) 1 (r-1)*iv (R := R5) r)+
          q^3*hhh (R := R5) 1 1 1 r+q^4*hhhh (R := R5) 1 1 1 1 r)^2 =
      (2*q*iv (R := R5) r *
        (1+q*hs (R := R5) 1 (p-1)+q^2*hh (R := R5) 1 1 (p-1)+
          q^3*hhh (R := R5) 1 1 1 (p-1)+q^4*hhhh (R := R5) 1 1 1 1 (p-1)) *
        (1+2*q*hs (R := R5) 1 (r-1)+4*q^2*hh (R := R5) 1 1 (r-1)+
          8*q^3*hhh (R := R5) 1 1 1 (r-1)+16*q^4*hhhh (R := R5) 1 1 1 1 (r-1)))^2 := halg
    _ = (bb p r *
        (1+q*(hs (R := R5) 1 (r-1)+iv (R := R5) r)+
          q^2*(hh (R := R5) 1 1 (r-1)+hs (R := R5) 1 (r-1)*iv (R := R5) r)+
          q^3*hhh (R := R5) 1 1 1 r+q^4*hhhh (R := R5) 1 1 1 1 r))^2 := hsq.symm
    _ = bb p r^2 *
        (1+q*(hs (R := R5) 1 (r-1)+iv (R := R5) r)+
          q^2*(hh (R := R5) 1 1 (r-1)+hs (R := R5) 1 (r-1)*iv (R := R5) r)+
          q^3*hhh (R := R5) 1 1 1 r+q^4*hhhh (R := R5) 1 1 1 1 r)^2 :=
      mul_pow _ _ 2

end Terms


section SumExpansion
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)
local notation "q" => (p : R5)

private lemma sq_q_factor (t x P : R5) : (t*x*P)^2 = x^2*(t^2*P^2) := by
  simp only [mul_pow]
  ac_rfl

set_option Elab.async false
private lemma first_block_sq {r : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    (((p+r-1).choose r : R5))^2 = q^2*iv (R := R5) r^2 *
      (1+2*q*hs (R := R5) 1 (r-1) + q^2*(hs (R := R5) 1 (r-1)^2 +
        2*hh (R := R5) 1 1 (r-1))) := by
  rw [first_block p hp hr0 hrp, pp_expansion p]
  simp only [one_mul, one_pow]
  have hq5 : q^5=0 := q_pow_five p
  have ht := q2_sq_trunc p (hs (R := R5) 1 (r-1))
    (hh (R := R5) 1 1 (r-1)) (hhh (R := R5) 1 1 1 (r-1)+
      q*hhhh (R := R5) 1 1 1 1 (r-1)) hq5
  rw [show q^3*(hhh (R := R5) 1 1 1 (r-1)+q*hhhh (R := R5) 1 1 1 1 (r-1)) =
    q^3*hhh (R := R5) 1 1 1 (r-1)+q^4*hhhh (R := R5) 1 1 1 1 (r-1) by
      exact mul_pow_three_tail _ _ _] at ht
  calc
    (q*iv (R := R5) r*
      (1+q*hs (R := R5) 1 (r-1)+q^2*hh (R := R5) 1 1 (r-1)+
       q^3*hhh (R := R5) 1 1 1 (r-1)+q^4*hhhh (R := R5) 1 1 1 1 (r-1)))^2 =
      iv (R := R5) r^2*(q^2*
       (1+q*hs (R := R5) 1 (r-1)+q^2*hh (R := R5) 1 1 (r-1)+
        q^3*hhh (R := R5) 1 1 1 (r-1)+q^4*hhhh (R := R5) 1 1 1 1 (r-1))^2) :=
        sq_q_factor p hp q (iv (R := R5) r) _
    _ = iv (R := R5) r^2*(q^2*(1+2*q*hs (R := R5) 1 (r-1)+
        q^2*(hs (R := R5) 1 (r-1)^2+2*hh (R := R5) 1 1 (r-1)))) := by
          simpa only [add_assoc] using
            congrArg (fun z : R5 => iv (R := R5) r^2*z) ht
    _ = q^2*iv (R := R5) r^2*(1+2*q*hs (R := R5) 1 (r-1)+
        q^2*(hs (R := R5) 1 (r-1)^2+2*hh (R := R5) 1 1 (r-1))) := by ac_rfl


private def zsum (n : ℕ) : R5 :=
  2*hhh (R := R5) 1 1 2 n + hh (R := R5) 2 2 n

private def smallSum (n : ℕ) : R5 :=
  ∑ k ∈ range n, (((p+(k+1)-1).choose (k+1) : R5)^2 + bb p (k+1)^2)

private def smallRhs (n : ℕ) : R5 :=
  let H := hs (R := R5) 1 (p-1)
  let H2 := hs (R := R5) 2 (p-1)
  5*q^2*hs (R := R5) 2 n +
  q^3*(10*hh (R := R5) 1 2 n + 8*H*hs (R := R5) 2 n - 8*hs (R := R5) 3 n) +
  q^4*(9*zsum p n + 2*hhh (R := R5) 1 1 2 n -
    16*hh (R := R5) 1 3 n - 12*hh (R := R5) 2 2 n + 12*hs (R := R5) 4 n +
    8*H^2*hs (R := R5) 2 n + 16*H*hh (R := R5) 1 2 n -
    16*H*hs (R := R5) 3 n - 4*H2*hs (R := R5) 2 n)

private lemma zsum_succ (n : ℕ) :
    zsum p (n+1) = zsum p n +
      hs (R := R5) 1 n^2*iv (R := R5) (n+1)^2 := by
  unfold zsum
  rw [hhh_succ, hh_succ, hs_self_sq 1]
  ring


private lemma small_sum_expansion {n : ℕ} (hn : n < p) :
    smallSum p n = smallRhs p n := by
  induction n with
  | zero => simp [smallSum, smallRhs, hs, hh, hhh, zsum]
  | succ n ih =>
    unfold smallSum
    rw [sum_range_succ]
    change smallSum p n + (((p+(n+1)-1).choose (n+1) : R5)^2 + bb p (n+1)^2) = _
    rw [ih (pred_lt_of_succ_lt hn)]
    rw [first_block_sq p hp (Nat.zero_lt_succ n) hn,
      bb_sq_approx p hp (Nat.zero_lt_succ n) hn]
    simp only [bApprox, smallRhs]
    rw [show n+1-1=n by exact Nat.add_sub_cancel n 1]
    rw [hh_succ 1 2 n, zsum_succ p hp n, hhh_succ 1 1 2 n,
      hh_succ 1 3 n, hh_succ 2 2 n]
    simp only [hs_succ, pow_one]
    ring

end SumExpansion

set_option Elab.async false
set_option Elab.async false
section FiniteDuality
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)

private def bt (f : ℕ → R5) (n : ℕ) : R5 :=
  ∑ k ∈ range n, (-1 : R5)^k * (n.choose (k+1) : R5) * f k

private lemma bt_succ (f : ℕ → R5) (n : ℕ) :
    bt p f (n+1) = bt p f n +
      ∑ k ∈ range (n+1), (-1 : R5)^k * (n.choose k : R5) * f k := by
  simp only [bt, sum_range_succ, Nat.choose_succ_succ, Nat.cast_add]
  simp_rw [mul_add, add_mul]
  rw [sum_add_distrib]
  simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, zero_add]
  ring

private lemma bt_prefix_succ (f g : ℕ → R5) (n : ℕ)
    (hf0 : f 0 = 0) (hfg : ∀ k, f (k+1) = f k + g k) :
    bt p f (n+1) = -bt p g n := by
  rw [bt_succ p hp, sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, hf0, mul_zero, add_zero]
  rw [show (∑ k ∈ range n, (-1 : R5)^(k+1) * (n.choose (k+1) : R5) * f (k+1)) =
      -(bt p f n) - bt p g n by
    simp only [bt]
    rw [← sum_neg_distrib, ← sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hfg k, show (-1 : R5)^(k+1) = (-1 : R5)^k * (-1) by exact pow_succ _ _]
    ring]
  ring

set_option Elab.async false
private lemma bt_hs_succ (n : ℕ) :
    bt p (fun k => hs (R := R5) 1 k) (n+1) = - alt p 1 n := by
  have h := bt_prefix_succ p hp (fun k => hs (R := R5) 1 k)
    (fun k => iv (R := R5) (k+1)) n (by simp [hs])
    (fun k => by simpa only [pow_one] using hs_succ (R := R5) 1 k)
  simpa only [bt, alt, pow_one] using h

private def bw (f : ℕ → R5) (a n : ℕ) : R5 :=
  bt p (fun k => f k * iv (R := R5) (k+1)^a) n

private lemma bw_succ (f : ℕ → R5) (a n : ℕ) (hn : n+1 < p) :
    bw p f (a+1) (n+1) = bw p f (a+1) n +
      iv (R := R5) (n+1) * bw p f a (n+1) := by
  rw [bw, bt_succ p hp]
  change bt p (fun k => f k * iv (R := R5) (k+1)^(a+1)) n +
      (∑ k ∈ range (n+1), (-1 : R5)^k * (n.choose k : R5) *
        (f k * iv (R := R5) (k+1)^(a+1))) = _
  congr 1
  rw [bw, bt, mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have hc := choose_iv_swap p hp (k := k) (n := n) (Nat.lt_succ_iff.mp hk) hn
  rw [show iv (R := R5) (k+1)^(a+1) =
    iv (R := R5) (k+1)^a * iv (R := R5) (k+1) by
      simpa only [Nat.add_comm] using (pow_succ (iv (R := R5) (k+1)) a)]
  linear_combination ((-1 : R5)^k * f k * iv (R := R5) (k+1)^a) * hc


private lemma bt_hs_eval {n : ℕ} (hn : n < p) :
    bt p (fun k => hs (R := R5) 1 k) n = -hs (R := R5) 1 (n-1) := by
  cases n with
  | zero => simp [bt, hs]
  | succ n =>
    rw [bt_hs_succ p hp, alt_one_eq_hs p hp (pred_lt_of_succ_lt hn)]
    congr 2

private lemma bw_hs_one {n : ℕ} (hn : n < p) :
    bw p (fun k => hs (R := R5) 1 k) 1 n = -hh (R := R5) 1 1 n := by
  induction n with
  | zero => simp [bw, bt, hh]
  | succ n ih =>
    rw [show 1=0+1 by rfl, bw_succ p hp _ 0 n hn, ih (pred_lt_of_succ_lt hn)]
    have hb := bt_hs_eval p hp (n := n+1) hn
    have hb' : bw p (fun k => hs (R := R5) 1 k) 0 (n+1) =
        -hs (R := R5) 1 (n+1-1) := by simpa [bw] using hb
    rw [hb', hh_succ]
    rw [show n+1-1=n by exact Nat.add_sub_cancel n 1]
    ring

private lemma bw_hs_two {n : ℕ} (hn : n < p) :
    bw p (fun k => hs (R := R5) 1 k) 2 n =
      -(hhh (R := R5) 1 1 1 n + hh (R := R5) 1 2 n) := by
  induction n with
  | zero => simp [bw, bt, hhh, hh]
  | succ n ih =>
    rw [show 2=1+1 by rfl, bw_succ p hp _ 1 n hn, ih (pred_lt_of_succ_lt hn),
      bw_hs_one p hp hn, hhh_succ, hh_succ, hh_succ]
    ring

private lemma bw_hs_three {n : ℕ} (hn : n < p) :
    bw p (fun k => hs (R := R5) 1 k) 3 n =
      -(hhhh (R := R5) 1 1 1 1 n + hhh (R := R5) 1 1 2 n +
        hhh (R := R5) 1 2 1 n + hh (R := R5) 1 3 n) := by
  induction n with
  | zero => simp [bw, bt, hhhh, hhh, hh]
  | succ n ih =>
    rw [show 3=2+1 by rfl, bw_succ p hp _ 2 n hn, ih (pred_lt_of_succ_lt hn),
      bw_hs_two p hp hn]
    simp only [hhhh_succ, hhh_succ, hh_succ, pow_one]
    norm_num
    ring

set_option Elab.async false
set_option Elab.async false
private lemma bt_hh_succ (n : ℕ) :
    bt p (fun k => hh (R := R5) 1 1 k) (n+1) =
      -bw p (fun k => hs (R := R5) 1 k) 1 n := by
  have h := bt_prefix_succ p hp (fun k => hh (R := R5) 1 1 k)
    (fun k => hs (R := R5) 1 k * iv (R := R5) (k+1)) n (by simp [hh])
    (fun k => by simpa only [pow_one] using hh_succ (R := R5) 1 1 k)
  simpa only [bw, pow_one] using h

private lemma bt_hh_eval {n : ℕ} (hn : n < p) :
    bt p (fun k => hh (R := R5) 1 1 k) n = hh (R := R5) 1 1 (n-1) := by
  cases n with
  | zero => simp [bt, hh]
  | succ n =>
    rw [bt_hh_succ p hp, bw_hs_one p hp (pred_lt_of_succ_lt hn)]
    simp only [neg_neg]
    congr 1

private lemma bw_hh_one {n : ℕ} (hn : n < p) :
    bw p (fun k => hh (R := R5) 1 1 k) 1 n = hhh (R := R5) 1 1 1 n := by
  induction n with
  | zero => simp [bw, bt, hhh]
  | succ n ih =>
    rw [show 1=0+1 by rfl, bw_succ p hp _ 0 n hn, ih (pred_lt_of_succ_lt hn)]
    have hb := bt_hh_eval p hp (n := n+1) hn
    have hb' : bw p (fun k => hh (R := R5) 1 1 k) 0 (n+1) =
        hh (R := R5) 1 1 (n+1-1) := by simpa [bw] using hb
    rw [hb', hhh_succ]
    rw [show n+1-1=n by exact Nat.add_sub_cancel n 1]
    ring

private lemma bw_hh_two {n : ℕ} (hn : n < p) :
    bw p (fun k => hh (R := R5) 1 1 k) 2 n =
      hhhh (R := R5) 1 1 1 1 n + hhh (R := R5) 1 1 2 n := by
  induction n with
  | zero => simp [bw, bt, hhhh, hhh]
  | succ n ih =>
    rw [show 2=1+1 by rfl, bw_succ p hp _ 1 n hn, ih (pred_lt_of_succ_lt hn),
      bw_hh_one p hp hn, hhhh_succ, hhh_succ, hhh_succ]
    ring

set_option Elab.async false
end FiniteDuality



set_option Elab.async false
set_option Elab.async true
section Newton
variable {R : Type*} [CommRing R] [Inv R]

private lemma six_hhh_one (n : ℕ) :
    6 * hhh (R := R) 1 1 1 n = hs (R := R) 1 n ^ 3 -
      3 * hs (R := R) 1 n * hs (R := R) 2 n + 2 * hs (R := R) 3 n := by
  induction n with
  | zero => simp [hs, hhh]
  | succ n ih =>
    have hst := hs_self_sq (R := R) 1 n
    rw [hhh_succ, hs_succ, hs_succ, hs_succ]
    simp only [pow_one]
    linear_combination ih - 3 * iv (R := R) (n+1) * hst

private lemma twenty_four_hhhh_one (n : ℕ) :
    24 * hhhh (R := R) 1 1 1 1 n = hs (R := R) 1 n ^ 4 -
      6 * hs (R := R) 1 n ^ 2 * hs (R := R) 2 n +
      3 * hs (R := R) 2 n ^ 2 + 8 * hs (R := R) 1 n * hs (R := R) 3 n -
      6 * hs (R := R) 4 n := by
  induction n with
  | zero => simp [hs, hhhh]
  | succ n ih =>
    have h6 := six_hhh_one (R := R) n
    rw [hhhh_succ, hs_succ, hs_succ, hs_succ, hs_succ]
    simp only [pow_one]
    linear_combination ih + 4 * iv (R := R) (n+1) * h6

end Newton
set_option Elab.async false
set_option Elab.async false



private lemma not_dvd_of_lt_seven {p n : ℕ} (hp7 : 7 ≤ p) (hn0 : 0 < n) (hn7 : n < 7) :
    ¬ p ∣ n :=
  Nat.not_dvd_of_pos_of_lt hn0 (Nat.lt_of_lt_of_le hn7 hp7)

private lemma small_lt_pred {a p : ℕ} (ha : a ≤ 4) (hp7 : 7 ≤ p) : a < p - 1 := by
  have h6 : 6 ≤ p - 1 := Nat.le_sub_of_add_le (by simpa using hp7)
  exact Nat.lt_of_le_of_lt ha (Nat.lt_of_lt_of_le (by decide) h6)

set_option Elab.async false
set_option Elab.async true
section WeightFour
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)
local notation "Fp" => ZMod p

private lemma rho_pm {n : ℕ} : rho p (pm p n) = 1 := by
  simp [pm, rho]

private lemma rho_bw_sum (f : ℕ → R5) (a : ℕ) :
    rho p (bw p f a (p-1)) =
      -rho p (∑ k ∈ range (p-1), f k * iv (R := R5) (k+1)^a) := by
  simp only [bw, bt, map_sum, map_mul, map_pow, map_neg]
  rw [← sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have hc := signed_choose_eq_pm p hp (k := k+1) (succ_lt_of_lt_pred hp.pos hk)
  have hs : (-1 : R5)^k * ((p-1).choose (k+1) : R5) = -(pm p (k+1)) := by
    calc
      _ = -((-1 : R5)^(k+1) * ((p-1).choose (k+1) : R5)) := by
        rw [pow_succ]; ring
      _ = _ := by rw [hc]
  have hsm : (-(rho p) 1)^k * (rho p) (((p-1).choose (k+1) : R5)) = -1 := by
    have hm := congr_arg (rho p) hs
    simpa only [map_mul, map_pow, map_neg, map_one, rho_pm p hp] using hm
  rw [hsm, neg_one_mul]

private lemma rho_hs_zero (a : ℕ) (ha0 : 0 < a) (ha : a < p-1) :
    rho p (hs (R := R5) a (p-1)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [rho_hs p hp, hs_eq_zero p a ha0 ha]

private lemma rho_hhhh_one_zero (hp7 : 7 ≤ p) :
    rho p (hhhh (R := R5) 1 1 1 1 (p-1)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hn := congr_arg (rho p) (twenty_four_hhhh_one (R := R5) (p-1))
  simp only [map_mul, map_natCast, map_sub, map_add, map_pow] at hn
  rw [rho_hs_zero p hp 1 (by decide) (small_lt_pred (by decide) hp7),
    rho_hs_zero p hp 2 (by decide) (small_lt_pred (by decide) hp7),
    rho_hs_zero p hp 3 (by decide) (small_lt_pred (by decide) hp7),
    rho_hs_zero p hp 4 (by decide) (small_lt_pred (by decide) hp7)] at hn
  simp only [zero_pow (by decide : 4 ≠ 0), zero_pow (by decide : 2 ≠ 0),
    zero_mul, mul_zero, add_zero, sub_zero] at hn
  have h24 : (24 : Fp) ≠ 0 := by
    change ((24 : ℕ) : Fp) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have hd' : p ∣ 3 * 8 := by norm_num at hd ⊢; exact hd
    rcases (hp.dvd_mul).mp hd' with h3 | h8
    · exact (not_dvd_of_lt_seven hp7 (by decide) (by decide)) h3
    · have h2d : p ∣ 2 := hp.dvd_of_dvd_pow (n := 3) (by norm_num at h8 ⊢; exact h8)
      exact (not_dvd_of_lt_seven hp7 (by decide) (by decide)) h2d
  have hm : rho p (24 : R5) = (24 : Fp) := by
    simpa [rho] using (ZMod.cast_natCast (R := Fp) (dvd_pow_self p (n := 5) (by decide)) 24)
  rw [hm] at hn
  exact (mul_eq_zero.mp hn).resolve_left h24

private lemma two_ne_zero_mod (hp7 : 7 ≤ p) : (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact not_dvd_of_lt_seven hp7 (by decide) (by decide)

private lemma rho_hhh_one_one_two_zero (hp7 : 7 ≤ p) :
    rho p (hhh (R := R5) 1 1 2 (p-1)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have he := congr_arg (rho p) (bw_hh_two p hp (n := p-1) (prime_pred_lt hp))
  rw [show rho p (bw p (fun k => hh (R := R5) 1 1 k) 2 (p-1)) =
      -rho p (hhh (R := R5) 1 1 2 (p-1)) by
    simpa only [hhh] using
      (rho_bw_sum p hp (fun k => hh (R := R5) 1 1 k) 2)] at he
  simp only [map_add] at he
  rw [rho_hhhh_one_zero p hp hp7] at he
  simp only [zero_add] at he
  have h2 : (2 : Fp) ≠ 0 := two_ne_zero_mod p hp hp7
  have hz : (2 : Fp) * rho p (hhh (R := R5) 1 1 2 (p-1)) = 0 := by
    linear_combination -he
  exact (_root_.mul_eq_zero.mp hz).resolve_left h2

end WeightFour
set_option Elab.async false
set_option Elab.async false


set_option Elab.async false
set_option Elab.async true
section MoreWeightFour
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)
local notation "Fp" => ZMod p

private lemma rho_hh_two_two_zero (hp7 : 7 ≤ p) :
    rho p (hh (R := R5) 2 2 (p-1)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hm := congr_arg (rho p) (hs_self_sq (R := R5) 2 (p-1))
  simp only [map_pow, map_add, map_mul, map_natCast] at hm
  rw [rho_hs_zero p hp 2 (by decide) (small_lt_pred (by decide) hp7),
    rho_hs_zero p hp 4 (by decide) (small_lt_pred (by decide) hp7)] at hm
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at hm
  have hmap : rho p (2 : R5) = (2 : Fp) := by
    simpa [rho] using (ZMod.cast_natCast (R := Fp)
      (dvd_pow_self p (n := 5) (by decide)) 2)
  rw [hmap] at hm
  have h2 : (2 : Fp) ≠ 0 := two_ne_zero_mod p hp hp7
  exact (_root_.mul_eq_zero.mp (by simpa using hm.symm)).resolve_left h2

private lemma rho_hh_one_three_zero (hp7 : 7 ≤ p) :
    rho p (hh (R := R5) 1 3 (p-1)) = 0 := by
  have hb := congr_arg (rho p) (bw_hs_three p hp (n := p-1) (prime_pred_lt hp))
  rw [show rho p (bw p (fun k => hs (R := R5) 1 k) 3 (p-1)) =
      -rho p (hh (R := R5) 1 3 (p-1)) by
    simpa only [hh] using
      (rho_bw_sum p hp (fun k => hs (R := R5) 1 k) 3)] at hb
  simp only [map_neg, map_add] at hb
  rw [rho_hhhh_one_zero p hp hp7, rho_hhh_one_one_two_zero p hp hp7] at hb
  simp only [zero_add] at hb
  have hP : rho p (hhh (R := R5) 1 2 1 (p-1)) = 0 := by
    linear_combination hb
  letI : Fact p.Prime := ⟨hp⟩
  have hm := congr_arg (rho p) (hs_mul_hh_one_two (R := R5) (p-1))
  simp only [map_mul, map_add, map_natCast] at hm
  rw [rho_hs_zero p hp 1 (by decide) (small_lt_pred (by decide) hp7),
    rho_hhh_one_one_two_zero p hp hp7, hP,
    rho_hh_two_two_zero p hp hp7] at hm
  simp only [zero_mul, zero_add, mul_zero] at hm
  exact hm.symm

end MoreWeightFour
set_option Elab.async false
set_option Elab.async false


set_option Elab.async false
set_option Elab.async true
section Orders
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)
local notation "q" => (p : R5)

private lemma two_isUnit (hp7 : 7 ≤ p) : IsUnit (2 : R5) := by
  change IsUnit ((2 : ℕ) : R5)
  rw [ZMod.isUnit_iff_coprime]
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact not_dvd_of_lt_seven hp7 (by decide) (by decide)
  exact hcop.pow_right 5

private lemma hs_one_bigO_two (hp7 : 7 ≤ p) :
    IsBigO p 2 (hs (R := R5) 1 (p-1)) := by
  obtain ⟨b, hb⟩ := hs_bigO_one p hp 2 (by decide) (small_lt_pred (by decide) hp7)
  let u : R5 := (2 : R5)⁻¹
  have hu : u * 2 = 1 := by
    exact ZMod.inv_mul_of_unit (2 : R5) (two_isUnit p hp hp7)
  have hr := reflect_hs_one p hp
  refine ⟨-u * (b + hs (R := R5) 3 (p-1) +
      q * hs (R := R5) 4 (p-1) + q^2 * hs (R := R5) 5 (p-1)), ?_⟩
  rw [hb] at hr
  let X : R5 := b + hs (R := R5) 3 (p-1) + q * hs (R := R5) 4 (p-1) +
    q^2 * hs (R := R5) 5 (p-1)
  have he : 2 * hs (R := R5) 1 (p-1) = -q^2 * X := by
    dsimp [X]
    linear_combination hr
  calc
    hs (R := R5) 1 (p-1) = u * (2 * hs (R := R5) 1 (p-1)) := by
      rw [show u * (2 * hs (R := R5) 1 (p-1)) =
        (u*2) * hs (R := R5) 1 (p-1) by ac_rfl, hu, one_mul]
    _ = u * (-q^2 * X) := by rw [he]
    _ = q^2 * (-u * X) := by
      simp only [neg_mul, mul_neg]
      ac_rfl

private lemma hs_three_bigO_two (hp7 : 7 ≤ p) :
    IsBigO p 2 (hs (R := R5) 3 (p-1)) := by
  obtain ⟨d, hd⟩ := hs_bigO_one p hp 4 (by decide) (small_lt_pred (by decide) hp7)
  obtain ⟨y, hy⟩ := reflect_hs_three_short p hp
  let u : R5 := (2 : R5)⁻¹
  have hu : u * 2 = 1 := ZMod.inv_mul_of_unit (2 : R5) (two_isUnit p hp hp7)
  refine ⟨u*(y-3*d), ?_⟩
  rw [hd] at hy
  calc
    hs (R := R5) 3 (p-1) = u*(2*hs (R := R5) 3 (p-1)) := by
      rw [show u*(2*hs (R := R5) 3 (p-1)) =
        (u*2)*hs (R := R5) 3 (p-1) by ac_rfl, hu, one_mul]
    _ = q^2*(u*(y-3*d)) := by linear_combination u*hy

private lemma hhh_one_one_two_bigO (hp7 : 7 ≤ p) :
    IsBigO p 1 (hhh (R := R5) 1 1 2 (p-1)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply isBigO_one_of_red_eq_zero
  simpa only [red] using rho_hhh_one_one_two_zero p hp hp7

private lemma hh_one_three_bigO (hp7 : 7 ≤ p) :
    IsBigO p 1 (hh (R := R5) 1 3 (p-1)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply isBigO_one_of_red_eq_zero
  simpa only [red] using rho_hh_one_three_zero p hp hp7

private lemma hh_two_two_bigO (hp7 : 7 ≤ p) :
    IsBigO p 1 (hh (R := R5) 2 2 (p-1)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply isBigO_one_of_red_eq_zero
  simpa only [red] using rho_hh_two_two_zero p hp hp7

set_option Elab.async false
set_option Elab.async false
private lemma zsum_bigO (hp7 : 7 ≤ p) : IsBigO p 1 (zsum p (p-1)) := by
  obtain ⟨k, hk⟩ := hhh_one_one_two_bigO p hp hp7
  obtain ⟨i, hi⟩ := hh_two_two_bigO p hp hp7
  refine ⟨2*k+i, ?_⟩
  unfold zsum
  change 2 * hhh (R := R5) 1 1 2 (p-1) + hh (R := R5) 2 2 (p-1) = _
  rw [hk, hi]
  rw [mul_add]
  congr 1
  ac_rfl

set_option Elab.async false
private lemma key_alt_relation :
    q^2*(hs (R := R5) 1 (p-1)^2+3*hs (R := R5) 2 (p-1)-
      2*q*(hh (R := R5) 1 2 (p-1)+hs (R := R5) 3 (p-1))+
      2*q^2*(hhh (R := R5) 1 1 2 (p-1)+hh (R := R5) 1 3 (p-1))) = 0 := by
  have hp0 := hp.pos
  have htwo := two_mul_alt_two p hp (n := p-1) (prime_pred_lt hp)
  obtain ⟨T, hT⟩ := alt_two_trunc p hp
  have hq : q^5=0 := q_pow_five p
  have he : hs (R := R5) 1 (p-1)^2+3*hs (R := R5) 2 (p-1)-
      2*q*(hh (R := R5) 1 2 (p-1)+hs (R := R5) 3 (p-1))+
      2*q^2*(hhh (R := R5) 1 1 2 (p-1)+hh (R := R5) 1 3 (p-1)) =
      2*q^3*T := by linear_combination 2*hT - htwo
  rw [he]
  calc
    q^2*(2*q^3*T)=2*q^5*T := by
      rw [show q^5=q^2*q^3 by rw [← pow_add]]
      ac_rfl
    _=0 := by rw [hq]; simp



private lemma hh_one_one_bigO (hp7 : 7 ≤ p) :
    IsBigO p 1 (hh (R := R5) 1 1 (p-1)) := by
  obtain ⟨a, ha⟩ := hs_one_bigO_two p hp hp7
  obtain ⟨b, hb⟩ := hs_bigO_one p hp 2 (by decide) (small_lt_pred (by decide) hp7)
  let u : R5 := (2 : R5)⁻¹
  have hu : u*2=1 := ZMod.inv_mul_of_unit (2 : R5) (two_isUnit p hp hp7)
  have he := hs_self_sq (R := R5) 1 (p-1)
  refine ⟨u*(q^3*a^2-b), ?_⟩
  rw [ha, hb] at he
  calc
    hh (R := R5) 1 1 (p-1) = u * (2 * hh (R := R5) 1 1 (p-1)) := by
      rw [show u*(2*hh (R := R5) 1 1 (p-1)) =
        (u*2)*hh (R := R5) 1 1 (p-1) by ac_rfl, hu, one_mul]
    _ = q * (u*(q^3*a^2-b)) := by
      linear_combination -u * he
    _ = q^1 * (u*(q^3*a^2-b)) := by simp

private lemma six_isUnit (hp7 : 7 ≤ p) : IsUnit (6 : R5) := by
  change IsUnit ((6 : ℕ) : R5)
  rw [ZMod.isUnit_iff_coprime]
  have hcop : Nat.Coprime 6 p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact not_dvd_of_lt_seven hp7 (by decide) (by decide)
  exact hcop.pow_right 5

private lemma hhh_one_bigO_two (hp7 : 7 ≤ p) :
    IsBigO p 2 (hhh (R := R5) 1 1 1 (p-1)) := by
  obtain ⟨a, ha⟩ := hs_one_bigO_two p hp hp7
  obtain ⟨b, hb⟩ := hs_bigO_one p hp 2 (by decide) (small_lt_pred (by decide) hp7)
  obtain ⟨c, hc⟩ := hs_three_bigO_two p hp hp7
  let u : R5 := (6 : R5)⁻¹
  have hu : u*6=1 := ZMod.inv_mul_of_unit (6 : R5) (six_isUnit p hp hp7)
  have he := six_hhh_one (R := R5) (p-1)
  refine ⟨u*(q^4*a^3-3*q*a*b+2*c), ?_⟩
  rw [ha, hb, hc] at he
  calc
    hhh (R := R5) 1 1 1 (p-1) = u * (6 * hhh (R := R5) 1 1 1 (p-1)) := by
      rw [show u*(6*hhh (R := R5) 1 1 1 (p-1)) =
        (u*6)*hhh (R := R5) 1 1 1 (p-1) by ac_rfl, hu, one_mul]
    _ = q^2 * (u*(q^4*a^3-3*q*a*b+2*c)) := by
      linear_combination u * he

private lemma hhhh_one_bigO (hp7 : 7 ≤ p) :
    IsBigO p 1 (hhhh (R := R5) 1 1 1 1 (p-1)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply isBigO_one_of_red_eq_zero
  simpa only [red] using rho_hhhh_one_zero p hp hp7

set_option Elab.async false
end Orders

section FinalAlgebra
variable {R : Type*} [CommRing R]

private lemma series_reduce (q a e j l α β γ δ : R) (hq : q^5=0) :
    1 + α*q*(q^2*a) + β*q^2*(q*e) + γ*q^3*(q^2*j) + δ*q^4*(q*l) =
      1+q^3*(α*a+β*e)  := by
  calc
    1 + α*q*(q^2*a) + β*q^2*(q*e) + γ*q^3*(q^2*j) + δ*q^4*(q*l) =
      (1+q^3*(α*a+β*e)) + q^5*(γ*j+δ*l) := by ring
    _ = 1+q^3*(α*a+β*e) := by rw [hq, zero_mul, add_zero]

private lemma x_reduce (q a b c d F g i k z : R) (hq : q^5=0) :
    5*q^2*(q*b) + q^3*(10*F+8*(q^2*a)*(q*b)-8*(q^2*c)) +
      q^4*(9*(q*z)+2*(q*k)-16*(q*g)-12*(q*i)+12*(q*d)+
        8*(q^2*a)^2*(q*b)+16*(q^2*a)*F-16*(q^2*a)*(q^2*c)-4*(q*b)^2) =
    q^3*(5*b+10*F)  := by
  calc
    5*q^2*(q*b) + q^3*(10*F+8*(q^2*a)*(q*b)-8*(q^2*c)) +
        q^4*(9*(q*z)+2*(q*k)-16*(q*g)-12*(q*i)+12*(q*d)+
          8*(q^2*a)^2*(q*b)+16*(q^2*a)*F-16*(q^2*a)*(q^2*c)-4*(q*b)^2) =
      q^3*(5*b+10*F) + q^5*(16*F*a*q+8*a^2*b*q^4+8*a*b*q-16*a*c*q^3-
        4*b^2*q-8*c+12*d-16*g-12*i+2*k+9*z) := by ring
    _ = q^3*(5*b+10*F) := by rw [hq, zero_mul, add_zero]

private lemma nil_sq (t y : R) (ht : t^2=0) :
    (1+t*y)^2=1+2*t*y  := by
  calc
    (1+t*y)^2 = 1+2*t*y+t^2*y^2 := by ring
    _ = 1+2*t*y := by rw [ht, zero_mul, add_zero]

private lemma nil_four (t y : R) (ht : t^2=0) :
    (1+t*y)^4=1+4*t*y  := by
  calc
    (1+t*y)^4 = 1+4*t*y+t^2*(6*y^2+4*t*y^3+t^2*y^4) := by ring
    _ = 1+4*t*y := by rw [ht, zero_mul, add_zero]

private lemma nil_cube_three (t y : R) (ht : t^2=0) :
    (3+t*y)^3=27+27*t*y  := by
  calc
    (3+t*y)^3 = 27+27*t*y+t^2*(9*y^2+t*y^3) := by ring
    _ = 27+27*t*y := by rw [ht, zero_mul, add_zero]

private lemma nil_product (t u v x : R) (ht : t^2=0) :
    (1+t*v)^4*(1+(1+t*u)^2+(1+t*v)^2+t*x)^3 =
      27+t*(108*v+27*(2*u+2*v+x)) := by
  rw [nil_four t v ht, nil_sq t u ht, nil_sq t v ht]
  have hs : 1+(1+2*t*u)+(1+2*t*v)+t*x = 3+t*(2*u+2*v+x) := by ring
  rw [hs, nil_cube_three t (2*u+2*v+x) ht]
  calc
    (1+4*t*v)*(27+27*t*(2*u+2*v+x)) =
      27+t*(108*v+27*(2*u+2*v+x))+t^2*(108*v*(2*u+2*v+x)) := by ring
    _ = 27+t*(108*v+27*(2*u+2*v+x)) := by rw [ht, zero_mul, add_zero]

set_option maxHeartbeats 1000000 in
private lemma product_eq_27
    (q A B C D E F G I J K L Z a b c d e g i j k l z H5 : R)
    (hq : q^5=0)
    (hA : A=q^2*a) (hB : B=q*b) (hC : C=q^2*c) (hD : D=q*d)
    (hEo : E=q*e) (hG : G=q*g) (hI : I=q*i) (hJ : J=q^2*j)
    (hK : K=q*k) (hL : L=q*l) (hZ : Z=q*z)
    (hE : A^2=2*E+B)
    (hr : 2*A+q*B+q^2*C+q^3*D+q^4*H5=0)
    (ha : q^2*(A^2+3*B-2*q*(F+C)+2*q^2*(K+G))=0) :
    let U := 1+q*A+q^2*E+q^3*J+q^4*L
    let V := 1+2*q*A+4*q^2*E+8*q^3*J+16*q^4*L
    let X := 5*q^2*B + q^3*(10*F+8*A*B-8*C) +
      q^4*(9*Z+2*K-16*G-12*I+12*D+8*A^2*B+16*A*F-16*A*C-4*B^2)
    V^4*(1+U^2+V^2+X)^3 = 27 := by
  dsimp only
  have hU := series_reduce q a e j l 1 1 1 1 hq
  have hV := series_reduce q a e j l 2 4 8 16 hq
  simp only [one_pow, one_mul] at hU
  norm_num at hV
  have hX := x_reduce q a b c d F g i k z hq
  simp only [hA, hB, hC, hD, hEo, hG, hI, hJ, hK, hL, hZ] at hE hr ha ⊢
  rw [hU, hV, hX]
  have ht : (q^3)^2=0 := by
    rw [← pow_mul]
    change q^6 = 0
    rw [show q^6=q^5*q by exact pow_succ q 5, hq, zero_mul]
  rw [nil_product (q^3) (a+e) (2*a+4*e) (5*b+10*F) ht]
  have hz : q^3*(108*(2*a+4*e)+
      27*(2*(a+e)+2*(2*a+4*e)+(5*b+10*F)))=0 := by
    linear_combination 189*q*hr - 351*q^2*hE - 135*ha +
      (-459*c-189*d-189*H5+270*k+270*g+486*q*a^2)*hq
  rw [hz, add_zero]

end FinalAlgebra



section Decomposition
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)

private def squareSum : ℕ :=
  ∑ k ∈ range (2*p+1), ((p+k-1).choose k)^2

private lemma endpoint (c : ℕ) :
    (((((c+1)*p-1).choose (c*p)) : ℕ) : R5) = pp p c (p-1) := by
  have hp2 := hp.two_le
  have htot : (c+1)*p-1=c*p+(p-1) := by
    rw [add_mul, one_mul]
    exact add_pred_eq (c*p) hp.pos
  rw [htot]
  have heq := Nat.choose_symm (Nat.le_add_right (c*p) (p-1))
  rw [Nat.add_sub_cancel_left] at heq
  rw [← heq]
  simpa using choose_cp_eq_pp p hp c (k := p-1) (prime_pred_lt hp)

private lemma squareSum_decompose :
    (squareSum p : R5) = 1 + pp p 1 (p-1)^2 + pp p 2 (p-1)^2 + smallSum p (p-1) := by
  have hp2 := hp.two_le
  let f : ℕ → R5 := fun k => (((p+k-1).choose k : ℕ) : R5)^2
  have hcast : (squareSum p : R5) = ∑ k ∈ range (2*p+1), f k := by
    simp only [squareSum, Nat.cast_sum, Nat.cast_pow, f]
  have hmain : (∑ k ∈ range (2*p+1), f k) =
      (∑ k ∈ range p, f k) + ∑ k ∈ range (p+1), f (p+k) := by
    rw [show 2*p+1=p+(p+1) by simp [two_mul, Nat.add_assoc], sum_range_add]
  have hfirst : (∑ k ∈ range p, f k) =
      1 + ∑ k ∈ range (p-1), f (k+1) := by
    rw [show range p = range (1+(p-1)) by congr 1; rw [Nat.add_comm, pred_succ_eq hp.pos], sum_range_add]
    simp only [sum_range_one, f, Nat.choose_zero_right, Nat.cast_one, one_pow]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [Nat.add_comm 1 x]
  have hsecond : (∑ k ∈ range (p+1), f (p+k)) =
      f p + (∑ k ∈ range (p-1), f (p+(k+1))) + f (2*p) := by
    rw [sum_range_succ']
    simp only [add_zero]
    rw [show range p = range ((p-1)+1) by rw [pred_succ_eq hp.pos], sum_range_succ]
    have hend : f (p+((p-1)+1)) = f (2*p) := by
      congr 1
      rw [pred_succ_eq hp.pos, two_mul]
    rw [hend]
    ac_rfl
  have hmiddle : (∑ k ∈ range (p-1), f (k+1)) +
      (∑ k ∈ range (p-1), f (p+(k+1))) = smallSum p (p-1) := by
    rw [← sum_add_distrib]
    unfold smallSum
    apply Finset.sum_congr rfl
    intro k hk
    simp only [f, bb]
    rw [show p+(p+(k+1))-1 = 2*p+(k+1)-1 by rw [two_mul, Nat.add_assoc]]
  rw [hcast, hmain, hfirst, hsecond]
  rw [show f p = pp p 1 (p-1)^2 by
    simp only [f]
    rw [show p+p-1=2*p-1 by rw [two_mul]]
    exact congrArg (fun x : R5 => x^2) (by simpa only [Nat.cast_one, one_mul] using endpoint p hp 1)]
  rw [show f (2*p) = pp p 2 (p-1)^2 by
    simp only [f]
    rw [show p+2*p-1=3*p-1 by rw [show 3*p=p+2*p by rw [Nat.succ_mul, Nat.add_comm]]]
    exact congrArg (fun x : R5 => x^2) (by simpa only [Nat.cast_ofNat] using endpoint p hp 2)]
  rw [← hmiddle]
  ac_rfl

end Decomposition

section FinalAssembly
variable (p : ℕ) (hp : p.Prime)
include hp
local notation "R5" => ZMod (p^5)
local notation "q" => (p : R5)

private def firstSum : ℕ :=
  ∑ k ∈ range (2*p+1), (p+k-1).choose k

private lemma firstSum_eq_choose : firstSum p = (3*p).choose p := by
  unfold firstSum
  rw [show 2*p+1=2*p+1 by rfl]
  convert Nat.sum_range_multichoose (2*p) p using 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.multichoose_eq]
  · congr 1
    simp [Nat.succ_mul, two_mul, Nat.add_assoc]

private lemma choose_three_eq : (3*p).choose p = 3*((3*p-1).choose (p-1)) := by
  simpa using (Nat.choose_mul_right (m := 3) (n := p) hp.ne_zero)

set_option maxHeartbeats 1000000 in
private lemma main_zmod (hp7 : 7 ≤ p) :
    (firstSum p : R5)^4 * (squareSum p : R5)^3 = 2187 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let A : R5 := hs (R := R5) 1 (p-1)
  let B : R5 := hs (R := R5) 2 (p-1)
  let C : R5 := hs (R := R5) 3 (p-1)
  let D : R5 := hs (R := R5) 4 (p-1)
  let E : R5 := hh (R := R5) 1 1 (p-1)
  let F : R5 := hh (R := R5) 1 2 (p-1)
  let G : R5 := hh (R := R5) 1 3 (p-1)
  let I : R5 := hh (R := R5) 2 2 (p-1)
  let J : R5 := hhh (R := R5) 1 1 1 (p-1)
  let K : R5 := hhh (R := R5) 1 1 2 (p-1)
  let L : R5 := hhhh (R := R5) 1 1 1 1 (p-1)
  let Z : R5 := zsum p (p-1)
  obtain ⟨a, hA⟩ := hs_one_bigO_two p hp hp7
  obtain ⟨b, hB⟩ := hs_bigO_one p hp 2 (by decide) (small_lt_pred (by decide) hp7)
  obtain ⟨c, hC⟩ := hs_three_bigO_two p hp hp7
  obtain ⟨d, hD⟩ := hs_bigO_one p hp 4 (by decide) (small_lt_pred (by decide) hp7)
  obtain ⟨e, hEo⟩ := hh_one_one_bigO p hp hp7
  obtain ⟨g, hG⟩ := hh_one_three_bigO p hp hp7
  obtain ⟨i, hI⟩ := hh_two_two_bigO p hp hp7
  obtain ⟨j, hJ⟩ := hhh_one_bigO_two p hp hp7
  obtain ⟨k, hK⟩ := hhh_one_one_two_bigO p hp hp7
  obtain ⟨l, hL⟩ := hhhh_one_bigO p hp hp7
  obtain ⟨z, hZ⟩ := zsum_bigO p hp hp7
  simp only [pow_one] at hB hD hEo hG hI hK hL hZ
  have hq : q^5=0 := q_pow_five p
  have helem : A^2=2*E+B := by
    dsimp [A, E, B]
    exact hs_self_sq (R := R5) 1 (p-1)
  have href : 2*A+q*B+q^2*C+q^3*D+q^4*hs (R := R5) 5 (p-1)=0 := by
    simpa only [A, B, C, D] using reflect_hs_one p hp
  have halt : q^2*(A^2+3*B-2*q*(F+C)+2*q^2*(K+G))=0 := by
    simpa only [A, B, C, F, K, G] using key_alt_relation p hp
  have hprod := product_eq_27 q A B C D E F G I J K L Z a b c d e g i j k l z
    (hs (R := R5) 5 (p-1)) hq
    (by simpa only [A] using hA) (by simpa only [B] using hB)
    (by simpa only [C] using hC) (by simpa only [D] using hD)
    (by simpa only [E] using hEo) (by simpa only [G] using hG)
    (by simpa only [I] using hI) (by simpa only [J] using hJ)
    (by simpa only [K] using hK) (by simpa only [L] using hL)
    (by simpa only [Z] using hZ) helem href halt
  have hU := pp_expansion p (1 : R5) (p-1)
  have hV := pp_expansion p (2 : R5) (p-1)
  simp only [one_pow, one_mul] at hU
  norm_num at hV
  have hX := small_sum_expansion p hp (n := p-1) (prime_pred_lt hp)
  dsimp only [A, B, C, D, E, F, G, I, J, K, L, Z] at hprod
  rw [← hU, ← hV] at hprod
  have hX' : smallSum p (p-1) =
      5*q^2*hs (R := R5) 2 (p-1) +
      q^3*(10*hh (R := R5) 1 2 (p-1)+8*hs (R := R5) 1 (p-1)*hs (R := R5) 2 (p-1)-
        8*hs (R := R5) 3 (p-1)) +
      q^4*(9*zsum p (p-1)+2*hhh (R := R5) 1 1 2 (p-1)-16*hh (R := R5) 1 3 (p-1)-
        12*hh (R := R5) 2 2 (p-1)+12*hs (R := R5) 4 (p-1)+
        8*hs (R := R5) 1 (p-1)^2*hs (R := R5) 2 (p-1)+
        16*hs (R := R5) 1 (p-1)*hh (R := R5) 1 2 (p-1)-
        16*hs (R := R5) 1 (p-1)*hs (R := R5) 3 (p-1)-
        4*hs (R := R5) 2 (p-1)^2) := by
    simpa only [smallRhs, pow_two, mul_assoc] using hX
  rw [← hX'] at hprod
  rw [← squareSum_decompose p hp] at hprod
  have hfirst : (firstSum p : R5) = 3*pp p 2 (p-1) := by
    rw [firstSum_eq_choose p hp, choose_three_eq p hp]
    push_cast
    rw [show 3*p-1=2*p+(p-1) by simpa [show 3*p=2*p+p by rw [Nat.succ_mul]] using add_pred_eq (2*p) hp.pos]
    rw [choose_cp_eq_pp p hp 2 (k := p-1) (prime_pred_lt hp)]
    simp only [Nat.cast_ofNat]
  rw [hfirst]
  calc
    (3 * pp p 2 (p-1))^4 * (squareSum p : R5)^3 =
        81 * (pp p 2 (p-1)^4 * (squareSum p : R5)^3) := by
      rw [mul_pow]
      norm_num
      exact mul_assoc _ _ _
    _ = 81*27 := by rw [hprod]
    _ = 2187 := by norm_num

end FinalAssembly


/--
Conjecture 1: $a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  rcases lt_or_ge p 7 with hsmall | hp7
  · interval_cases p
    · decide
    · norm_num at hp
    · decide
    · norm_num at hp
  · rw [← ZMod.natCast_eq_natCast_iff]
    rw [show A357674 p = firstSum p ^ 4 * squareSum p ^ 3 by rfl]
    push_cast
    rw [main_zmod p hp hp7]
    norm_num [A357674]
