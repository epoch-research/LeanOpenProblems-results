import FormalConjectures.Util.ProblemImports
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open Nat

/--
A357569: $a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

open Nat Finset
open scoped BigOperators

namespace RatioNat

def nondivProd (p q : ℕ) (f : ℕ → ℕ) : ℕ :=
  ∏ k ∈ Finset.Ico 1 (q+1) with ¬ p ∣ k, f k


lemma prod_num_eq_factorial_mul_choose (c n : ℕ) (hc : 1 ≤ c) :
    (∏ k ∈ Finset.Ico 1 (n+1), ((c-1)*n+k)) = n.factorial * ((c*n).choose n) := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  rw [Nat.descFactorial_eq_prod_range]
  rw [Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]
  rw [← Finset.prod_range_reflect (fun i => ((c-1)*n+(1+i))) n]
  apply Finset.prod_congr rfl
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  have hbase : (c - 1) * n + n = c * n := by
    nth_rewrite 2 [← Nat.one_mul n]
    rw [← Nat.add_mul, Nat.sub_add_cancel hc]
  have hone : 1 + (n - 1 - i) = n - i := by omega
  rw [hone]
  omega

-- Try proving the denominator split: product of p-multiples in 1..p*q0 is p^q0*q0!
lemma prod_divisible_Ico (p q0 : ℕ) (hp : 0 < p) :
    (∏ k ∈ Finset.Ico 1 (p*q0+1) with p ∣ k, k) = p^q0 * q0.factorial := by
  classical
  -- use bijection l ↦ p*l from Ico 1 (q0+1)
  trans ∏ l ∈ Finset.Ico 1 (q0+1), p*l
  · apply Finset.prod_bij (fun k hk => k / p)
    · intro k hk
      simp only [mem_filter, mem_Ico] at hk ⊢
      rcases hk with ⟨⟨hk1,hkle⟩, hpk⟩
      constructor
      · exact Nat.succ_le_iff.mpr (Nat.div_pos (Nat.le_of_dvd hk1 hpk) hp)
      · have : k / p ≤ q0 := by
          exact Nat.div_le_of_le_mul (by nlinarith)
        omega
    · intro a ha b hb hab
      simp only [mem_filter, mem_Ico] at ha hb
      rcases ha with ⟨⟨ha1,ha2⟩, hpa⟩
      rcases hb with ⟨⟨hb1,hb2⟩, hpb⟩
      have haeq : a = p * (a / p) := Nat.eq_mul_of_div_eq_right hpa rfl
      have hbeq : b = p * (b / p) := Nat.eq_mul_of_div_eq_right hpb rfl
      rw [haeq, hbeq, hab]
    · intro l hl
      simp only [mem_Ico] at hl
      refine ⟨p*l, ?_, ?_⟩
      · simp only [mem_filter, mem_Ico]
        constructor
        · constructor
          · nlinarith [hl.1, hp]
          · nlinarith [hl.2]
        · exact dvd_mul_right p l
      · exact Nat.mul_div_right l hp
    · intro k hk
      simp only [mem_filter, mem_Ico] at hk
      rcases hk with ⟨_, hpk⟩
      rw [Nat.mul_div_cancel' hpk]
  · rw [Finset.prod_mul_distrib, Finset.prod_const]
    rw [Nat.card_Ico]
    rw [prod_Ico_id_eq_factorial]
    simp

lemma prod_divisible_num_Ico (p q0 c : ℕ) (hp : 0 < p) :
    (∏ k ∈ Finset.Ico 1 (p*q0+1) with p ∣ k, ((c-1)*(p*q0)+k)) =
      p^q0 * (∏ l ∈ Finset.Ico 1 (q0+1), ((c-1)*q0+l)) := by
  classical
  trans ∏ l ∈ Finset.Ico 1 (q0+1), ((c-1)*(p*q0)+p*l)
  · apply Finset.prod_bij (fun k hk => k / p)
    · intro k hk
      simp only [mem_filter, mem_Ico] at hk ⊢
      rcases hk with ⟨⟨hk1,hkle⟩, hpk⟩
      constructor
      · exact Nat.succ_le_iff.mpr (Nat.div_pos (Nat.le_of_dvd hk1 hpk) hp)
      · have : k / p ≤ q0 := by
          exact Nat.div_le_of_le_mul (by nlinarith)
        omega
    · intro a ha b hb hab
      simp only [mem_filter, mem_Ico] at ha hb
      rcases ha with ⟨⟨ha1,ha2⟩, hpa⟩
      rcases hb with ⟨⟨hb1,hb2⟩, hpb⟩
      have haeq : a = p * (a / p) := Nat.eq_mul_of_div_eq_right hpa rfl
      have hbeq : b = p * (b / p) := Nat.eq_mul_of_div_eq_right hpb rfl
      rw [haeq, hbeq, hab]
    · intro l hl
      simp only [mem_Ico] at hl
      refine ⟨p*l, ?_, ?_⟩
      · simp only [mem_filter, mem_Ico]
        constructor
        · constructor
          · nlinarith [hl.1, hp]
          · nlinarith [hl.2]
        · exact dvd_mul_right p l
      · exact Nat.mul_div_right l hp
    · intro k hk
      simp only [mem_filter, mem_Ico] at hk
      rcases hk with ⟨_, hpk⟩
      rw [Nat.mul_div_cancel' hpk]
  · trans ∏ l ∈ Finset.Ico 1 (q0+1), p * ((c-1)*q0+l)
    · apply Finset.prod_congr rfl
      intro l hl
      ring
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
      simp

lemma choose_mul_nondivProd_eq (p q0 c : ℕ) (hp : 0 < p) (hc : 1 ≤ c) :
    ((c*(p*q0)).choose (p*q0)) * nondivProd p (p*q0) (fun k => k) =
      ((c*q0).choose q0) * nondivProd p (p*q0) (fun k => (c-1)*(p*q0)+k) := by
  classical
  let q := p*q0
  have hden_split :
      (p^q0 * q0.factorial) * nondivProd p (p*q0) (fun k => k) = (p*q0).factorial := by
    rw [← prod_divisible_Ico p q0 hp]
    rw [nondivProd]
    have h := Finset.prod_filter_mul_prod_filter_not (s := Finset.Ico 1 (p*q0+1)) (p := fun k => p ∣ k) (f := fun k => k)
    simpa [mul_comm] using h
  have hnum_split :
      (p^q0 * (∏ l ∈ Finset.Ico 1 (q0+1), ((c-1)*q0+l))) *
        nondivProd p (p*q0) (fun k => (c-1)*(p*q0)+k) =
          ∏ k ∈ Finset.Ico 1 (p*q0+1), ((c-1)*(p*q0)+k) := by
    rw [← prod_divisible_num_Ico p q0 c hp]
    rw [nondivProd]
    have h := Finset.prod_filter_mul_prod_filter_not (s := Finset.Ico 1 (p*q0+1)) (p := fun k => p ∣ k) (f := fun k => (c-1)*(p*q0)+k)
    simpa [mul_comm] using h
  have htop := prod_num_eq_factorial_mul_choose c (p*q0) hc
  have hlow := prod_num_eq_factorial_mul_choose c q0 hc
  have hmain : (p^q0 * q0.factorial) * (((c*(p*q0)).choose (p*q0)) * nondivProd p (p*q0) (fun k => k)) =
      (p^q0 * q0.factorial) * (((c*q0).choose q0) * nondivProd p (p*q0) (fun k => (c-1)*(p*q0)+k)) := by
    calc
      (p^q0 * q0.factorial) * (((c*(p*q0)).choose (p*q0)) * nondivProd p (p*q0) (fun k => k))
          = ((p*q0).factorial * ((c*(p*q0)).choose (p*q0))) := by
              rw [← hden_split]; ring
      _ = (∏ k ∈ Finset.Ico 1 (p*q0+1), ((c-1)*(p*q0)+k)) := by
              rw [htop]
      _ = ((p^q0 * (∏ l ∈ Finset.Ico 1 (q0+1), ((c-1)*q0+l))) * nondivProd p (p*q0) (fun k => (c-1)*(p*q0)+k)) := by
              rw [hnum_split]
      _ = (p^q0 * q0.factorial) * (((c*q0).choose q0) * nondivProd p (p*q0) (fun k => (c-1)*(p*q0)+k)) := by
              rw [hlow]
              ring
  exact Nat.mul_left_cancel (by positivity : 0 < p^q0 * q0.factorial) hmain

lemma isUnit_nondivProd_zmod {p q N : ℕ} (hp : Nat.Prime p) :
    IsUnit ((nondivProd p q (fun k => k) : ZMod (p^N))) := by
  classical
  unfold nondivProd
  rw [Nat.cast_prod]
  rw [IsUnit.prod_iff]
  intro k hk
  simp only [mem_filter, mem_Ico] at hk
  rw [ZMod.isUnit_iff_coprime]
  have hcopkp : Nat.Coprime k p := by
    exact Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hk.2)
  exact hcopkp.pow_right N

lemma zmod_choose_ratio_num_inv (p q0 c N : ℕ) (hp : Nat.Prime p) (hc : 1 ≤ c) :
    (((c*(p*q0)).choose (p*q0) : ℕ) : ZMod (p^N)) =
      (((c*q0).choose q0 : ℕ) : ZMod (p^N)) *
        (((nondivProd p (p*q0) (fun k => (c-1)*(p*q0)+k) : ℕ) : ZMod (p^N)) *
          (((nondivProd p (p*q0) (fun k => k) : ℕ) : ZMod (p^N))⁻¹)) := by
  classical
  let D : ZMod (p^N) := ((nondivProd p (p*q0) (fun k => k) : ℕ) : ZMod (p^N))
  let Num : ZMod (p^N) := ((nondivProd p (p*q0) (fun k => (c-1)*(p*q0)+k) : ℕ) : ZMod (p^N))
  let Ctop : ZMod (p^N) := (((c*(p*q0)).choose (p*q0) : ℕ) : ZMod (p^N))
  let C0 : ZMod (p^N) := (((c*q0).choose q0 : ℕ) : ZMod (p^N))
  have hnat := choose_mul_nondivProd_eq p q0 c hp.pos hc
  have hcast : Ctop * D = C0 * Num := by
    dsimp [Ctop, D, C0, Num]
    norm_num [← Nat.cast_mul, hnat]
  have hDunit : IsUnit D := by
    dsimp [D]
    exact isUnit_nondivProd_zmod (p := p) (q := p*q0) (N := N) hp
  calc
    Ctop = Ctop * D * D⁻¹ := by rw [mul_assoc, ZMod.mul_inv_of_unit D hDunit, mul_one]
    _ = (C0 * Num) * D⁻¹ := by rw [hcast]
    _ = C0 * (Num * D⁻¹) := by ring





end RatioNat

open Nat Finset
open scoped BigOperators

def UprodR (p q N x : ℕ) : ZMod (p^N) :=
  ∏ k ∈ Finset.Ico 1 (q+1) with ¬ p ∣ k,
    (1 + (x : ZMod (p^N)) * (q : ZMod (p^N)) * (k : ZMod (p^N))⁻¹)

lemma zmod_isUnit_nat_of_not_dvd {p N k : ℕ} (hp : Nat.Prime p) (hk : ¬ p ∣ k) :
    IsUnit (k : ZMod (p^N)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hk)).pow_right N

lemma ratio_nondivProd_eq_UprodR (p q N x : ℕ) (hp : Nat.Prime p) :
    (((RatioNat.nondivProd p q (fun k => x*q+k) : ℕ) : ZMod (p^N)) *
      (((RatioNat.nondivProd p q (fun k => k) : ℕ) : ZMod (p^N))⁻¹)) = UprodR p q N x := by
  classical
  let R := ZMod (p^N)
  have hDinv : ((∏ k ∈ Finset.Ico 1 (q+1) with ¬ p ∣ k, (k : R))⁻¹)
      = ∏ k ∈ Finset.Ico 1 (q+1) with ¬ p ∣ k, ((k : R)⁻¹) := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro k hk
    simp only [mem_filter, mem_Ico] at hk
    exact ZMod.mul_inv_of_unit _ (zmod_isUnit_nat_of_not_dvd (p:=p) (N:=N) hp hk.2)
  unfold RatioNat.nondivProd UprodR
  simp only [Nat.cast_prod]
  rw [hDinv]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [mem_filter, mem_Ico] at hk
  have hkunit : IsUnit (k : R) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=N) hp hk.2
  rw [Nat.cast_add, Nat.cast_mul, add_mul, ZMod.mul_inv_of_unit _ hkunit]
  ring

lemma pow_succ_sub_one_eq (p r : ℕ) (hr : 1 ≤ r) : p * p^(r-1) = p^r := by
  cases r with
  | zero => omega
  | succ r =>
      have hs : r + 1 - 1 = r := by omega
      rw [hs, pow_succ, mul_comm]

lemma choose_ratio_UprodR (p r c N : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) (hc : 1 ≤ c) :
    (((c * p^r).choose (p^r) : ℕ) : ZMod (p^N)) =
      (((c * p^(r-1)).choose (p^(r-1)) : ℕ) : ZMod (p^N)) * UprodR p (p^r) N (c-1) := by
  have hq : p * p^(r-1) = p^r := pow_succ_sub_one_eq p r hr
  have hratio := RatioNat.zmod_choose_ratio_num_inv (p:=p) (q0:=p^(r-1)) (c:=c) (N:=N) hp hc
  have hU := ratio_nondivProd_eq_UprodR (p:=p) (q:=p^r) (N:=N) (x:=c-1) hp
  rw [hq] at hratio
  rw [hratio]
  rw [hU]

lemma zmod_natCast_pow_eq_zero_of_le (p N e : ℕ) (h : N ≤ e) :
    ((p : ZMod (p^N)) ^ e) = 0 := by
  rw [← Nat.cast_pow]
  rw [← Int.cast_natCast]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact_mod_cast pow_dvd_pow p h

lemma zmod_mul_pow_eq_zero_of_le (p N e : ℕ) (x : ZMod (p^N)) (h : N ≤ e) :
    ((p : ZMod (p^N)) ^ e) * x = 0 := by
  rw [zmod_natCast_pow_eq_zero_of_le p N e h, zero_mul]

open scoped BigOperators

lemma Finset.prod_one_add_eq_one_add_sum_of_pairwise_mul_zero
    {ι R : Type*} [DecidableEq ι] [CommSemiring R] (s : Finset ι) (f : ι → R)
    (hzero : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → f i * f j = 0) :
    ∏ i ∈ s, (1 + f i) = 1 + ∑ i ∈ s, f i := by
  classical
  revert hzero
  refine Finset.induction_on s ?base ?step
  · intro hzero; simp
  · intro a s has ih hzero
    have hzero_s : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → f i * f j = 0 := by
      intro i hi j hj hij
      exact hzero (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    have ha_sum_zero : f a * (∑ i ∈ s, f i) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact hzero (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) (by exact fun h => has (h ▸ hi))
    simp [has, ih hzero_s]
    have hmul : (1 + f a) * (∑ i ∈ s, f i) = ∑ i ∈ s, f i := by
      rw [add_mul, one_mul, ha_sum_zero, add_zero]
    rw [mul_add, mul_one, hmul]
    simp [add_assoc, add_comm, add_left_comm]


lemma paired_factor_identity (p q N x k : ℕ) (hp : Nat.Prime p)
    (hk : ¬ p ∣ k) (hkq : ¬ p ∣ q - k) (hk_le : k ≤ q) :
    let R := ZMod (p^N)
    (1 + (x : R) * (q : R) * (k : R)⁻¹) *
      (1 + (x : R) * (q : R) * ((q-k : ℕ) : R)⁻¹)
    = 1 + ((x * (x+1)) : R) * (q : R)^2 * (k : R)⁻¹ * ((q-k : ℕ) : R)⁻¹ := by
  intro R
  let a : R := ((q-k : ℕ) : R)
  let b : R := (k : R)
  have huk : IsUnit b := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=N) hp hk
  have huqk : IsUnit a := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=N) hp hkq
  have hsum_nat : k + (q-k) = q := Nat.add_sub_of_le hk_le
  have hsum : b + a = (q : R) := by
    dsimp [a,b]
    calc
      (k : R) + ((q-k : ℕ) : R) = ((k + (q-k) : ℕ) : R) := by rw [Nat.cast_add]
      _ = (q : R) := by rw [hsum_nat]
  have hb1 : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk
  have ha1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit _ huqk
  have hinvsum : (q : R) * (b⁻¹ + a⁻¹) = (q : R)^2 * b⁻¹ * a⁻¹ := by
    calc
      (q : R) * (b⁻¹ + a⁻¹) = (q : R) * ((a + b) * b⁻¹ * a⁻¹) := by
        congr 1
        calc
          b⁻¹ + a⁻¹ = (a * a⁻¹) * b⁻¹ + (b * b⁻¹) * a⁻¹ := by rw [ha1, hb1]; ring
          _ = (a + b) * b⁻¹ * a⁻¹ := by ring
      _ = (q : R) * ((q : R) * b⁻¹ * a⁻¹) := by rw [add_comm a b, hsum]
      _ = (q : R)^2 * b⁻¹ * a⁻¹ := by ring
  calc
    (1 + (x : R) * (q : R) * (k : R)⁻¹) *
      (1 + (x : R) * (q : R) * ((q-k : ℕ) : R)⁻¹)
      = (1 + (x : R) * (q : R) * b⁻¹) * (1 + (x : R) * (q : R) * a⁻¹) := by rfl
    _ = 1 + (x : R) * ((q : R) * (b⁻¹ + a⁻¹))
          + (x : R)^2 * (q : R)^2 * b⁻¹ * a⁻¹ := by ring
    _ = 1 + ((x : R) + (x : R)^2) * (q : R)^2 * b⁻¹ * a⁻¹ := by
          rw [hinvsum]
          ring
    _ = 1 + ((x * (x+1)) : R) * (q : R)^2 * b⁻¹ * a⁻¹ := by
          norm_num [Nat.cast_mul, Nat.cast_add]
          ring

open Finset
open scoped BigOperators

def nondivSet (p q : ℕ) : Finset ℕ :=
  Finset.Ico 1 (q+1) |>.filter (fun k => ¬ p ∣ k)

lemma nondivSet_mem {p q k : ℕ} : k ∈ nondivSet p q ↔ 1 ≤ k ∧ k < q+1 ∧ ¬ p ∣ k := by
  simp [nondivSet, and_assoc]

lemma nondivSet_invol_mem {p q k : ℕ} (hp : Nat.Prime p) (hq : q = p ^ r) (hrpos : 0 < r)
    (hk : k ∈ nondivSet p q) : q - k ∈ nondivSet p q := by
  rw [nondivSet_mem] at hk ⊢
  rcases hk with ⟨hk1, hklt, hnd⟩
  have hk_le_q : k ≤ q := Nat.lt_succ_iff.mp hklt
  have hp_dvd_q : p ∣ q := by
    rw [hq]
    exact dvd_pow_self p (Nat.ne_zero_of_lt hrpos)
  constructor
  · have hneq : k ≠ q := by
      intro h
      apply hnd
      rw [h]
      exact hp_dvd_q
    omega
  constructor
  · omega
  · intro hd
    apply hnd
    have : p ∣ q - (q-k) := Nat.dvd_sub hp_dvd_q hd
    simpa [Nat.sub_sub_self hk_le_q] using this

lemma nondivSet_invol_invol {p q k : ℕ} (hk : k ∈ nondivSet p q) : q - (q - k) = k := by
  rw [nondivSet_mem] at hk
  exact Nat.sub_sub_self (Nat.lt_succ_iff.mp hk.2.1)

lemma product_reindex_invol (p q r : ℕ) (hp : Nat.Prime p) (hq : q = p ^ r) (hrpos : 0 < r)
    {R : Type*} [CommMonoid R] (f : ℕ → R) :
    (∏ k ∈ nondivSet p q, f (q-k)) = ∏ k ∈ nondivSet p q, f k := by
  classical
  apply Finset.prod_bij (fun k _ => q-k)
  · intro k hk
    exact nondivSet_invol_mem (p:=p) (q:=q) (r:=r) hp hq hrpos hk
  · intro a ha b hb hab
    have hha := nondivSet_invol_invol (p:=p) (q:=q) (k:=a) ha
    have hhb := nondivSet_invol_invol (p:=p) (q:=q) (k:=b) hb
    calc
      a = q - (q-a) := hha.symm
      _ = q - (q-b) := by rw [hab]
      _ = b := hhb
  · intro b hb
    refine ⟨q-b, nondivSet_invol_mem (p:=p) (q:=q) (r:=r) hp hq hrpos hb, ?_⟩
    exact nondivSet_invol_invol (p:=p) (q:=q) (k:=b) hb
  · intro k hk
    rfl

lemma product_square_paired (p q r N x : ℕ) (hp : Nat.Prime p) (hq : q = p ^ r) (hrpos : 0 < r) :
    let R := ZMod (p^N)
    (∏ k ∈ nondivSet p q, (1 + (x : R) * (q : R) * (k : R)⁻¹)) ^ 2 =
      ∏ k ∈ nondivSet p q,
        (1 + ((x * (x+1)) : R) * (q : R)^2 * (k : R)⁻¹ * ((q-k : ℕ) : R)⁻¹) := by
  intro R
  classical
  let f : ℕ → R := fun k => (1 + (x : R) * (q : R) * (k : R)⁻¹)
  calc
    (∏ k ∈ nondivSet p q, (1 + (x : R) * (q : R) * (k : R)⁻¹)) ^ 2
        = (∏ k ∈ nondivSet p q, f k) * (∏ k ∈ nondivSet p q, f k) := by simp [pow_two, f]
    _ = (∏ k ∈ nondivSet p q, f k) * (∏ k ∈ nondivSet p q, f (q-k)) := by
          rw [product_reindex_invol (p:=p) (q:=q) (r:=r) hp hq hrpos f]
    _ = ∏ k ∈ nondivSet p q, f k * f (q-k) := by rw [Finset.prod_mul_distrib]
    _ = ∏ k ∈ nondivSet p q,
        (1 + ((x * (x+1)) : R) * (q : R)^2 * (k : R)⁻¹ * ((q-k : ℕ) : R)⁻¹) := by
          apply Finset.prod_congr rfl
          intro k hk
          rw [nondivSet_mem] at hk
          have hkqmem : q - k ∈ nondivSet p q := nondivSet_invol_mem (p:=p) (q:=q) (r:=r) hp hq hrpos (by rwa [nondivSet_mem])
          rw [nondivSet_mem] at hkqmem
          exact paired_factor_identity (p:=p) (q:=q) (N:=N) (x:=x) (k:=k) hp hk.2.2 hkqmem.2.2 (Nat.lt_succ_iff.mp hk.2.1)

lemma paired_perturb_mul_zero_of_r_ge_three (p q r c k l : ℕ) (hr3 : 3 ≤ r) (hq : q = p^r) :
    let R := ZMod (p^(3*r+3))
    (((c : R) * (q : R)^2 * (k : R)⁻¹ * ((q-k : ℕ) : R)⁻¹) *
      ((c : R) * (q : R)^2 * (l : R)⁻¹ * ((q-l : ℕ) : R)⁻¹)) = 0 := by
  intro R
  have hq4 : (q : R)^4 = 0 := by
    rw [hq, Nat.cast_pow]
    change ((p : R)^r)^4 = 0
    rw [← pow_mul]
    change ((p : R) ^ (r*4)) = 0
    apply zmod_natCast_pow_eq_zero_of_le
    omega
  calc
    ((c : R) * (q : R)^2 * (k : R)⁻¹ * ((q-k : ℕ) : R)⁻¹) *
      ((c : R) * (q : R)^2 * (l : R)⁻¹ * ((q-l : ℕ) : R)⁻¹)
      = (q : R)^4 * (((c : R) * (k : R)⁻¹ * ((q-k : ℕ) : R)⁻¹) * ((c : R) * (l : R)⁻¹ * ((q-l : ℕ) : R)⁻¹)) := by ring
    _ = 0 := by rw [hq4, zero_mul]

lemma paired_product_linear_of_r_ge_three (p q r c : ℕ) (hr3 : 3 ≤ r) (hq : q = p^r) :
    let R := ZMod (p^(3*r+3))
    (∏ k ∈ nondivSet p q,
        (1 + (c : R) * (q : R)^2 * (k : R)⁻¹ * ((q-k : ℕ) : R)⁻¹))
      = 1 + ∑ k ∈ nondivSet p q,
        ((c : R) * (q : R)^2 * (k : R)⁻¹ * ((q-k : ℕ) : R)⁻¹) := by
  intro R
  classical
  apply Finset.prod_one_add_eq_one_add_sum_of_pairwise_mul_zero
  intro i hi j hj hij
  exact paired_perturb_mul_zero_of_r_ge_three (p:=p) (q:=q) (r:=r) (c:=c) (k:=i) (l:=j) hr3 hq

def Uprod (p q N x : ℕ) : ZMod (p^N) :=
  ∏ k ∈ nondivSet p q, (1 + (x : ZMod (p^N)) * (q : ZMod (p^N)) * (k : ZMod (p^N))⁻¹)

lemma Uprod_square_relation_r_ge_three (p q r : ℕ) (hp : Nat.Prime p)
    (hrpos : 0 < r) (hr3 : 3 ≤ r) (hq : q = p^r) :
    let R := ZMod (p^(3*r+3))
    (Uprod p q (3*r+3) 2 : R)^2 - 1 = 3 * ((Uprod p q (3*r+3) 1 : R)^2 - 1) := by
  intro R
  have h2 := product_square_paired (p:=p) (q:=q) (r:=r) (N:=3*r+3) (x:=2) hp hq hrpos
  have h1 := product_square_paired (p:=p) (q:=q) (r:=r) (N:=3*r+3) (x:=1) hp hq hrpos
  have lin6 := paired_product_linear_of_r_ge_three (p:=p) (q:=q) (r:=r) (c:=6) hr3 hq
  have lin2 := paired_product_linear_of_r_ge_three (p:=p) (q:=q) (r:=r) (c:=2) hr3 hq
  dsimp [Uprod]
  dsimp at h2 h1 lin6 lin2
  rw [h2, h1]
  norm_num at lin6 lin2 ⊢
  rw [lin6, lin2]
  simp only [add_sub_cancel_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring
open scoped BigOperators

lemma sum_units_inv_zmod_eq_zero (p k : ℕ) [NeZero (p^k)] (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    (∑ u : (ZMod (p^k))ˣ, ((u⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))) = 0 := by
  classical
  have h2not : ¬ p ∣ 2 := by
    intro h
    have hp_le_2 := Nat.le_of_dvd (by norm_num) h
    omega
  have hcop2p : Nat.Coprime 2 p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr h2not)
  have hcop2 : Nat.Coprime 2 (p^k) := hcop2p.pow_right k
  let R := ZMod (p^k)
  let t : (ZMod (p^k))ˣ := ZMod.unitOfCoprime 2 hcop2
  have ht : ((t : (ZMod (p^k))ˣ) : ZMod (p^k)) = (2 : ZMod (p^k)) := by
    simp [t, ZMod.coe_unitOfCoprime]
  let S : ZMod (p^k) := ∑ u : (ZMod (p^k))ˣ, ((u⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))
  have hperm : S = ∑ u : (ZMod (p^k))ˣ, (((t * u)⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k)) := by
    dsimp [S]
    let e : (ZMod (p^k))ˣ ≃ (ZMod (p^k))ˣ := Equiv.mulLeft t
    have h := Fintype.sum_equiv e
      (fun u : (ZMod (p^k))ˣ => ((((t * u)⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))))
      (fun u : (ZMod (p^k))ˣ => (((u⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))))
      (by intro u; rfl)
    exact h.symm
  have hscale : (∑ u : (ZMod (p^k))ˣ, (((t * u)⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k)))
      = ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k)) * S := by
    dsimp [S]
    simp only [mul_inv_rev, Units.val_mul, Finset.mul_sum]
    simp [mul_comm, mul_assoc]
  have hS : S = ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k)) * S := hperm.trans hscale
  have hunit_factor : IsUnit (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))) := by
    have hcalc : (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))) * ((t : (ZMod (p^k))ˣ) : ZMod (p^k)) = 1 := by
      rw [sub_mul, one_mul]
      simp only [← Units.val_mul]
      rw [inv_mul_cancel]
      change (((t : (ZMod (p^k))ˣ) : ZMod (p^k)) - 1 = 1)
      rw [ht]
      norm_num
    exact IsUnit.of_mul_eq_one _ hcalc
  have hz : (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))) * S = 0 := by
    calc (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))) * S
      _ = S - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k)) * S := by ring
      _ = 0 := by
        nth_rewrite 1 [hS]
        rw [sub_self]
  exact (IsUnit.mul_right_eq_zero hunit_factor).mp hz
open scoped BigOperators

lemma sum_units_inv_sq_zmod_eq_zero (p k : ℕ) [NeZero (p^k)] (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    (∑ u : (ZMod (p^k))ˣ, ((u⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) = 0 := by
  classical
  have h2not : ¬ p ∣ 2 := by
    intro h
    have hp_le_2 := Nat.le_of_dvd (by norm_num) h
    omega
  have hcop2p : Nat.Coprime 2 p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr h2not)
  have hcop2 : Nat.Coprime 2 (p^k) := hcop2p.pow_right k
  let R := ZMod (p^k)
  let t : (ZMod (p^k))ˣ := ZMod.unitOfCoprime 2 hcop2
  have ht : ((t : (ZMod (p^k))ˣ) : ZMod (p^k)) = (2 : ZMod (p^k)) := by
    simp [t, ZMod.coe_unitOfCoprime]
  let S : ZMod (p^k) := ∑ u : (ZMod (p^k))ˣ, ((u⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2
  have hperm : S = ∑ u : (ZMod (p^k))ˣ, (((t * u)⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2 := by
    dsimp [S]
    let e : (ZMod (p^k))ˣ ≃ (ZMod (p^k))ˣ := Equiv.mulLeft t
    have h := Fintype.sum_equiv e
      (fun u : (ZMod (p^k))ˣ => ((((t * u)⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2))
      (fun u : (ZMod (p^k))ˣ => (((u⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2))
      (by intro u; rfl)
    exact h.symm
  have hscale : (∑ u : (ZMod (p^k))ˣ, (((t * u)⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2)
      = ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2 * S := by
    dsimp [S]
    simp only [mul_inv_rev, Units.val_mul, Finset.mul_sum]
    simp [mul_pow, mul_comm, mul_left_comm, mul_assoc]
  have hS : S = ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2 * S := hperm.trans hscale
  have hunit_factor : IsUnit (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) := by
    have h3not : ¬ p ∣ 3 := by
      intro h
      have hp_le_3 := Nat.le_of_dvd (by norm_num) h
      omega
    have hcop3p : Nat.Coprime 3 p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr h3not)
    have hcop3 : Nat.Coprime 3 (p^k) := hcop3p.pow_right k
    have hunit3 : IsUnit (3 : ZMod (p^k)) := (ZMod.isUnit_iff_coprime 3 (p^k)).2 hcop3
    -- multiply by unit 4 to get 3
    have hcalc : (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) * ((t : (ZMod (p^k))ˣ) : ZMod (p^k))^2 = 3 := by
      rw [sub_mul, one_mul]
      simp only [← Units.val_pow_eq_pow_val, ← Units.val_mul]
      have htinvsq : (t⁻¹ : (ZMod (p^k))ˣ)^2 * t^2 = 1 := by
        rw [← mul_pow, inv_mul_cancel, one_pow]
      rw [htinvsq]
      change (((t : (ZMod (p^k))ˣ) : ZMod (p^k)) ^ 2 - 1 = 3)
      rw [ht]
      norm_num
    have hunit_t2 : IsUnit (((t : (ZMod (p^k))ˣ) : ZMod (p^k))^2) := (t^2).isUnit
    exact (IsUnit.mul_iff.mp (by rw [hcalc]; exact hunit3)).1
  have hz : (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) * S = 0 := by
    calc (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) * S
      _ = S - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2 * S := by ring
      _ = 0 := by
        nth_rewrite 1 [hS]
        rw [sub_self]
  exact (IsUnit.mul_right_eq_zero hunit_factor).mp hz
open scoped BigOperators

lemma Finset.prod_one_add_eq_sum_powersetCard_le_two_of_large_zero
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (f : ι → R)
    (hzero : ∀ t, t ⊆ s → 3 ≤ t.card → (∏ i ∈ t, f i) = 0) :
    ∏ i ∈ s, (1 + f i) =
      (∑ t ∈ s.powersetCard 0, ∏ i ∈ t, f i) +
      (∑ t ∈ s.powersetCard 1, ∏ i ∈ t, f i) +
      (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i) := by
  classical
  rw [Finset.prod_one_add]
  -- Need partition powerset by cardinality 0,1,2,>=3.
  rw [← Finset.sum_filter_add_sum_filter_not (s := s.powerset) (p := fun t => t.card ≤ 2) (f := fun t => ∏ i ∈ t, f i)]
  have hlarge : (∑ x ∈ s.powerset.filter (fun t => ¬ t.card ≤ 2), ∏ i ∈ x, f i) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [mem_filter, mem_powerset] at ht
    exact hzero t ht.1 (by omega)
  rw [hlarge, add_zero]
  -- split card≤2 into card=0,1,2
  have hsplit : (s.powerset.filter (fun t => t.card ≤ 2)) =
      (s.powersetCard 0) ∪ (s.powersetCard 1) ∪ (s.powersetCard 2) := by
    ext t
    simp only [mem_filter, mem_powerset, mem_union, mem_powersetCard]
    constructor
    · intro h
      have hc : t.card = 0 ∨ t.card = 1 ∨ t.card = 2 := by omega
      rcases hc with h0 | h1 | h2
      · exact Or.inl (Or.inl ⟨h.1, h0⟩)
      · exact Or.inl (Or.inr ⟨h.1, h1⟩)
      · exact Or.inr ⟨h.1, h2⟩
    · intro h
      rcases h with h01 | h2
      · rcases h01 with h0 | h1
        · exact ⟨h0.1, by omega⟩
        · exact ⟨h1.1, by omega⟩
      · exact ⟨h2.1, by omega⟩
  rw [hsplit]
  -- disjointness allows sum over unions
  have hd01 : Disjoint (s.powersetCard 0) (s.powersetCard 1) := by
    rw [Finset.disjoint_left]
    intro t ht0 ht1
    simp only [mem_powersetCard] at ht0 ht1
    omega
  have hd012 : Disjoint ((s.powersetCard 0) ∪ (s.powersetCard 1)) (s.powersetCard 2) := by
    rw [Finset.disjoint_left]
    intro t ht ht2
    simp only [mem_union, mem_powersetCard] at ht ht2
    rcases ht with ht0 | ht1 <;> omega
  rw [Finset.sum_union hd012, Finset.sum_union hd01]

lemma Finset.sum_powersetCard_zero_prod {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (f : ι → R) :
    (∑ t ∈ s.powersetCard 0, ∏ i ∈ t, f i) = 1 := by
  classical
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro b hb hbne
    simp only [mem_powersetCard] at hb
    exact False.elim (hbne (Finset.card_eq_zero.mp hb.2))
  · intro h
    simp at h

lemma Finset.sum_powersetCard_one_prod {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (f : ι → R) :
    (∑ t ∈ s.powersetCard 1, ∏ i ∈ t, f i) = ∑ i ∈ s, f i := by
  classical
  symm
  apply Finset.sum_bij (fun i _ => {i})
  · intro i hi
    simp [hi]
  · intro a ha b hb h
    simpa using congrArg (fun t : Finset ι => a ∈ t) h
  · intro t ht
    simp only [mem_powersetCard] at ht
    rcases Finset.card_eq_one.mp ht.2 with ⟨i, rfl⟩
    simp only [singleton_subset_iff] at ht
    exact ⟨i, ht.1, by simp⟩
  · intro i hi
    simp
open scoped BigOperators


lemma sum_sq_eq_diag_add_offdiag {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i)^2 =
      (∑ i ∈ s, (f i)^2) + (∑ p ∈ s.offDiag, f p.1 * f p.2) := by
  classical
  calc
    (∑ i ∈ s, f i)^2 = (∑ i ∈ s, f i) * (∑ j ∈ s, f j) := by rw [pow_two]
    _ = ∑ p ∈ s ×ˢ s, f p.1 * f p.2 := by
      rw [Finset.sum_product]
      simp [Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    _ = ∑ p ∈ s.diag ∪ s.offDiag, f p.1 * f p.2 := by rw [Finset.diag_union_offDiag]
    _ = (∑ p ∈ s.diag, f p.1 * f p.2) + (∑ p ∈ s.offDiag, f p.1 * f p.2) := by
      rw [Finset.sum_union (Finset.disjoint_diag_offDiag s)]
    _ = (∑ i ∈ s, (f i)^2) + (∑ p ∈ s.offDiag, f p.1 * f p.2) := by
      rw [Finset.sum_diag]
      simp [pow_two]
open scoped BigOperators

lemma offdiag_sum_eq_two_pairs {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (f : ι → R) :
    (∑ p ∈ s.offDiag, f p.1 * f p.2) =
      (2 : R) * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · rw [Finset.powersetCard_eq_empty.mpr (by simp : (∅ : Finset ι).card < 2)]
    simp
  · intro a s has ih
    rw [Finset.offDiag_insert has]
    have hd1 : Disjoint s.offDiag ({a} ×ˢ s) := by
      rw [Finset.disjoint_left]
      intro p hp hpa
      rw [Finset.mem_offDiag] at hp
      simp at hpa
      rcases hpa with ⟨b, hb, rfl⟩
      exact has hp.1
    have hd2 : Disjoint (s.offDiag ∪ ({a} ×ˢ s)) (s ×ˢ {a}) := by
      rw [Finset.disjoint_left]
      intro p hp hpsa
      simp at hp hpsa
      rcases hpsa with ⟨b, hb, rfl⟩
      rcases hp with hoff | hasp
      · exact has hoff.2.1
      · rcases hasp with ⟨c, hc, hp_eq⟩
        injection hp_eq with h1 h2
        exact has (h1 ▸ hb)
    rw [Finset.sum_union hd2, Finset.sum_union hd1]
    rw [ih]
    -- evaluate the two cross products
    have hcross1 : (∑ p ∈ {a} ×ˢ s, f p.1 * f p.2) = f a * ∑ i ∈ s, f i := by
      rw [Finset.sum_product]
      simp [Finset.mul_sum]
    have hcross2 : (∑ p ∈ s ×ˢ {a}, f p.1 * f p.2) = (∑ i ∈ s, f i) * f a := by
      rw [Finset.sum_product]
      simp [Finset.sum_mul]
    rw [hcross1, hcross2]
    -- powersetCard 2 insert = old pairs plus image singleton insert over old elements
    rw [Finset.powersetCard_succ_insert has 1]
    have hdpc : Disjoint (s.powersetCard 2) (Finset.image (insert a) (s.powersetCard 1)) := by
      rw [Finset.disjoint_left]
      intro t ht him
      rcases Finset.mem_image.mp him with ⟨u, hu, rfl⟩
      simp only [Finset.mem_powersetCard] at ht hu
      have : a ∈ insert a u := by simp
      exact has (ht.1 this)
    rw [Finset.sum_union hdpc]
    have himage : (∑ t ∈ Finset.image (insert a) (s.powersetCard 1), ∏ i ∈ t, f i) = f a * ∑ i ∈ s, f i := by
      rw [Finset.sum_image]
      · -- sum over singletons in s
        have hsingle : (∑ u ∈ s.powersetCard 1, ∏ i ∈ insert a u, f i) = ∑ i ∈ s, f a * f i := by
          symm
          apply Finset.sum_bij (fun i _ => {i})
          · intro i hi
            simp [hi]
          · intro i hi j hj h
            simpa using congrArg (fun t : Finset ι => i ∈ t) h
          · intro u hu
            simp only [Finset.mem_powersetCard] at hu
            rcases Finset.card_eq_one.mp hu.2 with ⟨i, rfl⟩
            exact ⟨i, hu.1 (by simp), by simp⟩
          · intro i hi
            have hne : a ≠ i := fun h => has (h ▸ hi)
            simp [hne]
        rw [hsingle]
        rw [Finset.mul_sum]
      · intro u hu v hv h
        -- insert a is injective on subsets not containing a; powersetCard subsets of s don't contain a
        have hua : a ∉ u := by
          intro hau
          exact has ((Finset.mem_powersetCard.mp hu).1 hau)
        have hva : a ∉ v := by
          intro hav
          exact has ((Finset.mem_powersetCard.mp hv).1 hav)
        apply Finset.ext
        intro x
        by_cases hx : x = a
        · subst x
          simp [hua, hva]
        · have hmem := congrArg (fun t : Finset ι => x ∈ t) h
          simpa [hx] using hmem
    rw [himage]
    ring
open scoped BigOperators


lemma pair_sum_zero_of_sum_and_sq_zero {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (f : ι → R) (h2 : IsUnit (2 : R))
    (hsum : (∑ i ∈ s, f i) = 0)
    (hsq : (∑ i ∈ s, (f i)^2) = 0) :
    (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i) = 0 := by
  have hsquare := sum_sq_eq_diag_add_offdiag s f
  rw [hsum, zero_pow (by norm_num : (2:ℕ) ≠ 0), hsq, zero_add] at hsquare
  have hoff : (∑ p ∈ s.offDiag, f p.1 * f p.2) = 0 := hsquare.symm
  have hdouble := offdiag_sum_eq_two_pairs s f
  rw [hoff] at hdouble
  have hmul : (2 : R) * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i) = 0 := hdouble.symm
  rw [mul_comm] at hmul
  exact (IsUnit.mul_left_eq_zero h2).mp hmul

lemma Finset.prod_one_add_eq_one_of_sum_sq_and_triple_zero
    {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (f : ι → R) (h2 : IsUnit (2 : R))
    (hsum : (∑ i ∈ s, f i) = 0)
    (hsq : (∑ i ∈ s, (f i)^2) = 0)
    (htriple : ∀ t, t ⊆ s → 3 ≤ t.card → (∏ i ∈ t, f i) = 0) :
    ∏ i ∈ s, (1 + f i) = 1 := by
  rw [Finset.prod_one_add_eq_sum_powersetCard_le_two_of_large_zero s f htriple]
  rw [Finset.sum_powersetCard_zero_prod]
  rw [Finset.sum_powersetCard_one_prod, hsum]
  have hpairs := pair_sum_zero_of_sum_and_sq_zero s f h2 hsum hsq
  rw [hpairs]
  ring

lemma final_from_ratio_algebra {R : Type*} [CommRing R]
    (A A0 B B0 u v : R)
    (hA : A = A0 * u) (hB : B = B0 * v)
    (hrel : u^2 - 1 = 6 * (v - 1))
    (hcoeff : (6 * A0^2 - 27 * B0) * (v - 1) = 0) :
    A^2 - 27 * B = A0^2 - 27 * B0 := by
  subst A
  subst B
  have hdiff : (A0 * u)^2 - 27 * (B0 * v) - (A0^2 - 27 * B0) = 0 := by
    calc
      (A0 * u)^2 - 27 * (B0 * v) - (A0^2 - 27 * B0)
          = A0^2 * (u^2 - 1) - 27 * B0 * (v - 1) := by ring
      _ = (6 * A0^2 - 27 * B0) * (v - 1) := by rw [hrel]; ring
      _ = 0 := hcoeff
  exact sub_eq_zero.mp hdiff

lemma square_relation_to_linear {R : Type*} [CommRing R] (u v : R)
    (hv_nil : (v - 1)^2 = 0)
    (hrel : u^2 - 1 = 3 * (v^2 - 1)) :
    u^2 - 1 = 6 * (v - 1) := by
  have hv_lin : v^2 - 1 = 2 * (v - 1) := by
    calc
      v^2 - 1 = (v - 1)^2 + 2 * (v - 1) := by ring
      _ = 2 * (v - 1) := by rw [hv_nil, zero_add]
  rw [hrel, hv_lin]
  ring

lemma nondiv_coprime_pow {p r k : ℕ} (hp : Nat.Prime p) (hk : ¬ p ∣ k) : Nat.Coprime k (p^r) := by
  exact (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hk)).pow_right r

lemma sum_nondiv_inv_sq_zmod_eq_units_sum' (p r : ℕ) [NeZero (p^r)] (hp : Nat.Prime p) (hrpos : 0 < r) :
    (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^r))⁻¹)^2)
    = (∑ u : (ZMod (p^r))ˣ, ((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2) := by
  classical
  let f : ℕ → ZMod (p^r) := fun k => ((k : ZMod (p^r))⁻¹)^2
  let g : (ZMod (p^r))ˣ → ZMod (p^r) := fun u => ((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2
  symm
  have hb : (∑ u ∈ (Finset.univ : Finset (ZMod (p^r))ˣ), g u) = ∑ k ∈ nondivSet p (p^r), f k := by
    refine Finset.sum_bij (s := (Finset.univ : Finset (ZMod (p^r))ˣ)) (t := nondivSet p (p^r)) (f := g) (g := f) (fun u _ => (u : ZMod (p^r)).val) ?_ ?_ ?_ ?_
    · intro u hu
      rw [nondivSet_mem]
      have hlt := (u : ZMod (p^r)).val_lt
      have hcop := ZMod.val_coe_unit_coprime u
      have hpos : 1 ≤ (u : ZMod (p^r)).val := by
        have hne : (u : ZMod (p^r)).val ≠ 0 := by
          intro h0
          have hcop0 : Nat.Coprime 0 (p^r) := by simpa [h0] using hcop
          have hp_dvd_pow : p ∣ p^r := by exact dvd_pow_self p (Nat.ne_zero_of_lt hrpos)
          rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_zero_left] at hcop0
          exact hp.not_dvd_one (by rwa [hcop0] at hp_dvd_pow)
        omega
      constructor
      · exact hpos
      constructor
      · exact Nat.lt_succ_of_lt hlt
      · intro hd
        have hpcop : Nat.Coprime p (p^r) := hcop.coprime_dvd_left hd
        have hp_dvd : p ∣ p^r := by exact dvd_pow_self p (Nat.ne_zero_of_lt hrpos)
        exact ((hp.coprime_iff_not_dvd).mp hpcop) hp_dvd
    · intro u1 hu1 u2 hu2 hval
      apply Units.ext
      rw [← ZMod.natCast_zmod_val (u1 : ZMod (p^r)), ← ZMod.natCast_zmod_val (u2 : ZMod (p^r))]
      exact congr_arg (fun n : ℕ => (n : ZMod (p^r))) hval
    · intro k hk
      rw [nondivSet_mem] at hk
      let u : (ZMod (p^r))ˣ := ZMod.unitOfCoprime k (nondiv_coprime_pow (p:=p) (r:=r) hp hk.2.2)
      refine ⟨u, Finset.mem_univ u, ?_⟩
      dsimp [u]
      have hklt : k < p^r := by
        have hneq : k ≠ p^r := by
          intro h
          exact hk.2.2 (by rw [h]; exact dvd_pow_self p (Nat.ne_zero_of_lt hrpos))
        omega
      rw [ZMod.val_natCast_of_lt hklt]
    · intro u hu
      dsimp [f,g]
      rw [← ZMod.natCast_zmod_val (u : ZMod (p^r))]
      simp [ZMod.inv_coe_unit]
  simpa using hb

lemma sum_nondiv_inv_sq_zmod_eq_zero' (p r : ℕ) [NeZero (p^r)] (hp : Nat.Prime p) (hp5 : p ≥ 5) (hrpos : 0 < r) :
    (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^r))⁻¹)^2) = 0 := by
  rw [sum_nondiv_inv_sq_zmod_eq_units_sum' (p:=p) (r:=r) hp hrpos]
  exact sum_units_inv_sq_zmod_eq_zero p r hp hp5

lemma zmod_pow_kernel_mul_zero (p r : ℕ) (x : ZMod (p^(2*r)))
    (h : ZMod.castHom (show p^r ∣ p^(2*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^r)) x = 0) :
    (p^r : ZMod (p^(2*r))) * x = 0 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simp only [map_intCast] at h
  have hzdiv : ((p^r : ℕ) : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z (p^r)).mp h
  rcases hzdiv with ⟨t, ht⟩
  rw [ht]
  norm_num [Int.cast_mul]
  rw [← mul_assoc]
  have hpp : ((p : ZMod (p^(2*r)))^r) * ((p : ZMod (p^(2*r)))^r) = 0 := by
    rw [← pow_add]
    apply zmod_natCast_pow_eq_zero_of_le
    omega
  simpa [Nat.cast_pow] using congrArg (fun y : ZMod (p^(2*r)) => y * (t : ZMod (p^(2*r)))) hpp

lemma castHom_inv_nat_of_not_dvd (p r k : ℕ) (hp : Nat.Prime p) (hk : ¬ p ∣ k) :
    ZMod.castHom (show p^r ∣ p^(2*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^r)) (((k : ZMod (p^(2*r)))⁻¹))
      = ((k : ZMod (p^r))⁻¹) := by
  let phi : ZMod (p^(2*r)) →+* ZMod (p^r) :=
    ZMod.castHom (show p^r ∣ p^(2*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^r))
  have huR : IsUnit (k : ZMod (p^(2*r))) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=2*r) hp hk
  have hkmap : phi (k : ZMod (p^(2*r))) = (k : ZMod (p^r)) := by simp [phi]
  have hmul : phi (((k : ZMod (p^(2*r)))⁻¹)) * (k : ZMod (p^r)) = 1 := by
    rw [← hkmap, ← map_mul, ZMod.inv_mul_of_unit _ huR, map_one]
  have hmul' : (k : ZMod (p^r)) * phi (((k : ZMod (p^(2*r)))⁻¹)) = 1 := by
    rw [mul_comm, hmul]
  exact (ZMod.inv_eq_of_mul_eq_one (p^r) (k : ZMod (p^r)) (phi (((k : ZMod (p^(2*r)))⁻¹))) hmul').symm

lemma castHom_sum_inv_sq_nondiv (p r : ℕ) (hp : Nat.Prime p) :
    ZMod.castHom (show p^r ∣ p^(2*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^r))
      (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^(2*r)))⁻¹)^2)
    = (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^r))⁻¹)^2) := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_pow]
  rw [castHom_inv_nat_of_not_dvd (p:=p) (r:=r) (k:=k) (hp:=hp) (hk:=(nondivSet_mem.mp hk).2.2)]

lemma p_pow_mul_sum_inv_sq_nondiv_eq_zero (p r : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hrpos : 0 < r) :
    (p^r : ZMod (p^(2*r))) *
      (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^(2*r)))⁻¹)^2) = 0 := by
  classical
  haveI : NeZero (p^r) := ⟨pow_ne_zero r hp.ne_zero⟩
  apply zmod_pow_kernel_mul_zero (p:=p) (r:=r)
  rw [castHom_sum_inv_sq_nondiv (p:=p) (r:=r) hp]
  exact sum_nondiv_inv_sq_zmod_eq_zero' (p:=p) (r:=r) hp hp5 hrpos

lemma sum_reindex_invol (p q r : ℕ) (hp : Nat.Prime p) (hq : q = p ^ r) (hrpos : 0 < r)
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ k ∈ nondivSet p q, f (q-k)) = ∑ k ∈ nondivSet p q, f k := by
  classical
  apply Finset.sum_bij (fun k _ => q-k)
  · intro k hk
    exact nondivSet_invol_mem (p:=p) (q:=q) (r:=r) hp hq hrpos hk
  · intro a ha b hb hab
    have hha := nondivSet_invol_invol (p:=p) (q:=q) (k:=a) ha
    have hhb := nondivSet_invol_invol (p:=p) (q:=q) (k:=b) hb
    calc
      a = q - (q-a) := hha.symm
      _ = q - (q-b) := by rw [hab]
      _ = b := hhb
  · intro b hb
    refine ⟨q-b, nondivSet_invol_mem (p:=p) (q:=q) (r:=r) hp hq hrpos hb, ?_⟩
    exact nondivSet_invol_invol (p:=p) (q:=q) (k:=b) hb
  · intro k hk
    rfl

lemma inv_add_inv_pair_eq (p r k : ℕ) (hp : Nat.Prime p) (hrpos : 0 < r)
    (hk : k ∈ nondivSet p (p^r)) :
    let R := ZMod (p^(2*r))
    ((k : R)⁻¹ + (((p^r - k : ℕ) : R)⁻¹)) =
      (p^r : R) * (k : R)⁻¹ * (((p^r - k : ℕ) : R)⁻¹) := by
  intro R
  have hk' := nondivSet_mem.mp hk
  have hkqmem : p^r - k ∈ nondivSet p (p^r) := nondivSet_invol_mem (p:=p) (q:=p^r) (r:=r) hp rfl hrpos hk
  have hkq' := nondivSet_mem.mp hkqmem
  let a : R := ((p^r - k : ℕ) : R)
  let b : R := (k : R)
  have huk : IsUnit b := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=2*r) hp hk'.2.2
  have huqk : IsUnit a := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=2*r) hp hkq'.2.2
  have hsum_nat : k + (p^r-k) = p^r := Nat.add_sub_of_le (Nat.lt_succ_iff.mp hk'.2.1)
  have hsum : b + a = (p^r : R) := by
    dsimp [a,b]
    calc
      (k : R) + ((p^r-k : ℕ) : R) = ((k + (p^r-k) : ℕ) : R) := by rw [Nat.cast_add]
      _ = (p^r : R) := by rw [hsum_nat, Nat.cast_pow]
  have hb1 : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk
  have ha1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit _ huqk
  calc
    (k : R)⁻¹ + (((p^r - k : ℕ) : R)⁻¹) = b⁻¹ + a⁻¹ := rfl
    _ = (a + b) * b⁻¹ * a⁻¹ := by
      calc
        b⁻¹ + a⁻¹ = (a * a⁻¹) * b⁻¹ + (b * b⁻¹) * a⁻¹ := by rw [ha1, hb1]; ring
        _ = (a + b) * b⁻¹ * a⁻¹ := by ring
    _ = (p^r : R) * b⁻¹ * a⁻¹ := by rw [add_comm a b, hsum]
    _ = (p^r : R) * (k : R)⁻¹ * (((p^r - k : ℕ) : R)⁻¹) := rfl

lemma q_mul_pair_inv_eq_neg_q_mul_inv_sq (p r k : ℕ) (hp : Nat.Prime p) (hrpos : 0 < r)
    (hk : k ∈ nondivSet p (p^r)) :
    let R := ZMod (p^(2*r))
    (p^r : R) * (k : R)⁻¹ * (((p^r - k : ℕ) : R)⁻¹) =
      - (p^r : R) * ((k : R)⁻¹)^2 := by
  intro R
  have hk' := nondivSet_mem.mp hk
  have hkqmem : p^r - k ∈ nondivSet p (p^r) := nondivSet_invol_mem (p:=p) (q:=p^r) (r:=r) hp rfl hrpos hk
  have hkq' := nondivSet_mem.mp hkqmem
  let a : R := ((p^r - k : ℕ) : R)
  let b : R := (k : R)
  have huk : IsUnit b := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=2*r) hp hk'.2.2
  have huqk : IsUnit a := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=2*r) hp hkq'.2.2
  have hsum_nat : k + (p^r-k) = p^r := Nat.add_sub_of_le (Nat.lt_succ_iff.mp hk'.2.1)
  have hsum : b + a = (p^r : R) := by
    dsimp [a,b]
    calc
      (k : R) + ((p^r-k : ℕ) : R) = ((k + (p^r-k) : ℕ) : R) := by rw [Nat.cast_add]
      _ = (p^r : R) := by rw [hsum_nat, Nat.cast_pow]
  have hb1 : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk
  have ha1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit _ huqk
  have hinvsum : b⁻¹ + a⁻¹ = (p^r : R) * b⁻¹ * a⁻¹ := by
    calc
      b⁻¹ + a⁻¹ = (a * a⁻¹) * b⁻¹ + (b * b⁻¹) * a⁻¹ := by rw [ha1, hb1]; ring
      _ = (a + b) * b⁻¹ * a⁻¹ := by ring
      _ = (p^r : R) * b⁻¹ * a⁻¹ := by rw [add_comm a b, hsum]
  have hq2 : (p^r : R) * (p^r : R) = 0 := by
    rw [← pow_add]
    apply zmod_natCast_pow_eq_zero_of_le
    omega
  have hadd0 : ((p^r : R) * b⁻¹ * a⁻¹) + (p^r : R) * b⁻¹^2 = 0 := by
    calc
      ((p^r : R) * b⁻¹ * a⁻¹) + (p^r : R) * b⁻¹^2
          = (p^r : R) * b⁻¹ * (a⁻¹ + b⁻¹) := by ring
      _ = (p^r : R) * b⁻¹ * ((p^r : R) * b⁻¹ * a⁻¹) := by rw [add_comm a⁻¹ b⁻¹, hinvsum]
      _ = ((p^r : R) * (p^r : R)) * (b⁻¹ * (b⁻¹ * a⁻¹)) := by ring
      _ = 0 := by rw [hq2, zero_mul]
  dsimp [a,b] at hadd0 ⊢
  calc
    (p^r : R) * (k : R)⁻¹ * (((p^r - k : ℕ) : R)⁻¹) = - ((p^r : R) * (k : R)⁻¹ ^ 2) := eq_neg_of_add_eq_zero_left hadd0
    _ = - (p^r : R) * (k : R)⁻¹ ^ 2 := by ring

lemma sum_nondiv_inv_zmod_eq_zero_two_r (p r : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hrpos : 0 < r) :
    (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^(2*r)))⁻¹)) = 0 := by
  classical
  let R := ZMod (p^(2*r))
  let S : R := ∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹)
  have hpair : (2 : R) * S = ∑ k ∈ nondivSet p (p^r),
      ((p^r : R) * (k : R)⁻¹ * (((p^r-k : ℕ) : R)⁻¹)) := by
    dsimp [S]
    have hre := sum_reindex_invol (p:=p) (q:=p^r) (r:=r) hp rfl hrpos (R:=R)
      (fun k => (((p^r-k : ℕ) : R)⁻¹))
    -- instantiate carefully: hre states sum f(q-k)=sum f(k); choose f(k)=k⁻¹ gives desired
    have hre2 : (∑ k ∈ nondivSet p (p^r), (((p^r-k : ℕ) : R)⁻¹)) =
        ∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹) := by
      simpa using (sum_reindex_invol (p:=p) (q:=p^r) (r:=r) hp rfl hrpos (R:=R) (fun k => ((k : R)⁻¹)))
    calc
      (2 : R) * (∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹))
          = (∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹)) +
            (∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹)) := by ring
      _ = (∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹)) +
            (∑ k ∈ nondivSet p (p^r), (((p^r-k : ℕ) : R)⁻¹)) := by rw [hre2]
      _ = ∑ k ∈ nondivSet p (p^r), (((k : R)⁻¹) + (((p^r-k : ℕ) : R)⁻¹)) := by rw [Finset.sum_add_distrib]
      _ = ∑ k ∈ nondivSet p (p^r), ((p^r : R) * (k : R)⁻¹ * (((p^r-k : ℕ) : R)⁻¹)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact inv_add_inv_pair_eq (p:=p) (r:=r) (k:=k) hp hrpos hk
  have hpair2 : (∑ k ∈ nondivSet p (p^r),
      ((p^r : R) * (k : R)⁻¹ * (((p^r-k : ℕ) : R)⁻¹))) =
      - (p^r : R) * (∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [q_mul_pair_inv_eq_neg_q_mul_inv_sq (p:=p) (r:=r) (k:=k) hp hrpos hk]
  have hsq := p_pow_mul_sum_inv_sq_nondiv_eq_zero (p:=p) (r:=r) hp hp5 hrpos
  have h2S : (2 : R) * S = 0 := by
    rw [hpair, hpair2]
    calc
      - (p^r : R) * (∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹)^2) = - ((p^r : R) * (∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹)^2)) := by ring
      _ = 0 := by rw [hsq, neg_zero]
  have hnot2 : ¬ p ∣ 2 := by
    intro h
    have hp_le_2 := Nat.le_of_dvd (by norm_num) h
    omega
  have h2unit : IsUnit (2 : R) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=2*r) hp hnot2
  exact (IsUnit.mul_right_eq_zero h2unit).mp h2S

lemma zmod_pow_kernel_mul_zero_2r_3r (p r : ℕ) (x : ZMod (p^(3*r)))
    (h : ZMod.castHom (show p^(2*r) ∣ p^(3*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^(2*r))) x = 0) :
    (p^r : ZMod (p^(3*r))) * x = 0 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simp only [map_intCast] at h
  have hzdiv : ((p^(2*r) : ℕ) : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z (p^(2*r))).mp h
  rcases hzdiv with ⟨t, ht⟩
  rw [ht]
  norm_num [Int.cast_mul]
  rw [← mul_assoc]
  have hpow : ((p : ZMod (p^(3*r)))^r) * ((p : ZMod (p^(3*r)))^(2*r)) = 0 := by
    rw [← pow_add]
    apply zmod_natCast_pow_eq_zero_of_le
    omega
  simpa [Nat.cast_pow] using congrArg (fun y : ZMod (p^(3*r)) => y * (t : ZMod (p^(3*r)))) hpow

lemma castHom_inv_nat_of_not_dvd_3r_2r (p r k : ℕ) (hp : Nat.Prime p) (hk : ¬ p ∣ k) :
    ZMod.castHom (show p^(2*r) ∣ p^(3*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^(2*r))) (((k : ZMod (p^(3*r)))⁻¹))
      = ((k : ZMod (p^(2*r)) )⁻¹) := by
  let phi : ZMod (p^(3*r)) →+* ZMod (p^(2*r)) :=
    ZMod.castHom (show p^(2*r) ∣ p^(3*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^(2*r)))
  have huR : IsUnit (k : ZMod (p^(3*r))) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=3*r) hp hk
  have hkmap : phi (k : ZMod (p^(3*r))) = (k : ZMod (p^(2*r))) := by simp [phi]
  have hmul : phi (((k : ZMod (p^(3*r)))⁻¹)) * (k : ZMod (p^(2*r))) = 1 := by
    rw [← hkmap, ← map_mul, ZMod.inv_mul_of_unit _ huR, map_one]
  have hmul' : (k : ZMod (p^(2*r))) * phi (((k : ZMod (p^(3*r)))⁻¹)) = 1 := by
    simpa [mul_comm] using hmul
  exact (ZMod.inv_eq_of_mul_eq_one (p^(2*r)) (k : ZMod (p^(2*r))) (phi (((k : ZMod (p^(3*r)))⁻¹))) hmul').symm

lemma castHom_sum_inv_nondiv_3r_2r (p r : ℕ) (hp : Nat.Prime p) :
    ZMod.castHom (show p^(2*r) ∣ p^(3*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^(2*r)))
      (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^(3*r)))⁻¹))
    = (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^(2*r)))⁻¹)) := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact castHom_inv_nat_of_not_dvd_3r_2r (p:=p) (r:=r) (k:=k) (hp:=hp) (hk:=(nondivSet_mem.mp hk).2.2)

lemma p_pow_mul_sum_inv_nondiv_eq_zero_3r (p r : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hrpos : 0 < r) :
    (p^r : ZMod (p^(3*r))) *
      (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^(3*r)))⁻¹)) = 0 := by
  classical
  apply zmod_pow_kernel_mul_zero_2r_3r (p:=p) (r:=r)
  rw [castHom_sum_inv_nondiv_3r_2r (p:=p) (r:=r) hp]
  exact sum_nondiv_inv_zmod_eq_zero_two_r (p:=p) (r:=r) hp hp5 hrpos

lemma zmod_pow_kernel_mul_zero_r_3r (p r : ℕ) (x : ZMod (p^(3*r)))
    (h : ZMod.castHom (show p^r ∣ p^(3*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^r)) x = 0) :
    (p^(2*r) : ZMod (p^(3*r))) * x = 0 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simp only [map_intCast] at h
  have hzdiv : ((p^r : ℕ) : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z (p^r)).mp h
  rcases hzdiv with ⟨t, ht⟩
  rw [ht]
  norm_num [Int.cast_mul]
  rw [← mul_assoc]
  have hpow : ((p : ZMod (p^(3*r)))^(2*r)) * ((p : ZMod (p^(3*r)))^r) = 0 := by
    rw [← pow_add]
    apply zmod_natCast_pow_eq_zero_of_le
    omega
  simpa [Nat.cast_pow] using congrArg (fun y : ZMod (p^(3*r)) => y * (t : ZMod (p^(3*r)))) hpow

lemma castHom_inv_nat_of_not_dvd_3r_r (p r k : ℕ) (hp : Nat.Prime p) (hk : ¬ p ∣ k) :
    ZMod.castHom (show p^r ∣ p^(3*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^r)) (((k : ZMod (p^(3*r)))⁻¹))
      = ((k : ZMod (p^r))⁻¹) := by
  let phi : ZMod (p^(3*r)) →+* ZMod (p^r) :=
    ZMod.castHom (show p^r ∣ p^(3*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^r))
  have huR : IsUnit (k : ZMod (p^(3*r))) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=3*r) hp hk
  have hkmap : phi (k : ZMod (p^(3*r))) = (k : ZMod (p^r)) := by simp [phi]
  have hmul : phi (((k : ZMod (p^(3*r)))⁻¹)) * (k : ZMod (p^r)) = 1 := by
    rw [← hkmap, ← map_mul, ZMod.inv_mul_of_unit _ huR, map_one]
  have hmul' : (k : ZMod (p^r)) * phi (((k : ZMod (p^(3*r)))⁻¹)) = 1 := by
    simpa [mul_comm] using hmul
  exact (ZMod.inv_eq_of_mul_eq_one (p^r) (k : ZMod (p^r)) (phi (((k : ZMod (p^(3*r)))⁻¹))) hmul').symm

lemma castHom_sum_inv_sq_nondiv_3r_r (p r : ℕ) (hp : Nat.Prime p) :
    ZMod.castHom (show p^r ∣ p^(3*r) by exact pow_dvd_pow p (by omega)) (ZMod (p^r))
      (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^(3*r)))⁻¹)^2)
    = (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^r))⁻¹)^2) := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_pow]
  rw [castHom_inv_nat_of_not_dvd_3r_r (p:=p) (r:=r) (k:=k) (hp:=hp) (hk:=(nondivSet_mem.mp hk).2.2)]

lemma p_pow_two_mul_sum_inv_sq_nondiv_eq_zero_3r (p r : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hrpos : 0 < r) :
    (p^(2*r) : ZMod (p^(3*r))) *
      (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^(3*r)))⁻¹)^2) = 0 := by
  classical
  haveI : NeZero (p^r) := ⟨pow_ne_zero r hp.ne_zero⟩
  apply zmod_pow_kernel_mul_zero_r_3r (p:=p) (r:=r)
  rw [castHom_sum_inv_sq_nondiv_3r_r (p:=p) (r:=r) hp]
  exact sum_nondiv_inv_sq_zmod_eq_zero' (p:=p) (r:=r) hp hp5 hrpos

lemma Uprod_eq_one_mod_3r_of_p_ge_5 (p r x : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hrpos : 0 < r) :
    Uprod p (p^r) (3*r) x = 1 := by
  classical
  let R := ZMod (p^(3*r))
  let s := nondivSet p (p^r)
  let f : ℕ → R := fun k => (x : R) * (p : R)^r * (k : R)⁻¹
  unfold Uprod
  simp_rw [Nat.cast_pow]
  change (∏ k ∈ s, (1 + f k)) = 1
  have hnot2 : ¬ p ∣ 2 := by
    intro h
    have hp_le_2 := Nat.le_of_dvd (by norm_num) h
    omega
  have h2unit : IsUnit (2 : R) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=3*r) hp hnot2
  apply Finset.prod_one_add_eq_one_of_sum_sq_and_triple_zero (s:=s) (f:=f) h2unit
  · dsimp [f, s]
    calc
      (∑ k ∈ nondivSet p (p^r), (x : R) * (p^r : R) * (k : R)⁻¹)
          = (x : R) * ((p^r : R) * (∑ k ∈ nondivSet p (p^r), (k : R)⁻¹)) := by
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = 0 := by rw [p_pow_mul_sum_inv_nondiv_eq_zero_3r (p:=p) (r:=r) hp hp5 hrpos, mul_zero]
  · dsimp [f, s]
    have hsq' : (p^(r*2) : R) * (∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹)^2) = 0 := by
      have h0 := p_pow_two_mul_sum_inv_sq_nondiv_eq_zero_3r (p:=p) (r:=r) hp hp5 hrpos
      simpa [mul_comm] using h0

    calc
      (∑ k ∈ nondivSet p (p^r), ((x : R) * (p^r : R) * (k : R)⁻¹)^2)
          = (x : R)^2 * ((p^(r*2) : R) * (∑ k ∈ nondivSet p (p^r), ((k : R)⁻¹)^2)) := by
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            calc
              ((x : R) * (p^r : R) * (k : R)⁻¹)^2 = (x : R)^2 * (((p^r : R)^2) * ((k : R)⁻¹)^2) := by ring
              _ = (x : R)^2 * ((p^(r*2) : R) * ((k : R)⁻¹)^2) := by
                rw [← pow_mul]
      _ = 0 := by rw [hsq', mul_zero]
  · intro t hts htcard
    dsimp [f, s]
    calc
      (∏ i ∈ t, (x : R) * (p^r : R) * (i : R)⁻¹)
          = (∏ i ∈ t, ((p^r : R) * ((x : R) * (i : R)⁻¹))) := by
            apply Finset.prod_congr rfl
            intro i hi
            ring
      _ = (∏ i ∈ t, (p^r : R)) * (∏ i ∈ t, ((x : R) * (i : R)⁻¹)) := by
            rw [← Finset.prod_mul_distrib]
      _ = ((p^r : R) ^ t.card) * (∏ i ∈ t, ((x : R) * (i : R)⁻¹)) := by rw [Finset.prod_const]
      _ = 0 := by
        have hpowzero : ((p^r : R) ^ t.card) = 0 := by
          rw [← pow_mul]
          apply zmod_natCast_pow_eq_zero_of_le
          nlinarith [htcard]
        rw [hpowzero, zero_mul]

lemma UprodR_eq_Uprod (p q N x : ℕ) : UprodR p q N x = Uprod p q N x := by
  unfold UprodR Uprod nondivSet
  rfl

lemma castHom_inv_nat_of_not_dvd_pow_to_three (p s k : ℕ) (hp : Nat.Prime p) (hs : 1 ≤ s) (hk : ¬ p ∣ k) :
    ZMod.castHom (show p^3 ∣ p^(3*s) by exact pow_dvd_pow p (by omega)) (ZMod (p^3)) (((k : ZMod (p^(3*s)))⁻¹))
      = ((k : ZMod (p^3))⁻¹) := by
  let phi : ZMod (p^(3*s)) →+* ZMod (p^3) :=
    ZMod.castHom (show p^3 ∣ p^(3*s) by exact pow_dvd_pow p (by omega)) (ZMod (p^3))
  have huR : IsUnit (k : ZMod (p^(3*s))) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=3*s) hp hk
  have hkmap : phi (k : ZMod (p^(3*s))) = (k : ZMod (p^3)) := by simp [phi]
  have hmul : phi (((k : ZMod (p^(3*s)))⁻¹)) * (k : ZMod (p^3)) = 1 := by
    rw [← hkmap, ← map_mul, ZMod.inv_mul_of_unit _ huR, map_one]
  have hmul' : (k : ZMod (p^3)) * phi (((k : ZMod (p^(3*s)))⁻¹)) = 1 := by
    simpa [mul_comm] using hmul
  exact (ZMod.inv_eq_of_mul_eq_one (p^3) (k : ZMod (p^3)) (phi (((k : ZMod (p^(3*s)))⁻¹))) hmul').symm

lemma castHom_Uprod_pow_to_three (p s x : ℕ) (hp : Nat.Prime p) (hs : 1 ≤ s) :
    ZMod.castHom (show p^3 ∣ p^(3*s) by exact pow_dvd_pow p (by omega)) (ZMod (p^3)) (Uprod p (p^s) (3*s) x)
      = Uprod p (p^s) 3 x := by
  classical
  unfold Uprod
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [map_add, map_one, map_mul, map_natCast]
  rw [castHom_inv_nat_of_not_dvd_pow_to_three (p:=p) (s:=s) (k:=k) hp hs (nondivSet_mem.mp hk).2.2]

lemma Uprod_eq_one_mod_three_of_p_ge_5 (p s x : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hs : 1 ≤ s) :
    Uprod p (p^s) 3 x = 1 := by
  have hbig := Uprod_eq_one_mod_3r_of_p_ge_5 (p:=p) (r:=s) (x:=x) hp hp5 (by omega)
  have hcast := congrArg (ZMod.castHom (show p^3 ∣ p^(3*s) by exact pow_dvd_pow p (by omega)) (ZMod (p^3))) hbig
  rw [castHom_Uprod_pow_to_three (p:=p) (s:=s) (x:=x) hp hs] at hcast
  rw [map_one] at hcast
  exact hcast

lemma UprodR_eq_one_mod_three_of_p_ge_5 (p s x : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hs : 1 ≤ s) :
    UprodR p (p^s) 3 x = 1 := by
  rw [UprodR_eq_Uprod]
  exact Uprod_eq_one_mod_three_of_p_ge_5 (p:=p) (s:=s) (x:=x) hp hp5 hs

lemma choose_c_pow_eq_c_mod_p3 (p c s : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hc : 1 ≤ c) :
    (((c * p^s).choose (p^s) : ℕ) : ZMod (p^3)) = (c : ZMod (p^3)) := by
  induction s with
  | zero =>
      simp [Nat.choose_one_right]
  | succ s ih =>
      have hs1 : 1 ≤ s+1 := by omega
      have hratio := choose_ratio_UprodR (p:=p) (r:=s+1) (c:=c) (N:=3) hp hs1 hc
      rw [hratio]
      have hU : UprodR p (p^(s+1)) 3 (c-1) = 1 := UprodR_eq_one_mod_three_of_p_ge_5 (p:=p) (s:=s+1) (x:=c-1) hp hp5 hs1
      rw [hU, mul_one]
      simpa using ih

lemma coeff_congruence_mod_p3_p_ge_5 (p s : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    let R := ZMod (p^3)
    (6 : R) * ((((3 * p^s).choose (p^s) : ℕ) : R)^2) -
      (27 : R) * ((((2 * p^s).choose (p^s) : ℕ) : R)) = 0 := by
  intro R
  have h3 := choose_c_pow_eq_c_mod_p3 (p:=p) (c:=3) (s:=s) hp hp5 (by norm_num)
  have h2 := choose_c_pow_eq_c_mod_p3 (p:=p) (c:=2) (s:=s) hp hp5 (by norm_num)
  change (6 : ZMod (p^3)) * ((((3 * p^s).choose (p^s) : ℕ) : ZMod (p^3))^2) -
      (27 : ZMod (p^3)) * ((((2 * p^s).choose (p^s) : ℕ) : ZMod (p^3))) = 0
  rw [h3, h2]
  norm_num

lemma zmod_mul_eq_zero_of_castHom_pow_eq_zero {p A B : ℕ} (x y : ZMod (p^(A+B)))
    (hx : ZMod.castHom (show p^A ∣ p^(A+B) by exact pow_dvd_pow p (by omega)) (ZMod (p^A)) x = 0)
    (hy : ZMod.castHom (show p^B ∣ p^(A+B) by exact pow_dvd_pow p (by omega)) (ZMod (p^B)) y = 0) :
    x * y = 0 := by
  obtain ⟨zx, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨zy, rfl⟩ := ZMod.intCast_surjective y
  simp only [map_intCast] at hx hy
  have hdx : ((p^A : ℕ) : ℤ) ∣ zx := (ZMod.intCast_zmod_eq_zero_iff_dvd zx (p^A)).mp hx
  have hdy : ((p^B : ℕ) : ℤ) ∣ zy := (ZMod.intCast_zmod_eq_zero_iff_dvd zy (p^B)).mp hy
  rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases hdx with ⟨tx, htx⟩
  rcases hdy with ⟨ty, hty⟩
  refine ⟨tx * ty, ?_⟩
  rw [htx, hty]
  calc
    (((p ^ A : ℕ) : ℤ) * tx) * (((p ^ B : ℕ) : ℤ) * ty)
        = (((p^A : ℕ) : ℤ) * ((p^B : ℕ) : ℤ)) * (tx * ty) := by ring
    _ = (((p ^ (A + B) : ℕ) : ℤ) * (tx * ty)) := by
      congr 1
      norm_cast
      rw [← pow_add]

lemma castHom_inv_nat_of_not_dvd_big_to_3r (p r k : ℕ) (hp : Nat.Prime p) (hk : ¬ p ∣ k) :
    ZMod.castHom (show p^(3*r) ∣ p^(3*r+3) by exact pow_dvd_pow p (by omega)) (ZMod (p^(3*r))) (((k : ZMod (p^(3*r+3)))⁻¹))
      = ((k : ZMod (p^(3*r)))⁻¹) := by
  let phi : ZMod (p^(3*r+3)) →+* ZMod (p^(3*r)) :=
    ZMod.castHom (show p^(3*r) ∣ p^(3*r+3) by exact pow_dvd_pow p (by omega)) (ZMod (p^(3*r)))
  have huR : IsUnit (k : ZMod (p^(3*r+3))) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=3*r+3) hp hk
  have hkmap : phi (k : ZMod (p^(3*r+3))) = (k : ZMod (p^(3*r))) := by simp [phi]
  have hmul : phi (((k : ZMod (p^(3*r+3)))⁻¹)) * (k : ZMod (p^(3*r))) = 1 := by
    rw [← hkmap, ← map_mul, ZMod.inv_mul_of_unit _ huR, map_one]
  have hmul' : (k : ZMod (p^(3*r))) * phi (((k : ZMod (p^(3*r+3)))⁻¹)) = 1 := by
    simpa [mul_comm] using hmul
  exact (ZMod.inv_eq_of_mul_eq_one (p^(3*r)) (k : ZMod (p^(3*r))) (phi (((k : ZMod (p^(3*r+3)))⁻¹))) hmul').symm

lemma castHom_Uprod_big_to_3r (p r x : ℕ) (hp : Nat.Prime p) :
    ZMod.castHom (show p^(3*r) ∣ p^(3*r+3) by exact pow_dvd_pow p (by omega)) (ZMod (p^(3*r))) (Uprod p (p^r) (3*r+3) x)
      = Uprod p (p^r) (3*r) x := by
  classical
  unfold Uprod
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [map_add, map_one, map_mul, map_natCast]
  rw [castHom_inv_nat_of_not_dvd_big_to_3r (p:=p) (r:=r) (k:=k) hp (nondivSet_mem.mp hk).2.2]

lemma Uprod_minus_one_cast_big_to_3r_eq_zero_of_p_ge_5 (p r x : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hrpos : 0 < r) :
    ZMod.castHom (show p^(3*r) ∣ p^(3*r+3) by exact pow_dvd_pow p (by omega)) (ZMod (p^(3*r)))
      ((Uprod p (p^r) (3*r+3) x : ZMod (p^(3*r+3))) - 1) = 0 := by
  rw [map_sub, map_one, castHom_Uprod_big_to_3r (p:=p) (r:=r) (x:=x) hp]
  have h := Uprod_eq_one_mod_3r_of_p_ge_5 (p:=p) (r:=r) (x:=x) hp hp5 hrpos
  rw [h, sub_self]

lemma square_zero_of_castHom_to_3r_eq_zero (p r : ℕ) (hr : 1 ≤ r) (x : ZMod (p^(3*r+3)))
    (hx : ZMod.castHom (show p^(3*r) ∣ p^(3*r+3) by exact pow_dvd_pow p (by omega)) (ZMod (p^(3*r))) x = 0) :
    x^2 = 0 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simp only [map_intCast] at hx
  have hzdiv : ((p^(3*r) : ℕ) : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z (p^(3*r))).mp hx
  rcases hzdiv with ⟨t, ht⟩
  rw [ht]
  norm_num [Int.cast_mul]
  calc
    (((p : ZMod (p^(3*r+3))) ^ (3*r) * (t : ZMod (p^(3*r+3)))) ^ 2)
        = ((p : ZMod (p^(3*r+3))) ^ (6*r)) * (t : ZMod (p^(3*r+3)))^2 := by ring_nf
    _ = 0 := by
      have hpzero : ((p : ZMod (p^(3*r+3))) ^ (6*r)) = 0 := by
        apply zmod_natCast_pow_eq_zero_of_le
        nlinarith
      rw [hpzero, zero_mul]

lemma coeff_cast_big_to_p3_eq_zero_p_ge_5 (p r : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    let R := ZMod (p^(3*r+3))
    let A0 : R := (((3 * p^(r-1)).choose (p^(r-1)) : ℕ) : R)
    let B0 : R := (((2 * p^(r-1)).choose (p^(r-1)) : ℕ) : R)
    ZMod.castHom (show p^3 ∣ p^(3*r+3) by exact pow_dvd_pow p (by omega)) (ZMod (p^3))
      ((6 : R) * A0^2 - (27 : R) * B0) = 0 := by
  intro R A0 B0
  dsimp [A0, B0, R]
  let hdiv : p^3 ∣ p^(3*r+3) := by exact pow_dvd_pow p (by omega)
  rw [ZMod.cast_sub hdiv]
  rw [ZMod.cast_mul hdiv]
  rw [ZMod.cast_mul hdiv]
  rw [ZMod.cast_pow hdiv]
  rw [ZMod.cast_natCast hdiv ((3 * p^(r-1)).choose (p^(r-1)))]
  rw [ZMod.cast_natCast hdiv ((2 * p^(r-1)).choose (p^(r-1)))]
  have h6 : (ZMod.cast (6 : ZMod (p^(3*r+3))) : ZMod (p^3)) = 6 := ZMod.cast_natCast hdiv 6
  have h27 : (ZMod.cast (27 : ZMod (p^(3*r+3))) : ZMod (p^3)) = 27 := ZMod.cast_natCast hdiv 27
  rw [h6, h27]
  exact coeff_congruence_mod_p3_p_ge_5 (p:=p) (s:=r-1) hp hp5

lemma final_zmod_p_ge_5_r_ge_3 (p r : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) (hr3 : 3 ≤ r) :
    let R := ZMod (p^(3*r+3))
    ((((3 * p^r).choose (p^r) : ℕ) : R)^2 - (27 : R) * (((2 * p^r).choose (p^r) : ℕ) : R)) =
    ((((3 * p^(r-1)).choose (p^(r-1)) : ℕ) : R)^2 - (27 : R) * (((2 * p^(r-1)).choose (p^(r-1)) : ℕ) : R)) := by
  intro R
  let A : R := (((3 * p^r).choose (p^r) : ℕ) : R)
  let A0 : R := (((3 * p^(r-1)).choose (p^(r-1)) : ℕ) : R)
  let B : R := (((2 * p^r).choose (p^r) : ℕ) : R)
  let B0 : R := (((2 * p^(r-1)).choose (p^(r-1)) : ℕ) : R)
  let u : R := Uprod p (p^r) (3*r+3) 2
  let v : R := Uprod p (p^r) (3*r+3) 1
  have hrpos : 0 < r := by omega
  have hr1 : 1 ≤ r := by omega
  have hA : A = A0 * u := by
    dsimp [A,A0,u,R]
    have h := choose_ratio_UprodR (p:=p) (r:=r) (c:=3) (N:=3*r+3) hp hr1 (by norm_num)
    rw [h, UprodR_eq_Uprod]
  have hB : B = B0 * v := by
    dsimp [B,B0,v,R]
    have h := choose_ratio_UprodR (p:=p) (r:=r) (c:=2) (N:=3*r+3) hp hr1 (by norm_num)
    rw [h, UprodR_eq_Uprod]
  have hvcast : ZMod.castHom (show p^(3*r) ∣ p^(3*r+3) by exact pow_dvd_pow p (by omega)) (ZMod (p^(3*r))) (v - 1) = 0 := by
    dsimp [v,R]
    exact Uprod_minus_one_cast_big_to_3r_eq_zero_of_p_ge_5 (p:=p) (r:=r) (x:=1) hp hp5 hrpos
  have hvnil : (v - 1)^2 = 0 := square_zero_of_castHom_to_3r_eq_zero (p:=p) (r:=r) hr1 (v-1) hvcast
  have hsquare := Uprod_square_relation_r_ge_three (p:=p) (q:=p^r) (r:=r) hp hrpos hr3 rfl
  have hrel_square : u^2 - 1 = 3 * (v^2 - 1) := by
    dsimp [u,v,R]
    exact hsquare
  have hrel : u^2 - 1 = 6 * (v - 1) := square_relation_to_linear u v hvnil hrel_square
  have hcoefcast := coeff_cast_big_to_p3_eq_zero_p_ge_5 (p:=p) (r:=r) hp hp5
  have hcoef : ((6 : R) * A0^2 - (27 : R) * B0) * (v - 1) = 0 := by
    have hprod := zmod_mul_eq_zero_of_castHom_pow_eq_zero (p:=p) (A:=3*r) (B:=3)
      (x := v - 1) (y := ((6 : R) * A0^2 - (27 : R) * B0)) hvcast (by
        dsimp [R,A0,B0] at hcoefcast ⊢
        simpa using hcoefcast)
    simpa [mul_comm] using hprod
  have hfinal := final_from_ratio_algebra (A:=A) (A0:=A0) (B:=B) (B0:=B0) (u:=u) (v:=v) hA hB hrel hcoef
  dsimp [A,A0,B,B0,R] at hfinal ⊢
  exact hfinal

lemma intCast_mul_eq_zero_of_dvd_and_castHom_pow_eq_zero {p A B : ℕ} (c : ℤ) (y : ZMod (p^(A+B)))
    (hc : ((p^B : ℕ) : ℤ) ∣ c)
    (hy : ZMod.castHom (show p^A ∣ p^(A+B) by exact pow_dvd_pow p (by omega)) (ZMod (p^A)) y = 0) :
    y * (c : ZMod (p^(A+B))) = 0 := by
  obtain ⟨zy, rfl⟩ := ZMod.intCast_surjective y
  simp only [map_intCast] at hy
  have hdy : ((p^A : ℕ) : ℤ) ∣ zy := (ZMod.intCast_zmod_eq_zero_iff_dvd zy (p^A)).mp hy
  rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases hdy with ⟨ty, hty⟩
  rcases hc with ⟨tc, htc⟩
  refine ⟨ty * tc, ?_⟩
  rw [hty, htc]
  calc
    (((p ^ A : ℕ) : ℤ) * ty) * (((p ^ B : ℕ) : ℤ) * tc)
        = (((p^A : ℕ) : ℤ) * ((p^B : ℕ) : ℤ)) * (ty * tc) := by ring
    _ = (((p ^ (A + B) : ℕ) : ℤ) * (ty * tc)) := by
      congr 1
      norm_cast
      rw [← pow_add]

lemma coeff_int_dvd_p3_p_ge_5 (p s : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    ((p^3 : ℕ) : ℤ) ∣
      ((6 : ℤ) * (Int.ofNat ((3 * p^s).choose (p^s)))^2 -
        (27 : ℤ) * Int.ofNat ((2 * p^s).choose (p^s))) := by
  have h := coeff_congruence_mod_p3_p_ge_5 (p:=p) (s:=s) hp hp5
  change (6 : ZMod (p^3)) * ((((3 * p^s).choose (p^s) : ℕ) : ZMod (p^3))^2) -
      (27 : ZMod (p^3)) * ((((2 * p^s).choose (p^s) : ℕ) : ZMod (p^3))) = 0 at h
  have hz : (((6 : ℤ) * (Int.ofNat ((3 * p^s).choose (p^s)))^2 -
        (27 : ℤ) * Int.ofNat ((2 * p^s).choose (p^s))) : ZMod (p^3)) = 0 := by
    calc
      (((6 : ℤ) * (Int.ofNat ((3 * p^s).choose (p^s)))^2 -
        (27 : ℤ) * Int.ofNat ((2 * p^s).choose (p^s))) : ZMod (p^3))
          = (6 : ZMod (p^3)) * ((((3 * p^s).choose (p^s) : ℕ) : ZMod (p^3))^2) -
              (27 : ZMod (p^3)) * ((((2 * p^s).choose (p^s) : ℕ) : ZMod (p^3))) := by
                norm_num [Int.cast_natCast]
      _ = 0 := h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^3)).mp (by
    exact_mod_cast hz)

lemma sum_units_inv_sq_three_mul_eq_zero (p k : ℕ) [NeZero (p^k)] (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    (3 : ZMod (p^k)) * (∑ u : (ZMod (p^k))ˣ, ((u⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) = 0 := by
  classical
  have h2not : ¬ p ∣ 2 := by
    intro h
    have hp_le_2 := Nat.le_of_dvd (by norm_num) h
    omega
  have hcop2p : Nat.Coprime 2 p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr h2not)
  have hcop2 : Nat.Coprime 2 (p^k) := hcop2p.pow_right k
  let t : (ZMod (p^k))ˣ := ZMod.unitOfCoprime 2 hcop2
  have ht : ((t : (ZMod (p^k))ˣ) : ZMod (p^k)) = (2 : ZMod (p^k)) := by
    simp [t, ZMod.coe_unitOfCoprime]
  let S : ZMod (p^k) := ∑ u : (ZMod (p^k))ˣ, ((u⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2
  have hperm : S = ∑ u : (ZMod (p^k))ˣ, (((t * u)⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2 := by
    dsimp [S]
    let e : (ZMod (p^k))ˣ ≃ (ZMod (p^k))ˣ := Equiv.mulLeft t
    have h := Fintype.sum_equiv e
      (fun u : (ZMod (p^k))ˣ => ((((t * u)⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2))
      (fun u : (ZMod (p^k))ˣ => (((u⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2))
      (by intro u; rfl)
    exact h.symm
  have hscale : (∑ u : (ZMod (p^k))ˣ, (((t * u)⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2)
      = ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2 * S := by
    dsimp [S]
    simp only [mul_inv_rev, Units.val_mul, Finset.mul_sum]
    simp [mul_pow, mul_comm, mul_left_comm, mul_assoc]
  have hS : S = ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2 * S := hperm.trans hscale
  have hz : (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) * S = 0 := by
    calc (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) * S
      _ = S - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2 * S := by ring
      _ = 0 := by
        nth_rewrite 1 [hS]
        rw [sub_self]
  have hcalc : (1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) * ((t : (ZMod (p^k))ˣ) : ZMod (p^k))^2 = 3 := by
    rw [sub_mul, one_mul]
    simp only [← Units.val_pow_eq_pow_val, ← Units.val_mul]
    have htinvsq : (t⁻¹ : (ZMod (p^k))ˣ)^2 * t^2 = 1 := by
      rw [← mul_pow, inv_mul_cancel, one_pow]
    rw [htinvsq]
    change (((t : (ZMod (p^k))ˣ) : ZMod (p^k)) ^ 2 - 1 = 3)
    rw [ht]
    norm_num
  have hmul : ((1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) * S) * ((t : (ZMod (p^k))ˣ) : ZMod (p^k))^2 = 0 := by rw [hz, zero_mul]
  calc
    (3 : ZMod (p^k)) * S = ((1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) * ((t : (ZMod (p^k))ˣ) : ZMod (p^k))^2) * S := by rw [hcalc]
    _ = ((1 - ((t⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))^2) * S) * ((t : (ZMod (p^k))ˣ) : ZMod (p^k))^2 := by ring
    _ = 0 := hmul

lemma three_mul_sum_nondiv_inv_sq_zmod_eq_zero (p r : ℕ) [NeZero (p^r)] (hp : Nat.Prime p) (hp3 : p ≥ 3) (hrpos : 0 < r) :
    (3 : ZMod (p^r)) * (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^r))⁻¹)^2) = 0 := by
  rw [sum_nondiv_inv_sq_zmod_eq_units_sum' (p:=p) (r:=r) hp hrpos]
  exact sum_units_inv_sq_three_mul_eq_zero p r hp hp3

lemma castHom_inv_nat_of_not_dvd_pow_general (p M N k : ℕ) (hp : Nat.Prime p) (hMN : M ≤ N) (hk : ¬ p ∣ k) :
    ZMod.castHom (show p^M ∣ p^N by exact pow_dvd_pow p hMN) (ZMod (p^M)) (((k : ZMod (p^N))⁻¹))
      = ((k : ZMod (p^M))⁻¹) := by
  let phi : ZMod (p^N) →+* ZMod (p^M) := ZMod.castHom (show p^M ∣ p^N by exact pow_dvd_pow p hMN) (ZMod (p^M))
  have huR : IsUnit (k : ZMod (p^N)) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=N) hp hk
  have hkmap : phi (k : ZMod (p^N)) = (k : ZMod (p^M)) := by simp [phi]
  have hmul : phi (((k : ZMod (p^N))⁻¹)) * (k : ZMod (p^M)) = 1 := by
    rw [← hkmap, ← map_mul, ZMod.inv_mul_of_unit _ huR, map_one]
  have hmul' : (k : ZMod (p^M)) * phi (((k : ZMod (p^N))⁻¹)) = 1 := by simpa [mul_comm] using hmul
  exact (ZMod.inv_eq_of_mul_eq_one (p^M) (k : ZMod (p^M)) (phi (((k : ZMod (p^N))⁻¹))) hmul').symm

lemma castHom_sum_inv_sq_nondiv_general (p r M N : ℕ) (hp : Nat.Prime p) (hMN : M ≤ N) :
    ZMod.castHom (show p^M ∣ p^N by exact pow_dvd_pow p hMN) (ZMod (p^M))
      (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^N))⁻¹)^2)
    = (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^M))⁻¹)^2) := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_pow]
  rw [castHom_inv_nat_of_not_dvd_pow_general (p:=p) (M:=M) (N:=N) (k:=k) hp hMN (nondivSet_mem.mp hk).2.2]

lemma inv_add_inv_pair_eq_modN (p r N k : ℕ) (hp : Nat.Prime p) (hrpos : 0 < r)
    (hk : k ∈ nondivSet p (p^r)) :
    let R := ZMod (p^N)
    ((k : R)⁻¹ + (((p^r - k : ℕ) : R)⁻¹)) =
      (p^r : R) * (k : R)⁻¹ * (((p^r - k : ℕ) : R)⁻¹) := by
  intro R
  have hk' := nondivSet_mem.mp hk
  have hkqmem : p^r - k ∈ nondivSet p (p^r) := nondivSet_invol_mem (p:=p) (q:=p^r) (r:=r) hp rfl hrpos hk
  have hkq' := nondivSet_mem.mp hkqmem
  let a : R := ((p^r - k : ℕ) : R)
  let b : R := (k : R)
  have huk : IsUnit b := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=N) hp hk'.2.2
  have huqk : IsUnit a := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=N) hp hkq'.2.2
  have hsum_nat : k + (p^r-k) = p^r := Nat.add_sub_of_le (Nat.lt_succ_iff.mp hk'.2.1)
  have hsum : b + a = (p^r : R) := by
    dsimp [a,b]
    calc
      (k : R) + ((p^r-k : ℕ) : R) = ((k + (p^r-k) : ℕ) : R) := by rw [Nat.cast_add]
      _ = (p^r : R) := by rw [hsum_nat, Nat.cast_pow]
  have hb1 : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk
  have ha1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit _ huqk
  calc
    (k : R)⁻¹ + (((p^r - k : ℕ) : R)⁻¹) = b⁻¹ + a⁻¹ := rfl
    _ = (a + b) * b⁻¹ * a⁻¹ := by
      calc
        b⁻¹ + a⁻¹ = (a * a⁻¹) * b⁻¹ + (b * b⁻¹) * a⁻¹ := by rw [ha1, hb1]; ring
        _ = (a + b) * b⁻¹ * a⁻¹ := by ring
    _ = (p^r : R) * b⁻¹ * a⁻¹ := by rw [add_comm a b, hsum]
    _ = (p^r : R) * (k : R)⁻¹ * (((p^r - k : ℕ) : R)⁻¹) := rfl

lemma q_mul_pair_inv_eq_neg_q_mul_inv_sq_modN (p r N k : ℕ) (hp : Nat.Prime p) (hrpos : 0 < r)
    (hN : N ≤ 2*r) (hk : k ∈ nondivSet p (p^r)) :
    let R := ZMod (p^N)
    (p^r : R) * (k : R)⁻¹ * (((p^r - k : ℕ) : R)⁻¹) =
      - (p^r : R) * ((k : R)⁻¹)^2 := by
  intro R
  have hk' := nondivSet_mem.mp hk
  have hkqmem : p^r - k ∈ nondivSet p (p^r) := nondivSet_invol_mem (p:=p) (q:=p^r) (r:=r) hp rfl hrpos hk
  have hkq' := nondivSet_mem.mp hkqmem
  let a : R := ((p^r - k : ℕ) : R)
  let b : R := (k : R)
  have huk : IsUnit b := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=N) hp hk'.2.2
  have huqk : IsUnit a := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=N) hp hkq'.2.2
  have hsum_nat : k + (p^r-k) = p^r := Nat.add_sub_of_le (Nat.lt_succ_iff.mp hk'.2.1)
  have hsum : b + a = (p^r : R) := by
    dsimp [a,b]
    calc
      (k : R) + ((p^r-k : ℕ) : R) = ((k + (p^r-k) : ℕ) : R) := by rw [Nat.cast_add]
      _ = (p^r : R) := by rw [hsum_nat, Nat.cast_pow]
  have hb1 : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk
  have ha1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit _ huqk
  have hinvsum : b⁻¹ + a⁻¹ = (p^r : R) * b⁻¹ * a⁻¹ := by
    calc
      b⁻¹ + a⁻¹ = (a * a⁻¹) * b⁻¹ + (b * b⁻¹) * a⁻¹ := by rw [ha1, hb1]; ring
      _ = (a + b) * b⁻¹ * a⁻¹ := by ring
      _ = (p^r : R) * b⁻¹ * a⁻¹ := by rw [add_comm a b, hsum]
  have hq2 : (p^r : R) * (p^r : R) = 0 := by
    rw [← pow_add]
    apply zmod_natCast_pow_eq_zero_of_le
    omega
  have hadd0 : ((p^r : R) * b⁻¹ * a⁻¹) + (p^r : R) * b⁻¹^2 = 0 := by
    calc
      ((p^r : R) * b⁻¹ * a⁻¹) + (p^r : R) * b⁻¹^2
          = (p^r : R) * b⁻¹ * (a⁻¹ + b⁻¹) := by ring
      _ = (p^r : R) * b⁻¹ * ((p^r : R) * b⁻¹ * a⁻¹) := by rw [add_comm a⁻¹ b⁻¹, hinvsum]
      _ = ((p^r : R) * (p^r : R)) * (b⁻¹ * (b⁻¹ * a⁻¹)) := by ring
      _ = 0 := by rw [hq2, zero_mul]
  dsimp [a,b] at hadd0 ⊢
  calc
    (p^r : R) * (k : R)⁻¹ * (((p^r - k : ℕ) : R)⁻¹) = - ((p^r : R) * (k : R)⁻¹ ^ 2) := eq_neg_of_add_eq_zero_left hadd0
    _ = - (p^r : R) * (k : R)⁻¹ ^ 2 := by ring

lemma castHom_three_pow_pred_eq_zero_of_three_mul_eq_zero (r : ℕ) (hr : 1 ≤ r) (x : ZMod (3^r))
    (h : (3 : ZMod (3^r)) * x = 0) :
    ZMod.castHom (show 3^(r-1) ∣ 3^r by exact pow_dvd_pow 3 (by omega)) (ZMod (3^(r-1))) x = 0 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simp only [map_intCast]
  rw [← Int.cast_ofNat, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases h with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hpow : ((3^r : ℕ) : ℤ) = (3 : ℤ) * ((3^(r-1) : ℕ) : ℤ) := by
    cases r with
    | zero => omega
    | succ r =>
        simp [pow_succ]
        ring
  have hcancel : (3 : ℤ) * z = (3 : ℤ) * (((3^(r-1) : ℕ) : ℤ) * t) := by
    rw [ht, hpow]
    ring
  exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) hcancel

lemma sum_inv_sq_cast_pred_zero_p3 (r : ℕ) (hr : 1 ≤ r) :
    ZMod.castHom (show 3^(r-1) ∣ 3^r by exact pow_dvd_pow 3 (by omega)) (ZMod (3^(r-1)))
      (∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^r))⁻¹)^2) = 0 := by
  have hp : Nat.Prime 3 := by norm_num
  haveI : NeZero (3^r) := ⟨pow_ne_zero r (by norm_num : (3:ℕ) ≠ 0)⟩
  have h3 := three_mul_sum_nondiv_inv_sq_zmod_eq_zero (p:=3) (r:=r) hp (by norm_num) (by omega)
  exact castHom_three_pow_pred_eq_zero_of_three_mul_eq_zero r hr _ h3

lemma sum_inv_sq_cast_big_to_pred_zero_p3 (r N : ℕ) (hr : 1 ≤ r) (hN : r - 1 ≤ N) :
    ZMod.castHom (show 3^(r-1) ∣ 3^N by exact pow_dvd_pow 3 hN) (ZMod (3^(r-1)))
      (∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^N))⁻¹)^2) = 0 := by
  have hp : Nat.Prime 3 := by norm_num
  rw [castHom_sum_inv_sq_nondiv_general (p:=3) (r:=r) (M:=r-1) (N:=N) hp hN]
  have hsmall := sum_inv_sq_cast_pred_zero_p3 r hr
  rw [castHom_sum_inv_sq_nondiv_general (p:=3) (r:=r) (M:=r-1) (N:=r) hp (by omega)] at hsmall
  exact hsmall

lemma pow_mul_sum_inv_sq_eq_zero_p3 (r B : ℕ) (hr : 1 ≤ r) :
    let A := r - 1
    let N := A + B
    (3^B : ZMod (3^N)) *
      (∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^N))⁻¹)^2) = 0 := by
  intro A N
  have hcast := sum_inv_sq_cast_big_to_pred_zero_p3 (r:=r) (N:=N) hr (by dsimp [N,A]; omega)
  have hmul := intCast_mul_eq_zero_of_dvd_and_castHom_pow_eq_zero (p:=3) (A:=A) (B:=B)
      (c := ((3^B : ℕ) : ℤ))
      (y := ∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^N))⁻¹)^2)
      (by exact dvd_rfl) hcast
  simpa [mul_comm] using hmul

lemma sum_nondiv_inv_zmod_eq_zero_p3_mod_2r_minus1 (r : ℕ) (hr2 : 2 ≤ r) :
    (∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^(2*r-1)))⁻¹)) = 0 := by
  classical
  let N := 2*r - 1
  let R := ZMod (3^N)
  let S : R := ∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹)
  have hp : Nat.Prime 3 := by norm_num
  have hrpos : 0 < r := by omega
  have hpair : (2 : R) * S = ∑ k ∈ nondivSet 3 (3^r),
      ((3^r : R) * (k : R)⁻¹ * (((3^r-k : ℕ) : R)⁻¹)) := by
    dsimp [S]
    have hre2 : (∑ k ∈ nondivSet 3 (3^r), (((3^r-k : ℕ) : R)⁻¹)) =
        ∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹) := by
      simpa using (sum_reindex_invol (p:=3) (q:=3^r) (r:=r) hp rfl hrpos (R:=R) (fun k => ((k : R)⁻¹)))
    calc
      (2 : R) * (∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹))
          = (∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹)) +
            (∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹)) := by ring
      _ = (∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹)) +
            (∑ k ∈ nondivSet 3 (3^r), (((3^r-k : ℕ) : R)⁻¹)) := by rw [hre2]
      _ = ∑ k ∈ nondivSet 3 (3^r), (((k : R)⁻¹) + (((3^r-k : ℕ) : R)⁻¹)) := by rw [Finset.sum_add_distrib]
      _ = ∑ k ∈ nondivSet 3 (3^r), ((3^r : R) * (k : R)⁻¹ * (((3^r-k : ℕ) : R)⁻¹)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact inv_add_inv_pair_eq_modN (p:=3) (r:=r) (N:=N) (k:=k) hp hrpos hk
  have hpair2 : (∑ k ∈ nondivSet 3 (3^r),
      ((3^r : R) * (k : R)⁻¹ * (((3^r-k : ℕ) : R)⁻¹))) =
      - (3^r : R) * (∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      (3^r : R) * (k : R)⁻¹ * (((3^r-k : ℕ) : R)⁻¹) = - ((3^r : R) * (k : R)⁻¹ ^ 2) := by
        simpa [Nat.cast_pow] using q_mul_pair_inv_eq_neg_q_mul_inv_sq_modN (p:=3) (r:=r) (N:=N) (k:=k) hp hrpos (by dsimp [N]; omega) hk
      _ = - (3^r : R) * (k : R)⁻¹ ^ 2 := by ring
  have hsq : (3^r : R) * (∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹)^2) = 0 := by
    have h := pow_mul_sum_inv_sq_eq_zero_p3 (r:=r) (B:=r) (by omega)
    dsimp at h
    change ((3 : ZMod (3^(2*r-1)))^r) * (∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^(2*r-1)))⁻¹)^2) = 0
    have hE : 2*r - 1 = (r - 1) + r := by omega
    rw [hE]
    simpa [Nat.cast_pow] using h
  have h2S : (2 : R) * S = 0 := by
    rw [hpair, hpair2]
    calc
      - (3^r : R) * (∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹)^2) = - ((3^r : R) * (∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹)^2)) := by ring
      _ = 0 := by rw [hsq, neg_zero]
  have h2unit : IsUnit (2 : R) := zmod_isUnit_nat_of_not_dvd (p:=3) (N:=N) hp (by norm_num)
  exact (IsUnit.mul_right_eq_zero h2unit).mp h2S

lemma castHom_sum_inv_nondiv_general (p r M N : ℕ) (hp : Nat.Prime p) (hMN : M ≤ N) :
    ZMod.castHom (show p^M ∣ p^N by exact pow_dvd_pow p hMN) (ZMod (p^M))
      (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^N))⁻¹))
    = (∑ k ∈ nondivSet p (p^r), ((k : ZMod (p^M))⁻¹)) := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [castHom_inv_nat_of_not_dvd_pow_general (p:=p) (M:=M) (N:=N) (k:=k) hp hMN (nondivSet_mem.mp hk).2.2]

lemma pow_mul_sum_inv_eq_zero_p3 (r B : ℕ) (hr2 : 2 ≤ r) :
    let A := 2*r - 1
    let N := A + B
    (3^B : ZMod (3^N)) *
      (∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^N))⁻¹)) = 0 := by
  intro A N
  have hp : Nat.Prime 3 := by norm_num
  have hcast : ZMod.castHom (show 3^A ∣ 3^N by exact pow_dvd_pow 3 (by dsimp [N]; omega)) (ZMod (3^A))
      (∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^N))⁻¹)) = 0 := by
    rw [castHom_sum_inv_nondiv_general (p:=3) (r:=r) (M:=A) (N:=N) hp (by dsimp [N]; omega)]
    dsimp [A]
    exact sum_nondiv_inv_zmod_eq_zero_p3_mod_2r_minus1 r hr2
  have hmul := intCast_mul_eq_zero_of_dvd_and_castHom_pow_eq_zero (p:=3) (A:=A) (B:=B)
      (c := ((3^B : ℕ) : ℤ))
      (y := ∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^N))⁻¹))
      (by exact dvd_rfl) hcast
  simpa [mul_comm] using hmul

lemma Uprod_eq_one_mod_3r_minus1_p3 (r x : ℕ) (hr2 : 2 ≤ r) :
    Uprod 3 (3^r) (3*r - 1) x = 1 := by
  classical
  let N := 3*r - 1
  let R := ZMod (3^N)
  let s := nondivSet 3 (3^r)
  let f : ℕ → R := fun k => (x : R) * (3 : R)^r * (k : R)⁻¹
  unfold Uprod
  simp_rw [Nat.cast_pow]
  change (∏ k ∈ s, (1 + f k)) = 1
  have hp : Nat.Prime 3 := by norm_num
  have h2unit : IsUnit (2 : R) := zmod_isUnit_nat_of_not_dvd (p:=3) (N:=N) hp (by norm_num)
  apply Finset.prod_one_add_eq_one_of_sum_sq_and_triple_zero (s:=s) (f:=f) h2unit
  · dsimp [f, s]
    have hsum0 : ((3 : R)^r) * (∑ k ∈ nondivSet 3 (3^r), (k : R)⁻¹) = 0 := by
      have h := pow_mul_sum_inv_eq_zero_p3 (r:=r) (B:=r) hr2
      dsimp at h
      have hE : (2*r - 1) + r = 3*r - 1 := by omega
      change ((3 : ZMod (3^N))^r) * (∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^N))⁻¹)) = 0
      rw [show N = (2*r - 1) + r by dsimp [N]; omega]
      simpa [Nat.cast_pow] using h
    calc
      (∑ k ∈ nondivSet 3 (3^r), (x : R) * (3 : R)^r * (k : R)⁻¹)
          = (x : R) * (((3 : R)^r) * (∑ k ∈ nondivSet 3 (3^r), (k : R)⁻¹)) := by
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = 0 := by rw [hsum0, mul_zero]
  · dsimp [f, s]
    have hsq0 : ((3 : R)^(2*r)) * (∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹)^2) = 0 := by
      have h := pow_mul_sum_inv_sq_eq_zero_p3 (r:=r) (B:=2*r) (by omega)
      dsimp at h
      have hE : (r - 1) + 2*r = 3*r - 1 := by omega
      change ((3 : ZMod (3^N))^(2*r)) * (∑ k ∈ nondivSet 3 (3^r), ((k : ZMod (3^N))⁻¹)^2) = 0
      rw [show N = (r - 1) + 2*r by dsimp [N]; omega]
      simpa [Nat.cast_pow] using h
    calc
      (∑ k ∈ nondivSet 3 (3^r), ((x : R) * (3 : R)^r * (k : R)⁻¹)^2)
          = (x : R)^2 * (((3 : R)^(2*r)) * (∑ k ∈ nondivSet 3 (3^r), ((k : R)⁻¹)^2)) := by
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            calc
              ((x : R) * (3 : R)^r * (k : R)⁻¹)^2 = (x : R)^2 * (((3 : R)^r)^2 * ((k : R)⁻¹)^2) := by ring
              _ = (x : R)^2 * (((3 : R)^(2*r)) * ((k : R)⁻¹)^2) := by rw [← pow_mul]; ring
      _ = 0 := by rw [hsq0, mul_zero]
  · intro t hts htcard
    dsimp [f, s]
    calc
      (∏ i ∈ t, (x : R) * (3 : R)^r * (i : R)⁻¹)
          = (∏ i ∈ t, ((3 : R)^r * ((x : R) * (i : R)⁻¹))) := by
            apply Finset.prod_congr rfl
            intro i hi
            ring
      _ = (∏ i ∈ t, (3 : R)^r) * (∏ i ∈ t, ((x : R) * (i : R)⁻¹)) := by rw [← Finset.prod_mul_distrib]
      _ = (((3 : R)^r) ^ t.card) * (∏ i ∈ t, ((x : R) * (i : R)⁻¹)) := by rw [Finset.prod_const]
      _ = 0 := by
        have hpowzero : (((3 : R)^r) ^ t.card) = 0 := by
          rw [← pow_mul]
          apply zmod_natCast_pow_eq_zero_of_le
          dsimp [N]
          have hmul : 3 * r ≤ r * t.card := by
            calc
              3 * r = r * 3 := by ring
              _ ≤ r * t.card := Nat.mul_le_mul_left r htcard
          omega
        rw [hpowzero, zero_mul]

lemma castHom_Uprod_general (p q M N x : ℕ) (hp : Nat.Prime p) (hMN : M ≤ N) :
    ZMod.castHom (show p^M ∣ p^N by exact pow_dvd_pow p hMN) (ZMod (p^M)) (Uprod p q N x)
      = Uprod p q M x := by
  classical
  unfold Uprod
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [map_add, map_one, map_mul, map_natCast]
  rw [castHom_inv_nat_of_not_dvd_pow_general (p:=p) (M:=M) (N:=N) (k:=k) hp hMN (nondivSet_mem.mp hk).2.2]

lemma UprodR_eq_one_mod_four_p3 (j x : ℕ) (hj : 2 ≤ j) :
    UprodR 3 (3^j) 4 x = 1 := by
  have hp : Nat.Prime 3 := by norm_num
  have hbig := Uprod_eq_one_mod_3r_minus1_p3 (r:=j) (x:=x) hj
  have hMN : 4 ≤ 3*j - 1 := by omega
  have hcast := congrArg (ZMod.castHom (show 3^4 ∣ 3^(3*j-1) by exact pow_dvd_pow 3 hMN) (ZMod (3^4))) hbig
  rw [castHom_Uprod_general (p:=3) (q:=3^j) (M:=4) (N:=3*j-1) (x:=x) hp hMN] at hcast
  rw [map_one] at hcast
  simpa [UprodR_eq_Uprod] using hcast

lemma choose_p3_stable_mod81 (c t : ℕ) (hc : 1 ≤ c) :
    ((((c * 3^(t+1)).choose (3^(t+1)) : ℕ) : ZMod (3^4))) =
      ((((c * 3).choose 3 : ℕ) : ZMod (3^4))) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hp : Nat.Prime 3 := by norm_num
      have hr : 1 ≤ t + 2 := by omega
      have hratio := choose_ratio_UprodR (p:=3) (r:=t+2) (c:=c) (N:=4) hp hr hc
      rw [hratio]
      have hU : UprodR 3 (3^(t+2)) 4 (c-1) = 1 := UprodR_eq_one_mod_four_p3 (j:=t+2) (x:=c-1) (by omega)
      rw [hU, mul_one]
      simpa [pow_succ] using ih

lemma coeff_congruence_mod_3pow4_p3 (s : ℕ) (hs : 1 ≤ s) :
    (6 : ZMod (3^4)) * ((((3 * 3^s).choose (3^s) : ℕ) : ZMod (3^4))^2) -
      (27 : ZMod (3^4)) * ((((2 * 3^s).choose (3^s) : ℕ) : ZMod (3^4))) = 0 := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0) with ⟨t, rfl⟩
  have h3 := choose_p3_stable_mod81 (c:=3) (t:=t) (by norm_num)
  have h2 := choose_p3_stable_mod81 (c:=2) (t:=t) (by norm_num)
  rw [h3, h2]
  change ((41796 : ℕ) : ZMod (3^4)) = 0
  rw [← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

lemma coeff_cast_big_to_3pow4_p3 (r : ℕ) (hr2 : 2 ≤ r) :
    let R := ZMod (3^(3*r+3))
    let A0 : R := (((3 * 3^(r-1)).choose (3^(r-1)) : ℕ) : R)
    let B0 : R := (((2 * 3^(r-1)).choose (3^(r-1)) : ℕ) : R)
    ZMod.castHom (show 3^4 ∣ 3^(3*r+3) by exact pow_dvd_pow 3 (by omega)) (ZMod (3^4))
      ((6 : R) * A0^2 - (27 : R) * B0) = 0 := by
  intro R A0 B0
  dsimp [A0, B0, R]
  let hdiv : 3^4 ∣ 3^(3*r+3) := by exact pow_dvd_pow 3 (by omega)
  rw [ZMod.cast_sub hdiv]
  rw [ZMod.cast_mul hdiv]
  rw [ZMod.cast_mul hdiv]
  rw [ZMod.cast_pow hdiv]
  have hn3 : (ZMod.cast (((3 * 3^(r-1)).choose (3^(r-1)) : ℕ) : ZMod (3^(3*r+3))) : ZMod (3^4)) =
      (((3 * 3^(r-1)).choose (3^(r-1)) : ℕ) : ZMod (3^4)) := ZMod.cast_natCast hdiv _
  have hn2 : (ZMod.cast (((2 * 3^(r-1)).choose (3^(r-1)) : ℕ) : ZMod (3^(3*r+3))) : ZMod (3^4)) =
      (((2 * 3^(r-1)).choose (3^(r-1)) : ℕ) : ZMod (3^4)) := ZMod.cast_natCast hdiv _
  have h6 : (ZMod.cast (6 : ZMod (3^(3*r+3))) : ZMod (3^4)) = 6 := ZMod.cast_natCast hdiv 6
  have h27 : (ZMod.cast (27 : ZMod (3^(3*r+3))) : ZMod (3^4)) = 27 := ZMod.cast_natCast hdiv 27
  rw [hn3, hn2, h6, h27]
  exact coeff_congruence_mod_3pow4_p3 (s:=r-1) (by omega)

lemma Uprod_minus_one_cast_big_to_3r_minus1_eq_zero_p3 (r x : ℕ) (hr2 : 2 ≤ r) :
    ZMod.castHom (show 3^(3*r-1) ∣ 3^(3*r+3) by exact pow_dvd_pow 3 (by omega)) (ZMod (3^(3*r-1)))
      ((Uprod 3 (3^r) (3*r+3) x : ZMod (3^(3*r+3))) - 1) = 0 := by
  have hp : Nat.Prime 3 := by norm_num
  rw [map_sub, map_one, castHom_Uprod_general (p:=3) (q:=3^r) (M:=3*r-1) (N:=3*r+3) (x:=x) hp (by omega)]
  have h := Uprod_eq_one_mod_3r_minus1_p3 (r:=r) (x:=x) hr2
  rw [h, sub_self]

lemma square_zero_of_castHom_to_3r_minus1_eq_zero_p3 (r : ℕ) (hr2 : 2 ≤ r) (x : ZMod (3^(3*r+3)))
    (hx : ZMod.castHom (show 3^(3*r-1) ∣ 3^(3*r+3) by exact pow_dvd_pow 3 (by omega)) (ZMod (3^(3*r-1))) x = 0) :
    x^2 = 0 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simp only [map_intCast] at hx
  have hzdiv : ((3^(3*r-1) : ℕ) : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z (3^(3*r-1))).mp hx
  rcases hzdiv with ⟨t, ht⟩
  rw [ht]
  norm_num [Int.cast_mul]
  calc
    (((3 : ZMod (3^(3*r+3))) ^ (3*r-1) * (t : ZMod (3^(3*r+3)))) ^ 2)
        = ((3 : ZMod (3^(3*r+3))) ^ (2*(3*r-1))) * (t : ZMod (3^(3*r+3)))^2 := by ring_nf
    _ = 0 := by
      have hpzero : ((3 : ZMod (3^(3*r+3))) ^ (2*(3*r-1))) = 0 := by
        apply zmod_natCast_pow_eq_zero_of_le
        omega
      rw [hpzero, zero_mul]

lemma zmod_mul_eq_zero_of_castHom_pow_eq_zero_E {p A B E : ℕ} (hE : A + B = E)
    (x y : ZMod (p^E))
    (hx : ZMod.castHom (show p^A ∣ p^E by rw [← hE]; exact pow_dvd_pow p (by omega)) (ZMod (p^A)) x = 0)
    (hy : ZMod.castHom (show p^B ∣ p^E by rw [← hE]; exact pow_dvd_pow p (by omega)) (ZMod (p^B)) y = 0) :
    x * y = 0 := by
  obtain ⟨zx, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨zy, rfl⟩ := ZMod.intCast_surjective y
  simp only [map_intCast] at hx hy
  have hdx : ((p^A : ℕ) : ℤ) ∣ zx := (ZMod.intCast_zmod_eq_zero_iff_dvd zx (p^A)).mp hx
  have hdy : ((p^B : ℕ) : ℤ) ∣ zy := (ZMod.intCast_zmod_eq_zero_iff_dvd zy (p^B)).mp hy
  rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases hdx with ⟨tx, htx⟩
  rcases hdy with ⟨ty, hty⟩
  refine ⟨tx * ty, ?_⟩
  rw [htx, hty]
  calc
    (((p ^ A : ℕ) : ℤ) * tx) * (((p ^ B : ℕ) : ℤ) * ty)
        = (((p^A : ℕ) : ℤ) * ((p^B : ℕ) : ℤ)) * (tx * ty) := by ring
    _ = (((p ^ E : ℕ) : ℤ) * (tx * ty)) := by
      congr 1
      norm_cast
      rw [← pow_add, hE]

lemma final_zmod_p_eq_3_r_ge_3 (r : ℕ) (hr3 : 3 ≤ r) :
    let R := ZMod (3^(3*r+3))
    ((((3 * 3^r).choose (3^r) : ℕ) : R)^2 - (27 : R) * (((2 * 3^r).choose (3^r) : ℕ) : R)) =
    ((((3 * 3^(r-1)).choose (3^(r-1)) : ℕ) : R)^2 - (27 : R) * (((2 * 3^(r-1)).choose (3^(r-1)) : ℕ) : R)) := by
  intro R
  let A : R := (((3 * 3^r).choose (3^r) : ℕ) : R)
  let A0 : R := (((3 * 3^(r-1)).choose (3^(r-1)) : ℕ) : R)
  let B : R := (((2 * 3^r).choose (3^r) : ℕ) : R)
  let B0 : R := (((2 * 3^(r-1)).choose (3^(r-1)) : ℕ) : R)
  let u : R := Uprod 3 (3^r) (3*r+3) 2
  let v : R := Uprod 3 (3^r) (3*r+3) 1
  have hp : Nat.Prime 3 := by norm_num
  have hrpos : 0 < r := by omega
  have hr1 : 1 ≤ r := by omega
  have hr2 : 2 ≤ r := by omega
  have hA : A = A0 * u := by
    dsimp [A,A0,u,R]
    have h := choose_ratio_UprodR (p:=3) (r:=r) (c:=3) (N:=3*r+3) hp hr1 (by norm_num)
    rw [h, UprodR_eq_Uprod]
  have hB : B = B0 * v := by
    dsimp [B,B0,v,R]
    have h := choose_ratio_UprodR (p:=3) (r:=r) (c:=2) (N:=3*r+3) hp hr1 (by norm_num)
    rw [h, UprodR_eq_Uprod]
  have hvcast : ZMod.castHom (show 3^(3*r-1) ∣ 3^(3*r+3) by exact pow_dvd_pow 3 (by omega)) (ZMod (3^(3*r-1))) (v - 1) = 0 := by
    dsimp [v,R]
    exact Uprod_minus_one_cast_big_to_3r_minus1_eq_zero_p3 (r:=r) (x:=1) hr2
  have hvnil : (v - 1)^2 = 0 := square_zero_of_castHom_to_3r_minus1_eq_zero_p3 (r:=r) hr2 (v-1) hvcast
  have hsquare := Uprod_square_relation_r_ge_three (p:=3) (q:=3^r) (r:=r) hp hrpos hr3 rfl
  have hrel_square : u^2 - 1 = 3 * (v^2 - 1) := by
    dsimp [u,v,R]
    exact hsquare
  have hrel : u^2 - 1 = 6 * (v - 1) := square_relation_to_linear u v hvnil hrel_square
  have hcoefcast := coeff_cast_big_to_3pow4_p3 (r:=r) hr2
  have hcoef : ((6 : R) * A0^2 - (27 : R) * B0) * (v - 1) = 0 := by
    have hE : 4 + (3*r - 1) = 3*r + 3 := by omega
    have hprod := zmod_mul_eq_zero_of_castHom_pow_eq_zero_E (p:=3) (A:=4) (B:=3*r-1) (E:=3*r+3) hE
      (x := ((6 : R) * A0^2 - (27 : R) * B0)) (y := v - 1) (by
        dsimp [R,A0,B0] at hcoefcast ⊢
        simpa using hcoefcast) (by
        dsimp [R] at hvcast ⊢
        simpa using hvcast)
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hprod
  have hfinal := final_from_ratio_algebra (A:=A) (A0:=A0) (B:=B) (B0:=B0) (u:=u) (v:=v) hA hB hrel hcoef
  dsimp [A,A0,B,B0,R] at hfinal ⊢
  exact hfinal


lemma pair_sum_zero_of_sum_sq_zero {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (f : ι → R) (h2 : IsUnit (2 : R))
    (hsumSq : (∑ i ∈ s, f i)^2 = 0)
    (hsq : (∑ i ∈ s, (f i)^2) = 0) :
    (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i) = 0 := by
  have hsquare := sum_sq_eq_diag_add_offdiag s f
  rw [hsumSq, hsq, zero_add] at hsquare
  have hoff : (∑ p ∈ s.offDiag, f p.1 * f p.2) = 0 := hsquare.symm
  have hdouble := offdiag_sum_eq_two_pairs s f
  rw [hoff] at hdouble
  have hmul : (2 : R) * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i) = 0 := hdouble.symm
  rw [mul_comm] at hmul
  exact (IsUnit.mul_left_eq_zero h2).mp hmul

lemma Finset.prod_one_add_eq_one_add_sum_of_sum_sq_zero
    {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (f : ι → R) (h2 : IsUnit (2 : R))
    (hsumSq : (∑ i ∈ s, f i)^2 = 0)
    (hsq : (∑ i ∈ s, (f i)^2) = 0)
    (htriple : ∀ t, t ⊆ s → 3 ≤ t.card → (∏ i ∈ t, f i) = 0) :
    ∏ i ∈ s, (1 + f i) = 1 + ∑ i ∈ s, f i := by
  rw [Finset.prod_one_add_eq_sum_powersetCard_le_two_of_large_zero s f htriple]
  rw [Finset.sum_powersetCard_zero_prod]
  rw [Finset.sum_powersetCard_one_prod]
  have hpairs := pair_sum_zero_of_sum_sq_zero s f h2 hsumSq hsq
  rw [hpairs]
  ring




lemma sum_units_cast_inv_four_zmod_eq_zero_p_ge_7 (p : ℕ) [NeZero (p^2)] (hp : Nat.Prime p) (hp7 : p ≥ 7) :
    (∑ u : (ZMod (p^2))ˣ,
      (ZMod.castHom (show p ∣ p^2 by exact dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)
        (((u⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4) = 0 := by
  classical
  have hdiv : p ∣ p^2 := by exact dvd_pow_self p (by norm_num : 2 ≠ 0)
  let phi : ZMod (p^2) →+* ZMod p := ZMod.castHom hdiv (ZMod p)
  have h2not : ¬ p ∣ 2 := by
    intro h
    have hp_le_2 := Nat.le_of_dvd (by norm_num) h
    omega
  have hcop2p : Nat.Coprime 2 p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr h2not)
  have hcop2p2 : Nat.Coprime 2 (p^2) := hcop2p.pow_right 2
  let t : (ZMod (p^2))ˣ := ZMod.unitOfCoprime 2 hcop2p2
  have ht : phi (t : ZMod (p^2)) = (2 : ZMod p) := by
    dsimp [t, phi]
    exact ZMod.cast_natCast hdiv 2
  let S : ZMod p := ∑ u : (ZMod (p^2))ˣ, (phi (((u⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4
  have hperm : S = ∑ u : (ZMod (p^2))ˣ, (phi ((((t * u)⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4 := by
    dsimp [S]
    let e : (ZMod (p^2))ˣ ≃ (ZMod (p^2))ˣ := Equiv.mulLeft t
    have h := Fintype.sum_equiv e
      (fun u : (ZMod (p^2))ˣ => (phi ((((t * u)⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4)
      (fun u : (ZMod (p^2))ˣ => (phi (((u⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4)
      (by intro u; rfl)
    exact h.symm
  have hscale : (∑ u : (ZMod (p^2))ˣ, (phi ((((t * u)⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4)
      = (phi (((t⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4 * S := by
    dsimp [S]
    simp only [mul_inv_rev, Units.val_mul, map_mul, Finset.mul_sum]
    simp [mul_pow, mul_comm, mul_assoc]
  have hS : S = (phi (((t⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4 * S := hperm.trans hscale
  have hz : (1 - (phi (((t⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4) * S = 0 := by
    calc (1 - (phi (((t⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4) * S
      _ = S - (phi (((t⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4 * S := by ring
      _ = 0 := by
        nth_rewrite 1 [hS]
        rw [sub_self]
  have hfacmul : (1 - (phi (((t⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4) * (2 : ZMod p)^4 = 15 := by
    rw [sub_mul, one_mul]
    have hinv : phi (((t⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))) * phi (t : ZMod (p^2)) = 1 := by
      rw [← map_mul]
      simp
    have hinvpow : (phi (((t⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4 * (phi (t : ZMod (p^2)))^4 = 1 := by
      rw [← mul_pow, hinv, one_pow]
    rw [← ht]
    rw [hinvpow]
    rw [ht]
    norm_num
  have h15unit : IsUnit (15 : ZMod p) := by
    have hnot : ¬ p ∣ 15 := by
      intro h
      have h35 : p ∣ 3 * 5 := by simpa using h
      rcases hp.dvd_mul.mp h35 with h3 | h5
      · have hp_le_3 := Nat.le_of_dvd (by norm_num) h3
        omega
      · have hp_le_5 := Nat.le_of_dvd (by norm_num) h5
        omega
    exact (ZMod.isUnit_iff_coprime 15 p).mpr (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hnot))
  have hfacunit : IsUnit (1 - (phi (((t⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4) := by
    apply isUnit_of_mul_isUnit_left (x := (1 - (phi (((t⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4)) (y := (2 : ZMod p)^4)
    rw [hfacmul]
    exact h15unit
  have hSzero : S = 0 := (IsUnit.mul_right_eq_zero hfacunit).mp hz
  simpa [S, phi]
    using hSzero

lemma sum_nondiv_inv_four_mod_p_eq_units_cast (p : ℕ) [NeZero (p^2)] (hp : Nat.Prime p) :
    let phi : ZMod (p^2) →+* ZMod p := ZMod.castHom (show p ∣ p^2 by exact dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)
    (∑ k ∈ nondivSet p (p^2), ((k : ZMod p)⁻¹)^4)
    = (∑ u : (ZMod (p^2))ˣ, (phi (((u⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro phi
  let f : ℕ → ZMod p := fun k => ((k : ZMod p)⁻¹)^4
  let g : (ZMod (p^2))ˣ → ZMod p := fun u => (phi (((u⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))))^4
  symm
  have hrpos : 0 < 2 := by norm_num
  have hb : (∑ u ∈ (Finset.univ : Finset (ZMod (p^2))ˣ), g u) = ∑ k ∈ nondivSet p (p^2), f k := by
    refine Finset.sum_bij (s := (Finset.univ : Finset (ZMod (p^2))ˣ)) (t := nondivSet p (p^2)) (f := g) (g := f) (fun u _ => (u : ZMod (p^2)).val) ?_ ?_ ?_ ?_
    · intro u hu
      rw [nondivSet_mem]
      have hlt := (u : ZMod (p^2)).val_lt
      have hcop := ZMod.val_coe_unit_coprime u
      have hpos : 1 ≤ (u : ZMod (p^2)).val := by
        have hne : (u : ZMod (p^2)).val ≠ 0 := by
          intro h0
          have hcop0 : Nat.Coprime 0 (p^2) := by simpa [h0] using hcop
          have hp_dvd_pow : p ∣ p^2 := by exact dvd_pow_self p (by norm_num : 2 ≠ 0)
          rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_zero_left] at hcop0
          exact hp.not_dvd_one (by rwa [hcop0] at hp_dvd_pow)
        omega
      constructor
      · exact hpos
      constructor
      · exact Nat.lt_succ_of_lt hlt
      · intro hd
        have hpcop : Nat.Coprime p (p^2) := hcop.coprime_dvd_left hd
        have hp_dvd : p ∣ p^2 := by exact dvd_pow_self p (by norm_num : 2 ≠ 0)
        exact ((hp.coprime_iff_not_dvd).mp hpcop) hp_dvd
    · intro u1 hu1 u2 hu2 hval
      apply Units.ext
      rw [← ZMod.natCast_zmod_val (u1 : ZMod (p^2)), ← ZMod.natCast_zmod_val (u2 : ZMod (p^2))]
      exact congr_arg (fun n : ℕ => (n : ZMod (p^2))) hval
    · intro k hk
      rw [nondivSet_mem] at hk
      let u : (ZMod (p^2))ˣ := ZMod.unitOfCoprime k (nondiv_coprime_pow (p:=p) (r:=2) hp hk.2.2)
      refine ⟨u, Finset.mem_univ u, ?_⟩
      dsimp [u]
      have hklt : k < p^2 := by
        have hneq : k ≠ p^2 := by
          intro h
          exact hk.2.2 (by rw [h]; exact dvd_pow_self p (by norm_num : 2 ≠ 0))
        omega
      rw [ZMod.val_natCast_of_lt hklt]
    · intro u hu
      dsimp [f,g]
      have hinv : phi (((u⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))) = (phi (u : ZMod (p^2)))⁻¹ := by
        have hmul : (phi (u : ZMod (p^2))) * phi (((u⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2))) = 1 := by
          rw [← map_mul]
          simp
        exact (ZMod.inv_eq_of_mul_eq_one p (phi (u : ZMod (p^2))) (phi (((u⁻¹ : (ZMod (p^2))ˣ) : ZMod (p^2)))) hmul).symm
      have hphiu : phi (u : ZMod (p^2)) = (((u : ZMod (p^2)).val : ℕ) : ZMod p) := by
        rw [← ZMod.natCast_zmod_val (u : ZMod (p^2))]
        simp [phi]
      rw [hinv, hphiu]
  dsimp [f,g] at hb
  simpa using hb

lemma sum_nondiv_inv_four_mod_p_eq_zero_p_ge_7 (p : ℕ) [NeZero (p^2)] (hp : Nat.Prime p) (hp7 : p ≥ 7) :
    (∑ k ∈ nondivSet p (p^2), ((k : ZMod p)⁻¹)^4) = 0 := by
  rw [sum_nondiv_inv_four_mod_p_eq_units_cast (p:=p) hp]
  exact sum_units_cast_inv_four_zmod_eq_zero_p_ge_7 (p:=p) hp hp7

lemma intCast_mul_eq_zero_of_dvd_and_castHom_p_eq_zero {p B E : ℕ} (hE : B + 1 = E)
    (c : ℤ) (y : ZMod (p^E))
    (hc : ((p^B : ℕ) : ℤ) ∣ c)
    (hy : ZMod.castHom (show p ∣ p^E by rw [← hE]; exact dvd_pow_self p (by omega)) (ZMod p) y = 0) :
    (c : ZMod (p^E)) * y = 0 := by
  obtain ⟨zy, rfl⟩ := ZMod.intCast_surjective y
  simp only [map_intCast] at hy
  have hdy : (p : ℤ) ∣ zy := (ZMod.intCast_zmod_eq_zero_iff_dvd zy p).mp hy
  rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases hc with ⟨tx, htx⟩
  rcases hdy with ⟨ty, hty⟩
  refine ⟨tx * ty, ?_⟩
  rw [htx, hty]
  calc
    (((p ^ B : ℕ) : ℤ) * tx) * ((p : ℤ) * ty)
        = (((p^B : ℕ) : ℤ) * (p : ℤ)) * (tx * ty) := by ring
    _ = (((p ^ E : ℕ) : ℤ) * (tx * ty)) := by
      congr 1
      norm_cast
      rw [← pow_succ, show B + 1 = E from hE]



lemma sum_pair_g_sq_eq_zero_r2_p_ge_7 (p : ℕ) (hp : Nat.Prime p) (hp7 : p ≥ 7) :
    let R := ZMod (p^9)
    (∑ k ∈ nondivSet p (p^2),
      ((((p : R)^4) * (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹))^2)) = 0 := by
  classical
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  intro R
  let T : R := ∑ k ∈ nondivSet p (p^2), ((k : R)⁻¹)^2 * (((((p^2 : ℕ) - k) : R)⁻¹)^2)
  have hfactor : (∑ k ∈ nondivSet p (p^2), ((((p : R)^4) * (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹))^2))
      = ((p : R)^8) * T := by
    dsimp [T]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkdata := nondivSet_mem.mp hk
    have hle : k ≤ p^2 := Nat.lt_succ_iff.mp hkdata.2.1
    rw [Nat.cast_sub hle]
    norm_num [Nat.cast_pow]
    ring
  rw [hfactor]
  have hy : ZMod.castHom (show p ∣ p^9 by exact dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p) T = 0 := by
    let phi9 : R →+* ZMod p := ZMod.castHom (show p ∣ p^9 by exact dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)
    change phi9 T = 0
    dsimp [T]
    rw [map_sum phi9]
    have hsum4 := sum_nondiv_inv_four_mod_p_eq_zero_p_ge_7 (p:=p) hp hp7
    convert hsum4 using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_mul, map_pow, map_pow]
    have hknd : ¬ p ∣ k := (nondivSet_mem.mp hk).2.2
    have hkqmem : p^2 - k ∈ nondivSet p (p^2) := nondivSet_invol_mem (p:=p) (q:=p^2) (r:=2) hp rfl (by norm_num) hk
    have hkqnd : ¬ p ∣ p^2 - k := (nondivSet_mem.mp hkqmem).2.2
    have hkdata0 := nondivSet_mem.mp hk
    have hle0 : k ≤ p^2 := Nat.lt_succ_iff.mp hkdata0.2.1
    have hsubR : (((p^2 - k : ℕ) : R)) = (((p^2 : ℕ) : R) - (k : R)) := by rw [Nat.cast_sub hle0]
    rw [← hsubR]

    have hki : phi9 ((k : R)⁻¹) = ((k : ZMod p)⁻¹) := by
      have huR : IsUnit (k : R) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=9) hp hknd
      have hmapk : phi9 (k : R) = (k : ZMod p) := by simp [phi9]
      have hmul : (k : ZMod p) * phi9 ((k : R)⁻¹) = 1 := by
        rw [← hmapk, ← map_mul, ZMod.mul_inv_of_unit _ huR, map_one]
      exact (ZMod.inv_eq_of_mul_eq_one p (k : ZMod p) (phi9 ((k : R)⁻¹)) hmul).symm
    have hqki : phi9 ((((p^2 - k : ℕ) : R)⁻¹)) = ((((p^2 - k : ℕ) : ZMod p))⁻¹) := by
      have huR : IsUnit ((p^2 - k : ℕ) : R) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=9) hp hkqnd
      have hmapk : phi9 ((p^2 - k : ℕ) : R) = ((p^2 - k : ℕ) : ZMod p) := by simp [phi9]
      have hmul : ((p^2 - k : ℕ) : ZMod p) * phi9 ((((p^2 - k : ℕ) : R)⁻¹)) = 1 := by
        rw [← hmapk, ← map_mul, ZMod.mul_inv_of_unit _ huR, map_one]
      exact (ZMod.inv_eq_of_mul_eq_one p ((p^2 - k : ℕ) : ZMod p) (phi9 ((((p^2 - k : ℕ) : R)⁻¹))) hmul).symm
    have hqk : (((p^2 - k : ℕ) : ZMod p)) = - (k : ZMod p) := by
      have hkdata := nondivSet_mem.mp hk
      have hle : k ≤ p^2 := Nat.lt_succ_iff.mp hkdata.2.1
      have hsum : (k : ZMod p) + ((p^2-k : ℕ) : ZMod p) = 0 := by
        calc
          (k : ZMod p) + ((p^2-k : ℕ) : ZMod p) = ((k + (p^2-k) : ℕ) : ZMod p) := by rw [Nat.cast_add]
          _ = (((p^2 : ℕ) : ZMod p)) := by rw [Nat.add_sub_of_le hle]
          _ = (p : ZMod p)^2 := by rw [Nat.cast_pow]
          _ = 0 := by
            rw [ZMod.natCast_self, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      exact eq_neg_of_add_eq_zero_right hsum
    rw [hki, hqki, hqk]
    simp [inv_neg]
    ring


  have hmul := intCast_mul_eq_zero_of_dvd_and_castHom_p_eq_zero (p:=p) (B:=8) (E:=9) (by norm_num)
      (c := ((p^8 : ℕ) : ℤ)) (y := T) (by exact dvd_rfl) hy
  simpa [Nat.cast_pow, Int.cast_natCast] using hmul


lemma sum_nondiv_inv_sq_mod_p_of_p_ge_5 (p : ℕ) [NeZero (p^2)] [NeZero p]
    (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    (∑ k ∈ nondivSet p (p^2), ((k : ZMod p)⁻¹)^2) = 0 := by
  classical
  have hbig : (∑ k ∈ nondivSet p (p^2), ((k : ZMod (p^2))⁻¹)^2) = 0 := by
    exact sum_nondiv_inv_sq_zmod_eq_zero' (p:=p) (r:=2) hp hp5 (by norm_num)
  let phi : ZMod (p^2) →+* ZMod p := ZMod.castHom (show p ∣ p^2 by exact dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)
  have hcast := congrArg phi hbig
  rw [map_zero] at hcast
  rw [map_sum phi] at hcast
  rw [← hcast]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_pow]
  have hknd : ¬ p ∣ k := (nondivSet_mem.mp hk).2.2
  have hki : phi ((k : ZMod (p^2))⁻¹) = ((k : ZMod p)⁻¹) := by
    have huR : IsUnit (k : ZMod (p^2)) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=2) hp hknd
    have hmapk : phi (k : ZMod (p^2)) = (k : ZMod p) := by simp [phi]
    have hmul : (k : ZMod p) * phi ((k : ZMod (p^2))⁻¹) = 1 := by
      rw [← hmapk, ← map_mul, ZMod.mul_inv_of_unit _ huR, map_one]
    exact (ZMod.inv_eq_of_mul_eq_one p (k : ZMod p) (phi ((k : ZMod (p^2))⁻¹)) hmul).symm
  rw [hki]


lemma sum_pair_g_square_eq_zero_r2_p_ge_7 (p : ℕ) (hp : Nat.Prime p) (hp7 : p ≥ 7) :
    let R := ZMod (p^9)
    (∑ k ∈ nondivSet p (p^2),
      ((p : R)^4 * (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹)))^2 = 0 := by
  classical
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  intro R
  let T : R := ∑ k ∈ nondivSet p (p^2), (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹)
  have hfactor : (∑ k ∈ nondivSet p (p^2),
      ((p : R)^4 * (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹))) = (p : R)^4 * T := by
    dsimp [T]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hfactor]
  have hy : ZMod.castHom (show p ∣ p^9 by exact dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p) T = 0 := by
    let phi9 : R →+* ZMod p := ZMod.castHom (show p ∣ p^9 by exact dvd_pow_self p (by norm_num : 9 ≠ 0)) (ZMod p)
    change phi9 T = 0
    dsimp [T]
    rw [map_sum phi9]
    have hsum2 := sum_nondiv_inv_sq_mod_p_of_p_ge_5 (p:=p) hp (by omega)
    calc
      (∑ x ∈ nondivSet p (p ^ 2), phi9 ((x : R)⁻¹ * (((p ^ 2 - x : ℕ) : R)⁻¹)))
          = - (∑ x ∈ nondivSet p (p ^ 2), ((x : ZMod p)⁻¹)^2) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            rw [map_mul]
            have hknd : ¬ p ∣ k := (nondivSet_mem.mp hk).2.2
            have hkqmem : p^2 - k ∈ nondivSet p (p^2) := nondivSet_invol_mem (p:=p) (q:=p^2) (r:=2) hp rfl (by norm_num) hk
            have hkqnd : ¬ p ∣ p^2 - k := (nondivSet_mem.mp hkqmem).2.2
            have hki : phi9 ((k : R)⁻¹) = ((k : ZMod p)⁻¹) := by
              have huR : IsUnit (k : R) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=9) hp hknd
              have hmapk : phi9 (k : R) = (k : ZMod p) := by simp [phi9]
              have hmul : (k : ZMod p) * phi9 ((k : R)⁻¹) = 1 := by
                rw [← hmapk, ← map_mul, ZMod.mul_inv_of_unit _ huR, map_one]
              exact (ZMod.inv_eq_of_mul_eq_one p (k : ZMod p) (phi9 ((k : R)⁻¹)) hmul).symm
            have hqki : phi9 ((((p^2 - k : ℕ) : R)⁻¹)) = ((((p^2 - k : ℕ) : ZMod p))⁻¹) := by
              have huR : IsUnit ((p^2 - k : ℕ) : R) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=9) hp hkqnd
              have hmapk : phi9 ((p^2 - k : ℕ) : R) = ((p^2 - k : ℕ) : ZMod p) := by simp [phi9]
              have hmul : ((p^2 - k : ℕ) : ZMod p) * phi9 ((((p^2 - k : ℕ) : R)⁻¹)) = 1 := by
                rw [← hmapk, ← map_mul, ZMod.mul_inv_of_unit _ huR, map_one]
              exact (ZMod.inv_eq_of_mul_eq_one p ((p^2 - k : ℕ) : ZMod p) (phi9 ((((p^2 - k : ℕ) : R)⁻¹))) hmul).symm
            have hqk : (((p^2 - k : ℕ) : ZMod p)) = - (k : ZMod p) := by
              have hkdata := nondivSet_mem.mp hk
              have hle : k ≤ p^2 := Nat.lt_succ_iff.mp hkdata.2.1
              have hsum : (k : ZMod p) + ((p^2-k : ℕ) : ZMod p) = 0 := by
                calc
                  (k : ZMod p) + ((p^2-k : ℕ) : ZMod p) = ((k + (p^2-k) : ℕ) : ZMod p) := by rw [Nat.cast_add]
                  _ = (((p^2 : ℕ) : ZMod p)) := by rw [Nat.add_sub_of_le hle]
                  _ = (p : ZMod p)^2 := by rw [Nat.cast_pow]
                  _ = 0 := by rw [ZMod.natCast_self, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
              exact eq_neg_of_add_eq_zero_right hsum
            rw [hki, hqki, hqk]
            have hinvneg : (-(k : ZMod p))⁻¹ = -((k : ZMod p)⁻¹) := by simpa using (inv_neg (a := (k : ZMod p)))
            rw [hinvneg]
            ring
      _ = 0 := by rw [hsum2, neg_zero]
  have hmul := intCast_mul_eq_zero_of_dvd_and_castHom_p_eq_zero (p:=p) (B:=8) (E:=9) (by norm_num)
      (c := ((p^8 : ℕ) : ℤ)) (y := T^2) (by exact dvd_rfl) (by
        rw [map_pow, hy, zero_pow (by norm_num : (2:ℕ) ≠ 0)])
  calc
    (((p : R)^4 * T)^2) = (p : R)^8 * T^2 := by ring
    _ = 0 := by simpa [Nat.cast_pow, Int.cast_natCast] using hmul

lemma paired_product_linear_r2_p_ge_7 (p c : ℕ) (hp : Nat.Prime p) (hp7 : p ≥ 7) :
    let R := ZMod (p^9)
    (∏ k ∈ nondivSet p (p^2),
        (1 + (c : R) * (p : R)^4 * (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹)))
      = 1 + ∑ k ∈ nondivSet p (p^2),
        ((c : R) * (p : R)^4 * (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹)) := by
  classical
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  intro R
  let s := nondivSet p (p^2)
  let g : ℕ → R := fun k => (p : R)^4 * (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹)
  let f : ℕ → R := fun k => (c : R) * (p : R)^4 * (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹)
  change (∏ k ∈ s, (1 + f k)) = 1 + ∑ k ∈ s, f k
  have hnot2 : ¬ p ∣ 2 := by
    intro h
    have hp_le_2 := Nat.le_of_dvd (by norm_num) h
    omega
  have h2unit : IsUnit (2 : R) := zmod_isUnit_nat_of_not_dvd (p:=p) (N:=9) hp hnot2
  apply Finset.prod_one_add_eq_one_add_sum_of_sum_sq_zero (s:=s) (f:=f) h2unit
  · dsimp [f, g, s]
    have hbase := sum_pair_g_square_eq_zero_r2_p_ge_7 (p:=p) hp hp7
    dsimp at hbase
    calc
      (∑ k ∈ nondivSet p (p ^ 2), (c : R) * (p : R)^4 * (k : R)⁻¹ * (((p ^ 2 - k : ℕ) : R)⁻¹)) ^ 2
          = (c : R)^2 * (∑ k ∈ nondivSet p (p ^ 2), ((p : R)^4 * (k : R)⁻¹ * (((p ^ 2 - k : ℕ) : R)⁻¹)))^2 := by
            have hsum : (∑ k ∈ nondivSet p (p ^ 2), (c : R) * (p : R)^4 * (k : R)⁻¹ * (((p ^ 2 - k : ℕ) : R)⁻¹))
                = (c : R) * (∑ k ∈ nondivSet p (p ^ 2), ((p : R)^4 * (k : R)⁻¹ * (((p ^ 2 - k : ℕ) : R)⁻¹))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring
            rw [hsum]
            ring
      _ = 0 := by rw [hbase, mul_zero]
  · dsimp [f, g, s]
    have hbase := sum_pair_g_sq_eq_zero_r2_p_ge_7 (p:=p) hp hp7
    dsimp at hbase
    calc
      (∑ k ∈ nondivSet p (p ^ 2), ((c : R) * (p : R)^4 * (k : R)⁻¹ * (((p ^ 2 - k : ℕ) : R)⁻¹)) ^ 2)
          = (c : R)^2 * (∑ k ∈ nondivSet p (p ^ 2), (((p : R)^4 * (k : R)⁻¹ * (((p ^ 2 - k : ℕ) : R)⁻¹))^2)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = 0 := by rw [hbase, mul_zero]
  · intro t hts htcard
    dsimp [f, g, s]
    calc
      (∏ i ∈ t, (c : R) * (p : R)^4 * (i : R)⁻¹ * (((p ^ 2 - i : ℕ) : R)⁻¹))
          = (∏ i ∈ t, (p : R)^4) * (∏ i ∈ t, (c : R) * ((i : R)⁻¹ * (((p ^ 2 - i : ℕ) : R)⁻¹))) := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro i hi
            ring
      _ = (((p : R)^4) ^ t.card) * (∏ i ∈ t, (c : R) * ((i : R)⁻¹ * (((p ^ 2 - i : ℕ) : R)⁻¹))) := by rw [Finset.prod_const]
      _ = 0 := by



        have hpzero : (((p : R)^4) ^ t.card) = 0 := by
          rw [← pow_mul]
          apply zmod_natCast_pow_eq_zero_of_le
          nlinarith [htcard]
        rw [hpzero, zero_mul]

lemma Uprod_square_relation_r2_p_ge_7 (p : ℕ) (hp : Nat.Prime p) (hp7 : p ≥ 7) :
    let R := ZMod (p^9)
    (Uprod p (p^2) 9 2 : R)^2 - 1 = 3 * ((Uprod p (p^2) 9 1 : R)^2 - 1) := by
  intro R
  have h2 := product_square_paired (p:=p) (q:=p^2) (r:=2) (N:=9) (x:=2) hp rfl (by norm_num)
  have h1 := product_square_paired (p:=p) (q:=p^2) (r:=2) (N:=9) (x:=1) hp rfl (by norm_num)
  have lin6 := paired_product_linear_r2_p_ge_7 (p:=p) (c:=6) hp hp7
  have lin2 := paired_product_linear_r2_p_ge_7 (p:=p) (c:=2) hp hp7
  dsimp [Uprod]
  dsimp at h2 h1 lin6 lin2
  rw [h2, h1]
  have lin6' :
      (∏ k ∈ nondivSet p (p ^ 2),
        (1 + (6 : R) * ((p ^ 2 : ℕ) : R)^2 * (k : R)⁻¹ * (((p ^ 2 - k : ℕ) : R)⁻¹)))
      = 1 + ∑ k ∈ nondivSet p (p^2),
        ((6 : R) * ((p ^ 2 : ℕ) : R)^2 * (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹)) := by
    simpa [Nat.cast_pow, ← pow_mul, mul_assoc] using lin6
  have lin2' :
      (∏ k ∈ nondivSet p (p ^ 2),
        (1 + (2 : R) * ((p ^ 2 : ℕ) : R)^2 * (k : R)⁻¹ * (((p ^ 2 - k : ℕ) : R)⁻¹)))
      = 1 + ∑ k ∈ nondivSet p (p^2),
        ((2 : R) * ((p ^ 2 : ℕ) : R)^2 * (k : R)⁻¹ * (((p^2 - k : ℕ) : R)⁻¹)) := by
    simpa [Nat.cast_pow, ← pow_mul, mul_assoc] using lin2
  norm_num at lin6' lin2' ⊢
  rw [lin6', lin2']
  simp only [add_sub_cancel_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma final_zmod_p_ge_7_r_eq_2 (p : ℕ) (hp : Nat.Prime p) (hp7 : p ≥ 7) :
    let R := ZMod (p^9)
    ((((3 * p^2).choose (p^2) : ℕ) : R)^2 - (27 : R) * (((2 * p^2).choose (p^2) : ℕ) : R)) =
    ((((3 * p^(2-1)).choose (p^(2-1)) : ℕ) : R)^2 - (27 : R) * (((2 * p^(2-1)).choose (p^(2-1)) : ℕ) : R)) := by
  intro R
  have hp5 : p ≥ 5 := by omega
  let A : R := (((3 * p^2).choose (p^2) : ℕ) : R)
  let A0 : R := (((3 * p^(2-1)).choose (p^(2-1)) : ℕ) : R)
  let B : R := (((2 * p^2).choose (p^2) : ℕ) : R)
  let B0 : R := (((2 * p^(2-1)).choose (p^(2-1)) : ℕ) : R)
  let u : R := Uprod p (p^2) 9 2
  let v : R := Uprod p (p^2) 9 1
  have hA : A = A0 * u := by
    dsimp [A,A0,u,R]
    have h := choose_ratio_UprodR (p:=p) (r:=2) (c:=3) (N:=9) hp (by norm_num) (by norm_num)
    rw [h, UprodR_eq_Uprod]
  have hB : B = B0 * v := by
    dsimp [B,B0,v,R]
    have h := choose_ratio_UprodR (p:=p) (r:=2) (c:=2) (N:=9) hp (by norm_num) (by norm_num)
    rw [h, UprodR_eq_Uprod]
  have hvcast : ZMod.castHom (show p^6 ∣ p^9 by exact pow_dvd_pow p (by norm_num)) (ZMod (p^6)) (v - 1) = 0 := by
    dsimp [v,R]
    simpa using Uprod_minus_one_cast_big_to_3r_eq_zero_of_p_ge_5 (p:=p) (r:=2) (x:=1) hp hp5 (by norm_num)
  have hvnil : (v - 1)^2 = 0 := by
    simpa using square_zero_of_castHom_to_3r_eq_zero (p:=p) (r:=2) (by norm_num) (v-1) hvcast
  have hsquare := Uprod_square_relation_r2_p_ge_7 (p:=p) hp hp7
  have hrel_square : u^2 - 1 = 3 * (v^2 - 1) := by
    dsimp [u,v,R]
    exact hsquare
  have hrel : u^2 - 1 = 6 * (v - 1) := square_relation_to_linear u v hvnil hrel_square
  have hcoefcast := coeff_cast_big_to_p3_eq_zero_p_ge_5 (p:=p) (r:=2) hp hp5
  have hcoef : ((6 : R) * A0^2 - (27 : R) * B0) * (v - 1) = 0 := by
    have hprod := zmod_mul_eq_zero_of_castHom_pow_eq_zero (p:=p) (A:=6) (B:=3)
      (x := v - 1) (y := ((6 : R) * A0^2 - (27 : R) * B0)) hvcast (by
        dsimp [R,A0,B0] at hcoefcast ⊢
        simpa using hcoefcast)
    simpa [mul_comm] using hprod
  have hfinal := final_from_ratio_algebra (A:=A) (A0:=A0) (B:=B) (B0:=B0) (u:=u) (v:=v) hA hB hrel hcoef
  dsimp [A,A0,B,B0,R] at hfinal ⊢
  exact hfinal

lemma final_zmod_p_eq_3_r_eq_2 :
    let R := ZMod (3^9)
    ((((3 * 3^2).choose (3^2) : ℕ) : R)^2 - (27 : R) * (((2 * 3^2).choose (3^2) : ℕ) : R)) =
    ((((3 * 3^(2-1)).choose (3^(2-1)) : ℕ) : R)^2 - (27 : R) * (((2 * 3^(2-1)).choose (3^(2-1)) : ℕ) : R)) := by
  change ((4686825 : ZMod (3^9))^2 - (27 : ZMod (3^9)) * (48620 : ZMod (3^9)) =
    (84 : ZMod (3^9))^2 - (27 : ZMod (3^9)) * (20 : ZMod (3^9)))
  rw [← sub_eq_zero]
  change ((21966327261369 : ℕ) : ZMod (3^9)) = 0
  rw [← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

lemma final_zmod_p_eq_5_r_eq_2 :
    let R := ZMod (5^9)
    ((((3 * 5^2).choose (5^2) : ℕ) : R)^2 - (27 : R) * (((2 * 5^2).choose (5^2) : ℕ) : R)) =
    ((((3 * 5^(2-1)).choose (5^(2-1)) : ℕ) : R)^2 - (27 : R) * (((2 * 5^(2-1)).choose (5^(2-1)) : ℕ) : R)) := by
  change ((52588547141148893628 : ZMod (5^9))^2 - (27 : ZMod (5^9)) * (126410606437752 : ZMod (5^9)) =
    (3003 : ZMod (5^9))^2 - (27 : ZMod (5^9)) * (252 : ZMod (5^9)))
  rw [← sub_eq_zero]
  change ((2765555290416839473031163791322076171875 : ℕ) : ZMod (5^9)) = 0
  rw [← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

lemma final_zmod_all (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    let R := ZMod (p^(3*r+3))
    ((((3 * p^r).choose (p^r) : ℕ) : R)^2 - (27 : R) * (((2 * p^r).choose (p^r) : ℕ) : R)) =
    ((((3 * p^(r-1)).choose (p^(r-1)) : ℕ) : R)^2 - (27 : R) * (((2 * p^(r-1)).choose (p^(r-1)) : ℕ) : R)) := by
  by_cases hr2eq : r = 2
  · subst r
    by_cases hp3eq : p = 3
    · subst p
      simpa using final_zmod_p_eq_3_r_eq_2
    · by_cases hp5eq : p = 5
      · subst p
        simpa using final_zmod_p_eq_5_r_eq_2
      · have hpne4 : p ≠ 4 := by intro h; subst p; norm_num at hp
        have hpne6 : p ≠ 6 := by intro h; subst p; norm_num at hp
        have hp7 : p ≥ 7 := by omega
        simpa using final_zmod_p_ge_7_r_eq_2 (p:=p) hp hp7
  · have hr3 : 3 ≤ r := by omega
    by_cases hp3eq : p = 3
    · subst p
      simpa using final_zmod_p_eq_3_r_ge_3 (r:=r) hr3
    · have hpne4 : p ≠ 4 := by intro h; subst p; norm_num at hp
      have hp5 : p ≥ 5 := by omega
      simpa using final_zmod_p_ge_5_r_ge_3 (p:=p) (r:=r) hp hp5 hr3


def aa (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

theorem final_int_modEq_all (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    aa (p ^ r) ≡ aa (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  let E := 3*r+3
  have hz := final_zmod_all (p:=p) (r:=r) hp hp3 hr
  dsimp at hz
  rw [Int.modEq_iff_dvd]
  have hnatdvd : ((p^E : ℕ) : ℤ) ∣ aa (p ^ (r - 1)) - aa (p ^ r) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (aa (p ^ (r - 1)) - aa (p ^ r)) (p^E)]
    change (((aa (p ^ (r - 1)) - aa (p ^ r) : ℤ) : ZMod (p^E)) = 0)
    rw [Int.cast_sub]
    dsimp [aa, E]
    norm_num [Int.cast_sub, Int.cast_mul, Int.cast_pow]
    exact sub_eq_zero.mpr hz.symm
  dsimp [E] at hnatdvd
  change (((p ^ (3 * r + 3) : ℕ) : ℤ) ∣ aa (p ^ (r - 1)) - aa (p ^ r))
  exact hnatdvd











/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] :=
by
  simpa [a, aa] using final_int_modEq_all p r hp hp3 hr
