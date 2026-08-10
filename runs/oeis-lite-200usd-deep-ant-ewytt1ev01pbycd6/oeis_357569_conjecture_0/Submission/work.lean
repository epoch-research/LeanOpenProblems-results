import FormalConjectures.Util.ProblemImports
open Nat
open scoped BigOperators

namespace Work

variable (p : ℕ)

/-- reduced residues in [0, p^m): {t : 0 ≤ t < p^m, ¬ p ∣ t}. -/
def Tset (m : ℕ) : Finset ℕ := (Finset.range (p^m)).filter (fun t => ¬ p ∣ t)

/-- G_c at level m : ∏_{t ∈ Tset} (t + c·p^m). -/
def Gp (m : ℕ) (c : ℤ) : ℤ := ∏ t ∈ Tset p m, ((t : ℤ) + c * (p^m : ℤ))

/-- w := v_p(3): 1 if p = 3 else 0. -/
def wv : ℕ := if p = 3 then 1 else 0

/-! ## The seven key lemmas (to be proven). -/

theorem G0_unit (m : ℕ) [hp : Fact p.Prime] : ¬ (p:ℤ) ∣ Gp p m 0 := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp.out
  unfold Gp
  simp only [zero_mul, add_zero]
  rw [hpp.dvd_finset_prod_iff]
  push_neg
  intro t ht
  simp only [Tset, Finset.mem_filter, Finset.mem_range] at ht
  intro hdvd
  exact ht.2 (by exact_mod_cast hdvd)

def GpN (m c : ℕ) : ℕ := ∏ t ∈ Tset p m, (t + c * p^m)

/-- The "coprime part" product: ∏_{k ∈ [1,L], ¬ p ∣ k} k. -/
def QR (L : ℕ) : ℕ := ∏ k ∈ (Finset.Icc 1 L).filter (fun k => ¬ p ∣ k), k

/-- `∏_{i ∈ [1,L]} i = L!`. -/
theorem prod_Icc_id : ∀ (L : ℕ), ∏ i ∈ Finset.Icc 1 L, i = L ! := by
  intro L
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega : (1:ℕ) ≤ n + 1), ih, Nat.factorial_succ]
    ring

/-- FACT_SPLIT: for `L = q*p`, `(q*p)! = p^q * q! * QR(q*p)`. -/
theorem FS (q : ℕ) [hp : Fact p.Prime] : (q * p)! = p ^ q * q ! * QR p (q * p) := by
  have hp0 : 0 < p := hp.out.pos
  have hPdvd : (∏ x ∈ (Finset.Icc 1 (q * p)).filter (fun k => p ∣ k), x) = p ^ q * q ! := by
    have hbij : (∏ x ∈ (Finset.Icc 1 (q * p)).filter (fun k => p ∣ k), x)
              = ∏ j ∈ Finset.Icc 1 q, p * j := by
      refine Finset.prod_bij' (fun x _ => x / p) (fun j _ => p * j) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        dsimp only
        rw [Finset.mem_filter, Finset.mem_Icc] at hx
        obtain ⟨⟨hx1, hx2⟩, hxd⟩ := hx
        rw [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · rw [Nat.one_le_div_iff hp0]; exact Nat.le_of_dvd (by omega) hxd
        · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hx2)
      · intro j hj
        dsimp only
        rw [Finset.mem_Icc] at hj
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact Nat.mul_pos hp0 hj.1
        · calc p * j ≤ p * q := Nat.mul_le_mul_left p hj.2
            _ = q * p := Nat.mul_comm p q
        · exact dvd_mul_right p j
      · intro x hx
        dsimp only
        rw [Finset.mem_filter] at hx
        exact Nat.mul_div_cancel' hx.2
      · intro j _
        dsimp only
        exact Nat.mul_div_cancel_left j hp0
      · intro x hx
        dsimp only
        rw [Finset.mem_filter] at hx
        exact (Nat.mul_div_cancel' hx.2).symm
    rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, prod_Icc_id, Nat.card_Icc,
      Nat.add_sub_cancel]
  have key : (q * p)! = (∏ x ∈ (Finset.Icc 1 (q * p)).filter (fun k => p ∣ k), x) * QR p (q * p) := by
    unfold QR
    rw [← prod_Icc_id (q * p)]
    exact (Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (q * p)) (fun k => p ∣ k)
      (fun x => x)).symm
  rw [key, hPdvd]

/-- BLOCK: `QR (a * p^m) = ∏_{j < a} GpN p m j`. -/
theorem QReq (m a : ℕ) (hm : 1 ≤ m) [hp : Fact p.Prime] :
    QR p (a * p ^ m) = ∏ j ∈ Finset.range a, GpN p m j := by
  have hp0 : 0 < p := hp.out.pos
  have hNpos : 0 < p ^ m := pow_pos hp0 m
  have hpN : p ∣ p ^ m := dvd_pow_self p (by omega : m ≠ 0)
  have hbij : (∏ x ∈ (Finset.range a ×ˢ Tset p m), (x.2 + x.1 * p ^ m)) = QR p (a * p ^ m) := by
    unfold QR
    refine Finset.prod_bij' (fun x _ => x.2 + x.1 * p ^ m) (fun k _ => (k / p ^ m, k % p ^ m))
      ?_ ?_ ?_ ?_ ?_
    · -- hi : image in filter
      intro x hx
      dsimp only
      obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
      simp only [Tset, Finset.mem_filter, Finset.mem_range] at hx1 hx2
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hx2ne : x.2 ≠ 0 := by
        intro h; exact hx2.2 (by rw [h]; exact dvd_zero p)
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have h1 : x.1 + 1 ≤ a := by omega
        have h2 : (x.1 + 1) * p ^ m ≤ a * p ^ m := Nat.mul_le_mul_right (p ^ m) h1
        have hexp : (x.1 + 1) * p ^ m = x.1 * p ^ m + p ^ m := by ring
        rw [hexp] at h2
        have := hx2.1
        omega
      · intro hdvd
        apply hx2.2
        have hpm : p ∣ x.1 * p ^ m := Dvd.dvd.mul_left hpN x.1
        exact (Nat.dvd_add_right hpm).mp (by rwa [add_comm] at hdvd)
    · -- hj : inverse in product
      intro k hk
      dsimp only
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk1, hk2⟩, hk3⟩ := hk
      rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hNpos]
        rcases lt_or_eq_of_le hk2 with h | h
        · exact h
        · exact absurd (by rw [h]; exact Dvd.dvd.mul_left hpN a) hk3
      · simp only [Tset, Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.mod_lt k hNpos, ?_⟩
        intro hdvd
        apply hk3
        have hkeq : k = p ^ m * (k / p ^ m) + k % p ^ m := (Nat.div_add_mod k (p ^ m)).symm
        rw [hkeq]
        exact dvd_add (Dvd.dvd.mul_right hpN _) hdvd
    · -- left_inv
      intro x hx
      dsimp only
      obtain ⟨_, hx2⟩ := Finset.mem_product.mp hx
      simp only [Tset, Finset.mem_filter, Finset.mem_range] at hx2
      have e1 : (x.2 + x.1 * p ^ m) / p ^ m = x.1 := by
        rw [Nat.add_mul_div_right _ _ hNpos, Nat.div_eq_of_lt hx2.1, zero_add]
      have e2 : (x.2 + x.1 * p ^ m) % p ^ m = x.2 := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx2.1]
      exact Prod.ext e1 e2
    · -- right_inv
      intro k _
      dsimp only
      exact Nat.mod_add_div' k (p ^ m)
    · -- value compatibility
      intro x _
      rfl
  rw [← hbij, Finset.prod_product]
  apply Finset.prod_congr rfl
  intro i _
  unfold GpN
  apply Finset.prod_congr rfl
  intro t _
  rfl

/-- Casting `Gp` to its Nat version. -/
theorem Gp_cast (m c : ℕ) : Gp p m (c : ℤ) = (GpN p m c : ℤ) := by
  unfold Gp GpN
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro t _
  push_cast
  ring

theorem GpN_pos (m c : ℕ) [hp : Fact p.Prime] : 0 < GpN p m c := by
  unfold GpN
  apply Finset.prod_pos
  intro t ht
  simp only [Tset, Finset.mem_filter, Finset.mem_range] at ht
  rcases Nat.eq_zero_or_pos t with h | h
  · exact absurd (by rw [h]; exact dvd_zero p) ht.2
  · omega

theorem BINOM3 (m : ℕ) (hm : 1 ≤ m) [hp : Fact p.Prime] :
    ((3 * p^m).choose (p^m) : ℤ) * Gp p m 0
      = ((3 * p^(m-1)).choose (p^(m-1)) : ℤ) * Gp p m 2 := by
  have hp0 : 0 < p := hp.out.pos
  have hN : p ^ m = p ^ (m - 1) * p := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  set n := p ^ (m - 1) with hndef
  have FS_N : (p ^ m)! = p ^ n * n ! * QR p (p ^ m) := by
    have h := FS p n
    rwa [← hN] at h
  have FS_2N : (2 * p ^ m)! = p ^ (2 * n) * (2 * n)! * QR p (2 * p ^ m) := by
    have h := FS p (2 * n)
    rwa [show 2 * n * p = 2 * p ^ m by rw [hN]; ring] at h
  have FS_3N : (3 * p ^ m)! = p ^ (3 * n) * (3 * n)! * QR p (3 * p ^ m) := by
    have h := FS p (3 * n)
    rwa [show 3 * n * p = 3 * p ^ m by rw [hN]; ring] at h
  have CH3N : (3 * p ^ m).choose (p ^ m) * (p ^ m)! * (2 * p ^ m)! = (3 * p ^ m)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show p ^ m ≤ 3 * p ^ m by omega)
    rwa [show 3 * p ^ m - p ^ m = 2 * p ^ m by omega] at h
  have CH3n : (3 * n).choose n * n ! * (2 * n)! = (3 * n)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
    rwa [show 3 * n - n = 2 * n by omega] at h
  have hpow3 : p ^ (3 * n) = p ^ n * p ^ (2 * n) := by rw [← pow_add]; congr 1; ring
  have hK : 0 < p ^ (3 * n) * (n ! * (2 * n)!) :=
    Nat.mul_pos (pow_pos hp0 _) (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  have qr1 : QR p (p ^ m) = GpN p m 0 := by
    have h := QReq p m 1 hm
    rw [one_mul] at h
    rw [h, Finset.prod_range_one]
  have qr2 : QR p (2 * p ^ m) = GpN p m 0 * GpN p m 1 := by
    have h := QReq p m 2 hm
    rw [h, show (2:ℕ) = 1 + 1 from rfl, Finset.prod_range_succ, Finset.prod_range_one]
  have qr3 : QR p (3 * p ^ m) = GpN p m 0 * GpN p m 1 * GpN p m 2 := by
    have h := QReq p m 3 hm
    rw [h, show (3:ℕ) = 2 + 1 from rfl, Finset.prod_range_succ, show (2:ℕ) = 1 + 1 from rfl,
      Finset.prod_range_succ, Finset.prod_range_one]
  have reduced : (3 * p ^ m).choose (p ^ m) * QR p (p ^ m) * QR p (2 * p ^ m)
               = (3 * n).choose n * QR p (3 * p ^ m) := by
    apply Nat.eq_of_mul_eq_mul_right hK
    calc (3 * p ^ m).choose (p ^ m) * QR p (p ^ m) * QR p (2 * p ^ m)
            * (p ^ (3 * n) * (n ! * (2 * n)!))
        = (3 * p ^ m).choose (p ^ m) * (p ^ n * n ! * QR p (p ^ m))
            * (p ^ (2 * n) * (2 * n)! * QR p (2 * p ^ m)) := by rw [hpow3]; ring
      _ = (3 * p ^ m).choose (p ^ m) * (p ^ m)! * (2 * p ^ m)! := by rw [← FS_N, ← FS_2N]
      _ = (3 * p ^ m)! := CH3N
      _ = p ^ (3 * n) * (3 * n)! * QR p (3 * p ^ m) := FS_3N
      _ = p ^ (3 * n) * ((3 * n).choose n * n ! * (2 * n)!) * QR p (3 * p ^ m) := by rw [← CH3n]
      _ = (3 * n).choose n * QR p (3 * p ^ m) * (p ^ (3 * n) * (n ! * (2 * n)!)) := by ring
  rw [qr1, qr2, qr3] at reduced
  have hGpos : 0 < GpN p m 0 * GpN p m 1 := Nat.mul_pos (GpN_pos p m 0) (GpN_pos p m 1)
  have natEq : (3 * p ^ m).choose (p ^ m) * GpN p m 0 = (3 * n).choose n * GpN p m 2 := by
    apply Nat.eq_of_mul_eq_mul_right hGpos
    have hR : (3 * n).choose n * GpN p m 2 * (GpN p m 0 * GpN p m 1)
            = (3 * n).choose n * (GpN p m 0 * GpN p m 1 * GpN p m 2) := by ring
    rw [hR, ← reduced]
  have g0 : Gp p m 0 = (GpN p m 0 : ℤ) := by
    rw [show (0:ℤ) = ((0:ℕ):ℤ) by norm_num]; exact Gp_cast p m 0
  have g2 : Gp p m 2 = (GpN p m 2 : ℤ) := by
    rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num]; exact Gp_cast p m 2
  rw [g0, g2]
  exact_mod_cast natEq

theorem BINOM2 (m : ℕ) (hm : 1 ≤ m) [hp : Fact p.Prime] :
    ((2 * p^m).choose (p^m) : ℤ) * Gp p m 0
      = ((2 * p^(m-1)).choose (p^(m-1)) : ℤ) * Gp p m 1 := by
  have hp0 : 0 < p := hp.out.pos
  have hN : p ^ m = p ^ (m - 1) * p := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  set n := p ^ (m - 1) with hndef
  have FS_N : (p ^ m)! = p ^ n * n ! * QR p (p ^ m) := by
    have h := FS p n
    rwa [← hN] at h
  have FS_2N : (2 * p ^ m)! = p ^ (2 * n) * (2 * n)! * QR p (2 * p ^ m) := by
    have h := FS p (2 * n)
    rwa [show 2 * n * p = 2 * p ^ m by rw [hN]; ring] at h
  have CH2N : (2 * p ^ m).choose (p ^ m) * (p ^ m)! * (p ^ m)! = (2 * p ^ m)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show p ^ m ≤ 2 * p ^ m by omega)
    rwa [show 2 * p ^ m - p ^ m = p ^ m by omega] at h
  have CH2n : (2 * n).choose n * n ! * n ! = (2 * n)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rwa [show 2 * n - n = n by omega] at h
  have hpow2 : p ^ (2 * n) = p ^ n * p ^ n := by rw [← pow_add]; congr 1; ring
  have hK : 0 < p ^ (2 * n) * (n ! * n !) :=
    Nat.mul_pos (pow_pos hp0 _) (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  have qr1 : QR p (p ^ m) = GpN p m 0 := by
    have h := QReq p m 1 hm
    rw [one_mul] at h
    rw [h, Finset.prod_range_one]
  have qr2 : QR p (2 * p ^ m) = GpN p m 0 * GpN p m 1 := by
    have h := QReq p m 2 hm
    rw [h, show (2:ℕ) = 1 + 1 from rfl, Finset.prod_range_succ, Finset.prod_range_one]
  have reduced : (2 * p ^ m).choose (p ^ m) * QR p (p ^ m) * QR p (p ^ m)
               = (2 * n).choose n * QR p (2 * p ^ m) := by
    apply Nat.eq_of_mul_eq_mul_right hK
    calc (2 * p ^ m).choose (p ^ m) * QR p (p ^ m) * QR p (p ^ m)
            * (p ^ (2 * n) * (n ! * n !))
        = (2 * p ^ m).choose (p ^ m) * (p ^ n * n ! * QR p (p ^ m))
            * (p ^ n * n ! * QR p (p ^ m)) := by rw [hpow2]; ring
      _ = (2 * p ^ m).choose (p ^ m) * (p ^ m)! * (p ^ m)! := by rw [← FS_N]
      _ = (2 * p ^ m)! := CH2N
      _ = p ^ (2 * n) * (2 * n)! * QR p (2 * p ^ m) := FS_2N
      _ = p ^ (2 * n) * ((2 * n).choose n * n ! * n !) * QR p (2 * p ^ m) := by rw [← CH2n]
      _ = (2 * n).choose n * QR p (2 * p ^ m) * (p ^ (2 * n) * (n ! * n !)) := by ring
  rw [qr1, qr2] at reduced
  have natEq : (2 * p ^ m).choose (p ^ m) * GpN p m 0 = (2 * n).choose n * GpN p m 1 := by
    apply Nat.eq_of_mul_eq_mul_right (GpN_pos p m 0)
    have hR : (2 * n).choose n * GpN p m 1 * GpN p m 0
            = (2 * n).choose n * (GpN p m 0 * GpN p m 1) := by ring
    rw [hR, ← reduced]
  have g0 : Gp p m 0 = (GpN p m 0 : ℤ) := by
    rw [show (0:ℤ) = ((0:ℕ):ℤ) by norm_num]; exact Gp_cast p m 0
  have g1 : Gp p m 1 = (GpN p m 1 : ℤ) := by
    rw [show (1:ℤ) = ((1:ℕ):ℤ) by norm_num]; exact Gp_cast p m 1
  rw [g0, g1]
  exact_mod_cast natEq

theorem kummer3 (k : ℕ) : (3 * 3^k).choose (3^k) ≡ 0 [MOD 3] := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  induction k with
  | zero => decide
  | succ j ih =>
    have hstep := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 3*3^(j+1)) (k := 3^(j+1)) (p := 3)
    have hpn : 3*3^(j+1) = 3*(3^(j+1)) := by ring
    have e1 : 3*3^(j+1) % 3 = 0 := by rw [hpn, Nat.mul_mod_right]
    have e2 : 3*3^(j+1) / 3 = 3^(j+1) := by rw [hpn, Nat.mul_div_cancel_left _ (by norm_num)]
    have e3 : 3^(j+1) % 3 = 0 := by
      have : 3^(j+1) = 3*3^j := by ring
      rw [this, Nat.mul_mod_right]
    have e4 : 3^(j+1) / 3 = 3^j := by
      have : 3^(j+1) = 3*3^j := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [e1, e2, e3, e4] at hstep
    simp only [Nat.choose_zero_right, one_mul] at hstep
    have hre : (3^(j+1)).choose (3^j) = (3*3^j).choose (3^j) := by
      congr 1; ring
    rw [hre] at hstep
    exact hstep.trans ih

theorem KUMMER (k : ℕ) [hp : Fact p.Prime] :
    (p:ℤ)^(wv p) ∣ ((3 * p^k).choose (p^k) : ℤ) := by
  unfold wv
  split
  · rename_i h; subst h
    simp only [pow_one]
    have hz : (3 * 3^k).choose (3^k) ≡ 0 [MOD 3] := kummer3 k
    have : (3:ℕ) ∣ (3 * 3^k).choose (3^k) := (Nat.modEq_zero_iff_dvd).mp hz
    exact_mod_cast this
  · simp

theorem central_mod (k : ℕ) [hp : Fact p.Prime] :
    (2*p^k).choose (p^k) ≡ 2 [MOD p] := by
  induction k with
  | zero => simp [Nat.ModEq]
  | succ n ih =>
    have hstep := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2*p^(n+1)) (k := p^(n+1)) (p := p)
    have hpn : 2*p^(n+1) = p*(2*p^n) := by ring
    have hqn : p^(n+1) = p*p^n := by ring
    have e1 : 2*p^(n+1) % p = 0 := by rw [hpn, Nat.mul_mod_right]
    have e2 : 2*p^(n+1) / p = 2*p^n := by rw [hpn, Nat.mul_div_cancel_left _ (hp.out.pos)]
    have e3 : p^(n+1) % p = 0 := by rw [hqn, Nat.mul_mod_right]
    have e4 : p^(n+1) / p = p^n := by rw [hqn, Nat.mul_div_cancel_left _ (hp.out.pos)]
    rw [e1, e2, e3, e4] at hstep
    simp only [Nat.choose_self, one_mul] at hstep
    exact hstep.trans ih

theorem CENTRAL (k : ℕ) (hp3 : 3 ≤ p) [hp : Fact p.Prime] : ¬ (p:ℤ) ∣ ((2 * p^k).choose (p^k) : ℤ) := by
  intro hd
  have hn : (p:ℕ) ∣ (2 * p^k).choose (p^k) := by exact_mod_cast hd
  have hz : (2 * p^k).choose (p^k) ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hn
  have h2 : (2 : ℕ) ≡ 0 [MOD p] := (central_mod p k).symm.trans hz
  have hp2 : p ∣ 2 := (Nat.modEq_zero_iff_dvd).mp h2
  have := Nat.le_of_dvd (by norm_num) hp2
  omega

theorem LEVEL_DIFF (m : ℕ) (hm : 1 ≤ m) (c : ℤ) (hc : c = 1 ∨ c = 2) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^(3*m - wv p) ∣ (Gp p m c - Gp p m 0) := by sorry

theorem CORE (m : ℕ) (hm : 2 ≤ m) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^(3*m+3) ∣ (Gp p m 2 * (Gp p m 0)^2 - (Gp p m 1)^3) := by sorry

/-! ## Generic divisibility helpers. -/

theorem pcancel [hp : Fact p.Prime] {b c : ℤ} {m : ℕ} (hb : ¬ (p:ℤ) ∣ b)
    (h : (p:ℤ)^m ∣ b * c) : (p:ℤ)^m ∣ c := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcop : IsCoprime ((p:ℤ)^m) b := (hpp.coprime_iff_not_dvd.mpr hb).pow_left
  exact hcop.dvd_of_dvd_mul_left h

theorem extract3 [hp : Fact p.Prime] {c : ℤ} {m : ℕ}
    (h : (p:ℤ)^m ∣ 3 * c) : (p:ℤ)^(m-1) ∣ c := by
  rcases eq_or_ne p 3 with h3 | h3
  · subst h3
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      have hpow : ((3:ℕ):ℤ)^m = 3 * ((3:ℕ):ℤ)^(m-1) := by
        rw [show m = (m-1)+1 by omega, pow_succ]; push_cast; ring
      rw [hpow] at hk
      have h3ne : (3:ℤ) ≠ 0 := by norm_num
      apply mul_left_cancel₀ h3ne; push_cast at hk ⊢; linarith [hk]
  · have hnd : ¬ (p:ℤ) ∣ 3 := by
      have hn : ¬ p ∣ 3 := by
        intro hd; rcases (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp hd; exact h3 rfl
      intro hd; exact hn (by exact_mod_cast hd)
    exact dvd_trans (pow_dvd_pow _ (Nat.sub_le m 1)) (pcancel p hnd h)

theorem pmul {a b : ℕ} {x y : ℤ} (hx : (p:ℤ)^a ∣ x) (hy : (p:ℤ)^b ∣ y) :
    (p:ℤ)^(a+b) ∣ x * y := by rw [pow_add]; exact mul_dvd_mul hx hy

theorem dvdK {a K : ℕ} {x : ℤ} (hx : (p:ℤ)^a ∣ x) (h : K ≤ a) : (p:ℤ)^K ∣ x :=
  dvd_trans (pow_dvd_pow _ h) hx

theorem hwle : wv p ≤ 1 := by unfold wv; split <;> norm_num

theorem pw_dvd_3 : (p:ℤ)^(wv p) ∣ (3:ℤ) := by
  unfold wv; split
  · rename_i h; subst h; norm_num
  · simp

theorem G0cube_unit (m : ℕ) [hp : Fact p.Prime] : ¬ (p:ℤ) ∣ (Gp p m 0)^3 := by
  intro hd
  exact G0_unit p m ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow hd)

/-! ## Assembly lemma (final integer arithmetic). -/

theorem assembly [hp : Fact p.Prime] (r : ℕ) (hr : 2 ≤ r)
    (A a0 B b0 : ℤ) (hb0 : ¬ (p:ℤ) ∣ b0)
    (H1 : (p:ℤ)^3 ∣ (a0 - 3)) (H2 : (p:ℤ)^3 ∣ 3*(b0 - 2))
    (Fα : (p:ℤ)^(3*r) ∣ (A - a0)) (Fβ : (p:ℤ)^(3*r) ∣ 3*(B - b0))
    (F3 : (p:ℤ)^(3*r+3) ∣ (A*b0^3 - a0*B^3)) :
    (p:ℤ)^(3*r+3) ∣ ((a0^2 - 27*b0) - (A^2 - 27*B)) := by
  set K := 3*r+3 with hK
  set α := A - a0 with hα
  set β := B - b0 with hβ
  have hβ1 : (p:ℤ)^(3*r-1) ∣ β := extract3 p Fβ
  have hα2 : (p:ℤ)^K ∣ α^2 := by
    rw [pow_two]; exact dvdK p (pmul p Fα Fα) (by rw [hK]; omega)
  have hβ2 : (p:ℤ)^K ∣ β^2 := by
    rw [pow_two]; exact dvdK p (pmul p hβ1 hβ1) (by rw [hK]; omega)
  have hβ3 : (p:ℤ)^K ∣ β^3 := by
    have h1 : (p:ℤ)^((3*r-1)+(3*r-1)+(3*r-1)) ∣ β^3 := by
      have e : β^3 = β*β*β := by ring
      rw [e, pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul hβ1 hβ1) hβ1
    exact dvdK p h1 (by rw [hK]; omega)
  have hb02 : ¬ (p:ℤ) ∣ b0^2 := by
    intro hd; exact hb0 ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow hd)
  have HP : (p:ℤ)^K ∣ (α*b0^3 - 3*a0*b0^2*β) := by
    have key : α*b0^3 - 3*a0*b0^2*β = (A*b0^3 - a0*B^3) + 3*a0*b0*β^2 + a0*β^3 := by
      rw [hα, hβ]; ring
    rw [key]
    exact dvd_add (dvd_add F3 (Dvd.dvd.mul_left hβ2 _)) (Dvd.dvd.mul_left hβ3 _)
  have HQ : (p:ℤ)^K ∣ (α*b0 - 3*a0*β) := by
    apply pcancel p hb02
    have : b0^2 * (α*b0 - 3*a0*β) = α*b0^3 - 3*a0*b0^2*β := by ring
    rw [this]; exact HP
  have HR : (p:ℤ)^K ∣ (α*b0 - 9*β) := by
    have t : (p:ℤ)^K ∣ (3*a0*β - 9*β) := by
      have e : 3*a0*β - 9*β = (a0 - 3)*(3*β) := by ring
      rw [e, hK, show 3*r+3 = 3+3*r by ring]; exact pmul p H1 Fβ
    have := dvd_add HQ t
    have e2 : (α*b0 - 3*a0*β) + (3*a0*β - 9*β) = α*b0 - 9*β := by ring
    rwa [e2] at this
  have T3ab : (p:ℤ)^K ∣ (3*α*b0 - 6*α) := by
    have e : 3*α*b0 - 6*α = α*(3*(b0-2)) := by ring
    rw [e, hK]; exact pmul p Fα H2
  have T2aa : (p:ℤ)^K ∣ (2*a0*α - 6*α) := by
    have e : 2*a0*α - 6*α = α*(2*(a0-3)) := by ring
    rw [e]
    have h2 : (p:ℤ)^3 ∣ 2*(a0-3) := Dvd.dvd.mul_left H1 2
    rw [hK]; exact pmul p Fα h2
  have HS : (p:ℤ)^K ∣ (6*α - 27*β) := by
    have h3 : (p:ℤ)^K ∣ (3*α*b0 - 27*β) := by
      have e : 3*α*b0 - 27*β = 3*(α*b0 - 9*β) := by ring
      rw [e]; exact Dvd.dvd.mul_left HR 3
    have := dvd_sub h3 T3ab
    have e2 : (3*α*b0 - 27*β) - (3*α*b0 - 6*α) = 6*α - 27*β := by ring
    rwa [e2] at this
  have main : (p:ℤ)^K ∣ (27*β - 2*a0*α) := by
    have := dvd_add HS T2aa
    have e : (6*α - 27*β) + (2*a0*α - 6*α) = -(27*β - 2*a0*α) := by ring
    rw [e] at this
    exact (dvd_neg).mp this
  have goaleq : ((a0^2 - 27*b0) - (A^2 - 27*B)) = (27*β - 2*a0*α) - α^2 := by
    rw [hα, hβ]; ring
  rw [goaleq]; exact dvd_sub main hα2

/-! ## Telescoping steps. -/

theorem STEP3 (k : ℕ) (hk : 1 ≤ k) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^(3*k) ∣ (((3*p^k).choose (p^k) : ℤ) - ((3*p^(k-1)).choose (p^(k-1)) : ℤ)) := by
  set C3 : ℤ := ((3*p^k).choose (p^k) : ℤ)
  set c3 : ℤ := ((3*p^(k-1)).choose (p^(k-1)) : ℤ)
  have hb := BINOM3 p k hk
  have hprod : (p:ℤ)^(wv p + (3*k - wv p)) ∣ (c3 * (Gp p k 2 - Gp p k 0)) :=
    pmul p (KUMMER p (k-1)) (LEVEL_DIFF p k hk 2 (Or.inr rfl) hp3)
  have hexp : wv p + (3*k - wv p) = 3*k := by have := hwle p; omega
  rw [hexp] at hprod
  have hcast : c3 * (Gp p k 2 - Gp p k 0) = (C3 - c3) * Gp p k 0 := by
    linear_combination -hb
  rw [hcast, mul_comm (C3 - c3) (Gp p k 0)] at hprod
  exact pcancel p (G0_unit p k) hprod

theorem STEP2 (k : ℕ) (hk : 1 ≤ k) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^(3*k - wv p) ∣ (((2*p^k).choose (p^k) : ℤ) - ((2*p^(k-1)).choose (p^(k-1)) : ℤ)) := by
  set C2 : ℤ := ((2*p^k).choose (p^k) : ℤ)
  set c2 : ℤ := ((2*p^(k-1)).choose (p^(k-1)) : ℤ)
  have hb := BINOM2 p k hk
  have hprod : (p:ℤ)^(3*k - wv p) ∣ (c2 * (Gp p k 1 - Gp p k 0)) :=
    Dvd.dvd.mul_left (LEVEL_DIFF p k hk 1 (Or.inl rfl) hp3) c2
  have hcast : c2 * (Gp p k 1 - Gp p k 0) = (C2 - c2) * Gp p k 0 := by
    linear_combination -hb
  rw [hcast, mul_comm (C2 - c2) (Gp p k 0)] at hprod
  exact pcancel p (G0_unit p k) hprod

/-! ## H1, H2 via telescoping induction. -/

theorem H1_gen (j : ℕ) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^3 ∣ (((3*p^j).choose (p^j) : ℤ) - 3) := by
  induction j with
  | zero => simp
  | succ n ih =>
    have hstep : (p:ℤ)^3 ∣ (((3*p^(n+1)).choose (p^(n+1)) : ℤ) - ((3*p^n).choose (p^n) : ℤ)) := by
      have := STEP3 p (n+1) (by omega) hp3
      simp only [Nat.add_sub_cancel] at this
      exact dvdK p this (by omega)
    have : (p:ℤ)^3 ∣ ((((3*p^(n+1)).choose (p^(n+1)) : ℤ) - ((3*p^n).choose (p^n) : ℤ))
        + (((3*p^n).choose (p^n) : ℤ) - 3)) := dvd_add hstep ih
    have e : (((3*p^(n+1)).choose (p^(n+1)) : ℤ) - ((3*p^n).choose (p^n) : ℤ))
        + (((3*p^n).choose (p^n) : ℤ) - 3) = ((3*p^(n+1)).choose (p^(n+1)) : ℤ) - 3 := by ring
    rwa [e] at this

theorem H2_gen (j : ℕ) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^3 ∣ 3 * (((2*p^j).choose (p^j) : ℤ) - 2) := by
  induction j with
  | zero => simp
  | succ n ih =>
    have hstep : (p:ℤ)^3 ∣ 3 * (((2*p^(n+1)).choose (p^(n+1)) : ℤ) - ((2*p^n).choose (p^n) : ℤ)) := by
      have hd := STEP2 p (n+1) (by omega) hp3
      simp only [Nat.add_sub_cancel] at hd
      have hprod : (p:ℤ)^(wv p + (3*(n+1) - wv p)) ∣
          3 * (((2*p^(n+1)).choose (p^(n+1)) : ℤ) - ((2*p^n).choose (p^n) : ℤ)) :=
        pmul p (pw_dvd_3 p) hd
      have hexp : wv p + (3*(n+1) - wv p) = 3*(n+1) := by have := hwle p; omega
      rw [hexp] at hprod
      exact dvdK p hprod (by omega)
    have : (p:ℤ)^3 ∣ (3 * (((2*p^(n+1)).choose (p^(n+1)) : ℤ) - ((2*p^n).choose (p^n) : ℤ))
        + 3 * (((2*p^n).choose (p^n) : ℤ) - 2)) := dvd_add hstep ih
    have e : (3 * (((2*p^(n+1)).choose (p^(n+1)) : ℤ) - ((2*p^n).choose (p^n) : ℤ))
        + 3 * (((2*p^n).choose (p^n) : ℤ) - 2))
        = 3 * (((2*p^(n+1)).choose (p^(n+1)) : ℤ) - 2) := by ring
    rwa [e] at this

/-! ## The main theorem-input package. -/

theorem main_dvd [hp : Fact p.Prime] (r : ℕ) (hr : 2 ≤ r) (hp3 : 3 ≤ p) :
    (p:ℤ)^(3*r+3) ∣
      ((((3*p^(r-1)).choose (p^(r-1)) : ℤ)^2 - 27*((2*p^(r-1)).choose (p^(r-1)) : ℤ))
        - (((3*p^r).choose (p^r) : ℤ)^2 - 27*((2*p^r).choose (p^r) : ℤ))) := by
  set A : ℤ := ((3*p^r).choose (p^r) : ℤ) with hA
  set a0 : ℤ := ((3*p^(r-1)).choose (p^(r-1)) : ℤ) with ha0
  set B : ℤ := ((2*p^r).choose (p^r) : ℤ) with hB
  set b0 : ℤ := ((2*p^(r-1)).choose (p^(r-1)) : ℤ) with hb0def
  -- hb0
  have hb0 : ¬ (p:ℤ) ∣ b0 := CENTRAL p (r-1) hp3
  -- H1
  have H1 : (p:ℤ)^3 ∣ (a0 - 3) := H1_gen p (r-1) hp3
  -- H2
  have H2 : (p:ℤ)^3 ∣ 3*(b0 - 2) := H2_gen p (r-1) hp3
  -- Fα
  have Fα : (p:ℤ)^(3*r) ∣ (A - a0) := by
    exact STEP3 p r (by omega) hp3
  -- Fβ
  have Fβ : (p:ℤ)^(3*r) ∣ 3*(B - b0) := by
    have hd := STEP2 p r (by omega) hp3
    have hprod : (p:ℤ)^(wv p + (3*r - wv p)) ∣ 3*(B - b0) := pmul p (pw_dvd_3 p) hd
    have hexp : wv p + (3*r - wv p) = 3*r := by have := hwle p; omega
    rwa [hexp] at hprod
  -- F3
  have F3 : (p:ℤ)^(3*r+3) ∣ (A*b0^3 - a0*B^3) := by
    have hcore := CORE p r hr hp3
    have h3 := BINOM3 p r (by omega)
    have h2 := BINOM2 p r (by omega)
    -- multiply core by a0*b0^3
    have hmul : (p:ℤ)^(3*r+3) ∣ (a0*b0^3*(Gp p r 2 * (Gp p r 0)^2 - (Gp p r 1)^3)) :=
      Dvd.dvd.mul_left hcore _
    have hid : a0*b0^3*(Gp p r 2 * (Gp p r 0)^2 - (Gp p r 1)^3)
        = (Gp p r 0)^3 * (A*b0^3 - a0*B^3) := by
      linear_combination (-(b0^3)*(Gp p r 0)^2) * h3
        + a0*((B*Gp p r 0)^2 + (B*Gp p r 0)*(b0*Gp p r 1) + (b0*Gp p r 1)^2) * h2
    rw [hid] at hmul
    exact pcancel p (G0cube_unit p r) hmul
  exact assembly p r hr A a0 B b0 hb0 H1 H2 Fα Fβ F3

/-! ## Connection to the Spec goal (test). -/

def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

theorem spec_test (r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Int.modEq_iff_dvd]
  have := main_dvd p r hr hp3
  simp only [a, Int.ofNat_eq_natCast]
  convert this using 2

end Work

