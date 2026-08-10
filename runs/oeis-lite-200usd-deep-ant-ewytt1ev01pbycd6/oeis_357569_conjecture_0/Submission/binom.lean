import FormalConjectures.Util.ProblemImports
open Nat
open scoped BigOperators

variable (p : ℕ)

def Tset (m : ℕ) : Finset ℕ := (Finset.range (p^m)).filter (fun t => ¬ p ∣ t)
def Gp (m : ℕ) (c : ℤ) : ℤ := ∏ t ∈ Tset p m, ((t : ℤ) + c * (p^m : ℤ))

/-- Nat version of `Gp`. -/
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

#print axioms BINOM3
#print axioms BINOM2
