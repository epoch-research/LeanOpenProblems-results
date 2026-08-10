import Submission.Lib

open Finset

variable (p : ℕ)

namespace P4

open A374605 Nat

/-- T(p-1,k) cast to ZMod p^4. -/
noncomputable def cc4 (p k : ℕ) : ZMod (p^4) := ((A374605.T (p-1) k : ℤ) : ZMod (p^4))

/-- Cast of the exact ratio identity to ZMod p^4. -/
lemma ratio4 (p : ℕ) (hp5 : 5 ≤ p) (k : ℕ) (hk : k ≤ p-1) :
    (((k:ZMod (p^4))+1)^3*(2*(p:ZMod (p^4))+2*k-1)*(2*(p:ZMod (p^4))+2*k)) * cc4 p (k+1)
      = (((p:ZMod (p^4))-1-k)^2*((p:ZMod (p^4))+k)*(3*(p:ZMod (p^4))+2*k-2)*(3*(p:ZMod (p^4))+2*k-1)) * cc4 p k := by
  have hr := A374605.T_k_ratio (p-1) k hk
  have hc : ((p-1:ℕ):ℤ) = (p:ℤ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hc] at hr
  have := congrArg (fun z : ℤ => (z : ZMod (p^4))) hr
  simp only [cc4]
  push_cast at this ⊢
  linear_combination this

lemma huni4 (p m : ℕ) (hp : Nat.Prime p) (h : ¬ p ∣ m) : IsUnit ((m:ℕ):ZMod (p^4)) :=
  (ZMod.isUnit_iff_coprime m (p^4)).mpr
    (Nat.Coprime.pow_right 4 (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr h)))

/-- C(3p-1,p-1) ≡ 1 (mod p^3), via `full_block` (j=2). -/
lemma C3pm1 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ((Nat.choose (3*p-1) (p-1) : ℕ) : ZMod (p^3)) = 1 := by
  have hch : Nat.choose (3*p-1) (p-1) * (p-1)! * (2*p)! = (3*p-1)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show p-1 ≤ 3*p-1 from by omega)
    rwa [show 3*p-1-(p-1) = 2*p from by omega] at h
  have hsplit : (3*p-1)! = (2*p)! * ∏ i ∈ Finset.Icc 1 (p-1), (2*p+i) := by
    have d1 : (3*p-1)! = ∏ i ∈ Finset.Icc 1 (3*p-1), i := by
      rw [show Finset.Icc 1 (3*p-1) = Finset.Ico 1 ((3*p-1)+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.prod_Ico_id_eq_factorial]
    have d2 : (2*p)! = ∏ i ∈ Finset.Icc 1 (2*p), i := by
      rw [show Finset.Icc 1 (2*p) = Finset.Ico 1 ((2*p)+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.prod_Ico_id_eq_factorial]
    have hu : Finset.Icc 1 (3*p-1) = Finset.Icc 1 (2*p) ∪ Finset.Icc (2*p+1) (3*p-1) := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hd : Disjoint (Finset.Icc 1 (2*p)) (Finset.Icc (2*p+1) (3*p-1)) := by
      rw [Finset.disjoint_left]; intro x hx hy; simp only [Finset.mem_Icc] at hx hy; omega
    have hmap : Finset.Icc (2*p+1) (3*p-1) = Finset.map (addLeftEmbedding (2*p)) (Finset.Icc 1 (p-1)) := by
      rw [Finset.map_add_left_Icc]; congr 1 <;> omega
    rw [d1, hu, Finset.prod_union hd, hmap, Finset.prod_map, ← d2]
    apply congrArg
    apply Finset.prod_congr rfl; intro i _; simp [addLeftEmbedding_apply]
  have hcomb : Nat.choose (3*p-1) (p-1) * (p-1)! = ∏ i ∈ Finset.Icc 1 (p-1), (2*p+i) := by
    have h2pos : 0 < (2*p)! := Nat.factorial_pos _
    apply Nat.eq_of_mul_eq_mul_right h2pos
    rw [hch, hsplit]; ring
  have hfb := full_block hp hp5 2
  have hunit : IsUnit (((p-1)! : ℕ) : ZMod (p^3)) := by
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
    rw [Nat.Prime.dvd_factorial hp]; omega
  have e := congrArg (fun z:ℕ => (z:ZMod (p^3))) hcomb
  simp only [Nat.cast_mul, Nat.cast_prod] at e
  rw [hfb] at e
  -- e : (C) * ((p-1)!) = ((p-1)!)
  apply mulu_cancel hunit
  rw [one_mul]
  exact e

/-- Clean anchor: cc4(1) = p(p-1)^2 (mod p^4). -/
lemma cc4_1 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    cc4 p 1 = (p:ZMod (p^4))*((p:ZMod (p^4))-1)^2 := by
  obtain ⟨t, ht⟩ : (p^3:ℤ) ∣ (((Nat.choose (3*p-1) (p-1) : ℕ) : ℤ) - 1) := by
    have h1 := C3pm1 p hp hp5
    have : ((((Nat.choose (3*p-1) (p-1) : ℕ):ℤ) - 1 : ℤ) : ZMod (p^3)) = 0 := by
      push_cast; rw [h1]; ring
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_pow] at this
  show ((A374605.T (p-1) 1 : ℤ):ZMod (p^4)) = _
  have hT : (A374605.T (p-1) 1 : ℤ) = ((p:ℤ)-1)^2*(p:ℤ)*((Nat.choose (3*p-1) (p-1) : ℕ):ℤ) := by
    unfold A374605.T
    have c1 : (p-1).choose 1 = p-1 := Nat.choose_one_right _
    have c2 : (p-1+1).choose 1 = p := by rw [show p-1+1 = p from by omega, Nat.choose_one_right]
    have c3 : 3*(p-1)+2 = 3*p-1 := by omega
    rw [c1, c2, c3]
    push_cast [show (1:ℕ) ≤ p from by omega]
    ring
  rw [hT]
  have key : ((p:ℤ)-1)^2*(p:ℤ)*((Nat.choose (3*p-1) (p-1) : ℕ):ℤ)
      = ((p:ℤ)-1)^2*(p:ℤ) + (p:ℤ)^4*(((p:ℤ)-1)^2*t) := by
    have : ((Nat.choose (3*p-1) (p-1) : ℕ):ℤ) = 1 + (p:ℤ)^3*t := by linarith [ht]
    rw [this]; ring
  rw [key]
  push_cast
  rw [show ((p:ZMod (p^4)))^4 = 0 from by rw [← Nat.cast_pow, ZMod.natCast_self]]
  ring

/-- Clean anchor relation: (3p-2)(3p-1)·cc4(0) = 2p(2p-1) (mod p^4), via exact ratio. -/
lemma cc4_0_rel (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (3*(p:ZMod (p^4))-2)*(3*(p:ZMod (p^4))-1)*cc4 p 0
      = 2*(p:ZMod (p^4))*(2*(p:ZMod (p^4))-1) := by
  have hTII := congrArg (fun z:ℤ => (z:ZMod (p^4))) (A374605.TII_int p hp5)
  simp only at hTII
  push_cast at hTII
  rw [show ((A374605.T (p-1) 1 : ℤ):ZMod (p^4)) = cc4 p 1 from rfl,
      show ((A374605.T (p-1) 0 : ℤ):ZMod (p^4)) = cc4 p 0 from rfl,
      cc4_1 p hp hp5] at hTII
  have hu : IsUnit (((p:ZMod (p^4))-1)^2) := by
    have he : ((p-1:ℕ):ZMod (p^4)) = (p:ZMod (p^4)) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← he]
    exact (huni4 p (p-1) hp (by intro h; have := Nat.le_of_dvd (by omega) h; omega)).pow 2
  apply mulu_cancel hu
  linear_combination -hTII

-- ===== region A invariant with harmonic drift =====

/-- per-step harmonic increment (region A). -/
noncomputable def incA (p j : ℕ) : ZMod (p^4) :=
  9*(5*(j:ZMod (p^4))-3) * ((2*(j-1)*(j+1)*(2*j-1) : ℕ):ZMod (p^4))⁻¹

/-- cumulative drift Ψ_A(k). -/
noncomputable def PsiA (p k : ℕ) : ZMod (p^4) :=
  (-6) + ∑ j ∈ Finset.Icc 2 (k-1), incA p j

lemma hp40 (p : ℕ) : ((p:ZMod (p^4)))^4 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]

/-- base value: 4·cc4(2) = 3p² − 6p³. -/
lemma cc4_2 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    2*(2:ZMod (p^4))*((2:ZMod (p^4))-1)*cc4 p 2 = 3*(p:ZMod (p^4))^2 + (p:ZMod (p^4))^3*(-6) := by
  have hr := ratio4 p hp5 1 (by omega)
  rw [cc4_1 p hp hp5] at hr
  -- hr : (1+1)^3*(2P+2-1)*(2P+2)*cc4(2) = (P-1-1)^2*(P+1)*(3P-2... )*cc4(1=p(p-1)^2)
  have hu : IsUnit ((8:ZMod (p^4))*(2*(p:ZMod (p^4))+1)*(2*(p:ZMod (p^4))+2)) := by
    have e1 : (8:ZMod (p^4))*(2*(p:ZMod (p^4))+1)*(2*(p:ZMod (p^4))+2)
        = (((8*(2*p+1)*(2*p+2) : ℕ)):ZMod (p^4)) := by push_cast; ring
    rw [e1]; apply huni4 p _ hp
    intro hd
    rw [show 8*(2*p+1)*(2*p+2) = 16*((2*p+1)*(p+1)) by ring] at hd
    rcases (hp.dvd_mul.mp hd) with h | h
    · exact absurd (hp.dvd_of_dvd_pow (show p ∣ 2^4 by simpa using h)) (by intro h2; have := Nat.le_of_dvd (by norm_num) h2; omega)
    · rcases (hp.dvd_mul.mp h) with h | h
      · have h1 : p ∣ 1 := (Nat.dvd_add_right ⟨2, by ring⟩).mp h; have := Nat.le_of_dvd (by norm_num) h1; omega
      · have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h; have := Nat.le_of_dvd (by norm_num) h1; omega
  apply mulu_cancel hu
  push_cast at hr ⊢
  linear_combination (4:ZMod (p^4))*hr
    + (36*(p:ZMod (p^4))^4 - 168*(p:ZMod (p^4))^3 + 192*(p:ZMod (p^4))^2 + 312*(p:ZMod (p^4)) - 84)*hp40 p

/-- drift recursion. -/
lemma PsiA_succ (p k : ℕ) (hk : 2 ≤ k) : PsiA p (k+1) = PsiA p k + incA p k := by
  unfold PsiA
  rw [show (k+1)-1 = (k-1)+1 from by omega,
      Finset.sum_Icc_succ_top (show 2 ≤ (k-1)+1 by omega) (incA p),
      show (k-1)+1 = k from by omega]
  ring

set_option maxHeartbeats 1600000 in
lemma invA4 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (k : ℕ) (hk2 : 2 ≤ k) :
    k ≤ (p+1)/2 →
    2*(k:ZMod (p^4))*((k:ZMod (p^4))-1)*cc4 p k
      = 3*(p:ZMod (p^4))^2 + (p:ZMod (p^4))^3 * PsiA p k := by
  induction k, hk2 using Nat.le_induction with
  | base =>
    intro _
    have h2 := cc4_2 p hp hp5
    have hpsi : PsiA p 2 = (-6 : ZMod (p^4)) := by
      simp [PsiA, Finset.Icc_eq_empty (show ¬ (2:ℕ) ≤ 2-1 by omega)]
    rw [hpsi]
    push_cast at h2 ⊢
    linear_combination h2
  | succ k hk2 IH =>
    intro hub
    have hubk : k ≤ (p+1)/2 := by omega
    have IHk := IH hubk
    have hkp : k ≤ p - 1 := by omega
    have hr := ratio4 p hp5 k hkp
    have hUu : IsUnit (((k:ZMod (p^4))-1)*((k:ZMod (p^4))+1)^3*(2*(p:ZMod (p^4))+2*(k:ZMod (p^4))-1)*(2*(p:ZMod (p^4))+2*(k:ZMod (p^4)))) := by
      have e1 : ((k:ZMod (p^4))-1)*((k:ZMod (p^4))+1)^3*(2*(p:ZMod (p^4))+2*(k:ZMod (p^4))-1)*(2*(p:ZMod (p^4))+2*(k:ZMod (p^4)))
          = ((( (k-1)*(k+1)^3*(2*p+2*k-1)*(2*p+2*k) : ℕ)):ZMod (p^4)) := by
        push_cast [Nat.cast_sub (show (1:ℕ) ≤ k by omega), Nat.cast_sub (show (1:ℕ) ≤ 2*p+2*k by omega)]
        ring
      rw [e1]; apply huni4 p _ hp
      have hkup : 2*k ≤ p - 1 := by omega
      intro hd
      rw [Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp] at hd
      rcases hd with (((h|h)|h)|h)
      · have := Nat.le_of_dvd (by omega) h; omega
      · have h1 : p ∣ (k+1) := hp.dvd_of_dvd_pow h
        have := Nat.le_of_dvd (by omega) h1; omega
      · have h1 : p ∣ (2*k-1) := by
          have he : 2*p+2*k-1 = 2*p + (2*k-1) := by omega
          rw [he] at h; exact (Nat.dvd_add_right ⟨2, by ring⟩).mp h
        have := Nat.le_of_dvd (by omega) h1; omega
      · have h1 : p ∣ (2*k) := (Nat.dvd_add_right ⟨2, by ring⟩).mp h
        have := Nat.le_of_dvd (by omega) h1; omega
    have hwwu : IsUnit (((2*(k-1)*(k+1)*(2*k-1):ℕ)):ZMod (p^4)) := by
      apply huni4 p _ hp
      have hkup : 2*k ≤ p - 1 := by omega
      intro hd
      rw [Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp] at hd
      rcases hd with (((h|h)|h)|h)
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by omega) h; omega
      · have := Nat.le_of_dvd (by omega) h; omega
      · have := Nat.le_of_dvd (by omega) h; omega
    have hw3 : 2*((k:ZMod (p^4))-1)*((k:ZMod (p^4))+1)*(2*(k:ZMod (p^4))-1)
        * (((2*(k-1)*(k+1)*(2*k-1):ℕ)):ZMod (p^4))⁻¹ = 1 := by
      have hcast : ((( 2*(k-1)*(k+1)*(2*k-1) : ℕ)):ZMod (p^4))
          = 2*((k:ZMod (p^4))-1)*((k:ZMod (p^4))+1)*(2*(k:ZMod (p^4))-1) := by
        push_cast [Nat.cast_sub (show (1:ℕ) ≤ k by omega), Nat.cast_sub (show (1:ℕ) ≤ 2*k by omega)]
        ring
      rw [← hcast]; exact ZMod.mul_inv_of_unit _ hwwu
    rw [PsiA_succ p k hk2]
    simp only [incA]
    set ww := (((2*(k-1)*(k+1)*(2*k-1):ℕ)):ZMod (p^4))⁻¹ with hwwdef
    set ss := PsiA p k with hssdef
    apply mulu_cancel hUu
    push_cast at hr IHk hw3 ⊢
    have hp4 := hp40 p
    set kk := (k:ZMod (p^4)) with hkkdef
    set pp := (p:ZMod (p^4)) with hppdef
    linear_combination
      (2*kk^3 - 2*kk)*hr
      + (4*kk^6 + 8*kk^5*pp + 6*kk^5 - 7*kk^4*pp^2 + 29*kk^4*pp - 4*kk^4 - 17*kk^3*pp^3 + 18*kk^3*pp^2 + 17*kk^3*pp - 8*kk^3 + 3*kk^2*pp^4 - 38*kk^2*pp^3 + 56*kk^2*pp^2 - 19*kk^2*pp + 9*kk*pp^5 - 24*kk*pp^4 + 8*kk*pp^3 + 18*kk*pp^2 - 13*kk*pp + 2*kk + 9*pp^5 - 27*pp^4 + 29*pp^3 - 13*pp^2 + 2*pp)*IHk
      + (-45*kk^4*pp^3 - 63*kk^3*pp^3 + 9*kk^2*pp^3 + 27*kk*pp^3)*hw3
      + (-360*kk^6*ww - 180*kk^5*pp*ww - 414*kk^5*ww - 11*kk^4*pp*ss - 252*kk^4*pp*ww + 15*kk^4*ss + 558*kk^4*ww - 33*kk^4 - 17*kk^3*pp^2*ss + 10*kk^3*pp*ss + 216*kk^3*pp*ww - 51*kk^3*pp + 21*kk^3*ss + 612*kk^3*ww + 30*kk^3 + 3*kk^2*pp^3*ss - 38*kk^2*pp^2*ss + 9*kk^2*pp^2 + 56*kk^2*pp*ss + 360*kk^2*pp*ww - 114*kk^2*pp - 3*kk^2*ss - 252*kk^2*ww + 168*kk^2 + 9*kk*pp^4*ss - 24*kk*pp^3*ss + 27*kk*pp^3 + 8*kk*pp^2*ss - 72*kk*pp^2 + 26*kk*pp*ss - 36*kk*pp*ww + 24*kk*pp - 9*kk*ss - 198*kk*ww + 78*kk + 9*pp^4*ss - 27*pp^3*ss + 27*pp^3 + 29*pp^2*ss - 81*pp^2 - 9*pp*ss - 108*pp*ww + 87*pp + 54*ww - 27)*hp4

-- ===== region B invariant with harmonic drift (descending) =====

noncomputable def incB (p j : ℕ) : ZMod (p^4) :=
  -3*(5*(j:ZMod (p^4))-3) * (((j-1)*(j+1)*(2*j-1) : ℕ):ZMod (p^4))⁻¹

noncomputable def PsiB (p k : ℕ) : ZMod (p^4) :=
  (43 * (6:ZMod (p^4))⁻¹) + ∑ j ∈ Finset.Icc k (p-2), incB p j

lemma PsiB_succ (p k : ℕ) (hk : k ≤ p-2) : PsiB p k = PsiB p (k+1) + incB p k := by
  unfold PsiB
  rw [show Finset.Icc k (p-2) = insert k (Finset.Icc (k+1) (p-2)) from by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  ring

set_option maxHeartbeats 1600000 in
lemma invB4 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hbase : cc4 p (p-1) = (p:ZMod (p^4))^2 + (p:ZMod (p^4))^3 * (61 * (12:ZMod (p^4))⁻¹))
    (k : ℕ) (hklo : (p+1)/2 + 1 ≤ k) (hkhi : k ≤ p-1) :
    (k:ZMod (p^4))*((k:ZMod (p^4))-1)*cc4 p k = 2*(p:ZMod (p^4))^2 + (p:ZMod (p^4))^3 * PsiB p k := by
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left (by omega)
  have key : ∀ j k, k + j = p-1 → (p+1)/2 + 1 ≤ k →
      (k:ZMod (p^4))*((k:ZMod (p^4))-1)*cc4 p k = 2*(p:ZMod (p^4))^2 + (p:ZMod (p^4))^3 * PsiB p k := by
    intro j
    induction j with
    | zero =>
      intro k hk hlo
      have hkp : k = p-1 := by omega
      subst hkp
      have hcast : ((p-1:ℕ):ZMod (p^4)) = (p:ZMod (p^4)) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hpsi : PsiB p (p-1) = 43 * (6:ZMod (p^4))⁻¹ := by
        simp [PsiB, Finset.Icc_eq_empty (show ¬ (p-1:ℕ) ≤ p-2 by omega)]
      have h12u : IsUnit ((12:ZMod (p^4))) := by
        rw [show (12:ZMod (p^4)) = ((12:ℕ):ZMod (p^4)) by norm_num]
        exact huni4 p 12 hp (by
          intro h; rw [show (12:ℕ) = 2^2*3 by norm_num] at h
          rcases hp.dvd_mul.mp h with h'|h'
          · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h'); omega
          · have := Nat.le_of_dvd (by norm_num) h'; omega)
      have h12 : (12:ZMod (p^4)) * (12:ZMod (p^4))⁻¹ = 1 := ZMod.mul_inv_of_unit _ h12u
      have h6u : IsUnit ((6:ZMod (p^4))) := by
        rw [show (6:ZMod (p^4)) = ((6:ℕ):ZMod (p^4)) by norm_num]
        exact huni4 p 6 hp (by
          intro h; rw [show (6:ℕ) = 2*3 by norm_num] at h
          rcases hp.dvd_mul.mp h with h'|h'
          · have := Nat.le_of_dvd (by norm_num) h'; omega
          · have := Nat.le_of_dvd (by norm_num) h'; omega)
      have h6 : (6:ZMod (p^4)) * (6:ZMod (p^4))⁻¹ = 1 := ZMod.mul_inv_of_unit _ h6u
      rw [hcast, hbase, hpsi]
      apply mulu_cancel h12u
      linear_combination
        (61*(p:ZMod (p^4))^5 - 183*(p:ZMod (p^4))^4 + 122*(p:ZMod (p^4))^3)*h12
        + (-86*(p:ZMod (p^4))^3)*h6
        + (61*(p:ZMod (p^4)) - 171)*hp40 p
    | succ j IH =>
      intro k hk hlo
      have hk1 : (k+1) + j = p-1 := by omega
      have hlo1 : (p+1)/2 + 1 ≤ k+1 := by omega
      have IHk := IH (k+1) hk1 hlo1
      have hkp : k ≤ p - 1 := by omega
      have hkp2 : k ≤ p - 2 := by omega
      have hr := ratio4 p hp5 k hkp
      have hRu : IsUnit (((p:ZMod (p^4))-1-(k:ZMod (p^4)))^2*((p:ZMod (p^4))+(k:ZMod (p^4)))*(3*(p:ZMod (p^4))+2*(k:ZMod (p^4))-2)*(3*(p:ZMod (p^4))+2*(k:ZMod (p^4))-1)) := by
        have e1 : ((p:ZMod (p^4))-1-(k:ZMod (p^4)))^2*((p:ZMod (p^4))+(k:ZMod (p^4)))*(3*(p:ZMod (p^4))+2*(k:ZMod (p^4))-2)*(3*(p:ZMod (p^4))+2*(k:ZMod (p^4))-1)
            = ((( (p-1-k)^2*(p+k)*(3*p+2*k-2)*(3*p+2*k-1) : ℕ)):ZMod (p^4)) := by
          push_cast [Nat.cast_sub (show (1:ℕ) ≤ p by omega), Nat.cast_sub (show k ≤ p-1 by omega),
            Nat.cast_sub (show (2:ℕ) ≤ 3*p+2*k by omega), Nat.cast_sub (show (1:ℕ) ≤ 3*p+2*k by omega)]
          ring
        rw [e1]; apply huni4 p _ hp
        intro hd
        rw [Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp] at hd
        rcases hd with (((h|h)|h)|h)
        · have hh := hp.dvd_of_dvd_pow h
          have := Nat.le_of_dvd (by omega) hh; omega
        · have hk0 : p ∣ k := (Nat.dvd_add_right (dvd_refl p)).mp h
          have := Nat.le_of_dvd (by omega) hk0; omega
        · have he : 3*p+2*k-2 = 3*p + (2*k-2) := by omega
          rw [he] at h
          have h2 : p ∣ (2*k-2) := (Nat.dvd_add_right (dvd_mul_left p 3)).mp h
          have h3 : p ∣ (2*k-2-p) := Nat.dvd_sub h2 (dvd_refl p)
          have := Nat.le_of_dvd (by omega) h3; omega
        · have he : 3*p+2*k-1 = 3*p + (2*k-1) := by omega
          rw [he] at h
          have h2 : p ∣ (2*k-1) := (Nat.dvd_add_right (dvd_mul_left p 3)).mp h
          have h3 : p ∣ (2*k-1-p) := Nat.dvd_sub h2 (dvd_refl p)
          have := Nat.le_of_dvd (by omega) h3; omega
      have hwwu : IsUnit ((((k-1)*(k+1)*(2*k-1):ℕ)):ZMod (p^4)) := by
        apply huni4 p _ hp
        intro hd
        rw [Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp] at hd
        rcases hd with ((h|h)|h)
        · have := Nat.le_of_dvd (by omega) h; omega
        · have := Nat.le_of_dvd (by omega) h; omega
        · have he : 2*k-1 = p + (2*k-1-p) := by omega
          rw [he] at h
          have h2 : p ∣ (2*k-1-p) := (Nat.dvd_add_right (dvd_refl p)).mp h
          have := Nat.le_of_dvd (by omega) h2; omega
      have hw3 : ((k:ZMod (p^4))-1)*((k:ZMod (p^4))+1)*(2*(k:ZMod (p^4))-1)
          * ((((k-1)*(k+1)*(2*k-1):ℕ)):ZMod (p^4))⁻¹ = 1 := by
        have hcast : (((  (k-1)*(k+1)*(2*k-1) : ℕ)):ZMod (p^4))
            = ((k:ZMod (p^4))-1)*((k:ZMod (p^4))+1)*(2*(k:ZMod (p^4))-1) := by
          push_cast [Nat.cast_sub (show (1:ℕ) ≤ k by omega), Nat.cast_sub (show (1:ℕ) ≤ 2*k by omega)]
          ring
        rw [← hcast]; exact ZMod.mul_inv_of_unit _ hwwu
      have hpb : PsiB p (k+1) = PsiB p k - incB p k := by rw [PsiB_succ p k hkp2]; ring
      rw [hpb] at IHk
      simp only [incB] at IHk
      set ww := ((((k-1)*(k+1)*(2*k-1):ℕ)):ZMod (p^4))⁻¹ with hwwdef
      set ss := PsiB p k with hssdef
      apply mulu_cancel hRu
      push_cast at hr IHk hw3 ⊢
      have hp4 := hp40 p
      set kk := (k:ZMod (p^4)) with hkkdef
      set pp := (p:ZMod (p^4)) with hppdef
      linear_combination
        (-kk^2 + kk)*hr
        + (4*kk^5 + 8*kk^4*pp + 2*kk^4 + 4*kk^3*pp^2 + 6*kk^3*pp - 6*kk^3 + 4*kk^2*pp^2 - 10*kk^2*pp - 2*kk^2 - 4*kk*pp^2 - 6*kk*pp + 2*kk - 4*pp^2 + 2*pp)*IHk
        + (30*kk^3*pp^3 + 12*kk^2*pp^3 - 18*kk*pp^3)*hw3
        + (120*kk^5*ww + 60*kk^4*pp*ww + 18*kk^4*ww + 11*kk^3*pp*ss + 24*kk^3*pp*ww - 15*kk^3*ss - 204*kk^3*ww + 22*kk^3 + 17*kk^2*pp^2*ss - 21*kk^2*pp*ss - 96*kk^2*pp*ww + 34*kk^2*pp - 6*kk^2*ss - 42*kk^2 - 3*kk*pp^3*ss + 21*kk*pp^2*ss - 6*kk*pp^2 - 35*kk*pp*ss - 24*kk*pp*ww + 42*kk*pp + 9*kk*ss + 84*kk*ww - 70*kk - 9*pp^4*ss + 27*pp^3*ss - 18*pp^3 - 29*pp^2*ss + 54*pp^2 + 9*pp*ss + 36*pp*ww - 58*pp - 18*ww + 18)*hp4
  exact key (p-1-k) k (by omega) hklo

-- ===== telescoping decompositions (mod p^4) =====

lemma ccA_tele4 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (k : ℕ)
    (hk2 : 2 ≤ k) (hkM : k ≤ (p+1)/2) :
    cc4 p k = 3*(p:ZMod (p^4))^2 * (2:ZMod (p^4))⁻¹ *
        (((k-1:ℕ):ZMod (p^4))⁻¹ - ((k:ℕ):ZMod (p^4))⁻¹)
      + (p:ZMod (p^4))^3 * PsiA p k * (2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹ := by
  have hpk : ¬ p ∣ k := by intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hpk1 : ¬ p ∣ (k-1) := by intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hp2 : ¬ p ∣ 2 := by intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have huk : IsUnit ((k:ZMod (p^4))) := huni4 p k hp hpk
  have huk1 : IsUnit (((k-1:ℕ)):ZMod (p^4)) := huni4 p (k-1) hp hpk1
  have hu2 : IsUnit ((2:ZMod (p^4))) := by have := huni4 p 2 hp hp2; simpa using this
  have m_k : (k:ZMod (p^4)) * (k:ZMod (p^4))⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk
  have m_k1 : ((k-1:ℕ):ZMod (p^4)) * ((k-1:ℕ):ZMod (p^4))⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk1
  have m_2 : (2:ZMod (p^4)) * (2:ZMod (p^4))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu2
  have hk1cast : ((k-1:ℕ):ZMod (p^4)) = (k:ZMod (p^4)) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hA := invA4 p hp hp5 k hk2 hkM
  have hUu : IsUnit (2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4))) := (hu2.mul huk).mul huk1
  have m_d : (2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4))) * (2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hUu
  have hKK : (k:ZMod (p^4)) * ((k-1:ℕ):ZMod (p^4)) *
      (((k-1:ℕ):ZMod (p^4))⁻¹ - (k:ZMod (p^4))⁻¹) = 1 := by
    have expand : (k:ZMod (p^4)) * ((k-1:ℕ):ZMod (p^4)) *
        (((k-1:ℕ):ZMod (p^4))⁻¹ - (k:ZMod (p^4))⁻¹)
        = (k:ZMod (p^4)) * (((k-1:ℕ):ZMod (p^4)) * ((k-1:ℕ):ZMod (p^4))⁻¹)
          - ((k-1:ℕ):ZMod (p^4)) * ((k:ZMod (p^4)) * (k:ZMod (p^4))⁻¹) := by ring
    rw [expand, m_k, m_k1, hk1cast]; ring
  apply mulu_cancel hUu
  have hL : cc4 p k * (2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4))) = 3*(p:ZMod (p^4))^2 + (p:ZMod (p^4))^3 * PsiA p k := by
    have e : cc4 p k * (2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))
        = 2*(k:ZMod (p^4))*((k:ZMod (p^4))-1)*cc4 p k := by rw [hk1cast]; ring
    rw [e]; exact hA
  rw [hL]
  have e2 : (3*(p:ZMod (p^4))^2 * (2:ZMod (p^4))⁻¹ *
        (((k-1:ℕ):ZMod (p^4))⁻¹ - ((k:ℕ):ZMod (p^4))⁻¹)
      + (p:ZMod (p^4))^3 * PsiA p k * (2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹)
      * (2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))
      = 3*(p:ZMod (p^4))^2 * ((2:ZMod (p^4))*(2:ZMod (p^4))⁻¹)
          * ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4))*(((k-1:ℕ):ZMod (p^4))⁻¹ - (k:ZMod (p^4))⁻¹))
        + (p:ZMod (p^4))^3 * PsiA p k * ((2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹ * (2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))) := by ring
  rw [e2, m_2, hKK, mul_comm ((2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹) _, m_d]; ring

lemma ccB_tele4 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hbase : cc4 p (p-1) = (p:ZMod (p^4))^2 + (p:ZMod (p^4))^3 * (61 * (12:ZMod (p^4))⁻¹)) (k : ℕ)
    (hklo : (p+1)/2+1 ≤ k) (hkhi : k ≤ p-1) :
    cc4 p k = 2*(p:ZMod (p^4))^2 * (((k-1:ℕ):ZMod (p^4))⁻¹ - ((k:ℕ):ZMod (p^4))⁻¹)
      + (p:ZMod (p^4))^3 * PsiB p k * ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹ := by
  have hpk : ¬ p ∣ k := by intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hpk1 : ¬ p ∣ (k-1) := by intro h; have := Nat.le_of_dvd (by omega) h; omega
  have huk : IsUnit ((k:ZMod (p^4))) := huni4 p k hp hpk
  have huk1 : IsUnit (((k-1:ℕ)):ZMod (p^4)) := huni4 p (k-1) hp hpk1
  have m_k : (k:ZMod (p^4)) * (k:ZMod (p^4))⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk
  have m_k1 : ((k-1:ℕ):ZMod (p^4)) * ((k-1:ℕ):ZMod (p^4))⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk1
  have hk1cast : ((k-1:ℕ):ZMod (p^4)) = (k:ZMod (p^4)) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hB := invB4 p hp hp5 hbase k hklo hkhi
  have hUu : IsUnit ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4))) := huk.mul huk1
  have m_d : ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4))) * ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hUu
  have hKK : (k:ZMod (p^4)) * ((k-1:ℕ):ZMod (p^4)) *
      (((k-1:ℕ):ZMod (p^4))⁻¹ - (k:ZMod (p^4))⁻¹) = 1 := by
    have expand : (k:ZMod (p^4)) * ((k-1:ℕ):ZMod (p^4)) *
        (((k-1:ℕ):ZMod (p^4))⁻¹ - (k:ZMod (p^4))⁻¹)
        = (k:ZMod (p^4)) * (((k-1:ℕ):ZMod (p^4)) * ((k-1:ℕ):ZMod (p^4))⁻¹)
          - ((k-1:ℕ):ZMod (p^4)) * ((k:ZMod (p^4)) * (k:ZMod (p^4))⁻¹) := by ring
    rw [expand, m_k, m_k1, hk1cast]; ring
  apply mulu_cancel hUu
  have hL : cc4 p k * ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4))) = 2*(p:ZMod (p^4))^2 + (p:ZMod (p^4))^3 * PsiB p k := by
    have e : cc4 p k * ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))
        = (k:ZMod (p^4))*((k:ZMod (p^4))-1)*cc4 p k := by rw [hk1cast]; ring
    rw [e]; exact hB
  rw [hL]
  have e2 : (2*(p:ZMod (p^4))^2 * (((k-1:ℕ):ZMod (p^4))⁻¹ - ((k:ℕ):ZMod (p^4))⁻¹)
      + (p:ZMod (p^4))^3 * PsiB p k * ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹)
      * ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))
      = 2*(p:ZMod (p^4))^2 * ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4))*(((k-1:ℕ):ZMod (p^4))⁻¹ - (k:ZMod (p^4))⁻¹))
        + (p:ZMod (p^4))^3 * PsiB p k * (((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹ * ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))) := by ring
  rw [e2, hKK, mul_comm (((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹) _, m_d]; ring

-- ===== telescoping sums (mod p^4) =====

lemma sumA4 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (m : ℕ) (hm2 : 2 ≤ m) :
    m ≤ (p+1)/2 →
    ∑ k ∈ Finset.Icc 2 m, cc4 p k
      = 3*(p:ZMod (p^4))^2*(2:ZMod (p^4))⁻¹*(1 - ((m:ℕ):ZMod (p^4))⁻¹)
        + (p:ZMod (p^4))^3 * ∑ k ∈ Finset.Icc 2 m, PsiA p k * (2*(k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹ := by
  induction m, hm2 using Nat.le_induction with
  | base =>
    intro hmM
    rw [show Finset.Icc 2 2 = {2} from by ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega,
      Finset.sum_singleton, Finset.sum_singleton, ccA_tele4 p hp hp5 2 (le_refl 2) hmM,
      show ((2-1:ℕ):ZMod (p^4))⁻¹ = 1 from by norm_num]
    ring
  | succ m hm IH =>
    intro hmM
    have IHm := IH (by omega)
    rw [show Finset.Icc 2 (m+1) = insert (m+1) (Finset.Icc 2 m) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), IHm,
      ccA_tele4 p hp hp5 (m+1) (by omega) hmM, show (m+1-1) = m from by omega]
    ring

lemma sumB4 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hbase : cc4 p (p-1) = (p:ZMod (p^4))^2 + (p:ZMod (p^4))^3 * (61 * (12:ZMod (p^4))⁻¹))
    (m : ℕ) (hmlo : (p+1)/2+1 ≤ m) :
    m ≤ p-1 →
    ∑ k ∈ Finset.Icc ((p+1)/2+1) m, cc4 p k
      = 2*(p:ZMod (p^4))^2*((((p+1)/2:ℕ):ZMod (p^4))⁻¹ - ((m:ℕ):ZMod (p^4))⁻¹)
        + (p:ZMod (p^4))^3 * ∑ k ∈ Finset.Icc ((p+1)/2+1) m, PsiB p k * ((k:ZMod (p^4))*((k-1:ℕ):ZMod (p^4)))⁻¹ := by
  induction m, hmlo using Nat.le_induction with
  | base =>
    intro hmhi
    rw [show Finset.Icc ((p+1)/2+1) ((p+1)/2+1) = {(p+1)/2+1} from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega,
      Finset.sum_singleton, Finset.sum_singleton, ccB_tele4 p hp hp5 hbase ((p+1)/2+1) (le_refl _) hmhi,
      show ((p+1)/2+1-1) = (p+1)/2 from by omega]
    ring
  | succ m hm IH =>
    intro hmhi
    have IHm := IH (by omega)
    rw [show Finset.Icc ((p+1)/2+1) (m+1) = insert (m+1) (Finset.Icc ((p+1)/2+1) m) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), IHm,
      ccB_tele4 p hp hp5 hbase (m+1) (by omega) hmhi, show (m+1-1) = m from by omega]
    ring

/-- Range decomposition for the full sum (mirrors Lib's `sum_zero` hdecomp). -/
lemma cc4_decomp (p : ℕ) (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.range p, cc4 p k
      = cc4 p 0 + cc4 p 1 + (∑ k ∈ Finset.Icc 2 ((p+1)/2), cc4 p k)
        + (∑ k ∈ Finset.Icc ((p+1)/2+1) (p-1), cc4 p k) := by
  have e1 : Finset.range p = (Finset.Icc 0 1 ∪ Finset.Icc 2 ((p+1)/2)) ∪ Finset.Icc ((p+1)/2+1) (p-1) := by
    ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
  have hdAB : Disjoint (Finset.Icc 0 1) (Finset.Icc 2 ((p+1)/2)) := by
    rw [Finset.disjoint_left]; intro x hx hy; simp only [Finset.mem_Icc] at hx hy; omega
  have hdC : Disjoint (Finset.Icc 0 1 ∪ Finset.Icc 2 ((p+1)/2)) (Finset.Icc ((p+1)/2+1) (p-1)) := by
    rw [Finset.disjoint_left]; intro x hx hy; simp only [Finset.mem_union, Finset.mem_Icc] at hx hy; omega
  rw [e1, Finset.sum_union hdC, Finset.sum_union hdAB,
    show Finset.Icc 0 1 = ({0, 1} : Finset ℕ) from by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega,
    Finset.sum_pair (by norm_num)]

end P4

/-- Cubic-order truncated product expansion mod p^4 (b^4 = 0). -/
theorem prod_one_add_truncate4 (b : ZMod (p^4)) (hb4 : b^4 = 0)
    (u : ℕ → ZMod (p^4)) (inv2 inv6 : ZMod (p^4))
    (hinv2 : (2:ZMod (p^4)) * inv2 = 1) (hinv6 : (6:ZMod (p^4)) * inv6 = 1)
    (s : Finset ℕ) (hu : ∀ i ∈ s, b ∣ u i) :
    ∏ i ∈ s, (1 + u i)
      = 1 + (∑ i ∈ s, u i)
        + ((∑ i ∈ s, u i)^2 - ∑ i ∈ s, (u i)^2) * inv2
        + ((∑ i ∈ s, u i)^3 - 3*(∑ i ∈ s, u i)*(∑ i ∈ s, (u i)^2)
            + 2*∑ i ∈ s, (u i)^3) * inv6 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert x t hx ih =>
    have hut : ∀ i ∈ t, b ∣ u i := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hbx : b ∣ u x := hu x (Finset.mem_insert_self x t)
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.sum_insert hx,
        Finset.sum_insert hx, ih hut]
    set E1 := ∑ i ∈ t, u i with hE1
    set P2 := ∑ i ∈ t, (u i)^2 with hP2
    set P3 := ∑ i ∈ t, (u i)^3 with hP3
    -- divisibilities
    have hbE1 : b ∣ E1 := Finset.dvd_sum hut
    have hbP2 : b^2 ∣ P2 := by
      apply Finset.dvd_sum; intro i hi; obtain ⟨v, hv⟩ := hut i hi; exact ⟨v^2, by rw [hv]; ring⟩
    have hbP3 : b^3 ∣ P3 := by
      apply Finset.dvd_sum; intro i hi; obtain ⟨v, hv⟩ := hut i hi; exact ⟨v^3, by rw [hv]; ring⟩
    have hbE1sq : b^2 ∣ E1^2 := by obtain ⟨w, hw⟩ := hbE1; exact ⟨w^2, by rw [hw]; ring⟩
    have hbE1cube : b^3 ∣ E1^3 := by obtain ⟨w, hw⟩ := hbE1; exact ⟨w^3, by rw [hw]; ring⟩
    have hbE2 : b^2 ∣ (E1^2 - P2) := dvd_sub hbE1sq hbP2
    have hbE3 : b^3 ∣ (E1^3 - 3*E1*P2 + 2*P3) := by
      apply dvd_add
      · apply dvd_sub hbE1cube
        obtain ⟨e, he⟩ := hbE1; obtain ⟨w, hw⟩ := hbP2; exact ⟨3*e*w, by rw [he, hw]; ring⟩
      · obtain ⟨w, hw⟩ := hbP3; exact ⟨2*w, by rw [hw]; ring⟩
    -- kill terms: u_x * (b^3 stuff) = 0  and  u_x * (b^2 stuff via inv2 then *u_x again? ) 
    -- We need: u x * ((E1^2-P2)*inv2) contributes to e3 (it's b^3),  u x * ((E1^3-...)*inv6) = 0 (b^4).
    obtain ⟨vx, hvx⟩ := hbx
    obtain ⟨w3, hw3⟩ := hbE3
    have hkill3 : u x * ((E1^3 - 3*E1*P2 + 2*P3) * inv6) = 0 := by
      rw [hvx, hw3, show b * vx * (b^3 * w3 * inv6) = b^4 * (vx*w3*inv6) by ring, hb4, zero_mul]
    -- relation inv2 = 3 * inv6
    have hrel : inv2 = 3 * inv6 := by
      calc inv2 = inv2 * (6 * inv6) := by rw [hinv6, mul_one]
        _ = 3 * (2 * inv2) * inv6 := by ring
        _ = 3 * 1 * inv6 := by rw [hinv2]
        _ = 3 * inv6 := by ring
    linear_combination
      (-(u x * E1)) * hinv2
      + (u x * (E1^2 - P2)) * hrel
      + hkill3
