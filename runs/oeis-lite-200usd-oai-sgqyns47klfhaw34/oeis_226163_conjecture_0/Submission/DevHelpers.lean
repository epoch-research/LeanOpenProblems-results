import FormalConjectures.Util.ProblemImports

open Finset MulChar Matrix Nat Int
open scoped BigOperators

abbrev QR2 (F : Type*) [Field F] [Fintype F] [DecidableEq F] :=
  {x : F // quadraticChar F x = 1}

-- from SquareInject
lemma zmod_square_half_injective {p m : ℕ} [Fact p.Prime]
    (hp : p = 2 * m + 1) :
    Function.Injective (fun i : Fin m => (((i.val + 1 : ℕ) : ZMod p) ^ 2)) := by
  intro i j hij
  have hs := (sq_eq_sq_iff_eq_or_eq_neg.mp hij)
  have hi_lt_p : i.val + 1 < p := by
    rw [hp]
    have := i.isLt
    omega
  have hj_lt_p : j.val + 1 < p := by
    rw [hp]
    have := j.isLt
    omega
  rcases hs with h | h
  · have hmod : (i.val + 1) ≡ (j.val + 1) [MOD p] := by
      exact (ZMod.natCast_eq_natCast_iff (i.val+1) (j.val+1) p).mp h
    have heqnat := hmod.eq_of_lt_of_lt hi_lt_p hj_lt_p
    apply Fin.ext
    omega
  · have hzero : (((i.val + 1) + (j.val + 1) : ℕ) : ZMod p) = 0 := by
      have h' : ((i.val + 1 : ℕ) : ZMod p) + ((j.val + 1 : ℕ) : ZMod p) = 0 := by
        rw [h]
        ring
      simpa using h'
    have hdvd : p ∣ (i.val + 1) + (j.val + 1) := (ZMod.natCast_eq_zero_iff _ p).mp hzero
    have hpos : 0 < (i.val + 1) + (j.val + 1) := by omega
    have hlt : (i.val + 1) + (j.val + 1) < p := by
      rw [hp]
      have hi := i.isLt
      have hj := j.isLt
      omega
    have hp_le := Nat.le_of_dvd hpos hdvd
    omega

lemma zmod_half_square_quadraticChar_one {p m : ℕ} [Fact p.Prime]
    (hp : p = 2 * m + 1) (i : Fin m) :
    quadraticChar (ZMod p) (((i.val + 1 : ℕ) : ZMod p) ^ 2) = 1 := by
  have hi_lt_p : i.val + 1 < p := by
    rw [hp]
    have := i.isLt
    omega
  have hne : ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ i.val + 1 := (ZMod.natCast_eq_zero_iff _ p).mp hzero
    have hpos : 0 < i.val + 1 := by omega
    have hle := Nat.le_of_dvd hpos hdvd
    omega
  exact quadraticChar_sq_one' (F:=ZMod p) hne

-- QR card from QRCard2
abbrev NQR2 (F : Type*) [Field F] [Fintype F] [DecidableEq F] :=
  {x : F // quadraticChar F x = -1}

lemma qr_nqr_card_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) : Fintype.card (QR2 F) = Fintype.card (NQR2 F) := by
  classical
  rcases quadraticChar_exists_neg_one' (F:=F) hF with ⟨a, ha⟩
  let f : QR2 F → NQR2 F := fun x => ⟨(a : F) * (x : F), by rw [map_mul, ha, x.property]; norm_num⟩
  let g : NQR2 F → QR2 F := fun y => ⟨(↑a)⁻¹ * (y : F), by
    have haunit : (a : F) ≠ 0 := a.ne_zero
    have hInv : quadraticChar F ((a : F)⁻¹) = -1 := by
      have hprod : quadraticChar F ((a : F)⁻¹) * quadraticChar F (a : F) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ haunit, map_one]
      rw [ha] at hprod; omega
    rw [map_mul, hInv, y.property]; norm_num⟩
  refine Fintype.card_congr ⟨f, g, ?_, ?_⟩ <;> intro x <;> apply Subtype.ext <;> dsimp [f,g] <;> field_simp [a.ne_zero]

lemma qr_nqr_card_total {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) :
    Fintype.card F = Fintype.card (QR2 F) + Fintype.card (NQR2 F) + 1 := by
  classical
  let s1 : Finset F := univ.filter (fun x => quadraticChar F x = 1)
  let sm1 : Finset F := univ.filter (fun x => quadraticChar F x = -1)
  have hunion : univ.erase (0 : F) = s1 ∪ sm1 := by
    ext x; simp [s1, sm1]
    constructor
    · intro hx0; exact quadraticChar_dichotomy (F:=F) hx0
    · intro h; rcases h with h | h <;> exact fun hx => by simp [hx] at h
  have hdis : Disjoint s1 sm1 := by
    rw [Finset.disjoint_left]
    intro x hx1 hxm1; simp [s1] at hx1; simp [sm1] at hxm1; omega
  have hcard1 : s1.card = Fintype.card (QR2 F) := by
    symm
    simpa [Set.mem_setOf_eq] using
      (Fintype.card_ofFinset (p := {x : F | quadraticChar F x = 1}) s1 (by intro x; simp [s1]))
  have hcardm1 : sm1.card = Fintype.card (NQR2 F) := by
    symm
    simpa [Set.mem_setOf_eq] using
      (Fintype.card_ofFinset (p := {x : F | quadraticChar F x = -1}) sm1 (by intro x; simp [sm1]))
  have hcarderase : (univ.erase (0 : F)).card + 1 = Fintype.card F := by
    rw [Finset.card_erase_add_one (by simp : (0 : F) ∈ (univ : Finset F))]
    simp
  calc
    Fintype.card F = (univ.erase (0 : F)).card + 1 := hcarderase.symm
    _ = (s1 ∪ sm1).card + 1 := by rw [hunion]
    _ = (s1.card + sm1.card) + 1 := by rw [card_union_of_disjoint hdis]
    _ = Fintype.card (QR2 F) + Fintype.card (NQR2 F) + 1 := by rw [hcard1, hcardm1]

lemma zmod_qr_card {p m : ℕ} [Fact p.Prime] (hp : p = 2*m + 1)
    (hp2 : ringChar (ZMod p) ≠ 2) : Fintype.card (QR2 (ZMod p)) = m := by
  have htot := qr_nqr_card_total (F:=ZMod p) hp2
  have heq := qr_nqr_card_eq (F:=ZMod p) hp2
  have htot' : 2 * m + 1 = Fintype.card (QR2 (ZMod p)) + Fintype.card (NQR2 (ZMod p)) + 1 := by
    rw [← hp]
    simpa [ZMod.card] using htot
  rw [← heq] at htot'
  omega

noncomputable def rowQRMap {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) (i : Fin m) : QR2 (ZMod p) :=
  ⟨(((i.val + 1 : ℕ) : ZMod p)^2), zmod_half_square_quadraticChar_one hp i⟩

lemma rowQRMap_injective {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) :
    Function.Injective (rowQRMap hp) := by
  intro i j h
  apply zmod_square_half_injective hp
  exact congr_arg Subtype.val h

noncomputable def rowQREquiv {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (hp2 : ringChar (ZMod p) ≠ 2) : Fin m ≃ QR2 (ZMod p) :=
  Equiv.ofBijective (rowQRMap hp) ((Fintype.bijective_iff_injective_and_card (rowQRMap hp)).2
    ⟨rowQRMap_injective hp, by simp [zmod_qr_card hp hp2]⟩)

lemma factorial_cast_zmod_ne_zero {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) :
    ((m.factorial : ℕ) : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ m.factorial := (ZMod.natCast_eq_zero_iff _ p).mp h
  have hpprime : p.Prime := Fact.out
  have hle : p ≤ m := (hpprime.dvd_factorial).mp hdvd
  rw [hp] at hle
  omega



noncomputable def signedQR {p m : ℕ} [Fact p.Prime] (C : ZMod p) (j : Fin m)
    (h : quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1 ∨
         quadraticChar (ZMod p) (-(C * ((j.val + 1 : ℕ) : ZMod p))) = 1) :
    {x : ZMod p // quadraticChar (ZMod p) x = 1} :=
  if hc : quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1 then
    ⟨C * ((j.val + 1 : ℕ) : ZMod p), hc⟩
  else
    ⟨-(C * ((j.val + 1 : ℕ) : ZMod p)), h.resolve_left hc⟩

lemma one_to_m_cast_ne_zero {p m : ℕ} [Fact p.Prime] (hp : p = 2*m + 1) (j : Fin m) :
    ((j.val + 1 : ℕ) : ZMod p) ≠ 0 := by
  intro hz
  have hdvd : p ∣ j.val + 1 := (ZMod.natCast_eq_zero_iff _ p).mp hz
  have hpos : 0 < j.val + 1 := by omega
  have hlt : j.val + 1 < p := by
    rw [hp]
    have := j.isLt
    omega
  have hle := Nat.le_of_dvd hpos hdvd
  omega

lemma signed_QR_exists {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (hneg1 : quadraticChar (ZMod p) (-1) = -1) (C : ZMod p) (hC : C ≠ 0) (j : Fin m) :
    quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1 ∨
      quadraticChar (ZMod p) (-(C * ((j.val + 1 : ℕ) : ZMod p))) = 1 := by
  have hj : ((j.val + 1 : ℕ) : ZMod p) ≠ 0 := one_to_m_cast_ne_zero hp j
  have hy : C * ((j.val + 1 : ℕ) : ZMod p) ≠ 0 := mul_ne_zero hC hj
  rcases quadraticChar_dichotomy (F:=ZMod p) hy with h | h
  · exact Or.inl h
  · right
    rw [show -(C * ((j.val + 1 : ℕ) : ZMod p)) = (-1 : ZMod p) * (C * ((j.val + 1 : ℕ) : ZMod p)) by ring]
    rw [map_mul, hneg1, h]
    norm_num

noncomputable def signedQR' {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (hneg1 : quadraticChar (ZMod p) (-1) = -1) (C : ZMod p) (hC : C ≠ 0) (j : Fin m) :
    {x : ZMod p // quadraticChar (ZMod p) x = 1} :=
  signedQR C j (signed_QR_exists hp hneg1 C hC j)

lemma signedQR'_spec {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (hneg1 : quadraticChar (ZMod p) (-1) = -1) (C : ZMod p) (hC : C ≠ 0) (j : Fin m) :
    ((signedQR' hp hneg1 C hC j : ZMod p) = C * ((j.val + 1 : ℕ) : ZMod p) ∧
      quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1) ∨
    ((signedQR' hp hneg1 C hC j : ZMod p) = -(C * ((j.val + 1 : ℕ) : ZMod p)) ∧
      quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = -1) := by
  unfold signedQR'
  unfold signedQR
  by_cases hc : quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1
  · left
    constructor
    · have hcq : quadraticCharFun (ZMod p) (C * (↑↑j + 1)) = 1 := by simpa using hc
      simp [hcq]
    · exact hc
  · right
    constructor
    · have hcq : ¬ quadraticCharFun (ZMod p) (C * (↑↑j + 1)) = 1 := by simpa using hc
      simp [hcq]
    · have hy : C * ((j.val + 1 : ℕ) : ZMod p) ≠ 0 := by
        exact mul_ne_zero hC (one_to_m_cast_ne_zero hp j)
      exact (quadraticChar_eq_neg_one_iff_not_one hy).2 hc


lemma zmod_half_natCast_eq_of_eq {p m : ℕ} [Fact p.Prime] (hp : p = 2*m + 1)
    {i j : Fin m} (h : ((i.val + 1 : ℕ) : ZMod p) = ((j.val + 1 : ℕ) : ZMod p)) : i = j := by
  have hi_lt_p : i.val + 1 < p := by rw [hp]; have := i.isLt; omega
  have hj_lt_p : j.val + 1 < p := by rw [hp]; have := j.isLt; omega
  have hmod : (i.val + 1) ≡ (j.val + 1) [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp h
  have hn := hmod.eq_of_lt_of_lt hi_lt_p hj_lt_p
  apply Fin.ext
  omega

lemma zmod_half_natCast_ne_neg {p m : ℕ} [Fact p.Prime] (hp : p = 2*m + 1)
    (i j : Fin m) :
    ¬ ((i.val + 1 : ℕ) : ZMod p) = - ((j.val + 1 : ℕ) : ZMod p) := by
  intro h
  have hzero : (((i.val + 1) + (j.val + 1) : ℕ) : ZMod p) = 0 := by
    have h' : ((i.val + 1 : ℕ) : ZMod p) + ((j.val + 1 : ℕ) : ZMod p) = 0 := by
      rw [h]
      ring
    simpa using h'
  have hdvd : p ∣ (i.val + 1) + (j.val + 1) := (ZMod.natCast_eq_zero_iff _ p).mp hzero
  have hpos : 0 < (i.val + 1) + (j.val + 1) := by omega
  have hlt : (i.val + 1) + (j.val + 1) < p := by
    rw [hp]
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hle := Nat.le_of_dvd hpos hdvd
  omega

lemma signedQR'_injective {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (hneg1 : quadraticChar (ZMod p) (-1) = -1) (C : ZMod p) (hC : C ≠ 0) :
    Function.Injective (signedQR' hp hneg1 C hC) := by
  intro i j hij
  have hs_i := signedQR'_spec hp hneg1 C hC i
  have hs_j := signedQR'_spec hp hneg1 C hC j
  have hval : (signedQR' hp hneg1 C hC i : ZMod p) = (signedQR' hp hneg1 C hC j : ZMod p) := congr_arg Subtype.val hij
  rcases hs_i with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rcases hs_j with ⟨hj, _⟩ | ⟨hj, _⟩
  · apply zmod_half_natCast_eq_of_eq hp
    apply mul_left_cancel₀ hC
    simpa [hi, hj] using hval
  · exfalso
    have hcontra : ((i.val + 1 : ℕ) : ZMod p) = - ((j.val + 1 : ℕ) : ZMod p) := by
      have hmul : C * ((i.val + 1 : ℕ) : ZMod p) = C * (-((j.val + 1 : ℕ) : ZMod p)) := by
        have : C * ((i.val + 1 : ℕ) : ZMod p) = -(C * ((j.val + 1 : ℕ) : ZMod p)) := by
          simpa [hi, hj] using hval
        rw [mul_neg]
        exact this
      exact mul_left_cancel₀ hC hmul
    exact zmod_half_natCast_ne_neg hp i j hcontra
  · exfalso
    have hcontra : ((j.val + 1 : ℕ) : ZMod p) = - ((i.val + 1 : ℕ) : ZMod p) := by
      have hmul : C * ((j.val + 1 : ℕ) : ZMod p) = C * (-((i.val + 1 : ℕ) : ZMod p)) := by
        have : -(C * ((i.val + 1 : ℕ) : ZMod p)) = C * ((j.val + 1 : ℕ) : ZMod p) := by
          simpa [hi, hj] using hval
        rw [mul_neg]
        exact this.symm
      exact mul_left_cancel₀ hC hmul
    exact zmod_half_natCast_ne_neg hp j i hcontra
  · apply zmod_half_natCast_eq_of_eq hp
    apply mul_left_cancel₀ hC
    have : -(C * ((i.val + 1 : ℕ) : ZMod p)) = -(C * ((j.val + 1 : ℕ) : ZMod p)) := by
      simpa [hi, hj] using hval
    simpa using neg_injective this




noncomputable def signedQREquiv {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (hp2 : ringChar (ZMod p) ≠ 2)
    (hneg1 : quadraticChar (ZMod p) (-1) = -1) (C : ZMod p) (hC : C ≠ 0) :
    Fin m ≃ QR2 (ZMod p) :=
  Equiv.ofBijective (signedQR' hp hneg1 C hC)
    ((Fintype.bijective_iff_injective_and_card (signedQR' hp hneg1 C hC)).2
      ⟨signedQR'_injective hp hneg1 C hC, by simpa [QR2] using (zmod_qr_card hp hp2).symm⟩)


lemma prod_pm_one_eq_neg_one_pow_count_neg {α : Type*} [Fintype α]
    (f : α → ℤ) (hf : ∀ a, f a = 1 ∨ f a = -1) :
    (∏ a : α, f a) = (-1 : ℤ) ^ (Fintype.card {a : α // f a = -1}) := by
  classical
  let s : Finset α := Finset.univ.filter (fun a => f a = -1)
  have hs_card : Fintype.card {a : α // f a = -1} = s.card := by
    exact Fintype.card_ofFinset (p := {a : α | f a = -1}) s (by intro a; simp [s])
  rw [hs_card]
  have hsplit := (Finset.prod_filter_mul_prod_filter_not (s:=Finset.univ) (p:=fun a : α => f a = -1) (f:=f))
  change (Finset.univ.filter (fun a : α => f a = -1)).prod f *
      (Finset.univ.filter (fun a : α => ¬ f a = -1)).prod f = Finset.univ.prod f at hsplit
  rw [← hsplit]
  have hleft : (Finset.univ.filter (fun a : α => f a = -1)).prod f = (-1 : ℤ) ^ s.card := by
    change s.prod f = _
    calc
      s.prod f = s.prod (fun _ => (-1 : ℤ)) := by
        apply Finset.prod_congr rfl
        intro a ha
        simpa [s] using ha
      _ = (-1 : ℤ) ^ s.card := by simp
  have hright : (Finset.univ.filter (fun a : α => ¬ f a = -1)).prod f = 1 := by
    apply Finset.prod_eq_one
    intro a ha
    simp at ha
    rcases hf a with h | h
    · exact h
    · exact False.elim (ha h)
  rw [hleft, hright, mul_one]

lemma odd_count_eq_prod_of_pm_one {α : Type*} [Fintype α]
    (f : α → ℤ) (hf : ∀ a, f a = 1 ∨ f a = -1)
    (hodd : Odd (Fintype.card α)) :
    Odd (Fintype.card {a : α // f a = ∏ a, f a}) := by
  classical
  let negs : Finset α := Finset.univ.filter (fun a => f a = -1)
  let eqprod : Finset α := Finset.univ.filter (fun a => f a = ∏ a, f a)
  have hnegs_card : Fintype.card {a : α // f a = -1} = negs.card := by
    exact Fintype.card_ofFinset (p := {a : α | f a = -1}) negs (by intro a; simp [negs])
  have heqprod_card : Fintype.card {a : α // f a = ∏ a, f a} = eqprod.card := by
    exact Fintype.card_ofFinset (p := {a : α | f a = ∏ a, f a}) eqprod (by intro a; simp [eqprod])
  rw [heqprod_card]
  have hprod_pm := prod_pm_one_eq_neg_one_pow_count_neg f hf
  rw [hnegs_card] at hprod_pm
  by_cases hprod : (∏ a, f a) = (1 : ℤ)
  · have hneg_even : Even negs.card := by
      have hpow : (-1 : ℤ) ^ negs.card = 1 := hprod_pm.symm.trans hprod
      exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℤ) ≠ 1)).mp hpow
    have hnot_neg_eq_pos (a : α) : (¬ f a = -1) ↔ f a = 1 := by
      constructor
      · intro hn
        rcases hf a with h | h
        · exact h
        · exact False.elim (hn h)
      · intro h hp
        rw [h] at hp
        norm_num at hp
    have heqset : eqprod = Finset.univ.filter (fun a : α => ¬ f a = -1) := by
      ext a
      simp [eqprod, hprod, hnot_neg_eq_pos]
    have hcard_split := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (p:=fun a : α => f a = -1)
    change negs.card + (Finset.univ.filter (fun a : α => ¬ f a = -1)).card = Fintype.card α at hcard_split
    rw [heqset]
    have heqcard : (Finset.univ.filter (fun a : α => ¬ f a = -1)).card = Fintype.card α - negs.card := by omega
    rw [heqcard]
    have hle : negs.card ≤ Fintype.card α := by omega
    exact Nat.Odd.sub_even hle hodd hneg_even
  · have hprod_neg : (∏ a, f a) = (-1 : ℤ) := by
      have hcases : (∏ a, f a) = 1 ∨ (∏ a, f a) = -1 := by
        rw [hprod_pm]
        by_cases he : Even negs.card
        · left; exact Even.neg_one_pow he
        · right; exact Odd.neg_one_pow (Nat.not_even_iff_odd.mp he)
      exact hcases.resolve_left hprod
    have hneg_odd : Odd negs.card := by
      have hpow : (-1 : ℤ) ^ negs.card = -1 := hprod_pm.symm.trans hprod_neg
      exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℤ) ≠ 1)).mp hpow
    have heq : eqprod = negs := by
      ext a
      simp [eqprod, negs, hprod_neg]
    rw [heq]
    exact hneg_odd


lemma odd_count_one_of_pm_one_prod_one {α : Type*} [Fintype α]
    (f : α → ℤ) (hf : ∀ a, f a = 1 ∨ f a = -1)
    (hodd : Odd (Fintype.card α)) (hprod : (∏ a, f a) = 1) :
    Odd (Fintype.card {a : α // f a = 1}) := by
  have h := odd_count_eq_prod_of_pm_one f hf hodd
  simpa [hprod] using h


lemma odd_count_prod_mul_eq_one_of_pm_one {α : Type*} [Fintype α]
    (g : α → ℤ) (hg : ∀ a, g a = 1 ∨ g a = -1)
    (hodd : Odd (Fintype.card α)) :
    Odd (Fintype.card {a : α // (∏ b, g b) * g a = 1}) := by
  classical
  let P : ℤ := ∏ b, g b
  let f : α → ℤ := fun a => P * g a
  have hP_pm : P = 1 ∨ P = -1 := by
    have hp := prod_pm_one_eq_neg_one_pow_count_neg g hg
    change (∏ b, g b) = 1 ∨ (∏ b, g b) = -1
    rw [hp]
    by_cases he : Even (Fintype.card {a : α // g a = -1})
    · left; exact Even.neg_one_pow he
    · right; exact Odd.neg_one_pow (Nat.not_even_iff_odd.mp he)
  have hf : ∀ a, f a = 1 ∨ f a = -1 := by
    intro a
    rcases hP_pm with hP | hP <;> rcases hg a with h | h <;> simp [f, P, hP, h]
  have hprod : (∏ a, f a) = 1 := by
    have hconst : (∏ a, f a) = P ^ Fintype.card α * (∏ a, g a) := by
      simp [f, Finset.prod_mul_distrib]
    rw [hconst]
    change P ^ Fintype.card α * P = 1
    rcases hP_pm with hP | hP
    · simp [hP]
    · rcases hodd with ⟨k, hk⟩
      rw [hP, hk]
      simp [pow_succ, pow_mul]
  have h := odd_count_one_of_pm_one_prod_one f hf hodd hprod
  simpa [f, P] using h



