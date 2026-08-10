import FormalConjectures.Util.ProblemImports

open Matrix Nat Int

/--
A226163: Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! \cdot j}{p_n}\right)$$
where $p_n$ is the $n$-th prime.
The sequence is naturally indexed starting from $n=2$.
-/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else

  -- p is the n-th prime, p_n. Mathlib's nth Nat.Prime is 0-indexed, so we use (n-1).
  -- Since n >= 2, p >= 3 is an an odd prime.
  let p : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Matrix dimension m = (p-1)/2.
  let m : ℕ := (p - 1) / 2

  -- The constant C = ((p-1)/2)! as an integer.
  let C : ℤ := m.factorial.cast

  -- The matrix M has entries in ℤ.
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    -- 1-based indices i' and j' for the formula: 1 <= i', j' <= m.
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast

    -- Argument for the Legendre symbol: i'^2 - C * j'
    let arg : ℤ := i' * i' - C * j'

    -- jacobiSym is the Legendre symbol since p is prime.
    jacobiSym arg p

  M.det

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





open Matrix Polynomial
open scoped BigOperators

variable {n R : Type*} [Fintype n] [DecidableEq n] [Field R] [CharZero R]

lemma det_mixed_identity_principal' {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (p : n → Prop) [DecidablePred p]
    (T : Matrix n n R) :
    (Matrix.det (fun i j : n => if p j then T i j else if i = j then (1 : R) else 0)) =
      Matrix.det (T.submatrix (fun x : {i // p i} => (x : n)) (fun x : {i // p i} => (x : n))) := by
  let M : Matrix n n R := fun i j => if p j then T i j else if i = j then (1 : R) else 0
  let e : ({i : n // p i} ⊕ {i : n // ¬ p i}) ≃ n := Equiv.sumCompl p
  have hdet := (Matrix.det_submatrix_equiv_self e M).symm
  change M.det = _
  rw [hdet]
  let N : Matrix ({i : n // p i} ⊕ {i : n // ¬ p i}) ({i : n // p i} ⊕ {i : n // ¬ p i}) R := M.submatrix e e
  change Matrix.det N = _
  have hN : Matrix.fromBlocks N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂ = N :=
    Matrix.fromBlocks_toBlocks N
  rw [← hN]
  have h12 : N.toBlocks₁₂ = 0 := by
    ext i j
    simp [Matrix.toBlocks₁₂, N, Matrix.submatrix, M, e, j.2,
      Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
  have h22 : N.toBlocks₂₂ = 1 := by
    ext i j
    rw [Matrix.one_apply]
    simp [Matrix.toBlocks₂₂, N, Matrix.submatrix, M, e, j.2,
      Equiv.sumCompl_apply_inr]
  have h11 : N.toBlocks₁₁ = T.submatrix (fun x : {i // p i} => (x : n)) (fun x : {i // p i} => (x : n)) := by
    ext i j
    simp [Matrix.toBlocks₁₁, N, Matrix.submatrix, M, e, j.2,
      Equiv.sumCompl_apply_inl]
  rw [h12, Matrix.det_fromBlocks_zero₁₂, h22, Matrix.det_one, mul_one, h11]

lemma det_eq_zero_of_transpose_eq_neg_odd'' {m R : Type*} [Fintype m] [DecidableEq m]
    [CommRing R] [NoZeroDivisors R] [CharZero R]
    (M : Matrix m m R) (hM : Mᵀ = (-1 : R) • M) (hodd : Odd (Fintype.card m)) :
    M.det = 0 := by
  have hdet : M.det = (((-1 : R) • M).det) := by
    rw [← hM, Matrix.det_transpose]
  have hneg : (((-1 : R) • M).det) = (-1 : R) ^ Fintype.card m * M.det := by
    simpa using Matrix.det_smul M (-1 : R)
  rw [hneg] at hdet
  have hpow : (-1 : R) ^ Fintype.card m = -1 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk]
    simp [pow_succ, pow_mul]
  rw [hpow] at hdet
  have hdneg : M.det = -M.det := by simpa using hdet
  have hadd : M.det + M.det = 0 := by
    nth_rewrite 2 [hdneg]
    exact add_neg_cancel M.det
  have htwo : (2 : R) * M.det = 0 := by
    simpa [two_mul] using hadd
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

lemma mixed_column_det_zero' {K : Type*} [Field K] [CharZero K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : n → Prop) [DecidablePred p]
    (A B : Matrix n n K) (hBunit : IsUnit B.det)
    (hTskew : (B⁻¹ * A)ᵀ = (-1 : K) • (B⁻¹ * A))
    (hodd : Odd (Fintype.card {j : n // p j})) :
    Matrix.det (fun i j : n => if p j then A i j else B i j) = 0 := by
  let C : Matrix n n K := fun i j => if p j then A i j else B i j
  let T : Matrix n n K := B⁻¹ * A
  let N : Matrix n n K := B⁻¹ * C
  have hNentry : N = fun i j : n => if p j then T i j else if i = j then (1 : K) else 0 := by
    ext i j
    by_cases hj : p j
    · simp [N, C, T, hj, Matrix.mul_apply]
    · have hmul := congr_fun (congr_fun (Matrix.nonsing_inv_mul B hBunit) i) j
      simp [N, C, T, hj, Matrix.mul_apply] at hmul ⊢
      simpa [Matrix.one_apply] using hmul
  have hpr_skew : ((T.submatrix (fun x : {j : n // p j} => (x : n)) (fun x : {j : n // p j} => (x : n)))ᵀ)
      = (-1 : K) • (T.submatrix (fun x : {j : n // p j} => (x : n)) (fun x : {j : n // p j} => (x : n))) := by
    ext i j
    have ht := congr_fun (congr_fun hTskew (i : n)) (j : n)
    simpa [Matrix.transpose_apply, Matrix.smul_apply, T] using ht
  have hpr_det : Matrix.det (T.submatrix (fun x : {j : n // p j} => (x : n)) (fun x : {j : n // p j} => (x : n))) = 0 :=
    det_eq_zero_of_transpose_eq_neg_odd'' _ hpr_skew hodd
  have hNdet : N.det = 0 := by
    rw [hNentry, det_mixed_identity_principal' p T, hpr_det]
  have hBC : B * N = C := by
    calc
      B * N = B * (B⁻¹ * C) := rfl
      _ = (B * B⁻¹) * C := by rw [Matrix.mul_assoc]
      _ = C := by rw [Matrix.mul_nonsing_inv B hBunit, Matrix.one_mul]
  have hdetC : C.det = (B * N).det := by rw [hBC]
  rw [hdetC, Matrix.det_mul, hNdet, mul_zero]

lemma transpose_nonsing_inv_mul_eq_neg' {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) (hBunit : IsUnit B.det)
    (hA : Aᵀ = (-1 : K) • A) (hB : Bᵀ = B) (hcomm : A * B = B * A) :
    (B⁻¹ * A)ᵀ = (-1 : K) • (B⁻¹ * A) := by
  calc
    (B⁻¹ * A)ᵀ = Aᵀ * (B⁻¹)ᵀ := by rw [Matrix.transpose_mul]
    _ = ((-1 : K) • A) * (Bᵀ)⁻¹ := by rw [hA, Matrix.transpose_nonsing_inv]
    _ = ((-1 : K) • A) * B⁻¹ := by rw [hB]
    _ = (-1 : K) • (A * B⁻¹) := by simp
    _ = (-1 : K) • (B⁻¹ * A) := by
      congr 1
      calc
        A * B⁻¹ = (B⁻¹ * B) * (A * B⁻¹) := by
          rw [Matrix.nonsing_inv_mul B hBunit, Matrix.one_mul]
        _ = B⁻¹ * (B * (A * B⁻¹)) := by rw [Matrix.mul_assoc]
        _ = B⁻¹ * ((B * A) * B⁻¹) := by rw [Matrix.mul_assoc]
        _ = B⁻¹ * ((A * B) * B⁻¹) := by rw [← hcomm]
        _ = B⁻¹ * (A * (B * B⁻¹)) := by rw [Matrix.mul_assoc]
        _ = B⁻¹ * A := by rw [Matrix.mul_nonsing_inv B hBunit, Matrix.mul_one]

set_option maxHeartbeats 800000 in

lemma mixed_column_det_zero_commuting
    (p : n → Prop) [DecidablePred p]
    (A B : Matrix n n R)
    (hA : Aᵀ = (-1 : R) • A) (hB : Bᵀ = B) (hcomm : A * B = B * A)
    (hodd : Odd (Fintype.card {j : n // p j})) :
    Matrix.det (fun i j : n => if p j then A i j else B i j) = 0 := by
  let P := R[X]
  let K := FractionRing P
  let fPK : P →+* K := algebraMap P K
  let fRK : R →+* K := algebraMap R K
  let Bpoly : Matrix n n P := (Polynomial.X : P) • (1 : Matrix n n P) + B.map Polynomial.C
  let Cpoly : Matrix n n P := fun i j => if p j then Polynomial.C (A i j) else Bpoly i j
  let AK : Matrix n n K := fRK.mapMatrix A
  let BK : Matrix n n K := fPK.mapMatrix Bpoly
  have hBpoly_ne : Bpoly.det ≠ 0 := by
    intro hzero
    have hlc := Polynomial.leadingCoeff_det_X_one_add_C B
    have : (Bpoly.det).leadingCoeff = 0 := by simp [hzero]
    have hBpoly_eq : Bpoly = (Polynomial.X : P) • (1 : Matrix n n P) + B.map Polynomial.C := rfl
    rw [← hBpoly_eq] at hlc
    rw [this] at hlc
    exact one_ne_zero hlc.symm
  have hBKunit : IsUnit BK.det := by
    rw [← RingHom.map_det]
    apply (isUnit_iff_ne_zero).mpr
    exact (IsFractionRing.to_map_eq_zero_iff.not).mpr hBpoly_ne
  have hAKskew : AKᵀ = (-1 : K) • AK := by
    ext i j
    have ht := congr_fun (congr_fun hA i) j
    have ht' := congr_arg fRK ht
    have ht'' : fRK (A j i) = - fRK (A i j) := by
      simpa [Matrix.transpose_apply, Matrix.smul_apply, map_neg] using ht'
    have hneg : - fRK (A i j) = (-1 : K) * fRK (A i j) := by ring
    simpa [AK, Matrix.transpose_apply, Matrix.smul_apply] using ht''.trans hneg
  have hBKsymm : BKᵀ = BK := by
    ext i j
    have ht := congr_fun (congr_fun hB i) j
    by_cases hij : i = j
    · subst j
      simp [BK, Bpoly, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply]
    · have hji : j ≠ i := by exact fun h => hij h.symm
      have ht' := congr_arg (fun x : R => fPK (Polynomial.C x)) ht
      simp [BK, Bpoly, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, hij, hji] at ht' ⊢
      exact ht'
  have hcommK : AK * BK = BK * AK := by
    let xK : K := fPK Polynomial.X
    let BKC : Matrix n n K := fRK.mapMatrix B
    have hBKdecomp : BK = xK • (1 : Matrix n n K) + BKC := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [BK, Bpoly, BKC, xK, fRK, fPK]
        rw [Algebra.smul_def, mul_one]
        congr 1

      · have hji : j ≠ i := fun h => hij h.symm
        simp [BK, Bpoly, BKC, xK, hij, hji, fRK, fPK]
        exact (IsScalarTower.algebraMap_apply R (R[X]) K (B i j)).symm
    have hABKC : AK * BKC = BKC * AK := by
      dsimp [AK, BKC]
      rw [← Matrix.map_mul, ← Matrix.map_mul, hcomm]
    rw [hBKdecomp]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, hABKC]
  have hTskew := transpose_nonsing_inv_mul_eq_neg' AK BK hBKunit hAKskew hBKsymm hcommK
  have hdetK : Matrix.det (fun i j : n => if p j then AK i j else BK i j) = 0 :=
    mixed_column_det_zero' p AK BK hBKunit hTskew hodd
  have hmapC : fPK.mapMatrix Cpoly = (fun i j : n => if p j then AK i j else BK i j) := by
    ext i j
    by_cases hj : p j
    · simp [Cpoly, AK, BK, Bpoly, hj, fRK, fPK]
      rw [Polynomial.C_eq_algebraMap, IsScalarTower.algebraMap_apply R P K]
    · simp [Cpoly, AK, BK, Bpoly, hj, fRK, fPK]
  have hCpoly_det_zero : Cpoly.det = 0 := by
    have hm : fPK Cpoly.det = 0 := by
      rw [RingHom.map_det, hmapC, hdetK]
    exact (IsFractionRing.to_map_eq_zero_iff (K:=K)).mp hm
  have h_eval : (Polynomial.evalRingHom (0 : R)) Cpoly.det = Matrix.det (fun i j : n => if p j then A i j else B i j) := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases hj : p j
    · simp [Cpoly, Bpoly, hj]
    · by_cases hij : i = j
      · subst j
        simp [Cpoly, Bpoly, hj, Polynomial.evalRingHom]
        rw [Polynomial.coeff_add, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero]
        simp
      · simp [Cpoly, Bpoly, hj, hij, Polynomial.evalRingHom, Polynomial.coeff_C_zero]
  rw [← h_eval, hCpoly_det_zero]
  simp


open Finset MulChar
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma jacobiSum_quadratic_quadratic (hF : ringChar F ≠ 2) :
    jacobiSum (quadraticChar F) (quadraticChar F) = -(quadraticChar F (-1)) := by
  have hne : quadraticChar F ≠ 1 := quadraticChar_ne_one hF
  have hinv : (quadraticChar F)⁻¹ = quadraticChar F := (quadraticChar_isQuadratic F).inv
  nth_rewrite 2 [← hinv]
  exact jacobiSum_nontrivial_inv hne

lemma sum_quadratic_mul_one_sub (hF : ringChar F ≠ 2) :
    (∑ x : F, (quadraticChar F) x * (quadraticChar F) (1 - x)) =
      -(quadraticChar F (-1)) := by
  simpa [jacobiSum] using jacobiSum_quadratic_quadratic (F:=F) hF

lemma sum_quadratic_mul_sub_one (hF : ringChar F ≠ 2) :
    (∑ x : F, (quadraticChar F) x * (quadraticChar F) (x - 1)) =
      -1 := by
  calc
    (∑ x : F, (quadraticChar F) x * (quadraticChar F) (x - 1))
        = ∑ x : F, (quadraticChar F) (-1) * ((quadraticChar F) x * (quadraticChar F) (1 - x)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [show x - 1 = -1 * (1 - x) by ring]
          rw [map_mul]
          ring
    _ = (quadraticChar F) (-1) * (∑ x : F, (quadraticChar F) x * (quadraticChar F) (1 - x)) := by
          rw [Finset.mul_sum]
    _ = (quadraticChar F) (-1) * (-(quadraticChar F (-1))) := by
          rw [sum_quadratic_mul_one_sub (F:=F) hF]
    _ = -1 := by
          have hneg : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
          have hs := quadraticChar_sq_one (F:=F) hneg
          nlinarith


lemma sum_quadratic_mul_shift_ne (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    (∑ x : F, (quadraticChar F) (x - a) * (quadraticChar F) (x - b)) = -1 := by
  let d : F := b - a
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  -- substitute x = a + d * y
  calc
    (∑ x : F, (quadraticChar F) (x - a) * (quadraticChar F) (x - b))
        = ∑ y : F, (quadraticChar F) (((Equiv.mulLeft₀ d hd).trans (Equiv.addLeft a)) y - a) *
            (quadraticChar F) (((Equiv.mulLeft₀ d hd).trans (Equiv.addLeft a)) y - b) := by
          exact (Equiv.sum_comp ((Equiv.mulLeft₀ d hd).trans (Equiv.addLeft a))
            (fun x : F => (quadraticChar F) (x - a) * (quadraticChar F) (x - b))).symm
    _ = ∑ y : F, (quadraticChar F) ((a + d * y) - a) * (quadraticChar F) ((a + d * y) - b) := by
          simp [add_comm]
    _ = ∑ y : F, (quadraticChar F) d ^ 2 * ((quadraticChar F) y * (quadraticChar F) (y - 1)) := by
          apply Finset.sum_congr rfl
          intro y _
          have h1 : (a + d * y) - a = d * y := by ring
          have h2 : (a + d * y) - b = d * (y - 1) := by
            dsimp [d]
            ring
          rw [h1, h2, map_mul, map_mul]
          ring
    _ = ∑ y : F, (quadraticChar F) y * (quadraticChar F) (y - 1) := by
          apply Finset.sum_congr rfl
          intro y _
          have hs := quadraticChar_sq_one (F:=F) hd
          rw [hs]
          ring
    _ = -1 := sum_quadratic_mul_sub_one (F:=F) hF


lemma sum_quadratic_square_shift (hF : ringChar F ≠ 2) (a : F) :
    (∑ x : F, (quadraticChar F) (x - a) * (quadraticChar F) (x - a)) = (Fintype.card F : ℤ) - 1 := by
  calc
    (∑ x : F, (quadraticChar F) (x - a) * (quadraticChar F) (x - a))
        = ∑ y : F, (quadraticChar F) y * (quadraticChar F) y := by
          exact (Equiv.sum_comp (Equiv.addRight a)
            (fun x : F => (quadraticChar F) (x - a) * (quadraticChar F) (x - a))).symm.trans (by simp)
    _ = ∑ y : F, if y = 0 then (0 : ℤ) else 1 := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : y = 0
          · simp [hy]
          · have hs := quadraticChar_sq_one (F:=F) hy
            simpa [hy, pow_two] using hs
    _ = (Fintype.card F : ℤ) - 1 := by
          rw [Finset.sum_eq_sum_diff_singleton_add (s:=Finset.univ) (i:=(0:F)) (by simp)
            (fun y => if y = 0 then (0 : ℤ) else 1)]
          simp only [ite_true, add_zero]
          have hconst : (∑ x ∈ (Finset.univ \ {0} : Finset F), if x = 0 then (0 : ℤ) else 1) =
              ∑ x ∈ (Finset.univ \ {0} : Finset F), (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp at hx
            simp [hx]
          rw [hconst, Finset.sum_const, nsmul_eq_mul]
          simp
          have hcard : #(Finset.univ \ ({0} : Finset F)) = Fintype.card F - 1 := by
            rw [Finset.card_sdiff]
            simp
          rw [hcard]
          have hpos : 1 ≤ Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
          rw [Nat.cast_sub hpos]
          simp


lemma sum_quadratic_mul_shift (hF : ringChar F ≠ 2) (a b : F) :
    (∑ x : F, (quadraticChar F) (x - a) * (quadraticChar F) (x - b)) =
      if a = b then (Fintype.card F : ℤ) - 1 else -1 := by
  by_cases hab : a = b
  · subst b
    simpa using sum_quadratic_square_shift (F:=F) hF a
  · simpa [hab] using sum_quadratic_mul_shift_ne (F:=F) hF hab


open Matrix Finset MulChar
open scoped BigOperators

lemma sum_QR_eq_half_weighted2 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (g : F → ℚ) :
    (∑ s : QR2 F, g s) = (1 / 2 : ℚ) *
      ∑ x : F, (((quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * g x) := by
  classical
  have hsub : (∑ s : QR2 F, g s) = (Finset.univ.filter (fun x : F => quadraticChar F x = 1)).sum (fun x => g x) := by
    symm
    simpa using (Finset.sum_subtype (s := Finset.univ.filter (fun x : F => quadraticChar F x = 1))
      (h := by intro x; simp) (f := g))
  rw [hsub]
  calc
    (Finset.univ.filter (fun x : F => quadraticChar F x = 1)).sum (fun x => g x)
        = ∑ x : F, if quadraticChar F x = 1 then g x else 0 := by
          simp [Finset.sum_filter]
    _ = (1 / 2 : ℚ) * ∑ x : F, (((quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * g x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · by_cases h1 : quadraticChar F x = 1
        · simp [h1]
        · have hsq := quadraticChar_sq_one (F:=F) hx0
          have hneg : quadraticChar F x = -1 := by
            exact quadraticChar_eq_neg_one_iff_not_one hx0 |>.2 h1
          simp [h1, hneg, hsq]

lemma sum_QR_neg_eq_half_weighted2 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hneg1 : quadraticChar F (-1) = -1) (g : F → ℚ) :
    (∑ s : QR2 F, g (-(s : F))) = (1 / 2 : ℚ) *
      ∑ x : F, (((-quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * g x) := by
  classical
  have hsub : (∑ s : QR2 F, g (-(s : F))) = (Finset.univ.filter (fun x : F => quadraticChar F x = 1)).sum (fun x => g (-x)) := by
    symm
    simpa using (Finset.sum_subtype (s := Finset.univ.filter (fun x : F => quadraticChar F x = 1))
      (h := by intro x; simp) (f := fun x => g (-x)))
  rw [hsub]
  calc
    (Finset.univ.filter (fun x : F => quadraticChar F x = 1)).sum (fun x => g (-x))
        = (Finset.univ.filter (fun y : F => quadraticChar F y = -1)).sum (fun y => g y) := by
          apply Finset.sum_bij (fun x _ => -x)
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            rw [show (-x) = (-1 : F) * x by ring]
            rw [map_mul, hneg1, hx]
            norm_num
          · intro x hx y hy hxy
            exact neg_injective hxy
          · intro y hy
            refine ⟨-y, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
              rw [show (-y) = (-1 : F) * y by ring]
              rw [map_mul, hneg1, hy]
              norm_num
            · simp
          · intro x hx
            simp
    _ = ∑ x : F, if quadraticChar F x = -1 then g x else 0 := by
          simp [Finset.sum_filter]
    _ = (1 / 2 : ℚ) * ∑ x : F, (((-quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * g x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hx0 : x = 0
          · simp [hx0]
          · by_cases hneg : quadraticChar F x = -1
            · have hsq : (quadraticChar F x)^2 = (1:ℤ) := by rw [hneg]; norm_num
              simp [hneg, hsq]
            · have hsq := quadraticChar_sq_one (F:=F) hx0
              have hcases := quadraticChar_dichotomy (F:=F) hx0
              rcases hcases with h1 | hm
              · simp [hneg, h1, hsq]
              · exact False.elim (hneg hm)

lemma paley_full_sum_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hneg1 : quadraticChar F (-1) = -1) (r t : QR2 F) :
    (∑ x : F, (quadraticChar F) ((r:F) - x) * (quadraticChar F) (x + (t:F))) = 1 := by
  have hrt : (r : F) ≠ -(t : F) := by
    intro h
    have hr : quadraticChar F (r:F) = 1 := r.2
    have ht : quadraticChar F (t:F) = 1 := t.2
    have hcalc : quadraticChar F (r:F) = -1 := by
      rw [h]
      rw [show (-(t : F)) = (-1 : F) * (t : F) by ring, map_mul, hneg1, ht]
      norm_num
    rw [hr] at hcalc
    norm_num at hcalc
  calc
    (∑ x : F, (quadraticChar F) ((r:F) - x) * (quadraticChar F) (x + (t:F)))
        = ∑ x : F, (-(quadraticChar F) (x - (r:F))) * (quadraticChar F) (x - (-(t:F))) := by
          apply Finset.sum_congr rfl
          intro x hx
          have h1 : (r:F) - x = - ((x - (r:F))) := by ring
          have h2 : x + (t:F) = x - (-(t:F)) := by ring
          rw [h1, h2]
          rw [show (-(x - (r:F))) = (-1 : F) * (x - (r:F)) by ring, map_mul, hneg1]
          ring
    _ = - (∑ x : F, (quadraticChar F) (x - (r:F)) * (quadraticChar F) (x - (-(t:F)))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = 1 := by
          have hs := sum_quadratic_mul_shift_ne (F:=F) hF hrt
          rw [hs]
          norm_num


lemma paley_indicator_sum_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hneg1 : quadraticChar F (-1) = -1) (r t : QR2 F) :
    (∑ x : F, (((quadraticChar F x)^2 : ℤ) : ℚ) *
      (((quadraticChar F) ((r:F) - x) * (quadraticChar F) (x + (t:F)) : ℤ) : ℚ)) = 0 := by
  let f : F → ℤ := fun x => (quadraticChar F) ((r:F) - x) * (quadraticChar F) (x + (t:F))
  have hfullZ := paley_full_sum_one (F:=F) hF hneg1 r t
  have hfullQ : (∑ x : F, ((f x : ℤ) : ℚ)) = 1 := by
    norm_num [f] at hfullZ ⊢
    exact_mod_cast hfullZ
  have hf0 : f 0 = 1 := by
    dsimp [f]
    rw [sub_zero, zero_add]
    change (quadraticChar F (r:F)) * (quadraticChar F (t:F)) = 1
    rw [r.2, t.2]
    norm_num
  calc
    (∑ x : F, (((quadraticChar F x)^2 : ℤ) : ℚ) * ((f x : ℤ) : ℚ))
        = ∑ x : F, (if x = 0 then (0 : ℚ) else ((f x : ℤ) : ℚ)) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hx0 : x = 0
          · simp [hx0]
          · have hsq := quadraticChar_sq_one (F:=F) hx0
            simp [hx0]
            change ((((quadraticChar F x)^2 : ℤ) : ℚ) * ((f x : ℤ) : ℚ)) = ((f x : ℤ) : ℚ)
            rw [hsq]
            norm_num
    _ = (∑ x : F, ((f x : ℤ) : ℚ)) - ((f 0 : ℤ) : ℚ) := by
          have hset : Finset.univ \ ({0} : Finset F) = Finset.univ.erase (0:F) := by
            ext x; simp
          have hif : (∑ x : F, if x = 0 then (0 : ℚ) else ((f x : ℤ) : ℚ)) =
              (Finset.univ.erase (0:F)).sum (fun x => ((f x : ℤ) : ℚ)) := by
            rw [Finset.sum_eq_sum_diff_singleton_add (s:=Finset.univ) (i:=(0:F)) (by simp)
              (fun x => if x = 0 then (0:ℚ) else ((f x:ℤ):ℚ))]
            simp only [if_true, add_zero]
            rw [hset]
            apply Finset.sum_congr rfl
            intro x hx
            simp at hx
            simp [hx]
          have htot : (∑ x : F, ((f x : ℤ) : ℚ)) =
              ((Finset.univ.erase (0:F)).sum (fun x => ((f x : ℤ) : ℚ))) + ((f 0 : ℤ) : ℚ) := by
            rw [Finset.sum_eq_sum_diff_singleton_add (s:=Finset.univ) (i:=(0:F)) (by simp)
              (fun x => ((f x:ℤ):ℚ))]
            rw [hset]
          rw [hif, htot]
          ring
    _ = 0 := by
          rw [hfullQ, hf0]
          norm_num

lemma paley_matrices_commute {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hneg1 : quadraticChar F (-1) = -1) :
    let A : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) - (s:F)) : ℤ) : ℚ)
    let B : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) + (s:F)) : ℤ) : ℚ)
    A * B = B * A := by
  classical
  intro A B
  ext r t
  let f : F → ℚ := fun x => (((quadraticChar F) ((r:F) - x) * (quadraticChar F) (x + (t:F)) : ℤ) : ℚ)
  have hAB : (A * B) r t = (1 / 2 : ℚ) * ∑ x : F,
      (((quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x) := by
    calc
      (A * B) r t = ∑ s : QR2 F, f (s : F) := by
        simp [Matrix.mul_apply, A, B, f]
      _ = (1 / 2 : ℚ) * ∑ x : F,
          (((quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x) :=
        sum_QR_eq_half_weighted2 (F:=F) f
  have hBA : (B * A) r t = (1 / 2 : ℚ) * ∑ x : F,
      (((quadraticChar F x - (quadraticChar F x)^2 : ℤ) : ℚ) * f x) := by
    have hneg := sum_QR_neg_eq_half_weighted2 (F:=F) hneg1 f
    -- BA summand is `- f (-s)`.
    calc
      (B * A) r t = ∑ s : QR2 F, - f (-(s:F)) := by
        simp [Matrix.mul_apply, A, B, f]
        conv_rhs => rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        rw [show (↑s - (t:F)) = - ((-(s:F)) + (t:F)) by ring]
        rw [show ((r:F) + ↑s) = (r:F) - (-(s:F)) by ring]
        rw [show (-((-(s:F)) + (t:F))) = (-1 : F) * ((-(s:F)) + (t:F)) by ring]
        change (((quadraticChar F) ((r:F) - (-(s:F))) : ℤ) : ℚ) *
            (((quadraticChar F) ((-1 : F) * ((-(s:F)) + (t:F))) : ℤ) : ℚ) =
          - ((((quadraticChar F) ((r:F) - (-(s:F))) : ℤ) : ℚ) *
            (((quadraticChar F) ((-(s:F)) + (t:F)) : ℤ) : ℚ))
        rw [map_mul, hneg1]
        rw [show (-1 : ℤ) * (quadraticChar F (-(s:F) + (t:F))) =
            - (quadraticChar F (-(s:F) + (t:F))) by ring]
        rw [Int.cast_neg]
        ring
      _ = - (∑ s : QR2 F, f (-(s:F))) := by rw [Finset.sum_neg_distrib]
      _ = - ((1 / 2 : ℚ) * ∑ x : F, (((-quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x)) := by rw [hneg]
      _ = (1 / 2 : ℚ) * ∑ x : F, (((quadraticChar F x - (quadraticChar F x)^2 : ℤ) : ℚ) * f x) := by
        rw [show -((1 / 2 : ℚ) * ∑ x : F, (((-quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x)) =
            (1 / 2 : ℚ) * (-(∑ x : F, (((-quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x))) by ring]
        rw [← Finset.sum_neg_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        norm_num
        ring
  have hS2 := paley_indicator_sum_zero (F:=F) hF hneg1 r t
  rw [hAB, hBA]
  have hsplit1 : (∑ x : F, (((quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x)) =
      (∑ x : F, ((quadraticChar F x : ℤ) : ℚ) * f x) +
      (∑ x : F, (((quadraticChar F x)^2 : ℤ) : ℚ) * f x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    norm_num
    ring
  have hsplit2 : (∑ x : F, (((quadraticChar F x - (quadraticChar F x)^2 : ℤ) : ℚ) * f x)) =
      (∑ x : F, ((quadraticChar F x : ℤ) : ℚ) * f x) -
      (∑ x : F, (((quadraticChar F x)^2 : ℤ) : ℚ) * f x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    norm_num
    ring
  rw [hsplit1, hsplit2, hS2]
  ring


lemma paley_A_skew {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hneg1 : quadraticChar F (-1) = -1) :
    let A : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) - (s:F)) : ℤ) : ℚ)
    Aᵀ = (-1 : ℚ) • A := by
  intro A
  ext r s
  by_cases hrs : (r : F) = (s : F)
  · simp [A, Matrix.transpose_apply, Matrix.smul_apply, hrs]
  · have hsub : (s:F) - (r:F) = (-1 : F) * ((r:F) - (s:F)) := by ring
    rw [Matrix.transpose_apply, Matrix.smul_apply]
    simp [A]
    rw [hsub]
    change (((quadraticChar F) ((-1 : F) * ((r:F) - (s:F))) : ℤ) : ℚ) =
      - (((quadraticChar F) ((r:F) - (s:F)) : ℤ) : ℚ)
    rw [map_mul, hneg1]
    norm_num

lemma paley_B_symm {F : Type*} [Field F] [Fintype F] [DecidableEq F] :
    let B : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) + (s:F)) : ℤ) : ℚ)
    Bᵀ = B := by
  intro B
  ext r s
  simp [B, Matrix.transpose_apply, add_comm]


lemma paley_mixed_det_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hneg1 : quadraticChar F (-1) = -1)
    (p : QR2 F → Prop) [DecidablePred p]
    (hodd : Odd (Fintype.card {j : QR2 F // p j})) :
    let A : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) - (s:F)) : ℤ) : ℚ)
    let B : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) + (s:F)) : ℤ) : ℚ)
    Matrix.det (fun i j : QR2 F => if p j then A i j else B i j) = 0 := by
  intro A B
  exact mixed_column_det_zero_commuting (R:=ℚ) p A B
    (paley_A_skew (F:=F) hneg1)
    (paley_B_symm (F:=F))
    (paley_matrices_commute (F:=F) hF hneg1)
    hodd



open Polynomial Finset Matrix
open scoped BigOperators

lemma moment_m_eq_neg_const {K : Type*} [Field K] {m : ℕ} (hmpos : 0 < m)
    (y : Fin m → K) (v : Fin m → K)
    (hmom : ∀ r : Fin m, r.val ≠ 0 → (∑ j : Fin m, v j * y j ^ r.val) = 0) :
    (∑ j : Fin m, v j * y j ^ m) =
      - ((∏ j : Fin m, - y j) * (∑ j : Fin m, v j)) := by
  classical
  let P : K[X] := ∏ j ∈ (Finset.univ : Finset (Fin m)), (X - C (y j))
  have hPnat : P.natDegree = m := by
    dsimp [P]
    rw [Polynomial.natDegree_prod_of_monic]
    · simp
    · intro i hi; exact monic_X_sub_C (y i)
  have hPmonic : P.Monic := by
    dsimp [P]
    simpa using (Polynomial.monic_prod_X_sub_C y (Finset.univ : Finset (Fin m)))
  have hPcoeffm : P.coeff m = 1 := by
    rw [← hPnat]
    exact hPmonic.coeff_natDegree
  have hPcoeff0 : P.coeff 0 = ∏ j : Fin m, - y j := by
    dsimp [P]
    rw [Polynomial.coeff_zero_prod]
    simp
  let S : ℕ → K := fun r => ∑ j : Fin m, v j * y j ^ r
  have hroot (j : Fin m) : P.eval (y j) = 0 := by
    dsimp [P]
    rw [Polynomial.eval_prod]
    change ((Finset.univ : Finset (Fin m)).prod (fun x => Polynomial.eval (y j) (X - C (y x)))) = 0
    exact Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin m))) (i := j) (by simp) (by simp)
  have hevalsum (j : Fin m) : (∑ r ∈ Finset.range (m+1), P.coeff r * y j ^ r) = 0 := by
    have hdeg : P.natDegree < m + 1 := by rw [hPnat]; omega
    have he : P.eval (y j) = ∑ i ∈ Finset.range (m+1), P.coeff i * y j ^ i :=
      Polynomial.eval_eq_sum_range' hdeg (y j)
    rw [hroot j] at he
    exact he.symm
  have hmain : (∑ r ∈ Finset.range (m+1), P.coeff r * S r) = 0 := by
    calc
      (∑ r ∈ Finset.range (m+1), P.coeff r * S r)
          = ∑ r ∈ Finset.range (m+1), P.coeff r * (∑ j : Fin m, v j * y j ^ r) := rfl
      _ = ∑ r ∈ Finset.range (m+1), ∑ j : Fin m, P.coeff r * (v j * y j ^ r) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
      _ = ∑ j : Fin m, ∑ r ∈ Finset.range (m+1), P.coeff r * (v j * y j ^ r) := by
          rw [Finset.sum_comm]
      _ = ∑ j : Fin m, v j * (∑ r ∈ Finset.range (m+1), P.coeff r * y j ^ r) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
      _ = 0 := by simp [hevalsum]
  have hsplit : (∑ r ∈ Finset.range m, P.coeff r * S r) = P.coeff 0 * S 0 := by
    apply Finset.sum_eq_single 0
    · intro r hr hr0
      have hrlt : r < m := by simpa using hr
      have hmz : S r = 0 := by
        exact hmom ⟨r, hrlt⟩ hr0
      simp [hmz]
    · intro h0not
      exact (h0not (by simpa [hmpos] : 0 ∈ Finset.range m)).elim
  rw [Finset.sum_range_succ] at hmain
  rw [hsplit, hPcoeffm, one_mul] at hmain
  have : P.coeff 0 * S 0 + S m = 0 := by simpa [add_comm, add_left_comm, add_assoc] using hmain
  have hs : S m = - (P.coeff 0 * S 0) := by
    exact eq_neg_of_add_eq_zero_right this
  simpa [S, hPcoeff0] using hs

noncomputable def momentMatrix {K : Type*} [Field K] {m : ℕ}
    (A : K) (d : Fin m → K) (y : Fin m → K) : Matrix (Fin m) (Fin m) K :=
  fun r j => if hr : r.val = 0 then A * y j ^ m + 1 else d r * y j ^ (m - r.val)

lemma momentMatrix_det_ne_zero {K : Type*} [Field K] {m : ℕ} (hmpos : 0 < m)
    (A : K) (d : Fin m → K) (y : Fin m → K)
    (hy : Function.Injective y)
    (hd : ∀ r : Fin m, r.val ≠ 0 → d r ≠ 0)
    (hAP : 1 - A * (∏ j : Fin m, - y j) ≠ 0) :
    (momentMatrix A d y).det ≠ 0 := by
  classical
  let M : Matrix (Fin m) (Fin m) K := momentMatrix A d y
  have hLI : LinearIndependent K M.col := by
    rw [Fintype.linearIndependent_iff]
    intro v hv
    let S : ℕ → K := fun r => ∑ j : Fin m, v j * y j ^ r
    have hrow (r : Fin m) : ∑ j : Fin m, v j * M r j = 0 := by
      have hvfun := congr_fun hv r
      simpa [Matrix.col, M, Pi.smul_apply, smul_eq_mul] using hvfun
    have hmom_pos : ∀ s : Fin m, s.val ≠ 0 → S s.val = 0 := by
      intro s hs0
      have hslt : s.val < m := s.isLt
      have hrowidx_lt : m - s.val < m := by omega
      let r : Fin m := ⟨m - s.val, hrowidx_lt⟩
      have hr0 : r.val ≠ 0 := by
        dsimp [r]
        omega
      have hr := hrow r
      have hs_eq : m - r.val = s.val := by
        dsimp [r]
        omega
      have hsum : (∑ j : Fin m, v j * (d r * y j ^ s.val)) = d r * S s.val := by
        dsimp [S]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      have : d r * S s.val = 0 := by
        have hr' : (∑ j : Fin m, v j * (d r * y j ^ s.val)) = 0 := by
          simpa [M, momentMatrix, r, hr0, hs_eq] using hr
        rwa [hsum] at hr'
      exact (mul_eq_zero.mp this).resolve_left (hd r hr0)
    have hSm : S m = - ((∏ j : Fin m, - y j) * S 0) := by
      simpa [S] using moment_m_eq_neg_const hmpos y v hmom_pos
    have hrow0 : A * S m + S 0 = 0 := by
      let r0 : Fin m := ⟨0, hmpos⟩
      have hr := hrow r0
      have hsum : (∑ j : Fin m, v j * (A * y j ^ m + 1)) = A * S m + S 0 := by
        dsimp [S]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        · apply Finset.sum_congr rfl
          intro j hj
          ring
      have hr' : (∑ j : Fin m, v j * (A * y j ^ m + 1)) = 0 := by
        simpa [M, momentMatrix, r0] using hr
      rwa [hsum] at hr'
    have hS0 : S 0 = 0 := by
      have htmp : (1 - A * (∏ j : Fin m, - y j)) * S 0 = 0 := by
        rw [hSm] at hrow0
        ring_nf at hrow0 ⊢
        exact hrow0
      exact (mul_eq_zero.mp htmp).resolve_left hAP
    have hforall : ∀ i : Fin m, ∑ j : Fin m, v j * y j ^ (i : ℕ) = 0 := by
      intro i
      by_cases hi : i.val = 0
      · simpa [S, hi] using hS0
      · simpa [S] using hmom_pos i hi
    have hvzero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hy hforall
    intro i
    exact congr_fun hvzero i
  have hunitM : IsUnit M := (Matrix.linearIndependent_cols_iff_isUnit).1 hLI
  have hunitdet : IsUnit M.det := hunitM.map Matrix.detMonoidHom
  exact (isUnit_iff_ne_zero.mp hunitdet)



lemma binomial_factor_entry {K : Type*} [Field K] {m : ℕ} (hmpos : 0 < m)
    (x c y : K) (hx : x ^ m = 1) :
    (x - c * y) ^ m =
      ∑ r : Fin m, x ^ r.val *
        (if r.val = 0 then (-c) ^ m * y ^ m + 1
         else (m.choose r.val : K) * (-c) ^ (m - r.val) * y ^ (m - r.val)) := by
  classical
  have hterm (r : ℕ) (hr : r < m) :
      x ^ r * ((-c) * y) ^ (m - r) * (m.choose r : K) =
      x ^ r * ((m.choose r : K) * (-c) ^ (m - r) * y ^ (m - r)) := by
    rw [mul_pow]
    ring
  have hzero : ((-c) * y) ^ m = (-c) ^ m * y ^ m := by rw [mul_pow]
  calc
    (x - c * y) ^ m = (x + (-c) * y) ^ m := by ring_nf
    _ = ∑ r ∈ Finset.range (m+1), x ^ r * (((-c) * y) ^ (m-r)) * (m.choose r : K) := by
      rw [add_pow]
    _ = (∑ r ∈ Finset.range m, x ^ r * (((-c) * y) ^ (m-r)) * (m.choose r : K)) + 1 := by
      rw [Finset.sum_range_succ]
      simp [hx]
    _ = (∑ r ∈ Finset.range m, x ^ r * ((m.choose r : K) * (-c) ^ (m-r) * y ^ (m-r))) + 1 := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      exact hterm r (by simpa using hr)
    _ = ∑ r : Fin m, x ^ r.val *
        (if r.val = 0 then (-c) ^ m * y ^ m + 1
         else (m.choose r.val : K) * (-c) ^ (m - r.val) * y ^ (m - r.val)) := by
      conv_rhs => rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => x ^ r *
        (if r = 0 then (-c) ^ m * y ^ m + 1
         else (m.choose r : K) * (-c) ^ (m - r) * y ^ (m - r))) m]
      have hdelta : (∑ r ∈ Finset.range m, (if r = 0 then (1 : K) else 0)) = 1 := by
        apply Finset.sum_eq_single 0
        · intro r hr h0
          simp [h0]
        · intro h0not
          exact (h0not (by simpa [hmpos] : 0 ∈ Finset.range m)).elim
      rw [← hdelta, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      have hrlt : r < m := by simpa using hr
      by_cases h0 : r = 0
      · subst r
        simp [hmpos, hzero]
      · simp [h0]


lemma powerMatrix_det_ne_zero {K : Type*} [Field K] {m : ℕ} (hmpos : 0 < m)
    (x y : Fin m → K) (c : K)
    (hxinj : Function.Injective x) (hyinj : Function.Injective y)
    (hxpow : ∀ i, x i ^ m = 1)
    (hc : c ≠ 0)
    (hchoose : ∀ r : Fin m, r.val ≠ 0 → ((m.choose r.val : ℕ) : K) ≠ 0)
    (hAP : 1 - (-c) ^ m * (∏ j : Fin m, - y j) ≠ 0) :
    Matrix.det (fun i j : Fin m => (x i - c * y j) ^ m) ≠ 0 := by
  classical
  let A : K := (-c) ^ m
  let d : Fin m → K := fun r => ((m.choose r.val : ℕ) : K) * (-c) ^ (m - r.val)
  let B : Matrix (Fin m) (Fin m) K := momentMatrix A d y
  let V : Matrix (Fin m) (Fin m) K := Matrix.vandermonde x
  let D : Matrix (Fin m) (Fin m) K := fun i j => (x i - c * y j) ^ m
  have hd : ∀ r : Fin m, r.val ≠ 0 → d r ≠ 0 := by
    intro r hr
    dsimp [d]
    exact mul_ne_zero (hchoose r hr) (pow_ne_zero _ (neg_ne_zero.mpr hc))
  have hB : B.det ≠ 0 := by
    simpa [B, A] using momentMatrix_det_ne_zero hmpos A d y hyinj hd hAP
  have hV : V.det ≠ 0 := by
    simpa [V] using (Matrix.det_vandermonde_ne_zero_iff.mpr hxinj)
  have hfactor : D = V * B := by
    ext i j
    dsimp [D, V, B, Matrix.vandermonde, momentMatrix, A, d]
    rw [Matrix.mul_apply]
    rw [binomial_factor_entry hmpos (x i) c (y j) (hxpow i)]
    apply Finset.sum_congr rfl
    intro r hr
    simp [Matrix.of_apply, momentMatrix]
  have hdet : D.det = V.det * B.det := by rw [hfactor, Matrix.det_mul]
  rw [hdet]
  exact mul_ne_zero hV hB



open Matrix Nat Int Finset MulChar
open scoped BigOperators

lemma jacobi_eq_qchar {p : ℕ} [Fact p.Prime] (a : ℤ) :
    jacobiSym a p = quadraticChar (ZMod p) (a : ZMod p) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  rfl

noncomputable def origRatMatrix (p m : ℕ) : Matrix (Fin m) (Fin m) ℚ := fun i j =>
  let Cint : ℤ := m.factorial.cast
  let ii : ℤ := (i.val + 1).cast
  let jj : ℤ := (j.val + 1).cast
  ((jacobiSym (ii * ii - Cint * jj) p : ℤ) : ℚ)

lemma odd_column_pred {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (C : ZMod p) (hCprod : C = ∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p)))
    (hoddm : Odd m) :
    Odd (Fintype.card {j : Fin m // quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1}) := by
  classical
  let g : Fin m → ℤ := fun j => quadraticChar (ZMod p) (((j.val + 1 : ℕ) : ZMod p))
  have hg : ∀ a, g a = 1 ∨ g a = -1 := by
    intro a
    have hne : ((a.val + 1 : ℕ) : ZMod p) ≠ 0 := one_to_m_cast_ne_zero hp a
    exact quadraticChar_dichotomy (F:=ZMod p) hne
  have hprodg : (∏ b, g b) = quadraticChar (ZMod p) C := by
    rw [hCprod]
    simp [g, map_prod]
  have hoddcard : Odd (Fintype.card (Fin m)) := by simpa using hoddm
  have hodd' := odd_count_prod_mul_eq_one_of_pm_one g hg hoddcard
  -- convert predicate `(∏g)*g a=1` to χ(C*a)=1
  let esub : {j : Fin m // (∏ b, g b) * g j = 1} ≃
      {j : Fin m // quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1} :=
    Equiv.subtypeEquivRight (fun j => by
      change (∏ b, g b) * g j = 1 ↔ quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1
      rw [hprodg]
      dsimp [g]
      have hm : quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) =
          quadraticChar (ZMod p) C * quadraticChar (ZMod p) (((j.val + 1 : ℕ) : ZMod p)) := by
        rw [map_mul]
      constructor
      · intro h
        change quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1
        rw [hm]
        exact h
      · intro h
        change quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1 at h
        rw [hm] at h
        exact h)
  have hcard := Fintype.card_congr esub
  rw [← hcard]
  exact hodd'

lemma paley_zero_orig_rat {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (hp2 : ringChar (ZMod p) ≠ 2)
    (hneg1 : quadraticChar (ZMod p) (-1) = -1)
    (hoddm : Odd m)
    (hCprod : ((m.factorial : ℕ) : ZMod p) = ∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p))) :
    Matrix.det (origRatMatrix p m) = 0 := by
  classical
  let C : ZMod p := (m.factorial : ℕ)
  have hC : C ≠ 0 := factorial_cast_zmod_ne_zero hp
  let eR := rowQREquiv hp hp2
  let eC := signedQREquiv hp hp2 hneg1 C hC
  let pred : QR2 (ZMod p) → Prop := fun s =>
    quadraticChar (ZMod p) (C * (((eC.symm s).val + 1 : ℕ) : ZMod p)) = 1
  have hodd_fin : Odd (Fintype.card {j : Fin m // quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1}) := by
    exact odd_column_pred hp C hCprod hoddm
  have hodd_qr : Odd (Fintype.card {s : QR2 (ZMod p) // pred s}) := by
    let esub : {j : Fin m // quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1} ≃ {s : QR2 (ZMod p) // pred s} :=
      Equiv.subtypeEquiv eC (by
        intro j
        dsimp [pred]
        simp [eC])
    have hcard := Fintype.card_congr esub
    rw [← hcard]
    exact hodd_fin
  let A : Matrix (QR2 (ZMod p)) (QR2 (ZMod p)) ℚ := fun r s => ((quadraticChar (ZMod p) ((r:ZMod p) - (s:ZMod p)) : ℤ) : ℚ)
  let B : Matrix (QR2 (ZMod p)) (QR2 (ZMod p)) ℚ := fun r s => ((quadraticChar (ZMod p) ((r:ZMod p) + (s:ZMod p)) : ℤ) : ℚ)
  let MQR : Matrix (QR2 (ZMod p)) (QR2 (ZMod p)) ℚ := fun i j => if pred j then A i j else B i j
  have hpal : Matrix.det MQR = 0 := by
    simpa [MQR, A, B] using (paley_mixed_det_zero (F:=ZMod p) hp2 hneg1 pred hodd_qr)
  have hreindex_zero : Matrix.det (Matrix.reindex eR.symm eC.symm MQR) = 0 := by
    rw [Matrix.det_reindex, hpal, mul_zero]
  have hmat : Matrix.reindex eR.symm eC.symm MQR = origRatMatrix p m := by
    ext i j
    simp only [Matrix.reindex_apply]
    change MQR (eR i) (eC j) = origRatMatrix p m i j
    have hspec := signedQR'_spec hp hneg1 C hC j
    have hrow : ((eR i : QR2 (ZMod p)) : ZMod p) = (((i.val + 1 : ℕ) : ZMod p) ^ 2) := by
      simp [eR, rowQREquiv, rowQRMap]
    have harg : (((((i.val + 1 : ℤ) * (i.val + 1 : ℤ) - (m.factorial : ℤ) * (j.val + 1 : ℤ)) : ℤ) : ZMod p)) =
          (((i.val + 1 : ℕ) : ZMod p) ^ 2 - C * ((j.val + 1 : ℕ) : ZMod p)) := by
      dsimp [C]
      norm_num [sq]
    rcases hspec with ⟨hcol, hchi⟩ | ⟨hcol, hchi⟩
    · have hcolE : ((eC j : QR2 (ZMod p)) : ZMod p) = C * ((j.val + 1 : ℕ) : ZMod p) := by
        simpa [eC, signedQREquiv] using hcol
      have hpred : pred (eC j) := by
        dsimp [pred]
        simpa [eC, signedQREquiv] using hchi
      simp only [MQR, hpred, if_true, A, origRatMatrix]
      rw [jacobi_eq_qchar]
      apply congrArg (fun z : ZMod p => ((quadraticChar (ZMod p) z : ℤ) : ℚ))
      rw [hrow, hcolE]
      exact harg.symm
    · have hcolE : ((eC j : QR2 (ZMod p)) : ZMod p) = -(C * ((j.val + 1 : ℕ) : ZMod p)) := by
        simpa [eC, signedQREquiv] using hcol
      have hpred : ¬ pred (eC j) := by
        intro hp1
        dsimp [pred] at hp1
        have hp1' : quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1 := by
          simpa [eC, signedQREquiv] using hp1
        omega
      simp only [MQR, hpred, if_false, B, origRatMatrix]
      rw [jacobi_eq_qchar]
      apply congrArg (fun z : ZMod p => ((quadraticChar (ZMod p) z : ℤ) : ℚ))
      rw [hrow, hcolE]
      calc
        ((i.val + 1 : ℕ) : ZMod p) ^ 2 + -(C * ((j.val + 1 : ℕ) : ZMod p)) =
            ((i.val + 1 : ℕ) : ZMod p) ^ 2 - C * ((j.val + 1 : ℕ) : ZMod p) := by rw [sub_eq_add_neg]
        _ = (((i.val + 1 : ℤ) * (i.val + 1 : ℤ) - (m.factorial : ℤ) * (j.val + 1 : ℤ) : ℤ) : ZMod p) := harg.symm
  rw [← hmat]
  exact hreindex_zero



open Finset Matrix Nat
open scoped BigOperators

lemma zmod_half_cast_injective {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) :
    Function.Injective (fun j : Fin m => ((j.val + 1 : ℕ) : ZMod p)) := by
  intro i j h
  have hmod : (i.val + 1) ≡ (j.val + 1) [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp h
  have hi : i.val + 1 < p := by rw [hp]; have := i.isLt; omega
  have hj : j.val + 1 < p := by rw [hp]; have := j.isLt; omega
  have hn := hmod.eq_of_lt_of_lt hi hj
  apply Fin.ext; omega

lemma zmod_half_square_pow_m {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) (i : Fin m) :
    ((((i.val + 1 : ℕ) : ZMod p)^2) ^ m) = 1 := by
  have hne : ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := one_to_m_cast_ne_zero hp i
  calc
    ((((i.val + 1 : ℕ) : ZMod p)^2) ^ m) = ((i.val + 1 : ℕ) : ZMod p) ^ (2*m) := by rw [← pow_mul]
    _ = ((i.val + 1 : ℕ) : ZMod p) ^ (p-1) := by congr 1; rw [hp]; omega
    _ = 1 := ZMod.pow_card_sub_one_eq_one hne

lemma zmod_choose_m_ne_zero {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (r : Fin m) (hr : r.val ≠ 0) : ((m.choose r.val : ℕ) : ZMod p) ≠ 0 := by
  intro hzero
  have hdvd : p ∣ m.choose r.val := (ZMod.natCast_eq_zero_iff _ p).mp hzero
  have hpprime : p.Prime := Fact.out
  have hm_lt_p : m < p := by rw [hp]; omega
  have hcop : p.Coprime (m.choose r.val) := hpprime.coprime_choose_of_lt hm_lt_p (Nat.le_of_lt r.isLt)
  have hp_eq1 := hcop.eq_one_of_dvd hdvd
  rw [hp] at hp_eq1
  omega

lemma zmod_m_even_of_p_mod_four_one {p m : ℕ} (hp : p = 2*m+1) (hp4 : p % 4 = 1) : Even m := by
  have hdiv := (Nat.div_add_mod p 4).symm
  rw [hp4] at hdiv
  refine ⟨p / 4, ?_⟩
  rw [hp] at hdiv
  omega

lemma zmod_half_wilson {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) (hmeven : Even m) :
    (((m.factorial : ℕ) : ZMod p)^2) = -1 := by
  let C : ZMod p := (m.factorial : ℕ)
  have hm_le_p : m ≤ p := by rw [hp]; omega
  have hdesc : (((p-1).descFactorial m : ℕ) : ZMod p) = (-1 : ZMod p)^m * C := by
    simpa [C] using (ZMod.cast_descFactorial (p:=p) (n:=m) hm_le_p)
  have hfac_nat : m.factorial * (p-1).descFactorial m = (p-1).factorial := by
    have hle : m ≤ p-1 := by rw [hp]; omega
    have h := Nat.factorial_mul_descFactorial hle
    have hpm : p - 1 - m = m := by rw [hp]; omega
    rwa [hpm] at h
  have hfac : C * (((p-1).descFactorial m : ℕ) : ZMod p) = -1 := by
    rw [← Nat.cast_mul, hfac_nat]
    exact ZMod.wilsons_lemma p
  rw [hdesc] at hfac
  have hpow : (-1 : ZMod p)^m = 1 := by
    rcases hmeven with ⟨k, hk⟩
    rw [hk]
    simp [pow_mul]
  rw [hpow] at hfac
  ring_nf at hfac ⊢
  simpa [C] using hfac

lemma zmod_prod_neg_y_eq_factorial {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) (hmeven : Even m) :
    (∏ j : Fin m, -(((j.val + 1 : ℕ) : ZMod p))) = ((m.factorial : ℕ) : ZMod p) := by
  have hprod_nat : (∏ j : Fin m, (j.val + 1 : ℕ)) = m.factorial := by
    rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => j + 1) m]
    exact Finset.prod_range_add_one_eq_factorial m
  have hprod : (∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p))) = ((m.factorial : ℕ) : ZMod p) := by
    rw [← Finset.prod_natCast, hprod_nat]
  have hnegprod : (∏ j : Fin m, -(((j.val + 1 : ℕ) : ZMod p))) =
      (-1 : ZMod p) ^ Fintype.card (Fin m) * (∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p))) := by
    simpa using (Finset.prod_neg (s := (Finset.univ : Finset (Fin m)))
      (f := fun j : Fin m => (((j.val + 1 : ℕ) : ZMod p))))
  rw [hnegprod, hprod]
  rcases hmeven with ⟨k, hk⟩
  rw [Fintype.card_fin, hk]
  simp [pow_mul]

lemma zmod_hAP_one {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) (hp4 : p % 4 = 1) :
    let C : ZMod p := (m.factorial : ℕ)
    1 - (-C)^m * (∏ j : Fin m, -(((j.val + 1 : ℕ) : ZMod p))) ≠ 0 := by
  intro C hzero
  have hmeven : Even m := zmod_m_even_of_p_mod_four_one hp hp4
  have hC2 : C^2 = -1 := by simpa [C] using zmod_half_wilson hp hmeven
  have hprod : (∏ j : Fin m, -(((j.val + 1 : ℕ) : ZMod p))) = C := by simpa [C] using zmod_prod_neg_y_eq_factorial hp hmeven
  have hT : (-C)^m * (∏ j : Fin m, -(((j.val + 1 : ℕ) : ZMod p))) = 1 := by
    have := sub_eq_zero.mp hzero
    simpa using this.symm
  rw [hprod] at hT
  have hT2 : ((-C)^m * C)^2 = (1 : ZMod p)^2 := by rw [hT]
  have hleft : ((-C)^m * C)^2 = -1 := by
    rcases hmeven with ⟨k, hk⟩
    rw [hk]
    calc
      ((-C)^(k+k) * C)^2 = (((-C)^2)^k * C)^2 := by rw [← two_mul, pow_mul]
      _ = ((C^2)^k * C)^2 := by ring_nf
      _ = ((-1 : ZMod p)^k * C)^2 := by rw [hC2]
      _ = ((-1 : ZMod p)^(2*k) * C^2) := by ring
      _ = -1 := by simp [hC2, pow_mul]
  rw [hleft] at hT2
  have hp2 : p ≠ 2 := by
    intro hp2eq
    rw [hp2eq] at hp4
    norm_num at hp4
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hnegoneeq : (-1 : ZMod p) = 1 := by simpa using hT2
  exact (Ring.neg_one_ne_one_of_char_ne_two hchar) hnegoneeq

lemma zmod_power_det_ne_zero_mod_one {p m : ℕ} [Fact p.Prime]
    (hp : p = 2*m+1) (hp4 : p % 4 = 1) :
    Matrix.det (fun i j : Fin m =>
      ((((i.val + 1 : ℕ) : ZMod p)^2) - ((m.factorial : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^ m) ≠ 0 := by
  let x : Fin m → ZMod p := fun i => (((i.val + 1 : ℕ) : ZMod p)^2)
  let y : Fin m → ZMod p := fun j => ((j.val + 1 : ℕ) : ZMod p)
  let C : ZMod p := (m.factorial : ℕ)
  have hmpos : 0 < m := by
    have hmeven : Even m := zmod_m_even_of_p_mod_four_one hp hp4
    rcases hmeven with ⟨k, hk⟩
    rw [hk]
    by_contra h0
    have hm0 : k + k = 0 := by omega
    have hp_eq1 : p = 1 := by rw [hp, hk, hm0]
    exact (Fact.out : p.Prime).ne_one hp_eq1
  have hc : C ≠ 0 := factorial_cast_zmod_ne_zero hp
  have hxinj : Function.Injective x := zmod_square_half_injective hp
  have hyinj : Function.Injective y := zmod_half_cast_injective hp
  have hxpow : ∀ i, x i ^ m = 1 := zmod_half_square_pow_m hp
  have hchoose : ∀ r : Fin m, r.val ≠ 0 → ((m.choose r.val : ℕ) : ZMod p) ≠ 0 := zmod_choose_m_ne_zero hp
  have hAP := zmod_hAP_one hp hp4
  simpa [x, y, C] using powerMatrix_det_ne_zero hmpos x y C hxinj hyinj hxpow hc hchoose hAP



open Matrix Nat Int Finset MulChar
open scoped BigOperators



noncomputable def origIntMatrix (p m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun i j =>
  let Cint : ℤ := m.factorial.cast
  let ii : ℤ := (i.val + 1).cast
  let jj : ℤ := (j.val + 1).cast
  jacobiSym (ii * ii - Cint * jj) p

lemma zmod_prod_y_eq_factorial {p m : ℕ} :
    (∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p))) = ((m.factorial : ℕ) : ZMod p) := by
  have hprod_nat : (∏ j : Fin m, (j.val + 1 : ℕ)) = m.factorial := by
    rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => j + 1) m]
    exact Finset.prod_range_add_one_eq_factorial m
  rw [← Finset.prod_natCast, hprod_nat]

lemma zmod_ringChar_ne_two_of_prime_mod_four_eq_three {p : ℕ} (hp4 : p % 4 = 3) :
    ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  intro h
  rw [h] at hp4
  norm_num at hp4

lemma zmod_quadraticChar_neg_one_of_prime_mod_four_eq_three {p : ℕ} [Fact p.Prime]
    (hp4 : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 := by
  have hF : ringChar (ZMod p) ≠ 2 := zmod_ringChar_ne_two_of_prime_mod_four_eq_three hp4
  rw [quadraticChar_neg_one hF, ZMod.card]
  exact ZMod.χ₄_nat_three_mod_four hp4

lemma m_odd_of_p_mod_four_three {p m : ℕ} (hp : p = 2*m+1) (hp4 : p % 4 = 3) : Odd m := by
  have hdiv := (Nat.div_add_mod p 4).symm
  rw [hp4] at hdiv
  refine ⟨p / 4, ?_⟩
  rw [hp] at hdiv
  omega

lemma p_eq_two_mul_half_add_one_of_prime_ne_two {p : ℕ} (hpprime : p.Prime) (hpne2 : p ≠ 2) :
    p = 2 * ((p - 1) / 2) + 1 := by
  have hodd : Odd p := hpprime.odd_of_ne_two hpne2
  rcases hodd with ⟨k, hk⟩
  rw [hk]
  have : (k + k + 1 - 1) / 2 = k := by omega
  omega

lemma cast_origInt_to_rat (p m : ℕ) :
    (((origIntMatrix p m).det : ℤ) : ℚ) = (origRatMatrix p m).det := by
  rw [Int.cast_det]
  rfl

lemma cast_origInt_to_zmod_power {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) :
    Matrix.det (((Int.castRingHom (ZMod p)).mapMatrix (origIntMatrix p m))) =
    Matrix.det (fun i j : Fin m =>
      ((((i.val + 1 : ℕ) : ZMod p)^2) - ((m.factorial : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^ m) := by
  congr 1
  ext i j
  dsimp [origIntMatrix]
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hpdiv : p / 2 = m := by rw [hp]; omega
  have he := legendreSym.eq_pow p (((i.val + 1 : ℤ) * (i.val + 1 : ℤ) - (m.factorial : ℤ) * (j.val + 1 : ℤ)))
  rw [hpdiv] at he
  rw [he]
  congr 1
  norm_num [sq]

lemma nth_prime_of_ge_one_ne_two {k : ℕ} (hk : 1 ≤ k) : Nat.nth Nat.Prime k ≠ 2 := by
  have hge : 3 ≤ Nat.nth Nat.Prime k := by
    calc
      3 = Nat.nth Nat.Prime 1 := by norm_num [Nat.nth_prime_one_eq_three]
      _ ≤ Nat.nth Nat.Prime k := (Nat.nth_le_nth Nat.infinite_setOf_prime).2 hk
  exact Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hge)

lemma nth_prime_n_sub_one_ne_two {n : ℕ} (hn : 2 ≤ n) : Nat.nth Nat.Prime (n - 1) ≠ 2 := by
  apply nth_prime_of_ge_one_ne_two
  omega

lemma A226163_eq_origInt (n : ℕ) (hn : 2 ≤ n) :
    A226163 n = (origIntMatrix (Nat.nth Nat.Prime (n-1)) ((Nat.nth Nat.Prime (n-1)-1)/2)).det := by
  unfold A226163
  have hnot : ¬ n < 2 := by omega
  simp [hnot]
  unfold origIntMatrix
  rfl

lemma oeis_zero_of_mod_three (n : ℕ) (hn : 2 ≤ n)
    (hp4 : Nat.nth Nat.Prime (n-1) % 4 = 3) : A226163 n = 0 := by
  let p := Nat.nth Nat.Prime (n-1)
  let m := (p-1)/2
  have hpprime : p.Prime := Nat.prime_nth_prime _
  have hpne2 : p ≠ 2 := nth_prime_n_sub_one_ne_two hn
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hp_eq : p = 2*m+1 := by
    dsimp [m]
    exact p_eq_two_mul_half_add_one_of_prime_ne_two hpprime hpne2
  have hp2 : ringChar (ZMod p) ≠ 2 := zmod_ringChar_ne_two_of_prime_mod_four_eq_three hp4
  have hneg1 : quadraticChar (ZMod p) (-1) = -1 := zmod_quadraticChar_neg_one_of_prime_mod_four_eq_three hp4
  have hoddm : Odd m := m_odd_of_p_mod_four_three hp_eq hp4
  have hCprod : ((m.factorial : ℕ) : ZMod p) = ∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p)) := by
    exact (zmod_prod_y_eq_factorial (p:=p) (m:=m)).symm
  have hrat : (origRatMatrix p m).det = 0 := paley_zero_orig_rat hp_eq hp2 hneg1 hoddm hCprod
  have hA := A226163_eq_origInt n hn
  rw [hA]
  have hcastzero : (((origIntMatrix p m).det : ℤ) : ℚ) = 0 := by
    rw [cast_origInt_to_rat]
    exact hrat
  exact Int.cast_eq_zero.mp hcastzero

lemma oeis_ne_zero_of_mod_one (n : ℕ) (hn : 2 ≤ n)
    (hp4 : Nat.nth Nat.Prime (n-1) % 4 = 1) : A226163 n ≠ 0 := by
  let p := Nat.nth Nat.Prime (n-1)
  let m := (p-1)/2
  have hpprime : p.Prime := Nat.prime_nth_prime _
  have hpne2 : p ≠ 2 := by
    intro h2
    change p % 4 = 1 at hp4
    rw [h2] at hp4
    norm_num at hp4
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hp_eq : p = 2*m+1 := by
    dsimp [m]
    exact p_eq_two_mul_half_add_one_of_prime_ne_two hpprime hpne2
  have hdet_ne := zmod_power_det_ne_zero_mod_one hp_eq hp4
  intro hA0
  have hA := A226163_eq_origInt n hn
  rw [hA] at hA0
  have hdet0 : (origIntMatrix p m).det = 0 := by
    simpa [p, m] using hA0
  have hmap : Matrix.det (((Int.castRingHom (ZMod p)).mapMatrix (origIntMatrix p m))) = 0 := by
    rw [← RingHom.map_det]
    simp [hdet0]
  rw [cast_origInt_to_zmod_power hp_eq] at hmap
  exact hdet_ne hmap

lemma prime_mod_four_eq_one_or_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
  have hmod2 : p % 4 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4), hodd]
  have hlt : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : p % 4 <;> simp_all

lemma nth_prime_n_sub_one_mod_four_eq_one_or_three {n : ℕ} (hn : 2 ≤ n) :
    Nat.nth Nat.Prime (n - 1) % 4 = 1 ∨ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  exact prime_mod_four_eq_one_or_three (Nat.prime_nth_prime _) (nth_prime_n_sub_one_ne_two hn)

lemma oeis_conjecture_dev (n : ℕ) (hn : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  constructor
  · intro hzero
    rcases nth_prime_n_sub_one_mod_four_eq_one_or_three hn with h1 | h3
    · exfalso
      exact oeis_ne_zero_of_mod_one n hn h1 hzero
    · exact h3
  · intro h3
    exact oeis_zero_of_mod_three n hn h3


theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  exact oeis_conjecture_dev n h_n
