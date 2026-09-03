import FormalConjecturesUtil

/-!
# Character-energy estimates for a finite analogue of Erdős Problem 66

These finite-field estimates do not establish the conjecture over natural numbers.
-/

namespace Erdos66CharacterEnergy
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma quadraticChar_product_base (hF : ringChar F ≠ 2) :
    (∑ x : F, quadraticChar F x * quadraticChar F (x - 1)) = -1 := by
  have hJ := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
  rw [(quadraticChar_isQuadratic F).inv] at hJ
  calc
    (∑ x : F, quadraticChar F x * quadraticChar F (x - 1)) =
        quadraticChar F (-1) * jacobiSum (quadraticChar F) (quadraticChar F) := by
      unfold jacobiSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have he : x - 1 = (-1) * (1 - x) := by ring
      rw [he, map_mul]
      ring
    _ = -1 := by
      rw [hJ]
      have hh := quadraticChar_sq_one (F := F) (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
      nlinarith

lemma quadraticChar_correlation (hF : ringChar F ≠ 2) (a b : F) :
    (∑ x : F, quadraticChar F (x - a) * quadraticChar F (x - b)) =
      if a = b then (Fintype.card F : ℤ) - 1 else -1 := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    calc
      (∑ x : F, quadraticChar F (x - a) * quadraticChar F (x - a)) =
          ∑ x : F, (1 - if x = a then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxa : x = a
        · simp [hxa]
        · rw [if_neg hxa, sub_zero, ← pow_two]
          exact quadraticChar_sq_one (sub_ne_zero.mpr hxa)
      _ = (Fintype.card F : ℤ) - 1 := by simp [Finset.sum_sub_distrib]
  · rw [if_neg hab]
    let e : F ≃ F := (Equiv.mulLeft₀ (b - a) (sub_ne_zero.mpr (Ne.symm hab))).trans (Equiv.addLeft a)
    rw [← e.sum_comp]
    calc
      (∑ x : F, quadraticChar F (e x - a) * quadraticChar F (e x - b)) =
          ∑ x : F, quadraticChar F x * quadraticChar F (x - 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← map_mul, ← map_mul]
        have he : (e x - a) * (e x - b) = (b - a) ^ 2 * (x * (x - 1)) := by
          dsimp [e]
          ring
        rw [he, map_mul, quadraticChar_sq_one' (sub_ne_zero.mpr (Ne.symm hab)), one_mul]
      _ = -1 := quadraticChar_product_base hF

noncomputable def shiftSum {ι : Type*} (S : Finset ι) (b : ι → F) (x : F) : ℤ :=
  ∑ i ∈ S, quadraticChar F (x - b i)

lemma shiftSum_energy_identity {ι : Type*} (hF : ringChar F ≠ 2)
    (S : Finset ι) (b : ι → F) :
    (∑ x : F, (shiftSum S b x) ^ 2) =
      (Fintype.card F : ℤ) * (∑ i ∈ S, ∑ j ∈ S, if b i = b j then (1 : ℤ) else 0) -
        (S.card : ℤ) ^ 2 := by
  classical
  have he (x : F) : (shiftSum S b x) ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, quadraticChar F (x - b i) * quadraticChar F (x - b j) := by
    unfold shiftSum
    rw [pow_two]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hinner (i : ι) :
      (∑ x : F, ∑ j ∈ S, quadraticChar F (x - b i) * quadraticChar F (x - b j)) =
        ∑ j ∈ S, ((Fintype.card F : ℤ) * (if b i = b j then 1 else 0) - 1) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [quadraticChar_correlation hF]
    split_ifs <;> ring
  simp_rw [hinner]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  ring

lemma shiftSum_energy_le_sq {ι : Type*} (hF : ringChar F ≠ 2)
    (S : Finset ι) (b : ι → F)
    (hfiber : ∀ i ∈ S, (S.filter (fun j ↦ b i = b j)).card ≤ 2) :
    (∑ x : F, (shiftSum S b x) ^ 2) ≤ (Fintype.card F : ℤ) ^ 2 := by
  classical
  have hf (i : ι) (hi : i ∈ S) :
      (∑ j ∈ S, if b i = b j then (1 : ℤ) else 0) ≤ 2 := by
    have he : (∑ j ∈ S, if b i = b j then (1 : ℤ) else 0) =
        ((S.filter (fun j ↦ b i = b j)).card : ℤ) := by
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [he]
    exact_mod_cast hfiber i hi
  have hb : (∑ i ∈ S, ∑ j ∈ S, if b i = b j then (1 : ℤ) else 0) ≤ 2 * S.card := by
    calc
      _ ≤ ∑ _i ∈ S, (2 : ℤ) := Finset.sum_le_sum hf
      _ = _ := by simp [mul_comm]
  rw [shiftSum_energy_identity hF]
  have hmul := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Fintype.card F))
  nlinarith [sq_nonneg ((Fintype.card F : ℤ) - S.card)]

noncomputable def collisionShift (ν x : F) : ℤ :=
  shiftSum (Finset.univ \ {0, 1}) (fun r ↦ ν / (r * (1 - r))) x

lemma collisionShift_energy_le (hF : ringChar F ≠ 2) (ν : F) (hν : ν ≠ 0) :
    (∑ x : F, (collisionShift ν x) ^ 2) ≤ (Fintype.card F : ℤ) ^ 2 := by
  classical
  apply shiftSum_energy_le_sq hF
  intro i hi
  have hi' : i ≠ 0 ∧ i ≠ 1 := by
    simpa only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] using hi
  have hi0 : i * (1 - i) ≠ 0 := mul_ne_zero hi'.1 (sub_ne_zero.mpr hi'.2.symm)
  apply le_trans (Finset.card_le_card (t := {i, 1 - i}) ?_) Finset.card_le_two
  intro j hj
  obtain ⟨hj, he⟩ := Finset.mem_filter.mp hj
  have hj' : j ≠ 0 ∧ j ≠ 1 := by
    simpa only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] using hj
  have hj0 : j * (1 - j) ≠ 0 := mul_ne_zero hj'.1 (sub_ne_zero.mpr hj'.2.symm)
  have hh : i * (1 - i) = j * (1 - j) :=
    (mul_left_cancel₀ hν ((div_eq_div_iff hi0 hj0).mp he)).symm
  have hp : (j - i) * (j - (1 - i)) = 0 := by linear_combination hh
  simpa only [Finset.mem_insert, Finset.mem_singleton, sub_eq_zero] using mul_eq_zero.mp hp

lemma square_fiber_card_le_two (v : F) :
    (Finset.univ.filter (fun x : F ↦ x ^ 2 = v)).card ≤ 2 := by
  by_contra h
  have h' : 2 < (Finset.univ.filter (fun x : F ↦ x ^ 2 = v)).card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp h'
  have hba : b = -a := (sq_eq_sq_iff_eq_or_eq_neg.mp
    ((Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp ha).2.symm)).resolve_left hab.symm
  have hca : c = -a := (sq_eq_sq_iff_eq_or_eq_neg.mp
    ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp ha).2.symm)).resolve_left hac.symm
  exact hbc (hba.trans hca.symm)

lemma sum_sq_comp_square_le_two (g : F → ℤ) :
    (∑ x : F, (g (x ^ 2)) ^ 2) ≤ 2 * ∑ v : F, (g v) ^ 2 := by
  rw [← Finset.sum_fiberwise (Finset.univ : Finset F) (fun x ↦ x ^ 2) (fun x ↦ (g (x ^ 2)) ^ 2)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  calc
    (∑ x ∈ Finset.univ.filter (fun x : F ↦ x ^ 2 = v), (g (x ^ 2)) ^ 2) =
        ∑ _x ∈ Finset.univ.filter (fun x : F ↦ x ^ 2 = v), (g v) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = ((Finset.univ.filter (fun x : F ↦ x ^ 2 = v)).card : ℤ) * (g v) ^ 2 := by simp
    _ ≤ 2 * (g v) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast square_fiber_card_le_two v

/-- Once the hyperbola transform is established, its energy estimate is elementary. -/
lemma energy_le_three_sq_of_transform (hF : ringChar F ≠ 2) (ν : F) (hν : ν ≠ 0)
    (C : F → ℤ) (hC0 : C 0 = Fintype.card F)
    (hC : ∀ x : F, x ≠ 0 → C x = collisionShift ν (x ^ 2)) :
    (∑ x : F, (C x) ^ 2) ≤ 3 * (Fintype.card F : ℤ) ^ 2 := by
  have hoff : (∑ x ∈ (Finset.univ : Finset F).erase 0, (C x) ^ 2) ≤
      2 * (Fintype.card F : ℤ) ^ 2 := by
    calc
      _ = ∑ x ∈ (Finset.univ : Finset F).erase 0, (collisionShift ν (x ^ 2)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hC x (Finset.mem_erase.mp hx).1]
      _ ≤ ∑ x : F, (collisionShift ν (x ^ 2)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ ↦ sq_nonneg _)
      _ ≤ 2 * ∑ x : F, (collisionShift ν x) ^ 2 := sum_sq_comp_square_le_two _
      _ ≤ 2 * (Fintype.card F : ℤ) ^ 2 := by
        exact mul_le_mul_of_nonneg_left (collisionShift_energy_le hF ν hν) (by norm_num)
  have hs := Finset.sum_erase_add (Finset.univ : Finset F) (fun x ↦ (C x) ^ 2) (Finset.mem_univ 0)
  dsimp only at hs
  rw [hC0] at hs
  omega

noncomputable def hyperbolaMid (ν : F) (u : Fˣ) : F := ((u : F) + ν / u) / 2

noncomputable def rootMidEquiv (hF : ringChar F ≠ 2) (ν x : F) (hν : ν ≠ 0) :
    {y : F // y ^ 2 = x ^ 2 - ν} ≃ {u : Fˣ // hyperbolaMid ν u = x} where
  toFun y := by
    have hn : (x - y.val) * (x + y.val) = ν := by linear_combination -y.property
    have h0 : x - y.val ≠ 0 := by
      intro h
      apply hν
      simpa only [h, zero_mul] using hn.symm
    refine ⟨Units.mk0 (x - y.val) h0, ?_⟩
    change ((x - y.val) + ν / (x - y.val)) / 2 = x
    have hquot : ν / (x - y.val) = x + y.val := by
      apply (div_eq_iff h0).mpr
      linear_combination -hn
    rw [hquot]
    field_simp [Ring.two_ne_zero hF]
    ring
  invFun u := by
    refine ⟨x - (u.val : F), ?_⟩
    have hh := u.property
    change ((u.val : F) + ν / u.val) / 2 = x at hh
    have h0 := u.val.ne_zero
    field_simp [Ring.two_ne_zero hF] at hh
    linear_combination hh
  left_inv y := by
    apply Subtype.ext
    change x - (x - y.val) = y.val
    ring
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    change x - (x - (u.val : F)) = (u.val : F)
    ring

noncomputable def fiberCount {X : Type*} [Fintype X] (f : X → F) (x : F) : ℕ :=
  Fintype.card {u : X // f u = x}

omit [Field F] in
lemma fiberCount_sum {X : Type*} [Fintype X] (f : X → F) :
    ∑ x : F, fiberCount f x = Fintype.card X := by
  classical
  simpa only [Fintype.card_sigma, fiberCount] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)

noncomputable def fiberPairEquiv {X : Type*} (f : X → F) (w : F) :
    (Σ x : F, {a : X // f a = x} × {b : X // f b = w - x}) ≃
      {p : X × X // f p.1 + f p.2 = w} where
  toFun v := ⟨(v.2.1.val, v.2.2.val), by rw [v.2.1.property, v.2.2.property]; ring⟩
  invFun p := ⟨f p.val.1, ⟨p.val.1, rfl⟩, ⟨p.val.2, by linear_combination p.property⟩⟩
  left_inv v := by
    obtain ⟨x, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩ := v
    subst x
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

lemma fiberCount_convolution {X : Type*} [Fintype X] (f : X → F) (w : F) :
    (∑ x : F, fiberCount f x * fiberCount f (w - x)) =
      Fintype.card {p : X × X // f p.1 + f p.2 = w} := by
  classical
  simpa only [Fintype.card_sigma, Fintype.card_prod, fiberCount] using
    Fintype.card_congr (fiberPairEquiv f w)

lemma hyperbola_fiber_count (hF : ringChar F ≠ 2) (ν x : F) (hν : ν ≠ 0) :
    (fiberCount (hyperbolaMid ν) x : ℤ) = 1 + quadraticChar F (x ^ 2 - ν) := by
  change (Fintype.card {u : Fˣ // hyperbolaMid ν u = x} : ℤ) = _
  rw [← Fintype.card_congr (rootMidEquiv hF ν x hν)]
  simpa only [Set.toFinset_card, add_comm] using quadraticChar_card_sqrts hF (x ^ 2 - ν)

lemma quadratic_sequence_sum (hF : ringChar F ≠ 2) (ν : F) (hν : ν ≠ 0) :
    (∑ x : F, quadraticChar F (x ^ 2 - ν)) = -1 := by
  have hh : (∑ x : F, (fiberCount (hyperbolaMid ν) x : ℤ)) = (Fintype.card Fˣ : ℤ) := by
    exact_mod_cast fiberCount_sum (hyperbolaMid ν)
  simp_rw [hyperbola_fiber_count hF ν _ hν] at hh
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_units] at hh
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  rw [Nat.cast_sub hq, Nat.cast_one] at hh
  omega

noncomputable def quadraticSequenceConv (ν w : F) : ℤ :=
  ∑ x : F, quadraticChar F (x ^ 2 - ν) * quadraticChar F ((w - x) ^ 2 - ν)

lemma hyperbola_pair_count (hF : ringChar F ≠ 2) (ν w : F) (hν : ν ≠ 0) :
    (Fintype.card {p : Fˣ × Fˣ // hyperbolaMid ν p.1 + hyperbolaMid ν p.2 = w} : ℤ) =
      (Fintype.card F : ℤ) - 2 + quadraticSequenceConv ν w := by
  rw [← fiberCount_convolution (hyperbolaMid ν) w]
  push_cast
  simp_rw [hyperbola_fiber_count hF ν _ hν]
  have he (x : F) : (1 + quadraticChar F (x ^ 2 - ν)) *
      (1 + quadraticChar F ((w - x) ^ 2 - ν)) =
      1 + quadraticChar F (x ^ 2 - ν) + quadraticChar F ((w - x) ^ 2 - ν) +
        quadraticChar F (x ^ 2 - ν) * quadraticChar F ((w - x) ^ 2 - ν) := by ring
  simp_rw [he, Finset.sum_add_distrib]
  have hs : (∑ x : F, quadraticChar F ((w - x) ^ 2 - ν)) = -1 := by
    calc
      _ = ∑ x : F, quadraticChar F (x ^ 2 - ν) := by
        simpa only [Equiv.subLeft_apply] using
          (Equiv.subLeft w).sum_comp (fun x ↦ quadraticChar F (x ^ 2 - ν))
      _ = -1 := quadratic_sequence_sum hF ν hν
  rw [hs, quadratic_sequence_sum hF ν hν]
  simp [quadraticSequenceConv]
  ring

omit [Fintype F] [DecidableEq F] in
lemma hyperbolaMid_sum_iff (hF : ringChar F ≠ 2) (ν w : F) (a b : Fˣ) :
    hyperbolaMid ν a + hyperbolaMid ν b = w ↔
      ((a : F) + b) * ((a : F) * b + ν) = 2 * w * a * b := by
  have h2 := Ring.two_ne_zero hF
  have ha := a.ne_zero
  have hb := b.ne_zero
  have he : ((a : F) + b) * ((a : F) * b + ν) - 2 * w * a * b =
      (2 * (a : F) * b) * (hyperbolaMid ν a + hyperbolaMid ν b - w) := by
    unfold hyperbolaMid
    field_simp
    ring
  conv_rhs => rw [← sub_eq_zero, he, mul_eq_zero]
  simp only [mul_ne_zero (mul_ne_zero h2 ha) hb, false_or, sub_eq_zero]

omit [Fintype F] [DecidableEq F] in
lemma fiber_pair_product (ν w r z : F) (hr : r ≠ 0) (hr1 : r ≠ 1)
    (hz : z ^ 2 = w ^ 2 - ν / (r * (1 - r))) :
    (r * (w + z)) * (r * (w - z)) = ν * r / (1 - r) := by
  have hr1' : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.symm
  calc
    (r * (w + z)) * (r * (w - z)) = r ^ 2 * (w ^ 2 - z ^ 2) := by ring
    _ = r ^ 2 * (ν / (r * (1 - r))) := by rw [hz]; ring
    _ = ν * r / (1 - r) := by field_simp

omit [Fintype F] [DecidableEq F] in
lemma pair_fiber_spec (ν w a b : F) (h2 : (2 : F) ≠ 0)
    (hν : ν ≠ 0) (hw : w ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hP : (a + b) * (a * b + ν) = 2 * w * a * b) :
    a + b ≠ 0 ∧ (a + b) / (2 * w) ≠ 0 ∧ (a + b) / (2 * w) ≠ 1 ∧
      (w * (a - b) / (a + b)) ^ 2 =
        w ^ 2 - ν / (((a + b) / (2 * w)) * (1 - (a + b) / (2 * w))) := by
  have hs : a + b ≠ 0 := by
    intro h
    have hh : 2 * w * a * b = 0 := by simpa only [h, zero_mul] using hP.symm
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hw) ha) hb) hh
  have hs2 : a + b ≠ 2 * w := by
    intro h
    rw [h] at hP
    have hh : (2 * w) * ν = 0 := by linear_combination hP
    exact (mul_ne_zero (mul_ne_zero h2 hw) hν) hh
  have hr0 : (a + b) / (2 * w) ≠ 0 := div_ne_zero hs (mul_ne_zero h2 hw)
  have hr1 : (a + b) / (2 * w) ≠ 1 := by
    intro h
    apply hs2
    simpa only [one_mul] using (div_eq_iff (mul_ne_zero h2 hw)).mp h
  refine ⟨hs, hr0, hr1, ?_⟩
  have hden : ((a + b) / (2 * w)) * (1 - (a + b) / (2 * w)) ≠ 0 :=
    mul_ne_zero hr0 (sub_ne_zero.mpr hr1.symm)
  have hprod : a * b * (2 * w - (a + b)) = (a + b) * ν := by
    linear_combination -hP
  have hform : (w ^ 2 - (w * (a - b) / (a + b)) ^ 2) *
      (((a + b) / (2 * w)) * (1 - (a + b) / (2 * w))) = ν := by
    calc
      _ = a * b * (2 * w - (a + b)) / (a + b) := by field_simp; ring
      _ = ν := (div_eq_iff hs).mpr (by linear_combination hprod)
  have hh := (eq_div_iff hden).mpr hform
  linear_combination -hh

abbrev HyperbolaFiber (ν w : F) :=
  Σ r : {r : F // r ≠ 0 ∧ r ≠ 1}, {z : F // z ^ 2 = w ^ 2 - ν / (r.val * (1 - r.val))}

omit [Fintype F] [DecidableEq F] in
lemma hyperbolaFiber_ext (ν w : F) {u v : HyperbolaFiber ν w}
    (hr : u.1.val = v.1.val) (hz : u.2.val = v.2.val) : u = v := by
  obtain ⟨⟨r, hr'⟩, ⟨z, hz'⟩⟩ := u
  obtain ⟨⟨s, hs'⟩, ⟨y, hy'⟩⟩ := v
  dsimp at hr hz
  subst s
  subst y
  rfl

noncomputable def hyperbolaFiberPairEquiv (hF : ringChar F ≠ 2) (ν w : F)
    (hν : ν ≠ 0) (hw : w ≠ 0) :
    HyperbolaFiber ν w ≃
      {p : Fˣ × Fˣ // hyperbolaMid ν p.1 + hyperbolaMid ν p.2 = w} where
  toFun v := by
    let r := v.1.val
    let z := v.2.val
    have hr0 : r ≠ 0 := v.1.property.1
    have hr1 : r ≠ 1 := v.1.property.2
    have hprod := fiber_pair_product ν w r z hr0 hr1 v.2.property
    have hprod0 : (r * (w + z)) * (r * (w - z)) ≠ 0 := by
      rw [hprod]
      exact div_ne_zero (mul_ne_zero hν hr0) (sub_ne_zero.mpr hr1.symm)
    have ha : r * (w + z) ≠ 0 := left_ne_zero_of_mul hprod0
    have hb : r * (w - z) ≠ 0 := right_ne_zero_of_mul hprod0
    refine ⟨(Units.mk0 (r * (w + z)) ha, Units.mk0 (r * (w - z)) hb), ?_⟩
    apply (hyperbolaMid_sum_iff hF ν w _ _).mpr
    change (r * (w + z) + r * (w - z)) * ((r * (w + z)) * (r * (w - z)) + ν) =
      2 * w * (r * (w + z)) * (r * (w - z))
    have hsum : r * (w + z) + r * (w - z) = 2 * w * r := by ring
    rw [hsum, hprod]
    conv_rhs => rw [mul_assoc, hprod]
    have hr1' := sub_ne_zero.mpr hr1.symm
    field_simp
    ring
  invFun p := by
    have hp := (hyperbolaMid_sum_iff hF ν w p.val.1 p.val.2).mp p.property
    have hh := pair_fiber_spec ν w (p.val.1 : F) (p.val.2 : F) (Ring.two_ne_zero hF)
      hν hw p.val.1.ne_zero p.val.2.ne_zero hp
    exact ⟨⟨((p.val.1 : F) + p.val.2) / (2 * w), hh.2.1, hh.2.2.1⟩,
      ⟨w * ((p.val.1 : F) - p.val.2) / ((p.val.1 : F) + p.val.2), hh.2.2.2⟩⟩
  left_inv v := by
    have h2 := Ring.two_ne_zero hF
    have hr0 := v.1.property.1
    have hsum : v.1.val * (w + v.2.val) + v.1.val * (w - v.2.val) = 2 * w * v.1.val := by ring
    apply hyperbolaFiber_ext ν w
    · change (v.1.val * (w + v.2.val) + v.1.val * (w - v.2.val)) / (2 * w) = v.1.val
      rw [hsum]
      field_simp
    · change w * (v.1.val * (w + v.2.val) - v.1.val * (w - v.2.val)) /
        (v.1.val * (w + v.2.val) + v.1.val * (w - v.2.val)) = v.2.val
      rw [hsum]
      field_simp
      ring
  right_inv p := by
    have h2 := Ring.two_ne_zero hF
    have hp := (hyperbolaMid_sum_iff hF ν w p.val.1 p.val.2).mp p.property
    have hs := (pair_fiber_spec ν w (p.val.1 : F) (p.val.2 : F) h2 hν hw
      p.val.1.ne_zero p.val.2.ne_zero hp).1
    apply Subtype.ext
    apply Prod.ext <;> apply Units.ext
    · change (((p.val.1 : F) + p.val.2) / (2 * w)) *
        (w + w * ((p.val.1 : F) - p.val.2) / ((p.val.1 : F) + p.val.2)) = (p.val.1 : F)
      field_simp
      ring
    · change (((p.val.1 : F) + p.val.2) / (2 * w)) *
        (w - w * ((p.val.1 : F) - p.val.2) / ((p.val.1 : F) + p.val.2)) = (p.val.2 : F)
      field_simp
      ring

lemma hyperbolaFiber_card (hF : ringChar F ≠ 2) (ν w : F) :
    (Fintype.card (HyperbolaFiber ν w) : ℤ) =
      (Fintype.card F : ℤ) - 2 + collisionShift ν (w ^ 2) := by
  classical
  let S : Finset F := Finset.univ \ {0, 1}
  have hmem (r : F) : r ∈ S ↔ r ≠ 0 ∧ r ≠ 1 := by
    simp only [S, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or]
  have hsum : (∑ _r ∈ S, (1 : ℤ)) = (Fintype.card F : ℤ) - 2 := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
    simp
  change (Fintype.card (Σ r : {r : F // r ≠ 0 ∧ r ≠ 1},
    {z : F // z ^ 2 = w ^ 2 - ν / (r.val * (1 - r.val))}) : ℤ) = _
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    (∑ r : {r : F // r ≠ 0 ∧ r ≠ 1},
        (Fintype.card {z : F // z ^ 2 = w ^ 2 - ν / (r.val * (1 - r.val))} : ℤ)) =
        ∑ r : {r : F // r ≠ 0 ∧ r ≠ 1},
          (1 + quadraticChar F (w ^ 2 - ν / (r.val * (1 - r.val)))) := by
      apply Finset.sum_congr rfl
      intro r hr
      simpa only [Set.toFinset_card, add_comm] using
        quadraticChar_card_sqrts hF (w ^ 2 - ν / (r.val * (1 - r.val)))
    _ = ∑ r ∈ S, (1 + quadraticChar F (w ^ 2 - ν / (r * (1 - r)))) :=
      (Finset.sum_subtype S hmem (fun r ↦ (1 : ℤ) + quadraticChar F (w ^ 2 - ν / (r * (1 - r))))).symm
    _ = (Fintype.card F : ℤ) - 2 + collisionShift ν (w ^ 2) := by
      rw [Finset.sum_add_distrib, hsum]
      rfl

/-- An elementary hyperbola transform for the signed self-convolution. -/
lemma quadraticSequenceConv_transform (hF : ringChar F ≠ 2) (ν w : F)
    (hν : ν ≠ 0) (hw : w ≠ 0) :
    quadraticSequenceConv ν w = collisionShift ν (w ^ 2) := by
  have hc : (Fintype.card (HyperbolaFiber ν w) : ℤ) =
      (Fintype.card {p : Fˣ × Fˣ // hyperbolaMid ν p.1 + hyperbolaMid ν p.2 = w} : ℤ) := by
    exact_mod_cast Fintype.card_congr (hyperbolaFiberPairEquiv hF ν w hν hw)
  rw [hyperbolaFiber_card hF ν w, hyperbola_pair_count hF ν w hν] at hc
  omega

lemma quadraticSequenceConv_zero (ν : F) (hν : ¬IsSquare ν) :
    quadraticSequenceConv ν 0 = Fintype.card F := by
  unfold quadraticSequenceConv
  simp only [zero_sub, neg_sq]
  calc
    (∑ x : F, quadraticChar F (x ^ 2 - ν) * quadraticChar F (x ^ 2 - ν)) =
        ∑ _x : F, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← pow_two]
      apply quadraticChar_sq_one
      intro hh
      exact hν ((sub_eq_zero.mp hh) ▸ IsSquare.sq x)
    _ = (Fintype.card F : ℤ) := by simp

/-- The explicit nonsquare-shift pattern has self-convolution energy at most `3q²`. -/
lemma quadraticSequenceConv_energy (hF : ringChar F ≠ 2) (ν : F) (hν : ¬IsSquare ν) :
    (∑ w : F, (quadraticSequenceConv ν w) ^ 2) ≤ 3 * (Fintype.card F : ℤ) ^ 2 := by
  have hν0 : ν ≠ 0 := fun h ↦ hν (h ▸ IsSquare.zero)
  exact energy_le_three_sq_of_transform hF ν hν0 (quadraticSequenceConv ν)
    (quadraticSequenceConv_zero ν hν)
    (fun w hw ↦ quadraticSequenceConv_transform hF ν w hν0 hw)

lemma quadraticSequenceConv_l1_sq (hF : ringChar F ≠ 2) (ν : F) (hν : ¬IsSquare ν) :
    (∑ w : F, |quadraticSequenceConv ν w|) ^ 2 ≤ 3 * (Fintype.card F : ℤ) ^ 3 := by
  calc
    (∑ w : F, |quadraticSequenceConv ν w|) ^ 2 ≤
        (Fintype.card F : ℤ) * ∑ w : F, (quadraticSequenceConv ν w) ^ 2 := by
      simpa only [Finset.card_univ, sq_abs] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun w : F ↦ |quadraticSequenceConv ν w|))
    _ ≤ (Fintype.card F : ℤ) * (3 * (Fintype.card F : ℤ) ^ 2) :=
      mul_le_mul_of_nonneg_left (quadraticSequenceConv_energy hF ν hν) (Nat.cast_nonneg _)
    _ = 3 * (Fintype.card F : ℤ) ^ 3 := by ring

end Erdos66CharacterEnergy
