import FormalConjectures.Util.ProblemImports

open scoped Real

/--
A364173: The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))


open scoped BigOperators

lemma sum_units_sq_zero (q : ℕ) (hq : Nat.Coprime q 6) [NeZero q] :
    (∑ u : (ZMod q)ˣ, ((u : ZMod q) ^ 2)) = 0 := by
  let c : (ZMod q)ˣ := ZMod.unitOfCoprime 2
    (Nat.Coprime.of_dvd (by norm_num : 2 ∣ 6) (dvd_refl q) hq.symm)
  have hc3 : IsUnit ((3 : ℕ) : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.of_dvd (by norm_num : 3 ∣ 6) (dvd_refl q) hq.symm
  let S : ZMod q := ∑ u : (ZMod q)ˣ, ((u : ZMod q) ^ 2)
  have hperm : S = ∑ u : (ZMod q)ˣ, (((c * u : (ZMod q)ˣ) : ZMod q) ^ 2) := by
    exact (Equiv.sum_comp (Equiv.mulLeft c)
      (fun u : (ZMod q)ˣ => ((u : ZMod q) ^ 2))).symm
  have hcval : (c : ZMod q) = 2 := by rfl
  have heq : S = (4 : ZMod q) * S := by
    calc
      S = ∑ u : (ZMod q)ˣ, (((c * u : (ZMod q)ˣ) : ZMod q) ^ 2) := hperm
      _ = ∑ u : (ZMod q)ˣ, ((c : ZMod q) ^ 2) * ((u : ZMod q) ^ 2) := by
        simp only [Units.val_mul, mul_pow]
      _ = ((c : ZMod q) ^ 2) * S := by rw [Finset.mul_sum]
      _ = (4 : ZMod q) * S := by rw [hcval]; norm_num
  have hzero : (3 : ZMod q) * S = 0 := by
    linear_combination -heq
  exact (hc3.mul_right_eq_zero.mp hzero)

lemma sum_units_zero (q : ℕ) (hq : Nat.Coprime q 2) [NeZero q] :
    (∑ u : (ZMod q)ˣ, (u : ZMod q)) = 0 := by
  let c : (ZMod q)ˣ := ZMod.unitOfCoprime 2 hq.symm
  let S : ZMod q := ∑ u : (ZMod q)ˣ, (u : ZMod q)
  have hperm : S = ∑ u : (ZMod q)ˣ, ((c * u : (ZMod q)ˣ) : ZMod q) := by
    exact (Equiv.sum_comp (Equiv.mulLeft c) (fun u : (ZMod q)ˣ => (u : ZMod q))).symm
  have hcval : (c : ZMod q) = 2 := by rfl
  have heq : S = (2 : ZMod q) * S := by
    calc
      S = ∑ u : (ZMod q)ˣ, ((c * u : (ZMod q)ˣ) : ZMod q) := hperm
      _ = ∑ u : (ZMod q)ˣ, (c : ZMod q) * (u : ZMod q) := by
        simp only [Units.val_mul]
      _ = (c : ZMod q) * S := by rw [Finset.mul_sum]
      _ = (2 : ZMod q) * S := by rw [hcval]
  linear_combination -heq



lemma q_sq_mul_eq_zero_of_cast_eq_zero (q : ℕ) [NeZero q]
    (x : ZMod (q ^ 3))
    (h : ZMod.castHom (by exact dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q) x = 0) :
    (q : ZMod (q ^ 3)) ^ 2 * x = 0 := by
  have hvcast : (x.val : ZMod q) = 0 := by
    simpa [ZMod.castHom_apply, ← ZMod.natCast_val] using h
  obtain ⟨k, hk⟩ : q ∣ x.val :=
    (ZMod.natCast_eq_zero_iff x.val q).mp hvcast
  rw [← ZMod.natCast_zmod_val x, hk]
  push_cast
  calc
    (q : ZMod (q ^ 3)) ^ 2 * ((q : ZMod (q ^ 3)) * k) =
        ((q ^ 3 : ℕ) : ZMod (q ^ 3)) * k := by push_cast; ring
    _ = 0 := by rw [ZMod.natCast_self]; simp

lemma q_mul_eq_zero_of_cast_eq_zero (q : ℕ) [NeZero q]
    (x : ZMod (q ^ 2))
    (h : ZMod.castHom (by exact dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q) x = 0) :
    (q : ZMod (q ^ 2)) * x = 0 := by
  have hvcast : (x.val : ZMod q) = 0 := by
    simpa [ZMod.castHom_apply, ← ZMod.natCast_val] using h
  obtain ⟨k, hk⟩ : q ∣ x.val :=
    (ZMod.natCast_eq_zero_iff x.val q).mp hvcast
  rw [← ZMod.natCast_zmod_val x, hk]
  push_cast
  calc
    (q : ZMod (q ^ 2)) * ((q : ZMod (q ^ 2)) * k) =
        ((q ^ 2 : ℕ) : ZMod (q ^ 2)) * k := by push_cast; ring
    _ = 0 := by rw [ZMod.natCast_self]; simp


lemma q_mul_eq_zero_of_cast_sq_eq_zero (q : ℕ) [NeZero q]
    (x : ZMod (q ^ 3))
    (h : ZMod.castHom (by
      exact pow_dvd_pow q (by norm_num : 2 ≤ 3)) (ZMod (q ^ 2)) x = 0) :
    (q : ZMod (q ^ 3)) * x = 0 := by
  have hvcast : (x.val : ZMod (q ^ 2)) = 0 := by
    simpa [ZMod.castHom_apply, ← ZMod.natCast_val] using h
  obtain ⟨k, hk⟩ : q ^ 2 ∣ x.val :=
    (ZMod.natCast_eq_zero_iff x.val (q ^ 2)).mp hvcast
  rw [← ZMod.natCast_zmod_val x, hk]
  push_cast
  calc
    (q : ZMod (q ^ 3)) * ((q : ZMod (q ^ 3)) ^ 2 * k) =
        ((q ^ 3 : ℕ) : ZMod (q ^ 3)) * k := by push_cast; ring
    _ = 0 := by rw [ZMod.natCast_self]; simp




section PairSum
variable {ι R : Type*} [DecidableEq ι] [CommRing R]

def pairSum (s : Finset ι) (f : ι → R) : R :=
  ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i

lemma pairSum_empty (f : ι → R) : pairSum ∅ f = 0 := by
  rw [pairSum, Finset.powersetCard_eq_empty.mpr (by norm_num)]
  simp

lemma pairSum_insert {a : ι} {s : Finset ι} (ha : a ∉ s) (f : ι → R) :
    pairSum (insert a s) f = pairSum s f + f a * ∑ i ∈ s, f i := by
  rw [pairSum, Finset.powersetCard_succ_insert ha 1]
  rw [Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [Finset.powersetCard_one, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Finset.prod_insert, Finset.prod_singleton]
      apply congrArg (fun z : R => pairSum s f + z)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hax : a ≠ x := fun h => ha (h ▸ hx)
      simp [hax, mul_comm]
    · intro t ht u hu htu
      have hat : a ∉ t := fun h => ha ((Finset.mem_powersetCard.mp ht).1 h)
      have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
      have := congrArg (fun v : Finset ι => v.erase a) htu
      simpa [hat, hau] using this
  · rw [Finset.disjoint_left]
    intro t ht1 ht2
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht2
    exact ha ((Finset.mem_powersetCard.mp ht1).1 (Finset.mem_insert_self a u))

lemma two_mul_pairSum (s : Finset ι) (f : ι → R) :
    2 * pairSum s f = (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2 := by
  induction s using Finset.induction with
  | empty => rw [pairSum_empty]; simp
  | @insert a s ha ih =>
      rw [pairSum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      linear_combination ih

lemma prod_one_add_trunc (s : Finset ι) (f : ι → R) (x : R) (hx : x ^ 3 = 0) :
    ∏ i ∈ s, (1 + x * f i) =
      1 + x * (∑ i ∈ s, f i) + x ^ 2 * pairSum s f := by
  induction s using Finset.induction with
  | empty => rw [pairSum_empty]; simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, pairSum_insert ha, ih]
      have hx' : x ^ 2 * x = 0 := by
        calc x ^ 2 * x = x ^ 3 := by ring
             _ = 0 := hx
      ring_nf at hx' ⊢
      simp [hx']



lemma map_pairSum {S : Type*} [CommRing S] (g : R →+* S) (s : Finset ι) (f : ι → R) :
    g (pairSum s f) = pairSum s (fun i => g (f i)) := by
  simp [pairSum, map_sum, map_prod]


end PairSum

section UnitLift

variable (q : ℕ) [NeZero q]

def liftUnit (u : (ZMod q)ˣ) : (ZMod (q ^ 3))ˣ :=
  ZMod.unitOfCoprime (u : ZMod q).val
    ((ZMod.val_coe_unit_coprime u).pow_right 3)

lemma liftUnit_val (u : (ZMod q)ˣ) :
    ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) = (u : ZMod q).val := rfl

lemma cast_liftUnit (u : (ZMod q)ˣ) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)
      ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) = (u : ZMod q) := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have hlt : (u : ZMod q).val < q ^ 3 :=
    lt_of_lt_of_le (ZMod.val_lt (u : ZMod q)) (Nat.le_pow (by norm_num : 0 < 3))
  have hv : ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)).val = (u : ZMod q).val := by
    rw [liftUnit, ZMod.coe_unitOfCoprime]
    exact ZMod.val_cast_of_lt hlt
  rw [hv]
  exact ZMod.natCast_zmod_val (u : ZMod q)

lemma cast_liftUnit_inv (u : (ZMod q)ˣ) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  apply IsUnit.mul_right_cancel (Units.isUnit u)
  calc
    ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)
          (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) * (u : ZMod q) =
        ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)
          ((((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) *
            ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) := by rw [map_mul, cast_liftUnit]
    _ = 1 := by rw [Units.inv_mul, map_one]
    _ = (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)) := by rw [Units.inv_mul]

lemma cast_sum_liftUnit_inv_sq_zero (hq : Nat.Coprime q 6) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)
      (∑ u : (ZMod q)ˣ,
        ((((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) ^ 2)) = 0 := by
  rw [map_sum]
  simp_rw [map_pow, cast_liftUnit_inv]
  rw [show (∑ u : (ZMod q)ˣ, (((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2)) =
      ∑ u : (ZMod q)ˣ, ((u : ZMod q) ^ 2) by
    exact Equiv.sum_comp (Equiv.inv (ZMod q)ˣ) (fun u : (ZMod q)ˣ => ((u : ZMod q) ^ 2))]
  exact sum_units_sq_zero q hq

def liftUnit2 (u : (ZMod q)ˣ) : (ZMod (q ^ 2))ˣ :=
  ZMod.unitOfCoprime (u : ZMod q).val
    ((ZMod.val_coe_unit_coprime u).pow_right 2)

lemma cast_liftUnit2 (u : (ZMod q)ˣ) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)
      ((liftUnit2 q u : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) = (u : ZMod q) := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have hlt : (u : ZMod q).val < q ^ 2 :=
    lt_of_lt_of_le (ZMod.val_lt (u : ZMod q)) (Nat.le_pow (by norm_num : 0 < 2))
  have hv : ((liftUnit2 q u : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)).val = (u : ZMod q).val := by
    rw [liftUnit2, ZMod.coe_unitOfCoprime]
    exact ZMod.val_cast_of_lt hlt
  rw [hv]
  exact ZMod.natCast_zmod_val (u : ZMod q)

lemma cast_liftUnit2_inv (u : (ZMod q)ˣ) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)
      (((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  apply IsUnit.mul_right_cancel (Units.isUnit u)
  calc
    ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)
          (((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) * (u : ZMod q) =
        ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)
          ((((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) *
            ((liftUnit2 q u : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2))) := by rw [map_mul, cast_liftUnit2]
    _ = 1 := by rw [Units.inv_mul, map_one]
    _ = (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)) := by rw [Units.inv_mul]

lemma liftUnit2_add_neg (hq : 1 < q) (u : (ZMod q)ˣ) :
    ((liftUnit2 q u : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) +
      ((liftUnit2 q (-u) : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) = q := by
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
  have hu0 : (u : ZMod q) ≠ 0 := Units.ne_zero u
  letI : NeZero (u : ZMod q) := ⟨hu0⟩
  have hvneg : (-(u : ZMod q)).val = q - (u : ZMod q).val := ZMod.val_neg_of_ne_zero _
  rw [liftUnit2, liftUnit2, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime]
  push_cast
  rw [hvneg]
  have hvlt := ZMod.val_lt (u : ZMod q)
  have hsum : (u : ZMod q).val + (q - (u : ZMod q).val) = q :=
    Nat.add_sub_of_le (Nat.le_of_lt hvlt)
  simpa using congrArg (fun n : ℕ => (n : ZMod (q ^ 2))) hsum

lemma liftUnit2_inv_add_neg (hq : 1 < q) (u : (ZMod q)ˣ) :
    (((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) +
      (((liftUnit2 q (-u))⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) =
    (q : ZMod (q ^ 2)) *
      ((((liftUnit2 q u) * (liftUnit2 q (-u)))⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) := by
  let a := liftUnit2 q u
  let b := liftUnit2 q (-u)
  have hab : (a : ZMod (q ^ 2)) + (b : ZMod (q ^ 2)) = q := liftUnit2_add_neg q hq u
  change (↑(a⁻¹) : ZMod (q ^ 2)) + ↑(b⁻¹) = q * (↑((a * b)⁻¹) : ZMod (q ^ 2))
  rw [← hab]
  apply IsUnit.mul_right_cancel (Units.isUnit (a * b))
  change ((↑(a⁻¹) : ZMod (q ^ 2)) + ↑(b⁻¹)) * ↑(a * b) =
    ((↑a + ↑b) * ↑((a * b)⁻¹)) * ↑(a * b)
  rw [add_mul]
  have h1 : (↑(a⁻¹) : ZMod (q ^ 2)) * ↑(a * b) = ↑b := by
    rw [Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
  have h2 : (↑(b⁻¹) : ZMod (q ^ 2)) * ↑(a * b) = ↑a := by
    rw [Units.val_mul]
    calc
      (↑(b⁻¹) : ZMod (q ^ 2)) * (↑a * ↑b) = ↑a * (↑(b⁻¹) * ↑b) := by ring
      _ = ↑a := by rw [Units.inv_mul, mul_one]
  have h3 : ((↑a + ↑b) : ZMod (q ^ 2)) * ↑((a * b)⁻¹) * ↑(a * b) = ↑a + ↑b := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  rw [h1, h2, h3, add_comm]

lemma cast_liftUnit2_mul_inv (u : (ZMod q)ˣ) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)
      (((liftUnit2 q u * liftUnit2 q (-u))⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) =
      (((u * (-u))⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  rw [show (liftUnit2 q u * liftUnit2 q (-u))⁻¹ =
      (liftUnit2 q u)⁻¹ * (liftUnit2 q (-u))⁻¹ by rw [mul_inv_rev]; exact mul_comm _ _]
  rw [show (u * (-u))⁻¹ = u⁻¹ * (-u)⁻¹ by rw [mul_inv_rev]; exact mul_comm _ _]
  simp only [Units.val_mul, map_mul]
  rw [cast_liftUnit2_inv, cast_liftUnit2_inv]

lemma cast_sum_liftUnit2_pair_inv_zero (hq : Nat.Coprime q 6) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)
      (∑ u : (ZMod q)ˣ,
        (((liftUnit2 q u * liftUnit2 q (-u))⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2))) = 0 := by
  rw [map_sum]
  simp_rw [cast_liftUnit2_mul_inv]
  have heach : ∀ u : (ZMod q)ˣ,
      (((u * (-u))⁻¹ : (ZMod q)ˣ) : ZMod q) = -(((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2) := by
    intro u
    calc
      (((u * (-u))⁻¹ : (ZMod q)ˣ) : ZMod q) =
          ((-(u⁻¹ * u⁻¹) : (ZMod q)ˣ) : ZMod q) := by
            congr 1
            rw [show -u = (-1) * u by exact neg_eq_neg_one_mul u]
            rw [mul_inv_rev]
            rw [show ((-1 : (ZMod q)ˣ) * u)⁻¹ = u⁻¹ * (-1 : (ZMod q)ˣ)⁻¹ by
              rw [mul_inv_rev]]
            rw [inv_neg, inv_one, mul_neg, mul_one, neg_mul]
      _ = -(((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2) := by
        simp only [Units.val_neg, Units.val_mul, pow_two]
  simp_rw [heach]
  change (∑ u : (ZMod q)ˣ, -(((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2)) = 0
  rw [show (∑ u : (ZMod q)ˣ, -(((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2)) =
      -(∑ u : (ZMod q)ˣ, (((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2)) by
    simpa using Finset.sum_neg_distrib (s := Finset.univ)
      (fun u : (ZMod q)ˣ => (((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2))]
  rw [show (∑ u : (ZMod q)ˣ, (((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2)) =
      ∑ u : (ZMod q)ˣ, ((u : ZMod q) ^ 2) by
    exact Equiv.sum_comp (Equiv.inv (ZMod q)ˣ) (fun u : (ZMod q)ˣ => ((u : ZMod q) ^ 2))]
  rw [sum_units_sq_zero q hq, neg_zero]

lemma sum_liftUnit2_inv_zero (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) :
    (∑ u : (ZMod q)ˣ,
      (((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2))) = 0 := by
  let S : ZMod (q ^ 2) := ∑ u : (ZMod q)ˣ,
    (((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2))
  let T : ZMod (q ^ 2) := ∑ u : (ZMod q)ˣ,
    (((liftUnit2 q u * liftUnit2 q (-u))⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2))
  have hperm : S = ∑ u : (ZMod q)ˣ,
      (((liftUnit2 q (-u))⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) := by
    exact (Equiv.sum_comp (Equiv.neg (ZMod q)ˣ)
      (fun u : (ZMod q)ˣ => (((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)))).symm
  have htwo : (2 : ZMod (q ^ 2)) * S = (q : ZMod (q ^ 2)) * T := by
    calc
      (2 : ZMod (q ^ 2)) * S = S + S := by ring
      _ = S + ∑ u : (ZMod q)ˣ,
          (((liftUnit2 q (-u))⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) := by
        exact congrArg (fun z : ZMod (q ^ 2) => S + z) hperm
      _ = ∑ u : (ZMod q)ˣ,
          ((((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) +
           (((liftUnit2 q (-u))⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2))) := by
        exact Finset.sum_add_distrib.symm
      _ = ∑ u : (ZMod q)ˣ, (q : ZMod (q ^ 2)) *
          (((liftUnit2 q u * liftUnit2 q (-u))⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact liftUnit2_inv_add_neg q hq1 u
      _ = (q : ZMod (q ^ 2)) * T := by rw [Finset.mul_sum]
  have hcastT : ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q) T = 0 :=
    cast_sum_liftUnit2_pair_inv_zero q hq6
  have hqT : (q : ZMod (q ^ 2)) * T = 0 := q_mul_eq_zero_of_cast_eq_zero q T hcastT
  have h2S : (2 : ZMod (q ^ 2)) * S = 0 := htwo.trans hqT
  have hcop2q : Nat.Coprime 2 (q ^ 2) :=
    (Nat.Coprime.of_dvd (by norm_num : 2 ∣ 6) (dvd_refl q) hq6.symm).pow_right 2
  have hu2 : IsUnit ((2 : ℕ) : ZMod (q ^ 2)) := (ZMod.isUnit_iff_coprime 2 (q ^ 2)).mpr hcop2q
  exact hu2.mul_right_eq_zero.mp h2S

lemma cast_liftUnit_to_sq (u : (ZMod q)ˣ) :
    ZMod.castHom (pow_dvd_pow q (by norm_num : 2 ≤ 3)) (ZMod (q ^ 2))
      ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) =
      ((liftUnit2 q u : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [liftUnit, liftUnit2, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime]
  have hlt3 : (u : ZMod q).val < q ^ 3 :=
    lt_of_lt_of_le (ZMod.val_lt (u : ZMod q)) (Nat.le_pow (by norm_num : 0 < 3))
  rw [ZMod.val_cast_of_lt hlt3]

lemma cast_liftUnit_inv_to_sq (u : (ZMod q)ˣ) :
    ZMod.castHom (pow_dvd_pow q (by norm_num : 2 ≤ 3)) (ZMod (q ^ 2))
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) =
      (((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) := by
  apply IsUnit.mul_right_cancel (Units.isUnit (liftUnit2 q u))
  calc
    ZMod.castHom (pow_dvd_pow q (by norm_num : 2 ≤ 3)) (ZMod (q ^ 2))
        (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) *
        ((liftUnit2 q u : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) =
      ZMod.castHom (pow_dvd_pow q (by norm_num : 2 ≤ 3)) (ZMod (q ^ 2))
        ((((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) *
          ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) := by
            rw [map_mul, cast_liftUnit_to_sq]
    _ = 1 := by rw [Units.inv_mul, map_one]
    _ = (((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) *
          ((liftUnit2 q u : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) := by rw [Units.inv_mul]

lemma cast_sum_liftUnit_inv_to_sq_zero (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) :
    ZMod.castHom (pow_dvd_pow q (by norm_num : 2 ≤ 3)) (ZMod (q ^ 2))
      (∑ u : (ZMod q)ˣ,
        (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) = 0 := by
  rw [map_sum]
  simp_rw [cast_liftUnit_inv_to_sq]
  exact sum_liftUnit2_inv_zero q hq1 hq6





lemma cast_pairSum_liftUnit_inv_zero (hq6 : Nat.Coprime q 6) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)
      (pairSum Finset.univ (fun u : (ZMod q)ˣ =>
        (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))) = 0 := by
  rw [map_pairSum]
  simp_rw [cast_liftUnit_inv]
  let f : (ZMod q)ˣ → ZMod q := fun u => ((u⁻¹ : (ZMod q)ˣ) : ZMod q)
  have hcop2 : Nat.Coprime q 2 :=
    Nat.Coprime.of_dvd (dvd_refl q) (by norm_num : 2 ∣ 6) hq6
  have hs : (∑ u : (ZMod q)ˣ, f u) = 0 := by
    rw [show (∑ u : (ZMod q)ˣ, f u) = ∑ u : (ZMod q)ˣ, (u : ZMod q) by
      exact Equiv.sum_comp (Equiv.inv (ZMod q)ˣ) (fun u : (ZMod q)ˣ => (u : ZMod q))]
    exact sum_units_zero q hcop2
  have hs2 : (∑ u : (ZMod q)ˣ, (f u) ^ 2) = 0 := by
    rw [show (∑ u : (ZMod q)ˣ, (f u) ^ 2) = ∑ u : (ZMod q)ˣ, ((u : ZMod q) ^ 2) by
      exact Equiv.sum_comp (Equiv.inv (ZMod q)ˣ) (fun u : (ZMod q)ˣ => ((u : ZMod q) ^ 2))]
    exact sum_units_sq_zero q hq6
  have htwo : (2 : ZMod q) * pairSum Finset.univ f = 0 := by
    rw [two_mul_pairSum, hs, hs2]
    ring
  have hu2 : IsUnit ((2 : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr hcop2.symm
  exact hu2.mul_right_eq_zero.mp htwo

lemma q_sq_mul_pairSum_liftUnit_inv_zero (hq6 : Nat.Coprime q 6) :
    (q : ZMod (q ^ 3)) ^ 2 *
      pairSum Finset.univ (fun u : (ZMod q)ˣ =>
        (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) = 0 :=
  q_sq_mul_eq_zero_of_cast_eq_zero q _ (cast_pairSum_liftUnit_inv_zero q hq6)





end UnitLift

section UnitBlock

variable (q : ℕ) [NeZero q]

def unitBlock (j : ℕ) : ZMod (q ^ 3) :=
  ∏ u : (ZMod q)ˣ, (((u : ZMod q).val + q * j : ℕ) : ZMod (q ^ 3))

lemma unitBlock_factor (j : ℕ) : unitBlock q j =
    (∏ u : (ZMod q)ˣ, ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) *
    ∏ u : (ZMod q)ˣ, (1 + (q * j : ℕ) *
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) := by
  rw [unitBlock]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u hu
  have ha : (((u : ZMod q).val : ℕ) : ZMod (q ^ 3)) =
      ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) := by
    rw [liftUnit, ZMod.coe_unitOfCoprime]
  push_cast
  rw [ha]
  have hunit : ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) *
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) = 1 := Units.mul_inv (liftUnit q u)
  ring_nf at hunit ⊢
  simp [hunit]

lemma unitBlock_zero : unitBlock q 0 =
    ∏ u : (ZMod q)ˣ, ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) := by
  rw [unitBlock]
  apply Finset.prod_congr rfl
  intro u hu
  simp only [Nat.mul_zero, Nat.add_zero]
  rw [liftUnit, ZMod.coe_unitOfCoprime]

lemma perturb_prod_eq_one (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) (j : ℕ) :
    (∏ u : (ZMod q)ˣ, (1 + (q * j : ℕ) *
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))) = 1 := by
  let f : (ZMod q)ˣ → ZMod (q ^ 3) := fun u =>
    (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
  let x : ZMod (q ^ 3) := (q * j : ℕ)
  have hx3 : x ^ 3 = 0 := by
    dsimp [x]
    push_cast
    calc
      ((q : ZMod (q ^ 3)) * j) ^ 3 =
          ((q ^ 3 : ℕ) : ZMod (q ^ 3)) * (j : ZMod (q ^ 3)) ^ 3 := by push_cast; ring
      _ = 0 := by rw [ZMod.natCast_self]; simp
  rw [prod_one_add_trunc Finset.univ f x hx3]
  have hcastS := cast_sum_liftUnit_inv_to_sq_zero q hq1 hq6
  have hqS : (q : ZMod (q ^ 3)) * (∑ u : (ZMod q)ˣ, f u) = 0 :=
    q_mul_eq_zero_of_cast_sq_eq_zero q _ hcastS
  have hxS : x * (∑ u : (ZMod q)ˣ, f u) = 0 := by
    dsimp [x]
    push_cast
    calc
      (q : ZMod (q ^ 3)) * j * (∑ u : (ZMod q)ˣ, f u) =
          (j : ZMod (q ^ 3)) * ((q : ZMod (q ^ 3)) * ∑ u : (ZMod q)ˣ, f u) := by ring
      _ = 0 := by rw [hqS, mul_zero]
  have hq2P := q_sq_mul_pairSum_liftUnit_inv_zero q hq6
  have hx2P : x ^ 2 * pairSum Finset.univ f = 0 := by
    dsimp [x]
    push_cast
    calc
      ((q : ZMod (q ^ 3)) * j) ^ 2 * pairSum Finset.univ f =
          (j : ZMod (q ^ 3)) ^ 2 *
            ((q : ZMod (q ^ 3)) ^ 2 * pairSum Finset.univ f) := by ring
      _ = 0 := by rw [hq2P, mul_zero]
  rw [hxS, hx2P, add_zero, add_zero]

lemma unitBlock_eq_zero (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) (j : ℕ) :
    unitBlock q j = unitBlock q 0 := by
  rw [unitBlock_factor, perturb_prod_eq_one q hq1 hq6, mul_one, unitBlock_zero]

end UnitBlock

section PunitFactorial

open scoped Nat

def punitFac (p m : ℕ) : ℕ :=
  ∏ i ∈ (Finset.Ico 1 (m + 1)).filter (fun i => ¬ p ∣ i), i

lemma prod_multiples (p m : ℕ) (hp : 0 < p) :
    (∏ i ∈ (Finset.Ico 1 (p * m + 1)).filter (fun i => p ∣ i), i) =
      p ^ m * m ! := by
  have hbij : (∏ a ∈ Finset.Ico 1 (m + 1), p * a) =
      ∏ i ∈ (Finset.Ico 1 (p * m + 1)).filter (fun i => p ∣ i), i := by
    apply Finset.prod_bij (fun a ha => p * a)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
      constructor
      · constructor <;> nlinarith
      · exact dvd_mul_right p a
    · intro a1 h1 a2 h2 heq
      exact Nat.eq_of_mul_eq_mul_left hp heq
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_Ico] at hb
      obtain ⟨hbI, ⟨a, rfl⟩⟩ := hb
      refine ⟨a, ?_, rfl⟩
      simp only [Finset.mem_Ico]
      constructor <;> nlinarith
    · intro a ha
      rfl
  rw [← hbij, Finset.prod_mul_distrib, Finset.prod_const]
  rw [Nat.card_Ico]
  rw [Nat.add_sub_cancel_right]
  rw [Finset.prod_Ico_id_eq_factorial]

lemma factorial_strip (p m : ℕ) (hp : 0 < p) :
    (p * m)! = p ^ m * m ! * punitFac p (p * m) := by
  rw [← Finset.prod_Ico_id_eq_factorial]
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.Ico 1 (p * m + 1)) (fun i => p ∣ i) (fun i => i)]
  rw [prod_multiples p m hp]
  rfl

end PunitFactorial

lemma punitFac_coprime (p m : ℕ) (hp : p.Prime) : p.Coprime (punitFac p m) := by
  rw [punitFac]
  apply Nat.Coprime.prod_right
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_Ico] at hi
  exact hp.coprime_iff_not_dvd.mpr hi.2



section PunitBlocks

open scoped Nat

def punitBlockNat (p q j : ℕ) : ℕ :=
  ∏ i ∈ (Finset.Ico (q * j + 1) (q * (j + 1) + 1)).filter (fun i => ¬ p ∣ i), i

lemma punitBlockNat_eq_units {p r : ℕ} (hp : p.Prime) (hr : 0 < r)
    (j : ℕ) (q : ℕ) [NeZero q] (hq : q = p ^ r) :
    punitBlockNat p q j = (Finset.univ : Finset ((ZMod q)ˣ)).prod
      (fun u : (ZMod q)ˣ => q * j + ZMod.val u.1) := by
  subst q
  let q := p ^ r
  have hq1 : 1 < q := one_lt_pow₀ hp.one_lt hr.ne'
  haveI : NeZero q := ⟨ne_of_gt (lt_trans Nat.zero_lt_one hq1)⟩
  have hpq : p ∣ q := dvd_pow_self p hr.ne'
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
  dsimp [q] at *
  have hqsucc : q * (j + 1) = q * j + q := by ring
  symm
  change (Finset.univ : Finset ((ZMod q)ˣ)).prod
      (fun u : (ZMod q)ˣ => q * j + (u : ZMod q).val) =
    ((Finset.Ico (q * j + 1) (q * (j + 1) + 1)).filter (fun i => ¬ p ∣ i)).prod id
  apply Finset.prod_bij
    (s := (Finset.univ : Finset ((ZMod q)ˣ)))
    (t := (Finset.Ico (q * j + 1) (q * (j + 1) + 1)).filter (fun i => ¬ p ∣ i))
    (f := fun u : (ZMod q)ˣ => q * j + (u : ZMod q).val)
    (g := id)
    (fun u hu => q * j + (u : ZMod q).val)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_Ico]
    have hvlt := ZMod.val_lt (u : ZMod q)
    have hv0 : 0 < (u : ZMod q).val := by
      have hne : (u : ZMod q) ≠ 0 := Units.ne_zero u
      exact Nat.pos_of_ne_zero (fun hv => hne ((ZMod.val_eq_zero (u : ZMod q)).mp hv))
    have hcop : (u : ZMod q).val.Coprime p :=
      Nat.Coprime.coprime_dvd_right hpq (ZMod.val_coe_unit_coprime u)
    have hnval : ¬ p ∣ (u : ZMod q).val :=
      (hp.coprime_iff_not_dvd.mp hcop.symm)
    constructor
    · constructor
      · omega
      · rw [hqsucc]
        omega
    · intro hd
      have hdqj : p ∣ q * j := dvd_mul_of_dvd_left hpq j
      exact hnval ((Nat.dvd_add_iff_right hdqj).mpr (by simpa [add_comm] using hd))
  · intro u1 h1 u2 h2 heq
    have hv : (u1 : ZMod q).val = (u2 : ZMod q).val := by omega
    apply Units.ext
    apply ZMod.val_injective
    exact hv
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_Ico] at hb
    rw [hqsucc] at hb
    let d := b - q * j
    have hdpos : 0 < d := by dsimp [d]; omega
    have hdle : d ≤ q := by dsimp [d]; omega
    have hdp : ¬ p ∣ d := by
      intro hpd
      have hdqj : p ∣ q * j := dvd_mul_of_dvd_left hpq j
      have : p ∣ b := by
        have hbdecomp : b = d + q * j := by dsimp [d]; omega
        rw [hbdecomp]
        exact dvd_add hpd hdqj
      exact hb.2 this
    have hdlt : d < q := lt_of_le_of_ne hdle (fun heq => by
      apply hb.2
      have hbq : b = q * (j + 1) := by dsimp [d] at heq; omega
      rw [hbq]
      exact dvd_mul_of_dvd_left hpq (j + 1))
    have hdcop : d.Coprime q := by
      dsimp [q]
      exact (hp.coprime_iff_not_dvd.mpr hdp).symm.pow_right r
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime d hdcop
    refine ⟨u, Finset.mem_univ _, ?_⟩
    have huval : (u : ZMod q).val = d := by
      dsimp [u]
      exact ZMod.val_cast_of_lt hdlt
    rw [huval]
    dsimp [d]
    omega
  · intro u hu
    rfl

lemma punitBlockNat_cast_eq_unitBlock {p r : ℕ} [NeZero (p ^ r)] (hp : p.Prime) (hr : 0 < r)
    (j : ℕ) :
    ((punitBlockNat p (p ^ r) j : ℕ) : ZMod ((p ^ r) ^ 3)) = unitBlock (p ^ r) j := by
  let q := p ^ r
  have hq1 : 1 < q := one_lt_pow₀ hp.one_lt hr.ne'
  haveI : NeZero q := ⟨ne_of_gt (lt_trans Nat.zero_lt_one hq1)⟩
  rw [punitBlockNat_eq_units hp hr j q rfl, unitBlock]
  push_cast
  apply Finset.prod_congr rfl
  intro u hu
  dsimp [q]
  push_cast
  ring

lemma punitFac_eq_prod_blocks (p q k : ℕ) :
    punitFac p (q * k) = ∏ j ∈ Finset.range k, punitBlockNat p q j := by
  induction k with
  | zero => simp [punitFac, punitBlockNat]
  | succ k ih =>
      rw [Nat.mul_succ]
      have hmul : q * (k + 1) = q * k + q := by ring
      have hsplit : Finset.Ico 1 (q * k + q + 1) =
          Finset.Ico 1 (q * k + 1) ∪ Finset.Ico (q * k + 1) (q * k + q + 1) := by
        rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
      have hdis : Disjoint
          ((Finset.Ico 1 (q * k + 1)).filter (fun i => ¬ p ∣ i))
          ((Finset.Ico (q * k + 1) (q * k + q + 1)).filter (fun i => ¬ p ∣ i)) := by
        apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_Ico] at hx1 hx2
        omega
      rw [punitFac, hsplit, Finset.filter_union, Finset.prod_union hdis]
      change punitFac p (q * k) * punitBlockNat p q k = _
      rw [ih, Finset.prod_range_succ]

lemma punitFac_cast_eq_block_pow {p r : ℕ} [NeZero (p ^ r)]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) (k : ℕ) :
    ((punitFac p ((p ^ r) * k) : ℕ) : ZMod ((p ^ r) ^ 3)) =
      unitBlock (p ^ r) 0 ^ k := by
  rw [punitFac_eq_prod_blocks]
  push_cast
  have hq1 : 1 < p ^ r := one_lt_pow₀ hp.one_lt hr.ne'
  have hp6 : p.Coprime 6 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have hple : p ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    have hcases : p = 5 ∨ p = 6 := by omega
    rcases hcases with rfl | rfl
    · norm_num at hd
    · norm_num at hp)
  have hcop : Nat.Coprime (p ^ r) 6 := hp6.pow_left r
  calc
    (∏ j ∈ Finset.range k,
        ((punitBlockNat p (p ^ r) j : ℕ) : ZMod ((p ^ r) ^ 3))) =
        ∏ j ∈ Finset.range k, unitBlock (p ^ r) 0 := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [punitBlockNat_cast_eq_unitBlock hp hr]
      exact unitBlock_eq_zero (p ^ r) hq1 hcop j
    _ = unitBlock (p ^ r) 0 ^ k := by rw [Finset.prod_const]; simp

end PunitBlocks

section EvenRatio

open scoped Nat

def evenNum (k : ℕ) : ℕ := (18 * k)! * (4 * k)! * (3 * k)!
def evenDen (k : ℕ) : ℕ := (9 * k)! * (8 * k)! * (6 * k)! * (2 * k)!

def evenUNum (p k : ℕ) : ℕ :=
  punitFac p (p * (18 * k)) * punitFac p (p * (4 * k)) * punitFac p (p * (3 * k))
def evenUDen (p k : ℕ) : ℕ :=
  punitFac p (p * (9 * k)) * punitFac p (p * (8 * k)) *
    punitFac p (p * (6 * k)) * punitFac p (p * (2 * k))

def evenPNum (p k : ℕ) : ℕ := p ^ (18 * k) * p ^ (4 * k) * p ^ (3 * k)
def evenPDen (p k : ℕ) : ℕ := p ^ (9 * k) * p ^ (8 * k) * p ^ (6 * k) * p ^ (2 * k)

lemma evenPNum_eq_evenPDen (p k : ℕ) : evenPNum p k = evenPDen p k := by
  simp only [evenPNum, evenPDen, ← pow_add]
  congr 1
  omega

lemma evenNum_strip (p k : ℕ) (hp : 0 < p) :
    evenNum (p * k) = evenPNum p k * evenNum k * evenUNum p k := by
  rw [evenNum, evenNum, evenPNum, evenUNum]
  have h18 := factorial_strip p (18 * k) hp
  have h4 := factorial_strip p (4 * k) hp
  have h3 := factorial_strip p (3 * k) hp
  rw [show 18 * (p * k) = p * (18 * k) by ring,
      show 4 * (p * k) = p * (4 * k) by ring,
      show 3 * (p * k) = p * (3 * k) by ring,
      h18, h4, h3]
  ring

lemma evenDen_strip (p k : ℕ) (hp : 0 < p) :
    evenDen (p * k) = evenPDen p k * evenDen k * evenUDen p k := by
  rw [evenDen, evenDen, evenPDen, evenUDen]
  have h9 := factorial_strip p (9 * k) hp
  have h8 := factorial_strip p (8 * k) hp
  have h6 := factorial_strip p (6 * k) hp
  have h2 := factorial_strip p (2 * k) hp
  rw [show 9 * (p * k) = p * (9 * k) by ring,
      show 8 * (p * k) = p * (8 * k) by ring,
      show 6 * (p * k) = p * (6 * k) by ring,
      show 2 * (p * k) = p * (2 * k) by ring,
      h9, h8, h6, h2]
  ring

lemma even_units_cast_eq {p s k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    let q := p ^ (s + 1)
    ((evenUNum p (k * p ^ s) : ℕ) : ZMod (q ^ 3)) =
      ((evenUDen p (k * p ^ s) : ℕ) : ZMod (q ^ 3)) := by
  let q := p ^ (s + 1)
  have hq1 : 1 < q := one_lt_pow₀ hp.one_lt (by omega)
  haveI : NeZero q := ⟨ne_of_gt (lt_trans Nat.zero_lt_one hq1)⟩
  let B : ZMod (q ^ 3) := unitBlock q 0
  have harg (c : ℕ) : p * (c * (k * p ^ s)) = q * (c * k) := by
    dsimp [q]
    rw [pow_succ']
    ring
  have hU (c : ℕ) :
      ((punitFac p (p * (c * (k * p ^ s))) : ℕ) : ZMod (q ^ 3)) = B ^ (c * k) := by
    rw [harg]
    exact punitFac_cast_eq_block_pow hp hp5 (by omega : 0 < s + 1) (c * k)
  simp only [evenUNum, evenUDen]
  push_cast
  simp_rw [hU]
  simp only [← pow_add]
  congr 1
  omega

lemma evenUDen_coprime (p k : ℕ) (hp : p.Prime) : p.Coprime (evenUDen p k) := by
  simp only [evenUDen]
  repeat' apply Nat.Coprime.mul_right
  all_goals exact punitFac_coprime p _ hp

lemma even_quotient_modEq {p s k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (z0 z1 : ℤ)
    (h0 : z0 * (evenDen (k * p ^ s) : ℤ) = (evenNum (k * p ^ s) : ℤ))
    (h1 : z1 * (evenDen (p * (k * p ^ s)) : ℤ) =
      (evenNum (p * (k * p ^ s)) : ℤ)) :
    z1 ≡ z0 [ZMOD ((p ^ (s + 1)) ^ 3 : ℕ)] := by
  let K := k * p ^ s
  let q := p ^ (s + 1)
  have hq1 : 1 < q := one_lt_pow₀ hp.one_lt (by omega)
  haveI : NeZero q := ⟨ne_of_gt (lt_trans Nat.zero_lt_one hq1)⟩
  have hP := evenPNum_eq_evenPDen p K
  have h1s := h1
  rw [evenDen_strip p K hp.pos, evenNum_strip p K hp.pos, hP] at h1s
  push_cast at h1s
  have hPnat : 0 < evenPDen p K := by
    unfold evenPDen
    positivity
  have hP0 : (evenPDen p K : ℤ) ≠ 0 := by exact_mod_cast hPnat.ne'
  have hstrip : z1 * (evenDen K : ℤ) * (evenUDen p K : ℤ) =
      (evenNum K : ℤ) * (evenUNum p K : ℤ) := by
    apply mul_left_cancel₀ hP0
    calc
      (evenPDen p K : ℤ) * (z1 * (evenDen K : ℤ) * (evenUDen p K : ℤ)) =
          z1 * ((evenPDen p K : ℤ) * (evenDen K : ℤ) * (evenUDen p K : ℤ)) := by ring
      _ = (evenPDen p K : ℤ) * (evenNum K : ℤ) * (evenUNum p K : ℤ) := h1s
      _ = (evenPDen p K : ℤ) * ((evenNum K : ℤ) * (evenUNum p K : ℤ)) := by ring
  have hDnat : 0 < evenDen K := by
    unfold evenDen
    positivity
  have hD0 : (evenDen K : ℤ) ≠ 0 := by exact_mod_cast hDnat.ne'
  have hcross : z1 * (evenUDen p K : ℤ) = z0 * (evenUNum p K : ℤ) := by
    apply mul_left_cancel₀ hD0
    calc
      (evenDen K : ℤ) * (z1 * (evenUDen p K : ℤ)) =
          z1 * (evenDen K : ℤ) * (evenUDen p K : ℤ) := by ring
      _ = (evenNum K : ℤ) * (evenUNum p K : ℤ) := hstrip
      _ = (z0 * (evenDen K : ℤ)) * (evenUNum p K : ℤ) := by rw [h0]
      _ = (evenDen K : ℤ) * (z0 * (evenUNum p K : ℤ)) := by ring
  have hcopP : p.Coprime (evenUDen p K) := evenUDen_coprime p K hp
  have hcopQ : Nat.Coprime (q ^ 3) (evenUDen p K) := by
    dsimp [q]
    rw [← pow_mul]
    exact hcopP.pow_left ((s + 1) * 3)
  have hunit : IsUnit ((evenUDen p K : ℕ) : ZMod (q ^ 3)) :=
    (ZMod.isUnit_iff_coprime (evenUDen p K) (q ^ 3)).mpr hcopQ.symm
  apply (ZMod.intCast_eq_intCast_iff z1 z0 (q ^ 3)).mp
  apply IsUnit.mul_left_cancel hunit
  have hcasteq := congrArg (fun z : ℤ => (z : ZMod (q ^ 3))) hcross
  push_cast at hcasteq ⊢
  rw [mul_comm (evenUDen p K : ZMod (q ^ 3)),
      mul_comm (evenUDen p K : ZMod (q ^ 3))]
  rw [hcasteq]
  have hu := even_units_cast_eq (p := p) (s := s) (k := k) hp hp5
  change ((evenUNum p K : ℕ) : ZMod (q ^ 3)) =
    ((evenUDen p K : ℕ) : ZMod (q ^ 3)) at hu
  rw [hu]

end EvenRatio

section HalfUnits

variable (q : ℕ) [NeZero q]

def halfUnits : Finset (ZMod q)ˣ :=
  Finset.univ.filter (fun u : (ZMod q)ˣ => Odd (u : ZMod q).val)

lemma odd_val_neg_iff (hq1 : 1 < q) (hqodd : Odd q) (u : (ZMod q)ˣ) :
    Odd ((-u : (ZMod q)ˣ) : ZMod q).val ↔ ¬ Odd (u : ZMod q).val := by
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
  have hu0 : (u : ZMod q) ≠ 0 := Units.ne_zero u
  letI : NeZero (u : ZMod q) := ⟨hu0⟩
  rw [show (((-u : (ZMod q)ˣ) : ZMod q)) = -(u : ZMod q) by rfl]
  rw [ZMod.val_neg_of_ne_zero]
  rw [Nat.odd_sub (Nat.le_of_lt (ZMod.val_lt (u : ZMod q)))]
  rw [iff_true_intro hqodd, true_iff]
  exact Nat.not_odd_iff_even.symm

lemma sum_half_inv_sq_zero (hq1 : 1 < q) (hqodd : Odd q) (hq6 : Nat.Coprime q 6) :
    (∑ u ∈ halfUnits q, (((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2)) = 0 := by
  let f : (ZMod q)ˣ → ZMod q := fun u => (((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2)
  let E := Finset.univ.filter (fun u : (ZMod q)ˣ => ¬ Odd (u : ZMod q).val)
  have hEH : (∑ u ∈ E, f u) = ∑ u ∈ halfUnits q, f u := by
    apply Finset.sum_bijective (fun u : (ZMod q)ˣ => -u)
    · exact (Equiv.neg (ZMod q)ˣ).bijective
    · intro u
      simp only [E, halfUnits, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [odd_val_neg_iff q hq1 hqodd]
    · intro u hu
      dsimp [f]
      simp only [inv_neg, Units.val_neg, neg_sq]
  have hpart : (∑ u ∈ halfUnits q, f u) + (∑ u ∈ E, f u) =
      ∑ u : (ZMod q)ˣ, f u := by
    simpa [halfUnits, E] using
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun u : (ZMod q)ˣ => Odd (u : ZMod q).val) f
  have hfull : (∑ u : (ZMod q)ˣ, f u) = 0 := by
    dsimp [f]
    rw [show (∑ u : (ZMod q)ˣ, (((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2)) =
        ∑ u : (ZMod q)ˣ, ((u : ZMod q) ^ 2) by
      exact Equiv.sum_comp (Equiv.inv (ZMod q)ˣ) (fun u : (ZMod q)ˣ => ((u : ZMod q) ^ 2))]
    exact sum_units_sq_zero q hq6
  have htwo : (2 : ZMod q) * (∑ u ∈ halfUnits q, f u) = 0 := by
    calc
      (2 : ZMod q) * (∑ u ∈ halfUnits q, f u) =
          (∑ u ∈ halfUnits q, f u) + (∑ u ∈ halfUnits q, f u) := by ring
      _ = (∑ u ∈ halfUnits q, f u) + (∑ u ∈ E, f u) := by
        exact congrArg (fun z : ZMod q => (∑ u ∈ halfUnits q, f u) + z) hEH.symm
      _ = ∑ u : (ZMod q)ˣ, f u := hpart
      _ = 0 := hfull
  have hcop2 : Nat.Coprime 2 q :=
    (Nat.Coprime.of_dvd (by norm_num : 2 ∣ 6) (dvd_refl q) hq6.symm)
  exact ((ZMod.isUnit_iff_coprime 2 q).mpr hcop2).mul_right_eq_zero.mp htwo

end HalfUnits

section HalfShift

variable (q : ℕ) [NeZero q]

lemma double_val_formula
    (hq1 : 2 < q) (hqodd : Odd q) (u : (ZMod q)ˣ) :
    2 * (u : ZMod q).val = ((2 : ZMod q) * (u : ZMod q)).val +
      if Odd (((2 : ZMod q) * (u : ZMod q)).val) then q else 0 := by
  have hcval : (2 : ZMod q).val = 2 := ZMod.val_cast_of_lt hq1
  have hv : ((2 : ZMod q) * (u : ZMod q)).val =
      (2 * (u : ZMod q).val) % q := by
    rw [ZMod.val_mul, hcval]
  have hu_lt := ZMod.val_lt (u : ZMod q)
  by_cases hlow : 2 * (u : ZMod q).val < q
  · have hv' : ((2 : ZMod q) * (u : ZMod q)).val =
        2 * (u : ZMod q).val := by rw [hv, Nat.mod_eq_of_lt hlow]
    have heven : Even (((2 : ZMod q) * (u : ZMod q)).val) := by
      rw [hv']; exact even_two_mul _
    simp only [if_neg (Nat.not_odd_iff_even.mpr heven)]
    omega
  · have hqle : q ≤ 2 * (u : ZMod q).val := by omega
    have hlt2 : 2 * (u : ZMod q).val - q < q := by omega
    have hv' : ((2 : ZMod q) * (u : ZMod q)).val =
        2 * (u : ZMod q).val - q := by
      rw [hv, Nat.mod_eq_sub_mod hqle, Nat.mod_eq_of_lt hlt2]
    have hodd : Odd (((2 : ZMod q) * (u : ZMod q)).val) := by
      rw [hv']
      apply (Nat.odd_sub hqle).mpr
      exact iff_of_false
        (Nat.not_odd_iff_even.mpr (even_two_mul _))
        (Nat.not_even_iff_odd.mpr hqodd)
    simp only [if_pos hodd]
    omega

lemma halfA_eq_two_pow (hq2 : 2 < q) (hqodd : Odd q) (hq6 : Nat.Coprime q 6) :
    let A : ZMod (q ^ 3) := ∏ u ∈ halfUnits q,
      (1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))
    A = (2 : ZMod (q ^ 3)) ^ Fintype.card (ZMod q)ˣ := by
  have hcop2 : Nat.Coprime 2 q :=
    Nat.Coprime.of_dvd (by norm_num : 2 ∣ 6) (dvd_refl q) hq6.symm
  let c : (ZMod q)ˣ := ZMod.unitOfCoprime 2 hcop2
  let X : (ZMod q)ˣ → ZMod (q ^ 3) := fun u =>
    ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
  let A : ZMod (q ^ 3) := ∏ u ∈ halfUnits q,
    (1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))
  change A = (2 : ZMod (q ^ 3)) ^ Fintype.card (ZMod q)ˣ
  let B : ZMod (q ^ 3) := ∏ u : (ZMod q)ˣ, X u
  let BU : (ZMod (q ^ 3))ˣ := ∏ u : (ZMod q)ˣ, liftUnit q u
  have hBU : (BU : ZMod (q ^ 3)) = B := by simp [BU, B, X]
  have hBunit : IsUnit B := by rw [← hBU]; exact Units.isUnit BU
  have hdouble (u : (ZMod q)ˣ) :
      (2 : ZMod (q ^ 3)) * X u =
      (((c * u : (ZMod q)ˣ).1.val : ℕ) : ZMod (q ^ 3)) +
        if Odd (c * u : (ZMod q)ˣ).1.val then q else 0 := by
    simp only [X, liftUnit, ZMod.coe_unitOfCoprime]
    push_cast
    have hc : (c : ZMod q) = 2 := by
      simp [c, ZMod.coe_unitOfCoprime]
    have hv : ((c : ZMod q) * (u : ZMod q)).val =
        ((2 : ZMod q) * (u : ZMod q)).val := by rw [hc]
    rw [hv]
    have hz := congrArg (fun x : ℕ => (x : ZMod (q ^ 3)))
      (double_val_formula q hq2 hqodd u)
    push_cast at hz
    exact hz
  have hpoint (u : (ZMod q)ˣ) :
      ((((u : ZMod q).val : ℕ) : ZMod (q ^ 3)) +
          if Odd (u : ZMod q).val then q else 0) =
        X u * (if Odd (u : ZMod q).val then
          1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
          else 1) := by
    have hunit : X u *
        (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) = 1 := by
      exact Units.mul_inv _
    have hX : X u = (((u : ZMod q).val : ℕ) : ZMod (q ^ 3)) := by
      simp [X, liftUnit, ZMod.coe_unitOfCoprime]
    by_cases hu : Odd (u : ZMod q).val
    · simp only [if_pos hu]
      rw [mul_add, mul_one]
      have hreorder : X u * (q *
          (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) = q := by
        calc
          _ = q * (X u *
              (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) := by ring
          _ = q := by rw [hunit, mul_one]
      rw [hreorder]
      exact congrArg (fun z : ZMod (q ^ 3) => z + (q : ZMod (q ^ 3))) hX.symm
    · simp only [if_neg hu, Nat.cast_zero, add_zero, mul_one]
      exact hX.symm
  have hcond : (∏ x : (ZMod q)ˣ, if Odd (x : ZMod q).val then
        1 + (q : ℕ) * (((liftUnit q x)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
        else 1) = A := by
    change (∏ x : (ZMod q)ˣ, if Odd (x : ZMod q).val then
        1 + (q : ℕ) * (((liftUnit q x)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
        else 1) =
      ∏ x ∈ halfUnits q,
        (1 + (q : ℕ) * (((liftUnit q x)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))
    simpa [halfUnits] using
      (Finset.prod_filter (s := (Finset.univ : Finset (ZMod q)ˣ))
        (fun x : (ZMod q)ˣ => Odd (x : ZMod q).val)
        (fun x : (ZMod q)ˣ =>
          1 + (q : ℕ) * (((liftUnit q x)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))).symm

  have hprod : (2 : ZMod (q ^ 3)) ^ Fintype.card (ZMod q)ˣ * B = B * A := by
    calc
      (2 : ZMod (q ^ 3)) ^ Fintype.card (ZMod q)ˣ * B =
          ∏ u : (ZMod q)ˣ, (2 : ZMod (q ^ 3)) * X u := by
            change (2 : ZMod (q ^ 3)) ^ Fintype.card (ZMod q)ˣ *
              (∏ u : (ZMod q)ˣ, X u) = _
            rw [Finset.prod_mul_distrib]
            simp
      _ = ∏ u : (ZMod q)ˣ,
          ((((c * u : (ZMod q)ˣ).1.val : ℕ) : ZMod (q ^ 3)) +
            if Odd (c * u : (ZMod q)ˣ).1.val then q else 0) := by
              apply Finset.prod_congr rfl
              intro u hu
              exact hdouble u
      _ = ∏ v : (ZMod q)ˣ,
          ((((v : ZMod q).val : ℕ) : ZMod (q ^ 3)) +
            if Odd (v : ZMod q).val then q else 0) := by
              exact Fintype.prod_bijective (fun u : (ZMod q)ˣ => c * u)
                (Group.mulLeft_bijective c) _ _ (fun u => rfl)
      _ = ∏ u : (ZMod q)ˣ, X u *
          (if Odd (u : ZMod q).val then
            1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
            else 1) := by
              apply Finset.prod_congr rfl
              intro u hu
              exact hpoint u
      _ = B * A := by
        rw [Finset.prod_mul_distrib, hcond]
  have hc : B * (2 : ZMod (q ^ 3)) ^ Fintype.card (ZMod q)ˣ = B * A := by
    simpa [mul_comm] using hprod
  exact (hBunit.mul_left_cancel hc).symm

end HalfShift













section HalfPerturb

variable (q : ℕ) [NeZero q]

noncomputable def halfPerturb (j : ℕ) : ZMod (q ^ 3) :=
  ∏ u ∈ halfUnits q,
    (1 + (q * j : ℕ) *
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))

lemma halfPerturb_formula (j : ℕ) :
    let S : ZMod (q ^ 3) := ∑ u ∈ halfUnits q,
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
    let P : ZMod (q ^ 3) := pairSum (halfUnits q) (fun u =>
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))
    halfPerturb q j = 1 + (q : ZMod (q ^ 3)) * j * S +
      (q : ZMod (q ^ 3)) ^ 2 * j ^ 2 * P := by
  let f : (ZMod q)ˣ → ZMod (q ^ 3) := fun u =>
    (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
  let S : ZMod (q ^ 3) := ∑ u ∈ halfUnits q, f u
  let P : ZMod (q ^ 3) := pairSum (halfUnits q) f
  have hq3 : (q : ZMod (q ^ 3)) ^ 3 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hx3 : ((q : ZMod (q ^ 3)) * j) ^ 3 = 0 := by
    rw [mul_pow, hq3, zero_mul]
  rw [halfPerturb]
  push_cast
  rw [prod_one_add_trunc (halfUnits q) f ((q : ZMod (q ^ 3)) * j) hx3]
  dsimp [S, P, f]
  ring

lemma cast_half_inv_sq_zero (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)
      (∑ u ∈ halfUnits q,
        ((((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) ^ 2)) = 0 := by
  rw [map_sum]
  simp_rw [map_pow, cast_liftUnit_inv]
  have hq2 : Nat.Coprime q 2 :=
    Nat.Coprime.of_dvd (dvd_refl q) (by norm_num : 2 ∣ 6) hq6
  exact sum_half_inv_sq_zero q hq1 (Nat.coprime_two_right.mp hq2) hq6

lemma half_quadratic_relation (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) :
    let S : ZMod (q ^ 3) := ∑ u ∈ halfUnits q,
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
    let P : ZMod (q ^ 3) := pairSum (halfUnits q) (fun u =>
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))
    (q : ZMod (q ^ 3)) ^ 2 * (S ^ 2 - 2 * P) = 0 := by
  let f : (ZMod q)ˣ → ZMod (q ^ 3) := fun u =>
    (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
  let S : ZMod (q ^ 3) := ∑ u ∈ halfUnits q, f u
  let P : ZMod (q ^ 3) := pairSum (halfUnits q) f
  have hid : S ^ 2 - 2 * P = ∑ u ∈ halfUnits q, (f u) ^ 2 := by
    rw [two_mul_pairSum]
    ring
  change (q : ZMod (q ^ 3)) ^ 2 * (S ^ 2 - 2 * P) = 0
  rw [hid]
  apply q_sq_mul_eq_zero_of_cast_eq_zero q
  exact cast_half_inv_sq_zero q hq1 hq6

lemma halfPerturb_add (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) (j k : ℕ) :
    halfPerturb q (j + k) = halfPerturb q j * halfPerturb q k := by
  let S : ZMod (q ^ 3) := ∑ u ∈ halfUnits q,
    (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
  let P : ZMod (q ^ 3) := pairSum (halfUnits q) (fun u =>
    (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))
  have hrel : (q : ZMod (q ^ 3)) ^ 2 * (S ^ 2 - 2 * P) = 0 :=
    half_quadratic_relation q hq1 hq6
  have hq3 : (q : ZMod (q ^ 3)) ^ 3 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  dsimp [S, P] at hrel
  rw [halfPerturb_formula, halfPerturb_formula, halfPerturb_formula]
  push_cast
  have hq4 : (q : ZMod (q ^ 3)) ^ 4 = 0 := by
    rw [show (4 : ℕ) = 3 + 1 by omega, pow_add, hq3, zero_mul]
  ring_nf at hrel hq3 hq4 ⊢
  simp only [hq3, hq4, zero_mul, mul_zero, add_zero, sub_zero] at ⊢
  linear_combination
    (-(j : ZMod (q ^ 3)) * (k : ZMod (q ^ 3))) * hrel

lemma halfPerturb_mul (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) (j k : ℕ) :
    halfPerturb q (j * k) = (halfPerturb q j) ^ k := by
  induction k with
  | zero => simp [halfPerturb]
  | succ k ih =>
      calc
        halfPerturb q (j * (k + 1)) = halfPerturb q (j * k + j) := by rw [Nat.mul_succ]
        _ = halfPerturb q (j * k) * halfPerturb q j := halfPerturb_add q hq1 hq6 _ _
        _ = (halfPerturb q j) ^ k * halfPerturb q j := by rw [ih]
        _ = (halfPerturb q j) ^ (k + 1) := (pow_succ _ _).symm

lemma halfPerturb_two (hq2 : 2 < q) (hqodd : Odd q) (hq6 : Nat.Coprime q 6) :
    halfPerturb q 2 =
      (2 : ZMod (q ^ 3)) ^ (2 * Fintype.card (ZMod q)ˣ) := by
  rw [show halfPerturb q 2 = (halfPerturb q 1) ^ 2 by
    simpa using halfPerturb_mul q (by omega) hq6 1 2]
  have hA := halfA_eq_two_pow q hq2 hqodd hq6
  change (halfPerturb q 1) ^ 2 = _
  rw [show halfPerturb q 1 =
      (2 : ZMod (q ^ 3)) ^ Fintype.card (ZMod q)ˣ by
    simpa [halfPerturb] using hA]
  rw [← pow_mul]
  congr 1
  omega

end HalfPerturb

section OddBlocks

variable (q : ℕ) [NeZero q]

noncomputable def oddHalfBlock (j : ℕ) : ZMod (q ^ 3) :=
  ∏ u ∈ halfUnits q,
    ((((u : ZMod q).val + 2 * q * j : ℕ)) : ZMod (q ^ 3))

noncomputable def oddFullBlock : ZMod (q ^ 3) :=
  ∏ u : (ZMod q)ˣ,
    ((((u : ZMod q).val + if Odd (u : ZMod q).val then 0 else q : ℕ)) :
      ZMod (q ^ 3))

lemma oddHalfBlock_factor (j : ℕ) :
    oddHalfBlock q j = oddHalfBlock q 0 * halfPerturb q (2 * j) := by
  rw [oddHalfBlock, oddHalfBlock, halfPerturb]
  simp only [Nat.mul_zero, Nat.add_zero]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u hu
  have hunit : (((u : ZMod q).val : ℕ) : ZMod (q ^ 3)) *
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) = 1 := by
    rw [← liftUnit_val]
    exact Units.mul_inv _
  have hval : (((u : ZMod q).val : ℕ) : ZMod (q ^ 3)) =
      ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) := liftUnit_val q u |>.symm
  push_cast
  rw [hval, mul_add, mul_one]
  congr 1
  symm
  calc
    ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) *
        ((q : ZMod (q ^ 3)) * (2 * j) *
          (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) =
      ((q : ZMod (q ^ 3)) * (2 * j)) *
        (((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) *
          (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) := by ring
    _ = (q : ZMod (q ^ 3)) * (2 * j) := by rw [Units.mul_inv, mul_one]
    _ = 2 * q * j := by ring

lemma oddHalfBlock_eq (hq2 : 2 < q) (hq6 : Nat.Coprime q 6) (j : ℕ) :
    oddHalfBlock q j = oddHalfBlock q 0 *
      ((2 : ZMod (q ^ 3)) ^ (2 * Fintype.card (ZMod q)ˣ)) ^ j := by
  have hqodd : Odd q := by
    apply Nat.coprime_two_right.mp
    exact Nat.Coprime.of_dvd (dvd_refl q) (by norm_num : 2 ∣ 6) hq6
  rw [oddHalfBlock_factor]
  rw [show halfPerturb q (2 * j) = (halfPerturb q 2) ^ j by
    exact halfPerturb_mul q (by omega) hq6 2 j]
  rw [halfPerturb_two q hq2 hqodd hq6]

lemma oddFullBlock_factor :
    oddFullBlock q =
      (∏ u : (ZMod q)ˣ,
        ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) *
      ∏ u : (ZMod q)ˣ, (if Odd (u : ZMod q).val then 1 else
        1 + (q : ℕ) *
          (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) := by
  rw [oddFullBlock, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u hu
  have hval : (((u : ZMod q).val : ℕ) : ZMod (q ^ 3)) =
      ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) := liftUnit_val q u |>.symm
  have hunit : ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) *
      (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) = 1 := Units.mul_inv _
  by_cases ho : Odd (u : ZMod q).val
  · simp only [if_pos ho, Nat.add_zero, Nat.cast_zero, mul_one]
    exact hval
  · simp only [if_neg ho]
    push_cast
    rw [hval, mul_add, mul_one]
    congr 1
    symm
    calc
      ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) *
          ((q : ZMod (q ^ 3)) *
            (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) =
        (q : ZMod (q ^ 3)) *
          (((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) *
            (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) := by ring
      _ = q := by rw [Units.mul_inv, mul_one]

lemma oddFullBlock_mul_two_pow (hq2 : 2 < q) (hq6 : Nat.Coprime q 6) :
    oddFullBlock q * (2 : ZMod (q ^ 3)) ^ Fintype.card (ZMod q)ˣ =
      ∏ u : (ZMod q)ˣ,
        ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) := by
  have hqodd : Odd q := by
    apply Nat.coprime_two_right.mp
    exact Nat.Coprime.of_dvd (dvd_refl q) (by norm_num : 2 ∣ 6) hq6
  let B : ZMod (q ^ 3) := ∏ u : (ZMod q)ˣ,
    ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
  let AO : ZMod (q ^ 3) := ∏ u ∈ halfUnits q,
    (1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))
  let AE : ZMod (q ^ 3) := ∏ u : (ZMod q)ˣ, if Odd (u : ZMod q).val then 1 else
    1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
  have hfull : AO * AE = 1 := by
    have hp := perturb_prod_eq_one q (by omega) hq6 1
    change AO * AE = 1
    rw [show AO = ∏ u : (ZMod q)ˣ, if Odd (u : ZMod q).val then
        1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) else 1 by
      dsimp [AO]
      simpa [halfUnits] using
        (Finset.prod_filter (s := (Finset.univ : Finset (ZMod q)ˣ))
          (fun u : (ZMod q)ˣ => Odd (u : ZMod q).val)
          (fun u : (ZMod q)ˣ =>
            1 + (q : ℕ) *
              (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))))]
    dsimp [AE]
    rw [← Finset.prod_mul_distrib]
    change (∏ u : (ZMod q)ˣ,
      (if Odd (u : ZMod q).val then
        1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) else 1) *
      (if Odd (u : ZMod q).val then 1 else
        1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))) = 1
    rw [show (∏ u : (ZMod q)ˣ,
      (if Odd (u : ZMod q).val then
        1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)) else 1) *
      (if Odd (u : ZMod q).val then 1 else
        1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3)))) =
      ∏ u : (ZMod q)ˣ,
        (1 + (q : ℕ) * (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))) by
      apply Finset.prod_congr rfl
      intro u hu
      by_cases h : Odd (u : ZMod q).val <;> simp [h]]
    simpa using hp
  have hA : AO = (2 : ZMod (q ^ 3)) ^ Fintype.card (ZMod q)ˣ := by
    simpa [AO] using halfA_eq_two_pow q hq2 hqodd hq6
  have hC : oddFullBlock q = B * AE := by
    simpa [B, AE] using oddFullBlock_factor q
  rw [hC, ← hA]
  calc
    B * AE * AO = B * (AO * AE) := by ring
    _ = B := by rw [hfull, mul_one]

end OddBlocks

section OddFactorialStrip

open scoped Nat

def oddNumbers (m : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (m + 1)).filter Odd

def punitDbl (p m : ℕ) : ℕ :=
  ∏ x ∈ (oddNumbers m).filter (fun x => ¬ p ∣ x), x

lemma prod_range_odd_eq_doubleFactorial (b : ℕ) :
    (∏ t ∈ Finset.range (b + 1), (2 * t + 1)) = (2 * b + 1)‼ := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [show b + 1 + 1 = (b + 1) + 1 by omega, Finset.prod_range_succ]
      rw [show 2 * (b + 1) + 1 = (2 * b + 1) + 2 by omega]
      rw [Nat.doubleFactorial_add_two, ih]
      ring

lemma oddNumbers_prod (b : ℕ) :
    ∏ x ∈ oddNumbers (2 * b + 1), x = (2 * b + 1)‼ := by
  calc
    (∏ x ∈ oddNumbers (2 * b + 1), x) =
        ∏ t ∈ Finset.range (b + 1), (2 * t + 1) := by
      symm
      apply Finset.prod_bij
        (s := Finset.range (b + 1))
        (t := oddNumbers (2 * b + 1))
        (f := fun t => 2 * t + 1)
        (g := id)
        (fun t ht => 2 * t + 1)
      · intro t ht
        simp only [Finset.mem_range] at ht
        simp [oddNumbers]
        omega
      · intro t1 ht1 t2 ht2 heq
        omega
      · intro x hx
        simp only [oddNumbers, Finset.mem_filter, Finset.mem_Ico] at hx
        rcases hx.2 with ⟨t, ht⟩
        refine ⟨t, ?_, ?_⟩
        · simp only [Finset.mem_range]
          omega
        · omega
      · intro t ht
        rfl
    _ = _ := prod_range_odd_eq_doubleFactorial b

lemma prod_odd_multiples (a b : ℕ) (ha : 1 ≤ a) :
    ∏ x ∈ (oddNumbers ((2 * a + 1) * (2 * b + 1))).filter
        (fun x => (2 * a + 1) ∣ x), x =
      (2 * a + 1) ^ (b + 1) * (2 * b + 1)‼ := by
  let p := 2 * a + 1
  let m := 2 * b + 1
  have hp : 0 < p := by dsimp [p]; omega
  calc
    (∏ x ∈ (oddNumbers (p * m)).filter (fun x => p ∣ x), x) =
        ∏ t ∈ Finset.range (b + 1), p * (2 * t + 1) := by
      symm
      apply Finset.prod_bij
        (s := Finset.range (b + 1))
        (t := (oddNumbers (p * m)).filter (fun x => p ∣ x))
        (f := fun t => p * (2 * t + 1))
        (g := id)
        (fun t ht => p * (2 * t + 1))
      · intro t ht
        simp only [Finset.mem_range] at ht
        simp only [Finset.mem_filter, oddNumbers, Finset.mem_Ico]
        constructor
        · constructor
          · constructor
            · exact mul_pos hp (by omega)
            · dsimp [p, m]
              nlinarith
          · exact Nat.odd_mul.mpr
              ⟨by dsimp [p]; exact ⟨a, by omega⟩, ⟨t, by omega⟩⟩
        · exact dvd_mul_right p (2 * t + 1)
      · intro t1 ht1 t2 ht2 heq
        have heq' : 2 * t1 + 1 = 2 * t2 + 1 :=
          Nat.eq_of_mul_eq_mul_left hp heq
        omega
      · intro x hx
        simp only [Finset.mem_filter, oddNumbers, Finset.mem_Ico] at hx
        obtain ⟨y, hy⟩ := hx.2
        have hyodd : Odd y := by
          apply Nat.Odd.of_mul_right
          rw [← hy]
          exact hx.1.2
        rcases hyodd with ⟨t, ht⟩
        refine ⟨t, ?_, ?_⟩
        · simp only [Finset.mem_range]
          dsimp [p, m] at hx hy
          nlinarith
        · rw [← ht, ← hy]
      · intro t ht
        rfl
    _ = (∏ _t ∈ Finset.range (b + 1), p) *
        ∏ t ∈ Finset.range (b + 1), (2 * t + 1) := by
      rw [← Finset.prod_mul_distrib]
    _ = p ^ (b + 1) * (2 * b + 1)‼ := by
      rw [Finset.prod_const, Finset.card_range, prod_range_odd_eq_doubleFactorial]

lemma doubleFactorial_strip (a b : ℕ) (ha : 1 ≤ a) :
    ((2 * a + 1) * (2 * b + 1))‼ =
      (2 * a + 1) ^ (b + 1) * (2 * b + 1)‼ *
        punitDbl (2 * a + 1) ((2 * a + 1) * (2 * b + 1)) := by
  have harg : 2 * (2 * a * b + a + b) + 1 =
      (2 * a + 1) * (2 * b + 1) := by ring
  rw [← harg]
  rw [← oddNumbers_prod (2 * a * b + a + b)]
  rw [harg]
  rw [← Finset.prod_filter_mul_prod_filter_not
    (oddNumbers ((2 * a + 1) * (2 * b + 1)))
    (fun x => (2 * a + 1) ∣ x) (fun x => x)]
  rw [prod_odd_multiples a b ha]
  rfl

lemma punitDbl_coprime (p m : ℕ) (hp : p.Prime) :
    p.Coprime (punitDbl p m) := by
  rw [punitDbl]
  apply Nat.Coprime.prod_right
  intro x hx
  simp only [Finset.mem_filter] at hx
  exact hp.coprime_iff_not_dvd.mpr hx.2

end OddFactorialStrip

section OddLiftPerturb

variable (q : ℕ) [NeZero q]

noncomputable def oddInv (u : (ZMod q)ˣ) : ZMod (q ^ 3) :=
  let z : ZMod (q ^ 3) :=
    (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
  if Odd (u : ZMod q).val then z
  else z - q * z ^ 2 + (q : ZMod (q ^ 3)) ^ 2 * z ^ 3

lemma oddRep_mul_oddInv (u : (ZMod q)ˣ) :
    ((((u : ZMod q).val + if Odd (u : ZMod q).val then 0 else q : ℕ)) :
        ZMod (q ^ 3)) * oddInv q u = 1 := by
  let z : ZMod (q ^ 3) :=
    (((liftUnit q u)⁻¹ : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
  let x : ZMod (q ^ 3) :=
    ((liftUnit q u : (ZMod (q ^ 3))ˣ) : ZMod (q ^ 3))
  have hxz : x * z = 1 := Units.mul_inv _
  have hq3 : (q : ZMod (q ^ 3)) ^ 3 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hval : (((u : ZMod q).val : ℕ) : ZMod (q ^ 3)) = x := liftUnit_val q u |>.symm
  by_cases ho : Odd (u : ZMod q).val
  · simp only [if_pos ho, Nat.add_zero, oddInv, z]
    exact hxz
  · simp only [if_neg ho, oddInv, z]
    push_cast
    rw [hval]
    ring_nf at hxz hq3 ⊢
    linear_combination
      (1 - (q : ZMod (q ^ 3)) * z + (q : ZMod (q ^ 3)) ^ 2 * z ^ 2) * hxz +
      z ^ 3 * hq3

lemma sum_even_inv_sq_zero (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) :
    (∑ u ∈ (Finset.univ.filter (fun u : (ZMod q)ˣ => ¬ Odd (u : ZMod q).val)),
      (((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2)) = 0 := by
  have hqodd : Odd q := by
    apply Nat.coprime_two_right.mp
    exact Nat.Coprime.of_dvd (dvd_refl q) (by norm_num : 2 ∣ 6) hq6
  let f : (ZMod q)ˣ → ZMod q := fun u => (((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2)
  have hpart : (∑ u ∈ halfUnits q, f u) +
      (∑ u ∈ Finset.univ.filter (fun u : (ZMod q)ˣ => ¬ Odd (u : ZMod q).val), f u) =
      ∑ u : (ZMod q)ˣ, f u := by
    simpa [halfUnits] using
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun u : (ZMod q)ˣ => Odd (u : ZMod q).val) f
  have hodd : (∑ u ∈ halfUnits q, f u) = 0 :=
    sum_half_inv_sq_zero q hq1 hqodd hq6
  have hfull : (∑ u : (ZMod q)ˣ, f u) = 0 := by
    rw [show (∑ u : (ZMod q)ˣ, f u) =
        ∑ u : (ZMod q)ˣ, ((u : ZMod q) ^ 2) by
      exact Equiv.sum_comp (Equiv.inv (ZMod q)ˣ)
        (fun u : (ZMod q)ˣ => ((u : ZMod q) ^ 2))]
    exact sum_units_sq_zero q hq6
  rw [hodd, zero_add, hfull] at hpart
  exact hpart

lemma cast_oddInv (u : (ZMod q)ˣ) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q) (oddInv q u) =
      ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  rw [oddInv]
  by_cases ho : Odd (u : ZMod q).val
  · simp only [if_pos ho]
    exact cast_liftUnit_inv q u
  · simp only [if_neg ho, map_add, map_sub, map_mul, map_pow]
    rw [cast_liftUnit_inv]
    simp

lemma cast_oddInv_to_sq (u : (ZMod q)ˣ) :
    ZMod.castHom (pow_dvd_pow q (by norm_num : 2 ≤ 3)) (ZMod (q ^ 2)) (oddInv q u) =
      let z : ZMod (q ^ 2) :=
        (((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2))
      if Odd (u : ZMod q).val then z else z - q * z ^ 2 := by
  rw [oddInv]
  by_cases ho : Odd (u : ZMod q).val
  · simp only [if_pos ho]
    exact cast_liftUnit_inv_to_sq q u
  · simp only [if_neg ho, map_add, map_sub, map_mul, map_pow]
    rw [cast_liftUnit_inv_to_sq]
    simp only [map_natCast]
    have hq2 : (q : ZMod (q ^ 2)) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hq2, zero_mul, add_zero]

lemma cast_sum_oddInv_to_sq_zero (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) :
    ZMod.castHom (pow_dvd_pow q (by norm_num : 2 ≤ 3)) (ZMod (q ^ 2))
      (∑ u : (ZMod q)ˣ, oddInv q u) = 0 := by
  let z : (ZMod q)ˣ → ZMod (q ^ 2) := fun u =>
    (((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2))
  let E := Finset.univ.filter (fun u : (ZMod q)ˣ => ¬ Odd (u : ZMod q).val)
  have hmap : ZMod.castHom (pow_dvd_pow q (by norm_num : 2 ≤ 3)) (ZMod (q ^ 2))
      (∑ u : (ZMod q)ˣ, oddInv q u) =
      (∑ u : (ZMod q)ˣ, z u) - (q : ZMod (q ^ 2)) * ∑ u ∈ E, (z u) ^ 2 := by
    rw [map_sum]
    simp_rw [cast_oddInv_to_sq]
    rw [Finset.sum_ite]
    dsimp [E]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun u : (ZMod q)ˣ => Odd (u : ZMod q).val) z]
    ring
  have hsum : (∑ u : (ZMod q)ˣ, z u) = 0 := by
    exact sum_liftUnit2_inv_zero q hq1 hq6
  have hcastE : ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)
      (∑ u ∈ E, (z u) ^ 2) = 0 := by
    rw [map_sum]
    dsimp [z, E]
    change (∑ u ∈ Finset.univ.filter (fun u : (ZMod q)ˣ => ¬ Odd (u : ZMod q).val),
      ZMod.castHom (dvd_pow_self q (by norm_num : 2 ≠ 0)) (ZMod q)
        ((((liftUnit2 q u)⁻¹ : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) ^ 2)) = 0
    simp_rw [map_pow, cast_liftUnit2_inv]
    exact sum_even_inv_sq_zero q hq1 hq6
  have hqE : (q : ZMod (q ^ 2)) * ∑ u ∈ E, (z u) ^ 2 = 0 :=
    q_mul_eq_zero_of_cast_eq_zero q _ hcastE
  rw [hmap, hsum, hqE, zero_sub, neg_zero]

lemma cast_pairSum_oddInv_zero (hq6 : Nat.Coprime q 6) :
    ZMod.castHom (dvd_pow_self q (by norm_num : 3 ≠ 0)) (ZMod q)
      (pairSum Finset.univ (oddInv q)) = 0 := by
  rw [map_pairSum]
  simp_rw [cast_oddInv]
  have h := cast_pairSum_liftUnit_inv_zero q hq6
  rw [map_pairSum] at h
  simp_rw [cast_liftUnit_inv] at h
  exact h

noncomputable def oddFullBlockShift (j : ℕ) : ZMod (q ^ 3) :=
  ∏ u : (ZMod q)ˣ,
    ((((u : ZMod q).val + if Odd (u : ZMod q).val then 0 else q) + 2 * q * j : ℕ) :
      ZMod (q ^ 3))

lemma oddFullBlockShift_factor (j : ℕ) :
    oddFullBlockShift q j = oddFullBlock q *
      ∏ u : (ZMod q)ˣ,
        (1 + (2 * q * j : ℕ) * oddInv q u) := by
  rw [oddFullBlockShift, oddFullBlock, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u hu
  let r : ZMod (q ^ 3) :=
    (((u : ZMod q).val : ℕ) : ZMod (q ^ 3)) +
      if Odd (u : ZMod q).val then 0 else (q : ZMod (q ^ 3))
  have hinv : r * oddInv q u = 1 := by
    dsimp [r]
    have h := oddRep_mul_oddInv q u
    push_cast at h
    exact h
  push_cast
  change r + 2 * q * j = r * (1 + 2 * q * j * oddInv q u)
  rw [mul_add, mul_one]
  congr 1
  symm
  calc
    r * (2 * q * j * oddInv q u) =
        2 * q * j * (r * oddInv q u) := by ring
    _ = 2 * q * j := by rw [hinv, mul_one]

lemma oddFullBlockShift_eq (hq1 : 1 < q) (hq6 : Nat.Coprime q 6) (j : ℕ) :
    oddFullBlockShift q j = oddFullBlock q := by
  rw [oddFullBlockShift_factor]
  have hq3 : (q : ZMod (q ^ 3)) ^ 3 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hx3 : ((2 * q * j : ℕ) : ZMod (q ^ 3)) ^ 3 = 0 := by
    push_cast
    ring_nf
    simp [hq3]
  rw [prod_one_add_trunc Finset.univ (oddInv q)
    ((2 * q * j : ℕ) : ZMod (q ^ 3)) hx3]
  have hqS : (q : ZMod (q ^ 3)) * (∑ u : (ZMod q)ˣ, oddInv q u) = 0 :=
    q_mul_eq_zero_of_cast_sq_eq_zero q _ (cast_sum_oddInv_to_sq_zero q hq1 hq6)
  have hq2P : (q : ZMod (q ^ 3)) ^ 2 * pairSum Finset.univ (oddInv q) = 0 :=
    q_sq_mul_eq_zero_of_cast_eq_zero q _ (cast_pairSum_oddInv_zero q hq6)
  push_cast
  ring_nf at hqS hq2P ⊢
  simp [hqS, hq2P]

end OddLiftPerturb

section PunitOddBlocks

open scoped Nat

def punitOddFullBlockNat (p q j : ℕ) : ℕ :=
  ∏ x ∈ (Finset.Ico (2 * q * j + 1) (2 * q * (j + 1) + 1)).filter
      (fun x => Odd x ∧ ¬ p ∣ x), x

def punitOddHalfBlockNat (p q j : ℕ) : ℕ :=
  ∏ x ∈ (Finset.Ico (2 * q * j + 1) (2 * q * j + q + 1)).filter
      (fun x => Odd x ∧ ¬ p ∣ x), x

lemma punitOddFullBlockNat_eq_units {p r : ℕ} [NeZero (p ^ r)] (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r)
    (j : ℕ) :
    punitOddFullBlockNat p (p ^ r) j =
      ∏ u : (ZMod (p ^ r))ˣ,
        (2 * (p ^ r) * j +
          ((u : ZMod (p ^ r)).val + if Odd (u : ZMod (p ^ r)).val then 0 else p ^ r)) := by
  let q := p ^ r
  have hq1 : 1 < q := one_lt_pow₀ hp.one_lt hr.ne'
  have hpq : p ∣ q := dvd_pow_self p hr.ne'
  have hqodd : Odd q := (hp.odd_of_ne_two (by omega)).pow
  haveI : NeZero q := ⟨by omega⟩
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
  symm
  change (Finset.univ : Finset (ZMod q)ˣ).prod (fun u =>
      2 * q * j + ((u : ZMod q).val + if Odd (u : ZMod q).val then 0 else q)) =
    ∏ x ∈ (Finset.Ico (2 * q * j + 1) (2 * q * (j + 1) + 1)).filter
      (fun x => Odd x ∧ ¬ p ∣ x), x
  apply Finset.prod_bij
    (s := (Finset.univ : Finset (ZMod q)ˣ))
    (t := (Finset.Ico (2 * q * j + 1) (2 * q * (j + 1) + 1)).filter
      (fun x => Odd x ∧ ¬ p ∣ x))
    (f := fun u : (ZMod q)ˣ =>
      2 * q * j + ((u : ZMod q).val + if Odd (u : ZMod q).val then 0 else q))
    (g := id)
    (fun u hu => 2 * q * j +
      ((u : ZMod q).val + if Odd (u : ZMod q).val then 0 else q))
  · intro u hu
    have hvlt := ZMod.val_lt (u : ZMod q)
    have hvpos : 0 < (u : ZMod q).val := by
      exact Nat.pos_of_ne_zero (fun h => Units.ne_zero u ((ZMod.val_eq_zero _).mp h))
    have hnp : ¬ p ∣ (u : ZMod q).val := by
      exact hp.coprime_iff_not_dvd.mp
        (Nat.Coprime.coprime_dvd_right hpq (ZMod.val_coe_unit_coprime u)).symm
    simp only [Finset.mem_filter, Finset.mem_Ico]
    by_cases ho : Odd (u : ZMod q).val
    · simp only [if_pos ho, Nat.add_zero]
      constructor
      · constructor
        · omega
        · rw [show 2 * q * (j + 1) = 2 * q * j + 2 * q by ring]
          omega
      · constructor
        · exact Even.add_odd (by simpa [mul_assoc] using even_two_mul (q * j)) ho
        · intro hd
          have hshift : p ∣ 2 * q * j := by
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              dvd_mul_of_dvd_right hpq (2 * j)
          exact hnp ((Nat.dvd_add_iff_right hshift).mpr hd)
    · simp only [if_neg ho]
      have he : Even (u : ZMod q).val := Nat.not_odd_iff_even.mp ho
      have htailodd : Odd ((u : ZMod q).val + q) := Even.add_odd he hqodd
      constructor
      · constructor
        · omega
        · rw [show 2 * q * (j + 1) = 2 * q * j + 2 * q by ring]
          omega
      · constructor
        · exact Even.add_odd (by simpa [mul_assoc] using even_two_mul (q * j)) htailodd
        · intro hd
          have hshift : p ∣ 2 * q * j := by
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              dvd_mul_of_dvd_right hpq (2 * j)
          have htail : p ∣ (u : ZMod q).val + q :=
            (Nat.dvd_add_iff_right hshift).mpr hd
          exact hnp ((Nat.dvd_add_iff_left hpq).mpr htail)
  · intro u1 h1 u2 h2 heq
    have htail : (u1 : ZMod q).val + (if Odd (u1 : ZMod q).val then 0 else q) =
        (u2 : ZMod q).val + (if Odd (u2 : ZMod q).val then 0 else q) := by omega
    have hv : (u1 : ZMod q).val = (u2 : ZMod q).val := by
      by_cases hodd1 : Odd (u1 : ZMod q).val <;>
      by_cases hodd2 : Odd (u2 : ZMod q).val
      · simp [hodd1, hodd2] at htail
        exact htail
      · simp [hodd1, hodd2] at htail
        have hp1 : (u1 : ZMod q).val < q := ZMod.val_lt _
        omega
      · simp [hodd1, hodd2] at htail
        have hp2 : (u2 : ZMod q).val < q := ZMod.val_lt _
        omega
      · simp [hodd1, hodd2] at htail
        omega
    apply Units.ext
    exact ZMod.val_injective q hv
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    let d := x - 2 * q * j
    have hdpos : 0 < d := by dsimp [d]; omega
    have hdle : d ≤ 2 * q := by dsimp [d]; ring_nf at hx ⊢; omega
    have hdodd : Odd d := by
      have hev : Even (2 * q * j) := by
        simpa [mul_assoc] using even_two_mul (q * j)
      exact (Nat.odd_sub (by omega)).mpr (iff_of_true hx.2.1 hev)
    have hdnp : ¬ p ∣ d := by
      intro hpd
      apply hx.2.2
      have hs : p ∣ 2 * q * j := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          dvd_mul_of_dvd_right hpq (2 * j)
      have hxd : x = d + 2 * q * j := by dsimp [d]; omega
      rw [hxd]
      exact dvd_add hpd hs
    have hdneq : d ≠ q := by intro h; apply hdnp; rw [h]; exact hpq
    have hvpos : 0 < d % q := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hdnp (dvd_trans hpq (Nat.dvd_of_mod_eq_zero hz))
    have hvcop : (d % q).Coprime q := by
      dsimp [q]
      apply (hp.coprime_iff_not_dvd.mpr ?_).symm.pow_right r
      intro hpd
      have hqpd : p ∣ q := hpq
      have : p ∣ d := by
        rw [← Nat.mod_add_div d q]
        exact dvd_add hpd (dvd_mul_of_dvd_left hqpd (d / q))
      exact hdnp this
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime (d % q) hvcop
    have huval : (u : ZMod q).val = d % q := by
      dsimp [u]
      exact ZMod.val_cast_of_lt (Nat.mod_lt _ (by omega))
    refine ⟨u, Finset.mem_univ _, ?_⟩
    rw [huval]
    have hdlt2 : d < 2 * q := lt_of_le_of_ne hdle (fun h => by
      have : Even d := by rw [h]; exact even_two_mul q
      exact (Nat.not_even_iff_odd.mpr hdodd) this)
    by_cases hdlt : d < q
    · have hmod : d % q = d := Nat.mod_eq_of_lt hdlt
      rw [hmod, if_pos hdodd]
      dsimp [d]
      omega
    · have hqle : q ≤ d := by omega
      have hmod : d % q = d - q := by
        rw [Nat.mod_eq_sub_mod hqle, Nat.mod_eq_of_lt (by omega)]
      have heven : Even (d - q) := by
        apply (Nat.even_sub hqle).mpr
        exact iff_of_false
          (Nat.not_even_iff_odd.mpr hdodd)
          (Nat.not_even_iff_odd.mpr hqodd)
      rw [hmod, if_neg (Nat.not_odd_iff_even.mpr heven)]
      dsimp [d]
      omega
  · intro u hu
    rfl

end PunitOddBlocks

section PunitOddBlockCasts

open scoped Nat

lemma punitOddHalfBlockNat_eq_units {p r : ℕ} [NeZero (p ^ r)] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 0 < r) (j : ℕ) :
    punitOddHalfBlockNat p (p ^ r) j =
      ∏ u ∈ halfUnits (p ^ r), (2 * (p ^ r) * j + (u : ZMod (p ^ r)).val) := by
  let q := p ^ r
  have hq1 : 1 < q := one_lt_pow₀ hp.one_lt hr.ne'
  have hpq : p ∣ q := dvd_pow_self p hr.ne'
  haveI : NeZero q := ⟨by omega⟩
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
  symm
  change (halfUnits q).prod (fun u => 2 * q * j + (u : ZMod q).val) =
    ∏ x ∈ (Finset.Ico (2 * q * j + 1) (2 * q * j + q + 1)).filter
      (fun x => Odd x ∧ ¬ p ∣ x), x
  apply Finset.prod_bij
    (s := halfUnits q)
    (t := (Finset.Ico (2 * q * j + 1) (2 * q * j + q + 1)).filter
      (fun x => Odd x ∧ ¬ p ∣ x))
    (f := fun u : (ZMod q)ˣ => 2 * q * j + (u : ZMod q).val)
    (g := id)
    (fun u hu => 2 * q * j + (u : ZMod q).val)
  · intro u hu
    have huodd : Odd (u : ZMod q).val := by simpa [halfUnits] using hu
    have hvlt := ZMod.val_lt (u : ZMod q)
    have hvpos : 0 < (u : ZMod q).val := by
      exact Nat.pos_of_ne_zero (fun h => Units.ne_zero u ((ZMod.val_eq_zero _).mp h))
    have hnp : ¬ p ∣ (u : ZMod q).val := by
      exact hp.coprime_iff_not_dvd.mp
        (Nat.Coprime.coprime_dvd_right hpq (ZMod.val_coe_unit_coprime u)).symm
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · constructor <;> omega
    · constructor
      · exact Even.add_odd (by simpa [mul_assoc] using even_two_mul (q * j)) huodd
      · intro hd
        have hs : p ∣ 2 * q * j := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            dvd_mul_of_dvd_right hpq (2 * j)
        exact hnp ((Nat.dvd_add_iff_right hs).mpr hd)
  · intro u1 h1 u2 h2 heq
    apply Units.ext
    apply ZMod.val_injective q
    omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    let d := x - 2 * q * j
    have hdpos : 0 < d := by dsimp [d]; omega
    have hdle : d ≤ q := by dsimp [d]; omega
    have hdodd : Odd d := by
      have hev : Even (2 * q * j) := by
        simpa [mul_assoc] using even_two_mul (q * j)
      exact (Nat.odd_sub (by omega)).mpr (iff_of_true hx.2.1 hev)
    have hdnp : ¬ p ∣ d := by
      intro hpd
      apply hx.2.2
      have hs : p ∣ 2 * q * j := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          dvd_mul_of_dvd_right hpq (2 * j)
      have hxd : x = d + 2 * q * j := by dsimp [d]; omega
      rw [hxd]
      exact dvd_add hpd hs
    have hdneq : d ≠ q := by intro h; apply hdnp; rw [h]; exact hpq
    have hdlt : d < q := lt_of_le_of_ne hdle hdneq
    have hdcop : d.Coprime q := by
      dsimp [q]
      exact (hp.coprime_iff_not_dvd.mpr hdnp).symm.pow_right r
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime d hdcop
    have huval : (u : ZMod q).val = d := by
      dsimp [u]
      exact ZMod.val_cast_of_lt hdlt
    refine ⟨u, ?_, ?_⟩
    · simp [halfUnits, huval, hdodd]
    · rw [huval]
      dsimp [d]
      omega
  · intro u hu
    rfl

lemma punitOddFullBlockNat_cast {p r : ℕ} [NeZero (p ^ r)]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) (j : ℕ) :
    ((punitOddFullBlockNat p (p ^ r) j : ℕ) : ZMod ((p ^ r) ^ 3)) =
      oddFullBlockShift (p ^ r) j := by
  rw [punitOddFullBlockNat_eq_units hp hp5 hr]
  rw [oddFullBlockShift]
  push_cast
  apply Finset.prod_congr rfl
  intro u hu
  push_cast
  ring

lemma punitOddHalfBlockNat_cast {p r : ℕ} [NeZero (p ^ r)]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) (j : ℕ) :
    ((punitOddHalfBlockNat p (p ^ r) j : ℕ) : ZMod ((p ^ r) ^ 3)) =
      oddHalfBlock (p ^ r) j := by
  rw [punitOddHalfBlockNat_eq_units hp hp5 hr]
  rw [oddHalfBlock]
  push_cast
  apply Finset.prod_congr rfl
  intro u hu
  push_cast
  ring

lemma punitDbl_even_blocks (p q d : ℕ) :
    punitDbl p (2 * q * d) =
      ∏ j ∈ Finset.range d, punitOddFullBlockNat p q j := by
  induction d with
  | zero => simp [punitDbl, oddNumbers, punitOddFullBlockNat]
  | succ d ih =>
      have hend : 2 * q * (d + 1) = 2 * q * d + 2 * q := by ring
      have hsplit : Finset.Ico 1 (2 * q * d + 2 * q + 1) =
          Finset.Ico 1 (2 * q * d + 1) ∪
            Finset.Ico (2 * q * d + 1) (2 * q * d + 2 * q + 1) := by
        rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
      have hdis : Disjoint
          ((Finset.Ico 1 (2 * q * d + 1)).filter (fun x => Odd x ∧ ¬ p ∣ x))
          ((Finset.Ico (2 * q * d + 1) (2 * q * d + 2 * q + 1)).filter
            (fun x => Odd x ∧ ¬ p ∣ x)) := by
        apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_Ico] at hx1 hx2
        omega
      rw [punitDbl, oddNumbers, hend, hsplit, Finset.filter_filter,
        Finset.filter_union, Finset.prod_union hdis]
      have hfirst : (∏ x ∈ (Finset.Ico 1 (2 * q * d + 1)).filter
          (fun x => Odd x ∧ ¬ p ∣ x), x) = punitDbl p (2 * q * d) := by
        simp [punitDbl, oddNumbers, Finset.filter_filter]
      have hsecond : (∏ x ∈
          (Finset.Ico (2 * q * d + 1) (2 * q * d + 2 * q + 1)).filter
            (fun x => Odd x ∧ ¬ p ∣ x), x) = punitOddFullBlockNat p q d := by
        rw [punitOddFullBlockNat]
        congr 3 <;> ring
      rw [hfirst, hsecond, ih, Finset.prod_range_succ]

lemma punitDbl_eq_odd_blocks (p q d : ℕ) :
    punitDbl p (q * (2 * d + 1)) =
      (∏ j ∈ Finset.range d, punitOddFullBlockNat p q j) *
        punitOddHalfBlockNat p q d := by
  have harg : q * (2 * d + 1) = 2 * q * d + q := by ring
  have hsplit : Finset.Ico 1 (2 * q * d + q + 1) =
      Finset.Ico 1 (2 * q * d + 1) ∪
        Finset.Ico (2 * q * d + 1) (2 * q * d + q + 1) := by
    rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  have hdis : Disjoint
      ((Finset.Ico 1 (2 * q * d + 1)).filter (fun x => Odd x ∧ ¬ p ∣ x))
      ((Finset.Ico (2 * q * d + 1) (2 * q * d + q + 1)).filter
        (fun x => Odd x ∧ ¬ p ∣ x)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Ico] at hx1 hx2
    omega
  rw [punitDbl, oddNumbers, harg, hsplit, Finset.filter_filter,
    Finset.filter_union, Finset.prod_union hdis]
  have hfirst : (∏ x ∈ (Finset.Ico 1 (2 * q * d + 1)).filter
      (fun x => Odd x ∧ ¬ p ∣ x), x) = punitDbl p (2 * q * d) := by
    simp [punitDbl, oddNumbers, Finset.filter_filter]
  have hsecond : (∏ x ∈
      (Finset.Ico (2 * q * d + 1) (2 * q * d + q + 1)).filter
        (fun x => Odd x ∧ ¬ p ∣ x), x) = punitOddHalfBlockNat p q d := by
    rfl
  rw [hfirst, hsecond, punitDbl_even_blocks]

lemma punitDbl_cast_eq_blocks {p r d : ℕ} [NeZero (p ^ r)]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) :
    ((punitDbl p ((p ^ r) * (2 * d + 1)) : ℕ) : ZMod ((p ^ r) ^ 3)) =
      oddFullBlock (p ^ r) ^ d * oddHalfBlock (p ^ r) d := by
  rw [punitDbl_eq_odd_blocks]
  push_cast
  rw [punitOddHalfBlockNat_cast hp hp5 hr]
  have hq1 : 1 < p ^ r := one_lt_pow₀ hp.one_lt hr.ne'
  have hp6 : p.Coprime 6 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have hple : p ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    have hc : p = 5 ∨ p = 6 := by omega
    rcases hc with rfl | rfl
    · norm_num at hd
    · norm_num at hp)
  have hq6 : (p ^ r).Coprime 6 := hp6.pow_left r
  calc
    (∏ j ∈ Finset.range d,
      ((punitOddFullBlockNat p (p ^ r) j : ℕ) : ZMod ((p ^ r) ^ 3))) *
        oddHalfBlock (p ^ r) d =
      (∏ _j ∈ Finset.range d, oddFullBlock (p ^ r)) * oddHalfBlock (p ^ r) d := by
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        rw [punitOddFullBlockNat_cast hp hp5 hr,
          oddFullBlockShift_eq (p ^ r) hq1 hq6]
    _ = _ := by rw [Finset.prod_const, Finset.card_range]

end PunitOddBlockCasts

section OddUnitRatio

open scoped Nat

def oddUNum (p N : ℕ) : ℕ :=
  punitFac p (9 * N) * punitFac p (2 * N) * punitDbl p (3 * N)

def oddUDen (p N : ℕ) : ℕ :=
  punitFac p (4 * N) * punitFac p (3 * N) * punitFac p N * punitDbl p (9 * N)

lemma oddUDen_coprime (p N : ℕ) (hp : p.Prime) : p.Coprime (oddUDen p N) := by
  simp only [oddUDen]
  exact Nat.Coprime.mul_right
    (Nat.Coprime.mul_right
      (Nat.Coprime.mul_right (punitFac_coprime p (4 * N) hp)
        (punitFac_coprime p (3 * N) hp))
      (punitFac_coprime p N hp))
    (punitDbl_coprime p (9 * N) hp)

lemma odd_units_cast_eq {p r k : ℕ} [NeZero (p ^ r)]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) :
    let q := p ^ r
    let s := p ^ (r - 1)
    let n := 2 * k + 1
    (((2 ^ (3 * (p - 1) * (n * s)) * oddUNum p (q * n) : ℕ) :
        ZMod (q ^ 3))) =
      ((oddUDen p (q * n) : ℕ) : ZMod (q ^ 3)) := by
  let q := p ^ r
  let s := p ^ (r - 1)
  let n := 2 * k + 1
  have hq1 : 1 < q := one_lt_pow₀ hp.one_lt hr.ne'
  have hp6 : p.Coprime 6 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have hple : p ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    have hc : p = 5 ∨ p = 6 := by omega
    rcases hc with rfl | rfl
    · norm_num at hd
    · norm_num at hp)
  have hq6 : q.Coprime 6 := by dsimp [q]; exact hp6.pow_left r
  have hpqle : p ≤ q := by
    dsimp [q]
    exact Nat.le_pow hr
  have hq2 : 2 < q := by omega

  let B : ZMod (q ^ 3) := unitBlock q 0
  let C : ZMod (q ^ 3) := oddFullBlock q
  let E : ZMod (q ^ 3) := oddHalfBlock q 0
  let e : ZMod (q ^ 3) := (2 : ZMod (q ^ 3)) ^ Fintype.card (ZMod q)ˣ
  have hcard : Fintype.card (ZMod q)ˣ = q - s := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hr]
    dsimp [q, s]
    have hpow : p ^ r = p ^ (r - 1) * p := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
      simp [pow_succ, mul_comm]
    rw [hpow]
    simpa using (Nat.mul_sub_left_distrib (p ^ (r - 1)) p 1)
  have hdiff : q - s = s * (p - 1) := by
    dsimp [q, s]
    have hpow : p ^ r = p ^ (r - 1) * p := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
      simp [pow_succ, mul_comm]
    rw [hpow]
    simpa using (Nat.mul_sub_left_distrib (p ^ (r - 1)) p 1).symm
  have hexp : 3 * (p - 1) * (n * s) = 3 * n * Fintype.card (ZMod q)ˣ := by
    rw [hcard, hdiff]
    ring
  have hCB : C * e = B := by
    dsimp [C, e, B]
    exact oddFullBlock_mul_two_pow q hq2 hq6
  let T : ZMod (q ^ 3) := (2 : ZMod (q ^ 3)) ^
    (2 * Fintype.card (ZMod q)ˣ)
  have hT : T = e ^ 2 := by
    dsimp [T, e]
    calc
      (2 : ZMod (q ^ 3)) ^ (2 * Fintype.card (ZMod q)ˣ) =
          2 ^ (Fintype.card (ZMod q)ˣ * 2) := by congr 1 <;> ring
      _ = (2 ^ Fintype.card (ZMod q)ˣ) ^ 2 := pow_mul _ _ _
  have hE3 : oddHalfBlock q (3 * k + 1) = E * T ^ (3 * k + 1) := by
    simpa [E, T] using oddHalfBlock_eq q hq2 hq6 (3 * k + 1)
  have hE9 : oddHalfBlock q (9 * k + 4) = E * T ^ (9 * k + 4) := by
    simpa [E, T] using oddHalfBlock_eq q hq2 hq6 (9 * k + 4)
  have hF (c : ℕ) :
      ((punitFac p (c * (q * n)) : ℕ) : ZMod (q ^ 3)) = B ^ (c * n) := by
    rw [show c * (q * n) = q * (c * n) by ring]
    simpa [q, B] using punitFac_cast_eq_block_pow hp hp5 hr (c * n)
  have hD3 : ((punitDbl p (3 * (q * n)) : ℕ) : ZMod (q ^ 3)) =
      C ^ (3 * k + 1) * oddHalfBlock q (3 * k + 1) := by
    rw [show 3 * (q * n) = q * (2 * (3 * k + 1) + 1) by dsimp [n]; ring]
    simpa [q, C] using punitDbl_cast_eq_blocks (p := p) (r := r)
      (d := 3 * k + 1) hp hp5 hr
  have hD9 : ((punitDbl p (9 * (q * n)) : ℕ) : ZMod (q ^ 3)) =
      C ^ (9 * k + 4) * oddHalfBlock q (9 * k + 4) := by
    rw [show 9 * (q * n) = q * (2 * (9 * k + 4) + 1) by dsimp [n]; ring]
    simpa [q, C] using punitDbl_cast_eq_blocks (p := p) (r := r)
      (d := 9 * k + 4) hp hp5 hr
  push_cast
  rw [hexp]
  change (2 : ZMod (q ^ 3)) ^ (3 * n * Fintype.card (ZMod q)ˣ) *
      ((oddUNum p (q * n) : ℕ) : ZMod (q ^ 3)) =
    ((oddUDen p (q * n) : ℕ) : ZMod (q ^ 3))
  rw [show (2 : ZMod (q ^ 3)) ^ (3 * n * Fintype.card (ZMod q)ˣ) = e ^ (3 * n) by
    dsimp [e]
    calc
      (2 : ZMod (q ^ 3)) ^ (3 * n * Fintype.card (ZMod q)ˣ) =
          2 ^ (Fintype.card (ZMod q)ˣ * (3 * n)) := by congr 1 <;> ring
      _ = (2 ^ Fintype.card (ZMod q)ˣ) ^ (3 * n) := pow_mul _ _ _]
  simp only [oddUNum, oddUDen]
  push_cast
  have hF1 : ((punitFac p (q * n) : ℕ) : ZMod (q ^ 3)) = B ^ n := by
    simpa using hF 1
  rw [hF 9, hF 2, hF 4, hF 3, hF1, hD3, hD9, hE3, hE9, hT]
  have hn : n = 2 * k + 1 := rfl
  have heq3 : 9 * k + 4 = (3 * k + 1) + 3 * n := by omega
  rw [heq3, pow_add, pow_add]
  have hBnum : B ^ (9 * n) * B ^ (2 * n) =
      B ^ (8 * n) * B ^ (3 * n) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have hBden : B ^ (4 * n) * B ^ (3 * n) * B ^ n = B ^ (8 * n) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  rw [hBnum, hBden]
  have hpows (m : ℕ) : B ^ m = C ^ m * e ^ m := by
    rw [← mul_pow, hCB]
  rw [hpows (3 * n)]
  ring_nf

end OddUnitRatio

section OddRatio

open scoped Nat

def oddNum (N : ℕ) : ℕ :=
  2 ^ (3 * N) * (9 * N)! * (2 * N)! * (3 * N)‼

def oddDen (N : ℕ) : ℕ :=
  (4 * N)! * (3 * N)! * N ! * (9 * N)‼

def oddStripPow (p b : ℕ) : ℕ := p ^ (25 * b + 13)

lemma oddNum_strip (a b : ℕ) (ha : 1 ≤ a) :
    oddNum ((2 * a + 1) * (2 * b + 1)) =
      oddStripPow (2 * a + 1) b *
        (2 ^ (3 * ((2 * a + 1) - 1) * (2 * b + 1)) * oddNum (2 * b + 1) *
          oddUNum (2 * a + 1) ((2 * a + 1) * (2 * b + 1))) := by
  let p := 2 * a + 1
  let K := 2 * b + 1
  have hp : 0 < p := by dsimp [p]; omega
  have h9 := factorial_strip p (9 * K) hp
  have h2 := factorial_strip p (2 * K) hp
  have h3 := doubleFactorial_strip a (3 * b + 1) ha
  rw [oddNum, oddNum, oddUNum, oddStripPow]
  rw [show 9 * (p * K) = p * (9 * K) by ring,
      show 2 * (p * K) = p * (2 * K) by ring,
      show 3 * (p * K) = p * (2 * (3 * b + 1) + 1) by dsimp [K]; ring,
      h9, h2, h3]
  dsimp [p, K]
  have hpows : (2 * a + 1) ^ (9 * (2 * b + 1)) *
      (2 * a + 1) ^ (2 * (2 * b + 1)) *
      (2 * a + 1) ^ (3 * b + 2) = (2 * a + 1) ^ (25 * b + 13) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have htwos : 2 ^ (3 * ((2 * a + 1) * (2 * b + 1))) =
      2 ^ (3 * ((2 * a + 1) - 1) * (2 * b + 1)) *
        2 ^ (3 * (2 * b + 1)) := by
    rw [show (2 * a + 1) - 1 = 2 * a by omega, ← pow_add]
    congr 1
    ring
  calc
    _ = ((2 * a + 1) ^ (9 * (2 * b + 1)) *
          (2 * a + 1) ^ (2 * (2 * b + 1)) *
          (2 * a + 1) ^ (3 * b + 2)) *
        (2 ^ (3 * ((2 * a + 1) * (2 * b + 1))) *
          ((9 * (2 * b + 1))! * (2 * (2 * b + 1))! *
            (3 * (2 * b + 1))‼) *
          (punitFac (2 * a + 1) ((2 * a + 1) * (9 * (2 * b + 1))) *
            punitFac (2 * a + 1) ((2 * a + 1) * (2 * (2 * b + 1))) *
            punitDbl (2 * a + 1) ((2 * a + 1) * (3 * (2 * b + 1))))) := by
          rw [show 3 * b + 1 + 1 = 3 * b + 2 by omega,
            show 2 * (3 * b + 1) + 1 = 3 * (2 * b + 1) by ring]
          ac_rfl
    _ = _ := by
      rw [hpows, htwos]
      simp only [show (2 * a + 1) - 1 = 2 * a by omega]
      rw [show (2 * a + 1) * (3 * (2 * b + 1)) =
        (2 * a + 1) * (2 * (3 * b + 1) + 1) by ring]
      ac_rfl

lemma oddDen_strip (a b : ℕ) (ha : 1 ≤ a) :
    oddDen ((2 * a + 1) * (2 * b + 1)) =
      oddStripPow (2 * a + 1) b *
        (oddDen (2 * b + 1) *
          oddUDen (2 * a + 1) ((2 * a + 1) * (2 * b + 1))) := by
  let p := 2 * a + 1
  let K := 2 * b + 1
  have hp : 0 < p := by dsimp [p]; omega
  have h4 := factorial_strip p (4 * K) hp
  have h3 := factorial_strip p (3 * K) hp
  have h1 := factorial_strip p K hp
  have h9 := doubleFactorial_strip a (9 * b + 4) ha
  rw [oddDen, oddDen, oddUDen, oddStripPow]
  rw [show 4 * (p * K) = p * (4 * K) by ring,
      show 3 * (p * K) = p * (3 * K) by ring,
      show p * K = p * K by rfl,
      show 9 * (p * K) = p * (2 * (9 * b + 4) + 1) by dsimp [K]; ring,
      h4, h3, h1, h9]
  dsimp [p, K]
  have hpows : (2 * a + 1) ^ (4 * (2 * b + 1)) *
      (2 * a + 1) ^ (3 * (2 * b + 1)) *
      (2 * a + 1) ^ (2 * b + 1) *
      (2 * a + 1) ^ (9 * b + 5) = (2 * a + 1) ^ (25 * b + 13) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  calc
    _ = ((2 * a + 1) ^ (4 * (2 * b + 1)) *
          (2 * a + 1) ^ (3 * (2 * b + 1)) *
          (2 * a + 1) ^ (2 * b + 1) *
          (2 * a + 1) ^ (9 * b + 5)) *
        (((4 * (2 * b + 1))! * (3 * (2 * b + 1))! *
            (2 * b + 1)! * (9 * (2 * b + 1))‼) *
          (punitFac (2 * a + 1) ((2 * a + 1) * (4 * (2 * b + 1))) *
            punitFac (2 * a + 1) ((2 * a + 1) * (3 * (2 * b + 1))) *
            punitFac (2 * a + 1) ((2 * a + 1) * (2 * b + 1)) *
            punitDbl (2 * a + 1) ((2 * a + 1) * (9 * (2 * b + 1))))) := by
          rw [show 9 * b + 4 + 1 = 9 * b + 5 by omega,
            show 2 * (9 * b + 4) + 1 = 9 * (2 * b + 1) by ring]
          ac_rfl
    _ = _ := by
      rw [hpows]
      rw [show (2 * a + 1) * (9 * (2 * b + 1)) =
        (2 * a + 1) * (2 * (9 * b + 4) + 1) by ring]

lemma odd_quotient_modEq {p r b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r)
    (z0 z1 : ℤ)
    (h0 : z0 * (oddDen ((2 * b + 1) * p ^ (r - 1)) : ℤ) =
      (oddNum ((2 * b + 1) * p ^ (r - 1)) : ℤ))
    (h1 : z1 * (oddDen ((2 * b + 1) * p ^ r) : ℤ) =
      (oddNum ((2 * b + 1) * p ^ r) : ℤ)) :
    z1 ≡ z0 [ZMOD ((p ^ r) ^ 3 : ℕ)] := by
  let s := p ^ (r - 1)
  let K := (2 * b + 1) * s
  let q := p ^ r
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  rcases hpodd with ⟨a, haeq⟩
  have ha : 1 ≤ a := by omega
  have hpodd2 : Odd p := ⟨a, haeq⟩
  have hsodd : Odd s := by dsimp [s]; exact hpodd2.pow
  have hKodd : Odd K := (show Odd (2 * b + 1) from ⟨b, rfl⟩).mul hsodd
  rcases hKodd with ⟨c, hK⟩
  have hqfac : q = p * s := by
    dsimp [q, s]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    simp [pow_succ', mul_comm]
  have hN : (2 * b + 1) * p ^ r = p * K := by
    dsimp [K, s]
    rw [show p ^ r = p * p ^ (r - 1) by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
      simp [pow_succ', mul_comm]]
    ring
  have hKarg : (2 * b + 1) * p ^ (r - 1) = K := rfl
  have h1s := h1
  rw [hN, haeq, hK] at h1s
  rw [oddDen_strip a c ha, oddNum_strip a c ha] at h1s
  simp only [Nat.cast_mul] at h1s
  have hPpos : 0 < oddStripPow (2 * a + 1) c := by
    unfold oddStripPow
    positivity
  have hP0 : (oddStripPow (2 * a + 1) c : ℤ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hstrip : z1 * (oddDen K : ℤ) *
      (oddUDen p (p * K) : ℤ) =
    (2 ^ (3 * (p - 1) * K) : ℤ) * (oddNum K : ℤ) *
      (oddUNum p (p * K) : ℤ) := by
    apply mul_left_cancel₀ hP0
    calc
      (oddStripPow (2 * a + 1) c : ℤ) *
          (z1 * (oddDen K : ℤ) * (oddUDen p (p * K) : ℤ)) =
        z1 * ((oddStripPow (2 * a + 1) c : ℤ) *
          ((oddDen K : ℤ) * (oddUDen p (p * K) : ℤ))) := by ring
      _ = (oddStripPow (2 * a + 1) c : ℤ) *
          ((2 ^ (3 * (p - 1) * K) : ℤ) * (oddNum K : ℤ) *
            (oddUNum p (p * K) : ℤ)) := by
        simpa [haeq, hK, mul_assoc] using h1s
      _ = _ := by ring
  have hDpos : 0 < oddDen K := by unfold oddDen; positivity
  have hD0 : (oddDen K : ℤ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hcross : z1 * (oddUDen p (p * K) : ℤ) =
      z0 * ((2 ^ (3 * (p - 1) * K) : ℕ) * oddUNum p (p * K) : ℕ) := by
    apply mul_left_cancel₀ hD0
    push_cast
    calc
      (oddDen K : ℤ) * (z1 * (oddUDen p (p * K) : ℤ)) =
          z1 * (oddDen K : ℤ) * (oddUDen p (p * K) : ℤ) := by ring
      _ = (2 ^ (3 * (p - 1) * K) : ℤ) * (oddNum K : ℤ) *
          (oddUNum p (p * K) : ℤ) := hstrip
      _ = (2 ^ (3 * (p - 1) * K) : ℤ) *
          (z0 * (oddDen K : ℤ)) * (oddUNum p (p * K) : ℤ) := by rw [h0]
      _ = (oddDen K : ℤ) *
          (z0 * ((2 ^ (3 * (p - 1) * K) : ℤ) * (oddUNum p (p * K) : ℤ))) := by ring
  have hq1 : 1 < q := by dsimp [q]; exact one_lt_pow₀ hp.one_lt hr.ne'
  haveI : NeZero q := ⟨by omega⟩
  have hcopP : p.Coprime (oddUDen p (p * K)) := oddUDen_coprime p (p * K) hp
  have hcopQ : Nat.Coprime (q ^ 3) (oddUDen p (p * K)) := by
    dsimp [q]
    rw [← pow_mul]
    exact hcopP.pow_left (r * 3)
  have hunit : IsUnit ((oddUDen p (p * K) : ℕ) : ZMod (q ^ 3)) :=
    (ZMod.isUnit_iff_coprime (oddUDen p (p * K)) (q ^ 3)).mpr hcopQ.symm
  apply (ZMod.intCast_eq_intCast_iff z1 z0 (q ^ 3)).mp
  apply IsUnit.mul_left_cancel hunit
  have hcasteq := congrArg (fun z : ℤ => (z : ZMod (q ^ 3))) hcross
  push_cast at hcasteq ⊢
  rw [mul_comm (oddUDen p (p * K) : ZMod (q ^ 3)),
      mul_comm (oddUDen p (p * K) : ZMod (q ^ 3))]
  rw [hcasteq]
  have hu := odd_units_cast_eq (p := p) (r := r) (k := b) hp hp5 hr
  dsimp only at hu
  change (((2 ^ (3 * (p - 1) * K) * oddUNum p (q * (2 * b + 1)) : ℕ) :
      ZMod (q ^ 3))) = ((oddUDen p (q * (2 * b + 1)) : ℕ) : ZMod (q ^ 3)) at hu
  rw [show q * (2 * b + 1) = p * K by rw [hqfac]; ring] at hu
  push_cast at hu
  exact congrArg (fun x : ZMod (q ^ 3) => (z0 : ZMod (q ^ 3)) * x) hu

end OddRatio

section GammaBridge



open scoped Real Nat

lemma gamma_doubleFactorial_ratio (N : ℕ) :
    Real.Gamma (3 / 2 * (N : ℝ) + 1) * (Nat.doubleFactorial (9 * N) : ℝ) =
      (2 : ℝ) ^ (3 * N) * (Nat.doubleFactorial (3 * N) : ℝ) *
        Real.Gamma (9 / 2 * (N : ℝ) + 1) := by
  rcases Nat.even_or_odd N with hN | hN
  · rcases hN with ⟨k, rfl⟩
    rw [show k + k = 2 * k by omega]
    rw [show (3 / 2 : ℝ) * (2 * k : ℕ) + 1 = ((3 * k : ℕ) : ℝ) + 1 by
      push_cast; ring]
    rw [show (9 / 2 : ℝ) * (2 * k : ℕ) + 1 = ((9 * k : ℕ) : ℝ) + 1 by
      push_cast; ring]
    rw [Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
    rw [show 9 * (2 * k) = 2 * (9 * k) by ring,
      show 3 * (2 * k) = 2 * (3 * k) by ring,
      Nat.doubleFactorial_two_mul, Nat.doubleFactorial_two_mul]
    push_cast
    rw [show 2 * (3 * k) = 6 * k by ring]
    rw [show (2 : ℝ) ^ (6 * k) = 2 ^ (3 * k) * 2 ^ (3 * k) by
      rw [← pow_add]; congr 1 <;> ring]
    ring
  · rcases hN with ⟨k, rfl⟩
    rw [show (3 / 2 : ℝ) * (2 * k + 1 : ℕ) + 1 =
        ((3 * k + 1 : ℕ) : ℝ) + 1 + 1 / 2 by push_cast; ring]
    rw [show (9 / 2 : ℝ) * (2 * k + 1 : ℕ) + 1 =
        ((9 * k + 4 : ℕ) : ℝ) + 1 + 1 / 2 by push_cast; ring]
    rw [Real.Gamma_nat_add_one_add_half, Real.Gamma_nat_add_one_add_half]
    rw [show 9 * (2 * k + 1) = 2 * (9 * k + 4) + 1 by ring,
      show 3 * (2 * k + 1) = 2 * (3 * k + 1) + 1 by ring]
    push_cast
    have hsqrt : (Real.sqrt Real.pi) ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
    field_simp
    rw [show (2 : ℝ) ^ (9 * k + 4 + 1) =
        2 ^ (3 * k + 1 + 1) * 2 ^ (3 * (2 * k + 1)) by
      rw [← pow_add]
      congr 1
      ring]
    ring

lemma a_mul_oddDen (N : ℕ) :
    a N * (oddDen N : ℝ) = (oddNum N : ℝ) := by
  rw [a, oddDen, oddNum]
  rw [show (9 : ℝ) * N + 1 = ((9 * N : ℕ) : ℝ) + 1 by push_cast; ring,
    show (2 : ℝ) * N + 1 = ((2 * N : ℕ) : ℝ) + 1 by push_cast; ring,
    show (4 : ℝ) * N + 1 = ((4 * N : ℕ) : ℝ) + 1 by push_cast; ring,
    show (3 : ℝ) * N + 1 = ((3 * N : ℕ) : ℝ) + 1 by push_cast; ring,
    show (N : ℝ) + 1 = ((N : ℕ) : ℝ) + 1 by rfl]
  rw [Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial]
  push_cast
  have hratio := gamma_doubleFactorial_ratio N
  have hfac4 : ((4 * N).factorial : ℝ) ≠ 0 := by positivity
  have hfac3 : ((3 * N).factorial : ℝ) ≠ 0 := by positivity
  have hfacN : (N.factorial : ℝ) ≠ 0 := by positivity
  have hdf9 : (Nat.doubleFactorial (9 * N) : ℝ) ≠ 0 := by positivity
  field_simp
  rw [show ((3 : ℝ) * N + 2) / 2 = 3 / 2 * (N : ℝ) + 1 by ring,
    show ((N : ℝ) * 9 + 2) / 2 = 9 / 2 * (N : ℝ) + 1 by ring]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hratio

lemma chosen_odd_cross
    (h_int : ∀ m : ℕ, a m ∈ Set.range (fun x : ℤ => (x : ℝ))) (N : ℕ) :
    (Classical.choose (h_int N) : ℤ) * (oddDen N : ℤ) = (oddNum N : ℤ) := by
  have hz : ((Classical.choose (h_int N) : ℤ) : ℝ) = a N :=
    Classical.choose_spec (h_int N)
  have hr := a_mul_oddDen N
  rw [← hz] at hr
  exact_mod_cast hr

end GammaBridge

section EvenBridge

open scoped Nat

lemma oddNum_even (k : ℕ) : oddNum (2 * k) = 2 ^ (9 * k) * evenNum k := by
  rw [oddNum, evenNum]
  rw [show 3 * (2 * k) = 2 * (3 * k) by ring,
    Nat.doubleFactorial_two_mul]
  have hp : 2 ^ (3 * (2 * k)) * 2 ^ (3 * k) = 2 ^ (9 * k) := by
    rw [← pow_add]
    congr 1
    ring
  rw [show 2 * (3 * k) = 3 * (2 * k) by ring,
    show 9 * (2 * k) = 18 * k by ring,
    show 2 * (2 * k) = 4 * k by ring]
  calc
    _ = (2 ^ (3 * (2 * k)) * 2 ^ (3 * k)) *
        ((18 * k)! * (4 * k)! * (3 * k)!) := by ring
    _ = _ := by rw [hp]

lemma oddDen_even (k : ℕ) : oddDen (2 * k) = 2 ^ (9 * k) * evenDen k := by
  rw [oddDen, evenDen]
  rw [show 9 * (2 * k) = 2 * (9 * k) by ring,
    Nat.doubleFactorial_two_mul]
  ring

lemma chosen_even_cross
    (h_int : ∀ m : ℕ, a m ∈ Set.range (fun x : ℤ => (x : ℝ))) (k : ℕ) :
    (Classical.choose (h_int (2 * k)) : ℤ) * (evenDen k : ℤ) = (evenNum k : ℤ) := by
  have h := chosen_odd_cross h_int (2 * k)
  rw [oddNum_even, oddDen_even] at h
  push_cast at h
  have hpow : (2 ^ (9 * k) : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hpow
  calc
    (2 ^ (9 * k) : ℤ) *
        ((Classical.choose (h_int (2 * k)) : ℤ) * (evenDen k : ℤ)) =
      (Classical.choose (h_int (2 * k)) : ℤ) *
        ((2 ^ (9 * k) : ℤ) * (evenDen k : ℤ)) := by ring
    _ = (2 ^ (9 * k) : ℤ) * (evenNum k : ℤ) := h

end EvenBridge

section Final

open scoped Real Nat

/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: This conjecture requires that a(n) is an integer for all n, which is only conjectural.
We assume integrality for the purpose of stating the congruence.
-/

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp hp5 n r hn hr
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · rcases hnEven with ⟨k, hk⟩
    have hnk : n = 2 * k := by omega
    let z0 : ℤ := Classical.choose (h_int (n * p ^ (r - 1)))
    let z1 : ℤ := Classical.choose (h_int (n * p ^ r))
    have h0raw := chosen_even_cross h_int (k * p ^ (r - 1))
    have h0 : z0 * (evenDen (k * p ^ (r - 1)) : ℤ) =
        (evenNum (k * p ^ (r - 1)) : ℤ) := by
      dsimp [z0]
      rw [show n * p ^ (r - 1) = 2 * (k * p ^ (r - 1)) by rw [hnk]; ring]
      exact h0raw
    have h1raw := chosen_even_cross h_int (p * (k * p ^ (r - 1)))
    have h1 : z1 * (evenDen (p * (k * p ^ (r - 1))) : ℤ) =
        (evenNum (p * (k * p ^ (r - 1))) : ℤ) := by
      dsimp [z1]
      rw [show n * p ^ r = 2 * (p * (k * p ^ (r - 1))) by
        rw [hnk]
        have hpr : p ^ r = p * p ^ (r - 1) := by
          obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
          simp [pow_succ', mul_comm]
        rw [hpr]
        ring]
      exact h1raw
    have hcon := even_quotient_modEq (p := p) (s := r - 1) (k := k)
      hp hp5 z0 z1 h0 h1
    dsimp [z0, z1] at hcon
    have hrid : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
    have hmodint : (((p : ℤ) ^ (r - 1 + 1)) ^ 3) = (p : ℤ) ^ (3 * r) := by
      rw [hrid, ← pow_mul]
      congr 1
      omega
    rw [hmodint] at hcon
    exact hcon
  · rcases hnOdd with ⟨k, hnk⟩
    let z0 : ℤ := Classical.choose (h_int (n * p ^ (r - 1)))
    let z1 : ℤ := Classical.choose (h_int (n * p ^ r))
    have h0 : z0 * (oddDen ((2 * k + 1) * p ^ (r - 1)) : ℤ) =
        (oddNum ((2 * k + 1) * p ^ (r - 1)) : ℤ) := by
      dsimp [z0]
      rw [← hnk]
      exact chosen_odd_cross h_int _
    have h1 : z1 * (oddDen ((2 * k + 1) * p ^ r) : ℤ) =
        (oddNum ((2 * k + 1) * p ^ r) : ℤ) := by
      dsimp [z1]
      rw [← hnk]
      exact chosen_odd_cross h_int _
    have hcon := odd_quotient_modEq (p := p) (r := r) (b := k)
      hp hp5 hr z0 z1 h0 h1
    dsimp [z0, z1] at hcon
    have hmodint : (((p : ℤ) ^ r) ^ 3) = (p : ℤ) ^ (3 * r) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hmodint] at hcon
    exact hcon

end Final
