import FormalConjecturesUtil

/-!
Counting bounded nonnegative matrix images with a shared rational offset.
This is auxiliary arithmetic, not a proof of the conjecture in Spec.lean.
-/
namespace RankOneBoundaryCounting

open Finset

lemma box_sum_bounds (D Q M : ℕ) (R : ℝ) (f : Fin D → ℝ)
    (hf : ∀ j, 0 ≤ f j ∧ f j ≤ R)
    (hM : (D : ℝ)*Q*R ≤ M) (u : Fin D → Fin (Q+1)) :
    0 ≤ ∑ j, (u j : ℝ)*f j ∧ ∑ j, (u j : ℝ)*f j ≤ M := by
  constructor
  · exact sum_nonneg (fun j _ => mul_nonneg (by positivity) (hf j).1)
  · calc
      _ ≤ ∑ _j : Fin D, (Q : ℝ)*R := by
        apply sum_le_sum
        intro j _
        have hu : (u j : ℝ) ≤ Q := by exact_mod_cast (Nat.le_of_lt_succ (u j).isLt)
        exact mul_le_mul hu (hf j).2 (hf j).1 (by positivity)
      _ = (D : ℝ)*Q*R := by simp; ring
      _ ≤ M := hM

/-- The common denominator L costs a single residue coordinate, not one
residue coordinate for each matrix row. The resulting vector can have zero
retained sum; nonzero weights are the only nonvanishing assertion. -/
theorem bounded_kernel (D m Q L M : ℕ) (hL : 0 < L)
    (γ R : ℝ) (z : ℤ) (hγ : (L : ℝ)*γ = z)
    (b : Fin m → Fin D → ℤ) (f : Fin m → Fin D → ℝ)
    (hf : ∀ i j, f i j = γ - (b i j : ℝ))
    (hpos : ∀ i j, 0 ≤ f i j ∧ f i j ≤ R)
    (hM : (D : ℝ)*Q*R ≤ M)
    (hcard : L*(M+1)^m < (Q+1)^D) :
    ∃ w : Fin D → ℤ, w ≠ 0 ∧ (∀ j, |w j| ≤ Q) ∧
      (L : ℤ) ∣ ∑ j, w j ∧
      ∀ i, ∑ j, (w j : ℝ)*f i j = 0 := by
  classical
  letI : NeZero L := ⟨hL.ne'⟩
  let y (u : Fin D → Fin (Q+1)) (i : Fin m) : ℝ :=
    ∑ j, (u j : ℝ)*f i j
  have hy (u : Fin D → Fin (Q+1)) (i : Fin m) : 0 ≤ y u i ∧ y u i ≤ M :=
    box_sum_bounds D Q M R (f i) (hpos i) hM u
  let digit (u : Fin D → Fin (Q+1)) (i : Fin m) : Fin (M+1) :=
    ⟨⌊y u i⌋₊, by
      have hh := Nat.floor_le_floor (hy u i).2
      simp only [Nat.floor_natCast] at hh
      omega⟩
  let code (u : Fin D → Fin (Q+1)) : ZMod L × (Fin m → Fin (M+1)) :=
    (∑ j, (u j : ZMod L), digit u)
  have hc : Fintype.card (ZMod L × (Fin m → Fin (M+1))) <
      Fintype.card (Fin D → Fin (Q+1)) := by simpa using hcard
  obtain ⟨u, v, huv, he⟩ := Fintype.exists_ne_map_eq_of_card_lt code hc
  let w : Fin D → ℤ := fun j => (u j : ℤ)-(v j : ℤ)
  have hw : w ≠ 0 := by
    intro hh
    apply huv
    funext j
    apply Fin.ext
    have hj := congrFun hh j
    simp only [w, Pi.zero_apply, sub_eq_zero] at hj
    exact_mod_cast hj
  have hsize (j : Fin D) : |w j| ≤ Q := by
    have hu := (u j).isLt
    have hv := (v j).isLt
    apply abs_le.mpr
    dsimp [w]
    constructor <;> omega
  have hmod : (L : ℤ) ∣ ∑ j, w j := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hh := congrArg Prod.fst he
    change (∑ j, (u j : ZMod L)) = ∑ j, (v j : ZMod L) at hh
    simp only [w, Int.cast_sum, Int.cast_sub, Int.cast_natCast, sum_sub_distrib]
    exact sub_eq_zero.mpr hh
  refine ⟨w, hw, hsize, hmod, ?_⟩
  intro i
  have hd : ⌊y u i⌋₊ = ⌊y v i⌋₊ := by
    have hh := congrArg (fun c => (c.2 i).val) he
    exact hh
  have hulo : (⌊y u i⌋₊ : ℝ) ≤ y u i := Nat.floor_le (hy u i).1
  have huhi : y u i < (⌊y u i⌋₊ : ℝ)+1 := Nat.lt_floor_add_one _
  have hvlo : (⌊y v i⌋₊ : ℝ) ≤ y v i := Nat.floor_le (hy v i).1
  have hvhi : y v i < (⌊y v i⌋₊ : ℝ)+1 := Nat.lt_floor_add_one _
  rw [hd] at hulo huhi
  have hid : (∑ j, (w j : ℝ)*f i j) = y u i-y v i := by
    simp only [w, y, Int.cast_sub, Int.cast_natCast, sub_mul, sum_sub_distrib]
  obtain ⟨k, hk⟩ := hmod
  have hint : (∑ j, (w j : ℝ)*f i j) =
      ((z*k-∑ j, w j*b i j : ℤ) : ℝ) := by
    simp only [hf, mul_sub, sum_sub_distrib, ← sum_mul, ← Int.cast_sum,
      hk, Int.cast_mul, Int.cast_sub]
    push_cast
    rw [show ((L : ℝ)*(k : ℝ))*γ = ((L : ℝ)*γ)*(k : ℝ) by ring, hγ]
  have hlo : (-1 : ℝ) < ((z*k-∑ j, w j*b i j : ℤ) : ℝ) := by
    rw [← hint, hid]
    linarith
  have hhi : ((z*k-∑ j, w j*b i j : ℤ) : ℝ) < 1 := by
    rw [← hint, hid]
    linarith
  have hz : z*k-∑ j, w j*b i j = 0 := by
    have hl : (-1 : ℤ) < z*k-∑ j, w j*b i j := by exact_mod_cast hlo
    have hh : z*k-∑ j, w j*b i j < (1 : ℤ) := by exact_mod_cast hhi
    omega
  rw [hint, hz, Int.cast_zero]

/-- Application to a rational endpoint and individually cleared boundaries.
Only one factor q.den occurs in the cardinality condition. -/
theorem rational_endpoint_kernel (D m Q C M : ℕ) (hC : 0 < C)
    (q : ℚ) (η : ℝ) (B : Fin m → Fin D → ℝ)
    (hB : ∀ i j, ∃ b : ℤ, (C : ℝ)*B i j = b)
    (he : ∀ i j, 0 ≤ (q : ℝ)-B i j ∧ (q : ℝ)-B i j ≤ η)
    (hM : (D : ℝ)*Q*((C : ℝ)*η) ≤ M)
    (hcard : q.den*(M+1)^m < (Q+1)^D) :
    ∃ w : Fin D → ℤ, w ≠ 0 ∧ (∀ j, |w j| ≤ Q) ∧
      (q.den : ℤ) ∣ ∑ j, w j ∧
      ∀ i, ∑ j, (w j : ℝ)*((q : ℝ)-B i j) = 0 := by
  classical
  choose b hb using hB
  have hγ : (q.den : ℝ)*((C : ℝ)*(q : ℝ)) = ((C : ℤ)*q.num : ℤ) := by
    rw [Rat.cast_def]
    have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    push_cast
    field_simp
  have hf (i : Fin m) (j : Fin D) :
      (C : ℝ)*((q : ℝ)-B i j) = (C : ℝ)*(q : ℝ)-(b i j : ℝ) := by
    rw [mul_sub, hb]
  have hpos (i : Fin m) (j : Fin D) :
      0 ≤ (C : ℝ)*((q : ℝ)-B i j) ∧
        (C : ℝ)*((q : ℝ)-B i j) ≤ (C : ℝ)*η :=
    ⟨mul_nonneg (by positivity) (he i j).1,
      mul_le_mul_of_nonneg_left (he i j).2 (by positivity)⟩
  obtain ⟨w, hw, hsize, hmod, hz⟩ := bounded_kernel D m Q q.den M q.pos
    ((C : ℝ)*(q : ℝ)) ((C : ℝ)*η) ((C : ℤ)*q.num) hγ b
    (fun i j => (C : ℝ)*((q : ℝ)-B i j)) hf hpos hM hcard
  refine ⟨w, hw, hsize, hmod, fun i => ?_⟩
  have hh : (C : ℝ)*(∑ j, (w j : ℝ)*((q : ℝ)-B i j)) = 0 := by
    rw [Finset.mul_sum]
    convert hz i using 1
    apply Finset.sum_congr rfl
    intros
    ring
  exact (mul_eq_zero.mp hh).resolve_left (by positivity)

lemma factorial_prefix_integral (c : ℕ → ℤ) (n T : ℕ) (hn : n ≤ T) :
    ∃ z : ℤ, (T.factorial : ℝ)*
      (∑ k ∈ Finset.range (n+1), (c k : ℝ)/k.factorial) = z := by
  refine ⟨∑ k ∈ Finset.range (n+1), c k*(T.factorial/k.factorial : ℕ), ?_⟩
  simp only [Finset.mul_sum, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro k hk
  have hkT : k ≤ T := by have := Finset.mem_range.mp hk; omega
  rw [Nat.cast_div (Nat.factorial_dvd_factorial hkT)
    (by positivity : (k.factorial : ℝ) ≠ 0)]
  ring

/-- A concrete factorial-prefix version. The coefficient sequence may, in
particular, retain only selected Lambert rows. Nonvanishing of the retained
sum is deliberately not asserted. -/
theorem factorial_matrix_kernel (D m Q T M : ℕ) (q : ℚ) (η : ℝ)
    (c : ℕ → ℤ) (n : Fin m → Fin D → ℕ) (hn : ∀ i j, n i j ≤ T)
    (he : ∀ i j,
      0 ≤ (q : ℝ)-(∑ k ∈ Finset.range (n i j+1), (c k : ℝ)/k.factorial) ∧
      (q : ℝ)-(∑ k ∈ Finset.range (n i j+1), (c k : ℝ)/k.factorial) ≤ η)
    (hM : (D : ℝ)*Q*((T.factorial : ℝ)*η) ≤ M)
    (hcard : q.den*(M+1)^m < (Q+1)^D) :
    ∃ w : Fin D → ℤ, w ≠ 0 ∧ (∀ j, |w j| ≤ Q) ∧
      (q.den : ℤ) ∣ ∑ j, w j ∧
      ∀ i, ∑ j, (w j : ℝ)*
        ((q : ℝ)-(∑ k ∈ Finset.range (n i j+1), (c k : ℝ)/k.factorial)) = 0 := by
  exact rational_endpoint_kernel D m Q T.factorial M (Nat.factorial_pos T)
    q η (fun i j => ∑ k ∈ Finset.range (n i j+1), (c k : ℝ)/k.factorial)
    (fun i j => factorial_prefix_integral c (n i j) T (hn i j)) he hM hcard

/-- If the common-denominator modulus is larger than the entire weight-sum
range, its homogeneous residue condition necessarily gives zero retained sum. -/
lemma sum_zero_of_small_modular_weights (D Q L : ℕ) (hL : D*Q < L)
    (w : Fin D → ℤ) (hw : ∀ j, |w j| ≤ Q)
    (hmod : (L : ℤ) ∣ ∑ j, w j) : ∑ j, w j = 0 := by
  have hb : |∑ j, w j| ≤ (D : ℤ)*Q := by
    calc
      _ ≤ ∑ j, |w j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin D, (Q : ℤ) := sum_le_sum (fun j _ => hw j)
      _ = _ := by simp
  have hs : |∑ j, w j| < (L : ℤ) := hb.trans_lt (by exact_mod_cast hL)
  by_contra hn
  have hp : (0 : ℤ) < |∑ j, w j| := abs_pos.mpr hn
  have hd : (L : ℤ) ∣ |∑ j, w j| := (dvd_abs _ _).mpr hmod
  have hh := Int.le_of_dvd hp hd
  omega

#print axioms bounded_kernel
#print axioms rational_endpoint_kernel
#print axioms factorial_matrix_kernel
#print axioms sum_zero_of_small_modular_weights

end RankOneBoundaryCounting
