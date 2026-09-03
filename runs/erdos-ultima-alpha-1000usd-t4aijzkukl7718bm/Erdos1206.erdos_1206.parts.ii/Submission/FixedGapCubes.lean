import FormalConjecturesUtil

/-!
Auxiliary separation results for equal cubic differences with two fixed,
unequal positive gaps. These do not settle the density conjecture.
-/

namespace Erdos1206

private lemma quadratic_increment_eliminant {A B C x y u v : ℤ}
    (h0 : A * x ^ 2 - B * y ^ 2 = C)
    (h1 : A * (x + u) ^ 2 - B * (y + v) ^ 2 = C) :
    (A * u ^ 2 - B * v ^ 2) *
      (4 * A * x ^ 2 + 4 * A * u * x + (A * u ^ 2 - B * v ^ 2)) +
      4 * B * v ^ 2 * C = 0 := by
  have hl : 2 * A * u * x - 2 * B * v * y + (A * u ^ 2 - B * v ^ 2) = 0 := by
    linear_combination h1 - h0
  linear_combination
    (2 * A * u * x + (A * u ^ 2 - B * v ^ 2) + 2 * B * v * y) * hl -
      4 * B * v ^ 2 * h0

/-- Fixing both coordinate increments fixes at most one positive point on a
nonzero quadratic level curve. -/
lemma quadratic_fixed_increment_unique {A B C x y x' y' u v : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hC : C ≠ 0)
    (hx : 0 ≤ x) (hx' : 0 ≤ x') (hu : 0 < u) (hv : 0 < v)
    (h0 : A * x ^ 2 - B * y ^ 2 = C)
    (h1 : A * (x + u) ^ 2 - B * (y + v) ^ 2 = C)
    (h0' : A * x' ^ 2 - B * y' ^ 2 = C)
    (h1' : A * (x' + u) ^ 2 - B * (y' + v) ^ 2 = C) : x = x' := by
  have hp := quadratic_increment_eliminant h0 h1
  have hp' := quadratic_increment_eliminant h0' h1'
  have hD : A * u ^ 2 - B * v ^ 2 ≠ 0 := by
    intro he
    rw [he, zero_mul, zero_add] at hp
    have hm : 4 * B * v ^ 2 ≠ 0 := by positivity
    exact hC ((mul_eq_zero.mp hp).resolve_left hm)
  have hf : (4 * A * (A * u ^ 2 - B * v ^ 2)) *
      (x - x') * (x + x' + u) = 0 := by
    linear_combination hp - hp'
  have hs : x + x' + u ≠ 0 := by omega
  have hm : 4 * A * (A * u ^ 2 - B * v ^ 2) ≠ 0 := by
    exact mul_ne_zero (by positivity) hD
  have hz := (mul_eq_zero.mp hf).resolve_right hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hm)

private lemma quadratic_point_ratio_bound {A B C x y : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hx : 0 ≤ x) (hy : 0 < y)
    (he : A * x ^ 2 - B * y ^ 2 = C) :
    x ≤ (B + |C| + 1) * y := by
  have hAx : x ^ 2 ≤ A * x ^ 2 := by
    exact le_mul_of_one_le_left (sq_nonneg x) (by omega)
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hC1 : C ≤ |C| := le_abs_self C
  have hB1 : 1 ≤ B := by omega
  have hy1 : 1 ≤ y ^ 2 := by nlinarith
  have hD : B + |C| ≤ (B + |C| + 1) ^ 2 := by nlinarith [sq_nonneg (B + |C|)]
  have hDy := mul_le_mul_of_nonneg_right hD (sq_nonneg y)
  have hCy := mul_le_mul_of_nonneg_left hy1 hC0
  have hs : x ^ 2 ≤ ((B + |C| + 1) * y) ^ 2 := by nlinarith
  have hpos : 0 ≤ (B + |C| + 1) * y := by positivity
  nlinarith

/-- A bounded increase in the first coordinate bounds the increase in the
second coordinate uniformly over the level curve. -/
lemma quadratic_point_increment_bound {A B C x y u v L : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hx : 0 ≤ x) (hy : 0 < y)
    (hu : 0 < u) (hv : 0 < v) (huL : u ≤ L)
    (h0 : A * x ^ 2 - B * y ^ 2 = C)
    (h1 : A * (x + u) ^ 2 - B * (y + v) ^ 2 = C) :
    v ≤ A * L * (2 * (B + |C| + 1) + L) := by
  have hr := quadratic_point_ratio_bound hA hB hx hy h0
  have hl : A * u * (2 * x + u) = B * v * (2 * y + v) := by
    linear_combination h1 - h0
  have hL : 0 < L := lt_of_lt_of_le hu huL
  have hleft : v * y ≤ B * v * (2 * y + v) := by
    have hh : v * y ≤ v * (2 * y + v) :=
      mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hh' : v * (2 * y + v) ≤ B * (v * (2 * y + v)) :=
      le_mul_of_one_le_left (by positivity) (by omega)
    nlinarith only [hh, hh']
  have hxu : 2 * x + u ≤ (2 * (B + |C| + 1) + L) * y := by
    have hLy : L ≤ L * y := le_mul_of_one_le_right (by omega) (by omega)
    nlinarith
  have hright : A * u * (2 * x + u) ≤
      (A * L * (2 * (B + |C| + 1) + L)) * y := by
    calc
      _ ≤ A * L * (2 * x + u) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huL (by omega)) (by omega)
      _ ≤ A * L * ((2 * (B + |C| + 1) + L) * y) :=
        mul_le_mul_of_nonneg_left hxu (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ hy).mp (hleft.trans (hl ▸ hright))

/-- Positive integral first coordinates on a quadratic level curve. -/
def quadraticPositiveAbscissae (A B : ℕ) (C : ℤ) : Set ℕ :=
  {x | 0 < x ∧ ∃ y : ℕ, 0 < y ∧ (A : ℤ) * x ^ 2 - B * y ^ 2 = C}

/-- A quantitative bound for the points with a nearby second point. -/
lemma quadratic_close_abscissae_bounds {A B : ℕ} {C : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hC : C ≠ 0) (L : ℕ) :
    {x ∈ quadraticPositiveAbscissae A B C |
      ∃ x' ∈ quadraticPositiveAbscissae A B C, x < x' ∧ x' ≤ x + L}.Finite ∧
    {x ∈ quadraticPositiveAbscissae A B C |
      ∃ x' ∈ quadraticPositiveAbscissae A B C, x < x' ∧ x' ≤ x + L}.ncard ≤
      L * (A * L * (2 * (B + C.natAbs + 1) + L)) := by
  classical
  let V := A * L * (2 * (B + C.natAbs + 1) + L)
  let T : ℕ → ℕ → Set ℕ := fun u v => {x | ∃ y : ℕ,
    (A : ℤ) * x ^ 2 - B * y ^ 2 = C ∧
      (A : ℤ) * ((x : ℤ) + u) ^ 2 - B * ((y : ℤ) + v) ^ 2 = C}
  have hTsub (u v : ℕ) (hu : 0 < u) (hv : 0 < v) : (T u v).Subsingleton := by
    rintro x ⟨y, h0, h1⟩ x' ⟨y', h0', h1'⟩
    have he := quadratic_fixed_increment_unique
      (by exact_mod_cast hA) (by exact_mod_cast hB) hC
      (by positivity : (0 : ℤ) ≤ x) (by positivity : (0 : ℤ) ≤ x')
      (by exact_mod_cast hu) (by exact_mod_cast hv) h0 h1 h0' h1'
    exact_mod_cast he
  have hT (u v : ℕ) (hu : 0 < u) (hv : 0 < v) : (T u v).Finite :=
    (hTsub u v hu hv).finite
  have hfin : (⋃ u ∈ Set.Icc 1 L, ⋃ v ∈ Set.Icc 1 V, T u v).Finite :=
    (Set.finite_Icc 1 L).biUnion fun u hu =>
      (Set.finite_Icc 1 V).biUnion fun v hv => hT u v hu.1 hv.1
  have hsub : {x ∈ quadraticPositiveAbscissae A B C |
      ∃ x' ∈ quadraticPositiveAbscissae A B C, x < x' ∧ x' ≤ x + L} ⊆
      ⋃ u ∈ Set.Icc 1 L, ⋃ v ∈ Set.Icc 1 V, T u v := by
    rintro x ⟨⟨hx, y, hy, h0⟩, x', ⟨hx', y', hy', h0'⟩, hxx', hL⟩
    have hyy' : y < y' := by
      by_contra hh
      have hys : (y' : ℤ) ^ 2 ≤ (y : ℤ) ^ 2 := by
        exact_mod_cast Nat.pow_le_pow_left (show y' ≤ y by omega) 2
      have hxs : (x : ℤ) ^ 2 < (x' : ℤ) ^ 2 := by
        exact_mod_cast Nat.pow_lt_pow_left hxx' (by decide : 2 ≠ 0)
      have hxs' := mul_lt_mul_of_pos_left hxs (show (0 : ℤ) < A by exact_mod_cast hA)
      have hys' := mul_le_mul_of_nonneg_left hys (show (0 : ℤ) ≤ B by positivity)
      omega
    let u := x' - x
    let v := y' - y
    have hu : 0 < u := by dsimp [u]; omega
    have hv : 0 < v := by dsimp [v]; omega
    have huL : u ≤ L := by dsimp [u]; omega
    have hxu : (x : ℤ) + u = x' := by dsimp [u]; omega
    have hyv : (y : ℤ) + v = y' := by dsimp [v]; omega
    have h1 : (A : ℤ) * ((x : ℤ) + u) ^ 2 - B * ((y : ℤ) + v) ^ 2 = C := by
      simpa only [hxu, hyv] using h0'
    have hvV : v ≤ V := by
      have hh := quadratic_point_increment_bound (L := (L : ℤ))
        (by exact_mod_cast hA) (by exact_mod_cast hB)
        (by positivity : (0 : ℤ) ≤ x) (by exact_mod_cast hy)
        (by exact_mod_cast hu) (by exact_mod_cast hv)
        (by exact_mod_cast huL) h0 h1
      have hVe : (V : ℤ) = (A : ℤ) * L * (2 * ((B : ℤ) + |C| + 1) + L) := by
        simp only [V, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Int.natCast_natAbs]
      rw [← hVe] at hh
      exact_mod_cast hh
    exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨⟨hu, huL⟩,
      Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨⟨hv, hvV⟩, ⟨y, h0, h1⟩⟩⟩⟩⟩
  refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans ?_⟩
  change (⋃ u ∈ Set.Icc 1 L, ⋃ v ∈ Set.Icc 1 V, T u v).ncard ≤ L * V
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 L, (⋃ v ∈ Set.Icc 1 V, T u v).ncard := by
      simpa only [Finset.mem_Icc, Set.mem_Icc] using
        (Finset.Icc 1 L).set_ncard_biUnion_le (fun u => ⋃ v ∈ Set.Icc 1 V, T u v)
    _ ≤ ∑ u ∈ Finset.Icc 1 L, ∑ v ∈ Finset.Icc 1 V, (T u v).ncard := by
      apply Finset.sum_le_sum
      intro u hu
      simpa only [Finset.mem_Icc, Set.mem_Icc] using
        (Finset.Icc 1 V).set_ncard_biUnion_le (T u)
    _ ≤ ∑ u ∈ Finset.Icc 1 L, ∑ v ∈ Finset.Icc 1 V, 1 := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      exact (Set.ncard_le_one (hT u v (Finset.mem_Icc.mp hu).1
        (Finset.mem_Icc.mp hv).1)).mpr (hTsub u v (Finset.mem_Icc.mp hu).1
        (Finset.mem_Icc.mp hv).1)
    _ = _ := by simp

/-- Only finitely many points have another point within a prescribed distance. -/
lemma quadratic_close_abscissae_finite {A B : ℕ} {C : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hC : C ≠ 0) (L : ℕ) :
    {x ∈ quadraticPositiveAbscissae A B C |
      ∃ x' ∈ quadraticPositiveAbscissae A B C, x < x' ∧ x' ≤ x + L}.Finite :=
  (quadratic_close_abscissae_bounds hA hB hC L).1

/-- Eventual separation gives a uniform prefix counting estimate. -/
lemma sparse_close_pairs_prefix_bound {S : Set ℕ} {L : ℕ} (hL : 0 < L)
    (hfin : {x ∈ S | ∃ y ∈ S, x < y ∧ y ≤ x + L}.Finite) :
    ∃ M : ℕ, ∀ N : ℕ, (S ∩ Set.Iio N).ncard ≤ M + N / L + 1 := by
  classical
  obtain ⟨K, hK⟩ := hfin.bddAbove
  let M := K + 1
  refine ⟨M, fun N => ?_⟩
  let T := (S ∩ Set.Iio N) ∩ Set.Ici M
  have hsep (x y : ℕ) (hx : x ∈ T) (hy : y ∈ T) (hxy : x < y) : x + L < y := by
    by_contra hh
    have hk := hK ⟨hx.1.1, y, hy.1.1, hxy, by omega⟩
    have hxM := hx.2
    change M ≤ x at hxM
    dsimp [M] at hxM
    omega
  have hmap (x : ℕ) (hx : x ∈ T) : x / L ∈ Set.Iio (N / L + 1) := by
    have hh := Nat.div_le_div_right (c := L) (show x ≤ N from (show x < N from hx.1.2).le)
    exact Nat.lt_succ_of_le hh
  have hinj : Set.InjOn (fun x : ℕ => x / L) T := by
    intro x hx y hy he
    have hsame (x y : ℕ) (he : x / L = y / L) : y < x + L := by
      have hh := Nat.lt_mul_div_succ y hL
      rw [← he, Nat.mul_add, Nat.mul_one] at hh
      have hh' := Nat.mul_div_le x L
      omega
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · have hh := hsame x y he
      have hh' := hsep x y hx hy hxy
      omega
    · exact hxy
    · have hh := hsame y x he.symm
      have hh' := hsep y x hy hx hyx
      omega
  have hcard : T.ncard ≤ N / L + 1 := by
    simpa only [Nat.ncard_Iio] using Set.ncard_le_ncard_of_injOn
      (fun x : ℕ => x / L) hmap hinj
  have hsub : S ∩ Set.Iio N ⊆ Set.Iio M ∪ T := by
    intro x hx
    by_cases hm : x < M
    · exact Or.inl hm
    · exact Or.inr ⟨hx, show M ≤ x by omega⟩
  have hTfin : T.Finite := (Set.finite_Iio N).subset (fun _ h => h.1.2)
  have hc := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le (Set.Iio M) T)
  simp only [Nat.ncard_Iio] at hc
  omega

/-- If close pairs are finite at every fixed separation, the set has natural
 density zero. -/
lemma hasDensity_zero_of_finite_close_pairs {S : Set ℕ}
    (hfin : ∀ L : ℕ, {x ∈ S | ∃ y ∈ S, x < y ∧ y ≤ x + L}.Finite) :
    S.HasDensity 0 := by
  open Filter in
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n => ha.trans_le (by positivity)
  · intro b hb
    obtain ⟨L, hLb⟩ := exists_nat_gt (2 / b)
    have hLr : (0 : ℝ) < L := (by positivity : (0 : ℝ) < 2 / b).trans hLb
    have hL : 0 < L := by exact_mod_cast hLr
    have hrec : (1 : ℝ) / L < b / 2 := by
      apply (div_lt_iff₀ hLr).mpr
      have hh := (div_lt_iff₀ hb).mp hLb
      nlinarith
    obtain ⟨M, hM⟩ := sparse_close_pairs_prefix_bound hL (hfin L)
    obtain ⟨K, hKb⟩ := exists_nat_gt (2 * ((M : ℝ) + 1) / b)
    apply Filter.eventually_atTop.mpr
    refine ⟨K + 1, fun N hN => ?_⟩
    have hN0 : 0 < N := by omega
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    have hKN : (K : ℝ) < N := by exact_mod_cast (show K < N by omega)
    have hMn : (M : ℝ) + 1 < b / 2 * N := by
      have hh := (div_lt_iff₀ hb).mp (hKb.trans hKN)
      nlinarith
    have hfrac : (N : ℝ) / L < b / 2 * N := by
      calc
        _ = (N : ℝ) * (1 / L) := by ring
        _ < (N : ℝ) * (b / 2) := mul_lt_mul_of_pos_left hrec hNr
        _ = _ := by ring
    have hcount : ((S ∩ Set.Iio N).ncard : ℝ) ≤ M + (N : ℝ) / L + 1 := by
      have hh : ((S ∩ Set.Iio N).ncard : ℝ) ≤ M + (N / L : ℕ) + 1 := by
        exact_mod_cast hM N
      have hd : ((N / L : ℕ) : ℝ) ≤ (N : ℝ) / L := Nat.cast_div_le
      linarith
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    apply (div_lt_iff₀ hNr).mpr
    linarith

lemma quadratic_abscissae_hasDensity_zero {A B : ℕ} {C : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hC : C ≠ 0) :
    (quadraticPositiveAbscissae A B C).HasDensity 0 :=
  hasDensity_zero_of_finite_close_pairs (quadratic_close_abscissae_finite hA hB hC)

/-- Bases of equal cubic differences with the two prescribed gaps. -/
def fixedGapCubeBases (h k : ℕ) : Set ℕ :=
  {x | ∃ y : ℕ, (x + h) ^ 3 + y ^ 3 = x ^ 3 + (y + k) ^ 3}

lemma fixedGapCubeBase_centered {h k x : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hx : x ∈ fixedGapCubeBases h k) :
    2 * x + h ∈ quadraticPositiveAbscissae (3 * h) (3 * k) ((k : ℤ) ^ 3 - h ^ 3) := by
  obtain ⟨y, he⟩ := hx
  refine ⟨by omega, 2 * y + k, by omega, ?_⟩
  have heZ : ((x : ℤ) + h) ^ 3 + (y : ℤ) ^ 3 =
      (x : ℤ) ^ 3 + ((y : ℤ) + k) ^ 3 := by exact_mod_cast he
  push_cast
  linear_combination 4 * heZ

lemma fixedGapCubeBases_close_finite {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hne : h ≠ k) (L : ℕ) :
    {x ∈ fixedGapCubeBases h k |
      ∃ x' ∈ fixedGapCubeBases h k, x < x' ∧ x' ≤ x + L}.Finite := by
  have hC : (k : ℤ) ^ 3 - h ^ 3 ≠ 0 := by
    intro he
    have he' : k ^ 3 = h ^ 3 := by exact_mod_cast sub_eq_zero.mp he
    exact hne (Nat.pow_left_injective (by decide : 3 ≠ 0) he').symm
  have hfin := quadratic_close_abscissae_finite
    (Nat.mul_pos (by decide : 0 < 3) hh) (Nat.mul_pos (by decide : 0 < 3) hk) hC (2 * L)
  refine Set.Finite.of_injOn (f := fun x : ℕ => 2 * x + h) ?_ ?_ hfin
  · rintro x ⟨hx, x', hx', hxx', hxL⟩
    exact ⟨fixedGapCubeBase_centered hh hk hx, 2 * x' + h,
      fixedGapCubeBase_centered hh hk hx', by dsimp only; omega, by dsimp only; omega⟩
  · intro x _ y _ he
    dsimp only at he
    omega

/-- For fixed unequal positive gaps, the bases of matching cubic differences
form a set of natural density zero. -/
lemma fixedGapCubeBases_hasDensity_zero {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hne : h ≠ k) :
    (fixedGapCubeBases h k).HasDensity 0 :=
  hasDensity_zero_of_finite_close_pairs (fixedGapCubeBases_close_finite hh hk hne)

/-- The same separation holds after adding any fixed offset. -/
lemma fixedGapCubeBases_translate_hasDensity_zero {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hne : h ≠ k) (t : ℕ) :
    ((fun x : ℕ => x + t) '' fixedGapCubeBases h k).HasDensity 0 := by
  apply hasDensity_zero_of_finite_close_pairs
  intro L
  have hfin := (fixedGapCubeBases_close_finite hh hk hne L).image (fun x : ℕ => x + t)
  apply hfin.subset
  rintro _ ⟨⟨x, hx, rfl⟩, _, ⟨x', hx', rfl⟩, hxx', hxL⟩
  dsimp only at hxx' hxL
  exact ⟨x, ⟨hx, x', hx', by omega, by omega⟩, rfl⟩

/-- A prefix count using the number, rather than the locations, of close pairs. -/
lemma close_pairs_count_prefix {S : Set ℕ} {L : ℕ} (hL : 0 < L)
    (hfin : {x ∈ S | ∃ y ∈ S, x < y ∧ y ≤ x + L}.Finite) (N : ℕ) :
    (S ∩ Set.Iio N).ncard ≤
      {x ∈ S | ∃ y ∈ S, x < y ∧ y ≤ x + L}.ncard + N / L + 1 := by
  classical
  let D := {x ∈ S | ∃ y ∈ S, x < y ∧ y ≤ x + L}
  let T := (S ∩ Set.Iio N) \ D
  have hsep (x y : ℕ) (hx : x ∈ T) (hy : y ∈ T) (hxy : x < y) : x + L < y := by
    by_contra hh
    exact hx.2 ⟨hx.1.1, y, hy.1.1, hxy, by omega⟩
  have hmap (x : ℕ) (hx : x ∈ T) : x / L ∈ Set.Iio (N / L + 1) := by
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (c := L) (show x < N from hx.1.2).le)
  have hinj : Set.InjOn (fun x : ℕ => x / L) T := by
    intro x hx y hy he
    have hsame (x y : ℕ) (he : x / L = y / L) : y < x + L := by
      have hh := Nat.lt_mul_div_succ y hL
      rw [← he, Nat.mul_add, Nat.mul_one] at hh
      have hh' := Nat.mul_div_le x L
      omega
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · have hh := hsame x y he
      have hh' := hsep x y hx hy hxy
      omega
    · exact hxy
    · have hh := hsame y x he.symm
      have hh' := hsep y x hy hx hyx
      omega
  have hcard : T.ncard ≤ N / L + 1 := by
    simpa only [Nat.ncard_Iio] using Set.ncard_le_ncard_of_injOn
      (fun x : ℕ => x / L) hmap hinj
  have hsub : S ∩ Set.Iio N ⊆ D ∪ T := by
    intro x hx
    by_cases hd : x ∈ D
    · exact Or.inl hd
    · exact Or.inr ⟨hx, hd⟩
  have hTfin : T.Finite := (Set.finite_Iio N).subset (fun _ h => h.1.2)
  have hc := (Set.ncard_le_ncard hsub (hfin.union hTfin)).trans (Set.ncard_union_le D T)
  dsimp only [D] at hc
  omega

/-- A power-saving prefix estimate along a geometric sequence of cutoffs. -/
lemma quadratic_abscissae_pow_prefix_bound {A B : ℕ} {C : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hC : C ≠ 0) (j : ℕ) :
    (quadraticPositiveAbscissae A B C ∩ Set.Iio (16 ^ j)).ncard ≤
      (A * (2 * (B + C.natAbs + 1) + 1) + 2) * 8 ^ j := by
  let L := 2 ^ j
  let D := B + C.natAbs + 1
  have hL : 0 < L := pow_pos (by decide) _
  have hL1 : 1 ≤ L := hL
  obtain ⟨hf, hc⟩ := quadratic_close_abscissae_bounds hA hB hC L
  have hp := close_pairs_count_prefix hL hf (16 ^ j)
  have hdiv : 16 ^ j / L = 8 ^ j := by
    have he : 16 ^ j = 8 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
    rw [he, Nat.mul_div_cancel _ hL]
  have hpow : L ^ 3 = 8 ^ j := by
    dsimp [L]
    rw [← pow_mul, Nat.mul_comm j 3, pow_mul]
    norm_num
  have hlin : 2 * D + L ≤ (2 * D + 1) * L := by nlinarith
  have hterm : L * (A * L * (2 * D + L)) ≤ (A * (2 * D + 1)) * L ^ 3 := by
    calc
      _ = A * L ^ 2 * (2 * D + L) := by ring
      _ ≤ A * L ^ 2 * ((2 * D + 1) * L) := Nat.mul_le_mul_left _ hlin
      _ = _ := by ring
  rw [hpow] at hterm
  rw [hdiv] at hp
  have h8 : 1 ≤ 8 ^ j := Nat.one_le_pow _ _ (by decide)
  change _ ≤ (A * (2 * D + 1) + 2) * 8 ^ j
  change _ ≤ L * (A * L * (2 * D + L)) at hc
  nlinarith

#print axioms quadratic_abscissae_pow_prefix_bound
#print axioms quadratic_abscissae_hasDensity_zero
#print axioms fixedGapCubeBases_hasDensity_zero
#print axioms fixedGapCubeBases_translate_hasDensity_zero

end Erdos1206
