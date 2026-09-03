import Submission.Structure

/-!
Exact pair-sum defect and a local square-Sidon criterion. These lemmas do not
improve the known asymptotic exponent and do not settle Erdős 773.
-/
namespace Erdos773.OrderedCollisionDefect
open Finset
set_option maxHeartbeats 1000000

/-- The pair-sum defect of four strictly ordered colliding roots is even. -/
lemma normalized_parameters {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a ^ 2 + d ^ 2 = b ^ 2 + c ^ 2) :
    ∃ z y t : ℕ, 0 < z ∧ 0 < y ∧ 0 < t ∧
      b = a + z + 2 * t ∧ c = a + z + 2 * t + y ∧
      d = a + 2 * z + 2 * t + y ∧ 2 * t * (a + t) = z * (z + y) := by
  obtain ⟨z, y, k, hz, hy, hk, hb, hc, hd, hprod⟩ :=
    ordered_square_collision_parameters hab hbc hcd he
  have hm := Nat.mul_mod k (2 * a + k) 2
  have ha2 : (2 * a + k) % 2 = k % 2 := by omega
  have hr : (2 * z * (z + y)) % 2 = 0 := by rw [mul_assoc]; omega
  rw [hprod, hr, ha2] at hm
  have hkrem := Nat.mod_lt k (by decide : 0 < 2)
  have hkmod : k % 2 = 0 := by
    interval_cases hh : k % 2 <;> norm_num at *
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hkmod
  refine ⟨z, y, t, hz, hy, by omega, by omega, by omega, by omega, ?_⟩
  subst k
  nlinarith only [hprod]

/-- The exact relationship between the span, the middle gap, and the defect. -/
lemma span_identity (a z y t : ℕ)
    (he : 2 * t * (a + t) = z * (z + y)) :
    4 * t * (2 * a + 2 * z + 3 * t + y) + y ^ 2 =
      (2 * z + 2 * t + y) ^ 2 := by
  nlinarith only [he]

lemma ordered_span_bound {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a ^ 2 + d ^ 2 = b ^ 2 + c ^ 2) :
    4 * (a + d + 1) + 1 ≤ (d - a) ^ 2 := by
  obtain ⟨z, y, t, hz, hy, ht, hb, hc, hd, hp⟩ :=
    normalized_parameters hab hbc hcd he
  have hs := span_identity a z y t hp
  have hspan : d - a = 2 * z + 2 * t + y := by omega
  rw [hspan, hd]
  have hm := Nat.mul_le_mul_left (2 * a + 2 * z + 3 * t + y)
    (show 1 ≤ t by omega)
  nlinarith only [hs, hm, ht, hy]

private lemma square_mod_two (n : ℕ) : n ^ 2 % 2 = n % 2 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt n (by decide : 0 < 2)
  interval_cases hh : n % 2 <;> norm_num

private lemma equal_sums_of_short_span (L H a b c d : ℕ)
    (ha : L ≤ a ∧ a ≤ L + H) (hb : L ≤ b ∧ b ≤ L + H)
    (hc : L ≤ c ∧ c ≤ L + H) (hd : L ≤ d ∧ d ≤ L + H)
    (hshort : H ^ 2 < 8 * L + 4)
    (he : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) : a + b = c + d := by
  have hmod := congrArg (fun n : ℕ => n % 2) he
  dsimp only at hmod
  rw [Nat.add_mod (a ^ 2) (b ^ 2) 2, Nat.add_mod (c ^ 2) (d ^ 2) 2,
    square_mod_two, square_mod_two, square_mod_two, square_mod_two] at hmod
  have hbound (x y : ℕ) (hx : L ≤ x ∧ x ≤ L + H)
      (hy : L ≤ y ∧ y ≤ L + H) : (x : ℤ) ^ 2 + y ^ 2 - 2 * x * y ≤ H ^ 2 := by
    have hu : (x : ℤ) - y ≤ H := by omega
    have hl : -(H : ℤ) ≤ (x : ℤ) - y := by omega
    have hp := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)
    nlinarith only [hp]
  have habound := hbound a b ha hb
  have hcdbound := hbound c d hc hd
  have heZ : (a : ℤ) ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by exact_mod_cast he
  have hshortZ : (H : ℤ) ^ 2 < 8 * L + 4 := by exact_mod_cast hshort
  have hsumab : (2 : ℤ) * L ≤ a + b := by omega
  have hsumcd : (2 : ℤ) * L ≤ c + d := by omega
  rcases lt_trichotomy (a + b) (c + d) with hlt | heq | hgt
  · have hgap : (a : ℤ) + b + 2 ≤ c + d := by omega
    have hprod := mul_nonneg (sub_nonneg.mpr hgap)
      (show (0 : ℤ) ≤ a + b + c + d + 2 by positivity)
    nlinarith [sq_nonneg ((c : ℤ) - d)]
  · exact heq
  · have hgap : (c : ℤ) + d + 2 ≤ a + b := by omega
    have hprod := mul_nonneg (sub_nonneg.mpr hgap)
      (show (0 : ℤ) ≤ a + b + c + d + 2 by positivity)
    nlinarith [sq_nonneg ((a : ℤ) - b)]

/-- Every sufficiently short interval of nonnegative roots has Sidon squares.
    The criterion is local, with a square-root-scale interval length. -/
lemma short_interval_squares_sidon (L H : ℕ) (hshort : H ^ 2 < 8 * L + 4) :
    IsSidon (((Icc L (L + H)).image (fun n : ℕ => n ^ 2)) : Set ℕ) := by
  intro a ha c hc b hb d hd he
  obtain ⟨a, ha', rfl⟩ := mem_image.mp (Finset.mem_coe.mp ha)
  obtain ⟨b, hb', rfl⟩ := mem_image.mp (Finset.mem_coe.mp hb)
  obtain ⟨c, hc', rfl⟩ := mem_image.mp (Finset.mem_coe.mp hc)
  obtain ⟨d, hd', rfl⟩ := mem_image.mp (Finset.mem_coe.mp hd)
  have hs := equal_sums_of_short_span L H a b c d (mem_Icc.mp ha') (mem_Icc.mp hb')
    (mem_Icc.mp hc') (mem_Icc.mp hd') hshort he
  have hf : ((a : ℤ) - c) * (a - d) = 0 := by
    have hsZ : (a : ℤ) + b = c + d := by exact_mod_cast hs
    have heZ : (a : ℤ) ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by exact_mod_cast he
    nlinarith [sq_nonneg ((a : ℤ) + b - c - d)]
  rcases mul_eq_zero.mp hf with hh | hh
  · left
    have hac : a = c := by omega
    have hbd : b = d := by omega
    simp [hac, hbd]
  · right
    have had : a = d := by omega
    have hbc : b = c := by omega
    simp [had, hbc]

/-- An explicit four-root family attaining the ordered span bound. -/
lemma short_collision_family (u : ℕ) (hu : 1 ≤ u) :
    let a := 2 * u ^ 2 + u - 1
    let b := 2 * u ^ 2 + 3 * u + 1
    let c := 2 * u ^ 2 + 3 * u + 2
    let d := 2 * u ^ 2 + 5 * u + 2
    a < b ∧ b < c ∧ c < d ∧
      a ^ 2 + d ^ 2 = b ^ 2 + c ^ 2 ∧
      (d - a) ^ 2 = 4 * (a + d + 1) + 1 := by
  have ha : 2 * u ^ 2 + u - 1 + 1 = 2 * u ^ 2 + u := by omega
  dsimp only
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · have hprod : 2 * 1 * (2 * u ^ 2 + u - 1 + 1) = (2 * u) * (2 * u + 1) := by
      rw [ha]; ring
    nlinarith only [hprod, ha]
  · have hspan : 2 * u ^ 2 + 5 * u + 2 - (2 * u ^ 2 + u - 1) = 4 * u + 3 := by omega
    rw [hspan]
    nlinarith only [ha]

lemma family_interval_not_sidon (u : ℕ) (hu : 1 ≤ u) :
    ¬ IsSidon (((Icc (2 * u ^ 2 + u - 1) (2 * u ^ 2 + 5 * u + 2)).image
      (fun n : ℕ => n ^ 2)) : Set ℕ) := by
  obtain ⟨hab, hbc, hcd, he, hspan⟩ := short_collision_family u hu
  let a := 2 * u ^ 2 + u - 1
  let b := 2 * u ^ 2 + 3 * u + 1
  let c := 2 * u ^ 2 + 3 * u + 2
  let d := 2 * u ^ 2 + 5 * u + 2
  change a < b at hab
  change b < c at hbc
  change c < d at hcd
  change a ^ 2 + d ^ 2 = b ^ 2 + c ^ 2 at he
  change ¬ IsSidon (((Icc a d).image (fun n : ℕ => n ^ 2)) : Set ℕ)
  have hm (n : ℕ) (hn : a ≤ n ∧ n ≤ d) :
      n ^ 2 ∈ (((Icc a d).image (fun n : ℕ => n ^ 2)) : Set ℕ) :=
    Finset.mem_coe.mpr (mem_image.mpr ⟨n, mem_Icc.mpr hn, rfl⟩)
  intro hs
  have hh := hs _ (hm a (by omega)) _ (hm b (by omega))
    _ (hm d (by omega)) _ (hm c (by omega)) he
  rcases hh with hh | hh <;> nlinarith [hh.1]

/-- The leading constant 8 in the local criterion cannot be increased uniformly
    for full intervals. This says nothing similar about arbitrary root subsets. -/
lemma full_interval_constant_optimal (η : ℝ) (hη : 0 < η) :
    ∃ L H : ℕ, (H : ℝ) ^ 2 < (8 + η) * L ∧
      ¬ IsSidon (((Icc L (L + H)).image (fun n : ℕ => n ^ 2)) : Set ℕ) := by
  obtain ⟨u, hu⟩ := exists_nat_ge (max 1 (34 / η))
  have hu1R : (1 : ℝ) ≤ u := (le_max_left _ _).trans hu
  have hu1 : 1 ≤ u := by exact_mod_cast hu1R
  have hηu : (34 : ℝ) ≤ η * u := by
    have h := (div_le_iff₀ hη).mp ((le_max_right _ _).trans hu)
    linarith only [h]
  let L := 2 * u ^ 2 + u - 1
  let H := 4 * u + 3
  have hLnat : L + 1 = 2 * u ^ 2 + u := by dsimp [L]; omega
  have hL : (L : ℝ) + 1 = 2 * (u : ℝ) ^ 2 + u := by exact_mod_cast hLnat
  have hH : (H : ℝ) = 4 * u + 3 := by dsimp [H]; norm_cast
  have hLlo : (u : ℝ) ^ 2 ≤ L := by nlinarith
  refine ⟨L, H, ?_, ?_⟩
  · have hp := mul_le_mul_of_nonneg_left hLlo hη.le
    have hp' := mul_le_mul_of_nonneg_right hηu (by positivity : (0 : ℝ) ≤ u)
    rw [hH]
    nlinarith only [hL, hp, hp', hu1R]
  · have he : L + H = 2 * u ^ 2 + 5 * u + 2 := by dsimp [H]; omega
    rw [he]
    exact family_interval_not_sidon u hu1

#print axioms normalized_parameters
#print axioms ordered_span_bound
#print axioms short_interval_squares_sidon
#print axioms full_interval_constant_optimal
end Erdos773.OrderedCollisionDefect
