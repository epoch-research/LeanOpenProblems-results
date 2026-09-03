import FormalConjecturesUtil

namespace Erdos952Investigation

lemma gaussian_norm_sq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  simp [Zsqrtd.norm, pow_two]

lemma norm_sublevel_finite (B : ℤ) : {z : GaussianInt | z.norm ≤ B}.Finite := by
  let S : Set (ℤ × ℤ) := Set.Icc (-B) B ×ˢ Set.Icc (-B) B
  have hS : S.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  have hinj : Function.Injective (fun z : GaussianInt => (z.re, z.im)) := by
    intro z w h
    exact Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  apply (hS.preimage hinj.injOn).subset
  intro z hz
  have hz' : z.re ^ 2 + z.im ^ 2 ≤ B := by simpa [gaussian_norm_sq] using hz
  have hr := Int.le_self_sq z.re
  have hr' := Int.le_self_sq (-z.re)
  have hi := Int.le_self_sq z.im
  have hi' := Int.le_self_sq (-z.im)
  change z.re ∈ Set.Icc (-B) B ∧ z.im ∈ Set.Icc (-B) B
  constructor <;> constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg z.im]

lemma injective_escapes_norm (x : ℕ → GaussianInt) (hx : Function.Injective x) :
    ∀ B : ℤ, ∃ N : ℕ, ∀ n ≥ N, B < (x n).norm := by
  intro B
  have hfinite : {n | (x n).norm ≤ B}.Finite :=
    (norm_sublevel_finite B).preimage (f := x) hx.injOn
  have hbounded := hfinite.bddAbove
  obtain ⟨N, hN⟩ := hbounded
  refine ⟨N + 1, ?_⟩
  intro n hn
  by_contra h
  have hle : (x n).norm ≤ B := le_of_not_gt h
  have := hN hle
  omega

lemma prime_even_coordinate_sum {z : GaussianInt} (hz : Prime z)
    (he : Even (z.re + z.im)) : z.norm = 2 := by
  obtain ⟨k, hk⟩ := he
  let a : GaussianInt := ⟨1, 1⟩
  let b : GaussianInt := ⟨k, z.im - k⟩
  have hab : z = a * b := by
    apply Zsqrtd.ext <;> simp [a, b, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> omega
  have ha : a.norm = 2 := by norm_num [a, gaussian_norm_sq]
  have hau : ¬ IsUnit a := by
    intro h
    have := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) a).mpr h
    omega
  have hbu := (hz.irreducible.isUnit_or_isUnit hab).resolve_left hau
  have hb : b.norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) b).mpr hbu
  rw [hab, Zsqrtd.norm_mul, ha, hb, mul_one]

lemma norm_mod_two (z : GaussianInt) : z.norm % 2 = (z.re + z.im) % 2 := by
  rcases Int.emod_two_eq_zero_or_one z.re with hr | hr <;>
    rcases Int.emod_two_eq_zero_or_one z.im with hi | hi <;>
    simp [gaussian_norm_sq, pow_two, Int.add_emod, Int.mul_emod, hr, hi]

lemma prime_large_odd_coordinate_sum {z : GaussianInt} (hz : Prime z)
    (hlarge : 2 < z.norm) : (z.re + z.im) % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one (z.re + z.im) with h | h
  · have hnorm := prime_even_coordinate_sum hz (Int.even_iff.mpr h)
    omega
  · exact h

lemma large_prime_difference_even_norm {z w : GaussianInt} (hz : Prime z) (hw : Prime w)
    (hzlarge : 2 < z.norm) (hwlarge : 2 < w.norm) : (w - z).norm % 2 = 0 := by
  rw [norm_mod_two]
  change ((w.re - z.re) + (w.im - z.im)) % 2 = 0
  calc
    _ = ((w.re + w.im) - (z.re + z.im)) % 2 := by congr 1 <;> ring
    _ = 0 := by
      rw [Int.sub_emod, prime_large_odd_coordinate_sum hw hwlarge,
        prime_large_odd_coordinate_sum hz hzlarge]
      norm_num

lemma step_bound_gt_two (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) : 2 < C := by
  obtain ⟨N, hN⟩ := injective_escapes_norm x hx 2
  have heven := large_prime_difference_even_norm (h N).1 (h (N + 1)).1
    (hN N le_rfl) (hN (N + 1) (by omega))
  have hne : x (N + 1) - x N ≠ 0 := by
    intro heq
    have := hx (sub_eq_zero.mp heq)
    omega
  have hpos := GaussianInt.norm_pos.mpr hne
  have hlt := (h N).2
  omega

lemma prime_norm_divisor_bound {z : GaussianInt} {p : ℕ} (hz : Prime z)
    (hp : p.Prime) (hdiv : (p : ℤ) ∣ z.norm) : z.norm ≤ (p : ℤ) ^ 2 := by
  have hn : z.norm.natAbs ≠ 0 := by
    intro hn
    exact hz.ne_zero (GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp hn))
  have hzdvd : z ∣ ((z.norm.natAbs.primeFactorsList.map
      (fun q : ℕ => (q : GaussianInt))).prod) := by
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList hn]
    rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right z (star z)
  obtain ⟨q', hq', hzq'⟩ := hz.dvd_prod_iff.mp hzdvd
  obtain ⟨q, hqmem, rfl⟩ := List.mem_map.mp hq'
  have hq := Nat.prime_of_mem_primeFactorsList hqmem
  have hnormdvd : z.norm ∣ (q : ℤ) ^ 2 := by
    simpa [pow_two] using map_dvd (Zsqrtd.normMonoidHom (d := -1)) hzq'
  have hpq : p ∣ q ^ 2 := by
    exact Int.natCast_dvd_natCast.mp (by simpa using hdiv.trans hnormdvd)
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpq)
  subst q
  have hp0 : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  exact Int.le_of_dvd (by positivity) hnormdvd

lemma prime_large_norm_residue {z : GaussianInt} {p : ℕ} (hz : Prime z)
    (hp : p.Prime) (hlarge : (p : ℤ) ^ 2 < z.norm) : z.norm % p ≠ 0 := by
  intro h
  have := prime_norm_divisor_bound hz hp (Int.dvd_of_emod_eq_zero h)
  omega

#print axioms prime_norm_divisor_bound
#print axioms prime_large_norm_residue

#print axioms gaussian_norm_sq
#print axioms norm_sublevel_finite
#print axioms injective_escapes_norm
#print axioms prime_even_coordinate_sum
#print axioms large_prime_difference_even_norm
#print axioms step_bound_gt_two

end Erdos952Investigation
