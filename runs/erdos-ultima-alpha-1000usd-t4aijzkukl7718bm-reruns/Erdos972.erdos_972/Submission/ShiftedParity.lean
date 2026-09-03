import FormalConjecturesUtil

/-!
# Parity obstructions for shifted rational slopes

Auxiliary work for Erdős 972. Odd outputs are not asserted to be prime.

For a reduced rational slope `a/b`, an arbitrary real shift cannot make all
sufficiently large prime inputs have even outputs unless `b = 1` or `b = 3`.
Consequently a convergent sequence of rational slopes with such shifted parity
obstructions has a rational limit. This excludes one proposed counterexample
construction; it is not a proof of the original conjecture.
-/

namespace Explore972

/-- Four explicit odd reduced residues show that an odd modulus at least five
has no reduced-residue gap as long as half of `2*b`. -/
lemma odd_coprime_in_integer_window (b z : ℤ) (hb : 5 ≤ b) (hbo : Odd b) :
    ∃ k : ℤ, z < k ∧ k ≤ z + b ∧ Odd k ∧ IsCoprime k b := by
  have hbmod : b % 2 = 1 := Int.odd_iff.mp hbo
  have hc2 : IsCoprime (2 : ℤ) b := by
    obtain ⟨t, ht⟩ := hbo
    refine ⟨-t, 1, ?_⟩
    omega
  have hcminus : IsCoprime (b - 2) b := by
    convert hc2.neg_left.add_mul_right_left 1 using 1 <;> ring
  have hcplus : IsCoprime (b + 2) b := by
    convert hc2.add_mul_right_left 1 using 1 <;> ring
  have hcend : IsCoprime (2 * b - 1) b := by
    convert (isCoprime_one_left (x := b)).neg_left.add_mul_right_left 2 using 1 <;> ring
  have hcwrap : IsCoprime (2 * b + 1) b := by
    convert (isCoprime_one_left (x := b)).add_mul_right_left 2 using 1 <;> ring
  let r : ℤ := z % (2 * b)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrb : r < 2 * b := Int.emod_lt_of_pos _ (by omega)
  have hj : ∃ j : ℤ, r < j ∧ j ≤ r + b ∧ j % 2 = 1 ∧ IsCoprime j b := by
    by_cases h1 : r < 1
    · exact ⟨1, h1, by omega, by norm_num, isCoprime_one_left⟩
    by_cases h2 : r < b - 2
    · exact ⟨b - 2, h2, by omega, by omega, hcminus⟩
    by_cases h3 : r < b + 2
    · exact ⟨b + 2, h3, by omega, by omega, hcplus⟩
    by_cases h4 : r < 2 * b - 1
    · exact ⟨2 * b - 1, h4, by omega, by omega, hcend⟩
    · exact ⟨2 * b + 1, by omega, by omega, by omega, hcwrap⟩
  obtain ⟨j, hrj, hjb, hjo, hjc⟩ := hj
  let t : ℤ := z / (2 * b)
  have hz : z = r + 2 * b * t := (Int.emod_add_mul_ediv z (2 * b)).symm
  refine ⟨j + 2 * b * t, by omega, by omega, ?_, ?_⟩
  · apply Int.odd_iff.mpr
    simp [Int.add_emod, Int.mul_emod, hjo]
  · convert hjc.add_mul_right_left (2 * t) using 1 <;> ring

/-- For odd moduli at least five, either prescribed parity can be represented
by a coprime integer in every interval of length `b`. -/
lemma coprime_of_parity_in_integer_window (b z e : ℤ) (hb : 5 ≤ b) (hbo : Odd b) :
    ∃ k : ℤ, z < k ∧ k ≤ z + b ∧ k % 2 = e % 2 ∧ IsCoprime k b := by
  by_cases he : e % 2 = 1
  · obtain ⟨k, hklo, hkhi, hko, hkc⟩ := odd_coprime_in_integer_window b z hb hbo
    exact ⟨k, hklo, hkhi, by simpa [he] using Int.odd_iff.mp hko, hkc⟩
  · obtain ⟨k, hklo, hkhi, hko, hkc⟩ :=
      odd_coprime_in_integer_window b (z - b) hb hbo
    have hkmod := Int.odd_iff.mp hko
    have hbmod := Int.odd_iff.mp hbo
    refine ⟨k + b, by omega, by omega, by omega, ?_⟩
    simpa using hkc.add_mul_right_left 1

lemma coprime_of_parity_in_real_window (b e : ℤ) (hb : 5 ≤ b) (hbo : Odd b) (x : ℝ) :
    ∃ k : ℤ, x ≤ k ∧ (k : ℝ) < x + b ∧ k % 2 = e % 2 ∧ IsCoprime k b := by
  obtain ⟨k, hklo, hkhi, hkpar, hkc⟩ :=
    coprime_of_parity_in_integer_window b (⌈x⌉ - 1) e hb hbo
  have hklo' : (⌈x⌉ : ℝ) ≤ k := by exact_mod_cast (show ⌈x⌉ ≤ k by omega)
  have hkhi' : (k : ℝ) ≤ (⌈x⌉ : ℝ) - 1 + b := by exact_mod_cast hkhi
  refine ⟨k, (Int.le_ceil x).trans hklo', ?_, hkpar, hkc⟩
  linarith [Int.ceil_lt_add_one x]

#print axioms coprime_of_parity_in_real_window


lemma affine_odd_lift_mod_two :
    ∀ a b r s : ZMod 2, (a ≠ 0 ∨ b ≠ 0) →
      a * r - b * s = a - b → ∃ t : ZMod 2, b * t + r = 1 ∧ a * t + s = 1 := by
  decide

/-- A Bézout model with both linear forms odd at the initial parameter. -/
lemma shifted_odd_affine_model (a b : ℕ) (hab : a.Coprime b) (k : ℤ)
    (hkc : IsCoprime k (b : ℤ)) (hkpar : k % 2 = ((a : ℤ) - b) % 2) :
    ∃ r s : ℤ, (a : ℤ) * r - b * s = k ∧
      IsCoprime r (b : ℤ) ∧ Odd r ∧ Odd s := by
  have hc : IsCoprime (a : ℤ) (b : ℤ) := by exact_mod_cast hab
  obtain ⟨u, v, huv⟩ := hc
  let r : ℤ := k * u
  let s : ℤ := -(k * v)
  have hdet : (a : ℤ) * r - b * s = k := by
    dsimp [r, s]
    nlinarith [congrArg (fun t : ℤ => k * t) huv]
  have hrc : IsCoprime r (b : ℤ) := by
    have he : k + s * b = (a : ℤ) * r := by linarith
    have h := hkc.add_mul_right_left s
    rw [he] at h
    exact h.of_mul_left_right
  have hnonzero : (a : ZMod 2) ≠ 0 ∨ (b : ZMod 2) ≠ 0 := by
    by_contra! h
    have hz := congrArg (fun t : ℤ => (t : ZMod 2)) huv
    push_cast at hz
    simp [h.1, h.2] at hz
  have hkz : (k : ZMod 2) = (a : ZMod 2) - b := by
    have h := (ZMod.intCast_eq_intCast_iff k ((a : ℤ) - b) 2).mpr hkpar
    simpa using h
  have hdetz : (a : ZMod 2) * r - b * s = (a : ZMod 2) - b := by
    have h := congrArg (fun t : ℤ => (t : ZMod 2)) hdet
    simpa [hkz] using h
  obtain ⟨t, ht₁, ht₂⟩ := affine_odd_lift_mod_two a b r s hnonzero hdetz
  let r' : ℤ := b * (t.val : ℤ) + r
  let s' : ℤ := a * (t.val : ℤ) + s
  have hr'z : (r' : ZMod 2) = 1 := by simpa [r'] using ht₁
  have hs'z : (s' : ZMod 2) = 1 := by simpa [s'] using ht₂
  refine ⟨r', s', ?_, ?_, ?_, ?_⟩
  · dsimp [r', s']
    nlinarith [hdet]
  · simpa [r', add_comm, mul_comm] using hrc.add_mul_right_left (t.val : ℤ)
  · apply Int.odd_iff.mpr
    have h := (ZMod.intCast_eq_intCast_iff r' 1 2).mp (by simpa using hr'z)
    exact h
  · apply Int.odd_iff.mpr
    have h := (ZMod.intCast_eq_intCast_iff s' 1 2).mp (by simpa using hs'z)
    exact h

lemma floor_shifted_rational_affine (a b r s k : ℤ) (β : ℝ) (hb : 0 < b)
    (hklo : 0 ≤ (k : ℝ) / b + β) (hkhi : (k : ℝ) / b + β < 1)
    (hdet : a * r - b * s = k) (t : ℤ) :
    ⌊(a : ℝ) / b * ((b * t + r : ℤ) : ℝ) + β⌋ = a * t + s := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hdetR : (a : ℝ) * r - b * s = k := by exact_mod_cast hdet
  have he : (a : ℝ) / b * ((b * t + r : ℤ) : ℝ) + β =
      (k : ℝ) / b + β + ((a * t + s : ℤ) : ℝ) := by
    push_cast
    field_simp
    nlinarith [hdetR]
  rw [he, Int.floor_add_intCast]
  have hz : ⌊(k : ℝ) / b + β⌋ = (0 : ℤ) :=
    Int.floor_eq_iff.mpr (by simpa using And.intro hklo hkhi)
  rw [hz, zero_add]

/-- Dirichlet's theorem turns a floor-compatible odd affine model into
arbitrarily large prime inputs with odd integer floors. -/
lemma prime_indices_odd_of_affine_model (a b : ℕ) (hb : 0 < b) (β : ℝ)
    (r s : ℤ) (hrb : IsCoprime r (b : ℤ)) (hro : Odd r) (hso : Odd s)
    (hfloor : ∀ t : ℤ,
      ⌊(a : ℝ) / b * ((b * t + r : ℤ) : ℝ) + β⌋ = (a : ℤ) * t + s) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ Odd ⌊(a : ℝ) / b * p + β⌋ := by
  have hrc2 : IsCoprime r (2 : ℤ) := by
    obtain ⟨t, ht⟩ := hro
    exact ⟨1, -t, by omega⟩
  have hrc : IsCoprime r ((2 * b : ℕ) : ℤ) := by
    simpa using hrc2.mul_right hrb
  obtain ⟨p, hNp, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq N
    (show 2 * b ≠ 0 by omega) hrc
  obtain ⟨t, ht⟩ := hmod.symm.dvd
  have hpeq : (p : ℤ) = b * (2 * t) + r := by
    push_cast at ht
    nlinarith
  have hf : ⌊(a : ℝ) / b * p + β⌋ = (a : ℤ) * (2 * t) + s := by
    convert hfloor (2 * t) using 1
    rw [← hpeq]
    simp
  refine ⟨p, hNp, hp, ?_⟩
  rw [hf]
  apply Int.odd_iff.mpr
  have hsm := Int.odd_iff.mp hso
  simp [Int.add_emod, Int.mul_emod, hsm]

/-- Odd denominators at least five cannot support an eventual parity
obstruction, even after an arbitrary real shift. This does not assert prime
outputs. -/
theorem odd_denominator_shift_has_odd_outputs (a b : ℕ) (hb : 5 ≤ b)
    (hbo : Odd b) (hab : a.Coprime b) (β : ℝ) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ Odd ⌊(a : ℝ) / b * p + β⌋ := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  obtain ⟨k, hklo, hkhi, hkpar, hkc⟩ := coprime_of_parity_in_real_window
    b ((a : ℤ) - b) (by exact_mod_cast hb) (by exact_mod_cast hbo) (-(b : ℝ) * β)
  push_cast at hkhi
  obtain ⟨r, s, hdet, hrc, hro, hso⟩ := shifted_odd_affine_model a b hab k hkc hkpar
  apply prime_indices_odd_of_affine_model a b (by omega) β r s hrc hro hso _ N
  intro t
  apply floor_shifted_rational_affine a b r s k β (by exact_mod_cast (show 0 < b by omega))
  · push_cast
    have hk := (le_div_iff₀ hbr).mpr (show -β * b ≤ (k : ℝ) by nlinarith [hklo])
    linarith
  · push_cast
    have hk := (div_lt_iff₀ hbr).mpr (show (k : ℝ) < (1 - β) * b by nlinarith [hkhi])
    linarith
  · exact hdet

#print axioms odd_denominator_shift_has_odd_outputs

lemma even_modulus_odd_coprime_real_window (b : ℤ) (hb : 0 < b) (hbe : Even b) (x : ℝ) :
    ∃ k : ℤ, x ≤ k ∧ (k : ℝ) < x + b ∧ Odd k ∧ IsCoprime k b := by
  let t : ℤ := ⌈(x - 1) / b⌉
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have htlo : (x - 1) / b ≤ (t : ℝ) := Int.le_ceil _
  have hthi : (t : ℝ) < (x - 1) / b + 1 := Int.ceil_lt_add_one _
  have hlo : x - 1 ≤ (t : ℝ) * b := (div_le_iff₀ hbr).mp htlo
  have hhi : ((t : ℝ) - 1) * b < x - 1 := (lt_div_iff₀ hbr).mp (by linarith)
  refine ⟨1 + b * t, ?_, ?_, ?_, ?_⟩
  · push_cast
    nlinarith
  · push_cast
    nlinarith
  · exact (hbe.mul_right t).one_add
  · exact isCoprime_one_left.add_mul_left_left t

/-- Even denominators also rule out an eventual parity obstruction for every
real shift. -/
theorem even_denominator_shift_has_odd_outputs (a b : ℕ) (hb : 0 < b)
    (hbe : Even b) (hab : a.Coprime b) (β : ℝ) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ Odd ⌊(a : ℝ) / b * p + β⌋ := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hao : Odd a := (hab.of_dvd_right (even_iff_two_dvd.mp hbe)).odd_of_right
  obtain ⟨k, hklo, hkhi, hko, hkc⟩ := even_modulus_odd_coprime_real_window b
    (by exact_mod_cast hb) (by exact_mod_cast hbe) (-(b : ℝ) * β)
  push_cast at hkhi
  have hkpar : k % 2 = ((a : ℤ) - b) % 2 := by
    have haodd : Odd (a : ℤ) := by exact_mod_cast hao
    have hbeven : Even (b : ℤ) := by exact_mod_cast hbe
    have hdiff : Odd ((a : ℤ) - b) := haodd.sub_even hbeven
    rw [Int.odd_iff.mp hko, Int.odd_iff.mp hdiff]
  obtain ⟨r, s, hdet, hrc, hro, hso⟩ := shifted_odd_affine_model a b hab k hkc hkpar
  apply prime_indices_odd_of_affine_model a b hb β r s hrc hro hso _ N
  intro t
  apply floor_shifted_rational_affine a b r s k β (by exact_mod_cast hb)
  · push_cast
    have hk := (le_div_iff₀ hbr).mpr (show -β * b ≤ (k : ℝ) by nlinarith [hklo])
    linarith
  · push_cast
    have hk := (div_lt_iff₀ hbr).mpr (show (k : ℝ) < (1 - β) * b by nlinarith [hkhi])
    linarith
  · exact hdet

/-- Denominators other than one or three cannot support an eventual parity
obstruction after any fixed shift. -/
theorem rational_shift_has_odd_outputs (a b : ℕ) (hb : 1 < b) (hb3 : b ≠ 3)
    (hab : a.Coprime b) (β : ℝ) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ Odd ⌊(a : ℝ) / b * p + β⌋ := by
  rcases Nat.even_or_odd b with hbe | hbo
  · exact even_denominator_shift_has_odd_outputs a b (by omega) hbe hab β N
  · have hbmod := Nat.odd_iff.mp hbo
    exact odd_denominator_shift_has_odd_outputs a b (by omega) hbo hab β N

/-- The same result for the natural floor, using positivity at sufficiently
large prime inputs. No claim of prime outputs is made. -/
theorem rational_shift_has_odd_nat_outputs (a b : ℕ) (hb : 1 < b) (hb3 : b ≠ 3)
    (hab : a.Coprime b) (β : ℝ) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ Odd ⌊(a : ℝ) / b * p + β⌋₊ := by
  have ha : 0 < a := by
    by_contra h
    have he : a = 0 := by omega
    simp [he] at hab
    omega
  have hα : (0 : ℝ) < (a : ℝ) / b := by positivity
  obtain ⟨L, hL⟩ := exists_nat_gt (-β / ((a : ℝ) / b))
  obtain ⟨p, hNp, hp, ho⟩ := rational_shift_has_odd_outputs a b hb hb3 hab β (max N L)
  have hpL : (L : ℝ) < p := by exact_mod_cast (lt_of_le_of_lt (le_max_right N L) hNp)
  have hx : 0 ≤ (a : ℝ) / b * p + β := by
    have h := (div_lt_iff₀ hα).mp (hL.trans hpL)
    nlinarith
  refine ⟨p, lt_of_le_of_lt (le_max_left N L) hNp, hp, ?_⟩
  apply (Int.odd_coe_nat _).mp
  rwa [Int.natCast_floor_eq_floor hx]

#print axioms rational_shift_has_odd_nat_outputs

/-- A necessary denominator condition for an eventual even-output obstruction. -/
theorem shifted_even_tail_denominator (a b : ℕ) (hb : 0 < b) (hab : a.Coprime b)
    (heven : ∃ β : ℝ, ∃ N : ℕ, ∀ p : ℕ, N < p → p.Prime →
      Even ⌊(a : ℝ) / b * p + β⌋₊) : b = 1 ∨ b = 3 := by
  by_cases hb1 : b = 1
  · exact Or.inl hb1
  by_cases hb3 : b = 3
  · exact Or.inr hb3
  obtain ⟨β, N, hN⟩ := heven
  obtain ⟨p, hNp, hp, ho⟩ := rational_shift_has_odd_nat_outputs a b (by omega) hb3 hab β N
  exact ((Nat.not_even_iff_odd.mpr ho) (hN p hNp hp)).elim

open Filter in
open scoped Topology in
/-- Rational models whose shifted outputs are eventually all even cannot
converge to an irrational slope. Their reduced denominators are restricted to
one or three, and the lattice `(1/3)ℤ` is closed. -/
theorem shifted_even_tail_models_limit_not_irrational {α : ℝ} (a b : ℕ → ℕ)
    (hb : ∀ n, 0 < b n) (hab : ∀ n, (a n).Coprime (b n))
    (heven : ∀ n, ∃ β : ℝ, ∃ N : ℕ, ∀ p : ℕ, N < p → p.Prime →
      Even ⌊(a n : ℝ) / b n * p + β⌋₊)
    (hlim : Tendsto (fun n => (a n : ℝ) / b n) atTop (𝓝 α)) :
    ¬ Irrational α := by
  have hmem : ∀ n, (3 : ℝ) * ((a n : ℝ) / b n) ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro n
    rcases shifted_even_tail_denominator (a n) (b n) (hb n) (hab n) (heven n) with h | h
    · refine ⟨((3 * a n : ℕ) : ℤ), ?_⟩
      push_cast
      rw [h]
      simp
    · refine ⟨(a n : ℤ), ?_⟩
      push_cast
      rw [h]
      ring
  obtain ⟨z, hz⟩ := Int.isClosedEmbedding_coe_real.isClosed_range.mem_of_tendsto
    (hlim.const_mul 3) (Eventually.of_forall hmem)
  intro hi
  exact (hi.intCast_mul (m := 3) (by norm_num)).ne_int z hz.symm

#print axioms shifted_even_tail_denominator
#print axioms shifted_even_tail_models_limit_not_irrational



end Explore972
