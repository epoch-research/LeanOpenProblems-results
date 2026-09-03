import FormalConjecturesUtil

/-! A limitation of comparable-modulus separation as a restriction on old
projections. A coprime coordinate with enough residues can separate every
comparable pair by the total prime-factor rank, while preserving arbitrary
old congruence classes. This constructs a partial family, NOT a covering. -/
namespace Erdos7RankResidueLift
open scoped ArithmeticFunction.Omega
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- An elementary two-modulus CRT lift with integer residues. -/
lemma exists_lift (q n : ℕ) (hcop : Nat.Coprime q n) (a c : ℤ) :
    ∃ b : ℤ, (n : ℤ) ∣ b - a ∧ (q : ℤ) ∣ b - c := by
  obtain ⟨s, t, hst⟩ := (hcop.isCoprime : IsCoprime (q : ℤ) (n : ℤ))
  refine ⟨a*s*q + c*t*n, ⟨t*(c-a), ?_⟩, ⟨s*(a-c), ?_⟩⟩
  · calc
      _ = (a*s*q + c*t*n) - a*(s*q+t*n) := by rw [hst, mul_one]
      _ = _ := by ring
  · calc
      _ = (a*s*q + c*t*n) - c*(s*q+t*n) := by rw [hst, mul_one]
      _ = _ := by ring

lemma projected_class_eq {n : ℕ} {a b : ℤ} (h : (n : ℤ) ∣ b - a) (x : ℤ) :
    (n : ℤ) ∣ x - b ↔ (n : ℤ) ∣ x - a := by
  constructor
  · intro hx
    convert dvd_add hx h using 1; ring
  · intro hx
    convert dvd_sub hx h using 1; ring

/-- Distinct bounded integer colors remain distinct modulo q. -/
lemma color_separation {q : ℕ} {a b : ℤ} {u v : ℕ}
    (hu : u < q) (hv : v < q) (huv : u ≠ v)
    (ha : (q : ℤ) ∣ a - u) (hb : (q : ℤ) ∣ b - v) :
    ¬ (q : ℤ) ∣ b - a := by
  intro hab
  have h₁ : ((u : ℕ) : ZMod q) = (a : ZMod q) := by
    simpa using (ZMod.intCast_eq_intCast_iff_dvd_sub (u : ℤ) a q).mpr ha
  have h₂ : (a : ZMod q) = (b : ZMod q) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a b q).mpr hab
  have h₃ : (b : ZMod q) = ((v : ℕ) : ZMod q) := by
    simpa using ((ZMod.intCast_eq_intCast_iff_dvd_sub (v : ℤ) b q).mpr hb).symm
  have hh := (ZMod.natCast_eq_natCast_iff' u v q).mp (h₁.trans (h₂.trans h₃))
  rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at hh
  exact huv hh

/-- Any proper coloring of the old divisibility relation can be installed
in a new coprime residue coordinate, without changing any old projection. -/
theorem colored_lift {I : Type*} (q : ℕ) (n color : I → ℕ) (a : I → ℤ)
    (hcop : ∀ i, Nat.Coprime q (n i)) (hrange : ∀ i, color i < q)
    (hcolor : ∀ i j, i ≠ j → n i ∣ n j → color i ≠ color j) :
    ∃ b : I → ℤ,
      (∀ i x, (n i : ℤ) ∣ x - b i ↔ (n i : ℤ) ∣ x - a i) ∧
      (∀ i, (q : ℤ) ∣ b i - color i) ∧
      (∀ i j, i ≠ j → n i ∣ n j →
        ¬ ((q * n i : ℕ) : ℤ) ∣ b j - b i) := by
  classical
  choose b hn hq using fun i => exists_lift q (n i) (hcop i) (a i) (color i)
  refine ⟨b, fun i x => projected_class_eq (hn i) x, hq, ?_⟩
  intro i j hij hd hbad
  have hqd : (q : ℤ) ∣ ((q * n i : ℕ) : ℤ) := by
    exact_mod_cast (dvd_mul_right q (n i))
  exact color_separation (hrange i) (hrange j) (hcolor i j hij hd)
    (hq i) (hq j) (hqd.trans hbad)

lemma rank_lt_of_proper_dvd {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hd : m ∣ n) (hne : m ≠ n) : Ω m < Ω n := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 0 := by intro hk; simp [hk] at hn
  have hk1 : k ≠ 1 := by intro hk; simp [hk] at hne
  have hkp : 1 < k := by omega
  rw [ArithmeticFunction.cardFactors_mul hm.ne' hk]
  have hp := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hkp
  omega

/-- If q exceeds every old total exponent rank, comparable pairs can always
be separated in the new coordinate, regardless of their old residues. -/
theorem rank_lift {I : Type*} (q : ℕ) (n : I → ℕ) (a : I → ℤ)
    (hn : ∀ i, 0 < n i) (hinj : Function.Injective n)
    (hcop : ∀ i, Nat.Coprime q (n i)) (hrank : ∀ i, Ω (n i) < q) :
    ∃ b : I → ℤ,
      (∀ i x, (n i : ℤ) ∣ x - b i ↔ (n i : ℤ) ∣ x - a i) ∧
      (∀ i, (q : ℤ) ∣ b i - (Ω (n i) : ℕ)) ∧
      (∀ i j, i ≠ j → n i ∣ n j →
        ¬ ((q * n i : ℕ) : ℤ) ∣ b j - b i) := by
  apply colored_lift q n (fun i => Ω (n i)) a hcop hrank
  intro i j hij hd
  exact (rank_lt_of_proper_dvd (hn i) (hn j) hd (fun h => hij (hinj h))).ne

/-- The residue separation required of an irredundant cover implies actual
pairwise disjointness for comparable moduli, as expected. -/
lemma comparable_classes_disjoint {q : ℕ} {m n : ℕ} {a b : ℤ}
    (hd : m ∣ n) (hs : ¬ ((q*m : ℕ) : ℤ) ∣ b-a) (x : ℤ) :
    ¬ (((q*m : ℕ) : ℤ) ∣ x-a ∧ ((q*n : ℕ) : ℤ) ∣ x-b) := by
  rintro ⟨ha, hb⟩
  have hmn : ((q*m : ℕ) : ℤ) ∣ ((q*n : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_dvd_mul_left q hd
  have h := dvd_sub ha (hmn.trans hb)
  apply hs
  convert h using 1; ring

/-- In the 4-by-4 exponent rectangle, q=7 has enough colors. This finite
check concerns only ranks, distinct moduli, and coprimality, not coverage. -/
lemma rectangle_data :
    (∀ i : Fin 4 × Fin 4, 0 < 3^i.1.val * 5^i.2.val) ∧
    Function.Injective (fun i : Fin 4 × Fin 4 => 3^i.1.val * 5^i.2.val) ∧
    (∀ i : Fin 4 × Fin 4, Nat.Coprime 7 (3^i.1.val * 5^i.2.val)) ∧
    (∀ i : Fin 4 × Fin 4, Ω (3^i.1.val * 5^i.2.val) < 7) := by
  decide +kernel

/-- All sixteen old projections may be prescribed arbitrarily, then lifted
to the distinct moduli 7*3^u*5^v while separating every comparable pair. -/
theorem four_by_four_lift (a : Fin 4 × Fin 4 → ℤ) :
    ∃ b : Fin 4 × Fin 4 → ℤ,
      (∀ i x, ((3^i.1.val * 5^i.2.val : ℕ) : ℤ) ∣ x - b i ↔
        ((3^i.1.val * 5^i.2.val : ℕ) : ℤ) ∣ x - a i) ∧
      (∀ i, (7 : ℤ) ∣ b i - (Ω (3^i.1.val * 5^i.2.val) : ℕ)) ∧
      (∀ i j, i ≠ j → 3^i.1.val * 5^i.2.val ∣ 3^j.1.val * 5^j.2.val →
        ¬ ((7 * (3^i.1.val * 5^i.2.val) : ℕ) : ℤ) ∣ b j - b i) :=
  rank_lift 7 _ a rectangle_data.1 rectangle_data.2.1
    rectangle_data.2.2.1 rectangle_data.2.2.2

#print axioms rank_lift
#print axioms four_by_four_lift
end Erdos7RankResidueLift
