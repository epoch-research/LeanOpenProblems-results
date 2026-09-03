import Submission.QuarticPrimePolynomial

/-! The finite-field obstruction to a coordinatewise quartic descent.
This is a local theorem, not a bound on the unrestricted representation count. -/

noncomputable section
namespace Erdos322Research.QuarticPrimeClassification

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

private def fourthPowers : Finset K := Finset.univ.image (fun x : K ↦ x^4)
private abbrev fourthUnits (K : Type*) [Field K] := (powMonoidHom 4 : Kˣ →* Kˣ).range

private theorem mem_fourthPowers (x : K) : x ∈ fourthPowers ↔ ∃ y : K, y^4 = x := by
  simp [fourthPowers]

private theorem fourthPowers_card : (fourthPowers (K := K)).card =
    (Fintype.card K - 1) / (Fintype.card K - 1).gcd 4 + 1 := by
  let H := fourthUnits K
  let f : H → K := fun x ↦ ((x : Kˣ) : K)
  have hf : Function.Injective f := fun a b h ↦ Subtype.ext (Units.ext h)
  have h0 : (0 : K) ∉ Finset.univ.image f := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro x
    exact (x : Kˣ).ne_zero
  have he : fourthPowers = insert 0 (Finset.univ.image f) := by
    ext x
    rw [mem_fourthPowers]
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, rfl⟩
      by_cases hy : y = 0
      · simp [hy]
      · right
        let v : Kˣ := Units.mk0 y hy
        refine ⟨⟨v^4, ⟨v, rfl⟩⟩, ?_⟩
        rfl
    · rintro (rfl | ⟨y, rfl⟩)
      · exact ⟨0, by norm_num⟩
      · obtain ⟨v, hv⟩ := y.property
        refine ⟨(v : K), ?_⟩
        exact congrArg Units.val hv
  rw [he, Finset.card_insert_of_notMem h0, Finset.card_image_of_injective _ hf,
    Finset.card_univ, ← Nat.card_eq_fintype_card]
  change Nat.card (fourthUnits K) + 1 = _
  rw [IsCyclic.card_powMonoidHom_range, Nat.card_units, Nat.card_eq_fintype_card]

private def Anisotropic (K : Type*) [Field K] : Prop :=
  ∀ a b c d : K, a^4+b^4+c^4+d^4 = 0 → a = 0

private theorem no_one_sum (han : Anisotropic K) {x y : K}
    (hx : x ∈ fourthPowers) (hy : y ∈ fourthPowers) : 1+x+y ≠ 0 := by
  obtain ⟨a, rfl⟩ := (mem_fourthPowers x).mp hx
  obtain ⟨b, rfl⟩ := (mem_fourthPowers y).mp hy
  intro he
  have := han 1 a b 0 (by simpa using he)
  exact one_ne_zero this

private theorem twice_card_le (han : Anisotropic K) :
    2*(fourthPowers (K := K)).card ≤ Fintype.card K := by
  let B := (fourthPowers (K := K)).image (fun x ↦ -1-x)
  have hb : B.card = (fourthPowers (K := K)).card := by
    apply Finset.card_image_of_injective
    intro x y h
    linear_combination -h
  have hd : Disjoint (fourthPowers (K := K)) B := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨y, hyA, rfl⟩ := Finset.mem_image.mp hy
    apply no_one_sum han hx hyA
    ring
  have hcard := Finset.card_le_univ (fourthPowers (K := K) ∪ B)
  rw [Finset.card_union_of_disjoint hd, hb] at hcard
  omega

private theorem gcd_four (han : Anisotropic K) : (Fintype.card K - 1).gcd 4 = 4 := by
  have hd := Nat.gcd_dvd_right (Fintype.card K - 1) 4
  have hpos := Nat.pos_of_dvd_of_pos hd (by decide : 0 < 4)
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hc := twice_card_le han
  rw [fourthPowers_card] at hc
  have hK := Fintype.one_lt_card (α := K)
  have hm := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left (Fintype.card K - 1) 4)
  interval_cases h : (Fintype.card K - 1).gcd 4 <;> simp_all <;> omega

private theorem card_eq_four_mul (han : Anisotropic K) :
    Fintype.card K = 4*Fintype.card (fourthUnits K)+1 := by
  have hd := gcd_four han
  have hdiv : 4 ∣ Fintype.card K - 1 := hd ▸ Nat.gcd_dvd_left (Fintype.card K - 1) 4
  have hh : Fintype.card (fourthUnits K) = (Fintype.card K - 1)/4 := by
    rw [← Nat.card_eq_fintype_card, IsCyclic.card_powMonoidHom_range,
      Nat.card_units, Nat.card_eq_fintype_card, hd]
  rw [hh, Nat.mul_div_cancel' hdiv]
  have hK := Fintype.one_lt_card (α := K)
  omega

private theorem fourthUnits_card_odd (han : Anisotropic K) :
    Odd (Fintype.card (fourthUnits K)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hdiv : 2 ∣ Fintype.card (fourthUnits K) := even_iff_two_dvd.mp heven
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card 2 hdiv
  have he : (((a : Kˣ) : K))^2 = 1 := by
    have hp := pow_orderOf_eq_one a
    rw [ha] at hp
    exact congrArg (fun x : fourthUnits K ↦ ((x : Kˣ) : K)) hp
  rcases sq_eq_one_iff.mp he with h1 | hn
  · have ha1 : a = 1 := Subtype.ext (Units.ext h1)
    simp [ha1] at ha
  · obtain ⟨v, hv⟩ := a.property
    have hv' : (v : K)^4 = -1 := (congrArg Units.val hv).trans hn
    have hf := han 1 (v : K) 0 0 (by simp [hv'])
    exact one_ne_zero hf

omit [Fintype K] [DecidableEq K] in
private theorem two_ne_zero (han : Anisotropic K) : (2 : K) ≠ 0 := by
  intro he
  exact one_ne_zero (han 1 1 0 0 (by simpa only [one_pow, zero_pow (by decide : 4 ≠ 0), add_zero, one_add_one_eq_two] using he))

private theorem fourthPowers_roots {x : K} (hx : x ∈ fourthPowers) :
    x = 0 ∨ x ^ Fintype.card (fourthUnits K) = 1 := by
  obtain ⟨y, rfl⟩ := (mem_fourthPowers x).mp hx
  by_cases hy : y = 0
  · simp [hy]
  · right
    let v : Kˣ := Units.mk0 y hy
    let a : fourthUnits K := ⟨v^4, ⟨v, rfl⟩⟩
    have he := pow_card_eq_one (x := a)
    exact congrArg (fun x : fourthUnits K ↦ ((x : Kˣ) : K)) he

private theorem minus_four_mem (han : Anisotropic K) : (-4 : K) ∈ fourthPowers := by
  have hmod : Fintype.card K % 4 ≠ 3 := by rw [card_eq_four_mul han]; omega
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.mpr hmod
  apply (mem_fourthPowers _).mpr
  refine ⟨1+i, ?_⟩
  linear_combination (norm := ring) -(i^2+4*i+5)*hi

private theorem two_not_mem (han : Anisotropic K) : (2 : K) ∉ fourthPowers := by
  intro h2
  obtain ⟨u, hu⟩ := (mem_fourthPowers _).mp h2
  obtain ⟨v, hv⟩ := (mem_fourthPowers _).mp (minus_four_mem han)
  have h2nz := two_ne_zero han
  letI : NeZero (2 : K) := ⟨h2nz⟩
  have he : (v/u^2)^4 = -1 := by
    rw [div_pow, ← pow_mul, show 2*4 = 4*2 by decide, pow_mul, hu, hv]
    field_simp
    ring
  exact one_ne_zero (han 1 (v/u^2) 0 0 (by simp [he]))

private theorem zero_of_four_sum (han : Anisotropic K) {a b c d : K}
    (ha : a ∈ fourthPowers) (hb : b ∈ fourthPowers)
    (hc : c ∈ fourthPowers) (hd : d ∈ fourthPowers)
    (he : a+b+c+d = 0) : a = 0 := by
  obtain ⟨w, rfl⟩ := (mem_fourthPowers _).mp ha
  obtain ⟨x, rfl⟩ := (mem_fourthPowers _).mp hb
  obtain ⟨y, rfl⟩ := (mem_fourthPowers _).mp hc
  obtain ⟨z, rfl⟩ := (mem_fourthPowers _).mp hd
  rw [han w x y z he]
  norm_num

open scoped Pointwise

private theorem sumset_card_le (han : Anisotropic K) :
    (fourthPowers + fourthPowers : Finset K).card ≤
      2*Fintype.card (fourthUnits K)+1 := by
  let S : Finset K := fourthPowers + fourthPowers
  have hi : S ∩ -S ⊆ {0} := by
    intro x hx
    obtain ⟨hx, hx'⟩ := Finset.mem_inter.mp hx
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_neg.mp hx'
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp hy
    have he : a+b+c+d = 0 := by linear_combination hab + hcd - hyx
    have hza := zero_of_four_sum han ha hb hc hd he
    have hzb := zero_of_four_sum han hb ha hc hd (by linear_combination he)
    rw [Finset.mem_singleton]
    linear_combination -hab + hza + hzb
  have hci := Finset.card_le_card hi
  rw [Finset.card_singleton] at hci
  have hcu := Finset.card_le_univ (S ∪ -S)
  have he := Finset.card_union_add_card_inter S (-S)
  rw [Finset.card_neg] at he
  rw [card_eq_four_mul han] at hcu
  dsimp [S] at *
  omega

private theorem fourthPowers_card_eq (han : Anisotropic K) :
    (fourthPowers (K := K)).card = Fintype.card (fourthUnits K)+1 := by
  rw [fourthPowers_card, gcd_four han, card_eq_four_mul han]
  omega

private theorem sumset_eq_union (han : Anisotropic K) :
    (fourthPowers + fourthPowers : Finset K) =
      fourthPowers ∪ fourthPowers.image (fun x : K ↦ 2*x) := by
  let A : Finset K := fourthPowers
  let T := A.image (fun x : K ↦ 2*x)
  have h0 : (0 : K) ∈ A := (mem_fourthPowers _).mpr ⟨0, by norm_num⟩
  have hs : A ∪ T ⊆ A+A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_add.mpr ⟨x, hx, 0, h0, add_zero _⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_add.mpr ⟨y, hy, y, hy, by ring⟩
  have hT : T.card = A.card := by
    exact Finset.card_image_of_injective _ (mul_right_injective₀ (two_ne_zero han))
  have hi : A ∩ T ⊆ {0} := by
    intro x hx
    obtain ⟨hxA, hxT⟩ := Finset.mem_inter.mp hx
    obtain ⟨a, ha⟩ := (mem_fourthPowers x).mp hxA
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxT
    obtain ⟨b, hb⟩ := (mem_fourthPowers y).mp hy
    by_cases hb0 : b = 0
    · simp [hb0] at hb
      simp [← hyx, ← hb]
    · exfalso
      apply two_not_mem han
      apply (mem_fourthPowers _).mpr
      refine ⟨a/b, ?_⟩
      rw [div_pow, div_eq_iff (pow_ne_zero _ hb0)]
      linear_combination ha - hyx - 2*hb
  have hci := Finset.card_le_card hi
  rw [Finset.card_singleton] at hci
  have hcu := Finset.card_union_add_card_inter A T
  rw [hT, show A.card = Fintype.card (fourthUnits K)+1 from fourthPowers_card_eq han] at hcu
  have hS := sumset_card_le han
  have he : A ∪ T = A+A := Finset.eq_of_subset_of_card_le hs (by dsimp [A] at *; omega)
  exact he.symm

/-- Over a finite field, coordinatewise anisotropy for four fourth powers forces
exactly five elements. -/
theorem card_eq_five_of_anisotropic
    (han : ∀ a b c d : K, a^4+b^4+c^4+d^4 = 0 → a = 0) :
    Fintype.card K = 5 := by
  by_contra hK5
  let h := Fintype.card (fourthUnits K)
  have hcard : Fintype.card K = 4*h+1 := card_eq_four_mul han
  have hodd : Odd h := fourthUnits_card_odd han
  have hh : 3 ≤ h := by
    obtain ⟨t, ht⟩ := hodd
    omega
  have h2nz := two_ne_zero han
  letI : NeZero (2 : K) := ⟨h2nz⟩
  have h3nz : (3 : K) ≠ 0 := by
    intro he
    apply one_ne_zero (han 1 1 1 0 ?_)
    linear_combination (norm := ring) he
  have hchar : 4*(h : K)+1 = 0 := by
    have he := Nat.cast_card_eq_zero K
    rw [hcard] at he
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using he
  have hplus : (h : K)+1 ≠ 0 := by
    intro he
    apply h3nz
    linear_combination (norm := ring) 4*he - hchar
  have h4nz : (-4 : K) ≠ 0 := by
    have he : (-4 : K) = -(2*2) := by ring
    rw [he]
    exact neg_ne_zero.mpr (mul_ne_zero h2nz h2nz)
  have hpow : (-4 : K)^h = 1 :=
    (fourthPowers_roots (minus_four_mem han)).resolve_left h4nz
  rw [hodd.neg_pow] at hpow
  have hu : ((2 : K)^h)^2 = -1 := by
    calc
      ((2 : K)^h)^2 = ((2 : K)^2)^h := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = (4 : K)^h := by congr 1; ring
      _ = -1 := by linear_combination (norm := ring) -hpow
  have hshift (x : K) (hx : x ∈ fourthPowers) :
      x+1 = 0 ∨ (x+1)^h = 1 ∨ (x+1)^h = (2 : K)^h := by
    have h1 : (1 : K) ∈ fourthPowers := (mem_fourthPowers _).mpr ⟨1, by simp⟩
    have hs : x+1 ∈ (fourthPowers + fourthPowers : Finset K) :=
      Finset.mem_add.mpr ⟨x, hx, 1, h1, rfl⟩
    rw [sumset_eq_union han] at hs
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases fourthPowers_roots hs with he | he
      · exact Or.inl he
      · exact Or.inr (Or.inl he)
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hs
      rcases fourthPowers_roots hy with he | he
      · left
        simpa [he] using hyx.symm
      · right; right
        rw [← hyx, mul_pow, he, mul_one]
  have h26 : (26 : K) = 0 := QuarticPrimePolynomial.characteristic_obstruction_of_roots
    h hh ((2 : K)^h) hchar hplus hu fourthPowers (fourthPowers_card_eq han)
    (fun _ hx ↦ fourthPowers_roots hx) hshift
  have h13 : (13 : K) = 0 := by
    have he : (2 : K)*13 = 0 := by linear_combination (norm := ring) h26
    exact (mul_eq_zero.mp he).resolve_left h2nz
  exact one_ne_zero (han 1 2 4 0 (by linear_combination (norm := ring) 21*h13))

/-- Every finite field other than the five-element field has a nontrivial zero
of the sum of four fourth powers. The first coordinate may be chosen nonzero. -/
theorem exists_nontrivial_fourth_sum (hcard : Fintype.card K ≠ 5) :
    ∃ a b c d : K, a ≠ 0 ∧ a^4+b^4+c^4+d^4 = 0 := by
  by_contra hn
  apply hcard
  apply card_eq_five_of_anisotropic
  intro a b c d he
  by_contra ha
  exact hn ⟨a, b, c, d, ha, he⟩

private theorem five_anisotropic :
    ∀ a b c d : ZMod 5, a^4+b^4+c^4+d^4 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  decide

/-- Exactly the prime 5 supports the coordinatewise divisibility descent for
four fourth powers at the prime-modulus level. -/
theorem prime_anisotropic_iff (p : ℕ) [Fact p.Prime] :
    (∀ a b c d : ZMod p, a^4+b^4+c^4+d^4 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ↔ p = 5 := by
  constructor
  · intro han
    have he := card_eq_five_of_anisotropic (K := ZMod p)
      (fun a b c d h ↦ (han a b c d h).1)
    simpa only [ZMod.card] using he
  · rintro rfl
    exact five_anisotropic

/-- Natural-number form of the prime-modulus classification. This concerns only
coordinatewise divisibility, not arbitrary descent procedures. -/
theorem prime_coordinatewise_descent_iff (p : ℕ) [Fact p.Prime] :
    (∀ a b c d : ℕ, p ∣ a^4+b^4+c^4+d^4 →
      p ∣ a ∧ p ∣ b ∧ p ∣ c ∧ p ∣ d) ↔ p = 5 := by
  rw [← prime_anisotropic_iff p]
  constructor
  · intro hn a b c d he
    have hd : p ∣ a.val^4+b.val^4+c.val^4+d.val^4 := by
      rw [← ZMod.natCast_eq_zero_iff]
      simpa only [Nat.cast_add, Nat.cast_pow, ZMod.natCast_zmod_val] using he
    obtain ⟨ha, hb, hc, hd⟩ := hn a.val b.val c.val d.val hd
    simpa only [← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val] using
      And.intro ha (And.intro hb (And.intro hc hd))
  · intro hz a b c d hd
    rw [← ZMod.natCast_eq_zero_iff] at hd
    push_cast at hd
    simpa only [ZMod.natCast_eq_zero_iff] using hz a b c d hd

end Erdos322Research.QuarticPrimeClassification
