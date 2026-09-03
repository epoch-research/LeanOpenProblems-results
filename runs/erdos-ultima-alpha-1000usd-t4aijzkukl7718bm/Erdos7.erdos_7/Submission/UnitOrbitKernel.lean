import Submission.UnitOrbitProbability

/-! The kernel lattice for reduction maps on unit groups. Auxiliary to the
unit-orbit descent; no universal collision bound is asserted here. -/
namespace Erdos7UnitOrbitKernel
open Erdos7UnitOrbitProbability
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {N m n : ℕ} [NeZero N]

def ker (hm : m ∣ N) : Subgroup (ZMod N)ˣ := (ZMod.unitsMap hm).ker

lemma mem_ker (hm : m ∣ N) (u : (ZMod N)ˣ) :
    u ∈ ker hm ↔ u.val.val ≡ 1 [MOD m] := by
  change ZMod.unitsMap hm u = 1 ↔ _
  rw [Units.ext_iff, ZMod.unitsMap_val]
  rw [← ZMod.natCast_val]
  simpa only [Nat.cast_one, Units.val_one] using
    (ZMod.natCast_eq_natCast_iff u.val.val 1 m)

lemma ker_anti (hm : m ∣ N) (hn : n ∣ N) (h : m ∣ n) : ker hn ≤ ker hm := by
  intro u hu
  exact (mem_ker hm u).mpr (((mem_ker hn u).mp hu).of_dvd h)

lemma ker_inf (hm : m ∣ N) (hn : n ∣ N) :
    ker hm ⊓ ker hn = ker (Nat.lcm_dvd hm hn) := by
  ext u
  simp only [Subgroup.mem_inf, mem_ker]
  exact ⟨fun h => Nat.mod_lcm h.1 h.2,
    fun h => ⟨h.of_dvd (Nat.dvd_lcm_left m n), h.of_dvd (Nat.dvd_lcm_right m n)⟩⟩

lemma totient_lattice (m n : ℕ) :
    (m.lcm n).totient * (m.gcd n).totient = m.totient * n.totient := by
  let f : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
  have hf : f.IsMultiplicative := ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩
  exact hf.lcm_apply_mul_gcd_apply

lemma ker_mass (hm : m ∣ N) : mass (ker hm) = 1 / (m.totient : ℚ) := by
  letI : NeZero m := ⟨(Nat.pos_of_dvd_of_pos hm (NeZero.pos N)).ne'⟩
  rw [ker, ← MonoidHom.comap_bot, mass_comap _ (ZMod.unitsMap_surjective hm)]
  rw [Subgroup.card_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  simp

lemma totient_pos_of_dvd (hm : m ∣ N) : 0 < m.totient :=
  Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hm (NeZero.pos N))

lemma mass_sup {G : Type*} [Group G] [Finite G] (A B : Subgroup G) [B.Normal] :
    mass (A ⊔ B) = mass A * mass B / mass (A ⊓ B) := by
  have h := mass_inf A B
  have hI := (mass_pos (A ⊓ B)).ne'
  have hS := (mass_pos (A ⊔ B)).ne'
  apply (eq_div_iff hI).mpr
  exact (mul_comm _ _).trans ((eq_div_iff hS).mp h)

lemma ker_sup_mass (hm : m ∣ N) (hn : n ∣ N) :
    mass (ker hm ⊔ ker hn) = mass (ker ((Nat.gcd_dvd_left m n).trans hm)) := by
  rw [mass_sup, ker_inf, ker_mass, ker_mass, ker_mass, ker_mass]
  have hm0 : (m.totient : ℚ) ≠ 0 := by exact_mod_cast (totient_pos_of_dvd hm).ne'
  have hn0 : (n.totient : ℚ) ≠ 0 := by exact_mod_cast (totient_pos_of_dvd hn).ne'
  have hg0 : ((m.gcd n).totient : ℚ) ≠ 0 := by
    exact_mod_cast (totient_pos_of_dvd ((Nat.gcd_dvd_left m n).trans hm)).ne'
  have hl0 : ((m.lcm n).totient : ℚ) ≠ 0 := by
    exact_mod_cast (totient_pos_of_dvd (Nat.lcm_dvd hm hn)).ne'
  have ht : ((m.lcm n).totient : ℚ) * (m.gcd n).totient =
      (m.totient : ℚ) * n.totient := by exact_mod_cast totient_lattice m n
  field_simp
  nlinarith

/-- Reductions of units form the gcd/lcm kernel lattice, not just when the
moduli are coprime. -/
theorem ker_sup (hm : m ∣ N) (hn : n ∣ N) :
    ker hm ⊔ ker hn = ker ((Nat.gcd_dvd_left m n).trans hm) := by
  apply Subgroup.eq_of_le_of_card_ge
  · exact sup_le (ker_anti _ hm (Nat.gcd_dvd_left m n))
      (ker_anti _ hn (Nat.gcd_dvd_right m n))
  · have h := ker_sup_mass hm hn
    unfold mass at h
    have hG := (card_cast_pos (ZMod N)ˣ).ne'
    have heq : (Nat.card ↥(ker hm ⊔ ker hn) : ℚ) =
        Nat.card (ker ((Nat.gcd_dvd_left m n).trans hm)) := by
      have hh := congrArg (fun x : ℚ => x * Nat.card (ZMod N)ˣ) h
      simpa only [div_mul_cancel₀ _ hG] using hh
    have : Nat.card ↥(ker hm ⊔ ker hn) =
        Nat.card (ker ((Nat.gcd_dvd_left m n).trans hm)) := by exact_mod_cast heq
    exact this.ge

/-- The elementary criterion for two subgroup cosets to intersect. -/
lemma coset_intersection_iff {G : Type*} [Group G] (A B : Subgroup G) [B.Normal]
    (z w : G) :
    (∃ v : G, z⁻¹*v ∈ A ∧ w⁻¹*v ∈ B) ↔ z⁻¹*w ∈ A ⊔ B := by
  constructor
  · rintro ⟨v, hvA, hvB⟩
    have hh := Subgroup.mul_mem_sup hvA (B.inv_mem hvB)
    convert hh using 1 <;> group
  · intro hh
    obtain ⟨x,hx,y,hy,hxy⟩ := Subgroup.mem_sup_of_normal_right.mp hh
    refine ⟨z*x, by simpa using hx, ?_⟩
    have hw : w = z*(x*y) := by rw [hxy]; group
    rw [hw]
    convert B.inv_mem hy using 1 <;> group

/-- Compatibility is tested modulo the gcd, up to the powers of the
chosen generator. It is weaker than ordinary CRT compatibility. -/
def Compatible (hm : m ∣ N) (hn : n ∣ N) (u : (ZMod N)ˣ)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) : Prop :=
  (ZMod.unitsMap (Nat.gcd_dvd_left m n) a)⁻¹ *
    ZMod.unitsMap (Nat.gcd_dvd_right m n) b ∈
      Subgroup.zpowers (ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm) u)

theorem pair_nonempty_iff (hm : m ∣ N) (hn : n ∣ N) (u : (ZMod N)ˣ)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    (∃ v, Meets (ZMod.unitsMap hm) u a v ∧ Meets (ZMod.unitsMap hn) u b v) ↔
      Compatible hm hn u a b := by
  obtain ⟨z,hz⟩ := ZMod.unitsMap_surjective hm a
  obtain ⟨w,hw⟩ := ZMod.unitsMap_surjective hn b
  have hzM : Meets (ZMod.unitsMap hm) u a z := ⟨0, by simpa using hz⟩
  have hwM : Meets (ZMod.unitsMap hn) u b w := ⟨0, by simpa using hw⟩
  simp_rw [meets_relative _ u z a hzM, meets_relative _ u w b hwM]
  rw [coset_intersection_iff, meeting_sup _ _
    (ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm)) (ker_sup hm hn).symm]
  change ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm) (z⁻¹*w) ∈
    Subgroup.zpowers (ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm) u) ↔ _
  rw [map_mul, map_inv]
  unfold Compatible
  rw [← hz, ← hw]
  simp only [← MonoidHom.comp_apply, ZMod.unitsMap_comp]

lemma units_card (hm : m ∣ N) : Nat.card (ZMod m)ˣ = m.totient := by
  letI : NeZero m := ⟨(Nat.pos_of_dvd_of_pos hm (NeZero.pos N)).ne'⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- Exact arithmetic pair probability, including the incompatible case. -/
theorem arithmetic_pair_probability (hm : m ∣ N) (hn : n ∣ N) (u : (ZMod N)ˣ)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    (Nat.card {v : (ZMod N)ˣ //
      Meets (ZMod.unitsMap hm) u a v ∧ Meets (ZMod.unitsMap hn) u b v} : ℚ) /
        N.totient =
    if Compatible hm hn u a b then
      ((orderOf (ZMod.unitsMap hm u) : ℚ) / m.totient) *
        ((orderOf (ZMod.unitsMap hn u) : ℚ) / n.totient) /
        ((orderOf (ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm) u) : ℚ) /
          (m.gcd n).totient)
    else 0 := by
  letI : NeZero m := ⟨(Nat.pos_of_dvd_of_pos hm (NeZero.pos N)).ne'⟩
  letI : NeZero n := ⟨(Nat.pos_of_dvd_of_pos hn (NeZero.pos N)).ne'⟩
  letI : NeZero (m.gcd n) := ⟨Nat.gcd_ne_zero_left (NeZero.ne m)⟩
  split_ifs with hh
  · obtain ⟨z,hzf,hzg⟩ := (pair_nonempty_iff hm hn u a b).mpr hh
    have h := pair_probability (ZMod.unitsMap hm) (ZMod.unitsMap hn)
      (ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm))
      (ZMod.unitsMap_surjective hm) (ZMod.unitsMap_surjective hn)
      (ZMod.unitsMap_surjective _) (ker_sup hm hn).symm u z a b hzf hzg
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using h
  · have he : IsEmpty {v : (ZMod N)ˣ //
        Meets (ZMod.unitsMap hm) u a v ∧ Meets (ZMod.unitsMap hn) u b v} :=
      ⟨fun v => hh ((pair_nonempty_iff hm hn u a b).mp ⟨v.val,v.property⟩)⟩
    simp [Nat.card_eq_zero.mpr (Or.inl he)]

/-- The lcm form of the same probability. For equal induced periods d, the
nonzero branch is d^2 / (d_gcd * phi(lcm(m,n))). -/
theorem arithmetic_pair_probability_lcm (hm : m ∣ N) (hn : n ∣ N) (u : (ZMod N)ˣ)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    (Nat.card {v : (ZMod N)ˣ //
      Meets (ZMod.unitsMap hm) u a v ∧ Meets (ZMod.unitsMap hn) u b v} : ℚ) /
        N.totient =
    if Compatible hm hn u a b then
      ((orderOf (ZMod.unitsMap hm u) : ℚ) * orderOf (ZMod.unitsMap hn u)) /
        ((orderOf (ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm) u) : ℚ) *
          (m.lcm n).totient)
    else 0 := by
  rw [arithmetic_pair_probability]
  split_ifs
  · have hm0 : (m.totient : ℚ) ≠ 0 := by exact_mod_cast (totient_pos_of_dvd hm).ne'
    have hn0 : (n.totient : ℚ) ≠ 0 := by exact_mod_cast (totient_pos_of_dvd hn).ne'
    have hg0 : ((m.gcd n).totient : ℚ) ≠ 0 := by
      exact_mod_cast (totient_pos_of_dvd ((Nat.gcd_dvd_left m n).trans hm)).ne'
    have hl0 : ((m.lcm n).totient : ℚ) ≠ 0 := by
      exact_mod_cast (totient_pos_of_dvd (Nat.lcm_dvd hm hn)).ne'
    have ht : ((m.lcm n).totient : ℚ) * (m.gcd n).totient =
        (m.totient : ℚ) * n.totient := by exact_mod_cast totient_lattice m n
    letI : NeZero (m.gcd n) :=
      ⟨(Nat.pos_of_dvd_of_pos ((Nat.gcd_dvd_left m n).trans hm) (NeZero.pos N)).ne'⟩
    have hd0 : (orderOf (ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm) u) : ℚ) ≠ 0 := by
      exact_mod_cast (orderOf_pos _).ne'
    field_simp
    nlinarith [congrArg (fun x : ℚ =>
      x * orderOf (ZMod.unitsMap hm u) * orderOf (ZMod.unitsMap hn u)) ht]
  · rfl

#print axioms arithmetic_pair_probability_lcm
#print axioms ker_sup
#print axioms pair_nonempty_iff
#print axioms arithmetic_pair_probability
end
end Erdos7UnitOrbitKernel
