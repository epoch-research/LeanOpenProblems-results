import Submission.UnitOrbitKernel

/-! Exact probabilities after deleting pairs that meet the same orbit point.
These identities do not provide a universal upper collision budget. -/
namespace Erdos7UnitOrbitPhaseProbability
open Erdos7UnitOrbitProbability Erdos7UnitOrbitKernel
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {N m n : ℕ} [NeZero N]

/-- Ordinary CRT compatibility, without allowing an orbit phase shift. -/
def CRTCompatible (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) : Prop :=
  ZMod.unitsMap (Nat.gcd_dvd_left m n) a = ZMod.unitsMap (Nat.gcd_dvd_right m n) b

def CoMeets (hm : m ∣ N) (hn : n ∣ N) (u : (ZMod N)ˣ)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) (v : (ZMod N)ˣ) : Prop :=
  ∃ t : ℤ, ZMod.unitsMap hm (v*u^t) = a ∧ ZMod.unitsMap hn (v*u^t) = b

lemma crt_compatible_iff (hm : m ∣ N) (hn : n ∣ N)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    (∃ z : (ZMod N)ˣ, ZMod.unitsMap hm z = a ∧ ZMod.unitsMap hn z = b) ↔
      CRTCompatible a b := by
  simpa [Meets, Compatible, Subgroup.mem_zpowers_iff, CRTCompatible, inv_mul_eq_one]
    using (pair_nonempty_iff hm hn 1 a b)

lemma fiber_lcm (hm : m ∣ N) (hn : n ∣ N) (z x : (ZMod N)ˣ) :
    ZMod.unitsMap (Nat.lcm_dvd hm hn) z = ZMod.unitsMap (Nat.lcm_dvd hm hn) x ↔
      ZMod.unitsMap hm z = ZMod.unitsMap hm x ∧ ZMod.unitsMap hn z = ZMod.unitsMap hn x := by
  have hh : z⁻¹*x ∈ ker (Nat.lcm_dvd hm hn) ↔ z⁻¹*x ∈ ker hm ⊓ ker hn := by
    rw [ker_inf]
  simpa only [Subgroup.mem_inf, ker, MonoidHom.mem_ker, map_mul, map_inv,
    inv_mul_eq_one] using hh

lemma order_lcm (hm : m ∣ N) (hn : n ∣ N) (u : (ZMod N)ˣ) :
    orderOf (ZMod.unitsMap (Nat.lcm_dvd hm hn) u) =
      Nat.lcm (orderOf (ZMod.unitsMap hm u)) (orderOf (ZMod.unitsMap hn u)) := by
  letI : NeZero (m.lcm n) :=
    ⟨(Nat.pos_of_dvd_of_pos (Nat.lcm_dvd hm hn) (NeZero.pos N)).ne'⟩
  let f := (ZMod.unitsMap (Nat.dvd_lcm_left m n)).prod (ZMod.unitsMap (Nat.dvd_lcm_right m n))
  have hf : Function.Injective f := by
    intro x y h
    have he := (fiber_lcm (Nat.dvd_lcm_left m n) (Nat.dvd_lcm_right m n) x y).mpr
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    simpa only [ZMod.unitsMap_self, MonoidHom.id_apply] using he
  rw [← orderOf_injective f hf]
  dsimp only [f]
  rw [MonoidHom.prod_apply, Prod.orderOf_mk]
  simp only [← MonoidHom.comp_apply, ZMod.unitsMap_comp]

lemma coMeets_iff_lcm (hm : m ∣ N) (hn : n ∣ N) (u z : (ZMod N)ˣ)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ)
    (hz : ZMod.unitsMap hm z = a ∧ ZMod.unitsMap hn z = b) (v : (ZMod N)ˣ) :
    CoMeets hm hn u a b v ↔
      Meets (ZMod.unitsMap (Nat.lcm_dvd hm hn)) u
        (ZMod.unitsMap (Nat.lcm_dvd hm hn) z) v := by
  simp only [CoMeets, Meets, ← hz.1, ← hz.2]
  exact exists_congr (fun t => (fiber_lcm hm hn (v*u^t) z).symm)

lemma coMeets_implies_compatible (hm : m ∣ N) (hn : n ∣ N) (u : (ZMod N)ˣ)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) (v : (ZMod N)ˣ)
    (h : CoMeets hm hn u a b v) : CRTCompatible a b := by
  obtain ⟨t,ht⟩ := h
  exact (crt_compatible_iff hm hn a b).mp ⟨v*u^t,ht⟩

/-- Shared-phase probability is the usual lcm-fiber meeting probability. -/
theorem common_phase_probability (hm : m ∣ N) (hn : n ∣ N) (u : (ZMod N)ˣ)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    (Nat.card {v : (ZMod N)ˣ // CoMeets hm hn u a b v} : ℚ) / N.totient =
      if CRTCompatible a b then
        (orderOf (ZMod.unitsMap (Nat.lcm_dvd hm hn) u) : ℚ) / (m.lcm n).totient
      else 0 := by
  split_ifs with hh
  · obtain ⟨z,hz⟩ := (crt_compatible_iff hm hn a b).mpr hh
    rw [Nat.card_congr (Equiv.subtypeEquivRight (coMeets_iff_lcm hm hn u z a b hz))]
    letI : NeZero (m.lcm n) :=
      ⟨(Nat.pos_of_dvd_of_pos (Nat.lcm_dvd hm hn) (NeZero.pos N)).ne'⟩
    have hp := single_probability (ZMod.unitsMap (Nat.lcm_dvd hm hn))
      (ZMod.unitsMap_surjective _) u (ZMod.unitsMap (Nat.lcm_dvd hm hn) z)
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using hp
  · have he : IsEmpty {v : (ZMod N)ˣ // CoMeets hm hn u a b v} :=
      ⟨fun v => hh (coMeets_implies_compatible hm hn u a b v.val v.property)⟩
    simp

lemma card_difference {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop) (hQP : ∀ v, Q v → P v) :
    Nat.card {v // P v ∧ ¬ Q v} + Nat.card {v // Q v} = Nat.card {v // P v} := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hh := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Ω).filter P) Q
  have he : ((Finset.univ : Finset Ω).filter P).filter Q = Finset.univ.filter Q := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hQP v h,h⟩⟩
  rw [he, Finset.filter_filter] at hh
  convert (add_comm _ _).trans hh using 1

/-- Exact probability of meeting both classes but never at the same parameter.
For equal induced periods these are precisely the harmful phase collisions. -/
theorem distinct_phase_probability (hm : m ∣ N) (hn : n ∣ N) (u : (ZMod N)ˣ)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    (Nat.card {v : (ZMod N)ˣ //
      (Meets (ZMod.unitsMap hm) u a v ∧ Meets (ZMod.unitsMap hn) u b v) ∧
        ¬ CoMeets hm hn u a b v} : ℚ) / N.totient =
      (if Compatible hm hn u a b then
        ((orderOf (ZMod.unitsMap hm u) : ℚ) * orderOf (ZMod.unitsMap hn u)) /
          ((orderOf (ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm) u) : ℚ) *
            (m.lcm n).totient)
      else 0) -
      (if CRTCompatible a b then
        (orderOf (ZMod.unitsMap (Nat.lcm_dvd hm hn) u) : ℚ) / (m.lcm n).totient
      else 0) := by
  rw [← arithmetic_pair_probability_lcm hm hn u a b,
    ← common_phase_probability hm hn u a b]
  have hh := card_difference
    (fun v => Meets (ZMod.unitsMap hm) u a v ∧ Meets (ZMod.unitsMap hn) u b v)
    (CoMeets hm hn u a b) (fun v ⟨t,ht⟩ => ⟨⟨t,ht.1⟩,⟨t,ht.2⟩⟩)
  have he : (Nat.card {v : (ZMod N)ˣ //
      (Meets (ZMod.unitsMap hm) u a v ∧ Meets (ZMod.unitsMap hn) u b v) ∧
        ¬ CoMeets hm hn u a b v} : ℚ) +
      Nat.card {v : (ZMod N)ˣ // CoMeets hm hn u a b v} =
      Nat.card {v : (ZMod N)ˣ //
        Meets (ZMod.unitsMap hm) u a v ∧ Meets (ZMod.unitsMap hn) u b v} := by
    exact_mod_cast hh
  rw [← he, add_div]
  ring

#print axioms crt_compatible_iff
#print axioms order_lcm
#print axioms common_phase_probability
#print axioms distinct_phase_probability
end
end Erdos7UnitOrbitPhaseProbability
