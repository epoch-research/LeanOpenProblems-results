import FormalConjecturesUtil

/-! Elementary arithmetic certificates for a restricted central-reflection
construction. These lemmas do not assert a cardinality bound for integral sets. -/
namespace Erdos213.ReflectionCubic
noncomputable section
set_option maxHeartbeats 3000000

lemma rational_no_root (p : ℕ) (hp : p.Prime) (a b c d : ℤ)
    (hmod : ∀ x y : ZMod p,
      (a : ZMod p)*x^3+b*x^2*y+c*x*y^2+d*y^3=0 → x=0 ∧ y=0)
    (q : ℚ) : (a : ℚ)*q^3+b*q^2+c*q+d≠0 := by
  intro h
  have hd : (q.den : ℚ)≠0 := by exact_mod_cast q.den_ne_zero
  have hz : a*q.num^3+b*q.num^2*(q.den : ℤ)+c*q.num*(q.den : ℤ)^2+
      d*(q.den : ℤ)^3=0 := by
    have hh := h
    rw [← Rat.num_div_den q] at hh
    field_simp at hh
    have hh' : (a : ℚ)*(q.num : ℚ)^3+b*(q.num : ℚ)^2*q.den+
        c*q.num*(q.den : ℚ)^2+d*(q.den : ℚ)^3=0 := by
      linear_combination hh
    exact_mod_cast hh' 
  have he := congrArg (Int.castRingHom (ZMod p)) hz
  simp only [map_add,map_mul,map_pow,map_zero,Int.coe_castRingHom,Int.cast_natCast] at he
  obtain ⟨hn,hD⟩ := hmod (q.num : ZMod p) (q.den : ZMod p) he
  have hn' : (p : ℤ)∣q.num := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn
  have hD' : p∣q.den := (ZMod.natCast_eq_zero_iff _ _).mp (by exact_mod_cast hD)
  have hn'' : p∣q.num.natAbs := Int.natCast_dvd.mp hn'
  have hg : p∣Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hn'' hD'
  rw [q.reduced] at hg
  exact hp.not_dvd_one hg

lemma no_quadratic_root (a b c u v : ℚ) (z : ℂ)
    (hroot : ∀ q : ℚ, q^3+a*q^2+b*q+c≠0)
    (hq : z^2-(u : ℂ)*z+(v : ℂ)=0) :
    z^3+(a : ℂ)*z^2+(b : ℂ)*z+(c : ℂ)≠0 := by
  intro hp
  let A : ℚ := u^2-v+a*u+b
  let B : ℚ := c-(u+a)*v
  have hab : (A : ℂ)*z+(B : ℂ)=0 := by
    dsimp [A,B]
    push_cast
    linear_combination hp-(z+(u : ℂ)+(a : ℂ))*hq
  by_cases ha : A=0
  · have hb : B=0 := by
      have he : (B : ℂ)=0 := by simpa [ha] using hab
      exact_mod_cast he
    apply hroot (-u-a)
    have he : (-u-a)^3+a*(-u-a)^2+b*(-u-a)+c=A*(-u-a)+B := by dsimp [A,B]; ring
    rw [he,ha,hb]
    ring
  · have ha' : (A : ℂ)≠0 := by exact_mod_cast ha
    have hz : z=((-B/A : ℚ) : ℂ) := by
      push_cast
      apply (eq_div_iff ha').mpr
      linear_combination hab
    rw [hz] at hp
    apply hroot (-B/A)
    exact_mod_cast hp

#print axioms rational_no_root
#print axioms no_quadratic_root
end
end Erdos213.ReflectionCubic
