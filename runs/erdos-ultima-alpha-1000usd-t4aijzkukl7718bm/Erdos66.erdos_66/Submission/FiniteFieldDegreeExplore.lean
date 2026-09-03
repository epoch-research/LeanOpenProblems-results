import Submission.GrowingSubfieldBlockExplore

/-! Realization of prescribed positive extension degrees over an arbitrary
finite field. The extension is supplied as an actual Lean field type. -/
namespace Erdos66FiniteFieldDegree
open scoped Classical
set_option maxHeartbeats 2400000

variable (F : Type*) [Field F] [Fintype F]

theorem exists_extension_degree (d : ℕ) (hd : 0<d) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra F K),
      Module.finrank F K=d ∧ Fintype.card K=(Fintype.card F)^d ∧
        ringChar K=ringChar F := by
  let p := ringChar F
  letI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let e := Module.finrank (ZMod p) F
  have he : 0<e := Module.finrank_pos
  let K := GaloisField p (e*d)
  letI : Fintype K := Fintype.ofFinite K
  have hdeg : Module.finrank (ZMod p) K=e*d := GaloisField.finrank p (Nat.ne_of_gt (Nat.mul_pos he hd))
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F:=ZMod p) (K:=F) (L:=K) (by rw [hdeg]; exact dvd_mul_right e d)
  algebraize [f.toRingHom]
  have hFK : Module.finrank F K=d := by
    have hh := Module.finrank_mul_finrank (ZMod p) F K
    rw [hdeg] at hh
    exact Nat.eq_of_mul_eq_mul_left he hh
  refine ⟨K,inferInstance,inferInstance,inferInstance,hFK,?_,?_⟩
  · rw [Module.card_eq_pow_finrank (K:=F) (V:=K),hFK]
  · exact Erdos66CharacterNorm.ringChar_eq_of_algebra (K:=F)

end Erdos66FiniteFieldDegree
