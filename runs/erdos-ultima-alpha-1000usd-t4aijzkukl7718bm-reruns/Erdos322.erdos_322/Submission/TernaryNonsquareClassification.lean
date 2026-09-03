import FormalConjecturesUtil

/-! A finite-field discriminant classification for ternary quadratics over
F_5. This file makes no assertion about integer representation counts. -/
namespace Erdos322Research.TernaryNonsquareClassification

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
abbrev K := ZMod 5
abbrev Coeff := Fin 6 → K
abbrev Vec := Fin 3 → K

def unit (i : Fin 4) : K := ![1,2,3,4] i

def value (a : Coeff) (x : Vec) : K :=
  a 0*x 0^2+a 1*x 1^2+a 2*x 2^2+a 3*x 0*x 1+a 4*x 0*x 2+a 5*x 1*x 2

def twiceSquare (a : Coeff) (b : Vec) : Prop :=
  a 0=2*b 0^2 ∧ a 1=2*b 1^2 ∧ a 2=2*b 2^2 ∧
  a 3=4*b 0*b 1 ∧ a 4=4*b 0*b 2 ∧ a 5=4*b 1*b 2

instance (a : Coeff) (b : Vec) : Decidable (twiceSquare a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def exceptional (a : Coeff) : Prop :=
  a 3=0 ∧ a 4=0 ∧ a 5=0 ∧
  ((a 0=0 ∧ a 1^2=1 ∧ a 2^2=1) ∨
   (a 1=0 ∧ a 0^2=1 ∧ a 2^2=1) ∨
   (a 2=0 ∧ a 0^2=1 ∧ a 1^2=1))

instance (a : Coeff) : Decidable (exceptional a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _))))

def TorusCondition (a : Coeff) : Prop :=
  ∀ u v : Fin 4, value a ![1,unit u,unit v] ≠ 1 ∧
    value a ![1,unit u,unit v] ≠ 4

instance (a : Coeff) : Decidable (TorusCondition a) :=
  inferInstanceAs (Decidable (∀ u v : Fin 4, _ ∧ _))

private theorem chunk_zero : ∀ b : Fin 5 → K,
    TorusCondition (Fin.cons 0 b) →
      (∃ c : Vec, twiceSquare (Fin.cons 0 b) c) ∨ exceptional (Fin.cons 0 b) := by
  decide +kernel

private theorem chunk_one : ∀ b : Fin 5 → K,
    TorusCondition (Fin.cons 1 b) →
      (∃ c : Vec, twiceSquare (Fin.cons 1 b) c) ∨ exceptional (Fin.cons 1 b) := by
  decide +kernel

private theorem chunk_two : ∀ b : Fin 5 → K,
    TorusCondition (Fin.cons 2 b) →
      (∃ c : Vec, twiceSquare (Fin.cons 2 b) c) ∨ exceptional (Fin.cons 2 b) := by
  decide +kernel

private theorem chunk_three : ∀ b : Fin 5 → K,
    TorusCondition (Fin.cons 3 b) →
      (∃ c : Vec, twiceSquare (Fin.cons 3 b) c) ∨ exceptional (Fin.cons 3 b) := by
  decide +kernel

private theorem chunk_four : ∀ b : Fin 5 → K,
    TorusCondition (Fin.cons 4 b) →
      (∃ c : Vec, twiceSquare (Fin.cons 4 b) c) ∨ exceptional (Fin.cons 4 b) := by
  decide +kernel

/-- Classification of ternary quadratics avoiding the two nonzero squares
on the projective torus. -/
theorem classify (a : Coeff) (h : TorusCondition a) :
    (∃ c : Vec, twiceSquare a c) ∨ exceptional a := by
  have ha := Fin.cons_self_tail a
  generalize hb : Fin.tail a = b at ha
  generalize hx : a 0 = x at ha
  subst a
  fin_cases x
  · exact chunk_zero b h
  · exact chunk_one b h
  · exact chunk_two b h
  · exact chunk_three b h
  · exact chunk_four b h

end Erdos322Research.TernaryNonsquareClassification
