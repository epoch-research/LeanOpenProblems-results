import Submission.SignedRankSix

/-! A Pfaffian identity for the central seven-point construction.
No new configuration or universal signed-rank bound is asserted. -/

namespace Erdos213.SignedRankSix
variable {R : Type*} [CommRing R]
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def centralGram (a b c ap bp cp : R) : R :=
  8*a^2*b^2*c^2 +
  2*(ap^2-a^2-b^2)*(bp^2-a^2-c^2)*(cp^2-b^2-c^2) -
  2*a^2*(cp^2-b^2-c^2)^2 - 2*b^2*(bp^2-a^2-c^2)^2 -
  2*c^2*(ap^2-a^2-b^2)^2

def centralMatrix (a b c ap am bp bm cp cm : R) : Fin 8 → Fin 8 → R :=
  !![0, am * ap, bm * bp, -ap * bp, bm * ap, am * bp, -am * bm, 1;
     -am * ap, 0, cm * cp, ap * cp, -cm * ap, -am * cm, am * cp, 1;
     -bm * bp, -cm * cp, 0, bp * cp, bm * cm, cm * bp, bm * cp, 1;
     ap * bp, -ap * cp, -bp * cp, 0, 2 * c * ap, 2 * b * bp, 2 * a * cp, 1;
     -bm * ap, cm * ap, -bm * cm, -2 * c * ap, 0, 2 * cm * a, 2 * bm * b, 1;
     -am * bp, am * cm, -cm * bp, -2 * b * bp, -2 * cm * a, 0, 2 * am * c, 1;
     am * bm, -am * cp, -bm * cp, -2 * a * cp, -2 * bm * b, -2 * am * c, 0, 1;
     -1, -1, -1, -1, -1, -1, -1, 0]

lemma central_pf8_zero (a b c ap am bp bm cp cm : R)
    (ha : am^2+ap^2-2*a^2-2*b^2 = 0)
    (hb : bm^2+bp^2-2*a^2-2*c^2 = 0)
    (hc : cm^2+cp^2-2*b^2-2*c^2 = 0)
    (hg : centralGram a b c ap bp cp = 0) :
    pf8 (centralMatrix a b c ap am bp bm cp cm) = 0 := by
  simp only [pf8, pf6, centralMatrix, Matrix.of_apply,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  dsimp [centralGram] at hg
  linear_combination (2 * bm * cm * bp * cp - 4 * a ^ 2 * b ^ 2 - 4 * a ^ 2 * c ^ 2 + 2 * a ^ 2 * cp ^ 2 - 4 * b ^ 2 * c ^ 2 + 2 * b ^ 2 * bp ^ 2 - 4 * c ^ 4 + 4 * c ^ 2 * ap ^ 2 + 2 * c ^ 2 * bp ^ 2 + 2 * c ^ 2 * cp ^ 2 - 2 * bp ^ 2 * cp ^ 2) * ha +
    (-2 * am ^ 2 * b ^ 2 - 2 * am ^ 2 * c ^ 2 + am ^ 2 * cp ^ 2 - 2 * am * cm * ap * cp + 4 * b ^ 2 * bp ^ 2 - ap ^ 2 * cp ^ 2) * hb +
    (-am ^ 2 * bm ^ 2 + 2 * am * bm * ap * bp + 4 * a ^ 2 * cp ^ 2 - ap ^ 2 * bp ^ 2) * hc +
    2 * hg

#print axioms central_pf8_zero
end Erdos213.SignedRankSix
