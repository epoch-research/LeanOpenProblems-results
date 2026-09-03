import FormalConjecturesUtil
import Submission.SignedRankSix
import Submission.DeterminantExpansions

/-! Determinant/Pfaffian identities for normalized alternating matrices.
These purely algebraic identities assert no distance-set rank bound. -/
namespace Erdos213.NormalizedPfaffian
open Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 200000
variable {R : Type*} [CommRing R]

def pf6 (M : Matrix (Fin 6) (Fin 6) R) : R :=
  M 0 1*(M 2 3*M 4 5-M 2 4*M 3 5+M 2 5*M 3 4) -
  M 0 2*(M 1 3*M 4 5-M 1 4*M 3 5+M 1 5*M 3 4) +
  M 0 3*(M 1 2*M 4 5-M 1 4*M 2 5+M 1 5*M 2 4) -
  M 0 4*(M 1 2*M 3 5-M 1 3*M 2 5+M 1 5*M 2 3) +
  M 0 5*(M 1 2*M 3 4-M 1 3*M 2 4+M 1 4*M 2 3)

def alt6 (a : Fin 15 → R) : Matrix (Fin 6) (Fin 6) R :=
  !![0,a 0,a 1,a 2,a 3,a 4;
    -(a 0),0,a 5,a 6,a 7,a 8;
    -(a 1),-(a 5),0,a 9,a 10,a 11;
    -(a 2),-(a 6),-(a 9),0,a 12,a 13;
    -(a 3),-(a 7),-(a 10),-(a 12),0,a 14;
    -(a 4),-(a 8),-(a 11),-(a 13),-(a 14),0]

def normal8 (a : Fin 21 → R) : Matrix (Fin 8) (Fin 8) R :=
  !![0,a 0,a 1,a 2,a 3,a 4,a 5,1;
    -(a 0),0,a 6,a 7,a 8,a 9,a 10,1;
    -(a 1),-(a 6),0,a 11,a 12,a 13,a 14,1;
    -(a 2),-(a 7),-(a 11),0,a 15,a 16,a 17,1;
    -(a 3),-(a 8),-(a 12),-(a 15),0,a 18,a 19,1;
    -(a 4),-(a 9),-(a 13),-(a 16),-(a 18),0,a 20,1;
    -(a 5),-(a 10),-(a 14),-(a 17),-(a 19),-(a 20),0,1;
    -(1),-(1),-(1),-(1),-(1),-(1),-(1),0]

def inner (a : Fin 21 → R) : Fin 15 → R :=
  ![a 6,a 7,a 8,a 9,a 10,a 11,a 12,a 13,a 14,a 15,a 16,a 17,a 18,a 19,a 20]

def shifted (a : Fin 21 → R) : Fin 15 → R :=
  ![a 6+a 0-a 1,a 7+a 0-a 2,a 8+a 0-a 3,a 9+a 0-a 4,a 10+a 0-a 5,a 11+a 1-a 2,a 12+a 1-a 3,a 13+a 1-a 4,a 14+a 1-a 5,a 15+a 2-a 3,a 16+a 2-a 4,a 17+a 2-a 5,a 18+a 3-a 4,a 19+a 3-a 5,a 20+a 4-a 5]

theorem det_alt6 (a : Fin 15 → R) :
    (alt6 a).det=pf6 (alt6 a)^2 := by
  simp only [DeterminantExpansions.det_expand6,DeterminantExpansions.det_expand5,
    DeterminantExpansions.det_expand4,Matrix.det_fin_three,alt6,pf6,
    Matrix.of_apply,Matrix.cons_val]
  ring!

#print axioms det_alt6

end Erdos213.NormalizedPfaffian
