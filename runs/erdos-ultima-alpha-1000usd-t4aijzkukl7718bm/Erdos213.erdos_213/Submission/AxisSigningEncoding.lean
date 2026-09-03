import Submission.AxisBasePolynomial

/-! A kernel-compatible encoding of arbitrary Boolean edge signings. -/
namespace Erdos213.AxisBaseCompleteness
open AxisRankObstruction
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Encode a finite Boolean signing without any compiler-evaluation axiom. -/
def encode : {n : ℕ} → (Fin n → Bool) → BitVec n
  | 0, _ => .nil
  | .succ _, s => .concat (encode (fun i => s i.succ)) (s 0)

lemma encode_get : ∀ {n : ℕ} (s : Fin n → Bool) (i : Fin n),
    (encode s).getLsbD i.val=s i := by
  intro n
  induction n with
  | zero => intro s i; exact Fin.elim0 i
  | succ n ih =>
    intro s i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [encode]
    · simp only [encode,Fin.val_succ,BitVec.getLsbD_concat_succ]
      exact ih _ j

lemma encode_testBit {n : ℕ} (s : Fin n → Bool) (k : ℕ) (hk : k<n) :
    (encode s).toNat.testBit k=s ⟨k,hk⟩ := by
  rw [BitVec.testBit_toNat]
  exact encode_get s ⟨k,hk⟩

def lowBits (s : Fin 21 → Bool) : BitVec 6 :=
  encode (fun i => s ⟨i.val,by omega⟩)

def highBits (s : Fin 21 → Bool) : BitVec 15 :=
  encode (fun i => s ⟨i.val+6,by omega⟩)

def template (s : Fin 21 → Bool) : Fin 8 → Fin 8 → ℤ :=
  !![0,952*sign (s 0),1800*sign (s 1),3536*sign (s 2),960*sign (s 3),1785*sign (s 4),6630*sign (s 5),1;
    -(952*sign (s 0)),0,848*sign (s 6),2584*sign (s 7),1352*sign (s 8),2023*sign (s 9),6698*sign (s 10),1;
    -(1800*sign (s 1)),-(848*sign (s 6)),0,1736*sign (s 11),2040*sign (s 12),2535*sign (s 13),6870*sign (s 14),1;
    -(3536*sign (s 2)),-(2584*sign (s 7)),-(1736*sign (s 11)),0,3664*sign (s 15),3961*sign (s 16),7514*sign (s 17),1;
    -(960*sign (s 3)),-(1352*sign (s 8)),-(2040*sign (s 12)),-(3664*sign (s 15)),0,825*sign (s 18),5670*sign (s 19),1;
    -(1785*sign (s 4)),-(2023*sign (s 9)),-(2535*sign (s 13)),-(3961*sign (s 16)),-(825*sign (s 18)),0,4845*sign (s 20),1;
    -(6630*sign (s 5)),-(6698*sign (s 10)),-(6870*sign (s 14)),-(7514*sign (s 17)),-(5670*sign (s 19)),-(4845*sign (s 20)),0,1;
    -(1),-(1),-(1),-(1),-(1),-(1),-(1),0]

lemma template_coded (s : Fin 21 → Bool) :
    template s=signedBase (highBits s).toNat (lowBits s).toNat := by
  have hl0 : (lowBits s).toNat.testBit 0=s 0 :=
    encode_testBit _ 0 (by decide)
  have hl1 : (lowBits s).toNat.testBit 1=s 1 :=
    encode_testBit _ 1 (by decide)
  have hl2 : (lowBits s).toNat.testBit 2=s 2 :=
    encode_testBit _ 2 (by decide)
  have hl3 : (lowBits s).toNat.testBit 3=s 3 :=
    encode_testBit _ 3 (by decide)
  have hl4 : (lowBits s).toNat.testBit 4=s 4 :=
    encode_testBit _ 4 (by decide)
  have hl5 : (lowBits s).toNat.testBit 5=s 5 :=
    encode_testBit _ 5 (by decide)
  have hh0 : (highBits s).toNat.testBit 0=s 6 :=
    encode_testBit _ 0 (by decide)
  have hh1 : (highBits s).toNat.testBit 1=s 7 :=
    encode_testBit _ 1 (by decide)
  have hh2 : (highBits s).toNat.testBit 2=s 8 :=
    encode_testBit _ 2 (by decide)
  have hh3 : (highBits s).toNat.testBit 3=s 9 :=
    encode_testBit _ 3 (by decide)
  have hh4 : (highBits s).toNat.testBit 4=s 10 :=
    encode_testBit _ 4 (by decide)
  have hh5 : (highBits s).toNat.testBit 5=s 11 :=
    encode_testBit _ 5 (by decide)
  have hh6 : (highBits s).toNat.testBit 6=s 12 :=
    encode_testBit _ 6 (by decide)
  have hh7 : (highBits s).toNat.testBit 7=s 13 :=
    encode_testBit _ 7 (by decide)
  have hh8 : (highBits s).toNat.testBit 8=s 14 :=
    encode_testBit _ 8 (by decide)
  have hh9 : (highBits s).toNat.testBit 9=s 15 :=
    encode_testBit _ 9 (by decide)
  have hh10 : (highBits s).toNat.testBit 10=s 16 :=
    encode_testBit _ 10 (by decide)
  have hh11 : (highBits s).toNat.testBit 11=s 17 :=
    encode_testBit _ 11 (by decide)
  have hh12 : (highBits s).toNat.testBit 12=s 18 :=
    encode_testBit _ 12 (by decide)
  have hh13 : (highBits s).toNat.testBit 13=s 19 :=
    encode_testBit _ 13 (by decide)
  have hh14 : (highBits s).toNat.testBit 14=s 20 :=
    encode_testBit _ 14 (by decide)
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [template,signedBase,Matrix.of_apply,
    hl0,hl1,hl2,hl3,hl4,hl5,hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9,hh10,hh11,hh12,hh13,hh14]


#print axioms encode_get
#print axioms template_coded
end Erdos213.AxisBaseCompleteness
