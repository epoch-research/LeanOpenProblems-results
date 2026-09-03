import FormalConjecturesUtil

/-! A computable natural-number mask for finite subsets, with a surjectivity proof. -/
namespace Erdos184Work.FinsetMask

def encode : {n : ℕ} → (Fin n → Bool) → BitVec n
  | 0, _ => 0
  | _+1, f => (encode (fun i => f i.succ)).concat (f 0)

lemma bit_encode {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (encode f).getLsbD i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [encode,BitVec.getLsbD_concat]
    · simpa only [encode,BitVec.getLsbD_concat,Fin.val_succ,
        Nat.add_eq_zero_iff, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        using ih (fun k => f k.succ) j

def word (n j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => j.testBit i.val)

lemma exists_word {n : ℕ} (s : Finset (Fin n)) :
    ∃ j : Fin (2^n), word n j.val = s := by
  let f : Fin n → Bool := fun i => decide (i ∈ s)
  refine ⟨(encode f).toFin,?_⟩
  ext i
  simp only [word,Finset.mem_filter,Finset.mem_univ,true_and]
  change (encode f).toNat.testBit i.val = true ↔ i ∈ s
  rw [BitVec.testBit_toNat,bit_encode]
  simp [f]

#print axioms exists_word
end Erdos184Work.FinsetMask
