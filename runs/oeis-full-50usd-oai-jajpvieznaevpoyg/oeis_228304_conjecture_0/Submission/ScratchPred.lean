import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix
open scoped BigOperators

lemma zmod_natCast_ne_zero_of_pos_lt (p a : ℕ) (ha0 : 0 < a) (hap : a < p) : (a : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ a := by
    rwa [ZMod.natCast_eq_zero_iff] at h
  exact (Nat.not_dvd_of_pos_of_lt ha0 hap) hdvd

lemma choose_pred_cast (p k : ℕ) (hp : Nat.Prime p) (hk : k < p) :
    (Nat.choose (p-1) k : ZMod p) = (-1 : ZMod p)^k := by
  haveI : Fact p.Prime := ⟨hp⟩
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < p := by omega
      have hksucc : k + 1 < p := hk
      have ih' := ih hklt
      have hp0 : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
      have hrecNat := Nat.choose_succ_right_eq (p-1) k
      -- cast recurrence
      have hrec : (Nat.choose (p-1) (k+1) : ZMod p) * (k+1 : ZMod p) =
          (Nat.choose (p-1) k : ZMod p) * ((p : ZMod p) - 1 - (k : ZMod p)) := by
        have h := congrArg (fun n : ℕ => (n : ZMod p)) hrecNat
        have hkp : k+1 ≤ p := by omega
        have hsubn : (p - 1) - k = p - (k+1) := by omega
        have hcastsub_add : ((p - (k+1) : ℕ) : ZMod p) + (k+1 : ZMod p) = (p : ZMod p) := by
          have hh := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.sub_add_cancel hkp)
          simpa [Nat.cast_add] using hh
        have hcastsub : ((p - (k+1) : ℕ) : ZMod p) = (p : ZMod p) - (k+1 : ZMod p) := by
          exact eq_sub_of_add_eq hcastsub_add
        simpa [Nat.cast_mul, Nat.cast_add, hsubn, hcastsub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
      have hnonzero : (k+1 : ZMod p) ≠ 0 := by
        simpa [Nat.cast_add] using zmod_natCast_ne_zero_of_pos_lt p (k+1) (by omega) hksucc
      apply mul_right_cancel₀ hnonzero
      calc
        (Nat.choose (p - 1) (k + 1) : ZMod p) * (k + 1 : ZMod p)
            = (Nat.choose (p-1) k : ZMod p) * ((p : ZMod p) - 1 - (k : ZMod p)) := hrec
        _ = ((-1 : ZMod p)^k) * (-(k+1 : ZMod p)) := by
          rw [ih']
          simp
          ring
        _ = ((-1 : ZMod p)^(k+1)) * (k+1 : ZMod p) := by
          rw [pow_succ]
          ring
