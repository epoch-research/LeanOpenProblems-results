import Submission.BinaryCertificates

/-! The rejected-copy-zero policy in the q=27 search is obstructed by 1093.
This only excludes that search restriction; it does not settle Erdős 406. -/
namespace Erdos406BinaryPolicyObstruction
open Erdos406BinaryCertificate

lemma eval_1093_forced {σ : Type*} (D : DFA ℕ σ) (f : Fin 27 → σ)
    (hs : D.start = f 0)
    (hsmall : ∀ (r : Fin 27) (d : ℕ), d < 2 → ∀ h : 2 * r.val + d < 27,
      D.step (f r) d = f ⟨2 * r.val + d, h⟩)
    (hzero : ∀ r : Fin 27, r.val % 3 ≠ 0 →
      D.step (f r) 0 = f ⟨2 * r.val % 27, Nat.mod_lt _ (by decide)⟩) :
    evalNat D 1093 = f 13 := by
  have h01 : D.step (f 0) 1 = f 1 := hsmall 0 1 (by decide) (by decide)
  have h10 : D.step (f 1) 0 = f 2 := hsmall 1 0 (by decide) (by decide)
  have h20 : D.step (f 2) 0 = f 4 := hsmall 2 0 (by decide) (by decide)
  have h40 : D.step (f 4) 0 = f 8 := hsmall 4 0 (by decide) (by decide)
  have h81 : D.step (f 8) 1 = f 17 := hsmall 8 1 (by decide) (by decide)
  have h170 : D.step (f 17) 0 = f 7 := hzero 17 (by decide)
  have h70 : D.step (f 7) 0 = f 14 := hsmall 7 0 (by decide) (by decide)
  have h140 : D.step (f 14) 0 = f 1 := hzero 14 (by decide)
  have h11 : D.step (f 1) 1 = f 3 := hsmall 1 1 (by decide) (by decide)
  have h30 : D.step (f 3) 0 = f 6 := hsmall 3 0 (by decide) (by decide)
  have h61 : D.step (f 6) 1 = f 13 := hsmall 6 1 (by decide) (by decide)
  have hd : (Nat.digits 2 1093).reverse = [1,0,0,0,1,0,0,0,1,0,1] := by decide +kernel
  rw [evalNat, hd]
  simp only [DFA.eval, DFA.evalFrom_cons, DFA.evalFrom_nil, hs,
    h01, h10, h20, h40, h81, h170, h70, h140, h11, h30, h61]

/-- No number of copies repairs this particular choice of the rejected orbit:
its forced binary transitions reject a required ternary-good boundary value. -/
theorem zero_tail_policy_impossible {σ : Type*} (D : DFA ℕ σ) (f : Fin 27 → σ)
    (hs : D.start = f 0)
    (hsmall : ∀ (r : Fin 27) (d : ℕ), d < 2 → ∀ h : 2 * r.val + d < 27,
      D.step (f r) d = f ⟨2 * r.val + d, h⟩)
    (hzero : ∀ r : Fin 27, r.val % 3 ≠ 0 →
      D.step (f r) 0 = f ⟨2 * r.val % 27, Nat.mod_lt _ (by decide)⟩)
    (hboundary : ∀ n : ℕ, 512 ≤ n → n ≤ 1537 → Nat.digits 3 n ⊆ [0,1] →
      evalNat D n ∈ D.accept)
    (hreject : f 13 ∉ D.accept) : False := by
  have hg : Nat.digits 3 1093 ⊆ [0,1] := by decide +kernel
  have ha := hboundary 1093 (by decide) (by decide) hg
  rw [eval_1093_forced D f hs hsmall hzero] at ha
  exact hreject ha

#print axioms eval_1093_forced
#print axioms zero_tail_policy_impossible
end Erdos406BinaryPolicyObstruction
