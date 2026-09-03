import Submission.NFAAntichainCertificates

/-! A finitely checkable interface for subset-family NFA certificates.
All soundness hypotheses are explicit. No certificate data solving Erdős406
are provided in this module. -/
namespace Erdos406NFAFinite
open Erdos406MSDCertificate

variable {σ : Type*} [DecidableEq σ]

structure Data (σ : Type*) [DecidableEq σ] where
  step : σ → ℕ → Finset σ
  start : Finset σ
  accept : Finset σ
  cutoff : ℕ
  stride : ℕ
  family : σ → ℕ → Finset (Finset σ)

namespace Data
variable (D : Data σ)

def toNFA : NFA ℕ σ where
  step q d := D.step q d
  start := D.start
  accept := D.accept

def stepStates (U : Finset σ) (d : ℕ) : Finset σ := U.biUnion (fun q => D.step q d)

def evalStates (n : ℕ) : Finset σ :=
  (Nat.digits 3 n).reverse.foldl D.stepStates D.start

lemma stepStates_coe (U : Finset σ) (d : ℕ) :
    (D.stepStates U d : Set σ) = D.toNFA.stepSet U d := by
  ext r
  simp [stepStates, NFA.mem_stepSet, toNFA]

lemma evalFrom_coe (w : List ℕ) (U : Finset σ) :
    ((w.foldl D.stepStates U : Finset σ) : Set σ) = D.toNFA.evalFrom U w := by
  induction w generalizing U with
  | nil => rfl
  | cons d w ih =>
    rw [List.foldl_cons, NFA.evalFrom_cons, ih, stepStates_coe]

lemma evalStates_coe (n : ℕ) :
    (D.evalStates n : Set σ) = evalNat D.toNFA.toDFA n := by
  exact D.evalFrom_coe (Nat.digits 3 n).reverse D.start

/-- Only the stored subsets are quantified over, not the entire powerset.
Each hypothesis is decidable for finite state types and concrete data. -/
def toCore (hs : 0 < D.stride)
    (hinit : ∀ q ∈ D.start, ∀ c, c < 4 ^ D.stride →
      ∃ U ∈ D.family q c, U ⊆ D.evalStates c)
    (hstep : ∀ q c, c < 4 ^ D.stride → ∀ U ∈ D.family q c,
      ∀ d, d < 3 → ∀ e, e < 3 → ∀ c', c' < 4 ^ D.stride →
      4 ^ D.stride * d + c' = 3 * c + e → ∀ r ∈ D.step q d,
      ∃ V ∈ D.family r c', V ⊆ D.stepStates U e)
    (hfinish : ∀ q ∈ D.accept, ∀ U ∈ D.family q 0, (U ∩ D.accept).Nonempty)
    (hseed : ∀ r, r < D.stride → (D.evalStates (4 ^ (D.cutoff + r)) ∩ D.accept).Nonempty) :
    Erdos406NFAAntichain.Core σ where
  M := D.toNFA
  cutoff := D.cutoff
  stride := D.stride
  stride_pos := hs
  family q c := {U | ∃ V ∈ D.family q c, U = (V : Set σ)}
  relation_start := by
    intro q hq c hc
    obtain ⟨U, hU, hUS⟩ := hinit q hq c hc
    refine ⟨(U : Set σ), ⟨U, hU, rfl⟩, ?_⟩
    rw [← D.evalStates_coe]
    exact hUS
  relation_step := by
    rintro q c U ⟨W, hW, rfl⟩ d e c' r hc hd he hc' hcarry hr
    obtain ⟨V, hV, hVW⟩ := hstep q c hc W hW d hd e he c' hc' hcarry r hr
    refine ⟨(V : Set σ), ⟨V, hV, rfl⟩, ?_⟩
    rw [← D.stepStates_coe]
    exact hVW
  relation_finish := by
    rintro q U ⟨V, hV, rfl⟩ hq
    obtain ⟨r, hr⟩ := hfinish q hq V hV
    exact ⟨r, (Finset.mem_inter.mp hr).1, (Finset.mem_inter.mp hr).2⟩
  seed := by
    intro r hr
    obtain ⟨q, hq⟩ := hseed r hr
    refine ⟨q, ?_, (Finset.mem_inter.mp hq).2⟩
    rw [← D.evalStates_coe]
    exact (Finset.mem_inter.mp hq).1

/-- A complete finite-data certificate implies precisely the original
conjecture. The current file supplies no witness for these hypotheses. -/
theorem finite_of_checks (hs : 0 < D.stride)
    (hinit : ∀ q ∈ D.start, ∀ c, c < 4 ^ D.stride →
      ∃ U ∈ D.family q c, U ⊆ D.evalStates c)
    (hstep : ∀ q c, c < 4 ^ D.stride → ∀ U ∈ D.family q c,
      ∀ d, d < 3 → ∀ e, e < 3 → ∀ c', c' < 4 ^ D.stride →
      4 ^ D.stride * d + c' = 3 * c + e → ∀ r ∈ D.step q d,
      ∃ V ∈ D.family r c', V ⊆ D.stepStates U e)
    (hfinish : ∀ q ∈ D.accept, ∀ U ∈ D.family q 0, (U ∩ D.accept).Nonempty)
    (hseed : ∀ r, r < D.stride → (D.evalStates (4 ^ (D.cutoff + r)) ∩ D.accept).Nonempty)
    (G : Finset σ) (hstartG : D.start ⊆ G)
    (hstepG : ∀ q ∈ G, ∀ d, d < 2 → D.step q d ⊆ G)
    (hrejectG : Disjoint G D.accept) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply (D.toCore hs hinit hstep hfinish hseed).finite_of_binary_safety (G : Set σ)
  · exact hstartG
  · exact hstepG
  · exact Finset.disjoint_coe.mpr hrejectG

end Data
#print axioms Data.toCore
#print axioms Data.finite_of_checks
end Erdos406NFAFinite
