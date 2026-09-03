import Submission.MSDCertificates

/-! Soundness of upward-closed subset certificates for NFA strided-multiplication
invariants. A concrete finite family may be stored as an antichain; neither
an antichain nor an invariant witness is supplied in this file. -/
namespace Erdos406NFAAntichain
open Erdos406MSDCertificate

lemma stepSet_mono {σ : Type*} (M : NFA ℕ σ) {U V : Set σ} (h : U ⊆ V) (d : ℕ) :
    M.stepSet U d ⊆ M.stepSet V d := by
  intro r hr
  obtain ⟨q, hq, he⟩ := NFA.mem_stepSet.mp hr
  exact NFA.mem_stepSet.mpr ⟨q, h hq, he⟩

/-- `family q c` stores lower bounds on possible output-state sets for a
single input state and a multiplication carry. Upward closure is implicit. -/
structure Core (σ : Type*) where
  M : NFA ℕ σ
  cutoff : ℕ
  stride : ℕ
  stride_pos : 0 < stride
  family : σ → ℕ → Set (Set σ)
  relation_start : ∀ q ∈ M.start, ∀ c, c < 4 ^ stride →
    ∃ U ∈ family q c, U ⊆ evalNat M.toDFA c
  relation_step : ∀ q c U, U ∈ family q c → ∀ d e c' r,
    c < 4 ^ stride → d < 3 → e < 3 → c' < 4 ^ stride → 4 ^ stride * d + c' = 3 * c + e →
    r ∈ M.step q d → ∃ V ∈ family r c', V ⊆ M.stepSet U e
  relation_finish : ∀ q U, U ∈ family q 0 → q ∈ M.accept →
    ∃ r ∈ U, r ∈ M.accept
  seed : ∀ r, r < stride → ∃ q ∈ evalNat M.toDFA (4 ^ (cutoff + r)), q ∈ M.accept

namespace Core
variable {σ : Type*} (C : Core σ)

/-- The nondeterministic certificate induces a sound powerset-DFA
certificate without requiring an explicit determinized transition table. -/
def toDFAcore : Erdos406MSDCertificate.Core (Set σ) where
  D := C.M.toDFA
  stride := C.stride
  stride_pos := C.stride_pos
  cutoff := C.cutoff
  R S T c := ∀ q ∈ S, ∃ U ∈ C.family q c, U ⊆ T
  relation_start := by
    intro c hc q hq
    exact C.relation_start q hq c (by simpa using hc)
  relation_step := by
    intro S T c d e c' hc hd he hc' hcarry hrel r hr
    obtain ⟨q, hq, hqr⟩ := NFA.mem_stepSet.mp hr
    obtain ⟨U, hU, hUT⟩ := hrel q hq
    obtain ⟨V, hV, hVW⟩ := C.relation_step q c U hU d e c' r
      (by simpa using hc) hd he (by simpa using hc')
      (by simpa using hcarry) hqr
    exact ⟨V, hV, hVW.trans (stepSet_mono C.M hUT e)⟩
  relation_finish := by
    intro S T hrel hacc
    obtain ⟨q, hqS, hqa⟩ := hacc
    obtain ⟨U, hU, hUS⟩ := hrel q hqS
    obtain ⟨r, hrU, hra⟩ := C.relation_finish q U hU hqa
    exact ⟨r, hUS hrU, hra⟩
  seeds := by
    intro r hr
    exact C.seed r hr

/-- With an all-word binary safety invariant, an NFA subset certificate
would settle the original conjecture. The certificate remains a hypothesis. -/
theorem finite_of_binary_safety (G : Set σ) (hstart : C.M.start ⊆ G)
    (hstep : ∀ q ∈ G, ∀ d, d < 2 → C.M.step q d ⊆ G)
    (hreject : Disjoint G C.M.accept) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Erdos406MSDCertificate.eventual_criterion C.toDFAcore (fun S => S ⊆ G)
  · exact hstart
  · intro S d hd hS r hr
    obtain ⟨q, hq, hqr⟩ := NFA.mem_stepSet.mp hr
    exact hstep q (hS hq) d hd hqr
  · intro S hS hacc
    obtain ⟨q, hqS, hqa⟩ := hacc
    exact Set.disjoint_left.mp hreject (hS hqS) hqa

/-- Every finite-state subset certificate can be pruned to inclusion-minimal
output sets. This justifies the antichain representation, without imposing
an unproved fixed bound on its width. -/
noncomputable def prune [Finite σ] : Core σ where
  M := C.M
  cutoff := C.cutoff
  stride := C.stride
  stride_pos := C.stride_pos
  family q c := {U | Minimal (fun V => V ∈ C.family q c) U}
  relation_start := by
    intro q hq c hc
    obtain ⟨U, hU, hUV⟩ := C.relation_start q hq c hc
    obtain ⟨V, hVU, hV⟩ := exists_minimal_le_of_wellFoundedLT
      (fun V => V ∈ C.family q c) U hU
    exact ⟨V, hV, hVU.trans hUV⟩
  relation_step := by
    intro q c U hU d e c' r hc hd he hc' hcarry hr
    obtain ⟨V, hV, hVU⟩ := C.relation_step q c U hU.prop d e c' r hc hd he hc' hcarry hr
    obtain ⟨W, hWV, hW⟩ := exists_minimal_le_of_wellFoundedLT
      (fun W => W ∈ C.family r c') V hV
    exact ⟨W, hW, hWV.trans hVU⟩
  relation_finish := by
    intro q U hU hq
    exact C.relation_finish q U hU.prop hq
  seed := C.seed

lemma prune_antichain [Finite σ] (q : σ) (c : ℕ) :
    IsAntichain (fun U V : Set σ => U ⊆ V) (C.prune.family q c) := by
  intro U hU V hV hne hUV
  apply hne
  exact Set.Subset.antisymm hUV (hV.le_of_le hU.prop hUV)

lemma prune_finite [Finite σ] (q : σ) (c : ℕ) : (C.prune.family q c).Finite :=
  Set.toFinite _

end Core

lemma evalNat_mul_three_add {σ : Type*} (D : DFA ℕ σ)
    (hpad : D.step D.start 0 = D.start) (n d : ℕ) (hd : d < 3) :
    evalNat D (3 * n + d) = D.step (evalNat D n) d := by
  by_cases h : 3 * n + d = 0
  · have hn : n = 0 := by omega
    have hd0 : d = 0 := by omega
    subst n; subst d
    simpa only [mul_zero, zero_add, evalNat_zero] using hpad.symm
  · rw [evalNat_pos D (by omega : 0 < 3 * n + d)]
    have hdiv : (3 * n + d) / 3 = n := by omega
    have hmod : (3 * n + d) % 3 = d := by omega
    rw [hdiv, hmod]

/-- Completeness of the unrestricted subset format: any padded NFA with the
required multiplication closure and seeds has such a certificate. Closure
and the seeds remain assumptions; this does not assert an invariant exists. -/
def coreOfClosure {σ : Type*} (M : NFA ℕ σ) (E s : ℕ) (hs : 0 < s)
    (hpad : M.stepSet M.start 0 = M.start)
    (hclosed : ∀ n, (∃ q ∈ evalNat M.toDFA n, q ∈ M.accept) →
      ∃ q ∈ evalNat M.toDFA (4 ^ s * n), q ∈ M.accept)
    (hseed : ∀ r, r < s → ∃ q ∈ evalNat M.toDFA (4 ^ (E + r)), q ∈ M.accept) :
    Core σ where
  M := M
  cutoff := E
  stride := s
  stride_pos := hs
  family q c := {U | ∃ n, q ∈ evalNat M.toDFA n ∧ U = evalNat M.toDFA (4 ^ s * n + c)}
  relation_start := by
    intro q hq c _
    refine ⟨evalNat M.toDFA c, ⟨0, ?_, ?_⟩, Set.Subset.rfl⟩
    · simpa [evalNat_zero, NFA.toDFA] using hq
    · simp
  relation_step := by
    rintro q c U ⟨n, hqn, rfl⟩ d e c' r _ hd he _ hcarry hqr
    refine ⟨evalNat M.toDFA (4 ^ s * (3 * n + d) + c'), ⟨3 * n + d, ?_, rfl⟩, ?_⟩
    · rw [evalNat_mul_three_add M.toDFA hpad n d hd]
      exact NFA.mem_stepSet.mpr ⟨q, hqn, hqr⟩
    · have heq : 4 ^ s * (3 * n + d) + c' = 3 * (4 ^ s * n + c) + e := by
        calc
          _ = 3 * (4 ^ s * n) + (4 ^ s * d + c') := by ring
          _ = 3 * (4 ^ s * n) + (3 * c + e) := by rw [hcarry]
          _ = _ := by ring
      rw [heq, evalNat_mul_three_add M.toDFA hpad _ e he]
      exact Set.Subset.rfl
  relation_finish := by
    rintro q U ⟨n, hqn, rfl⟩ hqa
    simpa only [add_zero] using hclosed n ⟨q, hqn, hqa⟩
  seed := hseed

#print axioms Core.prune
#print axioms Core.prune_antichain
#print axioms coreOfClosure
#print axioms Core.toDFAcore
#print axioms Core.finite_of_binary_safety
end Erdos406NFAAntichain
