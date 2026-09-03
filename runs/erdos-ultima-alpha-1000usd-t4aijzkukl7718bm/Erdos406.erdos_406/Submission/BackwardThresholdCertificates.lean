import Submission.IntegerRoundingMSDCertificates

/-! Necessary backward-image safety for threshold barriers, and sound finite
carry upper bounds for those images. No separating barrier is supplied. -/
namespace Erdos406BackwardThreshold
open Erdos406AffineCertificate Erdos406GroupedCertificate Erdos406AffinePotential

def jump (k n : ℕ) : ℕ := 4^k*n + orbit 4 1 k

lemma jump_zero (n : ℕ) : jump 0 n = n := by simp [jump]

lemma jump_succ (k n : ℕ) : jump (k+1) n = 4*jump k n+1 := by
  simp only [jump,pow_succ,orbit_succ]
  ring

lemma threshold_preserved_jump (V : ℕ → ℝ) (B : ℝ)
    (hpres : ∀ n, B < V n → B < V (4*n+1)) (k n : ℕ)
    (hn : B < V n) : B < V (jump k n) := by
  induction k with
  | zero => simpa only [jump_zero] using hn
  | succ k ih => simpa only [jump_succ] using hpres (jump k n) ih

/-- Safety is necessary on every backward image, without assuming any
homogeneous multiplier, monotonicity, or integrality of the score. -/
theorem backward_safety_necessary (V : ℕ → ℝ) (B : ℝ)
    (hpres : ∀ n, B < V n → B < V (4*n+1))
    (hgood : ∀ n, Good n → V n ≤ B) (k n : ℕ)
    (hn : Good (jump k n)) : V n ≤ B := by
  by_contra h
  have hi := threshold_preserved_jump V B hpres k n (lt_of_not_ge h)
  exact (not_lt_of_ge (hgood _ hn)) hi

/-- Upper-score potentials for the language `good(q*n+a)`, read most
significant digit first. Reachability may be overapproximated by `R`.
The relation is closed under all allowed carry steps; no closure property
is inferred merely from deleting nonaccepting states in a search graph. -/
structure BackwardUpper (σ : Type*) where
  D : DFA ℕ σ
  w : σ → ℕ → ℝ
  q : ℕ
  a : ℕ
  q_pos : 0 < q
  a_lt : a < q
  R : σ → ℕ → Prop
  P : σ → ℕ → ℝ
  relation_start : ∀ c, c < q → Good c → R D.start c
  upper_start : ∀ c, c < q → Good c → 0 ≤ P D.start c
  relation_step : ∀ s c d e c', c < q → d < 3 → e < 2 → c' < q →
    q*d+c' = 3*c+e → R s c → R (D.step s d) c'
  upper_step : ∀ s c d e c', c < q → d < 3 → e < 2 → c' < q →
    q*d+c' = 3*c+e → R s c → P s c + w s d ≤ P (D.step s d) c'
  upper_finish : ∀ s, R s a → P s a ≤ 0

namespace BackwardUpper
variable {σ : Type*} (C : BackwardUpper σ)

lemma relation_upper (n c : ℕ) (hc : c < C.q) (hg : Good (C.q*n+c)) :
    C.R (evalNat 3 C.D n) c ∧
      weightNat C.D C.w n ≤ C.P (evalNat 3 C.D n) c := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [mul_zero,zero_add] at hg
      simpa only [evalNat_zero,weightNat_zero] using
        And.intro (C.relation_start c hc hg) (C.upper_start c hc hg)
    · have hnpos := Nat.pos_of_ne_zero hn
      let d := n%3
      let cp := (C.q*d+c)/3
      let e := (C.q*d+c)%3
      have hd : d < 3 := Nat.mod_lt _ (by decide)
      have hcp : cp < C.q := by
        have hmul : C.q*d ≤ C.q*2 := Nat.mul_le_mul_left _ (by omega)
        dsimp only [cp]
        omega
      have hout : 0 < C.q*n+c := by
        have hh := Nat.mul_pos C.q_pos hnpos
        omega
      obtain ⟨houtq,houtm⟩ := affine_div_mod 3 C.q n c (by decide)
      have hgl : ((C.q*n+c)%3 :: Nat.digits 3 ((C.q*n+c)/3)) ⊆ [0,1] := by
        simpa only [Good,Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hout] using hg
      have he : e < 2 := by
        have hh := hgl (by simp : (C.q*n+c)%3 ∈
          ((C.q*n+c)%3 :: Nat.digits 3 ((C.q*n+c)/3)))
        rw [houtm] at hh
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
        dsimp only [e,d]
        omega
      have hgq : Good (C.q*(n/3)+cp) := by
        change Nat.digits 3 (C.q*(n/3)+cp) ⊆ [0,1]
        intro z hz
        apply hgl
        apply List.mem_cons_of_mem
        simpa only [houtq] using hz
      have hi := ih (n/3) (Nat.div_lt_self hnpos (by decide)) cp hcp hgq
      have hid : C.q*d+c = 3*cp+e := by dsimp only [cp,e]; omega
      have hr := C.relation_step _ cp d e c hcp hd he hc hid hi.1
      have hp := C.upper_step _ cp d e c hcp hd he hc hid hi.1
      rw [evalNat_pos 3 C.D (by decide) hnpos,weightNat_pos C.D C.w hnpos]
      exact ⟨hr, by dsimp only [d] at hp; linarith [hi.2]⟩

/-- Finite inequalities suffice for safety on the full backward language,
not merely on the finite sample words used in initial synthesis. -/
theorem good_affine_upper (n : ℕ) (hn : Good (C.q*n+C.a)) :
    weightNat C.D C.w n ≤ 0 := by
  have hh := C.relation_upper n C.a C.a_lt hn
  exact hh.2.trans (C.upper_finish _ hh.1)

end BackwardUpper

#print axioms backward_safety_necessary
#print axioms BackwardUpper.good_affine_upper
end Erdos406BackwardThreshold
