import Submission.SingleAffineCertificates

/-! Soundness of an exponent-indexed affine automaton certificate.
The two input coordinates are (z,k), and the joint orbit step is
(z,k) ↦ (4*z+1,k+1). No certificate witness is supplied here. -/

namespace Erdos406IndexedCertificate
open Erdos406AffineCertificate Erdos406GroupedCertificate

lemma pair_div_sum_lt (b : ℕ) (hb : 2 ≤ b) (n k : ℕ)
    (h : ¬ (n = 0 ∧ k = 0)) : n / b + k / b < n + k := by
  have hnle := Nat.div_le_self n b
  have hkle := Nat.div_le_self k b
  by_cases hn : n = 0
  · have hk : 0 < k := by omega
    have := Nat.div_lt_self hk hb
    omega
  · have := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hb
    omega

lemma pair_induction (b : ℕ) (hb : 2 ≤ b) {P : ℕ → ℕ → Prop}
    (hzero : P 0 0)
    (hstep : ∀ n k, ¬ (n = 0 ∧ k = 0) → P (n / b) (k / b) → P n k) :
    ∀ n k, P n k := by
  intro n k
  generalize htotal : n + k = s
  induction s using Nat.strong_induction_on generalizing n k with
  | h s ih =>
    by_cases hz : n = 0 ∧ k = 0
    · rcases hz with ⟨rfl, rfl⟩
      exact hzero
    · apply hstep n k hz
      exact ih (n / b + k / b) (by rw [← htotal]; exact pair_div_sum_lt b hb n k hz)
        _ _ rfl

def evalPair {σ : Type*} (b : ℕ) (hb : 2 ≤ b) (D : DFA (ℕ × ℕ) σ) (n k : ℕ) : σ :=
  if _h : n = 0 ∧ k = 0 then D.start
  else D.step (evalPair b hb D (n / b) (k / b)) (n % b, k % b)
termination_by n + k
decreasing_by exact pair_div_sum_lt b hb n k _h

lemma evalPair_zero {σ : Type*} (b : ℕ) (hb : 2 ≤ b) (D : DFA (ℕ × ℕ) σ) :
    evalPair b hb D 0 0 = D.start := by
  rw [evalPair]
  simp

lemma evalPair_step {σ : Type*} (b : ℕ) (hb : 2 ≤ b) (D : DFA (ℕ × ℕ) σ)
    (n k : ℕ) (h : ¬ (n = 0 ∧ k = 0)) :
    evalPair b hb D n k = D.step (evalPair b hb D (n / b) (k / b)) (n % b, k % b) := by
  rw [evalPair, dif_neg h]

lemma capped_digit_step (b E k : ℕ) (hb : 0 < b) :
    min E (b * min E (k / b) + k % b) = min E k := by
  have he := Nat.mod_add_div k b
  by_cases h : E ≤ k / b
  · have hE : E ≤ b * E := Nat.le_mul_of_pos_left E hb
    have hleft : E ≤ b * E + k % b := by omega
    have hk : E ≤ k := h.trans (Nat.div_le_self k b)
    rw [min_eq_left h, min_eq_left hleft, min_eq_left hk]
  · rw [min_eq_right (by omega : k / b ≤ E)]
    congr 1
    omega

structure Dynamics (σ : Type*) where
  D : DFA (ℕ × ℕ) σ
  base : ℕ
  base_ge_two : 2 ≤ base
  R : σ → σ → ℕ → ℕ → Prop
  relation_start : ∀ c d, c < 4 → d < 2 →
    R D.start (evalPair base base_ge_two D c d) c d
  relation_step : ∀ s t c d a u a' u' c' d',
    c < 4 → d < 2 → a < base → u < base → a' < base → u' < base → c' < 4 → d' < 2 →
    4 * a + c' = base * c + a' → u + d' = base * d + u' → R s t c d →
    R (D.step s (a,u)) (D.step t (a',u')) c' d'
  relation_finish : ∀ s t, R s t 1 1 → s ∈ D.accept → t ∈ D.accept
  seed : D.start ∈ D.accept

structure Core (σ : Type*) extends Dynamics σ where
  cutoff : ℕ
  G : σ → ℕ → Prop
  safety_start : G D.start 0
  safety_step : ∀ s r a u, r ≤ cutoff → a < base → u < base → Good a → G s r →
    G (D.step s (a,u)) (min cutoff (base * r + u))
  safety_finish : ∀ s, G s cutoff → s ∉ D.accept

namespace Dynamics
variable {σ : Type*} (C : Dynamics σ)

lemma relation (n k : ℕ) : ∀ c d, c < 4 → d < 2 →
    C.R (evalPair C.base C.base_ge_two C.D n k)
      (evalPair C.base C.base_ge_two C.D (4 * n + c) (k + d)) c d := by
  apply pair_induction C.base C.base_ge_two (P := fun n k => ∀ c d, c < 4 → d < 2 →
    C.R (evalPair C.base C.base_ge_two C.D n k)
      (evalPair C.base C.base_ge_two C.D (4 * n + c) (k + d)) c d) ?_ ?_ n k
  · intro c d hc hd
    simpa only [mul_zero, zero_add, evalPair_zero] using C.relation_start c d hc hd
  · intro n k hn ih c d hc hd
    have hb : 0 < C.base := by have := C.base_ge_two; omega
    let a := n % C.base
    let u := k % C.base
    let cp := (4 * a + c) / C.base
    let dp := (u + d) / C.base
    let aa := (4 * a + c) % C.base
    let uu := (u + d) % C.base
    have ha : a < C.base := Nat.mod_lt n hb
    have hu : u < C.base := Nat.mod_lt k hb
    have haa : aa < C.base := Nat.mod_lt _ hb
    have huu : uu < C.base := Nat.mod_lt _ hb
    have hcp : cp < 4 := by
      apply (Nat.div_lt_iff_lt_mul hb).mpr
      nlinarith
    have hdp : dp < 2 := by
      apply (Nat.div_lt_iff_lt_mul hb).mpr
      have := C.base_ge_two
      nlinarith
    have hr := ih cp dp hcp hdp
    have hs := C.relation_step _ _ cp dp a u aa uu c d hcp hdp ha hu haa huu hc hd
      (by dsimp [cp,aa]; have := Nat.mod_add_div (4*a+c) C.base; omega)
      (by dsimp [dp,uu]; have := Nat.mod_add_div (u+d) C.base; omega) hr
    have hout : ¬ (4 * n + c = 0 ∧ k + d = 0) := by omega
    obtain ⟨hqn, hmn⟩ := affine_div_mod C.base 4 n c hb
    obtain ⟨hqk, hmk⟩ := affine_div_mod C.base 1 k d hb
    simp only [one_mul] at hqk hmk
    rw [evalPair_step _ _ _ _ _ hn, evalPair_step _ _ _ _ _ hout, hqn, hmn, hqk, hmk]
    exact hs

lemma affine_closed {n k : ℕ}
    (ha : evalPair C.base C.base_ge_two C.D n k ∈ C.D.accept) :
    evalPair C.base C.base_ge_two C.D (4*n+1) (k+1) ∈ C.D.accept :=
  C.relation_finish _ _ (C.relation n k 1 1 (by decide) (by decide)) ha

lemma accepts_orbit (t : ℕ) :
    evalPair C.base C.base_ge_two C.D (orbit 4 1 t) t ∈ C.D.accept := by
  induction t with
  | zero => simpa only [orbit_zero, evalPair_zero] using C.seed
  | succ t ih => exact C.affine_closed ih

end Dynamics

namespace Core
variable {σ : Type*} (C : Core σ)

lemma safety (h : ℕ) (hbase : C.base = 3 ^ h) : ∀ n k, Good n →
    C.G (evalPair C.base C.base_ge_two C.D n k) (min C.cutoff k) := by
  apply pair_induction C.base C.base_ge_two
    (P := fun n k => Good n → C.G (evalPair C.base C.base_ge_two C.D n k) (min C.cutoff k))
  · intro _
    simpa only [evalPair_zero, Nat.min_zero] using C.safety_start
  · intro n k hn ih hg
    have hdiv : Good (n / C.base) := by
      rw [hbase]
      exact Erdos406SparseTriple.good_div_pow hg h
    have hmod : Good (n % C.base) := by
      rw [hbase]
      exact Erdos406SparseTriple.good_mod_pow hg h
    have hb : 0 < C.base := by have := C.base_ge_two; omega
    have hs := C.safety_step _ (min C.cutoff (k / C.base)) (n % C.base) (k % C.base)
      (min_le_left ..) (Nat.mod_lt _ hb) (Nat.mod_lt _ hb) hmod (ih hdiv)
    rw [capped_digit_step C.base C.cutoff k hb] at hs
    rwa [evalPair_step _ _ _ _ _ hn]

lemma orbit_cutoff (h : ℕ) (hbase : C.base = 3 ^ h) (t : ℕ) (ht : C.cutoff ≤ t) :
    ¬ Good (orbit 4 1 t) := by
  intro hg
  have hs := C.safety h hbase (orbit 4 1 t) t hg
  rw [min_eq_left ht] at hs
  exact C.safety_finish _ hs (C.toDynamics.accepts_orbit t)

end Core

/-- An actual indexed automaton certificate would settle the exact original
conjecture. The required certificate is not asserted to exist. -/
theorem indexed_certificate_criterion {σ : Type*} (C : Core σ) (h : ℕ)
    (hbase : C.base = 3 ^ h) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Erdos406SingleAffine.single_affine_criterion
  refine ((Finset.range C.cutoff).finite_toSet.image (orbit 4 1)).subset ?_
  rintro n ⟨⟨t,rfl⟩,hg⟩
  refine ⟨t, ?_, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hn
  exact C.orbit_cutoff h hbase t (by omega) hg

#print axioms Dynamics.relation
#print axioms indexed_certificate_criterion
end Erdos406IndexedCertificate
