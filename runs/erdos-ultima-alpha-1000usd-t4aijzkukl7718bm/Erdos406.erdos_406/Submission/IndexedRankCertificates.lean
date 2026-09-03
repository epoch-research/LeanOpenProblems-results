import Submission.IndexedAffineCertificates

/-! A finite-index safety criterion for paired digit automata. Good values
may be accepted at arbitrary finitely many exponents; their value coordinates
need not themselves be bounded in the accepted language. No witness is given. -/

namespace Erdos406IndexedCertificate
open Erdos406AffineCertificate Erdos406GroupedCertificate

structure RankSafety {σ : Type*} (b : ℕ) (D : DFA (ℕ × ℕ) σ) where
  H : σ → Prop
  G : σ → Prop
  K : σ → Prop
  rank : σ → ℕ
  bound : ℕ
  H_start : H D.start
  H_step : ∀ s a, a < b → Good a → H s → H (D.step s (a,0))
  G_start : ∀ s a u, a < b → u < b → Good a → 0 < u → H s → G (D.step s (a,u))
  G_step : ∀ s a u, a < b → u < b → Good a → G s → G (D.step s (a,u))
  K_accept : ∀ s, s ∈ D.accept → K s
  K_step : ∀ s a u, a < b → u < b → Good a → K (D.step s (a,u)) → K s
  rank_step : ∀ s a u, a < b → u < b → Good a → G s → K (D.step s (a,u)) →
    rank (D.step s (a,u)) < rank s
  rank_bound : ∀ s, rank s ≤ bound

namespace RankSafety
variable {σ : Type*} {b : ℕ} {D : DFA (ℕ × ℕ) σ}
variable (S : RankSafety b D) (hb : 2 ≤ b) (h : ℕ) (hbase : b = 3 ^ h)
include h hbase

lemma good_zero_reachable (n : ℕ) (hg : Good n) :
    S.H (evalPair b hb D n 0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [evalPair_zero] using S.H_start
    · have hdiv : Good (n / b) := by
        rw [hbase]
        exact Erdos406SparseTriple.good_div_pow hg h
      have hmod : Good (n % b) := by
        rw [hbase]
        exact Erdos406SparseTriple.good_mod_pow hg h
      rw [evalPair_step _ _ _ _ _ (by simp [hn]), Nat.zero_div, Nat.zero_mod]
      exact S.H_step _ _ (Nat.mod_lt _ (by omega)) hmod
        (ih (n/b) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) hb) hdiv)

lemma good_positive_reachable : ∀ n k, Good n → 0 < k →
    S.G (evalPair b hb D n k) := by
  apply pair_induction b hb
    (P := fun n k => Good n → 0 < k → S.G (evalPair b hb D n k))
  · intro _ hk
    omega
  · intro n k hn ih hg hk
    have hdiv : Good (n / b) := by
      rw [hbase]
      exact Erdos406SparseTriple.good_div_pow hg h
    have hmod : Good (n % b) := by
      rw [hbase]
      exact Erdos406SparseTriple.good_mod_pow hg h
    have hnb : n % b < b := Nat.mod_lt _ (by omega)
    have hkb : k % b < b := Nat.mod_lt _ (by omega)
    rw [evalPair_step _ _ _ _ _ hn]
    by_cases hquot : k / b = 0
    · have hkmod : 0 < k % b := by
        have he := Nat.mod_add_div k b
        rw [hquot, mul_zero, add_zero] at he
        omega
      have hh := S.good_zero_reachable hb h hbase (n / b) hdiv
      rw [← hquot] at hh
      exact S.G_start _ _ _ hnb hkb hmod hkmod hh
    · exact S.G_step _ _ _ hnb hkb hmod (ih hdiv (Nat.pos_of_ne_zero hquot))

/-- Each further exponent digit consumes one rank once the exponent is positive. -/
lemma log_add_rank_bound : ∀ n k, Good n → 0 < k →
    S.K (evalPair b hb D n k) →
    Nat.log b k + S.rank (evalPair b hb D n k) ≤ S.bound := by
  apply pair_induction b hb (P := fun n k => Good n → 0 < k →
    S.K (evalPair b hb D n k) →
    Nat.log b k + S.rank (evalPair b hb D n k) ≤ S.bound)
  · intro _ hk
    omega
  · intro n k hn ih hg hk hK
    have hdiv : Good (n / b) := by
      rw [hbase]
      exact Erdos406SparseTriple.good_div_pow hg h
    have hmod : Good (n % b) := by
      rw [hbase]
      exact Erdos406SparseTriple.good_mod_pow hg h
    have hnb : n % b < b := Nat.mod_lt _ (by omega)
    have hkb : k % b < b := Nat.mod_lt _ (by omega)
    by_cases hquot : k / b = 0
    · have hsmall : k < b := by
        have he := Nat.div_eq_zero_iff.mp hquot
        omega
      rw [Nat.log_of_lt hsmall, zero_add]
      exact S.rank_bound _
    · have hkq : 0 < k / b := Nat.pos_of_ne_zero hquot
      have hG := S.good_positive_reachable hb h hbase (n / b) (k / b) hdiv hkq
      rw [evalPair_step _ _ _ _ _ hn] at hK ⊢
      have hKpre := S.K_step _ _ _ hnb hkb hmod hK
      have hi := ih hdiv hkq hKpre
      have hr := S.rank_step _ _ _ hnb hkb hmod hG hK
      have hbk : b ≤ k := by
        by_contra hbk
        have := Nat.div_eq_of_lt (by omega : k < b)
        omega
      rw [Nat.log_of_one_lt_of_le (by omega : 1 < b) hbk]
      omega

lemma accepted_good_index_bound (n k : ℕ) (hg : Good n)
    (ha : evalPair b hb D n k ∈ D.accept) : k < b ^ (S.bound + 1) := by
  by_cases hk : k = 0
  · subst k
    positivity
  · have hi := S.log_add_rank_bound hb h hbase n k hg (Nat.pos_of_ne_zero hk)
      (S.K_accept _ ha)
    have hlog : Nat.log b k ≤ S.bound := by omega
    exact (Nat.lt_pow_succ_log_self (by omega : 1 < b) k).trans_le
      (Nat.pow_le_pow_right (by omega : 0 < b) (by omega : Nat.log b k + 1 ≤ S.bound + 1))

end RankSafety

/-- A dynamics certificate together with ranked finite-index safety would
prove the original conjecture. Neither certificate is supplied here. -/
theorem indexed_rank_certificate_criterion {σ : Type*} (C : Dynamics σ)
    (S : RankSafety C.base C.D) (h : ℕ) (hbase : C.base = 3 ^ h) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Erdos406SingleAffine.single_affine_criterion
  refine ((Finset.range (C.base ^ (S.bound + 1))).finite_toSet.image (orbit 4 1)).subset ?_
  rintro n ⟨⟨t,rfl⟩,hg⟩
  refine ⟨t, ?_, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_range]
  exact S.accepted_good_index_bound C.base_ge_two h hbase (orbit 4 1 t) t hg
    (C.accepts_orbit t)

#print axioms RankSafety.accepted_good_index_bound
#print axioms indexed_rank_certificate_criterion
end Erdos406IndexedCertificate
