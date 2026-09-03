import Submission.SingleAffineCertificates

/-! A subcritical potential criterion and soundness of weighted automata.
No subcritical potential or automaton witness is asserted to exist. -/

namespace Erdos406AffinePotential
open Erdos406AffineCertificate Erdos406GroupedCertificate

lemma orbit_length_log_le (t : ℕ) :
    ((Nat.digits 3 (orbit 4 1 t)).length : ℝ) * Real.log 3 ≤ (t : ℝ) * Real.log 4 := by
  by_cases hz : orbit 4 1 t = 0
  · simp only [hz, Nat.digits_zero, List.length_nil, Nat.cast_zero, zero_mul]
    positivity
  · have hl := Nat.base_pow_length_digits_le 3 (orbit 4 1 t) (by decide) hz
    have hi := Erdos406SingleAffine.single_orbit_identity t
    have hp : (3 : ℝ) ^ (Nat.digits 3 (orbit 4 1 t)).length ≤ (4 : ℝ) ^ t := by
      exact_mod_cast (hl.trans (by omega : 3 * orbit 4 1 t ≤ 4 ^ t))
    have hh := Real.log_le_log (by positivity) hp
    simpa only [Real.log_pow] using hh

lemma rational_subcritical (p q : ℕ) (hq : 0 < q) (hpq : 4 ^ p < 3 ^ q) :
    ((p : ℝ) / q) * Real.log 4 < Real.log 3 := by
  have hpow : (4 : ℝ) ^ p < (3 : ℝ) ^ q := by exact_mod_cast hpq
  have hh := Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hh
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mpr
  nlinarith

/-- Growth along the affine orbit together with a subcritical upper bound
on good digit strings would prove finiteness. The upper bound is required
ONLY on good strings, not on all integers. -/
theorem affine_potential_criterion (V : ℕ → ℝ) (c B : ℝ) (hc : 0 ≤ c)
    (hcrit : c * Real.log 4 < Real.log 3)
    (hgrow : ∀ n, V n + 1 ≤ V (4*n+1))
    (hgood : ∀ n, Good n → V n ≤ c * (Nat.digits 3 n).length + B) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have horbit : ∀ t : ℕ, V 0 + (t : ℝ) ≤ V (orbit 4 1 t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hs := hgrow (orbit 4 1 t)
      rw [orbit_succ]
      push_cast
      linarith
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hgap : 0 < Real.log 3 - c * Real.log 4 := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt ((B-V 0) * Real.log 3 / (Real.log 3-c*Real.log 4))
  have hlarge := (div_lt_iff₀ hgap).mp hM
  have hcut : ∀ t : ℕ, M ≤ t → ¬ Good (orbit 4 1 t) := by
    intro t ht hg
    have hb := (horbit t).trans (hgood _ hg)
    have hb' := mul_le_mul_of_nonneg_right hb hlog.le
    have hl := mul_le_mul_of_nonneg_left (orbit_length_log_le t) hc
    have hMt : (M : ℝ) ≤ t := by exact_mod_cast ht
    have htgap := mul_le_mul_of_nonneg_right hMt hgap.le
    nlinarith
  apply Erdos406SingleAffine.single_affine_criterion
  refine ((Finset.range M).finite_toSet.image (orbit 4 1)).subset ?_
  rintro n ⟨⟨t,rfl⟩,hg⟩
  refine ⟨t, ?_, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra ht
  exact hcut t (by omega) hg

def weightFrom {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) : σ → List ℕ → ℝ
  | _, [] => 0
  | s, d::L => w s d + weightFrom D w (D.step s d) L

lemma weightFrom_append_singleton {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ)
    (s : σ) (L : List ℕ) (d : ℕ) :
    weightFrom D w s (L++[d]) = weightFrom D w s L + w (D.evalFrom s L) d := by
  induction L generalizing s with
  | nil => simp [weightFrom]
  | cons a L ih => simp only [List.cons_append, weightFrom, DFA.evalFrom_cons, ih]; ring

def weightNat {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (n : ℕ) : ℝ :=
  weightFrom D w D.start (Nat.digits 3 n).reverse

lemma weightNat_zero {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) : weightNat D w 0 = 0 := by
  simp [weightNat, weightFrom]

lemma weightNat_pos {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    weightNat D w n = weightNat D w (n/3) + w (evalNat 3 D (n/3)) (n%3) := by
  rw [weightNat, Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn,
    List.reverse_cons, weightFrom_append_singleton]
  rfl

structure Growth (σ : Type*) where
  D : DFA ℕ σ
  w : σ → ℕ → ℝ
  R : σ → σ → ℕ → Prop
  P : σ → σ → ℕ → ℝ
  relation_start : ∀ c, c < 4 → R D.start (evalNat 3 D c) c
  relation_step : ∀ s t c d e c', c < 4 → d < 3 → e < 3 → c' < 4 →
    4*d+c' = 3*c+e → R s t c → R (D.step s d) (D.step t e) c'
  lower_start : ∀ c, c < 4 → P D.start (evalNat 3 D c) c ≤ weightNat D w c
  lower_step : ∀ s t c d e c', c < 4 → d < 3 → e < 3 → c' < 4 →
    4*d+c' = 3*c+e → R s t c →
    P (D.step s d) (D.step t e) c' ≤ P s t c + w t e - w s d
  lower_finish : ∀ s t, R s t 1 → 1 ≤ P s t 1

namespace Growth
variable {σ : Type*} (C : Growth σ)

lemma relation_potential (n c : ℕ) (hc : c < 4) :
    C.R (evalNat 3 C.D n) (evalNat 3 C.D (4*n+c)) c ∧
    C.P (evalNat 3 C.D n) (evalNat 3 C.D (4*n+c)) c ≤
      weightNat C.D C.w (4*n+c) - weightNat C.D C.w n := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [mul_zero, zero_add, evalNat_zero, weightNat_zero, sub_zero] using
        And.intro (C.relation_start c hc) (C.lower_start c hc)
    · have hnpos := Nat.pos_of_ne_zero hn
      let d := n % 3
      let cp := (4*d+c)/3
      let e := (4*d+c)%3
      have hd : d < 3 := Nat.mod_lt _ (by decide)
      have he : e < 3 := Nat.mod_lt _ (by decide)
      have hcp : cp < 4 := by dsimp [cp]; omega
      have hi := ih (n/3) (Nat.div_lt_self hnpos (by decide)) cp hcp
      have hid : 4*d+c = 3*cp+e := by dsimp [cp,e]; omega
      have hr := C.relation_step _ _ cp d e c hcp hd he hc hid hi.1
      have hp := C.lower_step _ _ cp d e c hcp hd he hc hid hi.1
      have hout : 0 < 4*n+c := by omega
      obtain ⟨hq,hm⟩ := affine_div_mod 3 4 n c (by decide)
      rw [evalNat_pos 3 C.D (by decide) hnpos, evalNat_pos 3 C.D (by decide) hout, hq, hm,
        weightNat_pos C.D C.w hnpos, weightNat_pos C.D C.w hout, hq, hm]
      exact ⟨hr, by dsimp only [d,cp,e] at hi hp ⊢; linarith⟩

lemma grows (n : ℕ) : weightNat C.D C.w n + 1 ≤ weightNat C.D C.w (4*n+1) := by
  have hh := C.relation_potential n 1 (by decide)
  have hf := C.lower_finish _ _ hh.1
  linarith

end Growth

structure GoodBound {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) where
  c : ℝ
  B : ℝ
  c_nonneg : 0 ≤ c
  G : σ → Prop
  J : σ → ℝ
  start : G D.start
  step : ∀ s d, d < 2 → G s → G (D.step s d)
  weight_step : ∀ s d, d < 2 → G s → w s d ≤ c + J (D.step s d) - J s
  bound : ∀ s, G s → J s - J D.start ≤ B

namespace GoodBound
variable {σ : Type*} {D : DFA ℕ σ} {w : σ → ℕ → ℝ} (S : GoodBound D w)

lemma weight_word (L : List ℕ) (hL : ∀ d ∈ L, d < 2) (s : σ) (hs : S.G s) :
    weightFrom D w s L ≤ S.c * (L.length : ℝ) + S.J (D.evalFrom s L) - S.J s := by
  induction L generalizing s with
  | nil => simp [weightFrom]
  | cons d L ih =>
    have hd := hL d (List.mem_cons_self ..)
    have ht := ih (fun a ha => hL a (List.mem_cons_of_mem _ ha)) _ (S.step s d hd hs)
    have hw := S.weight_step s d hd hs
    simp only [weightFrom, List.length_cons, Nat.cast_add, Nat.cast_one, DFA.evalFrom_cons]
    linarith

lemma good_bound (n : ℕ) (hn : Good n) :
    weightNat D w n ≤ S.c * (Nat.digits 3 n).length + S.B := by
  have hw : ∀ d ∈ (Nat.digits 3 n).reverse, d < 2 := by
    intro d hd
    have hh := hn (List.mem_reverse.mp hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    omega
  have hg := reachable_word D (fun d => d < 2) S.G S.step _ hw D.start S.start
  have hb := S.bound _ hg
  have hh := S.weight_word _ hw D.start S.start
  simp only [List.length_reverse] at hh
  change weightFrom D w D.start (Nat.digits 3 n).reverse ≤ _
  linarith

end GoodBound

/-- A finite weighted automaton with the stated STRICT slope inequality
would settle Erdős406. No such witness is supplied. -/
theorem weighted_affine_criterion {σ : Type*} (C : Growth σ) (S : GoodBound C.D C.w)
    (hcrit : S.c * Real.log 4 < Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite :=
  affine_potential_criterion (weightNat C.D C.w) S.c S.B S.c_nonneg hcrit C.grows S.good_bound

#print axioms affine_potential_criterion
#print axioms weighted_affine_criterion
end Erdos406AffinePotential
