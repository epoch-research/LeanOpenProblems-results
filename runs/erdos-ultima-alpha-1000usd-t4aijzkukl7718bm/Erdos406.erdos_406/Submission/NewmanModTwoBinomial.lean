import Submission.NewmanReciprocalCandidate

/-! Binary lifts of binomial powers in characteristic two.
This gives a conditional all-degree classification, not a settlement of
Erdős 406. No hypothesis on reduction modulo two is inferred for general
candidate polynomials. -/
namespace Erdos406ModTwoBinomial
open Polynomial Erdos406ReciprocalFlip Erdos406Cyclotomic
  Erdos406ReciprocalCandidate

lemma binary_map_two_injective (P Q : ℤ[X]) (hP : Binary P) (hQ : Binary Q)
    (he : P.map (Int.castRingHom (ZMod 2)) = Q.map (Int.castRingHom (ZMod 2))) :
    P = Q := by
  ext i
  have hi := congrArg (fun f : (ZMod 2)[X] => f.coeff i) he
  simp only [coeff_map] at hi
  rcases hP i with hp | hp <;> rcases hQ i with hq | hq <;>
    simp_all

lemma binary_expand_two (P : ℤ[X]) (hP : Binary P) : Binary (expand ℤ 2 P) := by
  intro i
  rw [coeff_expand (by decide : 0 < 2)]
  split_ifs
  · exact hP _
  · exact Or.inl rfl

lemma binary_interlace (P : ℤ[X]) (hP : Binary P) :
    Binary ((X+1) * expand ℤ 2 P) := by
  intro i
  rw [add_mul, one_mul, coeff_add]
  cases i with
  | zero =>
    simp only [coeff_X_mul_zero, zero_add, coeff_expand (by decide : 0 < 2),
      dvd_zero, if_true, Nat.zero_div]
    exact hP 0
  | succ i =>
    rw [coeff_X_mul]
    simp only [coeff_expand (by decide : 0 < 2), Nat.dvd_iff_mod_eq_zero]
    split_ifs with h₁ h₂
    · omega
    · simpa using hP (i / 2)
    · simpa using hP ((i+1) / 2)
    · simp

lemma expand_binomial_power_two (d : ℕ) :
    expand (ZMod 2) 2 ((X+1)^d) = (X+1)^(2*d) := by
  rw [map_pow, map_add, expand_X, map_one, pow_mul]
  have he : (X+1 : (ZMod 2)[X])^2 = X^2+1 := by
    have hc : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
    calc
      _ = X^2 + 2*X + 1 := by ring
      _ = _ := by rw [hc]; ring
  rw [he]

noncomputable def binomialProduct (L : List ℕ) : ℤ[X] :=
  (L.map (fun j => X^(2^j)+1)).prod

lemma binomialProduct_nil : binomialProduct [] = 1 := rfl

lemma binomialProduct_cons (j : ℕ) (L : List ℕ) :
    binomialProduct (j::L) = (X^(2^j)+1) * binomialProduct L := rfl

lemma expand_binomialProduct (L : List ℕ) :
    expand ℤ 2 (binomialProduct L) = binomialProduct (L.map Nat.succ) := by
  induction L with
  | nil => simp [binomialProduct]
  | cons j L ih =>
    simp only [binomialProduct_cons, map_mul, map_add, map_pow, expand_X, map_one,
      List.map_cons, ih]
    congr 1
    rw [← pow_mul, pow_succ']

/-- The binary lift of a power of X+1 modulo two is a product of the
binomials X^(2^j)+1. This is the polynomial form of the parity pattern in
Pascal's triangle. -/
theorem exists_binary_binomial_lift (d : ℕ) :
    ∃ P : ℤ[X], ∃ L : List ℕ, Binary P ∧
      P.map (Int.castRingHom (ZMod 2)) = (X+1)^d ∧ P = binomialProduct L := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d = 0
    · subst d
      refine ⟨1, [], ?_, by simp, rfl⟩
      intro i
      by_cases hi : i = 0 <;> simp [coeff_one, hi]
    obtain ⟨Q, L, hQ, hmQ, heQ⟩ := ih (d/2) (by omega)
    have hm : (expand ℤ 2 Q).map (Int.castRingHom (ZMod 2)) = (X+1)^(2*(d/2)) := by
      rw [map_expand, hmQ, expand_binomial_power_two]
    by_cases heven : d % 2 = 0
    · refine ⟨expand ℤ 2 Q, L.map Nat.succ, binary_expand_two Q hQ, ?_, ?_⟩
      · convert hm using 1
        congr 1
        omega
      · rw [heQ, expand_binomialProduct]
    · refine ⟨(X+1)*expand ℤ 2 Q, 0::L.map Nat.succ,
        binary_interlace Q hQ, ?_, ?_⟩
      · rw [Polynomial.map_mul, Polynomial.map_add, map_X, Polynomial.map_one, hm,
          ← pow_succ']
        congr 1
        omega
      · rw [binomialProduct_cons, pow_zero, pow_one, heQ, expand_binomialProduct]

/-- No irreducibility or degree bound is needed for this lifting identity. -/
theorem binary_binomial_mod_two_factorization (P : ℤ[X]) (hP : Binary P) (d : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^d) :
    ∃ L : List ℕ, P = binomialProduct L := by
  obtain ⟨Q,L,hQ,hmQ,heQ⟩ := exists_binary_binomial_lift d
  exact ⟨L, (binary_map_two_injective P Q hP hQ (hm.trans hmQ.symm)).trans heQ⟩

lemma binomial_dvd_of_mem (L : List ℕ) (j : ℕ) (hj : j ∈ L) :
    (X^(2^j)+1 : ℤ[X]) ∣ binomialProduct L := by
  exact List.dvd_prod (List.mem_map_of_mem hj)

lemma binomial_index_zero_of_power_value (P : ℤ[X]) (k j : ℕ)
    (he : P.eval 3 = (2 : ℤ)^k) (hd : (X^(2^j)+1 : ℤ[X]) ∣ P) : j = 0 := by
  have hh := eval_dvd (x := (3 : ℤ)) hd
  have hn : (3^(2^j)+1 : ℕ) ∣ 2^k := by
    rw [he] at hh
    norm_num only [eval_add, eval_pow, eval_X, eval_one] at hh
    exact_mod_cast hh
  have hx := Erdos406Structure.three_pow_add_one_dvd_two_pow (by positivity) hn
  have hj : j < 1 := by
    by_contra h
    have ht := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ j)
    norm_num [hx] at ht
  omega

lemma binomialProduct_zero_indices (L : List ℕ) (hL : ∀ j ∈ L, j = 0) :
    binomialProduct L = (X+1)^L.length := by
  induction L with
  | nil => simp [binomialProduct]
  | cons j L ih =>
    rw [binomialProduct_cons, hL j (by simp), pow_zero, pow_one,
      ih (fun i hi => hL i (by simp [hi])), List.length_cons, pow_succ']

/-- A pure-power value excludes all nontrivial binary Pascal patterns.
The reduction-modulo-two hypothesis is essential and is not asserted for
arbitrary candidates. -/
theorem binary_binomial_mod_two_power_classification (P : ℤ[X]) (hP : Binary P)
    (d k : ℕ) (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^d)
    (he : P.eval 3 = (2 : ℤ)^k) : P = 1 ∨ P = X+1 := by
  obtain ⟨L, hL⟩ := binary_binomial_mod_two_factorization P hP d hm
  have hzero : ∀ j ∈ L, j = 0 := by
    intro j hj
    apply binomial_index_zero_of_power_value P k j he
    rw [hL]
    exact binomial_dvd_of_mem L j hj
  rw [binomialProduct_zero_indices L hzero] at hL
  have hc := hP 1
  rw [hL, coeff_X_add_one_pow, Nat.choose_one_right] at hc
  have hlen : L.length = 0 ∨ L.length = 1 := by exact_mod_cast hc
  rcases hlen with hz | ho
  · exact Or.inl (by simpa [hz] using hL)
  · exact Or.inr (by simpa [ho] using hL)

/-- A consequence stated directly for the original candidates. -/
theorem candidate_binomial_mod_two_classification (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1]) (d : ℕ)
    (hm : (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) = (X+1)^d) :
    n = 1 ∨ n = 4 := by
  obtain ⟨k,rfl⟩ := hn
  have he : (digitPoly (Nat.digits 3 (2^k))).eval 3 = (2 : ℤ)^k := by
    rw [digitPoly_eval_three]
    norm_cast
  have hh := binary_binomial_mod_two_power_classification _ (binary_digitPoly _ hg) d k hm he
  rcases hh with hh | hh
  · left
    have hv := congrArg (eval (3 : ℤ)) hh
    rw [digitPoly_eval_three] at hv
    norm_num at hv
    exact_mod_cast hv
  · right
    have hv := congrArg (eval (3 : ℤ)) hh
    rw [digitPoly_eval_three] at hv
    norm_num at hv
    exact_mod_cast hv

/-- A normalized monic polynomial splitting over F₂ is a power of X+1,
since zero cannot be a root and one is the only other field element. -/
lemma split_mod_two_eq_binomial (P : (ZMod 2)[X]) (hm : P.Monic)
    (h0 : P.coeff 0 = 1) (hs : P.Splits) :
    ∃ d : ℕ, P = (X+1)^d := by
  have hroot : ∀ a ∈ P.roots, a = 1 := by
    intro a ha
    have hr := (mem_roots hm.ne_zero).mp ha
    have hc : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    rcases hc with rfl | ha
    · have hz : P.coeff 0 = 0 := by simpa only [IsRoot, ← coeff_zero_eq_eval_zero] using hr
      simp_all
    · exact ha
  refine ⟨P.roots.card, ?_⟩
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm]
  have hmap : P.roots.map (fun a => X-C a) =
      P.roots.map (fun _ => (X+1 : (ZMod 2)[X])) := by
    apply Multiset.map_congr rfl
    intro a ha
    rw [hroot a ha, C_1]
    have hn : (-1 : ZMod 2) = 1 := by decide
    rw [sub_eq_add_neg, ← C_1, ← map_neg, hn]
  rw [hmap, show (fun _ : ZMod 2 => (X+1 : (ZMod 2)[X])) =
    Function.const (ZMod 2) (X+1) from rfl, Multiset.map_const, Multiset.prod_replicate]

/-- Apart from 1 and 4, a candidate's digit polynomial cannot split
completely over the two-element field. -/
theorem candidate_split_mod_two_classification (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1])
    (hs : ((digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2))).Splits) :
    n = 1 ∨ n = 4 := by
  obtain ⟨k,rfl⟩ := hn
  have hm := (Erdos406FactorBridge.candidate_digitPoly_isMonicOfDegree k hg).monic
  have h0 := (Erdos406FactorParity.candidate_monic_factor k hg _ hm (dvd_refl _)).1
  obtain ⟨d,hd⟩ := split_mod_two_eq_binomial _ (hm.map _) (by simp only [coeff_map, h0, map_one]) hs
  exact candidate_binomial_mod_two_classification (2^k) ⟨k,rfl⟩ hg d hd

theorem candidate_mod_two_not_split (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1]) (h1 : n ≠ 1) (h4 : n ≠ 4) :
    ¬ ((digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2))).Splits := by
  intro hs
  exact (candidate_split_mod_two_classification n hn hg hs).elim h1 h4

/-- The splitting hypothesis cannot simply be assumed for all candidates:
the known candidate 256 already fails it. -/
theorem known_256_mod_two_not_split :
    ¬ ((digitPoly (Nat.digits 3 256)).map (Int.castRingHom (ZMod 2))).Splits := by
  exact candidate_mod_two_not_split 256 ⟨8, by norm_num⟩
    (by norm_num [Nat.digits_of_two_le_of_pos]) (by decide) (by decide)

#print axioms candidate_split_mod_two_classification
#print axioms candidate_mod_two_not_split
#print axioms known_256_mod_two_not_split
#print axioms binary_binomial_mod_two_factorization
#print axioms binary_binomial_mod_two_power_classification
#print axioms candidate_binomial_mod_two_classification
end Erdos406ModTwoBinomial
