import Submission.ArithmeticReduction

/-! A simultaneous collision fiber at every digit level of a period-minimal
odd cover. This is a necessary condition, not a settlement of Erdos7. -/
namespace Erdos7CollisionFiber
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
set_option maxHeartbeats 3000000
set_option autoImplicit false

theorem simultaneous_digit_restriction {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hcp : Pairwise (Function.onFun Nat.Coprime p)) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (i₀ : ι) (t : Fin (E i₀)) :
    ∃ b : κ → ℤ,
      (∀ k i, zmodDigits (p i) (E i) (b k) =
        (Function.update (fun j => zmodDigits (p j) (E j) (a k)) i₀
          (deleteDigit t 0 (zmodDigits (p i₀) (E i₀) (a k)))) i) ∧
      ∀ x : ℤ, ∀ r : Fin (p i₀), ∃ k,
      (e k i₀ ≤ t.val ∨ zmodDigits (p i₀) (E i₀) (a k) t = r) ∧
      ((∏ i, p i ^ eraseExponent i₀ t.val (e k) i : ℕ) : ℤ) ∣ x - b k := by
  classical
  let A (k : κ) (i : ι) := zmodDigits (p i) (E i) (a k : ZMod (p i ^ E i))
  let B (k : κ) := Function.update (A k) i₀ (deleteDigit t 0 (A k i₀))
  choose b hb using fun k => exists_integer_with_digits p E hp hcp (B k)
  refine ⟨b, hb, fun x r => ?_⟩
  let X (i : ι) := zmodDigits (p i) (E i) (x : ZMod (p i ^ E i))
  let Y := Function.update X i₀ (insertDigit t r (X i₀))
  obtain ⟨z, hz⟩ := exists_integer_with_digits p E hp hcp Y
  obtain ⟨k, hk⟩ := hc z
  have hkd := (divisor_product_iff_digits p E (e k) (he k) hcp z (a k)).mp hk
  have hmatch : ∀ j : Fin (E i₀), j.val < e k i₀ →
      insertDigit t r (X i₀) j = A k i₀ j := by
    intro j hj
    have hh := hkd i₀ j hj
    rw [hz] at hh
    simpa only [Y, Function.update_self] using hh
  refine ⟨k, ?_, (divisor_product_iff_digits p E (eraseExponent i₀ t.val (e k))
    (fun i => (eraseExponent_le i₀ t.val (e k) i).trans (he k i)) hcp x (b k)).mpr ?_⟩
  · by_cases hkt : e k i₀ ≤ t.val
    · exact Or.inl hkt
    · right
      have hh := hmatch t (by omega)
      rw [insertDigit_self] at hh
      exact hh.symm
  · intro i j hj
    rw [hb]
    by_cases hi : i = i₀
    · subst i
      change X i₀ j = B k i₀ j
      dsimp only [B]
      rw [Function.update_self]
      rw [eraseExponent_self] at hj
      exact prefix_agreement_after_deletion t r 0 (X i₀) (A k i₀) (e k i₀)
        (he k i₀) hmatch j hj
    · have hh := hkd i j (hj.trans_le (eraseExponent_le i₀ t.val (e k) i))
      rw [hz] at hh
      simp only [Y, Function.update_of_ne hi] at hh
      change X i j = B k i j
      simpa only [B, Function.update_of_ne hi] using hh

/-- Any covering by a safe subfamily of digit-deleted classes supplies a
smaller-period strict odd cover. The subset need not arise from a fixed digit. -/
theorem safe_subfamily_smaller_period {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (i₀ : ι) (t : Fin (E i₀)) (active : κ → Prop) (b : κ → ℤ)
    (hb : ∀ x : ℤ, ∃ k, active k ∧
      ((∏ i, p i ^ eraseExponent i₀ t.val (e k) i : ℕ) : ℤ) ∣ x-b k)
    (hunit : ∀ k, active k → ∃ i, eraseExponent i₀ t.val (e k) i ≠ 0)
    (hinj : ∀ k l, active k → active l →
      eraseExponent i₀ t.val (e k) = eraseExponent i₀ t.val (e l) → k = l) :
    ∃ N < ∏ i, p i ^ E i, HasOddArithmeticCover N (Fintype.card κ) := by
  classical
  let E' := Function.update E i₀ (E i₀ - 1)
  let N := ∏ i, p i ^ E' i
  let n (k : {k // active k}) := ∏ i, p i ^ eraseExponent i₀ t.val (e k.val) i
  have hE' (i : ι) : E' i ≤ E i := by
    by_cases hi : i = i₀
    · subst i; simp [E']
    · simp [E', hi]
  have hnewle (k : κ) (i : ι) : eraseExponent i₀ t.val (e k) i ≤ E' i := by
    by_cases hi : i = i₀
    · subst i
      simp only [eraseExponent_self, E', Function.update_self]
      unfold eraseLevel
      have hh := he k i₀
      have ht := t.isLt
      split_ifs <;> omega
    · simpa [E', eraseExponent, hi] using he k i
  have hNpos : 0 < N := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
  have hNlt : N < ∏ i, p i ^ E i := by
    apply Finset.prod_lt_prod (fun i _ => pow_pos (hp i).1.pos _)
      (fun i _ => Nat.pow_le_pow_right (hp i).1.pos (hE' i))
    refine ⟨i₀, Finset.mem_univ _, ?_⟩
    simp only [E', Function.update_self]
    exact Nat.pow_lt_pow_right (hp i₀).1.one_lt (by have := t.isLt; omega)
  refine ⟨N, hNlt, hNpos, {k // active k}, inferInstance, n, (fun k => b k.val),
    ?_, ?_, ?_, ?_, Fintype.card_subtype_le _⟩
  · intro k l hkl
    apply Subtype.ext
    apply hinj k.val l.val k.property l.property
    funext i
    have hh := congrArg (fun m : ℕ => m.factorization (p i)) hkl
    simpa only [n, factorization_prime_power_product p (fun i => (hp i).1) hpi] using hh
  · intro k
    have hnpos : 0 < n k := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
    have hnne : n k ≠ 1 := by
      intro h
      obtain ⟨i, hi⟩ := hunit k.val k.property
      have hh := factorization_prime_power_product p (fun i => (hp i).1) hpi
        (eraseExponent i₀ t.val (e k.val)) i
      change (n k).factorization (p i) = _ at hh
      rw [h, Nat.factorization_one, Finsupp.zero_apply] at hh
      exact hi hh.symm
    refine ⟨by omega, ?_⟩
    exact Finset.prod_induction (fun i => p i ^ eraseExponent i₀ t.val (e k.val) i) Odd
      (fun _ _ ha hb => ha.mul hb) (by norm_num) (fun i _ => (hp i).2.pow)
  · intro x
    obtain ⟨k, hk, hdiv⟩ := hb x
    exact ⟨⟨k, hk⟩, hdiv⟩
  · intro k
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow (p i) (hnewle k.val i))


/-- Upper members of precisely the collisions created by erasing a digit,
including an exceptional class that would become a unit. -/
def Bad {ι κ : Type*} [DecidableEq ι] (e : κ → ι → ℕ) (i₀ : ι) (t : ℕ)
    (k : κ) : Prop :=
  e k i₀ = t+1 ∧ ((∀ i, eraseExponent i₀ t (e k) i = 0) ∨
    ∃ l, e l i₀ = t ∧ eraseExponent i₀ t (e k) = e l)

lemma safe_nonunit {ι κ : Type*} [DecidableEq ι]
    (e : κ → ι → ℕ) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (i₀ : ι) (t : ℕ) (k : κ) (hk : ¬ Bad e i₀ t k) :
    ∃ i, eraseExponent i₀ t (e k) i ≠ 0 := by
  by_contra! hz
  by_cases hkt : e k i₀ ≤ t
  · rw [eraseExponent_eq_self i₀ t (e k) hkt] at hz
    obtain ⟨i,hi⟩ := he0 k
    exact hi (hz i)
  · have hh := hz i₀
    simp only [eraseExponent_self,eraseLevel,if_neg hkt] at hh
    exact hk ⟨by omega,Or.inl hz⟩

lemma safe_injective {ι κ : Type*} [DecidableEq ι]
    (e : κ → ι → ℕ) (hei : Function.Injective e) (i₀ : ι) (t : ℕ)
    (k l : κ) (hk : ¬ Bad e i₀ t k) (hl : ¬ Bad e i₀ t l)
    (heq : eraseExponent i₀ t (e k) = eraseExponent i₀ t (e l)) : k=l := by
  have hcollision (u v : κ) (hu : ¬ e u i₀ ≤ t) (hv : e v i₀ ≤ t)
      (hsafe : ¬ Bad e i₀ t u)
      (heq : eraseExponent i₀ t (e u) = eraseExponent i₀ t (e v)) : False := by
    rw [eraseExponent_eq_self i₀ t (e v) hv] at heq
    have hh := congrFun heq i₀
    simp only [eraseExponent_self,eraseLevel,if_neg hu] at hh
    exact hsafe ⟨by omega,Or.inr ⟨v,by omega,heq⟩⟩
  by_cases hkt : e k i₀ ≤ t <;> by_cases hlt : e l i₀ ≤ t
  · rw [eraseExponent_eq_self i₀ t (e k) hkt,
      eraseExponent_eq_self i₀ t (e l) hlt] at heq
    exact hei heq
  · exact False.elim (hcollision l k hlt hkt hl heq.symm)
  · exact False.elim (hcollision k l hkt hlt hk heq)
  · apply hei
    funext i
    have hh := congrFun heq i
    by_cases hi : i=i₀
    · subst i
      simp only [eraseExponent_self,eraseLevel,if_neg hkt,if_neg hlt] at hh
      omega
    · simpa only [eraseExponent_of_ne i₀ t (e k) hi,
        eraseExponent_of_ne i₀ t (e l) hi] using hh

/-- Deleting the final constrained digit does not change the residue modulo
the new modulus. The same holds if the class never constrained that digit. -/
lemma low_deleted_residue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p E : ι → ℕ) (hcp : Pairwise (Function.onFun Nat.Coprime p))
    [∀ i, NeZero (p i)] (e : ι → ℕ) (he : ∀ i, e i ≤ E i)
    (i₀ : ι) (t : Fin (E i₀)) (a b : ℤ)
    (hb : ∀ i, zmodDigits (p i) (E i) b =
      (Function.update (fun j => zmodDigits (p j) (E j) a) i₀
        (deleteDigit t 0 (zmodDigits (p i₀) (E i₀) a))) i)
    (ht : e i₀ ≤ t.val+1) :
    ((∏ i, p i ^ eraseExponent i₀ t.val e i : ℕ) : ℤ) ∣ b-a := by
  apply (divisor_product_iff_digits p E (eraseExponent i₀ t.val e)
    (fun i => (eraseExponent_le i₀ t.val e i).trans (he i)) hcp b a).mpr
  intro i j hj
  rw [hb]
  by_cases hi : i=i₀
  · subst i
    have hje : j.val < t.val := by
      rw [eraseExponent_self] at hj
      unfold eraseLevel at hj
      split_ifs at hj <;> omega
    simp only [Function.update_self,deleteDigit,if_pos hje]
  · simp only [Function.update_of_ne hi]

/-- At every digit level there is ONE integer that avoids all old lower-level
classes and is simultaneously in the projected collision classes for every
digit value. The upper witnesses therefore have compatible cofactor residues,
not merely a common prefix in the coordinate being deleted. -/
theorem minimal_period_collision_fiber {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (t : Fin (E i₀)) :
    ∃ x : ℤ,
      (∀ l, e l i₀ ≤ t.val → ¬ ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x-a l) ∧
      ∀ r : Fin (p i₀), ∃ k, Bad e i₀ t.val k ∧
        zmodDigits (p i₀) (E i₀) (a k) t = r ∧
        ((∏ i, p i ^ eraseExponent i₀ t.val (e k) i : ℕ) : ℤ) ∣ x-a k := by
  classical
  have hcp : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  obtain ⟨b,hb,hrestrict⟩ := simultaneous_digit_restriction p E
    (fun i => (hp i).1.pos) hcp e he a hc i₀ t
  have hnot : ¬ ∀ x : ℤ, ∃ k, (¬ Bad e i₀ t.val k) ∧
      ((∏ i, p i ^ eraseExponent i₀ t.val (e k) i : ℕ) : ℤ) ∣ x-b k := by
    intro hcover
    obtain ⟨N,hNlt,hN⟩ := safe_subfamily_smaller_period p E hp hpi e he i₀ t
      (fun k => ¬ Bad e i₀ t.val k) b hcover
      (safe_nonunit e he0 i₀ t.val) (safe_injective e hei i₀ t.val)
    apply hmin N hNlt
    obtain ⟨hNpos,ν,fν,n,c,hni,hn,hnc,hnN,hncard⟩ := hN
    exact ⟨hNpos,ν,fν,n,c,hni,hn,hnc,hnN,hncard.trans hcard⟩
  push_neg at hnot
  obtain ⟨x,hx⟩ := hnot
  refine ⟨x,?_,?_⟩
  · intro l hl hxl
    have hs : ¬ Bad e i₀ t.val l := fun h => by have := h.1; omega
    apply hx l hs
    have hba := low_deleted_residue p E hcp (e l) (he l) i₀ t (a l) (b l)
      (hb l) (by omega)
    rw [eraseExponent_eq_self i₀ t.val (e l) hl] at hba ⊢
    have hh := dvd_sub hxl hba
    convert hh using 1 <;> ring
  · intro r
    obtain ⟨k,hactive,hkx⟩ := hrestrict x r
    have hbad : Bad e i₀ t.val k := by
      by_contra hs
      exact hx k hs hkx
    have hkr : zmodDigits (p i₀) (E i₀) (a k) t = r :=
      hactive.resolve_left (by have := hbad.1; omega)
    refine ⟨k,hbad,hkr,?_⟩
    have hba := low_deleted_residue p E hcp (e k) (he k) i₀ t (a k) (b k)
      (hb k) (by have := hbad.1; omega)
    have hh := dvd_add hkx hba
    convert hh using 1 <;> ring

/-- At a positive level the exceptional unit is impossible. All upper/lower
modulus pairs can be chosen injectively, and all upper projected residues
pass through the same integer, which misses every corresponding lower class. -/
theorem minimal_period_collision_pairs {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (t : Fin (E i₀)) (ht : 0 < t.val) :
    ∃ (x : ℤ) (k l : Fin (p i₀) → κ),
      Function.Injective k ∧ Function.Injective l ∧
      ∀ r, e (k r) i₀ = t.val+1 ∧ e (l r) i₀ = t.val ∧
        eraseExponent i₀ t.val (e (k r)) = e (l r) ∧
        zmodDigits (p i₀) (E i₀) (a (k r)) t = r ∧
        ((∏ i, p i ^ e (l r) i : ℕ) : ℤ) ∣ x-a (k r) ∧
        ¬ ((∏ i, p i ^ e (l r) i : ℕ) : ℤ) ∣ x-a (l r) := by
  classical
  obtain ⟨x,hmiss,hfiber⟩ := minimal_period_collision_fiber p E hp hpi e he hei he0
    a hc K hcard hmin i₀ t
  have hpairs (r : Fin (p i₀)) : ∃ k l, e k i₀ = t.val+1 ∧ e l i₀ = t.val ∧
      eraseExponent i₀ t.val (e k) = e l ∧
      zmodDigits (p i₀) (E i₀) (a k) t = r ∧
      ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x-a k := by
    obtain ⟨k,⟨hk,hunit | ⟨l,hl,hkl⟩⟩,hkr,hkx⟩ := hfiber r
    · have hh := hunit i₀
      rw [eraseExponent_self,eraseLevel,if_neg (by omega),hk] at hh
      omega
    · rw [hkl] at hkx
      exact ⟨k,l,hk,hl,hkl,hkr,hkx⟩
  choose k l hk hl hkl hkr hkx using hpairs
  have hki : Function.Injective k := by
    intro r s hrs
    have hh := congrArg (fun k => zmodDigits (p i₀) (E i₀) (a k) t) hrs
    simpa only [hkr] using hh
  have hli : Function.Injective l := by
    intro r s hrs
    apply hki
    apply hei
    have hh : eraseExponent i₀ t.val (e (k r)) =
        eraseExponent i₀ t.val (e (k s)) := by rw [hkl r,hkl s,hrs]
    funext i
    by_cases hi : i=i₀
    · subst i; rw [hk r,hk s]
    · have hh' := congrFun hh i
      simpa only [eraseExponent_of_ne i₀ t.val (e (k r)) hi,
        eraseExponent_of_ne i₀ t.val (e (k s)) hi] using hh'
  exact ⟨x,k,l,hki,hli,fun r => ⟨hk r,hl r,hkl r,hkr r,hkx r,
    hmiss (l r) (by rw [hl r])⟩⟩

#print axioms minimal_period_collision_pairs
#print axioms simultaneous_digit_restriction
#print axioms safe_subfamily_smaller_period
#print axioms minimal_period_collision_fiber
end Erdos7CollisionFiber
