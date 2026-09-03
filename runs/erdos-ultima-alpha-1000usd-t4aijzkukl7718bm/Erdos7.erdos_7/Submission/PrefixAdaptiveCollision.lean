import Submission.ArithmeticReduction

/-! Prefix-dependent digit permutations strengthen the collision condition
in a minimal-period odd cover. This is a necessary condition, not a solution
of the odd covering-system conjecture. -/
namespace Erdos7PrefixAdaptiveCollision
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The digits strictly below a selected position. -/
def lowerPrefix {α : Type*} {n : ℕ} (t : Fin n) (x : Fin n → α) : Fin t.val → α :=
  fun j => x ⟨j.val, j.isLt.trans t.isLt⟩

/-- Swap a prefix-dependent chosen digit with a fixed default. -/
def twist {α : Type*} [DecidableEq α] {n : ℕ} (t : Fin n) (z : α)
    (f : (Fin t.val → α) → α) (x : Fin n → α) : Fin n → α :=
  Function.update x t (Equiv.swap (f (lowerPrefix t x)) z (x t))

@[simp] lemma twist_self {α : Type*} [DecidableEq α] {n : ℕ} (t : Fin n) (z : α)
    (f : (Fin t.val → α) → α) (x : Fin n → α) :
    twist t z f x t = Equiv.swap (f (lowerPrefix t x)) z (x t) := by
  simp [twist]

lemma twist_of_ne {α : Type*} [DecidableEq α] {n : ℕ} (t j : Fin n) (z : α)
    (f : (Fin t.val → α) → α) (x : Fin n → α) (hj : j ≠ t) : twist t z f x j = x j := by
  simp [twist,hj]

@[simp] lemma lowerPrefix_twist {α : Type*} [DecidableEq α] {n : ℕ} (t : Fin n) (z : α)
    (f : (Fin t.val → α) → α) (x : Fin n → α) :
    lowerPrefix t (twist t z f x) = lowerPrefix t x := by
  funext j
  apply twist_of_ne
  intro h
  have hh := congrArg Fin.val h
  change j.val = t.val at hh
  have hj := j.isLt
  omega

@[simp] lemma twist_involutive {α : Type*} [DecidableEq α] {n : ℕ} (t : Fin n) (z : α)
    (f : (Fin t.val → α) → α) (x : Fin n → α) : twist t z f (twist t z f x) = x := by
  funext j
  by_cases hj : j = t
  · subst j
    simp only [twist_self, lowerPrefix_twist, Equiv.swap_apply_self]
  · rw [twist_of_ne _ _ _ _ _ hj, twist_of_ne _ _ _ _ _ hj]

/-- The permutation respects every prefix length, including lengths crossing
its selected position. Its choice depends only on the lower prefix. -/
lemma twist_prefix_agreement {α : Type*} [DecidableEq α] {n : ℕ}
    (t : Fin n) (z : α) (f : (Fin t.val → α) → α) (x a : Fin n → α) (e : ℕ)
    (hmatch : ∀ j : Fin n, j.val < e → x j = a j) :
    ∀ j : Fin n, j.val < e → twist t z f x j = twist t z f a j := by
  intro j hj
  by_cases hjt : j = t
  · subst j
    have he : lowerPrefix t x = lowerPrefix t a := by
      funext k
      exact hmatch ⟨k.val,k.isLt.trans t.isLt⟩ (k.isLt.trans hj)
    simp only [twist_self,he,hmatch t hj]
  · rw [twist_of_ne _ _ _ _ _ hjt,twist_of_ne _ _ _ _ _ hjt]
    exact hmatch j hj

/-- A prefix-dependent permutation of one digit changes residues but preserves
all moduli and the covering property. -/
theorem residue_twist_cover {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hcp : Pairwise (Function.onFun Nat.Coprime p)) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (i₀ : ι) (t : Fin (E i₀)) (f : (Fin t.val → Fin (p i₀)) → Fin (p i₀)) :
    ∃ b : κ → ℤ,
      (∀ k, zmodDigits (p i₀) (E i₀) (b k) =
        twist t 0 f (zmodDigits (p i₀) (E i₀) (a k))) ∧
      ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-b k := by
  classical
  let A (k : κ) (i : ι) := zmodDigits (p i) (E i) (a k)
  let B (k : κ) := Function.update (A k) i₀ (twist t 0 f (A k i₀))
  choose b hb using fun k => exists_integer_with_digits p E hp hcp (B k)
  refine ⟨b,fun k => ?_,fun x => ?_⟩
  · simpa only [B,Function.update_self] using hb k i₀
  · let X (i : ι) := zmodDigits (p i) (E i) (x : ZMod (p i ^ E i))
    let Y := Function.update X i₀ (twist t 0 f (X i₀))
    obtain ⟨z,hz⟩ := exists_integer_with_digits p E hp hcp Y
    obtain ⟨k,hk⟩ := hc z
    have hkd := (divisor_product_iff_digits p E (e k) (he k) hcp z (a k)).mp hk
    refine ⟨k,(divisor_product_iff_digits p E (e k) (he k) hcp x (b k)).mpr ?_⟩
    intro i j hj
    rw [hb]
    by_cases hi : i = i₀
    · subst i
      have hmatch : ∀ l : Fin (E i₀), l.val < e k i₀ → twist t 0 f (X i₀) l = A k i₀ l := by
        intro l hl
        have hh := hkd i₀ l hl
        rw [hz] at hh
        simpa only [Y,Function.update_self] using hh
      have hh := twist_prefix_agreement t 0 f (twist t 0 f (X i₀)) (A k i₀) (e k i₀) hmatch j hj
      rw [twist_involutive] at hh
      simpa only [B,Function.update_self] using hh
    · have hh := hkd i j hj
      rw [hz] at hh
      simpa only [Y,B,Function.update_of_ne hi] using hh

/-- Every prefix-dependent choice of a digit forces an adjacent-level
collision or a unit in a period-minimal odd cover. -/
theorem minimal_period_adaptive_collision {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (t : Fin (E i₀)) (f : (Fin t.val → Fin (p i₀)) → Fin (p i₀)) :
    ∃ k, e k i₀ = t.val+1 ∧
      zmodDigits (p i₀) (E i₀) (a k) t =
        f (lowerPrefix t (zmodDigits (p i₀) (E i₀) (a k))) ∧
      ((∀ i, eraseExponent i₀ t.val (e k) i = 0) ∨
        ∃ l, e l i₀ = t.val ∧ eraseExponent i₀ t.val (e k) = e l) := by
  classical
  have hcp : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  obtain ⟨b,hb,hbc⟩ := residue_twist_cover p E (fun i => (hp i).1.pos) hcp e he a hc i₀ t f
  obtain ⟨k,hk,hkr,hcoll⟩ := minimal_period_every_digit_collision p E hp hpi e he hei he0 b hbc
    K hcard hmin i₀ t 0
  rw [hb,twist_self,Equiv.swap_apply_eq_iff,Equiv.swap_apply_right] at hkr
  exact ⟨k,hk,hkr,hcoll⟩

/-- If every choice function hits a marked pair, one first coordinate has
all second-coordinate values marked. No finiteness assumption is needed. -/
theorem diagonal_support {X Y I : Type*} (pref : I → X) (digit : I → Y) (B : I → Prop)
    (h : ∀ f : X → Y, ∃ i, B i ∧ digit i = f (pref i)) :
    ∃ x, ∀ y, ∃ i, B i ∧ pref i = x ∧ digit i = y := by
  classical
  by_contra! hn
  choose f hf using hn
  obtain ⟨i,hi,hif⟩ := h f
  exact hf (pref i) i hi rfl hif

/-- At every digit level, all digit values occur under ONE common lower
prefix among the adjacent-collision/unit witnesses. -/
theorem minimal_period_shared_prefix_collision {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (t : Fin (E i₀)) :
    ∃ u : Fin t.val → Fin (p i₀), ∀ r : Fin (p i₀), ∃ k,
      e k i₀ = t.val+1 ∧ lowerPrefix t (zmodDigits (p i₀) (E i₀) (a k)) = u ∧
      zmodDigits (p i₀) (E i₀) (a k) t = r ∧
      ((∀ i, eraseExponent i₀ t.val (e k) i = 0) ∨
        ∃ l, e l i₀ = t.val ∧ eraseExponent i₀ t.val (e k) = e l) := by
  let B (k : κ) := e k i₀ = t.val+1 ∧
      ((∀ i, eraseExponent i₀ t.val (e k) i = 0) ∨
        ∃ l, e l i₀ = t.val ∧ eraseExponent i₀ t.val (e k) = e l)
  have hh := diagonal_support (fun k => lowerPrefix t (zmodDigits (p i₀) (E i₀) (a k)))
    (fun k => zmodDigits (p i₀) (E i₀) (a k) t) B (by
      intro f
      obtain ⟨k,hk,hf,hb⟩ := minimal_period_adaptive_collision p E hp hpi e he hei he0 a hc
        K hcard hmin i₀ t f
      exact ⟨k,⟨hk,hb⟩,hf⟩)
  obtain ⟨u,hu⟩ := hh
  refine ⟨u,fun r => ?_⟩
  obtain ⟨k,hk,hku,hkr⟩ := hu r
  exact ⟨k,hk.1,hku,hkr,hk.2⟩

/-- At a positive digit position, the unit exception is impossible. There
are injectively indexed upper/lower pairs, with all upper residues sharing
the same lower prefix and realizing every next digit. -/
theorem minimal_period_shared_prefix_pairs {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (t : Fin (E i₀)) (ht : 0 < t.val) :
    ∃ (u : Fin t.val → Fin (p i₀)) (k l : Fin (p i₀) → κ),
      Function.Injective k ∧ Function.Injective l ∧
      ∀ r, e (k r) i₀ = t.val+1 ∧ e (l r) i₀ = t.val ∧
        eraseExponent i₀ t.val (e (k r)) = e (l r) ∧
        lowerPrefix t (zmodDigits (p i₀) (E i₀) (a (k r))) = u ∧
        zmodDigits (p i₀) (E i₀) (a (k r)) t = r := by
  classical
  obtain ⟨u,hu⟩ := minimal_period_shared_prefix_collision p E hp hpi e he hei he0 a hc
    K hcard hmin i₀ t
  have hpairs (r : Fin (p i₀)) : ∃ k l, e k i₀ = t.val+1 ∧ e l i₀ = t.val ∧
      eraseExponent i₀ t.val (e k) = e l ∧
      lowerPrefix t (zmodDigits (p i₀) (E i₀) (a k)) = u ∧
      zmodDigits (p i₀) (E i₀) (a k) t = r := by
    obtain ⟨k,hk,hku,hkr,hunit | ⟨l,hl,hkl⟩⟩ := hu r
    · have hh := hunit i₀
      rw [eraseExponent_self,eraseLevel,if_neg (by omega),hk] at hh
      omega
    · exact ⟨k,l,hk,hl,hkl,hku,hkr⟩
  choose k l hk hl hkl hku hkr using hpairs
  have hki : Function.Injective k := by
    intro r s hrs
    have hh := congrArg (fun k => zmodDigits (p i₀) (E i₀) (a k) t) hrs
    simpa only [hkr] using hh
  have hli : Function.Injective l := by
    intro r s hrs
    apply hki
    apply hei
    have hh : eraseExponent i₀ t.val (e (k r)) = eraseExponent i₀ t.val (e (k s)) := by
      rw [hkl r,hkl s,hrs]
    funext i
    by_cases hi : i = i₀
    · subst i
      rw [hk r,hk s]
    · have hhi := congrFun hh i
      simpa only [eraseExponent_of_ne i₀ t.val (e (k r)) hi,
        eraseExponent_of_ne i₀ t.val (e (k s)) hi] using hhi
  exact ⟨u,k,l,hki,hli,fun r => ⟨hk r,hl r,hkl r,hku r,hkr r⟩⟩

#print axioms residue_twist_cover
#print axioms minimal_period_adaptive_collision
#print axioms minimal_period_shared_prefix_collision
#print axioms minimal_period_shared_prefix_pairs
end Erdos7PrefixAdaptiveCollision
