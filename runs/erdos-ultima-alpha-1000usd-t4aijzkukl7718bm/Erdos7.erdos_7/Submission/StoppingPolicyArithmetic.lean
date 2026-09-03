import Submission.StoppingPolicyCharacterization
import Submission.StoppingPrefixArithmetic

/-! The prefix closure exactly characterizes collision-free, nonunit predictable
single-digit images of an arithmetic family, even without coverage. -/
namespace Erdos7StoppingPolicyArithmetic
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
open Erdos7AdaptiveDigitRestriction
open Erdos7StoppingDigitRestriction Erdos7StoppingPrefixClosure
open Erdos7StoppingPrefixArithmetic Erdos7StoppingPolicyCharacterization
set_option autoImplicit false
set_option maxHeartbeats 3000000

section Arithmetic
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (i₀ : ι) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (a : κ → ℤ)
    (T : (Fin (E i₀) → Fin (p i₀)) → Fin (E i₀))
    (V : (Fin (E i₀) → Fin (p i₀)) → Fin (p i₀))

def StrictImage : Prop :=
  (∀ k, Erdos7StoppingDigitRestriction.active p E i₀ T V (e k) (a k) →
    ∃ i, eraseExponent i₀ (T (zmodDigits (p i₀) (E i₀) (a k))).val (e k) i ≠ 0) ∧
  ∀ k l,
    Erdos7StoppingDigitRestriction.active p E i₀ T V (e k) (a k) →
    Erdos7StoppingDigitRestriction.active p E i₀ T V (e l) (a l) →
    eraseExponent i₀ (T (zmodDigits (p i₀) (E i₀) (a k))).val (e k) =
      eraseExponent i₀ (T (zmodDigits (p i₀) (E i₀) (a l))).val (e l) → k=l

/-- A strict nonunit image is safe for the exact companion marks. No covering,
primality, or irredundance hypothesis is needed in this direction. -/
theorem strict_image_safe (hT : Predictable T) (hV : PredictableValue T V)
    (hsafe : StrictImage p E i₀ e a T V) : Safe (Block p E i₀ e a) T V := by
  let A (k : κ) := zmodDigits (p i₀) (E i₀) (a k)
  intro x hx
  obtain ⟨k,hshort,hnode,hcolor,hunit | ⟨l,hadj,hother,hlt,hmem⟩⟩ := hx
  · have hpref : Agree (T x).val x (A k) :=
      ((node_eq_iff (A k) x (T x)).mp hnode).symm
    have htk := hT x (A k) hpref
    have hvk := hV x (A k) hpref
    have hk : Erdos7StoppingDigitRestriction.active p E i₀ T V (e k) (a k) := by
      right
      change A k (T (A k)) = V (A k)
      rw [htk,hvk]
      exact hcolor
    obtain ⟨i,hi⟩ := hsafe.1 k hk
    have hh := hunit i
    change eraseExponent i₀ (T x).val (e k) i = 0 at hh
    exact hi ((congrArg (fun t => eraseExponent i₀ t.val (e k) i) htk).trans hh)
  · have hpref : Agree (T x).val x (A k) :=
      ((node_eq_iff (A k) x (T x)).mp hnode).symm
    have htk := hT x (A k) hpref
    have hvk := hV x (A k) hpref
    have hk : Erdos7StoppingDigitRestriction.active p E i₀ T V (e k) (a k) := by
      right
      change A k (T (A k)) = V (A k)
      rw [htk,hvk]
      exact hcolor
    have hlong : e l i₀ ≤ (T (A l)).val :=
      (reached_node_iff T hT (A l) ⟨e l i₀,hlt⟩).mp hmem
    have hl : Erdos7StoppingDigitRestriction.active p E i₀ T V (e l) (a l) := Or.inl hlong
    have hupper : eraseExponent i₀ (T (A k)).val (e k) = e l := by
      funext i
      by_cases hi : i = i₀
      · subst i
        rw [htk,eraseExponent_self]
        change (if e k i₀ ≤ (T x).val then e k i₀ else e k i₀-1) = e l i₀
        have hn : ¬ e k i₀ ≤ (T x).val := Nat.not_le_of_gt hshort
        rw [if_neg hn,hadj]
        omega
      · simpa only [eraseExponent_of_ne _ _ _ hi] using hother i hi
    have hlower := eraseExponent_eq_self i₀ (T (A l)).val (e l) hlong
    have heq : k=l := hsafe.2 k l hk hl (hupper.trans hlower.symm)
    rw [heq] at hadj
    omega

/-- Conversely, exact safety excludes every nontrivial erased-vector
collision and every unit image. -/
theorem safe_strict_image (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (hT : Predictable T) (hSafe : Safe (Block p E i₀ e a) T V) :
    StrictImage p E i₀ e a T V := by
  classical
  let A (k : κ) := zmodDigits (p i₀) (E i₀) (a k)
  let S (k : κ) := T (A k)
  have hpair (k l : κ)
      (hk : Erdos7StoppingDigitRestriction.active p E i₀ T V (e k) (a k))
      (hadj : e k i₀ = e l i₀+1) (hother : ∀ i, i ≠ i₀ → e k i = e l i)
      (hs : (S k).val < e k i₀) (hlong : e l i₀ ≤ (S l).val) : False := by
    have hval : A k (S k) = V (A k) :=
      hk.resolve_left (fun hh => Nat.not_le_of_gt hs hh)
    have hlt : e l i₀ < E i₀ := hlong.trans_lt (S l).isLt
    have hmem : node (A l) ⟨e l i₀,hlt⟩ ∈ Reached T :=
      (reached_node_iff T hT (A l) _).mpr hlong
    exact hSafe (A k) ⟨k,hs,rfl,hval,Or.inr ⟨l,hadj,hother,hlt,hmem⟩⟩
  constructor
  · intro k hk
    by_contra! hz
    have hs : (S k).val < e k i₀ := by
      by_contra! hlow
      have heq := eraseExponent_eq_self i₀ (S k).val (e k) hlow
      obtain ⟨i,hi⟩ := he0 k
      exact hi ((congrFun heq i).symm.trans (hz i))
    have hval : A k (S k) = V (A k) :=
      hk.resolve_left (fun hh => Nat.not_le_of_gt hs hh)
    exact hSafe (A k) ⟨k,hs,rfl,hval,Or.inl hz⟩
  · intro k l hk hl hkl
    rcases erase_eq_cases i₀ (S k).val (S l).val (e k) (e l) hkl with hh | hh | hh
    · exact hei hh
    · exact (hpair k l hk hh.1 hh.2.2.2 hh.2.1 hh.2.2.1).elim
    · exact (hpair l k hl hh.1 hh.2.2.2 hh.2.1 hh.2.2.1).elim

/-- A complete finite criterion for this one-coordinate descent method. It
makes no claim that every odd partial family or cover passes the criterion. -/
theorem exists_strict_image_iff (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i ≠ 0) (hE : 0 < E i₀) :
    (∃ T : (Fin (E i₀) → Fin (p i₀)) → Fin (E i₀),
      ∃ V : (Fin (E i₀) → Fin (p i₀)) → Fin (p i₀),
        Predictable T ∧ PredictableValue T V ∧ StrictImage p E i₀ e a T V) ↔
    ¬ Terminal hE (Block p E i₀ e a) (Frozen hE (Block p E i₀ e a)) := by
  rw [← safe_policy_iff_nonterminal hE (Block p E i₀ e a)
    (fun hBC => block_mono p E i₀ e a hBC)]
  constructor
  · rintro ⟨T,V,hT,hV,hS⟩
    exact ⟨T,V,hT,hV,strict_image_safe p E i₀ e a T V hT hV hS⟩
  · rintro ⟨T,V,hT,hV,hS⟩
    exact ⟨T,V,hT,hV,safe_strict_image p E i₀ e a T V hei he0 hT hS⟩
end Arithmetic

#print axioms strict_image_safe
#print axioms safe_strict_image
#print axioms exists_strict_image_iff
end Erdos7StoppingPolicyArithmetic
