import Submission.BinaryEventualCertificates

/-! Sound arithmetic behind universal binary ancestor-family constraints.
No invariant or certificate witness is supplied; this does not settle Erdős 406. -/
namespace Erdos406BinaryAncestors

lemma affine_block (P : ℕ → Prop) (B : ℕ)
    (hstep : ∀ n d : ℕ, B ≤ n → d < 2 → P n → P (3 * n + d))
    (j a n : ℕ) (ha : a < 3 ^ j) (hg : Nat.digits 3 a ⊆ [0, 1])
    (hn : B ≤ n) (hp : P n) : P (3 ^ j * n + a) := by
  induction j generalizing a with
  | zero =>
    have hz : a = 0 := by simpa using ha
    simpa [hz] using hp
  | succ j ih =>
    have hsmall : a / 3 < 3 ^ j := by rw [pow_succ] at ha; omega
    have hd : a % 3 < 2 := by
      by_cases hz : a = 0
      · simp [hz]
      · rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) (by omega : 0 < a)] at hg
        have hh := hg (List.mem_cons_self ..)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        omega
    have hg' : Nat.digits 3 (a / 3) ⊆ [0, 1] := by
      by_cases hz : a = 0
      · simp [hz]
      · rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) (by omega : 0 < a)] at hg
        exact fun d hd => hg (List.mem_cons_of_mem _ hd)
    have hi := ih (a / 3) hsmall hg'
    have hlarge : B ≤ 3 ^ j * n + a / 3 := by
      have hpow : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by decide)
      have hmul : n ≤ 3 ^ j * n := by simpa using Nat.mul_le_mul_right n hpow
      omega
    have hs := hstep _ _ hlarge hd hi
    have he : 3 * (3 ^ j * n + a / 3) + a % 3 = 3 ^ (j + 1) * n + a := by
      rw [pow_succ]
      have hh := Nat.mod_add_div a 3
      nlinarith
    rwa [he] at hs

/-- Closure and a rejected power tail force rejection of every ternary ancestor.
The remainder is a whole good ternary block, not merely a sampled suffix. -/
theorem ancestor_rejected (P : ℕ → Prop) (B C : ℕ)
    (hstep : ∀ n d : ℕ, B ≤ n → d < 2 → P n → P (3 * n + d))
    (htail : ∀ e : ℕ, C ≤ e → ¬ P (2 ^ e))
    (j a n e : ℕ) (ha : a < 3 ^ j) (hg : Nat.digits 3 a ⊆ [0, 1])
    (hn : B ≤ n) (he : C ≤ e) (hid : 3 ^ j * n + a = 2 ^ e) : ¬ P n := by
  intro hp
  have hh := affine_block P B hstep j a n ha hg hn hp
  rw [hid] at hh
  exact htail e he hh

def binaryLoop (seed L b : ℕ) : ℕ → ℕ
  | 0 => seed
  | t + 1 => 2 ^ L * binaryLoop seed L b t + b

lemma binaryLoop_ge (seed L b t : ℕ) : seed ≤ binaryLoop seed L b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hpow : 1 ≤ 2 ^ L := Nat.one_le_pow _ _ (by decide)
    rw [binaryLoop]
    nlinarith

lemma binaryLoop_identity (m a seed L b e : ℕ)
    (hseed : m * seed + a = 2 ^ e) (hloop : m * b + a = a * 2 ^ L)
    (t : ℕ) : m * binaryLoop seed L b t + a = 2 ^ (e + L * t) := by
  have hh : m * binaryLoop seed L b t + a = 2 ^ e * (2 ^ L) ^ t := by
    induction t with
    | zero => simpa [binaryLoop] using hseed
    | succ t ih =>
      rw [binaryLoop, pow_succ]
      have he := congrArg (fun x : ℕ => 2 ^ L * x) ih
      nlinarith
  simpa only [pow_add, pow_mul] using hh

/-- The two exact seed/loop equations certify all repetitions at once.
This justifies a universal regular rejection constraint in certificate synthesis. -/
theorem loop_family_rejected (P : ℕ → Prop) (B C : ℕ)
    (hstep : ∀ n d : ℕ, B ≤ n → d < 2 → P n → P (3 * n + d))
    (htail : ∀ e : ℕ, C ≤ e → ¬ P (2 ^ e))
    (j a seed L b e : ℕ) (ha : a < 3 ^ j) (hg : Nat.digits 3 a ⊆ [0, 1])
    (hn : B ≤ seed) (he : C ≤ e)
    (hseed : 3 ^ j * seed + a = 2 ^ e) (hloop : 3 ^ j * b + a = a * 2 ^ L)
    (t : ℕ) : ¬ P (binaryLoop seed L b t) := by
  exact ancestor_rejected P B C hstep htail j a _ (e + L * t) ha hg
    (hn.trans (binaryLoop_ge seed L b t)) (by omega)
    (binaryLoop_identity (3 ^ j) a seed L b e hseed hloop t)

/-- The generic ancestor theorem applies to the already-proved eventual
certificate interface. The certificate remains an explicit hypothesis. -/
theorem eventual_certificate_ancestor {σ : Type*}
    (K : Erdos406BinaryEventual.Certificate σ)
    (j a n e : ℕ) (ha : a < 3 ^ j) (hg : Nat.digits 3 a ⊆ [0, 1])
    (hn : 2 ^ K.height ≤ n) (he : K.cutoff ≤ e)
    (hid : 3 ^ j * n + a = 2 ^ e) :
    Erdos406BinaryCertificate.evalNat K.D n ∉ K.D.accept := by
  apply ancestor_rejected (fun n => Erdos406BinaryCertificate.evalNat K.D n ∈ K.D.accept)
    (2 ^ K.height) K.cutoff (fun n d hn hd hp => K.affine_closed n d hn hd hp)
    ?_ j a n e ha hg hn he hid
  intro f hf hp
  have ht := K.tail (f - K.cutoff)
  have hh : K.cutoff + (f - K.cutoff) = f := by omega
  rw [hh] at ht
  exact K.tail_reject _ ht hp

#print axioms affine_block
#print axioms ancestor_rejected
#print axioms binaryLoop_identity
#print axioms loop_family_rejected
#print axioms eventual_certificate_ancestor
end Erdos406BinaryAncestors
