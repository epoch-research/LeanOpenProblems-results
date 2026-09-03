import Submission.Investigation

/-! A countermodel to a purely geometric shortcut, not to the conjecture.
The substitution + → +++−, − → −−−+ defines an injective bounded-step lattice
path which escapes fixed-width strips uniformly in both position and direction.
The vertices of this path are not asserted to be Gaussian primes. -/
namespace Erdos952Investigation
namespace UniformEscapeCountermodel

set_option maxHeartbeats 0

def sign (n : ℕ) : ℤ :=
  if hn : n = 0 then 1
  else (if n % 4 = 3 then -1 else 1)*sign (n/4)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

lemma sign_zero : sign 0 = 1 := by rw [sign]; simp

lemma sign_block (n t : ℕ) (ht : t < 4) :
    sign (4*n+t) = (if t = 3 then -1 else 1)*sign n := by
  by_cases hn : 4*n+t = 0
  · have hn0 : n = 0 := by omega
    have ht0 : t = 0 := by omega
    subst n; subst t
    simp [sign_zero]
  · rw [sign,dif_neg hn]
    have hmod : (4*n+t)%4 = t := by omega
    have hdiv : (4*n+t)/4 = n := by omega
    rw [hmod,hdiv]

lemma sign_abs (n : ℕ) : |sign n| = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp [sign_zero]
    · rw [sign,dif_neg hn,abs_mul,ih (n/4) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      split_ifs <;> norm_num

def height : ℕ → ℤ
  | 0 => 0
  | n+1 => height n+sign n

lemma height_add_four (n : ℕ) :
    height (n+4) = height n+sign n+sign (n+1)+sign (n+2)+sign (n+3) := by
  change height n+sign n+sign (n+1)+sign (n+2)+sign (n+3) = _
  rfl

lemma height_four_mul (n : ℕ) : height (4*n) = 2*height n := by
  induction n with
  | zero => simp [height]
  | succ n ih =>
    rw [show 4*(n+1) = 4*n+4 by omega,height_add_four,ih,height]
    have h0 := sign_block n 0 (by decide)
    have h1 := sign_block n 1 (by decide)
    have h2 := sign_block n 2 (by decide)
    have h3 := sign_block n 3 (by decide)
    simp only [Nat.add_zero,ite_true,neg_one_mul] at h0 h1 h2 h3
    norm_num at h0 h1 h2 h3
    rw [h0,h1,h2,h3]
    ring

lemma height_scale (k n : ℕ) : height (4^k*n) = (2 : ℤ)^k*height n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 4^(k+1)*n = 4*(4^k*n) by ring,height_four_mul,ih,pow_succ]
    ring

lemma block_height_difference (k n : ℕ) :
    height (4^k*(n+1))-height (4^k*n) = (2 : ℤ)^k*sign n := by
  rw [height_scale,height_scale,height]
  ring

def path (n : ℕ) : GaussianInt := ⟨n,height n⟩

lemma path_injective : Function.Injective path := by
  intro i j he
  exact Int.natCast_inj.mp (congrArg Zsqrtd.re he)

lemma path_step (n : ℕ) : (path (n+1)-path n).norm = 2 := by
  have hs : (sign n)^2 = 1 := by
    have hh := congrArg (fun z : ℤ => z^2) (sign_abs n)
    simpa using hh
  simp [path,gaussian_norm_sq,height,hs]

def projection (a b : ℝ) (n : ℕ) : ℝ := a*(n : ℝ)+b*(height n : ℝ)

lemma projection_block (k n : ℕ) (a b : ℝ) :
    projection a b (4^k*(n+1))-projection a b (4^k*n) =
      a*(4 : ℝ)^k+b*(2 : ℝ)^k*(sign n : ℝ) := by
  have hh : (height (4^k*(n+1)) : ℝ)-(height (4^k*n) : ℝ) =
      (2 : ℝ)^k*(sign n : ℝ) := by exact_mod_cast block_height_difference k n
  dsimp [projection]
  push_cast
  linear_combination b*hh

/-- Uniform escape from all linear strips. This is a property of the explicit
nonprime path, not an arithmetic conclusion about primes. -/
theorem uniform_projection_escape (B : ℝ) :
    ∃ K : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
      ∃ i ≤ K, B < |projection a b (N+i)-projection a b N| := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (2*B) (by norm_num : (1 : ℝ) < 2)
  let Q : ℕ := 4^k
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨8*Q,?_⟩
  intro N a b hab
  by_contra! hbound
  let m := N/(4*Q)+1
  let j : ℕ → ℕ := fun t => Q*(4*m+t)
  have hindex (t : ℕ) (ht : t ≤ 4) : N ≤ j t ∧ j t ≤ N+8*Q := by
    have hdiv := Nat.mod_add_div N (4*Q)
    have hmod := Nat.mod_lt N (by omega : 0 < 4*Q)
    have hj : j t = (4*Q)*(N/(4*Q))+4*Q+Q*t := by dsimp [j,m]; ring
    have hmul := Nat.mul_le_mul_left Q ht
    rw [hj]
    constructor <;> omega
  have hwindow (t : ℕ) (ht : t ≤ 4) :
      |projection a b (j t)-projection a b N| ≤ B := by
    obtain ⟨hl,hu⟩ := hindex t ht
    have hh := hbound (j t-N) (by omega)
    simpa only [Nat.add_sub_of_le hl] using hh
  have hbetween (s t : ℕ) (hs : s ≤ 4) (ht : t ≤ 4) :
      |projection a b (j s)-projection a b (j t)| ≤ 2*B := by
    have he : projection a b (j s)-projection a b (j t) =
        (projection a b (j s)-projection a b N) +
          -(projection a b (j t)-projection a b N) := by ring
    rw [he]
    have hh := abs_add_le (projection a b (j s)-projection a b N)
      (-(projection a b (j t)-projection a b N))
    rw [abs_neg] at hh
    linarith [hwindow s hs,hwindow t ht]
  have hs0 : sign (4*m) = sign m := by simpa using sign_block m 0 (by decide)
  have hs3 : sign (4*m+3) = -sign m := by simpa using sign_block m 3 (by decide)
  have hplus : |a*(4 : ℝ)^k+b*(2 : ℝ)^k*(sign m : ℝ)| ≤ 2*B := by
    have he : projection a b (j 1)-projection a b (j 0) =
        a*(4 : ℝ)^k+b*(2 : ℝ)^k*(sign m : ℝ) := by
      simpa only [j,Q,Nat.add_zero,hs0] using projection_block k (4*m) a b
    rw [← he]
    exact hbetween 1 0 (by decide) (by decide)
  have hminus : |a*(4 : ℝ)^k-b*(2 : ℝ)^k*(sign m : ℝ)| ≤ 2*B := by
    have he : projection a b (j 4)-projection a b (j 3) =
        a*(4 : ℝ)^k-b*(2 : ℝ)^k*(sign m : ℝ) := by
      have hh := projection_block k (4*m+3) a b
      simpa only [j,Q,show 4*m+3+1 = 4*m+4 by omega,hs3,Int.cast_neg,mul_neg,
        sub_eq_add_neg] using hh
    rw [← he]
    exact hbetween 4 3 (by decide) (by decide)
  have hp := abs_le.mp hplus
  have hm := abs_le.mp hminus
  have ha : |a*(4 : ℝ)^k| ≤ 2*B := abs_le.mpr ⟨by linarith,by linarith⟩
  have hb : |b*(2 : ℝ)^k*(sign m : ℝ)| ≤ 2*B := abs_le.mpr ⟨by linarith,by linarith⟩
  have hsign : |(sign m : ℝ)| = 1 := by exact_mod_cast sign_abs m
  rw [abs_mul,abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 4) k)] at ha
  rw [abs_mul,abs_mul,hsign,mul_one,
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) k)] at hb
  have hpow : (2 : ℝ)^k ≤ (4 : ℝ)^k := by gcongr <;> norm_num
  rcases le_total |a| |b| with hle | hle
  · rw [max_eq_right hle] at hab
    rw [hab,one_mul] at hb
    linarith
  · rw [max_eq_left hle] at hab
    rw [hab,one_mul] at ha
    linarith

theorem path_uniform_escape (B : ℝ) :
    ∃ K : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
      ∃ i ≤ K, B < |a*((path (N+i)-path N).re : ℝ)+b*((path (N+i)-path N).im : ℝ)| := by
  obtain ⟨K,hK⟩ := uniform_projection_escape B
  refine ⟨K,?_⟩
  intro N a b hab
  obtain ⟨i,hi,hh⟩ := hK N a b hab
  refine ⟨i,hi,?_⟩
  convert hh using 1
  congr 1
  simp only [path,Zsqrtd.re_sub,Zsqrtd.im_sub,Int.cast_sub,Int.cast_natCast,projection]
  ring

/-- This explicit path satisfies injectivity, bounded steps and the strongest
uniform strip-escape property established so far for hypothetical prime paths.
It is only a counterexample to the geometric shortcut. -/
theorem geometric_shortcut_counterexample :
    ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      (∀ n, (x (n+1)-x n).norm = 2) ∧
      ∀ B : ℝ, ∃ K : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
        ∃ i ≤ K, B < |a*((x (N+i)-x N).re : ℝ)+b*((x (N+i)-x N).im : ℝ)| :=
  ⟨path,path_injective,path_step,path_uniform_escape⟩

/-- The geometric countermodel fails even the sieve at the rational prime 5. -/
lemma path_hits_every_residue_mod_five (a b : ZMod 5) :
    ∃ n : ℕ, ((path n).re : ZMod 5) = a ∧ ((path n).im : ZMod 5) = b := by
  fin_cases a <;> fin_cases b
  · exact ⟨0, by decide +kernel⟩
  · exact ⟨10, by decide +kernel⟩
  · exact ⟨40, by decide +kernel⟩
  · exact ⟨5, by decide +kernel⟩
  · exact ⟨25, by decide +kernel⟩
  · exact ⟨26, by decide +kernel⟩
  · exact ⟨1, by decide +kernel⟩
  · exact ⟨11, by decide +kernel⟩
  · exact ⟨41, by decide +kernel⟩
  · exact ⟨6, by decide +kernel⟩
  · exact ⟨7, by decide +kernel⟩
  · exact ⟨12, by decide +kernel⟩
  · exact ⟨2, by decide +kernel⟩
  · exact ⟨22, by decide +kernel⟩
  · exact ⟨42, by decide +kernel⟩
  · exact ⟨13, by decide +kernel⟩
  · exact ⟨18, by decide +kernel⟩
  · exact ⟨38, by decide +kernel⟩
  · exact ⟨3, by decide +kernel⟩
  · exact ⟨8, by decide +kernel⟩
  · exact ⟨9, by decide +kernel⟩
  · exact ⟨49, by decide +kernel⟩
  · exact ⟨4, by decide +kernel⟩
  · exact ⟨24, by decide +kernel⟩
  · exact ⟨14, by decide +kernel⟩

theorem path_not_admissible_mod_five :
    ¬ ∃ a b : ZMod 5, ∀ n : ℕ,
      (a+((path n).re : ZMod 5))^2+(b+((path n).im : ZMod 5))^2 ≠ 0 := by
  rintro ⟨a,b,hab⟩
  obtain ⟨n,hr,hi⟩ := path_hits_every_residue_mod_five (-a) (-b)
  exact hab n (by simp [hr,hi])

#print axioms path_not_admissible_mod_five

#print axioms path_step
#print axioms uniform_projection_escape
#print axioms geometric_shortcut_counterexample

end UniformEscapeCountermodel
end Erdos952Investigation
