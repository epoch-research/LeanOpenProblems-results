import Submission.CountingExplore

/-! Two distinct equal-length digit loops, with a common accepting context,
force exponential representation peaks. This is a restriction on digit
constructions, not a negation of the unrestricted conjecture. -/
namespace Erdos66DigitLoopPeak
open Filter AdditiveCombinatorics Erdos66Counting
open scoped Topology Classical
set_option maxHeartbeats 1800000

lemma square_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k^2 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ (2 : ℕ) k]
    nlinarith

/-- A global logarithmic envelope excludes exponentially large peaks whose
locations grow at most exponentially in the cube dimension. -/
theorem no_log_limit_of_exponential_peaks (A : Set ℕ) (B D : ℕ) (hB : 1 ≤ B)
    (hpeak : ∀ k : ℕ, ∃ n : ℕ, n ≤ D*B^k ∧ 2^k ≤ sumRep A n) :
    ∀ c : ℝ, ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro c hc
  obtain ⟨K,C,hK,hC,hu⟩ := global_log_upper_bound hc
  have hlogD : 0 ≤ Real.log ((D : ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D; linarith)
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  obtain ⟨k,hk⟩ := exists_nat_gt (max 4 (K+C*Real.log ((D : ℝ)+2)+C*Real.log (B : ℝ)+1))
  have hk4 : 4 ≤ k := by have := (le_max_left _ _).trans_lt hk; exact_mod_cast this.le
  have hk1 : (1 : ℝ) < k := by have := (le_max_left _ _).trans_lt hk; linarith
  have hkbound : K+C*Real.log ((D : ℝ)+2)+C*Real.log (B : ℝ)+1 < k :=
    (le_max_right _ _).trans_lt hk
  obtain ⟨n,hn,hr⟩ := hpeak k
  have hp : (1 : ℝ) ≤ (B : ℝ)^k := one_le_pow₀ (by exact_mod_cast hB)
  have hn' : (n : ℝ)+2 ≤ ((D : ℝ)+2)*(B : ℝ)^k := by
    have hh : (n : ℝ) ≤ D*(B : ℝ)^k := by exact_mod_cast hn
    nlinarith
  have hl : Real.log ((n : ℝ)+2) ≤ Real.log ((D : ℝ)+2)+(k : ℝ)*Real.log B := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ)<(n : ℝ)+2) hn'
    rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hh
    exact hh
  have hh : (k : ℝ)^2 ≤ K+C*(Real.log ((D : ℝ)+2)+(k : ℝ)*Real.log B) := by
    have h₁ : (k : ℝ)^2 ≤ (sumRep A n : ℝ) := by exact_mod_cast (square_le_two_pow k hk4).trans hr
    exact h₁.trans ((hu n).trans (by nlinarith [mul_le_mul_of_nonneg_left hl hC.le]))
  have hnon : 0 ≤ K+C*Real.log ((D : ℝ)+2) := by positivity
  have hmul := mul_lt_mul_of_pos_right hkbound (show (0 : ℝ)<k by linarith)
  have hmul' := mul_le_mul_of_nonneg_left hk1.le hnon
  nlinarith

variable {b : ℕ}

def code (w : List (Fin b)) : ℕ := Nat.ofDigits b (w.map Fin.val)

lemma code_append (u v : List (Fin b)) :
    code (u++v)=code u+b^u.length*code v := by
  simp [code,Nat.ofDigits_append]

lemma code_lt (hb : 1<b) (w : List (Fin b)) : code w < b^w.length := by
  apply (Nat.ofDigits_lt_base_pow_length hb ?_).trans_le (by simp)
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  exact i.isLt

lemma code_inj (hb : 1<b) {u v : List (Fin b)} (hl : u.length=v.length)
    (he : code u=code v) : u=v := by
  have hh : u.map Fin.val=v.map Fin.val := Nat.ofDigits_inj_of_len_eq hb (by simpa using hl)
    (by intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact i.isLt)
    (by intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact i.isLt) he
  exact List.map_injective_iff.mpr Fin.val_injective hh

def blocks (u v : List (Fin b)) : List Bool → List (Fin b)
  | [] => []
  | x::xs => (if x then u else v)++blocks u v xs

lemma blocks_length (u v : List (Fin b)) (hl : u.length=v.length) (xs : List Bool) :
    (blocks u v xs).length=xs.length*u.length := by
  induction xs with
  | nil => simp [blocks]
  | cons x xs ih => cases x <;> simp [blocks,ih,hl,Nat.succ_mul] <;> omega

lemma blocks_injective (hb : 1<b) (u v : List (Fin b)) (hl : u.length=v.length)
    (hne : u≠v) : Function.Injective (blocks u v) := by
  have hpos : 0<u.length := by
    by_contra hh
    have hu : u=[] := List.length_eq_zero_iff.mp (by omega)
    have hv : v=[] := List.length_eq_zero_iff.mp (by omega)
    exact hne (hu.trans hv.symm)
  intro xs ys he
  have hlen : xs.length=ys.length := by
    have hh := congrArg List.length he
    rw [blocks_length _ _ hl,blocks_length _ _ hl] at hh
    exact Nat.eq_of_mul_eq_mul_right hpos hh
  induction xs generalizing ys with
  | nil => simpa using (List.length_eq_zero_iff.mp (by simpa using hlen.symm)).symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hh : (if x then u else v)=(if y then u else v) := by
        have hh := congrArg (List.take u.length) he
        cases x <;> cases y <;> simpa [blocks,←hl] using hh
      have hxy : x=y := by cases x <;> cases y <;> simp_all
      subst y
      have ht : blocks u v xs=blocks u v ys := by
        simpa only [blocks,List.append_cancel_left_eq] using he
      exact congrArg (List.cons x) (ih ht (by simpa using hlen))

def center (u v : List (Fin b)) : ℕ → ℕ
  | 0 => 0
  | k+1 => code u+code v+b^u.length*center u v k

lemma blocks_complement (u v : List (Fin b)) (hl : u.length=v.length) (xs : List Bool) :
    code (blocks u v xs)+code (blocks u v (xs.map Bool.not))=center u v xs.length := by
  induction xs with
  | nil => simp [blocks,center,code]
  | cons x xs ih =>
    cases x <;> simp only [blocks,Bool.false_eq_true,↓reduceIte,List.map_cons,Bool.not_false,
      Bool.not_true,List.length_cons,code_append,center] <;> rw [←hl,←ih] <;> ring

lemma context_code (a u v z : List (Fin b)) (hl : u.length=v.length) (xs : List Bool) :
    code (a++blocks u v xs++z)=code a+b^a.length*
      (code (blocks u v xs)+(b^u.length)^xs.length*code z) := by
  rw [List.append_assoc,code_append,code_append,blocks_length _ _ hl]
  rw [Nat.mul_comm xs.length u.length,pow_mul]

/-- Repetition of either of two distinct equal-length digit blocks between
fixed boundary words excludes every finite logarithmic limit. -/
theorem no_log_limit_of_digit_loops (hb : 1<b) (A : Set ℕ)
    (a u v z : List (Fin b)) (hl : u.length=v.length) (hne : u≠v)
    (hA : ∀ xs : List Bool, code (a++blocks u v xs++z)∈A) :
    ∀ c : ℝ, ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  apply no_log_limit_of_exponential_peaks A (b^u.length) (2*b^(a.length+z.length))
    (Nat.one_le_pow _ _ (by omega))
  intro k
  let f : (Fin k → Bool) → ℕ := fun t ↦ code (a++blocks u v (List.ofFn t)++z)
  let n := 2*code a+b^a.length*(center u v k+2*(b^u.length)^k*code z)
  have hsum (t : Fin k → Bool) : f t+f (fun i ↦ !(t i))=n := by
    have hc := blocks_complement u v hl (List.ofFn t)
    simp only [List.length_ofFn,List.map_ofFn,Function.comp_def] at hc
    dsimp only [f,n]
    rw [context_code _ _ _ _ hl,context_code _ _ _ _ hl]
    simp only [List.length_ofFn]
    rw [←hc]
    ring
  have hinj : Function.Injective f := by
    intro x y he
    have hh := code_inj hb (by simp [blocks_length _ _ hl]) he
    have hh' : blocks u v (List.ofFn x)=blocks u v (List.ofFn y) := by simpa using hh
    exact List.ofFn_injective (blocks_injective hb u v hl hne hh')
  have hrep : 2^k ≤ sumRep A n := by
    rw [sumRep_def]
    have hi := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin k → Bool)))
      (t := (Finset.antidiagonal n).filter (fun p ↦ p.1∈A ∧ p.2∈A))
      (f := fun t ↦ (f t,f (fun i ↦ !(t i))))
      (by
        intro t ht
        change (f t,f (fun i ↦ !(t i))) ∈ (Finset.antidiagonal n).filter (fun p ↦ p.1∈A ∧ p.2∈A)
        exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (hsum t),hA _,hA _⟩)
      (by intro x hx y hy he; exact hinj (congrArg Prod.fst he))
    simpa using hi
  have hn : n ≤ (2*b^(a.length+z.length))*(b^u.length)^k := by
    have h₁ := code_lt hb (a++blocks u v (List.ofFn (fun _ : Fin k ↦ true))++z)
    have h₂ := code_lt hb (a++blocks u v (List.ofFn (fun _ : Fin k ↦ false))++z)
    have hs := hsum (fun _ : Fin k ↦ true)
    simp only [Bool.not_true] at hs
    have hp : b^(a.length+k*u.length+z.length)=b^(a.length+z.length)*(b^u.length)^k := by
      rw [←pow_mul,←pow_add]; congr 1; ring
    simp only [List.length_append,blocks_length _ _ hl,List.length_ofFn] at h₁ h₂
    rw [hp] at h₁ h₂
    change code (a++blocks u v (List.ofFn (fun _ : Fin k ↦ true))++z)+
      code (a++blocks u v (List.ofFn (fun _ : Fin k ↦ false))++z)=n at hs
    calc
      n ≤ 2*(b^(a.length+z.length)*(b^u.length)^k) := by omega
      _ = _ := by ring
  exact ⟨n,hn,hrep⟩

end Erdos66DigitLoopPeak
