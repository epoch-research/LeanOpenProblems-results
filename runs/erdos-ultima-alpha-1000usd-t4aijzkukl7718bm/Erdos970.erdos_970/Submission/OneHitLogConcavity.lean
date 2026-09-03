import FormalConjecturesUtil

/-! Log-concavity for a finite one-hit occupancy model. Each modulus is at least
all population sizes under consideration. This is not a general sieve theorem. -/
namespace Erdos970.OneHitLogConcavity

noncomputable def update (p : ℕ) (f : ℕ → ℝ) (s : ℕ) : ℝ :=
  (((p : ℝ) - s) * f s + s * f (s-1)) / p

structure Shape (f : ℕ → ℝ) (M : ℕ) : Prop where
  zero : f 0 = 1
  nonneg : ∀ s ≤ M, 0 ≤ f s
  decreasing : ∀ s < M, f (s+1) ≤ f s
  concave : ∀ s, 0 < s → s < M → f (s-1) * f (s+1) ≤ f s ^ 2

lemma mixed_of_concave (a b c d : ℝ) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hdb : d ≤ b)
    (h1 : a*c ≤ b^2) (h2 : b*d ≤ c^2) : a*d ≤ b*c := by
  by_cases hb0 : b = 0
  · have hd0 : d = 0 := by linarith
    simp [hb0, hd0]
  by_cases hc0 : c = 0
  · have hd0 : d = 0 := by nlinarith
    simp [hc0, hd0]
  have hbc : 0 < b*c := mul_pos (lt_of_le_of_ne hb (Ne.symm hb0))
    (lt_of_le_of_ne hc (Ne.symm hc0))
  have hh := mul_le_mul h1 h2 (mul_nonneg hb hd) (sq_nonneg b)
  nlinarith only [hh, hbc]

lemma update_shape (p M : ℕ) (hp : 0 < p) (hMp : M ≤ p)
    (f : ℕ → ℝ) (hf : Shape f M) : Shape (update p f) M := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  constructor
  · simp [update, hf.zero, hp.ne']
  · intro s hs
    have hsR : (s : ℝ) ≤ p := by exact_mod_cast hs.trans hMp
    exact div_nonneg (add_nonneg (mul_nonneg (by linarith) (hf.nonneg s hs))
      (mul_nonneg (by positivity) (hf.nonneg (s-1) (by omega)))) hpR.le
  · intro s hs
    have h1 := hf.decreasing s hs
    have h2 : (s : ℝ) * (f (s-1) - f s) ≥ 0 := by
      by_cases hs0 : s = 0
      · simp [hs0]
      · have hh := hf.decreasing (s-1) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ s)] at hh
        exact mul_nonneg (by positivity) (by linarith)
    have hsp : (0 : ℝ) ≤ p-s-1 := by
      have hh : (s : ℝ)+1 ≤ p := by exact_mod_cast (show s+1 ≤ p by omega)
      linarith
    have h3 := mul_nonneg hsp (sub_nonneg.mpr h1)
    unfold update
    apply (div_le_div_iff_of_pos_right hpR).mpr
    rw [Nat.add_sub_cancel]
    push_cast
    nlinarith only [h2,h3]
  · intro s hs hMs
    let a := f (s-2)
    let b := f (s-1)
    let c := f s
    let d := f (s+1)
    have hb : 0 ≤ b := hf.nonneg _ (by omega)
    have hc : 0 ≤ c := hf.nonneg _ (by omega)
    have hd : 0 ≤ d := hf.nonneg _ (by omega)
    have hcd : d ≤ c := hf.decreasing s hMs
    have hbc : c ≤ b := by
      have h := hf.decreasing (s-1) (by omega)
      simpa only [Nat.sub_add_cancel hs] using h
    have h1 : a*c ≤ b^2 := by
      by_cases h : s = 1
      · subst s
        dsimp [a,b,c]
        rw [hf.zero]
        simpa only [hf.zero, zero_add, one_mul, one_pow] using hf.decreasing 0 (by omega)
      · have hh := hf.concave (s-1) (by omega) (by omega)
        simpa only [Nat.sub_sub, Nat.sub_add_cancel hs] using hh
    have h2 : b*d ≤ c^2 := hf.concave s hs hMs
    have h3 : a*d ≤ b*c := mixed_of_concave a b c d hb hc hd (hcd.trans hbc) h1 h2
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hsp : (1 : ℝ) ≤ (p : ℝ)-s := by
      have hh : (s : ℝ)+1 ≤ p := by exact_mod_cast (show s+1 ≤ p by omega)
      linarith
    have hA := mul_nonneg (show 0 ≤ ((p : ℝ)-s)^2-1 by nlinarith) (sub_nonneg.mpr h2)
    have hB := mul_nonneg (show 0 ≤ (s : ℝ)^2-1 by nlinarith) (sub_nonneg.mpr h1)
    have hC := mul_nonneg (mul_nonneg (show 0 ≤ (s : ℝ)-1 by linarith)
      (show 0 ≤ (p : ℝ)-s-1 by linarith)) (sub_nonneg.mpr h3)
    have hid : (((p : ℝ)-s)*c+s*b)^2 -
        (((p : ℝ)-s+1)*b+(s-1)*a)*(((p : ℝ)-s-1)*d+(s+1)*c) =
        (((p : ℝ)-s)^2-1)*(c^2-b*d) + ((s : ℝ)^2-1)*(b^2-a*c) +
        ((s : ℝ)-1)*((p : ℝ)-s-1)*(b*c-a*d) + (b-c)^2 := by ring
    have hmain : (((p : ℝ)-s+1)*b+(s-1)*a)*(((p : ℝ)-s-1)*d+(s+1)*c) ≤
        (((p : ℝ)-s)*c+s*b)^2 := by nlinarith only [hid,hA,hB,hC,sq_nonneg (b-c)]
    unfold update
    rw [← mul_div_mul_comm, div_pow, ← sq]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hpR)).mpr
    rw [Nat.cast_sub hs, Nat.sub_sub, Nat.add_sub_cancel]
    push_cast
    convert hmain using 1; dsimp [a,b,c,d]; ring

lemma Shape.antitone {f : ℕ → ℝ} {M : ℕ} (hf : Shape f M)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ M) : f j ≤ f i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih => exact (hf.decreasing j (by omega)).trans (ih (by omega))

lemma Shape.ratio_step {f : ℕ → ℝ} {M : ℕ} (hf : Shape f M)
    (i : ℕ) (hi : i+1 < M) : f (i+2)/f (i+1) ≤ f (i+1)/f i := by
  by_cases h0 : f (i+1) = 0
  · simp only [h0, zero_div, div_zero, le_refl]
  have h1 : 0 < f (i+1) := lt_of_le_of_ne (hf.nonneg _ (by omega)) (Ne.symm h0)
  have h2 : 0 < f i := h1.trans_le (hf.decreasing i (by omega))
  apply (div_le_div_iff₀ h1 h2).mpr
  simpa only [Nat.add_sub_cancel, pow_two, mul_comm] using hf.concave (i+1) (by omega) hi

lemma Shape.ratio_antitone {f : ℕ → ℝ} {M : ℕ} (hf : Shape f M)
    {i j : ℕ} (hij : i ≤ j) (hj : j < M) : f (j+1)/f j ≤ f (i+1)/f i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih => exact (hf.ratio_step j (by omega)).trans (ih (by omega))

lemma Shape.cross {f : ℕ → ℝ} {M : ℕ} (hf : Shape f M)
    {i j : ℕ} (hij : i ≤ j) (hj : j < M) : f (j+1)*f i ≤ f j*f (i+1) := by
  by_cases hj0 : f j = 0
  · have h1 : f (j+1) = 0 := by
      have h := hf.decreasing j hj
      have h' := hf.nonneg (j+1) (by omega)
      linarith
    simp [hj0, h1]
  have hjp : 0 < f j := lt_of_le_of_ne (hf.nonneg _ hj.le) (Ne.symm hj0)
  have hip : 0 < f i := hjp.trans_le (hf.antitone hij hj.le)
  have hh := (div_le_div_iff₀ hjp hip).mp (hf.ratio_antitone hij hj)
  simpa only [mul_comm] using hh

lemma Shape.submultiplicative {f : ℕ → ℝ} {M : ℕ} (hf : Shape f M)
    (a b : ℕ) (hab : a+b ≤ M) : f (a+b) ≤ f a*f b := by
  induction b with
  | zero => simp [hf.zero]
  | succ b ih =>
    by_cases hb0 : f b = 0
    · have h1 := hf.antitone (show b ≤ a+(b+1) by omega) hab
      have h2 := hf.nonneg (a+(b+1)) hab
      have h3 : f (a+(b+1)) = 0 := by linarith
      rw [h3]
      exact mul_nonneg (hf.nonneg a (by omega)) (hf.nonneg (b+1) (by omega))
    have hbp : 0 < f b := lt_of_le_of_ne (hf.nonneg b (by omega)) (Ne.symm hb0)
    have hx := hf.cross (show b ≤ a+b by omega) (show a+b < M by omega)
    have hy := mul_le_mul_of_nonneg_right (ih (by omega)) (hf.nonneg (b+1) (by omega))
    have : f (a+(b+1))*f b ≤ (f a*f (b+1))*f b := by
      rw [show a+(b+1) = a+b+1 by omega]
      nlinarith only [hx,hy]
    exact (mul_le_mul_iff_left₀ hbp).mp this

noncomputable def occupancy : List ℕ → ℕ → ℝ
  | [], s => if s = 0 then 1 else 0
  | p::ps, s => update p (occupancy ps) s

lemma occupancy_shape (ps : List ℕ) (M : ℕ)
    (hp : ∀ p ∈ ps, 0 < p ∧ M ≤ p) : Shape (occupancy ps) M := by
  induction ps with
  | nil =>
    constructor
    · simp [occupancy]
    · intro s hs; simp only [occupancy]; split_ifs <;> norm_num
    · intro s hs; simp [occupancy]; split_ifs <;> norm_num
    · intro s hs hM; simp [occupancy, show s ≠ 0 by omega]
  | cons p ps ih =>
    exact update_shape p M (hp p (by simp)).1 (hp p (by simp)).2 _
      (ih (fun q hq => hp q (by simp [hq])))

theorem occupancy_submultiplicative (ps : List ℕ) (a b : ℕ)
    (hp : ∀ p ∈ ps, 0 < p ∧ a+b ≤ p) :
    occupancy ps (a+b) ≤ occupancy ps a * occupancy ps b :=
  (occupancy_shape ps (a+b) hp).submultiplicative a b le_rfl

#print axioms occupancy_submultiplicative
end Erdos970.OneHitLogConcavity
