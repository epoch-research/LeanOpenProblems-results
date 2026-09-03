import FormalConjecturesUtil

/-!
# Full Beatty prefixes cannot have near-linear Sidon squares

For each real `α ≥ 1` there is a nontrivial square-sum collision among
`floor (α n)`, with positive indices at most `50000 * α`. This concerns
FULL prefixes only, not arbitrary subsets of a Beatty sequence, and does
not settle Erdős 773.
-/
namespace Erdos773.BeattySquareSidonBound

set_option maxHeartbeats 1000000

/-- An ordered, positive collision and an upper bound for its last index. -/
def Collision (α T : ℝ) : Prop :=
  ∃ a b c d : ℤ, 0 < a ∧ a < b ∧ b < c ∧ c < d ∧ (d : ℝ) ≤ T ∧
    0 < ⌊α * a⌋ ∧ ⌊α * a⌋ < ⌊α * b⌋ ∧ ⌊α * b⌋ < ⌊α * c⌋ ∧
    ⌊α * c⌋ < ⌊α * d⌋ ∧
    ⌊α * a⌋ ^ 2 + ⌊α * d⌋ ^ 2 = ⌊α * b⌋ ^ 2 + ⌊α * c⌋ ^ 2

lemma Collision.mono {α T U : ℝ} (h : Collision α T) (hTU : T ≤ U) :
    Collision α U := by
  obtain ⟨a,b,c,d,ha,hab,hbc,hcd,hd,hr,hrab,hrbc,hrcd,heq⟩ := h
  exact ⟨a,b,c,d,ha,hab,hbc,hcd,hd.trans hTU,hr,hrab,hrbc,hrcd,heq⟩

lemma floor_multiples_above {α e : ℝ} {q p : ℤ}
    (heq : α * q = p + e) (he0 : 0 ≤ e) (he : e ≤ 1/13)
    {k : ℤ} (hk0 : 0 ≤ k) (hk : k ≤ 11) :
    ⌊α * (k*q : ℤ)⌋ = k*p := by
  have hk0R : (0 : ℝ) ≤ k := by exact_mod_cast hk0
  have hkR : (k : ℝ) ≤ 11 := by exact_mod_cast hk
  apply Int.floor_eq_iff.mpr
  push_cast
  have hmul : α * ((k : ℝ)*q) = (k : ℝ)*p+(k : ℝ)*e := by
    nlinarith only [congrArg (fun x : ℝ => (k : ℝ)*x) heq]
  rw [hmul]
  constructor
  · nlinarith only [mul_nonneg hk0R he0]
  · have := mul_le_mul_of_nonneg_left he hk0R
    nlinarith only [this,hkR]

lemma homothetic_collision {α e : ℝ} {q p : ℤ} (hq : 0 < q) (hp : 0 < p)
    (heq : α * q = p + e) (he0 : 0 ≤ e) (he : e ≤ 1/13) :
    Collision α (11*q) := by
  refine ⟨3*q,7*q,9*q,11*q,by omega,by omega,by omega,by omega,?_,?_⟩
  · push_cast; rfl
  rw [floor_multiples_above heq he0 he (by norm_num : (0 : ℤ) ≤ 3) (by norm_num),
    floor_multiples_above heq he0 he (by norm_num : (0 : ℤ) ≤ 7) (by norm_num),
    floor_multiples_above heq he0 he (by norm_num : (0 : ℤ) ≤ 9) (by norm_num),
    floor_multiples_above heq he0 he (by norm_num : (0 : ℤ) ≤ 11) (by norm_num)]
  exact ⟨by omega,by omega,by omega,by omega,by ring⟩

lemma floor_multiples_below {α η : ℝ} {q p : ℤ}
    (heq : α * q = p - η) (hη : 0 < η) (hsmall : 15 * p * η ≤ 1)
    {k : ℤ} (hk0 : 0 < k) (hk : k ≤ 15*p) :
    ⌊α * (q*k : ℤ)⌋ = p*k-1 := by
  have hk0R : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkR : (k : ℝ) ≤ 15*p := by exact_mod_cast hk
  apply Int.floor_eq_iff.mpr
  push_cast
  have hmul : α * ((q : ℝ)*k) = (p : ℝ)*k-(k : ℝ)*η := by
    nlinarith only [congrArg (fun x : ℝ => (k : ℝ)*x) heq]
  rw [hmul]
  constructor
  · have := mul_le_mul_of_nonneg_right hkR hη.le
    linarith only [this,hsmall]
  · nlinarith only [mul_pos hk0R hη]

/-- The shifted-progression identity needed for a negative approximation error. -/
lemma shifted_identity (p : ℤ) :
    (p*(5*p+1)-1)^2+(p*(15*p)-1)^2 =
      (p*(9*p+2)-1)^2+(p*(13*p-1)-1)^2 := by ring

lemma shifted_collision {α η : ℝ} {q p : ℤ} (hq : 0 < q) (hp : 0 < p)
    (heq : α * q = p - η) (hη : 0 < η) (hsmall : 15 * p * η ≤ 1) :
    Collision α (15*p*q) := by
  have hq0 : 0 ≤ q := hq.le
  have hp0 : 0 ≤ p := hp.le
  have h1 : 0 < 5*p+1 := by omega
  have h12 : 5*p+1 < 9*p+2 := by omega
  have h23 : 9*p+2 < 13*p-1 := by omega
  have h34 : 13*p-1 < 15*p := by omega
  refine ⟨q*(5*p+1),q*(9*p+2),q*(13*p-1),q*(15*p),
    mul_pos hq h1,mul_lt_mul_of_pos_left h12 hq,
    mul_lt_mul_of_pos_left h23 hq,mul_lt_mul_of_pos_left h34 hq,?_,?_⟩
  · push_cast; nlinarith only []
  rw [floor_multiples_below heq hη hsmall h1 (by omega),
    floor_multiples_below heq hη hsmall (by omega : 0 < 9*p+2) (by omega),
    floor_multiples_below heq hη hsmall (by omega : 0 < 13*p-1) (by omega),
    floor_multiples_below heq hη hsmall (by omega : 0 < 15*p) le_rfl]
  refine ⟨?_,?_,?_,?_,shifted_identity p⟩
  · nlinarith
  · nlinarith only [mul_lt_mul_of_pos_left h12 hp]
  · nlinarith only [mul_lt_mul_of_pos_left h23 hp]
  · nlinarith only [mul_lt_mul_of_pos_left h34 hp]

/-- Convert a negative error that is not too small into a positive error,
with a multiplier at most `15*p`. Equality at `k*η = 1` is allowed. -/
lemma reverse_negative_error {α η : ℝ} {q p : ℤ} (hp : 0 < p)
    (heq : α * q = p - η) (hη : 0 < η) (hη1 : η ≤ 1/13)
    (hlarge : 1 < 15*p*η) :
    ∃ k m : ℤ, 0 < k ∧ k ≤ 15*p ∧ 0 < m ∧
      ∃ e : ℝ, α * (q*k : ℤ) = m + e ∧ 0 ≤ e ∧ e ≤ 1/13 := by
  let k : ℤ := ⌊1/η⌋
  have hklo : (k : ℝ) ≤ 1/η := Int.floor_le _
  have hkhi : 1/η < (k : ℝ)+1 := Int.lt_floor_add_one _
  have hηinv : (13 : ℝ) ≤ 1/η := (le_div_iff₀ hη).mpr (by linarith)
  have hk13 : (13 : ℤ) ≤ k := Int.le_floor.mpr (by exact_mod_cast hηinv)
  have hk0 : 0 < k := by omega
  have hkR : (k : ℝ) < 15*p := by
    have hbound : 1/η < 15*p := (div_lt_iff₀ hη).mpr (by nlinarith only [hlarge])
    exact hklo.trans_lt hbound
  have hk : k ≤ 15*p := by exact_mod_cast hkR.le
  have hprodlo : (k : ℝ)*η ≤ 1 := (le_div_iff₀ hη).mp hklo
  have hprodhi : 1 < ((k : ℝ)+1)*η := (div_lt_iff₀ hη).mp hkhi
  refine ⟨k,k*p-1,hk0,hk,?_,1-(k : ℝ)*η,?_,by linarith,by linarith⟩
  · nlinarith
  · push_cast
    nlinarith only [congrArg (fun x : ℝ => (k : ℝ)*x) heq]

/-- Every full Beatty prefix of length at least `50000*α` contains
four distinct positive roots with a nontrivial square-sum collision. -/
theorem collision {α : ℝ} (hα : 1 ≤ α) : Collision α (50000*α) := by
  obtain ⟨p,q,hq,hq12,happrox⟩ :=
    Real.exists_int_int_abs_mul_sub_le α (n := 12) (by norm_num)
  norm_num at hq12 happrox
  obtain ⟨herrlo,herrhi⟩ := abs_le.mp happrox
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq12
  have hαq : 1 ≤ α*(q : ℝ) := by nlinarith only [mul_nonneg (sub_nonneg.mpr hα) (sub_nonneg.mpr hq1),hα,hq1]
  have hp : 0 < p := by
    have hpR : (0 : ℝ) < p := by nlinarith only [hαq,herrhi]
    exact_mod_cast hpR
  have hpbound : (p : ℝ) ≤ 2*α*q := by nlinarith only [hαq,herrlo]
  have hpqbound : (p : ℝ)*q ≤ 288*α := by
    have hqq : (q : ℝ)^2 ≤ 144 := by nlinarith only [hq1,hqR]
    have h1 := mul_le_mul_of_nonneg_right hpbound (by linarith : (0 : ℝ) ≤ q)
    have h2 := mul_le_mul_of_nonneg_left hqq (by linarith : (0 : ℝ) ≤ 2*α)
    nlinarith only [h1,h2]
  by_cases he : 0 ≤ α*q-p
  · exact (homothetic_collision hq hp (by ring : α*q = p+(α*q-p)) he
        (by nlinarith only [herrhi])).mono (by nlinarith only [hqR,hα])
  · have hη : 0 < (p : ℝ)-α*q := by linarith only [he]
    have hη1 : (p : ℝ)-α*q ≤ 1/13 := by nlinarith only [herrlo]
    have heq : α*q = p-((p : ℝ)-α*q) := by ring
    by_cases hsmall : 15*p*((p : ℝ)-α*q) ≤ 1
    · exact (shifted_collision hq hp heq hη hsmall).mono (by nlinarith only [hpqbound,hα])
    · obtain ⟨k,m,hk,hkp,hm,e,hrev,he0,he1⟩ :=
        reverse_negative_error hp heq hη hη1 (by linarith only [hsmall])
      have hkR : (k : ℝ) ≤ 15*p := by exact_mod_cast hkp
      have hmul := mul_le_mul_of_nonneg_left hkR (by linarith : (0 : ℝ) ≤ q)
      apply (homothetic_collision (mul_pos hq hk) hm hrev he0 he1).mono
      push_cast
      nlinarith only [hmul,hpqbound,hα]

/-- The collision in natural-number notation, as used in the original conjecture. -/
theorem nat_collision {α : ℝ} (hα : 1 ≤ α) :
    ∃ a b c d : ℕ, 0 < a ∧ a < b ∧ b < c ∧ c < d ∧ (d : ℝ) ≤ 50000*α ∧
      0 < ⌊α * a⌋₊ ∧ ⌊α * a⌋₊ < ⌊α * b⌋₊ ∧ ⌊α * b⌋₊ < ⌊α * c⌋₊ ∧
      ⌊α * c⌋₊ < ⌊α * d⌋₊ ∧
      ⌊α * a⌋₊ ^ 2 + ⌊α * d⌋₊ ^ 2 = ⌊α * b⌋₊ ^ 2 + ⌊α * c⌋₊ ^ 2 := by
  obtain ⟨a,b,c,d,ha,hab,hbc,hcd,hd,hr,hrab,hrbc,hrcd,heq⟩ := collision hα
  have ha0 : 0 ≤ a := by omega
  have hb0 : 0 ≤ b := by omega
  have hc0 : 0 ≤ c := by omega
  have hd0 : 0 ≤ d := by omega
  have hc (i : ℤ) (hi : 0 ≤ i) : (i.toNat : ℝ) = i := by
    exact_mod_cast Int.toNat_of_nonneg hi
  have hf (i : ℤ) (hi : 0 ≤ i) : (⌊α*(i.toNat : ℝ)⌋₊ : ℤ) = ⌊α*i⌋ := by
    rw [hc i hi]
    exact Int.natCast_floor_eq_floor (mul_nonneg (by linarith only [hα]) (by exact_mod_cast hi))
  refine ⟨a.toNat,b.toNat,c.toNat,d.toNat,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast (show (0 : ℤ) < (a.toNat : ℤ) by simpa only [Int.toNat_of_nonneg ha0] using ha)
  · exact_mod_cast (show (a.toNat : ℤ) < (b.toNat : ℤ) by
      simpa only [Int.toNat_of_nonneg ha0,Int.toNat_of_nonneg hb0] using hab)
  · exact_mod_cast (show (b.toNat : ℤ) < (c.toNat : ℤ) by
      simpa only [Int.toNat_of_nonneg hb0,Int.toNat_of_nonneg hc0] using hbc)
  · exact_mod_cast (show (c.toNat : ℤ) < (d.toNat : ℤ) by
      simpa only [Int.toNat_of_nonneg hc0,Int.toNat_of_nonneg hd0] using hcd)
  · simpa only [hc d hd0] using hd
  · have hh : (0 : ℤ) < (⌊α*(a.toNat : ℝ)⌋₊ : ℤ) ∧
        (⌊α*(a.toNat : ℝ)⌋₊ : ℤ) < ⌊α*(b.toNat : ℝ)⌋₊ ∧
        (⌊α*(b.toNat : ℝ)⌋₊ : ℤ) < ⌊α*(c.toNat : ℝ)⌋₊ ∧
        (⌊α*(c.toNat : ℝ)⌋₊ : ℤ) < ⌊α*(d.toNat : ℝ)⌋₊ ∧
        (⌊α*(a.toNat : ℝ)⌋₊ : ℤ)^2+(⌊α*(d.toNat : ℝ)⌋₊ : ℤ)^2 =
          (⌊α*(b.toNat : ℝ)⌋₊ : ℤ)^2+(⌊α*(c.toNat : ℝ)⌋₊ : ℤ)^2 := by
      simpa only [hf a ha0,hf b hb0,hf c hc0,hf d hd0] using
        And.intro hr (And.intro hrab (And.intro hrbc (And.intro hrcd heq)))
    exact_mod_cast hh

/-- The squares in a full Beatty prefix. -/
noncomputable def squares (α : ℝ) (H : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).image (fun n : ℕ => ⌊α*n⌋₊^2)

/-- A full Beatty prefix with Sidon squares has length less than `50000*α`. -/
theorem prefix_length_bound {α : ℝ} {H : ℕ} (hα : 1 ≤ α)
    (hSidon : IsSidon (squares α H : Set ℕ)) : (H : ℝ) < 50000*α := by
  by_contra! hH
  obtain ⟨a,b,c,d,ha,hab,hbc,hcd,hd,_,hrab,hrbc,_,heq⟩ := nat_collision hα
  have hdH : d ≤ H := by exact_mod_cast hd.trans hH
  have hmem {n : ℕ} (hn : 1 ≤ n) (hnH : n ≤ H) : ⌊α*n⌋₊^2 ∈ (squares α H : Set ℕ) := by
    change ⌊α*n⌋₊^2 ∈ (Finset.Icc 1 H).image (fun n : ℕ => ⌊α*n⌋₊^2)
    exact Finset.mem_image.mpr ⟨n,Finset.mem_Icc.mpr ⟨hn,hnH⟩,rfl⟩
  have h := hSidon (⌊α*a⌋₊^2) (hmem (by omega) (by omega))
    (⌊α*b⌋₊^2) (hmem (by omega) (by omega))
    (⌊α*d⌋₊^2) (hmem (by omega) (by omega))
    (⌊α*c⌋₊^2) (hmem (by omega) (by omega)) heq
  rcases h with h | h
  · exact (Nat.pow_lt_pow_left hrab (by norm_num : 2 ≠ 0)).ne h.1
  · exact (Nat.pow_lt_pow_left (hrab.trans hrbc) (by norm_num : 2 ≠ 0)).ne h.1

/-- A uniform square-root ceiling in actual root height, for FULL Beatty prefixes.
It does not bound a Sidon subset selected from a longer prefix. -/
theorem prefix_height_bound {α : ℝ} {H N : ℕ} (hα : 1 ≤ α)
    (hheight : ⌊α*H⌋₊ ≤ N) (hSidon : IsSidon (squares α H : Set ℕ)) :
    (H : ℝ)^2 < 50000*((N : ℝ)+1) := by
  have hH := prefix_length_bound hα hSidon
  have hN : α*H < (N : ℝ)+1 := by
    have hh := Nat.lt_floor_add_one (α*H)
    have hcast : (⌊α*H⌋₊ : ℝ) ≤ N := by exact_mod_cast hheight
    linarith only [hh,hcast]
  have hmul := mul_le_mul_of_nonneg_right hH.le (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
  nlinarith only [hmul,hN]

end Erdos773.BeattySquareSidonBound

#print axioms Erdos773.BeattySquareSidonBound.collision
#print axioms Erdos773.BeattySquareSidonBound.nat_collision
#print axioms Erdos773.BeattySquareSidonBound.prefix_length_bound
#print axioms Erdos773.BeattySquareSidonBound.prefix_height_bound
