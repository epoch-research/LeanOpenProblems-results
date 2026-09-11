import FormalConjectures.Util.ProblemImports

open scoped Real

/--
A364173: The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

namespace Super

open Finset


variable (p : ℕ)

/-- p-free factor -/
def psi (m : ℕ) : ℕ := if p ∣ m then 1 else m

def psi2 (m : ℕ) : ℕ := if p ∣ m then 1 else 2

/-- product of integers in [1, M] not divisible by p -/
def F (M : ℕ) : ℕ := ∏ i ∈ range M, psi p (i+1)

lemma F_zero : F p 0 = 1 := by simp [F]

lemma F_succ (M : ℕ) : F p (M+1) = F p M * psi p (M+1) := by
  simp [F, prod_range_succ]

lemma F_add (A B : ℕ) : F p (A + B) = F p A * ∏ i ∈ range B, psi p (A + 1 + i) := by
  unfold F
  rw [prod_range_add]
  congr 1
  apply prod_congr rfl
  intros
  ring_nf

lemma factorial_eq (hp : 0 < p) (M : ℕ) :
    M.factorial = p^(M/p) * (M/p).factorial * F p M := by
  induction M with
  | zero => simp [F_zero]
  | succ M ih =>
    rw [Nat.factorial_succ, ih, F_succ]
    by_cases h : p ∣ M + 1
    · rw [Nat.succ_div_of_dvd h, psi, if_pos h]
      have hM : M + 1 = p * (M/p + 1) := by
        obtain ⟨c, hc⟩ := h
        have : c = M/p + 1 := by
          rw [← Nat.succ_div_of_dvd ⟨c, hc⟩, hc, Nat.mul_div_cancel_left _ hp]
        rw [hc, this]
      rw [Nat.factorial_succ, pow_succ]
      calc (M+1) * (p^(M/p) * (M/p).factorial * F p M)
          = (p * (M/p+1)) * (p^(M/p) * (M/p).factorial * F p M) := by rw [← hM]
        _ = _ := by ring
    · rw [Nat.succ_div_of_not_dvd h, psi, if_neg h]; ring

lemma factorial_eq' (hp : 0 < p) (M q s : ℕ) (h : M = p * q + s) (hs : s < p) :
    M.factorial = p^q * q.factorial * F p M := by
  have hq : M / p = q := by
    rw [h, Nat.mul_add_div hp, Nat.div_eq_of_lt hs, add_zero]
  rw [factorial_eq p hp M, hq]

lemma psi_coprime (hp : p.Prime) (m : ℕ) : Nat.Coprime (psi p m) p := by
  unfold psi
  split_ifs with h
  · exact Nat.coprime_one_left p
  · exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h)

lemma prod_psi_coprime (hp : p.Prime) (s : Finset ℕ) (f : ℕ → ℕ) :
    Nat.Coprime (∏ i ∈ s, psi p (f i)) p :=
  Nat.Coprime.prod_left (fun i _ => psi_coprime p hp (f i))

lemma F_coprime (hp : p.Prime) (M : ℕ) : Nat.Coprime (F p M) p :=
  prod_psi_coprime p hp _ _

lemma F_pos (M : ℕ) : 0 < F p M := by
  unfold F
  apply prod_pos
  intro i _
  unfold psi
  split_ifs <;> omega

lemma psi_two_mul (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) : psi p (2*m) = psi2 p m * psi p m := by
  unfold psi psi2
  have : p ∣ 2 * m ↔ p ∣ m := by
    constructor
    · intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2) hp2
      · exact h2
    · exact fun h => Dvd.dvd.mul_left h 2
  by_cases h : p ∣ m
  · rw [if_pos (this.2 h), if_pos h, if_pos h]
  · rw [if_neg (mt this.1 h), if_neg h, if_neg h]


/-- inverse of m in ZMod (p^k), or 0 if p ∣ m -/
def v (k : ℕ) (m : ℕ) : ZMod (p^k) := if p ∣ m then 0 else (m : ZMod (p^k))⁻¹

variable {p}

lemma isUnit_cast (hp : p.Prime) (k : ℕ) {m : ℕ} (hm : ¬ p ∣ m) : IsUnit (m : ZMod (p^k)) :=
  (ZMod.isUnit_iff_coprime m (p^k)).2
    (Nat.Coprime.pow_right k (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)))

lemma mul_v (hp : p.Prime) (k : ℕ) (m : ℕ) :
    (m : ZMod (p^k)) * v p k m = if p ∣ m then 0 else 1 := by
  unfold v
  split_ifs with h
  · simp
  · exact ZMod.mul_inv_of_unit _ (isUnit_cast hp k h)

lemma mul_v_of_not_dvd (hp : p.Prime) (k : ℕ) {m : ℕ} (hm : ¬ p ∣ m) :
    (m : ZMod (p^k)) * v p k m = 1 := by
  rw [mul_v hp, if_neg hm]

lemma v_of_dvd (k : ℕ) {m : ℕ} (hm : p ∣ m) : v p k m = 0 := by
  unfold v; rw [if_pos hm]

/-- uniqueness of inverses -/
lemma inv_unique {R : Type*} [CommRing R] {a b c : R} (hb : a * b = 1) (hc : a * c = 1) : b = c := by
  calc b = b * (a * c) := by rw [hc, mul_one]
    _ = (a * b) * c := by ring
    _ = c := by rw [hb, one_mul]

lemma v_mul (hp : p.Prime) (k : ℕ) (a b : ℕ) : v p k (a * b) = v p k a * v p k b := by
  by_cases ha : p ∣ a
  · rw [v_of_dvd k ha, v_of_dvd k (Dvd.dvd.mul_right ha b), zero_mul]
  by_cases hb : p ∣ b
  · rw [v_of_dvd k hb, v_of_dvd k (Dvd.dvd.mul_left hb a), mul_zero]
  have hab : ¬ p ∣ a * b := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact ha h
    · exact hb h
  apply inv_unique (a := ((a * b : ℕ) : ZMod (p^k)))
  · exact mul_v_of_not_dvd hp k hab
  · push_cast
    calc (a : ZMod (p^k)) * b * (v p k a * v p k b) = ((a : ZMod (p^k)) * v p k a) * ((b : ZMod (p^k)) * v p k b) := by ring
      _ = 1 := by rw [mul_v_of_not_dvd hp k ha, mul_v_of_not_dvd hp k hb, one_mul]

/-- key cast lemma: psi (A + m) = psi m * (1 + A * v m) when p ∣ A -/
lemma psi_cast (hp : p.Prime) (k : ℕ) {A : ℕ} (hA : p ∣ A) (m : ℕ) :
    ((psi p (A + m) : ℕ) : ZMod (p^k)) = (psi p m : ZMod (p^k)) * (1 + (A : ZMod (p^k)) * v p k m) := by
  unfold psi
  have hiff : p ∣ A + m ↔ p ∣ m := Nat.dvd_add_right hA
  by_cases hm : p ∣ m
  · rw [if_pos (hiff.2 hm), if_pos hm, v_of_dvd k hm]; simp
  · rw [if_neg (mt hiff.1 hm), if_neg hm]
    push_cast
    have := mul_v_of_not_dvd hp k hm
    linear_combination (-(A : ZMod (p^k))) * this

lemma prod_psi_cast (hp : p.Prime) (k : ℕ) {A : ℕ} (hA : p ∣ A) (g : ℕ → ℕ) (B : ℕ) :
    ((∏ i ∈ range B, psi p (A + g i) : ℕ) : ZMod (p^k)) =
      (∏ i ∈ range B, (psi p (g i) : ZMod (p^k))) * ∏ i ∈ range B, (1 + (A : ZMod (p^k)) * v p k (g i)) := by
  push_cast
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  exact psi_cast hp k hA (g i)

/-- expansion of a product of (1 + X w_i) when X^3 = 0 -/
lemma expand {R : Type*} [CommRing R] (X : R) (hX : X^3 = 0) (w : ℕ → R) (B : ℕ) :
    2 * ∏ i ∈ range B, (1 + X * w i) =
      2 + 2 * X * (∑ i ∈ range B, w i) + X^2 * ((∑ i ∈ range B, w i)^2 - ∑ i ∈ range B, (w i)^2) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [prod_range_succ, sum_range_succ, sum_range_succ, ← mul_assoc, ih]
    linear_combination (w B * ((∑ i ∈ range B, w i)^2 - ∑ i ∈ range B, (w i)^2)) * hX

/-- if X * Σw = 0 and X^2 Σw^2 = 0 and X^3 = 0 then the product is 1 -/
lemma prod_eq_one {R : Type*} [CommRing R] (h2 : IsUnit (2 : R)) (X : R) (hX : X^3 = 0) (w : ℕ → R) (B : ℕ)
    (h1 : X * (∑ i ∈ range B, w i) = 0) (h2' : X^2 * (∑ i ∈ range B, (w i)^2) = 0) :
    ∏ i ∈ range B, (1 + X * w i) = 1 := by
  have := expand X hX w B
  apply h2.mul_left_cancel
  rw [this, mul_one]
  linear_combination (2 + X * (∑ i ∈ range B, w i)) * h1 - h2'



lemma filter_eq_image (hp : p.Prime) (r : ℕ) (hr : 0 < r) [NeZero (p^r)] :
    (range (p^r)).filter (fun i => ¬ p ∣ i) =
      Finset.univ.image (fun u : (ZMod (p^r))ˣ => (u : ZMod (p^r)).val) := by
  ext i
  simp only [mem_filter, mem_range, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨hi, hpi⟩
    have hcop : Nat.Coprime i (p^r) :=
      Nat.Coprime.pow_right r (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpi))
    refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_cast_of_lt hi]
  · rintro ⟨u, rfl⟩
    refine ⟨ZMod.val_lt _, ?_⟩
    intro hdvd
    have hcop := ZMod.val_coe_unit_coprime u
    have := (Nat.Coprime.coprime_dvd_left hdvd hcop).eq_one_of_dvd (dvd_pow_self p hr.ne')
    exact hp.one_lt.ne' this

lemma isUnit_ofNat (hp : p.Prime) (K : ℕ) (c : ℕ) (hc : ¬ p ∣ c) : IsUnit ((c : ℕ) : ZMod (p^K)) :=
  isUnit_cast hp K hc

lemma not_dvd_two (hp5 : 5 ≤ p) : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
lemma not_dvd_three (hp5 : 5 ≤ p) : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega

lemma isUnit_two (hp : p.Prime) (hp5 : 5 ≤ p) (K : ℕ) : IsUnit (2 : ZMod (p^K)) := by
  have := isUnit_cast hp K (m := 2) (not_dvd_two hp5)
  simpa using this

lemma isUnit_three (hp : p.Prime) (hp5 : 5 ≤ p) (K : ℕ) : IsUnit (3 : ZMod (p^K)) := by
  have := isUnit_cast hp K (m := 3) (not_dvd_three hp5)
  simpa using this

lemma sum_v_sq_units (hp : p.Prime) (hp5 : 5 ≤ p) (r : ℕ) (hr : 0 < r) :
    ∑ i ∈ range (p^r), (v p r i)^2 = 0 := by
  haveI : NeZero (p^r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h1 : ∑ i ∈ range (p^r), (v p r i)^2 =
      ∑ u : (ZMod (p^r))ˣ, ((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2 := by
    have : ∀ i ∈ range (p^r), (v p r i)^2 = if ¬ p ∣ i then ((i : ZMod (p^r))⁻¹)^2 else 0 := by
      intro i _; unfold v; split_ifs <;> simp
    rw [sum_congr rfl this, ← sum_filter, filter_eq_image hp r hr, sum_image]
    · apply sum_congr rfl
      intro u _
      rw [ZMod.natCast_zmod_val, ZMod.inv_coe_unit]
    · intro u _ u' _ h
      simp only at h
      apply Units.ext
      rw [← ZMod.natCast_zmod_val (u : ZMod (p^r)), h, ZMod.natCast_zmod_val]
  have h2 : ∑ u : (ZMod (p^r))ˣ, ((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2 =
      ∑ u : (ZMod (p^r))ˣ, (u : ZMod (p^r))^2 :=
    Fintype.sum_equiv (Equiv.inv _) _ _ (fun u => rfl)
  have hcop2 : Nat.Coprime 2 (p^r) :=
    Nat.Coprime.pow_right r (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_two hp5)))
  set g : (ZMod (p^r))ˣ := ZMod.unitOfCoprime 2 hcop2 with hg
  have h3 : ∑ u : (ZMod (p^r))ˣ, ((g * u : (ZMod (p^r))ˣ) : ZMod (p^r))^2 =
      ∑ u : (ZMod (p^r))ˣ, (u : ZMod (p^r))^2 :=
    Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun u => rfl)
  have h4 : ∑ u : (ZMod (p^r))ˣ, ((g * u : (ZMod (p^r))ˣ) : ZMod (p^r))^2 =
      4 * ∑ u : (ZMod (p^r))ˣ, (u : ZMod (p^r))^2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro u _
    rw [Units.val_mul, hg, ZMod.coe_unitOfCoprime]
    push_cast
    ring
  set Z := ∑ u : (ZMod (p^r))ˣ, (u : ZMod (p^r))^2 with hZ
  have h5 : 3 * Z = 0 := by linear_combination h3 - h4
  have h6 : Z = 0 := by
    have := (isUnit_three hp hp5 r).mul_left_cancel (b := Z) (c := 0) (by rw [h5, mul_zero])
    exact this
  rw [h1, h2, h6]

lemma v_add_mul (hp : p.Prime) (r : ℕ) (hr : 0 < r) (a i : ℕ) : v p r (a * p^r + i) = v p r i := by
  unfold v
  have : p ∣ a * p^r + i ↔ p ∣ i := Nat.dvd_add_right (Dvd.dvd.mul_left (dvd_pow_self p hr.ne') a)
  have hc : ((a * p^r + i : ℕ) : ZMod (p^r)) = (i : ZMod (p^r)) := by
    have h0 : ((p^r : ℕ) : ZMod (p^r)) = 0 := ZMod.natCast_self _
    push_cast at h0 ⊢
    rw [h0]; ring
  by_cases h : p ∣ i
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (mt this.1 h), if_neg h, hc]

lemma sum_blocks (hp : p.Prime) (r : ℕ) (hr : 0 < r) (n : ℕ) :
    ∑ m ∈ range (n * p^r), (v p r m)^2 = n • ∑ i ∈ range (p^r), (v p r i)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [add_mul, one_mul, sum_range_add, ih, succ_nsmul]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [v_add_mul hp r hr]

lemma v_castHom (hp : p.Prime) {r K : ℕ} (hrK : r ≤ K) (m : ℕ) :
    ZMod.castHom (pow_dvd_pow p hrK) (ZMod (p^r)) (v p K m) = v p r m := by
  by_cases h : p ∣ m
  · rw [v_of_dvd K h, v_of_dvd r h, map_zero]
  · apply inv_unique (a := (m : ZMod (p^r)))
    · rw [← map_natCast (ZMod.castHom (pow_dvd_pow p hrK) (ZMod (p^r))), ← map_mul,
        mul_v_of_not_dvd hp K h, map_one]
    · exact mul_v_of_not_dvd hp r h

lemma dvd_of_castHom_eq_zero (hp : p.Prime) {r K : ℕ} (hrK : r ≤ K) (x : ZMod (p^K))
    (hx : ZMod.castHom (pow_dvd_pow p hrK) (ZMod (p^r)) x = 0) : (p : ZMod (p^K))^r ∣ x := by
  haveI : NeZero (p^K) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨c, hc⟩ := hx
  refine ⟨(c : ZMod (p^K)), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hc]; push_cast; ring

lemma W2 (hp : p.Prime) (hp5 : 5 ≤ p) {r K : ℕ} (hr : 0 < r) (hrK : r ≤ K) (n : ℕ) :
    (p : ZMod (p^K))^r ∣ ∑ m ∈ range (n * p^r), (v p K m)^2 := by
  apply dvd_of_castHom_eq_zero hp hrK
  rw [map_sum]
  simp_rw [map_pow, v_castHom hp hrK]
  rw [sum_blocks hp r hr, sum_v_sq_units hp hp5 r hr, smul_zero]

lemma v_pair (hp : p.Prime) (K : ℕ) {N m : ℕ} (hN : p ∣ N) (hm : m ≤ N) :
    v p K m + v p K (N - m) = (N : ZMod (p^K)) * (v p K m * v p K (N - m)) := by
  by_cases h : p ∣ m
  · rw [v_of_dvd K h, v_of_dvd K (Nat.dvd_sub hN h)]; simp
  · have h' : ¬ p ∣ N - m := fun h' => h ((Nat.dvd_sub_iff_right hm hN).1 h')
    have e1 := mul_v_of_not_dvd hp K h
    have e2 := mul_v_of_not_dvd hp K h'
    rw [Nat.cast_sub hm] at e2
    linear_combination (-(v p K m)) * e2 + (-(v p K (N-m))) * e1

lemma v_pair' (hp : p.Prime) (K : ℕ) {N m : ℕ} (hN : p ∣ N) (hm : m ≤ N) :
    v p K m * v p K (N - m) = -(v p K m)^2 + (N : ZMod (p^K)) * ((v p K m)^2 * v p K (N - m)) := by
  have := v_pair hp K hN hm
  linear_combination (v p K m) * this

/-- shift: sum over range N of v m equals sum of v (m+1) when p ∣ N -/
lemma sum_v_shift (K : ℕ) {N : ℕ} (hN : p ∣ N) (f : ZMod (p^K) → ZMod (p^K)) (hf : f 0 = 0) :
    ∑ m ∈ range N, f (v p K (m + 1)) = ∑ m ∈ range N, f (v p K m) := by
  have := sum_range_succ' (fun m => f (v p K m)) N
  rw [sum_range_succ] at this
  rw [v_of_dvd K hN, v_of_dvd K (dvd_zero p), hf] at this
  simpa using this.symm

lemma sum_v_reflect (K : ℕ) {N : ℕ} (hN : p ∣ N) (f : ZMod (p^K) → ZMod (p^K)) (hf : f 0 = 0) :
    ∑ m ∈ range N, f (v p K (N - m)) = ∑ m ∈ range N, f (v p K m) := by
  rw [← sum_v_shift K hN f hf]
  have e2 := sum_range_reflect (fun m => f (v p K (m + 1))) N
  rw [← e2]
  apply sum_congr rfl
  intro m hm
  rw [mem_range] at hm
  congr 2; omega

lemma sum_v_reflect' (K : ℕ) {N : ℕ} (hN : p ∣ N) :
    ∑ m ∈ range N, v p K (N - m) = ∑ m ∈ range N, v p K m := by
  have := sum_v_reflect K hN id rfl
  simpa using this

lemma W1 (hp : p.Prime) (hp5 : 5 ≤ p) {r K : ℕ} (hr : 0 < r) (hrK : r ≤ K) (n : ℕ) :
    (p : ZMod (p^K))^(2*r) ∣ ∑ m ∈ range (n * p^r), v p K m := by
  set N := n * p^r with hN
  have hpN : p ∣ N := Dvd.dvd.mul_left (dvd_pow_self p hr.ne') n
  set S := ∑ m ∈ range N, v p K m with hS
  have h2S : 2 * S = -(N : ZMod (p^K)) * (∑ m ∈ range N, (v p K m)^2) +
      (N : ZMod (p^K))^2 * (∑ m ∈ range N, (v p K m)^2 * v p K (N - m)) := by
    have e1 : 2 * S = ∑ m ∈ range N, (v p K m + v p K (N - m)) := by
      rw [sum_add_distrib, sum_v_reflect' K hpN, ← hS]; ring
    rw [e1]
    have e2 : ∀ m ∈ range N, v p K m + v p K (N - m) =
        (N : ZMod (p^K)) * (-(v p K m)^2 + (N : ZMod (p^K)) * ((v p K m)^2 * v p K (N - m))) := by
      intro m hm
      rw [mem_range] at hm
      rw [v_pair hp K hpN hm.le, v_pair' hp K hpN hm.le]
    rw [sum_congr rfl e2, ← mul_sum, sum_add_distrib, sum_neg_distrib, ← mul_sum]
    ring
  obtain ⟨c, hc⟩ := W2 hp hp5 hr hrK n
  rw [← hN] at hc
  have hNc : (N : ZMod (p^K)) = n * (p : ZMod (p^K))^r := by rw [hN]; push_cast; ring
  have hdvd : (p : ZMod (p^K))^(2*r) ∣ 2 * S := by
    refine ⟨-(n : ZMod (p^K)) * c + (n : ZMod (p^K))^2 * (∑ m ∈ range N, (v p K m)^2 * v p K (N - m)), ?_⟩
    rw [h2S, hc, hNc]; ring
  exact ((isUnit_two hp hp5 K).dvd_mul_left).1 hdvd


/- ### Block lemma -/

lemma pow_three_r_eq_zero (r : ℕ) : (p : ZMod (p^(3*r)))^(3*r) = 0 := by
  have := ZMod.natCast_self (p^(3*r))
  push_cast at this
  exact this

lemma prod_v_eq_one_block (hp : p.Prime) (hp5 : 5 ≤ p) {r : ℕ} (hr : 0 < r) (M : ℕ) :
    ∏ i ∈ range (p^r), (1 + ((M * p^r : ℕ) : ZMod (p^(3*r))) * v p (3*r) (i+1)) = 1 := by
  have hp3 := pow_three_r_eq_zero (p := p) r
  have hX : (((M * p^r : ℕ) : ZMod (p^(3*r))))^3 = 0 := by
    push_cast
    linear_combination ((M : ZMod (p^(3*r)))^3) * hp3
  have hsum1 : ∑ i ∈ range (p^r), v p (3*r) (i+1) = ∑ m ∈ range (p^r), v p (3*r) m := by
    have := sum_v_shift (p := p) (3*r) (dvd_pow_self p hr.ne') id rfl
    simpa using this
  have hsum2 : ∑ i ∈ range (p^r), (v p (3*r) (i+1))^2 = ∑ m ∈ range (p^r), (v p (3*r) m)^2 := by
    have := sum_v_shift (p := p) (3*r) (dvd_pow_self p hr.ne') (fun x => x^2) (by simp)
    simpa using this
  apply prod_eq_one (isUnit_two hp hp5 _) _ hX
  · obtain ⟨c, hc⟩ := W1 hp hp5 hr (by omega : r ≤ 3*r) 1
    rw [one_mul] at hc
    rw [hsum1, hc]
    push_cast
    linear_combination ((M : ZMod (p^(3*r))) * c) * hp3
  · obtain ⟨c, hc⟩ := W2 hp hp5 hr (by omega : r ≤ 3*r) 1
    rw [one_mul] at hc
    rw [hsum2, hc]
    push_cast
    linear_combination ((M : ZMod (p^(3*r)))^2 * c) * hp3

lemma F_block (hp : p.Prime) (hp5 : 5 ≤ p) {r : ℕ} (hr : 0 < r) (M : ℕ) :
    ((F p (M * p^r) : ℕ) : ZMod (p^(3*r))) = ((F p (p^r) : ℕ) : ZMod (p^(3*r)))^M := by
  induction M with
  | zero => simp [F_zero]
  | succ M ih =>
    rw [add_mul, one_mul, F_add, Nat.cast_mul, ih, pow_succ]
    congr 1
    have : ∀ i, M * p^r + 1 + i = M * p^r + (i + 1) := by intro i; ring
    simp_rw [this]
    rw [prod_psi_cast hp (3*r) (Dvd.dvd.mul_left (dvd_pow_self p hr.ne') M) (fun i => i + 1) (p^r),
      prod_v_eq_one_block hp hp5 hr M, mul_one]
    unfold F; push_cast; rfl


/- ### Odd case: the power of two identity -/

lemma prod_range_two_mul {M : Type*} [CommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∏ m ∈ range (2*k), f m = ∏ i ∈ range k, (f (2*i) * f (2*i+1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1) = 2*k+1+1 by ring, prod_range_succ, prod_range_succ, ih, prod_range_succ, mul_assoc]

lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∑ m ∈ range (2*k), f m = ∑ i ∈ range k, (f (2*i) + f (2*i+1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1) = 2*k+1+1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ, add_assoc]

lemma prod_psi2_eq (k : ℕ) : ∏ i ∈ range k, psi2 p (i+1) = 2^(k - k/p) := by
  unfold psi2
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  have h1 := Nat.card_multiples k p
  have h2 := Finset.card_filter_add_card_filter_not (s := range k) (fun e => p ∣ e + 1)
  rw [card_range] at h2
  omega

lemma two_pow_identity (hp : p.Prime) (hp2 : p ≠ 2) {k k' : ℕ} (hN : 2*k+1 = p*(2*k'+1)) :
    ∏ i ∈ range k, psi p ((2*k+1) + (2*i+1)) = 2^(2*k - 2*k') * ∏ i ∈ range k, psi p (2*i+1) := by
  have e1 : ∏ i ∈ range k, psi p ((2*k+1) + (2*i+1)) =
      (∏ i ∈ range k, psi2 p (k+1+i)) * ∏ i ∈ range k, psi p (k+1+i) := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl; intro i _
    rw [← psi_two_mul p hp hp2]; congr 1; ring
  have e2 : F p (2*k) = (∏ i ∈ range k, psi p (2*i+1)) * ((∏ i ∈ range k, psi2 p (i+1)) * F p k) := by
    unfold F
    rw [prod_range_two_mul, ← prod_mul_distrib, ← prod_mul_distrib]
    apply prod_congr rfl; intro i _
    rw [← psi_two_mul p hp hp2, show 2*i+1+1 = 2*(i+1) by ring]
  have e3 : F p (2*k) = F p k * ∏ i ∈ range k, psi p (k+1+i) := by
    rw [two_mul, F_add]
  have e4 : ∏ i ∈ range (2*k), psi2 p (i+1) =
      (∏ i ∈ range k, psi2 p (i+1)) * ∏ i ∈ range k, psi2 p (k+1+i) := by
    rw [two_mul, prod_range_add]; congr 1; apply prod_congr rfl; intro i _; congr 1; ring
  have e5 : ∏ i ∈ range (2*k), psi2 p (i+1) = 2^(2*k - 2*k') := by
    rw [prod_psi2_eq]; congr 1
    have h' : p*(2*k'+1) = p*(2*k') + p := by ring
    have hpos := hp.pos
    have : 2*k = p*(2*k') + (p-1) := by omega
    rw [this, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega)]
    omega
  have e6 : ∏ i ∈ range k, psi p (k+1+i) =
      (∏ i ∈ range k, psi p (2*i+1)) * ∏ i ∈ range k, psi2 p (i+1) := by
    have hFpos := F_pos p k
    have : F p k * ∏ i ∈ range k, psi p (k+1+i) =
        F p k * ((∏ i ∈ range k, psi p (2*i+1)) * ∏ i ∈ range k, psi2 p (i+1)) := by
      rw [← e3, e2]; ring
    exact Nat.eq_of_mul_eq_mul_left hFpos this
  rw [e1, e6, ← e5, e4]; ring

lemma isUnit_of_coprime (hp : p.Prime) (K : ℕ) {m : ℕ} (hm : Nat.Coprime m p) :
    IsUnit ((m : ℕ) : ZMod (p^K)) :=
  isUnit_cast hp K ((Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.coprime_comm.1 hm))

lemma two_pow_eq_prod (hp : p.Prime) (hp5 : 5 ≤ p) {r : ℕ} (hr : 0 < r) {k k' n : ℕ}
    (hN : 2*k+1 = n*p^r) (hN' : 2*k+1 = p*(2*k'+1)) :
    ∏ i ∈ range k, (1 + ((2*k+1 : ℕ) : ZMod (p^(3*r))) * v p (3*r) (2*i+1)) =
      (2 : ZMod (p^(3*r)))^(2*k - 2*k') := by
  have hp2 : p ≠ 2 := by omega
  have hpN : p ∣ 2*k+1 := by rw [hN']; exact dvd_mul_right p _
  have h := two_pow_identity hp hp2 hN'
  have hc := congrArg (fun m : ℕ => (m : ZMod (p^(3*r)))) h
  simp only at hc
  rw [prod_psi_cast hp (3*r) hpN (fun i => 2*i+1) k] at hc
  push_cast at hc
  have hunit : IsUnit (∏ i ∈ range k, ((psi p (2*i+1) : ℕ) : ZMod (p^(3*r)))) := by
    have := isUnit_of_coprime hp (3*r) (prod_psi_coprime p hp (range k) (fun i => 2*i+1))
    push_cast at this
    exact this
  apply hunit.mul_left_cancel
  push_cast
  rw [hc]; ring

/- ### Odd case: the sums -/

lemma sum_v_odd_split (hp : p.Prime) (K : ℕ) {k : ℕ} (hpN : p ∣ 2*k+1)
    (f : ZMod (p^K) → ZMod (p^K)) (hf : f 0 = 0) :
    ∑ m ∈ range (2*k+1), f (v p K m) =
      ∑ i ∈ range k, f (v p K (2*i+1)) + ∑ i ∈ range k, f (v p K (2*(i+1))) := by
  rw [← sum_v_shift K hpN f hf, sum_range_succ, v_of_dvd K hpN, hf, add_zero, sum_range_two_mul,
    sum_add_distrib]
  congr 1

lemma two_mul_v_two (hp : p.Prime) (hp5 : 5 ≤ p) (K : ℕ) : (2 : ZMod (p^K)) * v p K 2 = 1 := by
  have := mul_v_of_not_dvd hp K (not_dvd_two hp5)
  push_cast at this
  exact this

lemma odd_sums (hp : p.Prime) (hp5 : 5 ≤ p) {r : ℕ} (hr : 0 < r) {k n : ℕ} (hN : 2*k+1 = n*p^r) :
    ((2*k+1 : ℕ) : ZMod (p^(3*r))) *
        (2 * ∑ i ∈ range k, v p (3*r) (2*i+1) + ∑ i ∈ range k, v p (3*r) (i+1)) = 0 ∧
    ((2*k+1 : ℕ) : ZMod (p^(3*r)))^2 * ∑ i ∈ range k, (v p (3*r) (2*i+1))^2 = 0 ∧
    ((2*k+1 : ℕ) : ZMod (p^(3*r)))^2 * ∑ i ∈ range k, (v p (3*r) (i+1))^2 = 0 := by
  set K := 3*r with hK
  have hpN : p ∣ 2*k+1 := by rw [hN]; exact Dvd.dvd.mul_left (dvd_pow_self p hr.ne') n
  have hp3 := pow_three_r_eq_zero (p := p) r
  set x : ZMod (p^K) := ((2*k+1 : ℕ) : ZMod (p^K)) with hxdef
  have hx : x = n * (p : ZMod (p^K))^r := by rw [hxdef, hN]; push_cast; ring
  have hx3 : x^3 = 0 := by
    rw [hx]; linear_combination ((n : ZMod (p^K))^3) * hp3
  have h2v := two_mul_v_two hp hp5 K
  set A := ∑ i ∈ range k, v p K (2*i+1) with hA
  set B := ∑ i ∈ range k, v p K (i+1) with hB
  set A2 := ∑ i ∈ range k, (v p K (2*i+1))^2 with hA2
  set B2 := ∑ i ∈ range k, (v p K (i+1))^2 with hB2
  have e3 : ∑ i ∈ range k, (v p K (2*(i+1)))^2 = (v p K 2)^2 * B2 := by
    rw [hB2, mul_sum]; apply sum_congr rfl; intro i _; rw [v_mul hp]; ring
  have e3' : ∑ i ∈ range k, v p K (2*(i+1)) = v p K 2 * B := by
    rw [hB, mul_sum]; apply sum_congr rfl; intro i _; rw [v_mul hp]
  -- first sum
  have hS1 : ∑ m ∈ range (2*k+1), v p K m = A + v p K 2 * B := by
    have := sum_v_odd_split hp K hpN id rfl
    simp only [id] at this
    rw [this, e3']
  have hS2 : ∑ m ∈ range (2*k+1), (v p K m)^2 = A2 + (v p K 2)^2 * B2 := by
    have := sum_v_odd_split hp K hpN (fun x => x^2) (by simp)
    simp only at this
    rw [this, e3]
  -- reflection for A2
  set C := ∑ i ∈ range k, (-2 * (v p K (2*(i+1)))^2 * v p K (2*k+1 - 2*(i+1)) +
        x * (v p K (2*(i+1)))^2 * (v p K (2*k+1 - 2*(i+1)))^2) with hC
  have hA2' : A2 = (v p K 2)^2 * B2 + x * C := by
    have e1 : A2 = ∑ i ∈ range k, (v p K (2*k+1 - 2*(i+1)))^2 := by
      rw [hA2, ← sum_range_reflect (fun i => (v p K (2*i+1))^2) k]
      apply sum_congr rfl; intro i hi
      rw [mem_range] at hi
      congr 2; omega
    have e2 : ∀ i ∈ range k, (v p K (2*k+1 - 2*(i+1)))^2 = (v p K (2*(i+1)))^2 +
        x * (-2 * (v p K (2*(i+1)))^2 * v p K (2*k+1 - 2*(i+1)) +
        x * (v p K (2*(i+1)))^2 * (v p K (2*k+1 - 2*(i+1)))^2) := by
      intro i hi
      rw [mem_range] at hi
      have hm : 2*(i+1) ≤ 2*k+1 := by omega
      have := v_pair hp K hpN hm
      linear_combination (v p K (2*k+1 - 2*(i+1)) - v p K (2*(i+1)) +
        x * v p K (2*(i+1)) * v p K (2*k+1 - 2*(i+1))) * this
    rw [e1, sum_congr rfl e2, sum_add_distrib, e3, ← mul_sum]
  obtain ⟨c1, hc1⟩ := W1 hp hp5 hr (by omega : r ≤ K) n
  obtain ⟨c2, hc2⟩ := W2 hp hp5 hr (by omega : r ≤ K) n
  rw [← hN] at hc1 hc2
  rw [hS1] at hc1
  rw [hS2] at hc2
  have hB2z : x^2 * B2 = 0 := by
    have hcomb : x^2 * (2 * (v p K 2)^2 * B2) = 0 := by
      have : 2 * (v p K 2)^2 * B2 = (p : ZMod (p^K))^r * c2 - x * C := by
        linear_combination hc2 - hA2'
      rw [this]
      linear_combination (c2 * (p : ZMod (p^K))^r * (x + n * (p : ZMod (p^K))^r)) * hx +
        (c2 * (n : ZMod (p^K))^2) * hp3 - C * hx3
    linear_combination 2 * hcomb - (x^2 * B2 * (2 * v p K 2 + 1)) * h2v
  refine ⟨?_, ?_, hB2z⟩
  · -- x * (2A + B) = 0
    have : 2 * A + B = 2 * (A + v p K 2 * B) := by linear_combination (-B) * h2v
    rw [this, hc1, hx]
    linear_combination (2 * (n : ZMod (p^K)) * c1) * hp3
  · linear_combination ((v p K 2)^2) * hB2z + C * hx3 + x^2 * hA2'


/- ### Core identity -/

lemma core_identity {R : Type*} [CommRing R] (h2 : IsUnit (2:R)) (x : R) (w1 w2 : ℕ → R) (k : ℕ)
    (hx3 : x^3 = 0)
    (h1 : x * (2 * ∑ i ∈ range k, w2 i + ∑ i ∈ range k, w1 i) = 0)
    (h2' : x^2 * ∑ i ∈ range k, (w2 i)^2 = 0) (h3 : x^2 * ∑ i ∈ range k, (w1 i)^2 = 0) :
    ∏ i ∈ range k, (1 + x * w1 i) =
      (∏ i ∈ range k, (1 + x * w2 i))^6 * ∏ i ∈ range k, (1 + (4*x) * w1 i) := by
  have hE1 := expand x hx3 w1 k
  have hE2 := expand x hx3 w2 k
  have hE3 := expand (4*x) (by linear_combination 64 * hx3) w1 k
  set A := ∑ i ∈ range k, w2 i
  set B := ∑ i ∈ range k, w1 i
  set A2 := ∑ i ∈ range k, (w2 i)^2
  set B2 := ∑ i ∈ range k, (w1 i)^2
  set P1 := ∏ i ∈ range k, (1 + x * w1 i)
  set P2 := ∏ i ∈ range k, (1 + x * w2 i)
  set P3 := ∏ i ∈ range k, (1 + (4*x) * w1 i)
  have h1' : x * B = -2 * x * A := by linear_combination h1
  have hy3 : (x*A)^3 = 0 := by linear_combination A^3 * hx3
  have hE1' : 2 * P1 = 2 - 4*(x*A) + 4*(x*A)^2 := by
    linear_combination hE1 + (2 + x*B - 2*x*A) * h1' - h3
  have hE2' : 2 * P2 = 2 + 2*(x*A) + (x*A)^2 := by linear_combination hE2 - h2'
  have hE3' : 2 * P3 = 2 - 16*(x*A) + 64*(x*A)^2 := by
    linear_combination hE3 + (8 + 16*x*B - 32*x*A) * h1' - 16 * h3
  have key : 2^7 * P1 = 2^7 * (P2^6 * P3) := by
    calc 2^7 * P1 = 2^6 * (2 * P1) := by ring
      _ = (2*P2)^6 * (2*P3) := by
          rw [hE1', hE2', hE3']
          linear_combination (-(64*(x*A)^11 + 752*(x*A)^10 + 4418*(x*A)^9 + 16792*(x*A)^8 +
            45584*(x*A)^7 + 92528*(x*A)^6 + 143384*(x*A)^5 + 170176*(x*A)^4 + 152704*(x*A)^3 +
            99968*(x*A)^2 + 44128*(x*A) + 10624)) * hy3
      _ = 2^7 * (P2^6 * P3) := by ring
  exact (h2.pow 7).mul_left_cancel key

/- ### Main lemmas -/

lemma fact_decomp_int (hp : 0 < p) (M q s : ℕ) (h : M = p*q + s) (hs : s < p) :
    ((M.factorial : ℕ) : ℤ) = (p:ℤ)^q * (q.factorial : ℤ) * (F p M : ℤ) := by
  have := factorial_eq' p hp M q s h hs
  exact_mod_cast this

lemma isUnit_F (hp : p.Prime) (K M : ℕ) : IsUnit ((F p M : ℕ) : ZMod (p^K)) :=
  isUnit_of_coprime hp K (F_coprime p hp M)

lemma even_main (hp : p.Prime) (hp5 : 5 ≤ p) {r : ℕ} (hr : 0 < r) (n' : ℕ) (x x' : ℤ)
    (hx : x * ((9*(n'*p^r)).factorial * (8*(n'*p^r)).factorial * (6*(n'*p^r)).factorial *
        (2*(n'*p^r)).factorial : ℕ) =
      ((18*(n'*p^r)).factorial * (4*(n'*p^r)).factorial * (3*(n'*p^r)).factorial : ℕ))
    (hx' : x' * ((9*(n'*p^(r-1))).factorial * (8*(n'*p^(r-1))).factorial *
        (6*(n'*p^(r-1))).factorial * (2*(n'*p^(r-1))).factorial : ℕ) =
      ((18*(n'*p^(r-1))).factorial * (4*(n'*p^(r-1))).factorial * (3*(n'*p^(r-1))).factorial : ℕ)) :
    (x : ZMod (p^(3*r))) = x' := by
  set k' := n' * p^(r-1) with hk'
  have hpr : p^r = p * p^(r-1) := by rw [← pow_succ']; congr 1; omega
  have hk : n' * p^r = p * k' := by
    rw [hk', hpr]; ring
  rw [hk] at hx
  have hd : ∀ c : ℕ, (((c * (p*k')).factorial : ℕ) : ℤ) =
      (p:ℤ)^(c*k') * ((c*k').factorial : ℤ) * (F p (c*(p*k')) : ℤ) := by
    intro c
    exact fact_decomp_int hp.pos _ (c*k') 0 (by ring) hp.pos
  push_cast at hx hx'
  rw [hd 9, hd 8, hd 6, hd 2, hd 18, hd 4, hd 3] at hx
  -- cancel
  have hD : ((p:ℤ)^(25*k') * ((9*k').factorial * (8*k').factorial * (6*k').factorial *
      (2*k').factorial : ℕ)) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    · exact Nat.cast_ne_zero.2 (by positivity)
  have key : (x : ℤ) * (F p (9*(p*k')) * F p (8*(p*k')) * F p (6*(p*k')) * F p (2*(p*k')) : ℕ) =
      x' * (F p (18*(p*k')) * F p (4*(p*k')) * F p (3*(p*k')) : ℕ) := by
    apply mul_left_cancel₀ hD
    push_cast at hx' ⊢
    linear_combination hx - ((p:ℤ)^(25*k') * (F p (18*(p*k')) * F p (4*(p*k')) * F p (3*(p*k')) : ℤ)) * hx'
  -- cast to ZMod
  have key2 := congrArg (fun z : ℤ => (z : ZMod (p^(3*r)))) key
  simp only at key2
  push_cast at key2
  have hF : ∀ c : ℕ, ((F p (c*(p*k')) : ℕ) : ZMod (p^(3*r))) = ((F p (p^r) : ℕ) : ZMod (p^(3*r)))^(c*n') := by
    intro c
    rw [← F_block hp hp5 hr, ← hk]; congr 2; ring
  rw [hF 9, hF 8, hF 6, hF 2, hF 18, hF 4, hF 3] at key2
  have hΦ := isUnit_F hp (3*r) (p^r)
  set Φ : ZMod (p^(3*r)) := ((F p (p^r) : ℕ) : ZMod (p^(3*r))) with hΦdef
  have : (x : ZMod (p^(3*r))) * Φ^(25*n') = x' * Φ^(25*n') := by
    calc (x : ZMod (p^(3*r))) * Φ^(25*n')
        = x * (Φ^(9*n') * Φ^(8*n') * Φ^(6*n') * Φ^(2*n')) := by ring
      _ = x' * (Φ^(18*n') * Φ^(4*n') * Φ^(3*n')) := key2
      _ = x' * Φ^(25*n') := by ring
  exact (hΦ.pow _).mul_right_cancel this


lemma odd_main (hp : p.Prime) (hp5 : 5 ≤ p) {r : ℕ} (hr : 0 < r) {k k' n : ℕ}
    (hN : 2*k+1 = n*p^r) (hN' : 2*k'+1 = n*p^(r-1)) (x x' : ℤ)
    (hx : x * ((3*k+1).factorial * (8*k+4).factorial * (2*k+1).factorial : ℕ) =
      2^(12*k+6) * ((4*k+2).factorial * (9*k+4).factorial : ℕ))
    (hx' : x' * ((3*k'+1).factorial * (8*k'+4).factorial * (2*k'+1).factorial : ℕ) =
      2^(12*k'+6) * ((4*k'+2).factorial * (9*k'+4).factorial : ℕ)) :
    (x : ZMod (p^(3*r))) = x' := by
  have hpr : p^r = p * p^(r-1) := by rw [← pow_succ']; congr 1; omega
  have hNN : 2*k+1 = p*(2*k'+1) := by rw [hN, hN', hpr]; ring
  have hp2 : p ≠ 2 := by omega
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
  have hkk : k' ≤ k := by
    have : 2*k'+1 ≤ p*(2*k'+1) := Nat.le_mul_of_pos_left _ hp.pos
    omega
  obtain ⟨d, rfl⟩ : ∃ d, k = k' + d := ⟨k - k', by omega⟩
  -- factorial decompositions
  have e1 : 3*(k'+d)+1 = p*(3*k'+1) + t := by
    rw [ht]; rw [ht] at hNN; ring_nf at hNN ⊢; omega
  have e5 : 9*(k'+d)+4 = p*(9*k'+4) + t := by
    rw [ht]; rw [ht] at hNN; ring_nf at hNN ⊢; omega
  have e2 : 8*(k'+d)+4 = p*(8*k'+4) + 0 := by ring_nf at hNN ⊢; omega
  have e3 : 2*(k'+d)+1 = p*(2*k'+1) + 0 := by ring_nf at hNN ⊢; omega
  have e4 : 4*(k'+d)+2 = p*(4*k'+2) + 0 := by ring_nf at hNN ⊢; omega
  have hf1 := fact_decomp_int hp.pos (3*(k'+d)+1) (3*k'+1) t e1 (by omega)
  have hf2 := fact_decomp_int hp.pos (8*(k'+d)+4) (8*k'+4) 0 e2 hp.pos
  have hf3 := fact_decomp_int hp.pos (2*(k'+d)+1) (2*k'+1) 0 e3 hp.pos
  have hf4 := fact_decomp_int hp.pos (4*(k'+d)+2) (4*k'+2) 0 e4 hp.pos
  have hf5 := fact_decomp_int hp.pos (9*(k'+d)+4) (9*k'+4) t e5 (by omega)
  push_cast at hx hx'
  rw [hf1, hf2, hf3, hf4, hf5] at hx
  have hD : ((p:ℤ)^(13*k'+6) * ((3*k'+1).factorial * (8*k'+4).factorial *
      (2*k'+1).factorial : ℕ)) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    · exact Nat.cast_ne_zero.2 (by positivity)
  have key : (x : ℤ) * (F p (3*(k'+d)+1) * F p (8*(k'+d)+4) * F p (2*(k'+d)+1) : ℕ) =
      2^(12*d) * x' * (F p (4*(k'+d)+2) * F p (9*(k'+d)+4) : ℕ) := by
    apply mul_left_cancel₀ hD
    push_cast
    linear_combination hx - ((p:ℤ)^(13*k'+6) * 2^(12*d) *
      (F p (4*(k'+d)+2) * F p (9*(k'+d)+4) : ℤ)) * hx'
  -- cast to ZMod
  set R := ZMod (p^(3*r)) with hR
  have key2 := congrArg (fun z : ℤ => (z : R)) key
  simp only at key2
  push_cast at key2
  set Φ : R := ((F p (p^r) : ℕ) : R) with hΦdef
  set xx : R := ((2*(k'+d)+1 : ℕ) : R) with hxx
  have hpN : p ∣ 2*(k'+d)+1 := by rw [hNN]; exact dvd_mul_right p _
  have hF8 : ((F p (8*(k'+d)+4) : ℕ) : R) = Φ^(4*n) := by
    rw [hΦdef, ← F_block hp hp5 hr]; congr 2
    rw [show 8*(k'+d)+4 = 4*(2*(k'+d)+1) by ring, hN]; ring
  have hF2 : ((F p (2*(k'+d)+1) : ℕ) : R) = Φ^n := by
    rw [hΦdef, ← F_block hp hp5 hr]; congr 2
  have hF4 : ((F p (4*(k'+d)+2) : ℕ) : R) = Φ^(2*n) := by
    rw [hΦdef, ← F_block hp hp5 hr]; congr 2
    rw [show 4*(k'+d)+2 = 2*(2*(k'+d)+1) by ring, hN]; ring
  -- the products
  set Ψ : R := ∏ i ∈ range (k'+d), ((psi p (i+1) : ℕ) : R) with hΨ
  set E1 : R := ∏ i ∈ range (k'+d), (1 + xx * v p (3*r) (i+1)) with hE1
  set E4 : R := ∏ i ∈ range (k'+d), (1 + (4*xx) * v p (3*r) (i+1)) with hE4
  have hF9 : ((F p (9*(k'+d)+4) : ℕ) : R) = Φ^(4*n) * (Ψ * E4) := by
    rw [show 9*(k'+d)+4 = (8*(k'+d)+4) + (k'+d) by ring, F_add, Nat.cast_mul, hF8]
    congr 1
    have : ∀ i, 8*(k'+d)+4 + 1 + i = (8*(k'+d)+4) + (i+1) := by intro i; ring
    simp_rw [this]
    rw [prod_psi_cast hp (3*r) (by rw [show 8*(k'+d)+4 = 4*(2*(k'+d)+1) by ring]; exact Dvd.dvd.mul_left hpN 4) (fun i => i+1)]
    congr 1
    apply prod_congr rfl; intro i _
    rw [hxx]; push_cast; ring
  have hF3 : ((F p (3*(k'+d)+1) : ℕ) : R) = Φ^n * (Ψ * E1) := by
    rw [show 3*(k'+d)+1 = (2*(k'+d)+1) + (k'+d) by ring, F_add, Nat.cast_mul, hF2]
    congr 1
    have : ∀ i, 2*(k'+d)+1 + 1 + i = (2*(k'+d)+1) + (i+1) := by intro i; ring
    simp_rw [this]
    rw [prod_psi_cast hp (3*r) hpN (fun i => i+1)]
  -- core identity
  obtain ⟨h1, h2', h3⟩ := odd_sums hp hp5 hr hN
  have hp3 := pow_three_r_eq_zero (p := p) r
  have hx3 : xx^3 = 0 := by
    rw [hxx, hN]; push_cast; linear_combination ((n : R)^3) * hp3
  have hcore := core_identity (isUnit_two hp hp5 (3*r)) xx (fun i => v p (3*r) (i+1))
    (fun i => v p (3*r) (2*i+1)) (k'+d) hx3 h1 h2' h3
  have htwo := two_pow_eq_prod hp hp5 hr hN hNN
  rw [show 2*(k'+d) - 2*k' = 2*d by omega] at htwo
  simp only at hcore
  rw [htwo] at hcore
  -- hcore : E1 = (2^(2d))^6 * E4
  have hE1E4 : E1 = 2^(12*d) * E4 := by rw [hE1, hE4, hcore]; ring
  -- units
  have hΦu : IsUnit Φ := isUnit_F hp (3*r) (p^r)
  have hQu : IsUnit (Ψ * E4) := by
    have := isUnit_of_coprime hp (3*r) (prod_psi_coprime p hp (range (k'+d)) (fun i => 8*(k'+d)+4 + (i+1)))
    rw [prod_psi_cast hp (3*r) (by rw [show 8*(k'+d)+4 = 4*(2*(k'+d)+1) by ring]; exact Dvd.dvd.mul_left hpN 4) (fun i => i+1)] at this
    convert this using 2
    rw [hE4]
    apply prod_congr rfl; intro i _
    rw [hxx]; push_cast; ring
  have h2u : IsUnit (2 : R) := isUnit_two hp hp5 (3*r)
  rw [hF3, hF8, hF2, hF4, hF9, hE1E4] at key2
  have hfin : (x : R) * (Φ^(6*n) * (2^(12*d) * (Ψ * E4))) = x' * (Φ^(6*n) * (2^(12*d) * (Ψ * E4))) := by
    linear_combination key2
  exact ((hΦu.pow _).mul ((h2u.pow _).mul hQu)).mul_right_cancel hfin

lemma gamma_nat' (c : ℝ) (m : ℕ) (h : c = m + 1) : Real.Gamma c = m.factorial := by
  rw [h, Real.Gamma_nat_eq_factorial]

lemma a_even (k : ℕ) : a (2*k) = (((18*k).factorial * (4*k).factorial * (3*k).factorial : ℕ) : ℝ) /
    (((9*k).factorial * (8*k).factorial * (6*k).factorial * (2*k).factorial : ℕ) : ℝ) := by
  simp only [a]
  push_cast
  rw [gamma_nat' _ (18*k) (by push_cast; ring), gamma_nat' _ (4*k) (by push_cast; ring),
    gamma_nat' _ (3*k) (by push_cast; ring), gamma_nat' _ (9*k) (by push_cast; ring),
    gamma_nat' _ (8*k) (by push_cast; ring), gamma_nat' _ (6*k) (by push_cast; ring),
    gamma_nat' _ (2*k) (by push_cast; ring)]

lemma two_rpow_neg_nat (m : ℕ) : (2:ℝ) ^ (-(m:ℝ)) = ((2:ℝ)^m)⁻¹ := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]

lemma dup1 (k : ℕ) : ((3*k+1).factorial : ℝ) * Real.Gamma (3/2 * (2 * (k:ℝ) + 1) + 1) =
    ((6*k+3).factorial : ℝ) * ((2:ℝ)^(6*k+3))⁻¹ * √Real.pi := by
  have := Real.Gamma_mul_Gamma_add_half ((3*k+2 : ℕ) : ℝ)
  rw [show (1 - 2 * ((3*k+2 : ℕ) : ℝ)) = -((6*k+3 : ℕ) : ℝ) by push_cast; ring, two_rpow_neg_nat,
    show (2:ℝ) * ((3*k+2 : ℕ) : ℝ) = ((6*k+3 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial,
    show ((3*k+2 : ℕ) : ℝ) + 1/2 = 3/2 * (2 * (k:ℝ) + 1) + 1 by push_cast; ring,
    show ((3*k+2 : ℕ) : ℝ) = ((3*k+1 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial] at this
  exact this

lemma dup2 (k : ℕ) : ((9*k+4).factorial : ℝ) * Real.Gamma (9/2 * (2 * (k:ℝ) + 1) + 1) =
    ((18*k+9).factorial : ℝ) * ((2:ℝ)^(18*k+9))⁻¹ * √Real.pi := by
  have := Real.Gamma_mul_Gamma_add_half ((9*k+5 : ℕ) : ℝ)
  rw [show (1 - 2 * ((9*k+5 : ℕ) : ℝ)) = -((18*k+9 : ℕ) : ℝ) by push_cast; ring, two_rpow_neg_nat,
    show (2:ℝ) * ((9*k+5 : ℕ) : ℝ) = ((18*k+9 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial,
    show ((9*k+5 : ℕ) : ℝ) + 1/2 = 9/2 * (2 * (k:ℝ) + 1) + 1 by push_cast; ring,
    show ((9*k+5 : ℕ) : ℝ) = ((9*k+4 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial] at this
  exact this

lemma a_odd (k : ℕ) : a (2*k+1) = (2^(12*k+6) * (((4*k+2).factorial * (9*k+4).factorial : ℕ) : ℝ)) /
    (((3*k+1).factorial * (8*k+4).factorial * (2*k+1).factorial : ℕ) : ℝ) := by
  simp only [a]
  push_cast
  rw [gamma_nat' (9 * (2 * (k:ℝ) + 1) + 1) (18*k+9) (by push_cast; ring),
    gamma_nat' (2 * (2 * (k:ℝ) + 1) + 1) (4*k+2) (by push_cast; ring),
    gamma_nat' (4 * (2 * (k:ℝ) + 1) + 1) (8*k+4) (by push_cast; ring),
    gamma_nat' (3 * (2 * (k:ℝ) + 1) + 1) (6*k+3) (by push_cast; ring),
    gamma_nat' (2 * (k:ℝ) + 1 + 1) (2*k+1) (by push_cast; ring)]
  have h1 := dup1 k
  have h2 := dup2 k
  have hG1 : 0 < Real.Gamma (3/2 * (2 * (k:ℝ) + 1) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG2 : 0 < Real.Gamma (9/2 * (2 * (k:ℝ) + 1) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hf : ∀ m : ℕ, (0:ℝ) < m.factorial := fun m => by exact_mod_cast Nat.factorial_pos m
  have e1 : Real.Gamma (3/2 * (2 * (k:ℝ) + 1) + 1) =
      ((6*k+3).factorial : ℝ) * ((2:ℝ)^(6*k+3))⁻¹ * √Real.pi / ((3*k+1).factorial : ℝ) := by
    rw [eq_div_iff (hf _).ne']; linear_combination h1
  have e2 : Real.Gamma (9/2 * (2 * (k:ℝ) + 1) + 1) =
      ((18*k+9).factorial : ℝ) * ((2:ℝ)^(18*k+9))⁻¹ * √Real.pi / ((9*k+4).factorial : ℝ) := by
    rw [eq_div_iff (hf _).ne']; linear_combination h2
  rw [e1, e2]
  have := hf (3*k+1); have := hf (6*k+3); have := hf (18*k+9); have := hf (9*k+4)
  have := hf (4*k+2); have := hf (8*k+4); have := hf (2*k+1)
  field_simp
  ring

end Super

/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: This conjecture requires that a(n) is an integer for all n, which is only conjectural.
We assume integrality for the purpose of stating the congruence.
-/
theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp hp5 n r hn hr
  have hspec : ∀ m, ((Classical.choose (h_int m) : ℤ) : ℝ) = a m :=
    fun m => Classical.choose_spec (h_int m)
  have hmod : ((p : ℤ) ^ (3 * r)) = ((p ^ (3 * r) : ℕ) : ℤ) := by push_cast; rfl
  rw [hmod, ← ZMod.intCast_eq_intCast_iff]
  obtain ⟨n', hn' | hn'⟩ := Nat.even_or_odd' n
  · subst hn'
    apply Super.even_main hp hp5 hr n'
    · have h := hspec (2 * n' * p^r)
      generalize Classical.choose (h_int (2 * n' * p^r)) = x at h ⊢
      rw [mul_assoc, Super.a_even] at h
      rw [eq_div_iff (by positivity)] at h
      exact_mod_cast h
    · have h := hspec (2 * n' * p^(r-1))
      generalize Classical.choose (h_int (2 * n' * p^(r-1))) = x at h ⊢
      rw [mul_assoc, Super.a_even] at h
      rw [eq_div_iff (by positivity)] at h
      exact_mod_cast h
  · subst hn'
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    obtain ⟨k, hk⟩ : Odd ((2*n'+1) * p^r) := Odd.mul (odd_two_mul_add_one n') (Odd.pow hpodd)
    obtain ⟨k', hk'⟩ : Odd ((2*n'+1) * p^(r-1)) := Odd.mul (odd_two_mul_add_one n') (Odd.pow hpodd)
    apply Super.odd_main hp hp5 hr (k := k) (k' := k') (n := 2*n'+1) hk.symm hk'.symm
    · have h := hspec ((2*n'+1) * p^r)
      generalize Classical.choose (h_int ((2*n'+1) * p^r)) = x at h ⊢
      rw [hk, Super.a_odd] at h
      rw [eq_div_iff (by positivity)] at h
      exact_mod_cast h
    · have h := hspec ((2*n'+1) * p^(r-1))
      generalize Classical.choose (h_int ((2*n'+1) * p^(r-1))) = x at h ⊢
      rw [hk', Super.a_odd] at h
      rw [eq_div_iff (by positivity)] at h
      exact_mod_cast h


theorem oeis_364173_conjecture_0.disproof : ¬ (type_of% @oeis_364173_conjecture_0) := sorry
