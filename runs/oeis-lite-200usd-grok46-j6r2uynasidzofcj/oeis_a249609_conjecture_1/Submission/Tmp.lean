import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 4000000

open Nat List

def popc (n : ℕ) : ℕ := (List.range (n.log2 + 1)).countP n.testBit

lemma popc_zero : popc 0 = 0 := by
  have h0 : Nat.log2 0 = 0 := by rw [Nat.log2_def]; simp
  unfold popc
  rw [h0]
  simp only [zero_add, range_one, countP_singleton]
  have : Nat.testBit 0 0 = false := Nat.testBit_lt_two_pow (by decide : (0 : ℕ) < 2 ^ 0)
  simp [this]

lemma popc_one : popc 1 = 1 := by
  have hlog : Nat.log2 1 = 0 := by rw [Nat.log2_def]; simp
  unfold popc
  rw [hlog]
  simp only [zero_add, range_one, countP_singleton, Nat.testBit_zero]
  decide

lemma log2_div2 {n : ℕ} (hn : 2 ≤ n) : n.log2 = (n / 2).log2 + 1 := by
  rw [Nat.log2_def (n := n)]
  simp [hn]

lemma popc_rec (n : ℕ) : popc n = n % 2 + popc (n / 2) := by
  by_cases h0 : n = 0
  · subst h0; simp [popc_zero]
  by_cases h1 : n = 1
  · subst h1; simp [popc_one, popc_zero]
  have hn2 : 2 ≤ n := by omega
  unfold popc
  have hlog : n.log2 = (n / 2).log2 + 1 := log2_div2 hn2
  rw [hlog, range_succ_eq_map]
  simp only [countP_cons, Nat.testBit_zero]
  have hmap :
      countP n.testBit (map succ (range ((n / 2).log2 + 1))) =
      countP (n / 2).testBit (range ((n / 2).log2 + 1)) := by
    rw [countP_map]
    apply countP_congr
    intro i hi
    simp [Nat.testBit_succ]
  rw [hmap]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [h]
  · simp [h]; omega

lemma popc_two_pow (m : ℕ) : popc (2 ^ m) = 1 := by
  induction m with
  | zero =>
    simp [pow_zero, popc_one]
  | succ m ih =>
    rw [pow_succ, popc_rec]
    have hmod : (2 ^ m * 2) % 2 = 0 := by
      rw [Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod]
    have hdiv : (2 ^ m * 2) / 2 = 2 ^ m := by
      rw [Nat.mul_div_cancel _ (by decide : 0 < 2)]
    rw [hmod, hdiv, zero_add, ih]

lemma popc_mul_two_pow (t k : ℕ) : popc (2 ^ t * k) = popc k := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h2 : 2 ^ (t + 1) * k = 2 * (2 ^ t * k) := by
      rw [pow_succ]
      ring
    rw [h2, popc_rec]
    have hmod : (2 * (2 ^ t * k)) % 2 = 0 := by simp
    have hdiv : (2 * (2 ^ t * k)) / 2 = 2 ^ t * k := by
      rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    rw [hmod, hdiv, zero_add, ih]

lemma popc_two_pow_mul_add {a b i : ℕ} (hb : b < 2 ^ i) :
    popc (2 ^ i * a + b) = popc a + popc b := by
  induction i generalizing a b with
  | zero =>
    have : b = 0 := by
      have : b < 1 := by simpa using hb
      omega
    subst this
    simp [popc_zero]
  | succ i ih =>
    rw [popc_rec (2 ^ (i + 1) * a + b), popc_rec b]
    have hmod : (2 ^ (i + 1) * a + b) % 2 = b % 2 := by
      have : 2 ^ (i + 1) * a = 2 * (2 ^ i * a) := by
        rw [pow_succ]
        ring
      rw [this, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
    have hdiv : (2 ^ (i + 1) * a + b) / 2 = 2 ^ i * a + b / 2 := by
      have : 2 ^ (i + 1) * a = 2 * (2 ^ i * a) := by
        rw [pow_succ]
        ring
      rw [this, Nat.mul_add_div (by decide : 0 < 2)]
    rw [hmod, hdiv]
    have hb' : b / 2 < 2 ^ i := by
      have : b < 2 * 2 ^ i := by
        rwa [pow_succ, mul_comm] at hb
      omega
    rw [ih hb']
    omega

lemma geom_sum_pow_two (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 : ℕ) ^ i) = 2 ^ n - 1 := by
  simpa using Nat.geomSum_eq (m := 2) (by decide) n

lemma sum_two_pow_lt {s : Finset ℕ} {k : ℕ} (h : ∀ x ∈ s, x < k) :
    (∑ i ∈ s, (2 : ℕ) ^ i) < 2 ^ k := by
  have hsub : s ⊆ Finset.range k := by
    intro x hx; simp [h x hx]
  have hle : (∑ i ∈ s, (2 : ℕ) ^ i) ≤ ∑ i ∈ Finset.range k, 2 ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have : (∑ i ∈ Finset.range k, (2 : ℕ) ^ i) = 2 ^ k - 1 := geom_sum_pow_two k
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
  omega

lemma popc_sum_two_pow_finset (s : Finset ℕ) :
    popc (∑ i ∈ s, (2 : ℕ) ^ i) = s.card := by
  refine Finset.induction_on_max s ?empty ?step
  · simp [popc_zero]
  · intro a s hlt ih
    have hnot : a ∉ s := fun ha => (lt_irrefl a) (hlt a ha)
    have hsum : ∑ i ∈ insert a s, (2 : ℕ) ^ i = 2 ^ a + ∑ i ∈ s, 2 ^ i :=
      Finset.sum_insert hnot
    have hbound : (∑ i ∈ s, (2 : ℕ) ^ i) < 2 ^ a :=
      sum_two_pow_lt (fun x hx => hlt x hx)
    have hform : 2 ^ a + ∑ i ∈ s, (2 : ℕ) ^ i = 2 ^ a * 1 + ∑ i ∈ s, 2 ^ i := by
      ring
    rw [hsum, hform, popc_two_pow_mul_add hbound, popc_one, ih,
      Finset.card_insert_of_notMem hnot]
    omega

lemma four_pow_eq (i : ℕ) : (4 : ℕ) ^ i = 2 ^ (2 * i) := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]

lemma three_dvd_four_pow_sub_one (b : ℕ) : 3 ∣ 4 ^ b - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow (4 : ℕ) 1 b

lemma R_eq_sum (b : ℕ) :
    (4 ^ b - 1) / 3 = ∑ i ∈ Finset.range b, (2 : ℕ) ^ (2 * i) := by
  have hgeom : ∑ i ∈ Finset.range b, (4 : ℕ) ^ i = (4 ^ b - 1) / 3 := by
    simpa using Nat.geomSum_eq (m := 4) (by decide) b
  rw [← hgeom]
  apply Finset.sum_congr rfl
  intro i _
  exact four_pow_eq i

lemma injective_double : Function.Injective (fun i : ℕ => 2 * i) :=
  fun _ _ h => Nat.mul_left_cancel (by decide : (0 : ℕ) < 2) h

lemma injective_odd_shift (t : ℕ) :
    Function.Injective (fun i : ℕ => 2 * t + 1 + 2 * i) := by
  intro x y h
  have : 2 * x = 2 * y := Nat.add_left_cancel h
  exact injective_double this

lemma popc_R (b : ℕ) : popc ((4 ^ b - 1) / 3) = b := by
  rw [R_eq_sum]
  have himg :
      ∑ i ∈ Finset.range b, (2 : ℕ) ^ (2 * i) =
        ∑ j ∈ (Finset.range b).image (fun i => 2 * i), 2 ^ j := by
    rw [Finset.sum_image]
    intro x _ y _ h
    exact injective_double h
  rw [himg, popc_sum_two_pow_finset, Finset.card_image_of_injective _ injective_double]
  simp

lemma three_dvd_two_pow_add_one_of_odd {g : ℕ} (h : g % 2 = 1) :
    3 ∣ 2 ^ g + 1 := by
  have hg : g = 2 * (g / 2) + 1 := by omega
  rw [hg, pow_add, pow_mul, pow_one, mul_comm (a := (2 ^ 2) ^ (g / 2))]
  have hsub : 3 ∣ (2 ^ 2) ^ (g / 2) - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 (g / 2)
  have hle : 1 ≤ (2 ^ 2) ^ (g / 2) := Nat.one_le_pow _ _ (by decide)
  have : 2 * (2 ^ 2) ^ (g / 2) + 1 = 2 * ((2 ^ 2) ^ (g / 2) - 1) + 3 := by
    omega
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right hsub 2) (by decide : 3 ∣ 3)

lemma Q_eq (t : ℕ) :
    (2 ^ (2 * t + 1) + 1) / 3 = 1 + 2 * ((4 ^ t - 1) / 3) := by
  have hdiv : 3 ∣ 2 ^ (2 * t + 1) + 1 :=
    three_dvd_two_pow_add_one_of_odd (by omega)
  have hdiv' : 3 ∣ 4 ^ t - 1 := three_dvd_four_pow_sub_one t
  apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
  have lhs : 3 * ((2 ^ (2 * t + 1) + 1) / 3) = 2 ^ (2 * t + 1) + 1 :=
    Nat.mul_div_cancel' hdiv
  have rhs : 3 * (1 + 2 * ((4 ^ t - 1) / 3)) =
      3 + 2 * (3 * ((4 ^ t - 1) / 3)) := by ring
  rw [lhs, rhs, Nat.mul_div_cancel' hdiv']
  have hpow : 2 ^ (2 * t + 1) = 2 * 4 ^ t := by
    rw [pow_add, pow_one, four_pow_eq, mul_comm]
  have hle : 1 ≤ 4 ^ t := Nat.one_le_pow _ _ (by decide)
  omega

lemma popc_Q (t : ℕ) :
    popc ((2 ^ (2 * t + 1) + 1) / 3) = t + 1 := by
  rw [Q_eq, add_comm, popc_rec]
  have hmod : (2 * ((4 ^ t - 1) / 3) + 1) % 2 = 1 := by simp
  have hdiv : (2 * ((4 ^ t - 1) / 3) + 1) / 2 = (4 ^ t - 1) / 3 := by
    rw [Nat.mul_add_div (by decide : 0 < 2)]
    simp
  rw [hmod, hdiv, popc_R, add_comm]

lemma term3_eq (t b : ℕ) :
    ((2 ^ (2 * t + 1) + 1) / 3) * (4 ^ b - 1) =
      (4 ^ b - 1) / 3 + 2 ^ (2 * t + 1) * ((4 ^ b - 1) / 3) := by
  set Q := (2 ^ (2 * t + 1) + 1) / 3
  set R := (4 ^ b - 1) / 3
  have hR : 3 * R = 4 ^ b - 1 := Nat.mul_div_cancel' (three_dvd_four_pow_sub_one b)
  have hQ : 3 * Q = 2 ^ (2 * t + 1) + 1 :=
    Nat.mul_div_cancel' (three_dvd_two_pow_add_one_of_odd (by omega))
  calc
    Q * (4 ^ b - 1) = Q * (3 * R) := by rw [hR]
    _ = (3 * Q) * R := by ring
    _ = (2 ^ (2 * t + 1) + 1) * R := by rw [hQ]
    _ = R + 2 ^ (2 * t + 1) * R := by ring

lemma term3_as_sum (t b : ℕ) :
    (4 ^ b - 1) / 3 + 2 ^ (2 * t + 1) * ((4 ^ b - 1) / 3) =
      ∑ i ∈ Finset.range b, (2 : ℕ) ^ (2 * i) +
        ∑ i ∈ Finset.range b, 2 ^ (2 * t + 1 + 2 * i) := by
  rw [R_eq_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← pow_add]

lemma disjoint_parity_images (t b : ℕ) :
    Disjoint ((Finset.range b).image (fun i => 2 * i))
      ((Finset.range b).image (fun i => 2 * t + 1 + 2 * i)) := by
  refine Finset.disjoint_iff_ne.2 ?_
  intro x hx y hy hxy
  simp only [Finset.mem_image, Finset.mem_range] at hx hy
  rcases hx with ⟨i, _, rfl⟩
  rcases hy with ⟨j, _, rfl⟩
  have : (2 * i) % 2 = (2 * t + 1 + 2 * j) % 2 := by rw [hxy]
  simp [Nat.add_mod] at this

lemma popc_term3 (t b : ℕ) :
    popc (((2 ^ (2 * t + 1) + 1) / 3) * (4 ^ b - 1)) = 2 * b := by
  rw [term3_eq, term3_as_sum]
  have h1 :
      ∑ i ∈ Finset.range b, (2 : ℕ) ^ (2 * i) =
        ∑ j ∈ (Finset.range b).image (fun i => 2 * i), 2 ^ j := by
    rw [Finset.sum_image]; intro x _ y _ h; exact injective_double h
  have h2 :
      ∑ i ∈ Finset.range b, (2 : ℕ) ^ (2 * t + 1 + 2 * i) =
        ∑ j ∈ (Finset.range b).image (fun i => 2 * t + 1 + 2 * i), 2 ^ j := by
    rw [Finset.sum_image]; intro x _ y _ h; exact injective_odd_shift t h
  rw [h1, h2, ← Finset.sum_union (disjoint_parity_images t b)]
  rw [popc_sum_two_pow_finset, Finset.card_union_of_disjoint (disjoint_parity_images t b)]
  rw [Finset.card_image_of_injective _ injective_double]
  rw [Finset.card_image_of_injective _ (injective_odd_shift t)]
  simp; omega

lemma Q_mul_odd_sq (t ea b : ℕ) :
    let Q := (2 ^ (2 * t + 1) + 1) / 3
    Q * (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) =
      2 ^ (2 * ea) * Q + 2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1) := by
  intro Q
  have h4 : (4 : ℕ) ^ b - 1 = 2 ^ (2 * b) - 1 := by rw [four_pow_eq]
  rw [mul_add, mul_add, h4]
  ring

lemma one_le_two_pow (n : ℕ) : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_pow _ _ (by decide)

lemma term3_lt (t b : ℕ) :
    ((2 ^ (2 * t + 1) + 1) / 3) * (4 ^ b - 1) < 2 ^ (2 * b + (2 * t + 1) + 1) := by
  set Q := (2 ^ (2 * t + 1) + 1) / 3
  set g := 2 * t + 1
  have hdiv : 3 ∣ 2 ^ g + 1 := three_dvd_two_pow_add_one_of_odd (by omega)
  have hQ3 : 3 * Q = 2 ^ g + 1 := Nat.mul_div_cancel' hdiv
  have hQle : Q ≤ 2 ^ g := by
    have : 3 * Q ≤ 3 * 2 ^ g := by
      have h1 : 1 ≤ 2 ^ g := one_le_two_pow g
      omega
    exact Nat.le_of_mul_le_mul_left this (by decide)
  have hRlt : (4 : ℕ) ^ b - 1 < 4 ^ b := Nat.sub_lt (Nat.one_le_pow _ _ (by decide)) (by decide)
  have hgpos : 0 < 2 ^ g := Nat.one_le_pow _ _ (by decide)
  have hlt : Q * (4 ^ b - 1) < 2 ^ g * 4 ^ b :=
    Nat.mul_lt_mul_of_le_of_lt hQle hRlt hgpos
  have heq : 2 ^ g * 4 ^ b = 2 ^ (g + 2 * b) := by
    rw [four_pow_eq, ← pow_add]
  have hpowlt : 2 ^ (g + 2 * b) < 2 ^ (2 * b + g + 1) :=
    Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2) (by omega)
  omega

lemma Q_lt_shift (t : ℕ) (ht : 1 ≤ t) :
    (2 ^ (2 * t + 1) + 1) / 3 < 2 ^ (2 * t) := by
  have hdiv : 3 ∣ 2 ^ (2 * t + 1) + 1 :=
    three_dvd_two_pow_add_one_of_odd (by omega)
  have h3 : 3 * ((2 ^ (2 * t + 1) + 1) / 3) = 2 ^ (2 * t + 1) + 1 :=
    Nat.mul_div_cancel' hdiv
  have hgoal : 2 ^ (2 * t + 1) + 1 < 3 * 2 ^ (2 * t) := by
    have : 2 ^ (2 * t + 1) = 2 ^ (2 * t) * 2 := pow_succ _ _
    rw [this]
    have : 1 < 2 ^ (2 * t) := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hmul : 3 * ((2 ^ (2 * t + 1) + 1) / 3) < 3 * 2 ^ (2 * t) := by
    rwa [h3]
  exact Nat.lt_of_mul_lt_mul_left hmul

lemma popc_P {t ea b : ℕ} (ht : 1 ≤ t)
    (hg : ea = b + (2 * t + 1)) :
    popc (((2 ^ (2 * t + 1) + 1) / 3) *
      (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1))) =
        2 * t + 2 + 2 * b := by
  set Q := (2 ^ (2 * t + 1) + 1) / 3
  have hdecomp := Q_mul_odd_sq t ea b
  change Q * (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) =
      2 ^ (2 * ea) * Q + 2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1) at hdecomp
  rw [hdecomp]
  have hT3lt : Q * (4 ^ b - 1) < 2 ^ (ea + b + 1) := by
    have hlt0 := term3_lt t b
    have hidx : 2 * b + (2 * t + 1) + 1 = ea + b + 1 := by omega
    rwa [hidx] at hlt0
  have hT2T3 :
      popc (2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1)) =
        popc Q + popc (Q * (4 ^ b - 1)) :=
    popc_two_pow_mul_add hT3lt
  have hQlt : Q < 2 ^ (2 * t) := Q_lt_shift t ht
  have hsumlt : 2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1) < 2 ^ (2 * ea) := by
    have : 2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1) <
        2 ^ (ea + b + 1) * Q + 2 ^ (ea + b + 1) :=
      Nat.add_lt_add_left hT3lt _
    have hsplit : 2 ^ (ea + b + 1) * Q + 2 ^ (ea + b + 1) =
        2 ^ (ea + b + 1) * (Q + 1) := by ring
    have hQ1 : Q + 1 ≤ 2 ^ (2 * t) := by omega
    have : 2 ^ (ea + b + 1) * (Q + 1) ≤ 2 ^ (ea + b + 1) * 2 ^ (2 * t) :=
      Nat.mul_le_mul_left _ hQ1
    have hpow : 2 ^ (ea + b + 1) * 2 ^ (2 * t) = 2 ^ (2 * ea) := by
      rw [← pow_add]; congr 1; omega
    omega
  have hform :
      2 ^ (2 * ea) * Q + 2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1) =
        2 ^ (2 * ea) * Q + (2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1)) := by
    ring
  rw [hform, popc_two_pow_mul_add hsumlt, hT2T3, popc_Q, popc_term3]
  omega

lemma sq_sub_one_of_three_bit (ea b : ℕ) :
    (2 ^ ea + 2 ^ b + 1) * (2 ^ ea + 2 ^ b - 1) =
      2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) := by
  have hbpow : 1 ≤ 2 ^ b := one_le_two_pow b
  have hx : 1 ≤ 2 ^ ea + 2 ^ b :=
    hbpow.trans (Nat.le_add_left (2 ^ b) (2 ^ ea))
  have hb : 1 ≤ 2 ^ (2 * b) := one_le_two_pow _
  have hpos : 1 ≤ 2 ^ (2 * ea) + 2 ^ (ea + b + 1) + 2 ^ (2 * b) :=
    hb.trans (Nat.le_add_left _ _)
  have h1 : (2 ^ ea + 2 ^ b + 1) * (2 ^ ea + 2 ^ b - 1) =
      (2 ^ ea + 2 ^ b) * (2 ^ ea + 2 ^ b) - 1 := by
    set x := 2 ^ ea + 2 ^ b
    have hx' : 1 ≤ x := hx
    have : (x + 1) * (x - 1) = x * x - 1 := by
      have hdist := Nat.mul_sub_left_distrib (x + 1) x 1
      simp only [mul_one] at hdist
      have : (x + 1) * x = x * x + x := by ring
      rw [hdist, this]
      have hxcancel : x * x + x - x = x * x := Nat.add_sub_cancel (x * x) x
      have hle : x ≤ x * x + x := Nat.le_add_left _ _
      have hle1 : 1 ≤ x := hx'
      -- (x*x + x) - 1 - x = x*x - 1, and (x*x + x - x) - 1 = x*x - 1
      have : x * x + x - 1 - x = x * x + x - x - 1 := by
        have : x ≤ x * x + x - 1 := by
          have : 1 ≤ x * x := by
            have : 1 ≤ x := hle1
            exact le_trans this (Nat.le_mul_of_pos_right x this)
          omega
        omega
      omega
    exact this
  have h2 : (2 ^ ea + 2 ^ b) * (2 ^ ea + 2 ^ b) =
      2 ^ (2 * ea) + 2 ^ (ea + b + 1) + 2 ^ (2 * b) := by
    have ha : 2 ^ ea * 2 ^ ea = 2 ^ (2 * ea) := by rw [← pow_add]; congr 1; omega
    have hb' : 2 ^ b * 2 ^ b = 2 ^ (2 * b) := by rw [← pow_add]; congr 1; omega
    have hab : 2 * 2 ^ ea * 2 ^ b = 2 ^ (ea + b + 1) := by
      have : 2 * 2 ^ ea * 2 ^ b = 2 ^ 1 * 2 ^ ea * 2 ^ b := by simp
      rw [this, mul_assoc, ← pow_add, ← pow_add]
      congr 1; omega
    calc
      (2 ^ ea + 2 ^ b) * (2 ^ ea + 2 ^ b) =
          2 ^ ea * 2 ^ ea + 2 * 2 ^ ea * 2 ^ b + 2 ^ b * 2 ^ b := by ring
      _ = 2 ^ (2 * ea) + 2 ^ (ea + b + 1) + 2 ^ (2 * b) := by rw [ha, hab, hb']
  have : (2 ^ ea + 2 ^ b) * (2 ^ ea + 2 ^ b) - 1 =
      2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) := by
    rw [h2, Nat.add_sub_assoc hb]
  exact h1.trans this

lemma popc_odd_part_choose_three {ea b : ℕ} (_hba : b < ea)
    (_hb : 1 ≤ b) (hodd : (ea - b) % 2 = 1) (hne : 3 ≤ ea - b) :
    popc (((2 ^ ea + 2 ^ b + 1) * (2 ^ (ea - b) + 1) * (2 ^ ea + 2 ^ b - 1)) / 3) % 2 = 0 := by
  set g := ea - b
  have hg : g = 2 * (g / 2) + 1 := by omega
  have ht : 1 ≤ g / 2 := by omega
  have hea : ea = b + g := by omega
  have hdiv : 3 ∣ 2 ^ g + 1 := three_dvd_two_pow_add_one_of_odd hodd
  have hprod := sq_sub_one_of_three_bit ea b
  have hrewrite :
      ((2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1)) / 3 =
        (2 ^ g + 1) / 3 * (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) := by
    have hmul :
        (2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1) =
          (2 ^ g + 1) * (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) := by
      calc
        (2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1) =
            (2 ^ g + 1) * ((2 ^ ea + 2 ^ b + 1) * (2 ^ ea + 2 ^ b - 1)) := by ring
        _ = (2 ^ g + 1) * (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) := by
              rw [hprod]
    rw [hmul, mul_comm (2 ^ g + 1), Nat.mul_div_assoc _ hdiv, mul_comm]
  rw [hrewrite, show g = 2 * (g / 2) + 1 from hg]
  have hp := popc_P (t := g / 2) (ea := ea) (b := b) ht (by omega)
  rw [hp]; omega


lemma two_pow_add_sub_one_div_three_eq (b s : ℕ) :
    2 ^ (2 * (b + (4 * s + 2))) + 2 ^ ((b + (4 * s + 2)) + b + 1) + (2 ^ (2 * b) - 1) =
      (4 ^ b - 1) + 2 ^ (2 * b + (4 * s + 2) + 1) * (2 ^ ((4 * s + 2) - 1) + 1) := by
  set g := 4 * s + 2
  set ea := b + g
  have h4 : (4 : ℕ) ^ b = 2 ^ (2 * b) := four_pow_eq b
  have hpow1 : 2 ^ (2 * b + g + 1) * 2 ^ (g - 1) = 2 ^ (2 * ea) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow2 : 2 ^ (2 * b + g + 1) = 2 ^ (ea + b + 1) := by
    congr 1; omega
  calc
    2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) =
        2 ^ (2 * b + g + 1) * 2 ^ (g - 1) + 2 ^ (2 * b + g + 1) + (2 ^ (2 * b) - 1) := by
          rw [hpow1, hpow2]
    _ = 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) + (2 ^ (2 * b) - 1) := by ring
    _ = 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) + (4 ^ b - 1) := by rw [h4]
    _ = (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by ring

lemma Qbig_eq (b s : ℕ) :
    (2 ^ (2 * (b + (4 * s + 2))) + 2 ^ ((b + (4 * s + 2)) + b + 1) +
        (2 ^ (2 * b) - 1)) / 3 =
      (4 ^ b - 1) / 3 +
        2 ^ (2 * b + (4 * s + 2) + 1) * ((2 ^ ((4 * s + 2) - 1) + 1) / 3) := by
  set g := 4 * s + 2
  set ea := b + g
  have hdivR : 3 ∣ 4 ^ b - 1 := three_dvd_four_pow_sub_one b
  have hodd : (g - 1) % 2 = 1 := by omega
  have hdivS : 3 ∣ 2 ^ (g - 1) + 1 := three_dvd_two_pow_add_one_of_odd hodd
  have hid := two_pow_add_sub_one_div_three_eq b s
  have hdiv : 3 ∣ 2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) := by
    have : 3 ∣ (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) :=
      hdivR.add (hdivS.mul_left _)
    simpa [g, ea] using (hid.symm ▸ this)
  apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
  have lhs : 3 * ((2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) / 3) =
      2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) :=
    Nat.mul_div_cancel' hdiv
  have rhs :
      3 * ((4 ^ b - 1) / 3 + 2 ^ (2 * b + g + 1) * ((2 ^ (g - 1) + 1) / 3)) =
        (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by
    rw [mul_add, Nat.mul_div_cancel' hdivR]
    have : 3 * (2 ^ (2 * b + g + 1) * ((2 ^ (g - 1) + 1) / 3)) =
        2 ^ (2 * b + g + 1) * (3 * ((2 ^ (g - 1) + 1) / 3)) := by ring
    rw [this, Nat.mul_div_cancel' hdivS]
  rw [lhs, rhs]
  simpa [g, ea] using hid


lemma R_mul_one_add_four_pow_of_le {b t : ℕ} (ht : t ≤ b) :
    ((4 ^ b - 1) / 3) * (1 + 4 ^ t) =
      (4 ^ t - 1) / 3 + 2 * 4 ^ t * ((4 ^ (b - t) - 1) / 3) +
        4 ^ b * ((4 ^ t - 1) / 3) := by
  have hRb : 3 ∣ 4 ^ b - 1 := three_dvd_four_pow_sub_one b
  have hRt : 3 ∣ 4 ^ t - 1 := three_dvd_four_pow_sub_one t
  have hRbt : 3 ∣ 4 ^ (b - t) - 1 := three_dvd_four_pow_sub_one (b - t)
  apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
  have lhs : 3 * (((4 ^ b - 1) / 3) * (1 + 4 ^ t)) = (4 ^ b - 1) * (1 + 4 ^ t) := by
    rw [← mul_assoc, Nat.mul_div_cancel' hRb]
  have rhs :
      3 * ((4 ^ t - 1) / 3 + 2 * 4 ^ t * ((4 ^ (b - t) - 1) / 3) +
          4 ^ b * ((4 ^ t - 1) / 3)) =
        (4 ^ t - 1) + 2 * 4 ^ t * (4 ^ (b - t) - 1) + 4 ^ b * (4 ^ t - 1) := by
    have h1 : 3 * ((4 ^ t - 1) / 3) = 4 ^ t - 1 := Nat.mul_div_cancel' hRt
    have h2 : 3 * (2 * 4 ^ t * ((4 ^ (b - t) - 1) / 3)) =
        2 * 4 ^ t * (4 ^ (b - t) - 1) := by
      have : 3 * (2 * 4 ^ t * ((4 ^ (b - t) - 1) / 3)) =
          2 * 4 ^ t * (3 * ((4 ^ (b - t) - 1) / 3)) := by ring
      rw [this, Nat.mul_div_cancel' hRbt]
    have h3 : 3 * (4 ^ b * ((4 ^ t - 1) / 3)) = 4 ^ b * (4 ^ t - 1) := by
      have : 3 * (4 ^ b * ((4 ^ t - 1) / 3)) = 4 ^ b * (3 * ((4 ^ t - 1) / 3)) := by
        ring
      rw [this, Nat.mul_div_cancel' hRt]
    rw [mul_add, mul_add, h1, h2, h3]
  rw [lhs, rhs]
  have hle1 : 1 ≤ 4 ^ t := Nat.one_le_pow _ _ (by decide)
  have hle2 : 1 ≤ 4 ^ (b - t) := Nat.one_le_pow _ _ (by decide)
  have hle3 : 1 ≤ 4 ^ b := Nat.one_le_pow _ _ (by decide)
  have hpow : (4 : ℕ) ^ t * 4 ^ (b - t) = 4 ^ b := by
    rw [← pow_add]; congr 1; omega
  zify [hle1, hle2, hle3]
  have hpowZ : (4 : ℤ) ^ t * 4 ^ (b - t) = 4 ^ b := by
    exact_mod_cast hpow
  rw [← hpowZ]
  ring

lemma popc_R_mul_one_add_four_pow {b t : ℕ} (ht : t ≤ b) :
    popc (((4 ^ b - 1) / 3) * (1 + 4 ^ t)) = b + t := by
  rw [R_mul_one_add_four_pow_of_le ht]
  set R1 := (4 ^ t - 1) / 3
  set R2 := (4 ^ (b - t) - 1) / 3
  have h1 : R1 = ∑ i ∈ Finset.range t, (2 : ℕ) ^ (2 * i) := R_eq_sum t
  have h2 : R2 = ∑ i ∈ Finset.range (b - t), (2 : ℕ) ^ (2 * i) := R_eq_sum (b - t)
  have hmid : 2 * 4 ^ t * R2 = ∑ i ∈ Finset.range (b - t), (2 : ℕ) ^ (2 * t + 1 + 2 * i) := by
    rw [h2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have : 2 * 4 ^ t * 2 ^ (2 * i) = 2 ^ (2 * t + 1 + 2 * i) := by
      have : (4 : ℕ) ^ t = 2 ^ (2 * t) := four_pow_eq t
      rw [this]
      have : (2 : ℕ) * 2 ^ (2 * t) = 2 ^ (2 * t + 1) := (pow_succ' 2 (2 * t)).symm
      rw [this, ← pow_add]
    exact this
  have hhi : 4 ^ b * R1 = ∑ i ∈ Finset.range t, (2 : ℕ) ^ (2 * b + 2 * i) := by
    rw [h1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have : (4 : ℕ) ^ b * 2 ^ (2 * i) = 2 ^ (2 * b + 2 * i) := by
      rw [four_pow_eq, ← pow_add]
    exact this
  -- pack as images and take union
  have himg1 :
      ∑ i ∈ Finset.range t, (2 : ℕ) ^ (2 * i) =
        ∑ j ∈ (Finset.range t).image (fun i => 2 * i), 2 ^ j := by
    rw [Finset.sum_image]; intro x _ y _ h; exact injective_double h
  have himg2 :
      ∑ i ∈ Finset.range (b - t), (2 : ℕ) ^ (2 * t + 1 + 2 * i) =
        ∑ j ∈ (Finset.range (b - t)).image (fun i => 2 * t + 1 + 2 * i), 2 ^ j := by
    rw [Finset.sum_image]; intro x _ y _ h; exact injective_odd_shift t h
  have himg3 :
      ∑ i ∈ Finset.range t, (2 : ℕ) ^ (2 * b + 2 * i) =
        ∑ j ∈ (Finset.range t).image (fun i => 2 * b + 2 * i), 2 ^ j := by
    rw [Finset.sum_image]
    intro x _ y _ h
    exact injective_double (Nat.add_left_cancel h)
  have d12 : Disjoint ((Finset.range t).image (fun i => 2 * i))
      ((Finset.range (b - t)).image (fun i => 2 * t + 1 + 2 * i)) := by
    refine Finset.disjoint_iff_ne.2 ?_
    intro x hx y hy hxy
    simp only [Finset.mem_image, Finset.mem_range] at hx hy
    rcases hx with ⟨i, _, rfl⟩
    rcases hy with ⟨j, _, rfl⟩
    have : (2 * i) % 2 = (2 * t + 1 + 2 * j) % 2 := by rw [hxy]
    simp [Nat.add_mod] at this
  have d13 : Disjoint ((Finset.range t).image (fun i => 2 * i))
      ((Finset.range t).image (fun i => 2 * b + 2 * i)) := by
    refine Finset.disjoint_iff_ne.2 ?_
    intro x hx y hy hxy
    simp only [Finset.mem_image, Finset.mem_range] at hx hy
    rcases hx with ⟨i, hi, rfl⟩
    rcases hy with ⟨j, hj, rfl⟩
    have : 2 * i = 2 * b + 2 * j := hxy
    omega
  have d23 : Disjoint ((Finset.range (b - t)).image (fun i => 2 * t + 1 + 2 * i))
      ((Finset.range t).image (fun i => 2 * b + 2 * i)) := by
    refine Finset.disjoint_iff_ne.2 ?_
    intro x hx y hy hxy
    simp only [Finset.mem_image, Finset.mem_range] at hx hy
    rcases hx with ⟨i, hi, rfl⟩
    rcases hy with ⟨j, hj, rfl⟩
    have : 2 * t + 1 + 2 * i = 2 * b + 2 * j := hxy
    omega
  have d123 : Disjoint
      (((Finset.range t).image (fun i => 2 * i)) ∪
        (Finset.range (b - t)).image (fun i => 2 * t + 1 + 2 * i))
      ((Finset.range t).image (fun i => 2 * b + 2 * i)) :=
    Finset.disjoint_union_left.2 ⟨d13, d23⟩
  rw [hmid, hhi, h1, himg1, himg2, himg3]
  rw [← Finset.sum_union d12, ← Finset.sum_union d123]
  rw [popc_sum_two_pow_finset]
  rw [Finset.card_union_of_disjoint d123, Finset.card_union_of_disjoint d12]
  rw [Finset.card_image_of_injective _ injective_double]
  rw [Finset.card_image_of_injective _ (injective_odd_shift t)]
  have hinj : Function.Injective (fun i : ℕ => 2 * b + 2 * i) :=
    fun x y h => injective_double (Nat.add_left_cancel h)
  rw [Finset.card_image_of_injective _ hinj]
  simp; omega

lemma two_pow_eq_four_pow_half (s : ℕ) :
    (2 : ℕ) ^ (4 * s + 2) = 4 ^ (2 * s + 1) := by
  rw [four_pow_eq]; congr 1; omega

lemma Qg_lt (s : ℕ) :
    (2 ^ ((4 * s + 2) - 1) + 1) / 3 < 2 ^ ((4 * s + 2) - 1) := by
  have hodd : ((4 * s + 2) - 1) % 2 = 1 := by omega
  have hdiv : 3 ∣ 2 ^ ((4 * s + 2) - 1) + 1 := three_dvd_two_pow_add_one_of_odd hodd
  have h3 : 3 * ((2 ^ ((4 * s + 2) - 1) + 1) / 3) = 2 ^ ((4 * s + 2) - 1) + 1 :=
    Nat.mul_div_cancel' hdiv
  have : 2 ^ ((4 * s + 2) - 1) + 1 < 3 * 2 ^ ((4 * s + 2) - 1) := by
    have h1 : 1 ≤ 2 ^ ((4 * s + 2) - 1) := Nat.one_le_two_pow
    omega
  have : 3 * ((2 ^ ((4 * s + 2) - 1) + 1) / 3) < 3 * 2 ^ ((4 * s + 2) - 1) := by
    rwa [h3]
  exact Nat.lt_of_mul_lt_mul_left this

lemma Rb_lt (b : ℕ) : (4 ^ b - 1) / 3 < 2 ^ (2 * b) := by
  have hdiv := three_dvd_four_pow_sub_one b
  have hmul : 3 * ((4 ^ b - 1) / 3) = 4 ^ b - 1 := Nat.mul_div_cancel' hdiv
  have hlt : 4 ^ b - 1 < 4 ^ b := Nat.sub_lt (Nat.one_le_pow _ _ (by decide)) (by decide)
  have hlt3 : 4 ^ b - 1 < 3 * 4 ^ b :=
    lt_of_lt_of_le hlt (Nat.le_mul_of_pos_left _ (by decide : 0 < 3))
  have hmul_lt : 3 * ((4 ^ b - 1) / 3) < 3 * 4 ^ b := by
    rwa [hmul]
  have hlt4 : (4 ^ b - 1) / 3 < 4 ^ b := Nat.lt_of_mul_lt_mul_left hmul_lt
  simpa [four_pow_eq] using hlt4

lemma popc_add_two_pow_mul {a b i : ℕ} (hb : b < 2 ^ i) :
    popc (b + 2 ^ i * a) = popc a + popc b := by
  rw [add_comm b]
  exact popc_two_pow_mul_add hb

lemma popc_one_add_two_pow_mul {q g : ℕ} (hq : q < 2 ^ g) :
    popc (q * (1 + 2 ^ g)) = 2 * popc q := by
  have hdecomp : q * (1 + 2 ^ g) = q + 2 ^ g * q := by ring
  rw [hdecomp, popc_add_two_pow_mul hq]
  omega

lemma Rb_mul_lt (b g : ℕ) :
    ((4 ^ b - 1) / 3) * (1 + 2 ^ g) < 2 ^ (2 * b + g + 1) := by
  set Rb := (4 ^ b - 1) / 3
  have hRb : Rb < 2 ^ (2 * b) := Rb_lt b
  have h1b : 1 ≤ (2 : ℕ) ^ (2 * b) := Nat.one_le_two_pow
  have hpos : 0 < 1 + (2 : ℕ) ^ g := Nat.add_pos_left (by decide) _
  have hmul_lt : Rb * (1 + 2 ^ g) < 2 ^ (2 * b) * (1 + 2 ^ g) :=
    Nat.mul_lt_mul_of_pos_right hRb hpos
  have hsplit : 2 ^ (2 * b) * (1 + 2 ^ g) = 2 ^ (2 * b) + 2 ^ (2 * b + g) := by
    rw [mul_add, mul_one, ← pow_add]
  have hle : 2 ^ (2 * b) + 2 ^ (2 * b + g) ≤ 2 ^ (2 * b + g + 1) := by
    have hpow : 2 ^ (2 * b) ≤ 2 ^ (2 * b + g) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ (2 * b + g) + 2 ^ (2 * b + g) = 2 ^ (2 * b + g + 1) := by
      rw [← two_mul, ← Nat.pow_succ']
    omega
  omega

lemma popc_Qs_one_add (s : ℕ) :
    popc (((2 ^ ((4 * s + 2) - 1) + 1) / 3) * (1 + 2 ^ (4 * s + 2))) % 2 = 0 := by
  set g := 4 * s + 2
  set Qs := (2 ^ (g - 1) + 1) / 3
  have hQslt : Qs < 2 ^ g := by
    have hlt : Qs < 2 ^ (g - 1) := by simpa [Qs, g] using Qg_lt s
    have hle : 2 ^ (g - 1) ≤ 2 ^ g := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have : popc (Qs * (1 + 2 ^ g)) = 2 * popc Qs := popc_one_add_two_pow_mul hQslt
  omega

lemma popc_Qbig_mul_even_gap {b g : ℕ} (_hb : 1 ≤ b) (hgeven : g % 2 = 0) (hg2 : 2 ≤ g)
    (hcond : g / 2 ≤ b → b % 2 = (g / 2) % 2) :
    popc (((2 ^ (2 * (b + g)) + 2 ^ ((b + g) + b + 1) + (2 ^ (2 * b) - 1)) / 3) *
      (1 + 2 ^ g)) % 2 = 0 := by
  set ea := b + g
  set Rb := (4 ^ b - 1) / 3
  set Qs := (2 ^ (g - 1) + 1) / 3
  -- reuse the algebraic split, specialized from `Qbig_eq`
  have hsplit :
      (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) / 3 =
        Rb + 2 ^ (2 * b + g + 1) * Qs := by
    have hg' : g = 4 * (g / 4) + g % 4 := by omega
    -- prove the identity directly (same as Qbig_eq, for general even g)
    have hdivR : 3 ∣ 4 ^ b - 1 := three_dvd_four_pow_sub_one b
    have hodd : (g - 1) % 2 = 1 := by omega
    have hdivS : 3 ∣ 2 ^ (g - 1) + 1 := three_dvd_two_pow_add_one_of_odd hodd
    have h4 : (4 : ℕ) ^ b = 2 ^ (2 * b) := four_pow_eq b
    have hid :
        2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) =
          (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by
      have hpow1 : 2 ^ (2 * b + g + 1) * 2 ^ (g - 1) = 2 ^ (2 * ea) := by
        rw [← pow_add]; congr 1; omega
      have hpow2 : 2 ^ (2 * b + g + 1) = 2 ^ (ea + b + 1) := by
        congr 1; omega
      calc
        2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) =
            2 ^ (2 * b + g + 1) * 2 ^ (g - 1) + 2 ^ (2 * b + g + 1) +
              (2 ^ (2 * b) - 1) := by rw [hpow1, hpow2]
        _ = 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) + (2 ^ (2 * b) - 1) := by ring
        _ = 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) + (4 ^ b - 1) := by rw [h4]
        _ = (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by ring
    have hdiv :
        3 ∣ 2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) := by
      have : 3 ∣ (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) :=
        hdivR.add (hdivS.mul_left _)
      simpa using (hid.symm ▸ this)
    apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
    have lhs :
        3 * ((2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) / 3) =
          2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) :=
      Nat.mul_div_cancel' hdiv
    have rhs :
        3 * (Rb + 2 ^ (2 * b + g + 1) * Qs) =
          (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by
      rw [mul_add, Nat.mul_div_cancel' hdivR]
      have :
          3 * (2 ^ (2 * b + g + 1) * Qs) =
            2 ^ (2 * b + g + 1) * (3 * Qs) := by ring
      rw [this, show 3 * Qs = 2 ^ (g - 1) + 1 from Nat.mul_div_cancel' hdivS]
    rw [lhs, rhs]
    exact hid
  rw [hsplit]
  have hdecomp :
      (Rb + 2 ^ (2 * b + g + 1) * Qs) * (1 + 2 ^ g) =
        Rb * (1 + 2 ^ g) + 2 ^ (2 * b + g + 1) * (Qs * (1 + 2 ^ g)) := by
    ring
  rw [hdecomp]
  have hlow_lt : Rb * (1 + 2 ^ g) < 2 ^ (2 * b + g + 1) := by
    simpa [Rb] using Rb_mul_lt b g
  have hsum :
      popc (Rb * (1 + 2 ^ g) + 2 ^ (2 * b + g + 1) * (Qs * (1 + 2 ^ g))) =
        popc (Qs * (1 + 2 ^ g)) + popc (Rb * (1 + 2 ^ g)) :=
    popc_add_two_pow_mul hlow_lt
  rw [hsum]
  have hQs_even : popc (Qs * (1 + 2 ^ g)) % 2 = 0 := by
    have hQslt : Qs < 2 ^ g := by
      have hdiv : 3 ∣ 2 ^ (g - 1) + 1 :=
        three_dvd_two_pow_add_one_of_odd (by omega)
      have h3 : 3 * Qs = 2 ^ (g - 1) + 1 := Nat.mul_div_cancel' hdiv
      have hlt0 : 2 ^ (g - 1) + 1 < 3 * 2 ^ (g - 1) := by
        have h1 : 1 ≤ 2 ^ (g - 1) := Nat.one_le_two_pow
        omega
      have : 3 * Qs < 3 * 2 ^ (g - 1) := by rwa [h3]
      have : Qs < 2 ^ (g - 1) := Nat.lt_of_mul_lt_mul_left this
      have : 2 ^ (g - 1) ≤ 2 ^ g := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have : popc (Qs * (1 + 2 ^ g)) = 2 * popc Qs := popc_one_add_two_pow_mul hQslt
    omega
  have hlow_even : popc (Rb * (1 + 2 ^ g)) % 2 = 0 := by
    by_cases ht : g / 2 ≤ b
    · have hpar : b % 2 = (g / 2) % 2 := hcond ht
      have hfour : (2 : ℕ) ^ g = 4 ^ (g / 2) := by
        calc (2 : ℕ) ^ g
            = 2 ^ (2 * (g / 2)) := by congr 1; omega
          _ = (2 ^ 2) ^ (g / 2) := (pow_mul (2 : ℕ) 2 (g / 2))
          _ = 4 ^ (g / 2) := rfl
      have hpop : popc (Rb * (1 + 2 ^ g)) = b + g / 2 := by
        rw [hfour]
        simpa [Rb] using popc_R_mul_one_add_four_pow (t := g / 2) ht
      rw [hpop]
      omega
    · have hgt : b < g / 2 := by omega
      have hdecomp' : Rb * (1 + 2 ^ g) = Rb + 2 ^ g * Rb := by ring
      rw [hdecomp']
      have hRblt : Rb < 2 ^ g := by
        have hRb2 : Rb < 2 ^ (2 * b) := Rb_lt b
        have h2bg : 2 * b < g := by omega
        have hpow : 2 ^ (2 * b) ≤ 2 ^ g :=
          Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h2bg)
        omega
      rw [popc_add_two_pow_mul hRblt]
      omega
  omega

lemma popc_odd_part_choose_three_even_gap {ea b : ℕ}
    (hba : b < ea) (hb : 1 ≤ b) (heven : (ea - b) % 2 = 0) (hne : 2 ≤ ea - b)
    (hcond : (ea - b) / 2 ≤ b → b % 2 = ((ea - b) / 2) % 2) :
    popc (((2 ^ ea + 2 ^ b + 1) * (2 ^ (ea - b) + 1) * (2 ^ ea + 2 ^ b - 1)) / 3) % 2 = 0 := by
  set g := ea - b
  have hea : ea = b + g := by omega
  have hprod := sq_sub_one_of_three_bit ea b
  have hrewrite :
      ((2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1)) / 3 =
        ((2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) / 3) * (1 + 2 ^ g) := by
    have hmul :
        (2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1) =
          (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) * (1 + 2 ^ g) := by
      calc
        (2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1) =
            ((2 ^ ea + 2 ^ b + 1) * (2 ^ ea + 2 ^ b - 1)) * (1 + 2 ^ g) := by ring
        _ = (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) * (1 + 2 ^ g) := by
              rw [hprod]
    -- 3 divides the square-difference because g is even
    have hdivR : 3 ∣ 4 ^ b - 1 := three_dvd_four_pow_sub_one b
    have hodd : (g - 1) % 2 = 1 := by omega
    have hdivS : 3 ∣ 2 ^ (g - 1) + 1 := three_dvd_two_pow_add_one_of_odd hodd
    have h4 : (4 : ℕ) ^ b = 2 ^ (2 * b) := four_pow_eq b
    have hid :
        2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) =
          (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by
      have hpow1 : 2 ^ (2 * b + g + 1) * 2 ^ (g - 1) = 2 ^ (2 * ea) := by
        rw [← pow_add]; congr 1; omega
      have hpow2 : 2 ^ (2 * b + g + 1) = 2 ^ (ea + b + 1) := by
        congr 1; omega
      calc
        2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) =
            2 ^ (2 * b + g + 1) * 2 ^ (g - 1) + 2 ^ (2 * b + g + 1) +
              (2 ^ (2 * b) - 1) := by rw [hpow1, hpow2]
        _ = 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) + (2 ^ (2 * b) - 1) := by ring
        _ = 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) + (4 ^ b - 1) := by rw [h4]
        _ = (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by ring
    have hdiv :
        3 ∣ 2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) := by
      have : 3 ∣ (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) :=
        hdivR.add (hdivS.mul_left _)
      simpa using (hid.symm ▸ this)
    rw [hmul, mul_comm (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)),
      Nat.mul_div_assoc _ hdiv, mul_comm]
  rw [hrewrite, hea]
  exact popc_Qbig_mul_even_gap hb heven hne (by simpa [g] using hcond)

/-! ### Even 3-bit: `C(n,2)` when the odd part sits below the valuation. -/

lemma two_pow_succ_eq (n : ℕ) : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by
  rw [pow_succ, mul_comm]

lemma m_sq_three_bit (A B : ℕ) :
    (2 ^ A + 2 ^ B + 1) * (2 ^ A + 2 ^ B + 1) =
      2 ^ (2 * A) + 2 ^ (2 * B) + 1 + 2 ^ (A + B + 1) + 2 ^ (A + 1) + 2 ^ (B + 1) := by
  have hA : (2 : ℕ) ^ (A + 1) = 2 * 2 ^ A := two_pow_succ_eq A
  have hB : (2 : ℕ) ^ (B + 1) = 2 * 2 ^ B := two_pow_succ_eq B
  have hAB : (2 : ℕ) ^ (A + B + 1) = 2 * 2 ^ A * 2 ^ B := by
    rw [show A + B + 1 = (A + B) + 1 from rfl, two_pow_succ_eq, pow_add]
    ring
  have h2A : (2 : ℕ) ^ (2 * A) = 2 ^ A * 2 ^ A := by
    rw [two_mul, pow_add]
  have h2B : (2 : ℕ) ^ (2 * B) = 2 ^ B * 2 ^ B := by
    rw [two_mul, pow_add]
  rw [hA, hB, hAB, h2A, h2B]
  ring

lemma two_pow_sub_ones_sub_two {e A B : ℕ} (hA : A < e) (hB : B < e) (hAB : A ≠ B) :
    2 ^ e - 1 - 2 ^ A - 2 ^ B =
      ∑ i ∈ (Finset.range e \ {A, B}), (2 : ℕ) ^ i := by
  have hr : ∑ i ∈ Finset.range e, (2 : ℕ) ^ i = 2 ^ e - 1 := geom_sum_pow_two e
  have hAin : A ∈ Finset.range e := by simp [hA]
  have hBin : B ∈ Finset.range e := by simp [hB]
  have hss : ({A, B} : Finset ℕ) ⊆ Finset.range e := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hAin, hBin]
  have hsum :
      ∑ i ∈ Finset.range e, (2 : ℕ) ^ i =
        ∑ i ∈ {A, B}, (2 : ℕ) ^ i + ∑ i ∈ Finset.range e \ {A, B}, 2 ^ i := by
    rw [← Finset.sum_sdiff hss, add_comm]
  have hsumAB : ∑ i ∈ ({A, B} : Finset ℕ), (2 : ℕ) ^ i = 2 ^ A + 2 ^ B := by
    simp [Finset.sum_pair hAB]
  have h1 : 1 ≤ (2 : ℕ) ^ e := Nat.one_le_two_pow
  have hleAB : 2 ^ A + 2 ^ B ≤ 2 ^ e - 1 := by
    have hle :=
      Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => (2 : ℕ) ^ i) hss
        (fun _ _ _ => Nat.zero_le _)
    omega
  have : (2 : ℕ) ^ e - 1 - 2 ^ A - 2 ^ B =
      (∑ i ∈ Finset.range e, (2 : ℕ) ^ i) - (2 ^ A + 2 ^ B) := by
    omega
  rw [this, hsum, hsumAB, Nat.add_sub_cancel_left]


lemma popc_two_pow_sub_ones_sub_two {e A B : ℕ}
    (hA : A < e) (hB : B < e) (hAB : A ≠ B) :
    popc (2 ^ e - 1 - 2 ^ A - 2 ^ B) = e - 2 := by
  rw [two_pow_sub_ones_sub_two hA hB hAB, popc_sum_two_pow_finset]
  have hAin : A ∈ Finset.range e := by simp [hA]
  have hBin : B ∈ Finset.range e := by simp [hB]
  have hss : ({A, B} : Finset ℕ) ⊆ Finset.range e := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hAin, hBin]
  have hinter : ({A, B} : Finset ℕ) ∩ Finset.range e = {A, B} := by
    rw [Finset.inter_comm, Finset.inter_eq_right.mpr hss]
  rw [Finset.card_sdiff, hinter, Finset.card_range]
  have hcard : ({A, B} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [hAB]
  omega

lemma choose_two_of_even_three_bit {e A B : ℕ} (he : 1 ≤ e) :
    Nat.choose (2 ^ e * (2 ^ A + 2 ^ B + 1)) 2 =
      2 ^ (e - 1) * ((2 ^ A + 2 ^ B + 1) * (2 ^ e * (2 ^ A + 2 ^ B + 1) - 1)) := by
  set m := 2 ^ A + 2 ^ B + 1
  set n := 2 ^ e * m
  have hm1 : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le _)
  have hn2 : 2 ≤ n := by
    have h2 : 2 ≤ 2 ^ e := by
      have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
      simpa using this
    have : 2 ^ e ≤ 2 ^ e * m := Nat.le_mul_of_pos_right _ hm1
    exact h2.trans this
  rw [Nat.choose_two_right]
  have hnm : n * (n - 1) = 2 ^ e * (m * (n - 1)) := by
    rw [show n = 2 ^ e * m from rfl]
    ring
  have he2 : 2 ^ e = 2 * 2 ^ (e - 1) := by
    have : e = e - 1 + 1 := by omega
    rw [this, two_pow_succ_eq, Nat.add_sub_cancel]
  have hdiv : n * (n - 1) / 2 = 2 ^ (e - 1) * (m * (n - 1)) := by
    have : n * (n - 1) = 2 * (2 ^ (e - 1) * (m * (n - 1))) := by
      rw [hnm, he2]
      ring
    rw [this, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  have hnm1 : n - 1 = 2 ^ e * m - 1 := rfl
  rw [hdiv, hnm1]

lemma mul_shift_sub_eq {e A B : ℕ} :
    (2 ^ A + 2 ^ B + 1) * (2 ^ e * (2 ^ A + 2 ^ B + 1) - 1) =
      2 ^ e * ((2 ^ A + 2 ^ B + 1) * (2 ^ A + 2 ^ B + 1)) - (2 ^ A + 2 ^ B + 1) := by
  set m := 2 ^ A + 2 ^ B + 1
  have : m * (2 ^ e * m - 1) = m * (2 ^ e * m) - m * 1 :=
    Nat.mul_sub_left_distrib m (2 ^ e * m) 1
  rw [this, mul_one]
  ring

lemma m_sq_shift_sub {e A B : ℕ} :
    2 ^ e * ((2 ^ A + 2 ^ B + 1) * (2 ^ A + 2 ^ B + 1)) - (2 ^ A + 2 ^ B + 1) =
      2 ^ e * (2 ^ (2 * A) + 2 ^ (2 * B) + 1 + 2 ^ (A + B + 1) + 2 ^ (A + 1) +
        2 ^ (B + 1)) - (2 ^ A + 2 ^ B + 1) := by
  rw [m_sq_three_bit A B]

lemma two_pow_add_two_le_of_lt {e A B : ℕ}
    (hA : A < e) (hB : B < e) (hAB : A ≠ B) :
    2 ^ A + 2 ^ B + 1 ≤ 2 ^ e := by
  have he2 : 2 ≤ e := by
    have : 1 ≤ e := by
      cases e with
      | zero =>
        exact False.elim (Nat.not_lt_zero _ hA)
      | succ _ => omega
    have : ¬ (A = 0 ∧ B = 0) := by
      intro h; exact hAB (h.1.trans h.2.symm)
    omega
  wlog hBA : B < A generalizing A B
  · have hlt : A < B := lt_of_le_of_ne (Nat.le_of_not_lt hBA) hAB
    simpa [add_comm (2 ^ A)] using this hB hA hAB.symm hlt
  have hAe : 2 ^ A ≤ 2 ^ (e - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hBe : 2 ^ B ≤ 2 ^ (e - 2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hsum : 2 ^ (e - 1) + 2 ^ (e - 2) + 1 ≤ 2 ^ e := by
    have hsplit : 2 ^ e = 2 * 2 ^ (e - 1) := by
      calc 2 ^ e = 2 ^ (e - 1 + 1) := by congr 1; omega
        _ = 2 * 2 ^ (e - 1) := two_pow_succ_eq _
    have hdouble : 2 * 2 ^ (e - 1) = 2 ^ (e - 1) + 2 ^ (e - 1) := two_mul _
    have hhalf : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := by
      calc 2 ^ (e - 1) = 2 ^ (e - 2 + 1) := by congr 1; omega
        _ = 2 * 2 ^ (e - 2) := two_pow_succ_eq _
    have hdouble' : 2 * 2 ^ (e - 2) = 2 ^ (e - 2) + 2 ^ (e - 2) := two_mul _
    have hone : 1 ≤ 2 ^ (e - 2) := Nat.one_le_two_pow
    omega
  omega

lemma high_plus_low_of_even_three_bit {e A B : ℕ}
    (hA : A < e) (hB : B < e) (hAB : A ≠ B) :
    2 ^ e * (2 ^ (2 * A) + 2 ^ (2 * B) + 1 + 2 ^ (A + B + 1) + 2 ^ (A + 1) +
        2 ^ (B + 1)) - (2 ^ A + 2 ^ B + 1) =
      2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
        2 ^ (e + A + 1) + 2 ^ (e + B + 1) + (2 ^ e - 1 - 2 ^ A - 2 ^ B) := by
  have hleAB : 2 ^ A + 2 ^ B + 1 ≤ 2 ^ e := two_pow_add_two_le_of_lt hA hB hAB
  have hdist :
      2 ^ e * (2 ^ (2 * A) + 2 ^ (2 * B) + 1 + 2 ^ (A + B + 1) + 2 ^ (A + 1) +
          2 ^ (B + 1)) =
        2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ e + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) := by
    simp only [mul_add, mul_one]
    simp [← pow_add]
    ac_rfl
  rw [hdist]
  have hle' : 2 ^ A + 2 ^ B + 1 ≤
      2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ e + 2 ^ (e + A + B + 1) +
        2 ^ (e + A + 1) + 2 ^ (e + B + 1) := by
    have hpos : 2 ^ e ≤
        2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ e + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) := by
      have h1 : 1 ≤ (2 : ℕ) ^ (e + 2 * A) := Nat.one_le_two_pow
      have h2 : 1 ≤ (2 : ℕ) ^ (e + 2 * B) := Nat.one_le_two_pow
      have h3 : 1 ≤ (2 : ℕ) ^ (e + A + B + 1) := Nat.one_le_two_pow
      have h4 : 1 ≤ (2 : ℕ) ^ (e + A + 1) := Nat.one_le_two_pow
      have h5 : 1 ≤ (2 : ℕ) ^ (e + B + 1) := Nat.one_le_two_pow
      omega
    exact hleAB.trans hpos
  have hrearr :
      2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ e + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) - (2 ^ A + 2 ^ B + 1) =
        2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) + (2 ^ e - (2 ^ A + 2 ^ B + 1)) := by
    omega
  rw [hrearr]
  congr 1
  omega


lemma five_high_eq {e A B : ℕ} :
    2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
      2 ^ (e + A + 1) + 2 ^ (e + B + 1) =
    2 ^ (e + 2 * A) + 2 ^ (e + (A + B + 1)) + 2 ^ (e + (A + 1)) +
      2 ^ (e + 2 * B) + 2 ^ (e + (B + 1)) := by
  ring

lemma exponents_five_order_gt {A B : ℕ}
    (hAB : B + 2 ≤ A) (hB : 2 ≤ B) (hne : A ≠ 2 * B - 1) (hgt : 2 * B < A + 1) :
    B + 1 < 2 * B ∧ 2 * B < A + 1 ∧ A + 1 < A + B + 1 ∧ A + B + 1 < 2 * A := by
  omega

lemma exponents_five_order_lt {A B : ℕ}
    (hAB : B + 2 ≤ A) (hB : 2 ≤ B) (hne : A ≠ 2 * B - 1) (hlt : A + 1 < 2 * B) :
    B + 1 < A + 1 ∧ A + 1 < 2 * B ∧ 2 * B < A + B + 1 ∧ A + B + 1 < 2 * A := by
  omega

lemma popc_sum_two_pow_distinct {i j : ℕ} (hij : j < i) :
    popc (2 ^ i + 2 ^ j) = 2 := by
  have hb : 2 ^ j < 2 ^ i := Nat.pow_lt_pow_right (by decide : 1 < 2) hij
  have : 2 ^ i + 2 ^ j = 2 ^ i * 1 + 2 ^ j := by ring
  rw [this, popc_two_pow_mul_add hb, popc_one, popc_two_pow]

lemma two_pow_add_lt_of_lt {i j : ℕ} (h : j < i) : 2 ^ j < 2 ^ i :=
  Nat.pow_lt_pow_right (by decide : 1 < 2) h

lemma popc_sum_five_pow {e1 e2 e3 e4 e5 : ℕ}
    (h12 : e2 < e1) (h23 : e3 < e2) (h34 : e4 < e3) (h45 : e5 < e4) :
    popc (2 ^ e1 + 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5) = 5 := by
  have hle4 : 2 ^ e4 + 2 ^ e5 < 2 ^ e3 := by
    have : 2 ^ e5 < 2 ^ e4 := two_pow_add_lt_of_lt h45
    have : 2 ^ e4 + 2 ^ e5 < 2 ^ e4 + 2 ^ e4 := Nat.add_lt_add_left this _
    have : 2 ^ e4 + 2 ^ e4 = 2 ^ (e4 + 1) := by
      rw [← two_mul, ← two_pow_succ_eq]
    have : 2 ^ (e4 + 1) ≤ 2 ^ e3 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hle3 : 2 ^ e3 + 2 ^ e4 + 2 ^ e5 < 2 ^ e2 := by
    have : 2 ^ e3 + (2 ^ e4 + 2 ^ e5) < 2 ^ e3 + 2 ^ e3 :=
      Nat.add_lt_add_left hle4 _
    have : 2 ^ e3 + 2 ^ e3 = 2 ^ (e3 + 1) := by
      rw [← two_mul, ← two_pow_succ_eq]
    have : 2 ^ (e3 + 1) ≤ 2 ^ e2 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hle2 : 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 < 2 ^ e1 := by
    have : 2 ^ e2 + (2 ^ e3 + 2 ^ e4 + 2 ^ e5) < 2 ^ e2 + 2 ^ e2 :=
      Nat.add_lt_add_left hle3 _
    have : 2 ^ e2 + 2 ^ e2 = 2 ^ (e2 + 1) := by
      rw [← two_mul, ← two_pow_succ_eq]
    have : 2 ^ (e2 + 1) ≤ 2 ^ e1 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hform1 : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 =
      2 ^ e1 * 1 + (2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5) := by ring
  rw [hform1, popc_two_pow_mul_add hle2, popc_one]
  have hform2 : 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 =
      2 ^ e2 * 1 + (2 ^ e3 + 2 ^ e4 + 2 ^ e5) := by ring
  rw [hform2, popc_two_pow_mul_add hle3, popc_one]
  have hform3 : 2 ^ e3 + 2 ^ e4 + 2 ^ e5 =
      2 ^ e3 * 1 + (2 ^ e4 + 2 ^ e5) := by ring
  rw [hform3, popc_two_pow_mul_add hle4, popc_one, popc_sum_two_pow_distinct h45]

lemma popc_five_high {e A B : ℕ}
    (hAB : B + 2 ≤ A) (hB : 2 ≤ B) (hne : A ≠ 2 * B - 1) :
    popc (2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
      2 ^ (e + A + 1) + 2 ^ (e + B + 1)) = 5 := by
  have hne' : A + 1 ≠ 2 * B := by
    intro h
    apply hne
    omega
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have : 2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
        2 ^ (e + A + 1) + 2 ^ (e + B + 1) =
      2 ^ (e + 2 * A) + 2 ^ (e + (A + B + 1)) + 2 ^ (e + 2 * B) +
        2 ^ (e + (A + 1)) + 2 ^ (e + (B + 1)) := by ring
    rw [this]
    exact popc_sum_five_pow
      (e1 := e + 2 * A) (e2 := e + (A + B + 1)) (e3 := e + 2 * B)
      (e4 := e + (A + 1)) (e5 := e + (B + 1))
      (by omega) (by omega) (by omega) (by omega)
  · have : 2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
        2 ^ (e + A + 1) + 2 ^ (e + B + 1) =
      2 ^ (e + 2 * A) + 2 ^ (e + (A + B + 1)) + 2 ^ (e + (A + 1)) +
        2 ^ (e + 2 * B) + 2 ^ (e + (B + 1)) := by ring
    rw [this]
    exact popc_sum_five_pow
      (e1 := e + 2 * A) (e2 := e + (A + B + 1)) (e3 := e + (A + 1))
      (e4 := e + 2 * B) (e5 := e + (B + 1))
      (by omega) (by omega) (by omega) (by omega)

lemma low_lt_high_start {e A B : ℕ} (hA : A < e) (hB : B < e) (hAB : A ≠ B) :
    2 ^ e - 1 - 2 ^ A - 2 ^ B < 2 ^ (e + B + 1) := by
  have h1 : 1 ≤ (2 : ℕ) ^ e := Nat.one_le_two_pow
  have hle : 2 ^ A + 2 ^ B + 1 ≤ 2 ^ e := two_pow_add_two_le_of_lt hA hB hAB
  have heq : 2 ^ e - 1 - 2 ^ A - 2 ^ B = 2 ^ e - (2 ^ A + 2 ^ B + 1) := by
    have hA1 : 1 ≤ (2 : ℕ) ^ A := Nat.one_le_two_pow
    have hB1 : 1 ≤ (2 : ℕ) ^ B := Nat.one_le_two_pow
    omega
  rw [heq]
  have hbound : 2 ^ e - (2 ^ A + 2 ^ B + 1) ≤ 2 ^ e := Nat.sub_le _ _
  have hpow : 2 ^ e < 2 ^ (e + B + 1) :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  omega

lemma popc_odd_part_even_three_bit_easy {e A B : ℕ}
    (heA : A < e) (hB : 2 ≤ B) (hAB : B + 2 ≤ A) (hne : A ≠ 2 * B - 1) :
    popc ((2 ^ A + 2 ^ B + 1) * (2 ^ e * (2 ^ A + 2 ^ B + 1) - 1)) = e + 3 := by
  have hBlt : B < e := by omega
  have hAB' : A ≠ B := by omega
  have hform := mul_shift_sub_eq (e := e) (A := A) (B := B)
  rw [hform, m_sq_shift_sub, high_plus_low_of_even_three_bit heA hBlt hAB']
  have hlow_lt : 2 ^ e - 1 - 2 ^ A - 2 ^ B < 2 ^ (e + B + 1) :=
    low_lt_high_start heA hBlt hAB'
  have hhigh_mul :
      2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) =
        2 ^ (e + B + 1) *
          (2 ^ (e + 2 * A - (e + B + 1)) + 2 ^ (e + 2 * B - (e + B + 1)) +
            2 ^ (e + A + B + 1 - (e + B + 1)) + 2 ^ (e + A + 1 - (e + B + 1)) +
            1) := by
    have h1 : 2 ^ (e + 2 * A) = 2 ^ (e + B + 1) * 2 ^ (e + 2 * A - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have h2 : 2 ^ (e + 2 * B) = 2 ^ (e + B + 1) * 2 ^ (e + 2 * B - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have h3 : 2 ^ (e + A + B + 1) =
        2 ^ (e + B + 1) * 2 ^ (e + A + B + 1 - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have h4 : 2 ^ (e + A + 1) =
        2 ^ (e + B + 1) * 2 ^ (e + A + 1 - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have h5 : 2 ^ (e + B + 1) = 2 ^ (e + B + 1) * 1 := by ring
    rw [h1, h2, h3, h4, h5]
    ring
  have hsplit :
      2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) + (2 ^ e - 1 - 2 ^ A - 2 ^ B) =
        2 ^ (e + B + 1) *
          (2 ^ (e + 2 * A - (e + B + 1)) + 2 ^ (e + 2 * B - (e + B + 1)) +
            2 ^ (e + A + B + 1 - (e + B + 1)) + 2 ^ (e + A + 1 - (e + B + 1)) +
            1) + (2 ^ e - 1 - 2 ^ A - 2 ^ B) := by
    rw [hhigh_mul]
  rw [hsplit, popc_two_pow_mul_add hlow_lt]
  have hcoeff :
      popc (2 ^ (e + 2 * A - (e + B + 1)) + 2 ^ (e + 2 * B - (e + B + 1)) +
        2 ^ (e + A + B + 1 - (e + B + 1)) + 2 ^ (e + A + 1 - (e + B + 1)) +
        1) = 5 := by
    rw [← popc_mul_two_pow (e + B + 1), ← hhigh_mul]
    exact popc_five_high (e := e) hAB hB hne
  rw [hcoeff, popc_two_pow_sub_ones_sub_two heA hBlt hAB']
  omega

lemma popc_choose_two_even_three_bit_easy {e A B : ℕ}
    (he : 1 ≤ e) (heA : A < e) (hB : 2 ≤ B) (hAB : B + 2 ≤ A)
    (hne : A ≠ 2 * B - 1) (hodd : e % 2 = 1) :
    popc (Nat.choose (2 ^ e * (2 ^ A + 2 ^ B + 1)) 2) % 2 = 0 := by
  rw [choose_two_of_even_three_bit he, popc_mul_two_pow]
  have hpop := popc_odd_part_even_three_bit_easy heA hB hAB hne
  omega

lemma three_bit_even_factor {e1 e2 e3 : ℕ} (h32 : e3 < e2) (h21 : e2 < e1) :
    2 ^ e1 + 2 ^ e2 + 2 ^ e3 =
      2 ^ e3 * (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) := by
  have h31 : e3 < e1 := h32.trans h21
  have h1 : 2 ^ e1 = 2 ^ e3 * 2 ^ (e1 - e3) := by
    rw [← pow_add]; congr 1; omega
  have h2 : 2 ^ e2 = 2 ^ e3 * 2 ^ (e2 - e3) := by
    rw [← pow_add]; congr 1; omega
  rw [h1, h2]
  ring

lemma high_adjacent_merge {e B : ℕ} :
    2 ^ (e + 2 * (B + 1)) + 2 ^ (e + 2 * B) + 2 ^ (e + (B + 1) + B + 1) +
      2 ^ (e + (B + 1) + 1) + 2 ^ (e + B + 1) =
    2 ^ (e + 2 * B + 3) + 2 ^ (e + 2 * B) + 2 ^ (e + B + 2) + 2 ^ (e + B + 1) := by
  have hA : 2 * (B + 1) = 2 * B + 2 := by omega
  have hAB : (B + 1) + B + 1 = 2 * B + 2 := by omega
  have hA1 : (B + 1) + 1 = B + 2 := by omega
  have h2 : 2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B + 2) = 2 ^ (e + 2 * B + 3) := by
    rw [← two_mul, ← two_pow_succ']
  -- after rewriting exponents, two copies of 2^{e+2B+2}
  have : 2 ^ (e + 2 * (B + 1)) = 2 ^ (e + 2 * B + 2) := by congr 1; omega
  have : 2 ^ (e + (B + 1) + B + 1) = 2 ^ (e + 2 * B + 2) := by congr 1; omega
  have : 2 ^ (e + (B + 1) + 1) = 2 ^ (e + B + 2) := by congr 1; omega
  omega

lemma popc_four_high_adjacent {e B : ℕ} (hB : 3 ≤ B) :
    popc (2 ^ (e + 2 * B + 3) + 2 ^ (e + 2 * B) + 2 ^ (e + B + 2) +
      2 ^ (e + B + 1)) = 4 := by
  have h1 : e + B + 1 < e + B + 2 := by omega
  have h2 : e + B + 2 < e + 2 * B := by omega
  have h3 : e + 2 * B < e + 2 * B + 3 := by omega
  exact popc_sum_four_pow (e1 := e + 2 * B + 3) (e2 := e + 2 * B)
    (e3 := e + B + 2) (e4 := e + B + 1) h3 h2 h1

-- Tmp may not have popc_sum_four_pow; define if needed
lemma popc_sum_four_pow {e1 e2 e3 e4 : ℕ}
    (h12 : e2 < e1) (h23 : e3 < e2) (h34 : e4 < e3) :
    popc (2 ^ e1 + 2 ^ e2 + 2 ^ e3 + 2 ^ e4) = 4 := by
  have hle3 : 2 ^ e3 + 2 ^ e4 < 2 ^ e2 := by
    have : 2 ^ e4 < 2 ^ e3 := two_pow_add_lt_of_lt h34
    have : 2 ^ e3 + 2 ^ e4 < 2 ^ e3 + 2 ^ e3 := Nat.add_lt_add_left this _
    have : 2 ^ e3 + 2 ^ e3 = 2 ^ (e3 + 1) := by rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e3 + 1) ≤ 2 ^ e2 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hle2 : 2 ^ e2 + 2 ^ e3 + 2 ^ e4 < 2 ^ e1 := by
    have : 2 ^ e2 + (2 ^ e3 + 2 ^ e4) < 2 ^ e2 + 2 ^ e2 := Nat.add_lt_add_left hle3 _
    have : 2 ^ e2 + 2 ^ e2 = 2 ^ (e2 + 1) := by rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e2 + 1) ≤ 2 ^ e1 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hform1 : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 + 2 ^ e4 =
      2 ^ e1 * 1 + (2 ^ e2 + 2 ^ e3 + 2 ^ e4) := by ring
  rw [hform1, popc_two_pow_mul_add hle2, popc_one]
  have hform2 : 2 ^ e2 + 2 ^ e3 + 2 ^ e4 = 2 ^ e2 * 1 + (2 ^ e3 + 2 ^ e4) := by ring
  rw [hform2, popc_two_pow_mul_add hle3, popc_one, popc_sum_two_pow_distinct h34]

