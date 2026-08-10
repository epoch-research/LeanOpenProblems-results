import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A060957: Number of different products (including the empty product) of any subset of $\{1, 2, 3, \dots, n\}$.
-/
def A060957 (n : ℕ) : ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id) |>.card

-- Convenience definition for the set of products
private def products (n : ℕ) : Finset ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id)

lemma Icc_eq_insert (n : ℕ) (hn : n ≥ 1) : Icc 1 n = insert n (Icc 1 (n-1)) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

lemma n_not_mem_Icc (n : ℕ) : n ∉ Icc 1 (n-1) := by
  simp only [mem_Icc]
  omega

theorem products_rec (n : ℕ) (hn : n ≥ 1) :
    products n = products (n-1) ∪ (products (n-1)).image (fun x => n * x) := by
  dsimp [products]
  rw [Icc_eq_insert n hn]
  rw [powerset_insert]
  rw [image_union]
  congr 1
  simp only [image_image]
  apply image_congr
  intro s hs
  simp at hs
  have hs_finset : s ⊆ Icc 1 (n-1) := by
    intro x hx
    have hx' : x ∈ Set.Icc 1 (n-1) := hs hx
    rwa [← coe_Icc] at hx'
  have h_not : n ∉ s := fun h => n_not_mem_Icc n (hs_finset h)
  dsimp only [Function.comp_apply]
  rw [prod_insert h_not]
  rfl

lemma div_p_eq_p_of_mem_Icc (p : ℕ) (hp : Nat.Prime p) (y : ℕ) (hy : y ∈ Icc 1 p) (h_div : p ∣ y) : y = p := by
  have hy_mem := mem_Icc.1 hy
  have h_le : p ≤ y := Nat.le_of_dvd (by omega) h_div
  omega

lemma coprime_prod_erase (p : ℕ) (hp : Nat.Prime p) (s : Finset ℕ) (hs : s ⊆ Icc 1 p) :
    Nat.Coprime p (s.erase p |>.prod id) := by
  apply Nat.Coprime.prod_right
  intro i hi
  rw [mem_erase] at hi
  have hi_mem : i ∈ Icc 1 p := hs hi.2
  have h_not_div : ¬ p ∣ i := by
    intro h_div
    have h_eq := div_p_eq_p_of_mem_Icc p hp i hi_mem h_div
    exact hi.1 h_eq
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 h_not_div

lemma not_p_sq_dvd_prod (p : ℕ) (hp : Nat.Prime p) (s : Finset ℕ) (hs : s ⊆ Icc 1 p) :
    ¬ p^2 ∣ s.prod id := by
  have h_coprime := coprime_prod_erase p hp s hs
  by_cases hp_mem : p ∈ s
  · have h_eq : s.prod id = p * (s.erase p).prod id := by
      conv_lhs => rw [← insert_erase hp_mem]
      rw [prod_insert (by simp)]
      rfl
    rw [h_eq]
    intro h_div
    -- we want to change p^2 to p * p
    have h_div' : p * p ∣ p * (s.erase p).prod id := by
      rwa [pow_two] at h_div
    have h_div_C : p ∣ (s.erase p).prod id := by
      rwa [mul_dvd_mul_iff_left hp.ne_zero] at h_div'
    have h_not_div := (Nat.Prime.coprime_iff_not_dvd hp).1 h_coprime
    exact h_not_div h_div_C
  · -- p ∉ s, so s.erase p = s
    have h_erase_eq : s.erase p = s := by simp [hp_mem]
    have h_coprime' : Nat.Coprime p (s.prod id) := by
      have h_temp := h_coprime
      rw [h_erase_eq] at h_temp
      exact h_temp
    intro h_div
    -- if p^2 ∣ C, then p ∣ C (since p ∣ p^2)
    have h_div_C : p ∣ s.prod id := by
      have h_p_dvd : p ∣ p^2 := dvd_pow_self p (by decide)
      exact dvd_trans h_p_dvd h_div
    have h_not_div := (Nat.Prime.coprime_iff_not_dvd hp).1 h_coprime'
    exact h_not_div h_div_C

lemma p_mul_mem_of_not_mem (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n) (s : Finset ℕ) (hs : s ⊆ Icc 1 n) (h_not_mem : p ∉ s) :
    p * s.prod id ∈ products n := by
  dsimp [products]
  rw [mem_image]
  use insert p s
  rw [mem_powerset]
  constructor
  · rw [insert_subset_iff]
    exact ⟨mem_Icc.2 ⟨hp.pos, hpn⟩, hs⟩
  · rw [prod_insert h_not_mem]
    rfl

lemma p_mul_mem_of_not_dvd (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n) (x : ℕ) (hx : x ∈ products n) (h_not_dvd : ¬ p ∣ x) :
    p * x ∈ products n := by
  dsimp [products] at hx ⊢
  rw [mem_image] at hx ⊢
  rcases hx with ⟨s, hs, h_prod⟩
  rw [mem_powerset] at hs
  simp only [mem_powerset]
  have h_not_mem : p ∉ s := by
    intro hp_mem
    have hp_dvd : p ∣ s.prod id := Finset.dvd_prod_of_mem id hp_mem
    rw [h_prod] at hp_dvd
    exact h_not_dvd hp_dvd
  use insert p s
  constructor
  · rw [insert_subset_iff]
    constructor
    · rw [mem_Icc]
      exact ⟨hp.pos, hpn⟩
    · exact hs
  · rw [prod_insert h_not_mem]
    rw [h_prod]
    rfl

theorem oeis_60957_conjecture_0_of_step (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n)
    (h_step : ∀ m a, m ∈ products n → (p^a * m) ∈ products n → a ≥ 1 → (p * m) ∈ products n)
    (m : ℕ) (a : ℕ) (hm : m ∈ products n) (hpa : (p^a * m) ∈ products n)
    (k : ℕ) (hk : 0 < k) (hka : k < a) : (p^k * m) ∈ products n := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk_zero : k = 0
    · -- k + 1 = 1
      have ha_ge_one : a ≥ 1 := by omega
      have h_pm := h_step m a hm hpa ha_ge_one
      rw [hk_zero]
      have h_pow_one : p ^ (0 + 1) * m = p * m := by
        simp only [zero_add, pow_one]
      rw [h_pow_one]
      exact h_pm
    · -- k > 0
      have hk_pos : k > 0 := by omega
      have hk_lt : k < a := by omega
      have hpk := ih hk_pos hk_lt
      have h_step_applied := h_step (p^k * m) (a - k) hpk
      have h_pa_m : p ^ (a - k) * (p ^ k * m) ∈ products n := by
        have h_eq : p ^ (a - k) * (p ^ k * m) = p^a * m := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          omega
        rwa [h_eq]
      have h_step_result := h_step_applied h_pa_m (by omega)
      have h_final_eq : p * (p ^ k * m) = p ^ (k + 1) * m := by
        rw [← mul_assoc]
        congr 1
        rw [mul_comm, ← pow_succ]
      rwa [h_final_eq] at h_step_result

lemma p_mul_mem_of_replace (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n) (s : Finset ℕ) (hs : s ⊆ Icc 1 n) (h : ℕ) (hh : h ≥ 2) (hp_prev : p^(h-1) ∈ s) (hp_curr : p^h ∉ s) (hp_curr_le : p^h ≤ n) :
    p * s.prod id ∈ products n := by
  dsimp [products]
  rw [mem_image]
  use insert (p^h) (s.erase (p^(h-1)))
  rw [mem_powerset]
  constructor
  · rw [insert_subset_iff]
    constructor
    · rw [mem_Icc]
      have hp_pos : 0 < p := hp.pos
      have h_ph_pos : 0 < p^h := Nat.pow_pos hp_pos
      exact ⟨h_ph_pos, hp_curr_le⟩
    · exact subset_trans (erase_subset _ s) hs
  · rw [prod_insert]
    · have h_eq : s.prod id = p^(h-1) * (s.erase (p^(h-1))).prod id := by
        conv_lhs => rw [← insert_erase hp_prev]
        rw [prod_insert (by simp)]
        rfl
      rw [h_eq]
      have h_pow : p * p^(h-1) = p^h := by
        rw [← pow_succ']
        congr 1
        omega
      dsimp only [id_eq]
      rw [← mul_assoc, h_pow]
      rfl
    · intro h_mem
      rw [mem_erase] at h_mem
      exact hp_curr h_mem.2


lemma replacement_step (n p : ℕ) (hp : Nat.Prime p) (s2 : Finset ℕ) (hs2 : s2 ⊆ Icc 1 n)
    (x : ℕ) (hx : x ∈ s2) (h_div : p ∣ x) (hx_p : x / p ∉ s2) :
    ∃ s3, s3 ⊆ Icc 1 n ∧ s3.prod id = s2.prod id / p := by
  have hp_ge2 : p ≥ 2 := hp.two_le
  have h_x_mem : x ∈ Icc 1 n := hs2 hx
  rw [mem_Icc] at h_x_mem
  have h_x_pos : 1 ≤ x := h_x_mem.1
  have h_x_le : x ≤ n := h_x_mem.2
  have h_xp_le : x / p ≤ n := by
    have : x / p ≤ x := Nat.div_le_self x p
    omega
  have h_xp_pos : 1 ≤ x / p := by
    have h_div_eq : x = p * (x / p) := (Nat.mul_div_cancel' h_div).symm
    by_contra h_lt
    have h_zero : x / p = 0 := Nat.lt_one_iff.1 (Nat.lt_of_not_le h_lt)
    have h_x_zero : x = 0 := by
      rw [h_div_eq, h_zero, mul_zero]
    omega
  have h_xp_mem : x / p ∈ Icc 1 n := by
    rw [mem_Icc]
    exact ⟨h_xp_pos, h_xp_le⟩
  let s3 := insert (x / p) (s2.erase x)
  use s3
  constructor
  · rw [insert_subset_iff]
    constructor
    · exact h_xp_mem
    · exact subset_trans (erase_subset x s2) hs2
  · dsimp [s3]
    have h_not_mem : x / p ∉ s2.erase x := by
      rw [mem_erase]
      push_neg
      intro _
      exact hx_p
    rw [prod_insert h_not_mem]
    dsimp [id]
    have h_eq : s2.prod id = x * (s2.erase x).prod id := by
      conv_lhs => rw [← insert_erase hx]
      rw [prod_insert (by simp)]
      rfl
    have h_div_eq : x = p * (x / p) := (Nat.mul_div_cancel' h_div).symm
    rw [h_eq, h_div_eq]
    rw [mul_assoc]
    have hp_ne_zero : p ≠ 0 := by omega
    have h_cancel_lhs : p * (x / p) / p = x / p :=
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp_ne_zero)
    rw [h_cancel_lhs]
    have h_cancel : p * (x / p * (s2.erase (p * (x / p))).prod id) / p = x / p * (s2.erase (p * (x / p))).prod id :=
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp_ne_zero)
    rw [h_cancel]
    rfl

lemma p_mul_mem_of_not_closed (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n) (s : Finset ℕ) (hs : s ⊆ Icc 1 n) (x : ℕ) (hx : x ∈ s) (h_px : p * x ≤ n) (h_not_mem : p * x ∉ s) :
    p * s.prod id ∈ products n := by
  dsimp [products]
  rw [mem_image]
  use insert (p * x) (s.erase x)
  rw [mem_powerset]
  constructor
  · rw [insert_subset_iff]
    constructor
    · rw [mem_Icc]
      have h_x_pos : 1 ≤ x := by
        have hx' := hs hx
        rw [mem_Icc] at hx'
        exact hx'.1
      have h_px_pos : 1 ≤ p * x := by
        have hp_pos : 1 ≤ p := hp.pos
        exact Nat.mul_pos hp_pos h_x_pos
      exact ⟨h_px_pos, h_px⟩
    · exact subset_trans (erase_subset x s) hs
  · rw [prod_insert]
    · have h_eq : s.prod id = x * (s.erase x).prod id := by
        conv_lhs => rw [← insert_erase hx]
        rw [prod_insert (by simp)]
        rfl
      rw [h_eq]
      simp only [id_eq, mul_assoc]
    · intro h
      rw [mem_erase] at h
      exact h_not_mem h.2


def non_p_part (p x : ℕ) : ℕ := x / p^(padicValNat p x)

lemma p_pow_padicValNat_dvd (p x : ℕ) : p^(padicValNat p x) ∣ x := by
  exact pow_padicValNat_dvd

lemma self_eq_pow_mul_non_p_part (p x : ℕ) : x = p^(padicValNat p x) * non_p_part p x := by
  dsimp [non_p_part]
  rw [Nat.mul_div_cancel']
  exact pow_padicValNat_dvd

lemma prod_pow (p : ℕ) (s : Finset ℕ) (g : ℕ → ℕ) : s.prod (fun x => p^(g x)) = p^(∑ x ∈ s, g x) := by
  induction' s using Finset.induction_on with x s hxs ih
  · simp
  · rw [prod_insert hxs, sum_insert hxs, pow_add, ih]

lemma padicValNat_prod {p : ℕ} [hp : Fact (Nat.Prime p)] (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValNat p (s.prod f) = ∑ x ∈ s, padicValNat p (f x) := by
  induction' s using Finset.induction_on with x s hxs ih
  · simp
  · rw [prod_insert hxs, sum_insert hxs]
    have h_fx : f x ≠ 0 := hf x (mem_insert_self x s)
    have h_prod : s.prod f ≠ 0 := by
      apply prod_ne_zero_iff.2
      intro y hy
      exact hf y (mem_insert_of_mem hy)
    rw [padicValNat.mul h_fx h_prod]
    have h_ih : padicValNat p (s.prod f) = ∑ x ∈ s, padicValNat p (f x) := by
      apply ih
      intro y hy
      exact hf y (mem_insert_of_mem hy)
    rw [h_ih]

lemma non_p_part_prod (p : ℕ) [hp : Fact (Nat.Prime p)] (s : Finset ℕ) (hs : ∀ x ∈ s, x ≠ 0) :
    non_p_part p (s.prod id) = s.prod (fun x => non_p_part p x) := by
  have h_prod_ne : s.prod id ≠ 0 := by
    apply prod_ne_zero_iff.2
    intro x hx
    exact hs x hx
  have h_eq : s.prod id = p^(padicValNat p (s.prod id)) * s.prod (fun x => non_p_part p x) := by
    rw [padicValNat_prod s id hs]
    have h_split : s.prod id = s.prod (fun x => p^(padicValNat p x) * non_p_part p x) := by
      apply prod_congr rfl
      intro x hx
      exact self_eq_pow_mul_non_p_part p x
    rw [h_split]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [prod_pow]
    rfl
  have h_eq2 : s.prod id = p^(padicValNat p (s.prod id)) * non_p_part p (s.prod id) := by
    exact self_eq_pow_mul_non_p_part p (s.prod id)
  have hp_pow_pos : p^(padicValNat p (s.prod id)) > 0 := Nat.pow_pos hp.out.pos
  have h_mul_eq : p^(padicValNat p (s.prod id)) * non_p_part p (s.prod id) = p^(padicValNat p (s.prod id)) * s.prod (fun x => non_p_part p x) := by
    trans s.prod id
    · exact h_eq2.symm
    · exact h_eq
  exact Nat.eq_of_mul_eq_mul_left hp_pow_pos h_mul_eq

lemma non_p_part_mul_p_pow (p x a : ℕ) [hp : Fact (Nat.Prime p)] (hx : x ≠ 0) :
    non_p_part p (p^a * x) = non_p_part p x := by
  have hp_pow_ne : p^a ≠ 0 := _root_.ne_of_gt (Nat.pow_pos hp.out.pos)
  have h_ne : p^a * x ≠ 0 := Nat.mul_ne_zero hp_pow_ne hx
  dsimp [non_p_part]
  rw [padicValNat.mul hp_pow_ne hx]
  rw [padicValNat.pow a hp.out.ne_zero]
  simp only [padicValNat_self]
  have h_pow : p^(a * 1 + padicValNat p x) = p^a * p^(padicValNat p x) := by
    rw [mul_one, pow_add]
  rw [h_pow]
  rw [Nat.mul_div_mul_left _ _ (Nat.pow_pos hp.out.pos)]

lemma find_h (n p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n) (s : Finset ℕ) (hs : s ⊆ Icc 1 n) (hp_mem : p ∈ s) :
    ∃ h, h ≥ 1 ∧ (p^h ∉ s ∨ p^h > n) := by
  use n + 1
  constructor
  · omega
  · right
    have h_lt : n + 1 < p^(n+1) := Nat.lt_pow_self hp.two_le
    omega

noncomputable def min_h (n p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n) (s : Finset ℕ) (hs : s ⊆ Icc 1 n) (hp_mem : p ∈ s) : ℕ :=
  Nat.find (find_h n p hp hpn s hs hp_mem)

lemma min_h_spec (n p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n) (s : Finset ℕ) (hs : s ⊆ Icc 1 n) (hp_mem : p ∈ s) :
    min_h n p hp hpn s hs hp_mem ≥ 1 ∧ (p^(min_h n p hp hpn s hs hp_mem) ∉ s ∨ p^(min_h n p hp hpn s hs hp_mem) > n) :=
  Nat.find_spec (find_h n p hp hpn s hs hp_mem)

lemma min_h_ge_two (n p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n) (s : Finset ℕ) (hs : s ⊆ Icc 1 n) (hp_mem : p ∈ s) :
    min_h n p hp hpn s hs hp_mem ≥ 2 := by
  have h_spec := @Nat.find_min (fun h => h ≥ 1 ∧ (p^h ∉ s ∨ p^h > n)) _ (find_h n p hp hpn s hs hp_mem)
  have h_prop := min_h_spec n p hp hpn s hs hp_mem
  by_contra h_lt
  have h_eq : min_h n p hp hpn s hs hp_mem = 1 := by omega
  rw [h_eq] at h_prop
  simp only [pow_one, ge_iff_le, le_refl, true_and] at h_prop
  rcases h_prop with h1 | h2
  · exact h1 hp_mem
  · omega

lemma min_h_prev_mem (n p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n) (s : Finset ℕ) (hs : s ⊆ Icc 1 n) (hp_mem : p ∈ s) :
    p^(min_h n p hp hpn s hs hp_mem - 1) ∈ s := by
  have h_spec := @Nat.find_min (fun h => h ≥ 1 ∧ (p^h ∉ s ∨ p^h > n)) _ (find_h n p hp hpn s hs hp_mem)
  have h_ge2 := min_h_ge_two n p hp hpn s hs hp_mem
  have h_prev : min_h n p hp hpn s hs hp_mem - 1 < min_h n p hp hpn s hs hp_mem := by omega
  have h_prop := h_spec h_prev
  push_neg at h_prop
  have h_prev_ge1 : min_h n p hp hpn s hs hp_mem - 1 ≥ 1 := by omega
  exact (h_prop h_prev_ge1).1

lemma exists_replacement_of_not_closed (n p : ℕ) (hp : Nat.Prime p) (s2 : Finset ℕ) (hs2 : s2 ⊆ Icc 1 n)
    (x : ℕ) (hx : x ∈ s2) (h_div : p ∣ x) (h_not_closed : ¬ (∀ j ≤ padicValNat p x, x / p^j ∈ s2)) :
    ∃ z ∈ s2, p ∣ z ∧ z / p ∉ s2 := by
  have hp_fact : Fact (Nat.Prime p) := ⟨hp⟩
  push_neg at h_not_closed
  rcases h_not_closed with ⟨J, hJ_le, hJ_not⟩
  have h_find_exists : ∃ j, j ≤ padicValNat p x ∧ x / p^j ∉ s2 := ⟨J, hJ_le, hJ_not⟩
  let k := Nat.find h_find_exists
  have h_k_spec := Nat.find_spec h_find_exists
  have h_k_le : k ≤ padicValNat p x := h_k_spec.1
  have h_k_not : x / p^k ∉ s2 := h_k_spec.2
  have h_k_pos : k ≥ 1 := by
    by_contra h_lt
    have : k = 0 := by omega
    rw [this, pow_zero, Nat.div_one] at h_k_not
    exact h_k_not hx
  have h_prev : k - 1 < k := by omega
  have h_prev_spec := Nat.find_min h_find_exists h_prev
  push_neg at h_prev_spec
  have h_prev_le : k - 1 ≤ padicValNat p x := by omega
  have h_prev_mem : x / p^(k - 1) ∈ s2 := h_prev_spec h_prev_le
  let z := x / p^(k - 1)
  use z
  constructor
  · exact h_prev_mem
  · constructor
    · -- we want to show p ∣ z
      have h_div_pow_prev : p^(k - 1) ∣ x := by
        have h_pow_dvd : p^(k - 1) ∣ p^(padicValNat p x) := pow_dvd_pow p (by omega)
        exact dvd_trans h_pow_dvd pow_padicValNat_dvd
      have h_div_pow : p^(k - 1) * p ∣ x := by
        have h_eq : p^(k - 1) * p = p^k := by rw [← pow_succ, Nat.sub_add_cancel h_k_pos]
        rw [h_eq]
        have h_pow_dvd : p^k ∣ p^(padicValNat p x) := pow_dvd_pow p h_k_le
        exact dvd_trans h_pow_dvd pow_padicValNat_dvd
      exact (Nat.dvd_div_iff_mul_dvd h_div_pow_prev).2 h_div_pow
    · -- we want to show z / p ∉ s2
      have h_z_div : z / p = x / p^k := by
        dsimp [z]
        rw [Nat.div_div_eq_div_mul]
        congr 2
        rw [← pow_succ, Nat.sub_add_cancel h_k_pos]
      rwa [h_z_div]


lemma val_lt_h (n p x h : ℕ) (hp : Nat.Prime p) (hx : x ∈ Icc 1 n) (h_h : p^h > n) :
    padicValNat p x < h := by
  have hp_fact : Fact (Nat.Prime p) := ⟨hp⟩
  by_contra h_ge
  push_neg at h_ge
  have h_pow_dvd : p^h ∣ p^(padicValNat p x) := pow_dvd_pow p h_ge
  have h_div : p^h ∣ x := dvd_trans h_pow_dvd pow_padicValNat_dvd
  have h_x_pos : x ≥ 1 := mem_Icc.1 hx |>.1
  have h_le : p^h ≤ x := Nat.le_of_dvd h_x_pos h_div
  have h_x_le : x ≤ n := mem_Icc.1 hx |>.2
  omega

lemma div_pow_mem_of_closed (n p : ℕ) (hp : Nat.Prime p) (s2 : Finset ℕ) (hs2 : s2 ⊆ Icc 1 n) (h_closed : ∀ y ∈ s2, p ∣ y → y / p ∈ s2) (x : ℕ) (hx : x ∈ s2) (j : ℕ) (hj : j ≤ padicValNat p x) :
    x / p^j ∈ s2 := by
  by_cases hj_zero : j = 0
  · rw [hj_zero]
    simp only [pow_zero, Nat.div_one]
    exact hx
  · have h_val_pos : padicValNat p x ≥ 1 := by omega
    have hp_fact : Fact (Nat.Prime p) := ⟨hp⟩
    have h_div : p ∣ x := by
      have h_pow_dvd : p^1 ∣ p^(padicValNat p x) := pow_dvd_pow p h_val_pos
      simp only [pow_one] at h_pow_dvd
      exact dvd_trans h_pow_dvd pow_padicValNat_dvd
    by_contra h_not
    have h_not_all : ¬ (∀ j ≤ padicValNat p x, x / p^j ∈ s2) := by
      push_neg
      exact ⟨j, hj, h_not⟩
    have h_rep := exists_replacement_of_not_closed n p hp s2 hs2 x hx h_div h_not_all
    rcases h_rep with ⟨z, hz, h_z_div, h_z_not⟩
    exact h_z_not (h_closed z hz h_z_div)

lemma h_step_helper (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n) :
    ∀ m a, m ∈ products n → (p^a * m) ∈ products n → a ≥ 1 → (p * m) ∈ products n := by
  intro m a hm hpa ha
  induction' a with a ih generalizing m
  · omega
  · by_cases ha_zero : a = 0
    · -- a = 0, so a + 1 = 1
      rw [ha_zero] at hpa
      simp only [zero_add, pow_one] at hpa
      exact hpa
    · dsimp [products] at hm hpa
      rw [mem_image] at hm hpa
      rcases hm with ⟨s, hs, h_prod⟩
      rcases hpa with ⟨s2, hs2, h_prod2⟩
      rw [mem_powerset] at hs hs2
      by_cases h_div_closed : ∀ x ∈ s2, p ∣ x → x / p ∈ s2
      · by_cases hp_mem_s2 : p ∈ s2
        · -- p ∈ s2
          have h_eq : s2.prod id = p * (s2.erase p).prod id := by
            conv_lhs => rw [← insert_erase hp_mem_s2]
            rw [prod_insert (by simp)]
            rfl
          have h_eq2 : p * (p^a * s.prod id) = p * (s2.erase p).prod id := by
            calc p * (p^a * s.prod id) = p^(a+1) * s.prod id := by ring
            _ = p^(a+1) * m := by rw [h_prod]
            _ = s2.prod id := h_prod2.symm
            _ = p * (s2.erase p).prod id := h_eq
          have h_rep : p^a * s.prod id = (s2.erase p).prod id :=
            Nat.eq_of_mul_eq_mul_left hp.pos h_eq2
          have h_rep2 : (s2.erase p).prod id = p^a * m := by
            rw [← h_rep, h_prod]
          have h_pa_m : p^a * m ∈ products n := by
            dsimp [products]
            rw [mem_image]
            use s2.erase p
            rw [mem_powerset]
            constructor
            · exact subset_trans (erase_subset p s2) hs2
            · exact h_rep2
          have hm_in : m ∈ products n := by
            dsimp [products]
            rw [mem_image]
            use s
            rw [mem_powerset]
            exact ⟨hs, h_prod⟩
          exact ih m hm_in h_pa_m (by omega)
        · -- p ∉ s2 (which is impossible)
          sorry
      · push_neg at h_div_closed
        rcases h_div_closed with ⟨x, hx, h_div, hx_p⟩
        have h_rep := replacement_step n p hp s2 hs2 x hx h_div hx_p
        rcases h_rep with ⟨s3, hs3, h_prod3⟩
        have hp_pos : p > 0 := hp.pos
        have h_prod_s3 : s3.prod id = p^a * m := by
          rw [h_prod3, h_prod2]
          have h_eq : p^(a+1) * m = p * (p^a * m) := by ring
          rw [h_eq]
          exact Nat.mul_div_cancel_left _ hp_pos
        have h_pa_m : p^a * m ∈ products n := by
          dsimp [products]
          rw [mem_image]
          use s3
          rw [mem_powerset]
          exact ⟨hs3, h_prod_s3⟩
        have hm_in : m ∈ products n := by
          dsimp [products]
          rw [mem_image]
          use s
          rw [mem_powerset]
          exact ⟨hs, h_prod⟩
        exact ih m hm_in h_pa_m (by omega)

/--
Conjecture: Let p <= n be prime. If m and p^a*m are two such products, then so is p^k*m for all 0 < k < a.
-/
theorem oeis_60957_conjecture_0 (n : ℕ) :
    ∀ p, Nat.Prime p → p ≤ n →
    ∀ m a, m ∈ products n → (p ^ a * m) ∈ products n →
    ∀ k, 0 < k → k < a → (p ^ k * m) ∈ products n := by
  intro p hp hpn m a hm hpa k hk hka
  apply oeis_60957_conjecture_0_of_step n p hp hpn (h_step_helper n p hp hpn) m a hm hpa k hk hka
