import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A141057: Number of Abelian cubes of length $3n$ over an alphabet of size 3.
The formula is $a(n) = \sum_{n_1+n_2+n_3=n, n_i \ge 0} \left(\frac{n!}{n_1! n_2! n_3!}\right)^3$.
This sum is computed via the identity $\binom{n}{n_1, n_2, n_3} = \binom{n}{n_1} \binom{n-n_1}{n_2}$:
$$a(n) = \sum_{n_1=0}^n \sum_{n_2=0}^{n-n_1} \left(\binom{n}{n_1} \binom{n-n_1}{n_2}\right)^3$$
-/
def A141057 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun n₁ =>
    Finset.sum (Finset.range (n - n₁ + 1)) fun n₂ =>
      (choose n n₁ * choose (n - n₁) n₂) ^ 3

lemma isUnit_unit_mul {M:Type*}[CommMonoid M](u:Mˣ)(x:M): IsUnit ((u:M)*x) ↔ IsUnit x := by
  constructor
  · intro h; have hx : x = (↑u⁻¹) * ((u:M)*x) := by rw [← mul_assoc]; simp
    rw [hx]; exact (u⁻¹).isUnit.mul h
  · exact fun h => u.isUnit.mul h

lemma US_zero (m : ℕ) [NeZero m] (u : (ZMod m)ˣ) (c : ZMod m) (g : ZMod m → ZMod m)
    (hg : ∀ x : ZMod m, IsUnit x → g ((u:ZMod m) * x) = c * g x)
    (hc : IsUnit (c - 1)) :
    ∑ x : ZMod m, (if IsUnit x then g x else 0) = 0 := by
  set F : ZMod m → ZMod m := fun x => if IsUnit x then g x else 0 with hF
  have htoperm : ∀ x, (MulAction.toPerm u) x = (u:ZMod m) * x := fun x => rfl
  have hreind : ∑ x : ZMod m, F ((u:ZMod m) * x) = ∑ x : ZMod m, F x := by
    have h := Equiv.sum_comp (MulAction.toPerm u) F
    simpa only [htoperm] using h
  have hterm : ∀ x : ZMod m, F ((u:ZMod m) * x) = c * F x := by
    intro x
    by_cases hx : IsUnit x
    · have hux : IsUnit ((u:ZMod m) * x) := u.isUnit.mul hx
      simp only [hF, hx, hux, if_true]
      exact hg x hx
    · have hux : ¬ IsUnit ((u:ZMod m)*x) := fun h => hx ((isUnit_unit_mul u x).mp h)
      simp only [hF, hx, hux, if_false, mul_zero]
  have e1 : ∑ x, F ((u:ZMod m)*x) = ∑ x, c * F x := Finset.sum_congr rfl (fun x _ => hterm x)
  have heq : ∑ x, c * F x = ∑ x, F x := by rw [← e1, hreind]
  rw [← Finset.mul_sum] at heq
  have key : (c - 1) * (∑ x, F x) = 0 := by linear_combination heq
  rcases hc with ⟨w, hw⟩
  have hw2 : (w:ZMod m) * (∑ x, F x) = 0 := by rw [hw]; exact key
  have h2 := congrArg (fun t => (↑w⁻¹ : ZMod m) * t) hw2
  simp only [mul_zero, ← mul_assoc, Units.inv_mul, one_mul] at h2
  exact h2

lemma zmod_mul_inv (m:ℕ)(u:(ZMod m)ˣ)(x:ZMod m)(hx:IsUnit x):
    ((u:ZMod m)*x)⁻¹ = (u:ZMod m)⁻¹ * x⁻¹ := by
  obtain ⟨v, rfl⟩ := hx
  rw [← Units.val_mul u v, ZMod.inv_coe_unit (u*v), ZMod.inv_coe_unit u, ZMod.inv_coe_unit v,
      mul_inv_rev, Units.val_mul]
  ring

lemma US_inv (m:ℕ)[NeZero m](hu2:IsUnit (2:ZMod m)) :
    ∑ x:ZMod m, (if IsUnit x then x⁻¹ else 0) = 0 := by
  set u := hu2.unit with hu
  have huv : (u:ZMod m) = 2 := hu2.unit_spec
  have hmul : (u:ZMod m)⁻¹ * (u:ZMod m) = 1 := by rw [ZMod.inv_coe_unit]; exact u.inv_mul
  have hinvunit : IsUnit ((u:ZMod m)⁻¹) := by rw [ZMod.inv_coe_unit]; exact (u⁻¹).isUnit
  apply US_zero m u ((u:ZMod m)⁻¹) (fun x => x⁻¹)
  · intro x hx; exact zmod_mul_inv m u x hx
  · have hfac : (u:ZMod m)⁻¹ - 1 = (u:ZMod m)⁻¹ * (1 - (u:ZMod m)) := by
      rw [mul_sub, mul_one, hmul]
    rw [hfac]
    refine hinvunit.mul ?_
    rw [huv, show (1:ZMod m) - 2 = -1 by ring]; exact isUnit_one.neg

lemma US_inv2 (m:ℕ)[NeZero m](hu2:IsUnit (2:ZMod m))(hu3:IsUnit (3:ZMod m)) :
    ∑ x:ZMod m, (if IsUnit x then x⁻¹*x⁻¹ else 0) = 0 := by
  set u := hu2.unit with hu
  have huv : (u:ZMod m) = 2 := hu2.unit_spec
  have hmul : (u:ZMod m)⁻¹ * (u:ZMod m) = 1 := by rw [ZMod.inv_coe_unit]; exact u.inv_mul
  have hinvunit : IsUnit ((u:ZMod m)⁻¹) := by rw [ZMod.inv_coe_unit]; exact (u⁻¹).isUnit
  apply US_zero m u ((u:ZMod m)⁻¹*(u:ZMod m)⁻¹) (fun x => x⁻¹*x⁻¹)
  · intro x hx; rw [zmod_mul_inv m u x hx]; ring
  · have hfac : (u:ZMod m)⁻¹*(u:ZMod m)⁻¹ - 1
        = ((u:ZMod m)⁻¹ - 1) * ((u:ZMod m)⁻¹ + 1) := by ring
    rw [hfac]
    refine IsUnit.mul ?_ ?_
    · have h1 : (u:ZMod m)⁻¹ - 1 = (u:ZMod m)⁻¹ * (1 - (u:ZMod m)) := by
        rw [mul_sub, mul_one, hmul]
      rw [h1]; refine hinvunit.mul ?_
      rw [huv, show (1:ZMod m) - 2 = -1 by ring]; exact isUnit_one.neg
    · have h1 : (u:ZMod m)⁻¹ + 1 = (u:ZMod m)⁻¹ * (1 + (u:ZMod m)) := by
        rw [mul_add, mul_one, hmul]
      rw [h1]; refine hinvunit.mul ?_
      rw [huv, show (1:ZMod m) + 2 = 3 by ring]; exact hu3

lemma sum_block {R : Type*} [AddCommMonoid R] (L n : ℕ) (F : ℕ → R) :
    ∑ a ∈ Finset.range (L * n), F a
      = ∑ c ∈ Finset.range L, ∑ r ∈ Finset.range n, F (c * n + r) := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun a => (a / n, a % n)) (fun x => x.1 * n + x.2)
  · intro a ha
    simp only [Finset.mem_range] at ha
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.div_lt_of_lt_mul (by rwa [mul_comm] at ha), Nat.mod_lt _ hn⟩
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    simp only [Finset.mem_range]
    calc x.1 * n + x.2 < x.1 * n + n := by omega
      _ = (x.1 + 1) * n := by ring
      _ ≤ L * n := Nat.mul_le_mul_right n hx.1
  · intro a ha; exact Nat.div_add_mod' a n
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    have hn : 0 < n := by omega
    have h1 : (x.1 * n + x.2) / n = x.1 := by
      rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hx.2, zero_add]
    have h2 : (x.1 * n + x.2) % n = x.2 := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx.2]
    exact Prod.ext h1 h2
  · intro a ha; exact congrArg F (Nat.div_add_mod' a n).symm

lemma sum_zmod_eq_sum_range (n:ℕ)[NeZero n](H:ZMod n → ZMod n):
    ∑ x : ZMod n, H x = ∑ r ∈ Finset.range n, H (r:ZMod n) := by
  apply Finset.sum_nbij' (fun x => ZMod.val x) (fun r => (r:ZMod n))
  · intro x _; simp only [Finset.mem_range]; exact ZMod.val_lt x
  · intro r _; exact Finset.mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro r hr; simp only [Finset.mem_range] at hr; exact ZMod.val_natCast_of_lt hr
  · intro x _; rw [ZMod.natCast_zmod_val]

lemma RED (p s N : ℕ) [NeZero (p^s)] (hp : p.Prime) (hs : 1 ≤ s) (hdvd : p^s ∣ N)
    (g : ZMod (p^s) → ZMod (p^s)) :
    ∑ a ∈ (Finset.range N).filter (fun a => ¬ p ∣ a), g (a : ZMod (p^s))
      = ((N/p^s : ℕ) : ZMod (p^s)) * ∑ x : ZMod (p^s), (if IsUnit x then g x else 0) := by
  have hmpos : 0 < p^s := Nat.pos_of_ne_zero (NeZero.ne (p^s))
  have hpm : p ∣ p^s := dvd_pow_self p (by omega)
  obtain ⟨q, hq⟩ := hdvd
  rw [Finset.sum_filter, hq, mul_comm (p^s) q, sum_block q (p^s)]
  have hNdiv : (q * p^s) / p^s = q := Nat.mul_div_cancel q hmpos
  rw [hNdiv]
  have hinner : ∀ c, ∑ r ∈ Finset.range (p^s),
        (if ¬p∣(c*(p^s)+r) then g ((c*(p^s)+r : ℕ):ZMod (p^s)) else 0)
      = ∑ x : ZMod (p^s), (if IsUnit x then g x else 0) := by
    intro c
    rw [sum_zmod_eq_sum_range (p^s) (fun x => if IsUnit x then g x else 0)]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_range] at hr
    have hcast : ((c*(p^s)+r : ℕ) : ZMod (p^s)) = (r:ZMod (p^s)) := by
      have hz : ((p^s : ℕ) : ZMod (p^s)) = 0 := ZMod.natCast_self _
      rw [Nat.cast_add, Nat.cast_mul, hz, mul_zero, zero_add]
    have hdiv : (p ∣ (c*(p^s)+r)) ↔ (p ∣ r) := Nat.dvd_add_right (hpm.mul_left c)
    have hunit : IsUnit ((r:ZMod (p^s))) ↔ ¬ p ∣ r := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd
    rw [hcast, if_congr (not_congr hdiv) rfl rfl, if_congr hunit.symm rfl rfl]
  rw [Finset.sum_congr rfl (fun c _ => hinner c), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]

noncomputable def gg (p M : ℕ) : ℕ := ∏ j ∈ (Finset.Icc 1 (M * p)).filter (fun j => ¬ p ∣ j), j

lemma prod_Icc_id_eq_fac : ∀ n : ℕ, ∏ j ∈ Finset.Icc 1 n, j = n ! := by
  intro n; induction n with
  | zero => simp
  | succ k ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]

lemma fac_split (p M : ℕ) (hp : 0 < p) : (M * p)! = gg p M * p ^ M * M ! := by
  unfold gg
  have hsplit : (M * p)! = (∏ j ∈ Finset.Icc 1 (M * p), j) := (prod_Icc_id_eq_fac _).symm
  rw [hsplit, ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (M * p)) (fun j => ¬ p ∣ j)]
  have hdvd : (∏ j ∈ (Finset.Icc 1 (M * p)).filter (fun j => ¬ ¬ p ∣ j), j) = p ^ M * M ! := by
    have himg : (Finset.Icc 1 (M * p)).filter (fun j => ¬ ¬ p ∣ j)
        = (Finset.Icc 1 M).image (fun i => p * i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, not_not]
      constructor
      · rintro ⟨⟨h1, h2⟩, hd⟩
        obtain ⟨i, rfl⟩ := hd
        refine ⟨i, ⟨?_, ?_⟩, by ring⟩
        · rcases Nat.eq_zero_or_pos i with h | h
          · simp [h] at h1
          · exact h
        · refine Nat.le_of_mul_le_mul_right ?_ hp
          rw [mul_comm i p]; exact h2
      · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
        exact ⟨⟨by nlinarith, by rw [mul_comm]; exact Nat.mul_le_mul_right p h2⟩, ⟨i, rfl⟩⟩
    rw [himg, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, prod_Icc_id_eq_fac]
    congr 1
    rw [Nat.card_Icc]; simp
  rw [hdvd]; ring

-- F3: the gg ratio identity
lemma F3 (p A B : ℕ) (hp : 0 < p) (hBA : B ≤ A) :
    Nat.choose (A*p) (B*p) * gg p B * gg p (A-B) = Nat.choose A B * gg p A := by
  set L := A - B with hL
  have hAL : A = B + L := by omega
  have hLp : A*p - B*p = L*p := by rw [hL, Nat.sub_mul]
  -- (Ap)! identity
  have h1 : Nat.choose (A*p) (B*p) * (B*p)! * (A*p - B*p)! = (A*p)! :=
    Nat.choose_mul_factorial_mul_factorial (Nat.mul_le_mul_right p hBA)
  rw [hLp] at h1
  -- A! identity
  have h2 : Nat.choose A B * B ! * (A-B)! = A ! :=
    Nat.choose_mul_factorial_mul_factorial hBA
  rw [← hL] at h2
  -- expand factorials
  rw [fac_split p B hp, fac_split p L hp, fac_split p A hp] at h1
  -- h1 : choose(Ap)(Bp) * (gg B * p^B * B!) * (gg L * p^L * L!) = gg A * p^A * A!
  -- substitute A! = choose A B * B! * L!
  rw [← h2] at h1
  -- p^A = p^B * p^L  (A = B+L)
  have hpow : p^A = p^B * p^L := by rw [hAL, pow_add]
  rw [hpow] at h1
  -- now cancel by casting to ℤ
  have hKn : 0 < p^B * p^L * (B ! * L !) := by positivity
  have hK : (0:ℤ) < ((p^B * p^L * (B ! * L !) : ℕ):ℤ) := by exact_mod_cast hKn
  have h1z : ((Nat.choose (A*p) (B*p) * gg p B * gg p L : ℕ):ℤ)
        * ((p^B * p^L * (B ! * L !) : ℕ):ℤ)
      = ((Nat.choose A B * gg p A : ℕ):ℤ) * ((p^B * p^L * (B ! * L !) : ℕ):ℤ) := by
    have h1z' := congrArg (Nat.cast : ℕ → ℤ) h1
    push_cast at h1z' ⊢
    linear_combination h1z'
  have := mul_right_cancel₀ (ne_of_gt hK) h1z
  exact_mod_cast this

lemma gg_add (p B L : ℕ) :
    gg p (B + L) = gg p B * ∏ a ∈ (Finset.Icc 1 (L * p)).filter (fun a => ¬ p ∣ a), (B * p + a) := by
  unfold gg
  have hexp : (B+L)*p = B*p + L*p := by ring
  have e1 : Finset.Icc 1 (B*p) = Finset.Ioc 0 (B*p) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have e2 : Finset.Icc 1 ((B+L)*p) = Finset.Ioc 0 ((B+L)*p) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit : Finset.Icc 1 ((B+L)*p) = Finset.Icc 1 (B*p) ∪ Finset.Ioc (B*p) ((B+L)*p) := by
    rw [e1, e2, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by nlinarith)]
  have hdisj : Disjoint (Finset.Icc 1 (B*p)) (Finset.Ioc (B*p) ((B+L)*p)) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at ha hb; omega
  rw [hsplit, Finset.filter_union, Finset.prod_union (Finset.disjoint_filter_filter hdisj)]
  congr 1
  refine Finset.prod_nbij' (fun j => j - B*p) (fun a => B*p + a) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hj ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro hd; apply hj.2
    have hje : B*p + (j - B*p) = j := by omega
    rw [← hje]; exact (dvd_mul_left p B).add hd
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at ha ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro hd; exact ha.2 ((Nat.dvd_add_right (dvd_mul_left p B)).mp hd)
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_Ioc] at hj; dsimp only; omega
  · intro a ha; dsimp only; omega
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_Ioc] at hj; dsimp only; omega

lemma isUnit_two_zmod (p s:ℕ)[NeZero (p^s)](hp:p.Prime)(hp5:5≤p) : IsUnit (2:ZMod (p^s)) := by
  have h2 : ((2:ℕ):ZMod (p^s)) = 2 := by norm_num
  rw [← h2, ZMod.isUnit_iff_coprime]
  exact ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right s

lemma isUnit_three_zmod (p s:ℕ)[NeZero (p^s)](hp:p.Prime)(hp5:5≤p) : IsUnit (3:ZMod (p^s)) := by
  have h3 : ((3:ℕ):ZMod (p^s)) = 3 := by norm_num
  rw [← h3, ZMod.isUnit_iff_coprime]
  exact ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega)).pow_right s

lemma sumAinv (p s N : ℕ) [NeZero (p^s)] (hp : p.Prime) (hp5:5≤p) (hs : 1 ≤ s) (hdvd : p^s ∣ N) :
    ∑ a ∈ (Finset.range N).filter (fun a => ¬ p ∣ a), ((a : ZMod (p^s)))⁻¹ = 0 := by
  rw [RED p s N hp hs hdvd (fun x => x⁻¹), US_inv (p^s) (isUnit_two_zmod p s hp hp5), mul_zero]

lemma sumAinv2 (p s N : ℕ) [NeZero (p^s)] (hp : p.Prime) (hp5:5≤p) (hs : 1 ≤ s) (hdvd : p^s ∣ N) :
    ∑ a ∈ (Finset.range N).filter (fun a => ¬ p ∣ a), ((a : ZMod (p^s)))⁻¹ * ((a : ZMod (p^s)))⁻¹ = 0 := by
  rw [RED p s N hp hs hdvd (fun x => x⁻¹*x⁻¹),
      US_inv2 (p^s) (isUnit_two_zmod p s hp hp5) (isUnit_three_zmod p s hp hp5), mul_zero]

-- generalized product inverse for two units
lemma zmod_mul_inv' (m:ℕ)(a b:ZMod m)(ha:IsUnit a)(hb:IsUnit b): (a*b)⁻¹ = a⁻¹*b⁻¹ := by
  obtain ⟨u,rfl⟩ := ha; obtain ⟨v,rfl⟩ := hb
  rw [← Units.val_mul, ZMod.inv_coe_unit (u*v), ZMod.inv_coe_unit u, ZMod.inv_coe_unit v,
      mul_inv_rev, Units.val_mul]; ring

-- product of inverses = inverse of product, for units
lemma prod_zmod_inv (m:ℕ)(t:Finset ℕ)(f:ℕ→ZMod m)(hf:∀a∈t, IsUnit (f a)):
    (∏ a ∈ t, f a)⁻¹ = ∏ a ∈ t, (f a)⁻¹ := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a₀ s ha₀ ih =>
    rw [Finset.prod_insert ha₀, Finset.prod_insert ha₀,
        zmod_mul_inv' m _ _ (hf a₀ (Finset.mem_insert_self _ _))
          (Finset.prod_induction f IsUnit (fun _ _ => IsUnit.mul) isUnit_one
            (fun a ha => hf a (Finset.mem_insert_of_mem ha))),
        ih (fun a ha => hf a (Finset.mem_insert_of_mem ha))]

-- key2: (∑ x)^2 = ∑ x^2 + 2 * ∑_{pairs} ∏ x
lemma key2 {R:Type*}[CommRing R](s:Finset ℕ)(x:ℕ→R):
    (∑ a ∈ s, x a)^2 = ∑ a ∈ s, (x a)^2 + 2 * ∑ t ∈ s.powersetCard 2, ∏ a ∈ t, x a := by
  classical
  induction s using Finset.induction with
  | empty => rw [show (∅:Finset ℕ).powersetCard 2 = ∅ by rw [Finset.powersetCard_eq_empty]; norm_num]; simp
  | insert a₀ s ha₀ ih =>
    have hinj : ∀ c ∈ s.powersetCard 1, ∀ d ∈ s.powersetCard 1,
        insert a₀ c = insert a₀ d → c = d := by
      intro c hc d hd hcd
      have hc' : a₀ ∉ c := fun h => ha₀ ((Finset.mem_powersetCard.mp hc).1 h)
      have hd' : a₀ ∉ d := fun h => ha₀ ((Finset.mem_powersetCard.mp hd).1 h)
      rw [← Finset.erase_insert hc', ← Finset.erase_insert hd', hcd]
    have hdisj : Disjoint (s.powersetCard 2) ((s.powersetCard 1).image (insert a₀)) := by
      rw [Finset.disjoint_left]; intro c hc hc2
      simp only [Finset.mem_image] at hc2
      obtain ⟨d, hd, rfl⟩ := hc2
      have hsub := (Finset.mem_powersetCard.mp hc).1
      exact ha₀ (hsub (Finset.mem_insert_self _ _))
    rw [Finset.sum_insert ha₀, Finset.sum_insert ha₀,
        Finset.powersetCard_succ_insert ha₀, Finset.sum_union hdisj, Finset.sum_image hinj]
    have h1 : ∀ c ∈ s.powersetCard 1, ∏ a ∈ insert a₀ c, x a = x a₀ * ∏ a ∈ c, x a := by
      intro c hc
      have : a₀ ∉ c := fun h => ha₀ ((Finset.mem_powersetCard.mp hc).1 h)
      rw [Finset.prod_insert this]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have hpc1 : ∑ c ∈ s.powersetCard 1, ∏ a ∈ c, x a = ∑ c ∈ s, x c := by
      rw [Finset.powersetCard_one, Finset.sum_map]
      apply Finset.sum_congr rfl; intro c _; simp
    rw [hpc1]
    linear_combination ih

lemma zmod_unit_mul_inv (m:ℕ)(b:ZMod m)(hb:IsUnit b): b*b⁻¹=1 := by
  obtain ⟨u,rfl⟩ := hb; rw [ZMod.inv_coe_unit]; exact u.mul_inv

lemma prod_compl_eq (m:ℕ)(𝒜 t:Finset ℕ)(f:ℕ→ZMod m)(ht:t⊆𝒜)
    (hunit:∀a∈t, IsUnit (f a)) :
    ∏ a ∈ 𝒜 \ t, f a = (∏ a ∈ 𝒜, f a) * (∏ a ∈ t, f a)⁻¹ := by
  have hB : IsUnit (∏ a ∈ t, f a) :=
    Finset.prod_induction f IsUnit (fun _ _ => IsUnit.mul) isUnit_one hunit
  have hkey := Finset.prod_sdiff ht (f := f)
  calc ∏ a ∈ 𝒜 \ t, f a
      = (∏ a ∈ 𝒜 \ t, f a) * ((∏ a ∈ t, f a) * (∏ a ∈ t, f a)⁻¹) := by
        rw [zmod_unit_mul_inv m _ hB, mul_one]
    _ = (∏ a ∈ 𝒜, f a) * (∏ a ∈ t, f a)⁻¹ := by rw [← mul_assoc, hkey]

-- FACT-T2 : p^s ∣ e2
lemma dvd_e2 (p s L : ℕ) [NeZero (p^s)] (hp:p.Prime)(hp5:5≤p)(hs:1≤s)(hdvd:p^s ∣ L*p) :
    (p:ℤ)^s ∣ ∑ t ∈ ((Finset.range (L*p)).filter (fun a => ¬ p ∣ a)).powersetCard 2,
        ∏ a ∈ ((Finset.range (L*p)).filter (fun a => ¬ p ∣ a)) \ t, (a:ℤ) := by
  set 𝒜 := (Finset.range (L*p)).filter (fun a => ¬ p ∣ a) with h𝒜
  have hunitA : ∀ a ∈ 𝒜, IsUnit ((a:ZMod (p^s))) := by
    intro a ha
    rw [h𝒜, Finset.mem_filter, Finset.mem_range] at ha
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr ha.2
  rw [show ((p:ℤ)^s) = ((p^s:ℕ):ℤ) by push_cast; ring,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  -- reduce each term
  set D₀ := ∏ a ∈ 𝒜, ((a:ZMod (p^s))) with hD₀
  have hstep : ∀ t ∈ 𝒜.powersetCard 2, ∏ a ∈ 𝒜 \ t, ((a:ZMod (p^s)))
      = D₀ * ∏ a ∈ t, ((a:ZMod (p^s)))⁻¹ := by
    intro t ht
    have hts : t ⊆ 𝒜 := (Finset.mem_powersetCard.mp ht).1
    rw [prod_compl_eq (p^s) 𝒜 t _ hts (fun a ha => hunitA a (hts ha)),
        prod_zmod_inv (p^s) t _ (fun a ha => hunitA a (hts ha))]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  -- now show ∑_t ∏_{a∈t}(↑a)⁻¹ = 0
  have hdoubling : (2:ZMod (p^s)) * ∑ t ∈ 𝒜.powersetCard 2, ∏ a ∈ t, ((a:ZMod (p^s)))⁻¹ = 0 := by
    have hk := key2 𝒜 (fun a => ((a:ZMod (p^s)))⁻¹)
    have hS1 : ∑ a ∈ 𝒜, ((a:ZMod (p^s)))⁻¹ = 0 := sumAinv p s (L*p) hp hp5 hs hdvd
    have hS2 : ∑ a ∈ 𝒜, (((a:ZMod (p^s)))⁻¹)^2 = 0 := by
      have := sumAinv2 p s (L*p) hp hp5 hs hdvd
      rw [← this]; apply Finset.sum_congr rfl; intro a _; rw [sq]
    rw [hS1, hS2] at hk
    linear_combination -hk
  have h2u : IsUnit (2:ZMod (p^s)) := isUnit_two_zmod p s hp hp5
  rcases h2u with ⟨w, hw⟩
  have : (w:ZMod (p^s)) * ∑ t ∈ 𝒜.powersetCard 2, ∏ a ∈ t, ((a:ZMod (p^s)))⁻¹ = 0 := by
    rw [hw]; exact hdoubling
  have h3 := congrArg (fun z => (↑w⁻¹:ZMod (p^s)) * z) this
  simp only [mul_zero, ← mul_assoc, Units.inv_mul, one_mul] at h3
  rw [h3, mul_zero]

lemma neg_zmod_inv (m:ℕ)(y:ZMod m)(hy:IsUnit y): (-y)⁻¹ = -(y⁻¹) := by
  have h1 : (-y) * (-(y⁻¹)) = 1 := by rw [neg_mul_neg]; exact zmod_unit_mul_inv m y hy
  have hu : IsUnit (-y) := hy.neg
  calc (-y)⁻¹ = (-y)⁻¹ * ((-y)*(-(y⁻¹))) := by rw [h1, mul_one]
    _ = ((-y)⁻¹ * (-y)) * (-(y⁻¹)) := by ring
    _ = 1 * (-(y⁻¹)) := by rw [mul_comm ((-y)⁻¹) (-y), zmod_unit_mul_inv m _ hu]
    _ = -(y⁻¹) := by rw [one_mul]

lemma dvd_T1 (p s L : ℕ) [NeZero (p^s)] (hp:p.Prime)(hp5:5≤p)(hs:1≤s)(hdvd:p^s ∣ L*p) :
    (p:ℤ)^(2*s) ∣ ∑ c ∈ ((Finset.range (L*p)).filter (fun a => ¬ p ∣ a)),
        ∏ a ∈ ((Finset.range (L*p)).filter (fun a => ¬ p ∣ a)).erase c, (a:ℤ) := by
  set 𝒜 := (Finset.range (L*p)).filter (fun a => ¬ p ∣ a) with h𝒜
  set Lp := L*p with hLp
  have hmem : ∀ c, c ∈ 𝒜 ↔ (c < Lp ∧ ¬ p ∣ c) := by
    intro c; rw [h𝒜, Finset.mem_filter, Finset.mem_range]
  have hpLp : p ∣ Lp := dvd_mul_left p L
  have hge1 : ∀ c ∈ 𝒜, 1 ≤ c := by
    intro c hc; rw [hmem] at hc
    rcases Nat.eq_zero_or_pos c with h|h
    · exact absurd (h ▸ dvd_zero p) hc.2
    · exact h
  have hunitA : ∀ a ∈ 𝒜, IsUnit ((a:ZMod (p^s))) := by
    intro a ha
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr ((hmem a).mp ha).2
  have hσmem : ∀ c ∈ 𝒜, Lp - c ∈ 𝒜 := by
    intro c hc
    have hc1 := hge1 c hc
    rw [hmem] at hc ⊢
    refine ⟨by omega, ?_⟩
    intro hd
    have hcle : c ≤ Lp := by omega
    have hdc : p ∣ c := by
      have := Nat.dvd_sub hpLp hd
      rwa [Nat.sub_sub_self hcle] at this
    exact hc.2 hdc
  have hσne : ∀ c ∈ 𝒜, Lp - c ≠ c := by
    intro c hc heq
    have hc1 := hge1 c hc
    rw [hmem] at hc
    have h2c : 2 * c = Lp := by omega
    have hpc : p ∣ 2 * c := h2c ▸ hpLp
    rcases (hp.dvd_mul.mp hpc) with h | h
    · rw [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two] at h; omega
    · exact hc.2 h
  have hset : ∀ c, (𝒜.erase c).erase (Lp-c) = 𝒜 \ {c, Lp - c} := by
    intro c; ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hset2 : ∀ c, (𝒜.erase (Lp-c)).erase c = 𝒜 \ {c, Lp - c} := by
    intro c; ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  set T1 := ∑ c ∈ 𝒜, ∏ a ∈ 𝒜.erase c, (a:ℤ) with hT1
  set U := ∑ c ∈ 𝒜, ∏ a ∈ 𝒜 \ {c, Lp - c}, (a:ℤ) with hU
  have hsplit : ∀ c ∈ 𝒜, ∏ a ∈ 𝒜.erase c, (a:ℤ)
      = ((Lp - c : ℕ):ℤ) * ∏ a ∈ 𝒜 \ {c, Lp - c}, (a:ℤ) := by
    intro c hc
    have hσc : Lp - c ∈ 𝒜.erase c := Finset.mem_erase.mpr ⟨hσne c hc, hσmem c hc⟩
    rw [← Finset.mul_prod_erase (𝒜.erase c) (fun a => (a:ℤ)) hσc, hset c]
  have hsplit2 : ∀ c ∈ 𝒜, ∏ a ∈ 𝒜.erase (Lp-c), (a:ℤ)
      = (c:ℤ) * ∏ a ∈ 𝒜 \ {c, Lp - c}, (a:ℤ) := by
    intro c hc
    have hcmem : c ∈ 𝒜.erase (Lp-c) := Finset.mem_erase.mpr ⟨(hσne c hc).symm, hc⟩
    rw [← Finset.mul_prod_erase (𝒜.erase (Lp-c)) (fun a => (a:ℤ)) hcmem, hset2 c]
  have hrei : ∑ c ∈ 𝒜, ∏ a ∈ 𝒜.erase (Lp - c), (a:ℤ) = T1 := by
    rw [hT1]
    refine Finset.sum_nbij' (fun c => Lp - c) (fun c => Lp - c) hσmem hσmem ?_ ?_ ?_
    · intro c hc; have := hge1 c hc; rw [hmem] at hc; dsimp only; omega
    · intro c hc; have := hge1 c hc; rw [hmem] at hc; dsimp only; omega
    · intro c hc; rfl
  have h2T1 : 2 * T1 = (Lp:ℤ) * U := by
    have hsum : 2 * T1 = ∑ c ∈ 𝒜, (∏ a ∈ 𝒜.erase c, (a:ℤ) + ∏ a ∈ 𝒜.erase (Lp-c), (a:ℤ)) := by
      rw [Finset.sum_add_distrib, ← hT1, hrei]; ring
    rw [hsum, hU, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    rw [hsplit c hc, hsplit2 c hc, ← add_mul]
    have hc1 := hge1 c hc
    have hcle : c ≤ Lp := by rw [hmem] at hc; omega
    have hcast : ((Lp - c : ℕ):ℤ) + (c:ℤ) = (Lp:ℤ) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [hcast]
  -- p^s ∣ U
  have hpU : (p:ℤ)^s ∣ U := by
    rw [show ((p:ℤ)^s)=((p^s:ℕ):ℤ) by push_cast;ring, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hU]
    push_cast
    set D₀ := ∏ a ∈ 𝒜, ((a:ZMod (p^s))) with hD₀
    have hLpzero : ((Lp:ℕ):ZMod (p^s)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hdvd
    have hstepU : ∀ c ∈ 𝒜, ∏ a ∈ 𝒜 \ {c, Lp - c}, ((a:ZMod (p^s)))
        = - (D₀ * (((c:ZMod (p^s)))⁻¹ * ((c:ZMod (p^s)))⁻¹)) := by
      intro c hc
      have hpair : ({c, Lp - c} : Finset ℕ) ⊆ 𝒜 := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl; exacts [hc, hσmem c hc]
      have hunits : ∀ a ∈ ({c, Lp-c}:Finset ℕ), IsUnit ((a:ZMod (p^s))) :=
        fun a ha => hunitA a (hpair ha)
      rw [prod_compl_eq (p^s) 𝒜 _ (fun a => (a:ZMod (p^s))) hpair hunits,
          Finset.prod_pair (hσne c hc).symm]
      have hcle : c ≤ Lp := by have := hge1 c hc; rw [hmem] at hc; omega
      have hnegc : ((Lp - c : ℕ):ZMod (p^s)) = -((c:ZMod (p^s))) := by
        rw [Nat.cast_sub hcle, hLpzero, zero_sub]
      rw [hnegc, zmod_mul_inv' (p^s) _ _ (hunitA c hc) ((hunitA c hc).neg),
          neg_zmod_inv (p^s) _ (hunitA c hc)]
      ring
    rw [Finset.sum_congr rfl hstepU, Finset.sum_neg_distrib, ← Finset.mul_sum]
    have : ∑ c ∈ 𝒜, ((c:ZMod (p^s)))⁻¹ * ((c:ZMod (p^s)))⁻¹ = 0 :=
      sumAinv2 p s Lp hp hp5 hs hdvd
    rw [this, mul_zero, neg_zero]
  -- combine
  have hpLpZ : (p:ℤ)^s ∣ (Lp:ℤ) := by
    rw [show ((p:ℤ)^s)=((p^s:ℕ):ℤ) by push_cast;ring]; exact_mod_cast hdvd
  have hpow2 : (p:ℤ)^(2*s) ∣ 2 * T1 := by
    rw [h2T1, two_mul, pow_add]
    exact mul_dvd_mul hpLpZ hpU
  -- divide out the 2
  have hcop : Nat.Coprime (p^(2*s)) 2 :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  have hcopZ : IsCoprime ((p:ℤ)^(2*s)) (2:ℤ) := by
    have := (Nat.isCoprime_iff_coprime).mpr hcop
    push_cast at this; exact this
  exact hcopZ.dvd_of_dvd_mul_left hpow2
lemma prod_const_add_expand (s:Finset ℕ)(y:ℤ):
    ∏ a ∈ s, (y + (a:ℤ))
      = ∑ k ∈ Finset.range (s.card+1), y^k * ∑ t ∈ s.powersetCard k, ∏ a ∈ s\t, (a:ℤ) := by
  rw [Finset.prod_add (fun _ : ℕ => y) (fun a : ℕ => (a:ℤ)) s,
      Finset.powerset_card_disjiUnion s, Finset.sum_disjiUnion]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]

lemma dvd_Delta (p L B : ℕ) (hp:p.Prime)(hp5:5≤p) :
    (p:ℤ)^(3 + 3*min (padicValNat p B) (padicValNat p L)) ∣
      (∏ a ∈ (Finset.range (L*p)).filter (fun a => ¬ p ∣ a), ((B*p:ℤ) + (a:ℤ))
       - ∏ a ∈ (Finset.range (L*p)).filter (fun a => ¬ p ∣ a), (a:ℤ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · subst hB0; simp
  set 𝒜 := (Finset.range (L*p)).filter (fun a => ¬ p ∣ a) with h𝒜
  set vB := padicValNat p B with hvB
  set vL := padicValNat p L with hvL
  set w := min vB vL with hw
  set s := vL + 1 with hs
  haveI : NeZero (p^s) := ⟨pow_ne_zero s hp.pos.ne'⟩
  have hdvdLp : p^s ∣ L*p := by
    rcases Nat.eq_zero_or_pos L with hL0|hLpos
    · subst hL0; simp
    · have hval : padicValNat p (L*p) = s := by
        rw [padicValNat.mul (by omega) (by omega), hs, hvL, padicValNat.self hp.one_lt]
      rw [← hval]; exact pow_padicValNat_dvd
  have hpB : (p:ℤ)^vB ∣ (B:ℤ) := by rw [hvB]; exact_mod_cast pow_padicValNat_dvd
  have hpBP : (p:ℤ)^(vB+1) ∣ (B*p:ℤ) := by
    rw [pow_succ]; push_cast; exact mul_dvd_mul hpB (dvd_refl _)
  have hpBP3 : (p:ℤ)^(3*(vB+1)) ∣ (B*p:ℤ)^3 := by
    rw [mul_comm 3 (vB+1), pow_mul]; exact pow_dvd_pow_of_dvd hpBP 3
  have hpc1eq : (∑ t ∈ 𝒜.powersetCard 1, ∏ a ∈ 𝒜\t, (a:ℤ))
      = ∑ c ∈ 𝒜, ∏ a ∈ 𝒜.erase c, (a:ℤ) := by
    rw [Finset.powersetCard_one, Finset.sum_map]
    apply Finset.sum_congr rfl; intro c _; rw [Finset.erase_eq]; rfl
  have hpF1 : (p:ℤ)^(2*s) ∣ (∑ t ∈ 𝒜.powersetCard 1, ∏ a ∈ 𝒜\t, (a:ℤ)) := by
    rw [hpc1eq]; exact dvd_T1 p s L hp hp5 (by omega) hdvdLp
  have hpF2 : (p:ℤ)^s ∣ (∑ t ∈ 𝒜.powersetCard 2, ∏ a ∈ 𝒜\t, (a:ℤ)) :=
    dvd_e2 p s L hp hp5 (by omega) hdvdLp
  rw [prod_const_add_expand 𝒜 (B*p:ℤ), Finset.sum_range_succ']
  have hF0 : (B*p:ℤ)^0 * (∑ t ∈ 𝒜.powersetCard 0, ∏ a ∈ 𝒜\t, (a:ℤ)) = ∏ a ∈ 𝒜, (a:ℤ) := by
    rw [pow_zero, one_mul]; simp [Finset.powersetCard_zero]
  rw [hF0, add_sub_cancel_right]
  apply Finset.dvd_sum
  intro k _
  have hmul : ∀ (A C : ℕ) (x y : ℤ), (p:ℤ)^A ∣ x → (p:ℤ)^C ∣ y →
      (3+3*w) ≤ A + C → (p:ℤ)^(3+3*w) ∣ x * y := by
    intro A C x y hx hy hle
    have h1 : (p:ℤ)^(A+C) ∣ x*y := by rw [pow_add]; exact mul_dvd_mul hx hy
    exact dvd_trans (pow_dvd_pow (p:ℤ) hle) h1
  obtain _ | _ | k := k
  · rw [show (0:ℕ)+1 = 1 by rfl, pow_one]
    exact hmul (vB+1) (2*s) _ _ hpBP hpF1 (by omega)
  · rw [show (1:ℕ)+1 = 2 by rfl]
    refine hmul (2*(vB+1)) s _ _ ?_ hpF2 (by omega)
    rw [mul_comm 2 (vB+1), pow_mul]; exact pow_dvd_pow_of_dvd hpBP 2
  · refine hmul (3*(vB+1)) 0 _ _ ?_ (one_dvd _) (by omega)
    exact dvd_trans hpBP3 (pow_dvd_pow _ (by omega))

lemma kazan (p A B : ℕ) (hp:p.Prime)(hp5:5≤p)(hBA:B≤A) :
    (p:ℤ)^(padicValNat p (A.choose B) + (3 + 3*min (padicValNat p B) (padicValNat p (A-B))))
      ∣ ((A*p).choose (B*p) : ℤ) - (A.choose B : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set L := A - B with hL
  have hAe : A = B + L := by omega
  set 𝒜 := (Finset.range (L*p)).filter (fun a => ¬ p ∣ a) with h𝒜
  have hpLp : p ∣ L*p := dvd_mul_left p L
  have hIR : (Finset.Icc 1 (L*p)).filter (fun a => ¬p∣a) = 𝒜 := by
    rw [h𝒜]; ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1,h2⟩,hd⟩
      refine ⟨?_,hd⟩
      rcases lt_or_eq_of_le h2 with h|h
      · exact h
      · exact absurd (h ▸ hpLp) hd
    · rintro ⟨h1,hd⟩
      refine ⟨⟨?_,by omega⟩,hd⟩
      rcases Nat.eq_zero_or_pos x with h|h
      · exact absurd (h ▸ dvd_zero p) hd
      · exact h
  -- ℕ identities
  have hF3 := F3 p A B hp.pos hBA
  have hF2 := gg_add p B L
  rw [← hAe] at hF2
  -- gg L = ∏_𝒜 (nat)
  have hggL : gg p L = ∏ a ∈ 𝒜, a := by unfold gg; rw [hIR]
  have hggP : (∏ a ∈ (Finset.Icc 1 (L*p)).filter (fun a=>¬p∣a), (B*p+a))
      = ∏ a ∈ 𝒜, (B*p + a) := by rw [hIR]
  rw [← hL] at hF3
  -- cancel gg B in ℤ
  set c := ((A*p).choose (B*p) : ℤ) with hc
  set d := (A.choose B : ℤ) with hd
  set D₀ := ∏ a ∈ 𝒜, (a:ℤ) with hD₀
  set P := ∏ a ∈ 𝒜, ((B:ℤ)*p + (a:ℤ)) with hP
  have hggBpos : 0 < gg p B := by
    rw [gg]; apply Finset.prod_pos; intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi; omega
  -- from F3 & F2 : c * ggL = d * P'  (cancel ggB)
  have hcD0 : c * D₀ = d * P := by
    have hF3z : c * (gg p B : ℤ) * (gg p L : ℤ) = d * (gg p A : ℤ) := by
      rw [hc, hd]; exact_mod_cast hF3
    have hF2z : (gg p A : ℤ) = (gg p B : ℤ) * P := by
      have h2 : (gg p A : ℤ) = (gg p B : ℤ) * ∏ a ∈ 𝒜, ((B*p + a : ℕ):ℤ) := by
        rw [hIR] at hF2; exact_mod_cast hF2
      rw [h2, hP]; push_cast; rfl
    rw [hF2z] at hF3z
    have hggLz : (gg p L : ℤ) = D₀ := by rw [hggL, hD₀]; push_cast; rfl
    rw [hggLz] at hF3z
    -- hF3z : c * ggB * D₀ = d * (ggB * P)
    have hggBne : (gg p B : ℤ) ≠ 0 := by exact_mod_cast hggBpos.ne'
    have hcancel : (gg p B : ℤ) * (c * D₀) = (gg p B : ℤ) * (d * P) := by
      ring_nf; ring_nf at hF3z; linarith [hF3z]
    exact mul_left_cancel₀ hggBne hcancel
  -- Δ divisibility
  have hΔ : (p:ℤ)^(3 + 3*min (padicValNat p B) (padicValNat p L)) ∣ (P - D₀) := by
    have := dvd_Delta p L B hp hp5
    rw [← h𝒜] at this
    -- this : ... ∣ (∏_𝒜 (B*p+a) - ∏_𝒜 a) = P - D₀
    exact this
  -- p^vd ∣ d
  have hvd : (p:ℤ)^(padicValNat p (A.choose B)) ∣ d := by
    rw [hd]; exact_mod_cast pow_padicValNat_dvd
  -- (c-d)*D₀ = d*(P-D₀)
  have hkey : (c - d) * D₀ = d * (P - D₀) := by
    have := hcD0; ring_nf; ring_nf at this; linarith [this]
  -- p^N ∣ d*(P-D₀)
  have hNdvd : (p:ℤ)^(padicValNat p (A.choose B) + (3 + 3*min (padicValNat p B) (padicValNat p L)))
      ∣ d * (P - D₀) := by rw [pow_add]; exact mul_dvd_mul hvd hΔ
  rw [← hkey] at hNdvd
  -- cancel D₀ (coprime to p)
  have hcopD0 : IsCoprime ((p:ℤ)^(padicValNat p (A.choose B) + (3 + 3*min (padicValNat p B) (padicValNat p L)))) D₀ := by
    apply IsCoprime.pow_left
    rw [hD₀]
    apply IsCoprime.prod_right
    intro a ha
    rw [h𝒜, Finset.mem_filter, Finset.mem_range] at ha
    exact Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr ha.2)
  have := hcopD0.dvd_of_dvd_mul_right hNdvd
  rw [hL] at this ⊢
  exact this

lemma padicVal_choose_ge (p m i : ℕ) (hp : p.Prime) (h1 : 1 ≤ i) (hi : i ≤ m) :
    padicValNat p m ≤ padicValNat p i + padicValNat p (m.choose i) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i-1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m-1, by omega⟩
  have hid := Nat.succ_mul_choose_eq m' i'
  have hi' : i' ≤ m' := by omega
  have hm1 : (m'+1) ≠ 0 := by omega
  have hc1 : m'.choose i' ≠ 0 := (Nat.choose_pos hi').ne'
  have hc2 : (m'+1).choose (i'+1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hi1 : (i'+1) ≠ 0 := by omega
  have := congrArg (padicValNat p) hid
  rw [padicValNat.mul hm1 hc1, padicValNat.mul hc2 hi1] at this
  omega

lemma kummerBin (p x y : ℕ)(hp:p.Prime)(hx:1≤x)(hy:1≤y) :
    padicValNat p (x+y) ≤ padicValNat p ((x+y).choose x)
      + min (padicValNat p x) (padicValNat p y) := by
  have h1 := padicVal_choose_ge p (x+y) x hp hx (by omega)
  have h2 := padicVal_choose_ge p (x+y) y hp hy (by omega)
  have hsymm : (x+y).choose y = (x+y).choose x := by
    rw [← Nat.choose_symm (show x ≤ x+y by omega)]; congr 1; omega
  rw [hsymm] at h2
  omega

lemma perterm (p m i j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hij : i + j ≤ m) :
    (p:ℤ)^(3*(padicValNat p m + 1)) ∣
      ((((m*p).choose (i*p)) * (((m-i)*p).choose (j*p)) : ℤ)^3
       - ((m.choose i) * ((m-i).choose j) : ℤ)^3) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set t := padicValNat p m with ht
  set c1 := ((m*p).choose (i*p) : ℤ) with hc1def
  set c2 := (((m-i)*p).choose (j*p) : ℤ) with hc2def
  set d1 := (m.choose i : ℤ) with hd1def
  set d2 := ((m-i).choose j : ℤ) with hd2def
  set vd1 := padicValNat p (m.choose i) with hvd1
  set vd2 := padicValNat p ((m-i).choose j) with hvd2
  set w1 := min (padicValNat p i) (padicValNat p (m-i)) with hw1
  set w2 := min (padicValNat p j) (padicValNat p ((m-i)-j)) with hw2
  set C := c1 * c2 with hCdef
  set D := d1 * d2 with hDdef
  have hmul2 : ∀ (E a b:ℕ)(x y:ℤ), (p:ℤ)^a∣x → (p:ℤ)^b∣y → E≤a+b → (p:ℤ)^E∣x*y := by
    intro E a b x y hx hy hle
    exact dvd_trans (pow_dvd_pow (p:ℤ) hle) (by rw [pow_add]; exact mul_dvd_mul hx hy)
  -- base divisibilities
  have hd1 : (p:ℤ)^vd1 ∣ d1 := by rw [hd1def, hvd1]; exact_mod_cast pow_padicValNat_dvd
  have hd2 : (p:ℤ)^vd2 ∣ d2 := by rw [hd2def, hvd2]; exact_mod_cast pow_padicValNat_dvd
  have hkz1 := kazan p m i hp hp5 (by omega)
  have hkz2 := kazan p (m-i) j hp hp5 (by omega)
  -- rewrite exponents/terms of hkz1, hkz2 into our names
  have he1 : (p:ℤ)^(vd1 + (3 + 3*w1)) ∣ (c1 - d1) := by
    rw [hc1def, hd1def, hvd1, hw1]; exact hkz1
  have he2 : (p:ℤ)^(vd2 + (3 + 3*w2)) ∣ (c2 - d2) := by
    rw [hc2def, hd2def, hvd2, hw2]; exact hkz2
  have hle1 : vd1 ≤ vd1 + (3 + 3*w1) := by omega
  have hle2 : vd2 ≤ vd2 + (3 + 3*w2) := by omega
  have hc1u : (p:ℤ)^vd1 ∣ c1 := by
    have : c1 = d1 + (c1 - d1) := by ring
    rw [this]; exact dvd_add hd1 (dvd_trans (pow_dvd_pow _ hle1) he1)
  have hc2u : (p:ℤ)^vd2 ∣ c2 := by
    have : c2 = d2 + (c2 - d2) := by ring
    rw [this]; exact dvd_add hd2 (dvd_trans (pow_dvd_pow _ hle2) he2)
  have hCu : (p:ℤ)^(vd1+vd2) ∣ C := by rw [hCdef]; exact hmul2 _ _ _ _ _ hc1u hc2u (by omega)
  have hDu : (p:ℤ)^(vd1+vd2) ∣ D := by rw [hDdef]; exact hmul2 _ _ _ _ _ hd1 hd2 (by omega)
  have hCD : (p:ℤ)^(2*(vd1+vd2)) ∣ C*D := hmul2 _ _ _ _ _ hCu hDu (by omega)
  -- Claims
  have hClaimA : (c1 - d1) ≠ 0 → t ≤ vd1 + vd2 + w1 := by
    intro he
    have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h|h
      · exfalso; apply he; rw [hc1def, hd1def, h]; simp
      · exact h
    have hmi1 : 1 ≤ m - i := by
      rcases Nat.eq_zero_or_pos (m-i) with h|h
      · exfalso; apply he; rw [hc1def, hd1def]
        have him : i = m := by omega
        rw [him]; simp
      · exact h
    have hk := kummerBin p i (m-i) hp hi1 hmi1
    have hmm : i + (m-i) = m := by omega
    rw [hmm] at hk
    rw [hvd1, hw1, ht]; omega
  have hClaimB : (c2 - d2) ≠ 0 → t ≤ vd1 + vd2 + w2 := by
    intro he
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h|h
      · exfalso; apply he; rw [hc2def, hd2def, h]; simp
      · exact h
    have hl1 : 1 ≤ (m-i) - j := by
      rcases Nat.eq_zero_or_pos ((m-i)-j) with h|h
      · exfalso; apply he; rw [hc2def, hd2def]
        have hjm : j = m - i := by omega
        rw [hjm]; simp
      · exact h
    have hk := kummerBin p j ((m-i)-j) hp hj1 hl1
    have hmm : j + ((m-i)-j) = m - i := by omega
    rw [hmm] at hk
    -- hk : padicValNat p (m-i) ≤ padicValNat p ((m-i).choose j) + min (v_p j)(v_p ((m-i)-j))
    -- need t ≤ vd1+vd2+w2 ; use vd1 bounds via K on i (only if i≥1) else vd1=... handle
    have hKi : padicValNat p m ≤ padicValNat p (m-i) + vd1 := by
      rcases Nat.eq_zero_or_pos i with h|h
      · rw [h]; simp [hvd1]
      · have := kummerBin p i (m-i) hp h (by omega)
        have hmm2 : i + (m-i) = m := by omega
        rw [hmm2] at this
        rw [hvd1]; omega
    rw [hvd2, hw2, ht]; omega
  -- δ = C - D = d1 e2 + d2 e1 + e1 e2
  have hδeq : C - D = d1*(c2-d2) + d2*(c1-d1) + (c1-d1)*(c2-d2) := by rw [hCdef, hDdef]; ring
  -- hδ1 : p^(t+1) ∣ (C - D)
  have hδ1 : (p:ℤ)^(t+1) ∣ (C - D) := by
    rw [hδeq]
    refine dvd_add (dvd_add ?_ ?_) ?_
    · -- d1 * e2
      rcases eq_or_ne (c2-d2) 0 with h|h
      · rw [h, mul_zero]; exact dvd_zero _
      · exact hmul2 _ _ _ _ _ hd1 he2 (by have := hClaimB h; omega)
    · rcases eq_or_ne (c1-d1) 0 with h|h
      · rw [h, mul_zero]; exact dvd_zero _
      · exact hmul2 _ _ _ _ _ hd2 he1 (by have := hClaimA h; omega)
    · rcases eq_or_ne (c1-d1) 0 with h|h
      · rw [h, zero_mul]; exact dvd_zero _
      · exact hmul2 _ _ _ _ _ he1 he2 (by have := hClaimA h; omega)
  -- hδ2 : p^(3(t+1)) ∣ 3*C*D*(C-D)
  have hδ2 : (p:ℤ)^(3*(t+1)) ∣ 3*C*D*(C-D) := by
    have hrw : 3*C*D*(C-D) = 3*((C*D)*(d1*(c2-d2))) + 3*((C*D)*(d2*(c1-d1)))
        + 3*((C*D)*((c1-d1)*(c2-d2))) := by rw [hδeq]; ring
    rw [hrw]
    refine dvd_add (dvd_add ?_ ?_) ?_
    · rcases eq_or_ne (c2-d2) 0 with h|h
      · rw [h, mul_zero, mul_zero, mul_zero]; exact dvd_zero _
      · refine Dvd.dvd.mul_left ?_ 3
        refine hmul2 _ _ _ _ _ hCD (hmul2 _ _ _ _ _ hd1 he2 (le_refl _)) ?_
        have := hClaimB h; omega
    · rcases eq_or_ne (c1-d1) 0 with h|h
      · rw [h, mul_zero, mul_zero, mul_zero]; exact dvd_zero _
      · refine Dvd.dvd.mul_left ?_ 3
        refine hmul2 _ _ _ _ _ hCD (hmul2 _ _ _ _ _ hd2 he1 (le_refl _)) ?_
        have := hClaimA h; omega
    · rcases eq_or_ne (c1-d1) 0 with h|h
      · rw [h, zero_mul, mul_zero, mul_zero]; exact dvd_zero _
      · refine Dvd.dvd.mul_left ?_ 3
        refine hmul2 _ _ _ _ _ hCD (hmul2 _ _ _ _ _ he1 he2 (le_refl _)) ?_
        have := hClaimA h; omega
  -- combine via C^3 - D^3 = (C-D)^3 + 3 C D (C-D)
  have hcube : C^3 - D^3 = (C-D)^3 + 3*C*D*(C-D) := by ring
  have hgoal : (p:ℤ)^(3*(t+1)) ∣ (C^3 - D^3) := by
    rw [hcube]
    refine dvd_add ?_ hδ2
    have : (p:ℤ)^(3*(t+1)) = ((p:ℤ)^(t+1))^3 := by rw [← pow_mul]; ring_nf
    rw [this]; exact pow_dvd_pow_of_dvd hδ1 3
  -- rewrite goal to C^3 - D^3
  have : ((((m*p).choose (i*p)) * (((m-i)*p).choose (j*p)) : ℤ)^3
       - ((m.choose i) * ((m-i).choose j) : ℤ)^3) = C^3 - D^3 := by
    rw [hCdef, hDdef, hc1def, hc2def, hd1def, hd2def]
  rw [this]; exact hgoal

/-! ### Reduction machinery -/

def gt (N a b : ℕ) : ℤ := ((N.choose a) * ((N - a).choose b) : ℤ) ^ 3

def Dom (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun q => q.1 + q.2 ≤ N)

lemma multinom_symm (N a b : ℕ) (hab : a + b ≤ N) :
    N.choose a * (N - a).choose b = N.choose b * (N - b).choose a := by
  have e1 : N.choose a * (N - a).choose b * (a ! * b ! * (N - a - b)!) = N ! := by
    have h1 : N.choose a * a ! * (N - a)! = N ! := Nat.choose_mul_factorial_mul_factorial (by omega)
    have h2 : (N - a).choose b * b ! * (N - a - b)! = (N - a)! :=
      Nat.choose_mul_factorial_mul_factorial (by omega)
    calc N.choose a * (N - a).choose b * (a ! * b ! * (N - a - b)!)
        = N.choose a * a ! * ((N - a).choose b * b ! * (N - a - b)!) := by ring
      _ = N.choose a * a ! * (N - a)! := by rw [h2]
      _ = N ! := h1
  have e2 : N.choose b * (N - b).choose a * (a ! * b ! * (N - a - b)!) = N ! := by
    have h1 : N.choose b * b ! * (N - b)! = N ! := Nat.choose_mul_factorial_mul_factorial (by omega)
    have h2 : (N - b).choose a * a ! * (N - b - a)! = (N - b)! :=
      Nat.choose_mul_factorial_mul_factorial (by omega)
    have hs : N - b - a = N - a - b := by omega
    calc N.choose b * (N - b).choose a * (a ! * b ! * (N - a - b)!)
        = N.choose b * b ! * ((N - b).choose a * a ! * (N - a - b)!) := by ring
      _ = N.choose b * b ! * ((N - b).choose a * a ! * (N - b - a)!) := by rw [hs]
      _ = N.choose b * b ! * (N - b)! := by rw [h2]
      _ = N ! := h1
  have hK : 0 < a ! * b ! * (N - a - b)! :=
    Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)
  exact Nat.eq_of_mul_eq_mul_right hK (e1.trans e2.symm)

lemma A141057_eq (N : ℕ) : (A141057 N : ℤ) = ∑ q ∈ Dom N, gt N q.1 q.2 := by
  simp only [Dom, gt]
  rw [Finset.sum_filter, Finset.sum_product]
  unfold A141057
  push_cast
  apply Finset.sum_congr rfl
  intro n₁ hn₁
  rw [Finset.mem_range] at hn₁
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n₂; simp only [Finset.mem_filter, Finset.mem_range]; omega
  · intro n₂ _; rfl

lemma Claim1 (p m n₁ n₂ : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hsum : n₁ + n₂ ≤ m * p) (hna : ¬ (p ∣ n₁ ∧ p ∣ n₂)) :
    (p : ℤ) ^ (3 * (padicValNat p m + 1)) ∣ gt (m * p) n₁ n₂ := by
  haveI : Fact p.Prime := ⟨hp⟩
  set t := padicValNat p m with ht
  have hpos : 1 ≤ n₁ + n₂ := by
    by_contra h; push_neg at h
    have hn1 : n₁ = 0 := by omega
    have hn2 : n₂ = 0 := by omega
    exact hna ⟨hn1 ▸ dvd_zero p, hn2 ▸ dvd_zero p⟩
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; rw [h, Nat.zero_mul] at hsum; omega
    · exact h
  have hvp : padicValNat p (m * p) = t + 1 := by
    rw [padicValNat.mul (by omega) (by omega), padicValNat.self hp.one_lt, ht]
  suffices hM : p ^ (t + 1) ∣ (m * p).choose n₁ * ((m * p - n₁).choose n₂) by
    unfold gt
    have hMz : (p : ℤ) ^ (t + 1) ∣ ((m * p).choose n₁ * ((m * p - n₁).choose n₂) : ℤ) := by
      exact_mod_cast hM
    have hpp : (p : ℤ) ^ (3 * (t + 1)) = ((p : ℤ) ^ (t + 1)) ^ 3 := by rw [← pow_mul]; ring_nf
    rw [hpp]
    exact pow_dvd_pow_of_dvd hMz 3
  by_cases hd1 : p ∣ n₁
  · have hd2 : ¬ p ∣ n₂ := fun h => hna ⟨hd1, h⟩
    rw [multinom_symm (m * p) n₁ n₂ hsum]
    have hn2_1 : 1 ≤ n₂ := Nat.one_le_iff_ne_zero.mpr (fun h => hd2 (h ▸ dvd_zero p))
    have hv := padicVal_choose_ge p (m * p) n₂ hp hn2_1 (by omega)
    rw [padicValNat.eq_zero_of_not_dvd hd2, hvp] at hv
    have hdvd : p ^ (t + 1) ∣ (m * p).choose n₂ :=
      dvd_trans (pow_dvd_pow p (by omega)) pow_padicValNat_dvd
    exact Dvd.dvd.mul_right hdvd _
  · have hn1_1 : 1 ≤ n₁ := Nat.one_le_iff_ne_zero.mpr (fun h => hd1 (h ▸ dvd_zero p))
    have hv := padicVal_choose_ge p (m * p) n₁ hp hn1_1 (by omega)
    rw [padicValNat.eq_zero_of_not_dvd hd1, hvp] at hv
    have hdvd : p ^ (t + 1) ∣ (m * p).choose n₁ :=
      dvd_trans (pow_dvd_pow p (by omega)) pow_padicValNat_dvd
    exact Dvd.dvd.mul_right hdvd _

lemma red (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) :
    (p : ℤ) ^ (3 * (padicValNat p m + 1)) ∣ ((A141057 (m * p) : ℤ) - (A141057 m : ℤ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := by omega
  have hinj : Set.InjOn (fun k : ℕ × ℕ => (k.1 * p, k.2 * p)) (↑(Dom m)) := by
    intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext (Nat.eq_of_mul_eq_mul_right hp0 hab.1) (Nat.eq_of_mul_eq_mul_right hp0 hab.2)
  have himg : (Dom (m * p)).filter (fun q => p ∣ q.1 ∧ p ∣ q.2)
      = (Dom m).image (fun k => (k.1 * p, k.2 * p)) := by
    ext q
    obtain ⟨x, y⟩ := q
    simp only [Finset.mem_filter, Finset.mem_image, Dom, Finset.mem_product,
               Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, hxy⟩, hd1, hd2⟩
      have hax : x / p * p = x := Nat.div_mul_cancel hd1
      have hby : y / p * p = y := Nat.div_mul_cancel hd2
      have hsum2 : (x / p + y / p) * p ≤ m * p := by rw [add_mul, hax, hby]; exact hxy
      have hle : x / p + y / p ≤ m := Nat.le_of_mul_le_mul_right hsum2 hp0
      exact ⟨(x / p, y / p),
        ⟨⟨Nat.lt_succ_of_le (le_trans (Nat.le_add_right (x / p) (y / p)) hle),
          Nat.lt_succ_of_le (le_trans (Nat.le_add_left (y / p) (x / p)) hle)⟩, hle⟩, hax, hby⟩
    · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hab⟩, hax, hby⟩
      subst hax; subst hby
      dsimp only
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨a, by ring⟩, ⟨b, by ring⟩⟩
      · have : a * p ≤ m * p := mul_le_mul_right' (by omega) p; omega
      · have : b * p ≤ m * p := mul_le_mul_right' (by omega) p; omega
      · rw [← add_mul]; exact mul_le_mul_right' hab p
  have hAsum : ∑ q ∈ (Dom (m * p)).filter (fun q => p ∣ q.1 ∧ p ∣ q.2), gt (m * p) q.1 q.2
      = ∑ k ∈ Dom m, gt (m * p) (k.1 * p) (k.2 * p) := by
    rw [himg, Finset.sum_image hinj]
  have hsplit : ∑ q ∈ Dom (m * p), gt (m * p) q.1 q.2
      = ∑ k ∈ Dom m, gt (m * p) (k.1 * p) (k.2 * p)
        + ∑ q ∈ (Dom (m * p)).filter (fun q => ¬ (p ∣ q.1 ∧ p ∣ q.2)), gt (m * p) q.1 q.2 := by
    rw [← hAsum]
    exact (Finset.sum_filter_add_sum_filter_not (Dom (m * p)) (fun q => p ∣ q.1 ∧ p ∣ q.2) _).symm
  rw [A141057_eq (m * p), A141057_eq m, hsplit]
  have harr : (∑ k ∈ Dom m, gt (m * p) (k.1 * p) (k.2 * p)
        + ∑ q ∈ (Dom (m * p)).filter (fun q => ¬ (p ∣ q.1 ∧ p ∣ q.2)), gt (m * p) q.1 q.2)
        - ∑ k ∈ Dom m, gt m k.1 k.2
      = (∑ k ∈ Dom m, (gt (m * p) (k.1 * p) (k.2 * p) - gt m k.1 k.2))
        + ∑ q ∈ (Dom (m * p)).filter (fun q => ¬ (p ∣ q.1 ∧ p ∣ q.2)), gt (m * p) q.1 q.2 := by
    rw [Finset.sum_sub_distrib]; ring
  rw [harr]
  apply dvd_add
  · apply Finset.dvd_sum
    intro k hk
    have hk' : k.1 + k.2 ≤ m := by
      simp only [Dom, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hk
      exact hk.2
    have hpt := perterm p m k.1 k.2 hp hp5 hk'
    have hsub : m * p - k.1 * p = (m - k.1) * p := by rw [Nat.sub_mul]
    unfold gt
    rw [hsub]
    exact hpt
  · apply Finset.dvd_sum
    intro q hq
    simp only [Dom, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    exact Claim1 p m q.1 q.2 hp hp5 hq.1.2 hq.2


/--
Conjecture: the supercongruences $a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$
hold for primes $p \ge 5$ and positive integers $n$ and $k$.
The note regarding extending the sequence to negative $n$ is omitted from the formal statement,
which focuses on the main claim for $n \in \mathbb{N}^+$.
-/
theorem oeis_a141057_supercongruence_conjecture (p k n : ℕ)
    (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (h_n_pos : 1 ≤ n) :
    (A141057 (n * p ^ k) : ℤ) ≡ A141057 (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k))] := by
  haveI : Fact p.Prime := ⟨hp⟩
  set m := n * p ^ (k - 1) with hm
  have hmp : n * p ^ k = m * p := by
    have hpk : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ]; congr 1; omega
    rw [hm, mul_assoc, ← hpk]
  have hm1 : 1 ≤ m := by
    rw [hm]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hred := red p m hp h_p_ge_5 hm1
  have htge : k - 1 ≤ padicValNat p m := by
    rw [hm, padicValNat.mul (show n ≠ 0 by omega) (by positivity), padicValNat.prime_pow]
    omega
  have hexp : 3 * k ≤ 3 * (padicValNat p m + 1) := by omega
  have hdvd : (p : ℤ) ^ (3 * k) ∣ ((A141057 (n * p ^ k) : ℤ) - A141057 (n * p ^ (k - 1))) := by
    rw [hmp]
    exact dvd_trans (pow_dvd_pow _ hexp) hred
  rw [Int.modEq_iff_dvd]
  have hneg : (A141057 (n * p ^ (k - 1)) : ℤ) - (A141057 (n * p ^ k) : ℤ)
      = -((A141057 (n * p ^ k) : ℤ) - A141057 (n * p ^ (k - 1))) := by ring
  rw [hneg]
  exact (dvd_neg).mpr hdvd

