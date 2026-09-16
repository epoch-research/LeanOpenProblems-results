import FormalConjectures.Util.ProblemImports
import Submission.Tree
import Submission.ProofAll

open Nat Int Finset

def A281977 (n : ℕ) : ℕ :=
  let B : ℕ := n.sqrt
  let R := Finset.range (B + 1)
  R.sum fun x =>
  R.sum fun y =>
  R.sum fun z =>
  R.sum fun w =>
    let sum_sq_eq := x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n
    let x_is_sq := x.sqrt * x.sqrt = x
    let L : ℤ := -7 * (x : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ)
    let L_is_sq := L ≥ 0 ∧ L.sqrt * L.sqrt = L
    if sum_sq_eq ∧ x_is_sq ∧ L_is_sq then 1 else 0

lemma sum_four (R : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ) (x y z w : ℕ)
  (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R) (hw : w ∈ R)
  (h_val : f x y z w > 0) :
  (R.sum fun a => R.sum fun b => R.sum fun c => R.sum fun d => f a b c d) > 0 := by
  have H1 : (R.sum fun d => f x y z d) > 0 := by
    apply lt_of_lt_of_le h_val
    apply single_le_sum (fun i _ => zero_le _) hw
  have H2 : (R.sum fun c => R.sum fun d => f x y c d) > 0 := by
    apply lt_of_lt_of_le H1
    apply single_le_sum (fun i _ => zero_le _) hz
  have H3 : (R.sum fun b => R.sum fun c => R.sum fun d => f x b c d) > 0 := by
    apply lt_of_lt_of_le H2
    apply single_le_sum (fun i _ => zero_le _) hy
  have H4 : (R.sum fun a => R.sum fun b => R.sum fun c => R.sum fun d => f a b c d) > 0 := by
    apply lt_of_lt_of_le H3
    apply single_le_sum (fun i _ => zero_le _) hx
  exact H4

lemma A281977_pos_of_witness (n x y z w : ℕ)
  (h_sum : x^2 + y^2 + z^2 + w^2 = n)
  (h_x : x.sqrt * x.sqrt = x)
  (h_L : let L : ℤ := -7*x - 8*y + 8*z + 16*w; L ≥ 0 ∧ L.sqrt * L.sqrt = L) :
  A281977 n > 0 := by
  have h_x2 : x^2 = x * x := by ring
  have h_y2 : y^2 = y * y := by ring
  have h_z2 : z^2 = z * z := by ring
  have h_w2 : w^2 = w * w := by ring
  have hx_le : x ≤ n.sqrt := by
    apply Nat.le_sqrt.mpr
    rw [←h_x2, ←h_sum]
    have : x^2 ≤ x^2 + y^2 + z^2 + w^2 := by omega
    exact this
  have hy_le : y ≤ n.sqrt := by
    apply Nat.le_sqrt.mpr
    rw [←h_y2, ←h_sum]
    have : y^2 ≤ x^2 + y^2 + z^2 + w^2 := by omega
    exact this
  have hz_le : z ≤ n.sqrt := by
    apply Nat.le_sqrt.mpr
    rw [←h_z2, ←h_sum]
    have : z^2 ≤ x^2 + y^2 + z^2 + w^2 := by omega
    exact this
  have hw_le : w ≤ n.sqrt := by
    apply Nat.le_sqrt.mpr
    rw [←h_w2, ←h_sum]
    have : w^2 ≤ x^2 + y^2 + z^2 + w^2 := by omega
    exact this
  unfold A281977
  apply sum_four _ _ x y z w
  · exact mem_range.mpr (Nat.lt_succ_of_le hx_le)
  · exact mem_range.mpr (Nat.lt_succ_of_le hy_le)
  · exact mem_range.mpr (Nat.lt_succ_of_le hz_le)
  · exact mem_range.mpr (Nat.lt_succ_of_le hw_le)
  · dsimp
    split_ifs with h
    · decide
    · exfalso
      rcases h_L with ⟨hL1, hL2⟩
      apply h
      exact ⟨h_sum, h_x, hL1, hL2⟩

lemma is_sq_of_eq_sq (k x : ℕ) (h : k * k = x) : x.sqrt * x.sqrt = x := by
  subst h
  rw [Nat.sqrt_eq]

lemma L_is_sq_of_eq_sq (L : Int) (k : ℕ) (h1 : L ≥ 0) (h2 : (k * k : Int) = L) :
  L.sqrt * L.sqrt = L := by
  have H : Int.sqrt (k * k) = k := by
    unfold Int.sqrt
    have : Int.toNat (↑k * ↑k) = k * k := rfl
    rw [this, Nat.sqrt_eq]
  subst h2
  rw [H]

lemma leaf_implies_real (n x_rt y z w L_rt : Nat) :
  check_one n x_rt y z w L_rt = true → A281977 n > 0 := by
  intro h
  unfold check_one at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨h_sum, h_L1, h_L2⟩
  apply A281977_pos_of_witness n (x_rt * x_rt) y z w
  · have H : (x_rt * x_rt) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = x_rt * x_rt * (x_rt * x_rt) + y * y + z * z + w * w := by ring
    rw [H, h_sum]
  · exact is_sq_of_eq_sq x_rt (x_rt * x_rt) rfl
  · have h_push : (-7 * (x_rt * x_rt : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ)) =
                  (-7 * (x_rt : ℤ) * (x_rt : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ)) := by  ring
    change (8 * (z:Nat) + 16 * (w:Nat) ≥ 7 * ((x_rt*x_rt):Nat) + 8 * (y:Nat)) at h_L1
    have h_L1_int : -7 * (x_rt * x_rt : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ) ≥ 0 := by
      
      linarith
    change ((L_rt * L_rt : Nat) + (7 * ((x_rt*x_rt):Nat) + 8 * (y:Nat)) = 8 * (z:Nat) + 16 * (w:Nat)) at h_L2
    have h_L2_int : (L_rt * L_rt : ℤ) = -7 * (x_rt * x_rt : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ) := by
      
      linarith
    exact ⟨h_L1_int, L_is_sq_of_eq_sq _ _ h_L1_int h_L2_int⟩

lemma check_huge_loop_implies (k cur_n cur_val : Nat) :
  check_huge_loop k cur_n cur_val = true →
  ∀ i < k, ∃ x_rt y z w L_rt, check_one (cur_n + i) x_rt y z w L_rt = true := by
  induction k generalizing cur_n cur_val with
  | zero =>
    intro _ i hi
    omega
  | succ k ih =>
    intro h i hi
    unfold check_huge_loop at h
    dsimp at h
    split_ifs at h with h_one
    · if h_i : i = 0 then
        subst h_i
        rw [Nat.add_zero]
        exact ⟨_, _, _, _, _, h_one⟩
      else
        have hi' : i - 1 < k := by omega
        have := ih (cur_n + 1) (cur_val / 0x1000000000000) h (i - 1) hi'
        have h_eq : cur_n + 1 + (i - 1) = cur_n + i := by omega
        rw [h_eq] at this
        exact this

lemma check_huge_implies (n val count : Nat) :
  (check_huge n val count).1 = true →
  ∀ i < count, ∃ x_rt y z w L_rt, check_one (n + i) x_rt y z w L_rt = true := by
  intro h
  exact check_huge_loop_implies count n val h

lemma check_list_loop_implies (cur_n stop : Nat) (l : List Nat) :
  check_list_loop cur_n stop l = true →
  ∀ i, cur_n ≤ i → i < stop → ∃ x_rt y z w L_rt, check_one i x_rt y z w L_rt = true := by
  induction l generalizing cur_n with
  | nil =>
    intro h i hi1 hi2
    unfold check_list_loop at h
    have : cur_n = stop := beq_iff_eq.mp h
    omega
  | cons v vs ih =>
    intro h i hi1 hi2
    unfold check_list_loop at h
    dsimp at h
    let count := if cur_n + 1000 > stop then stop - cur_n else 1000
    have h_next : (check_huge cur_n v count).2 = cur_n + count := rfl
    revert h
    generalize h_ok : (check_huge cur_n v count).1 = ok
    intro h
    if h_ok_true : ok = true then
      subst h_ok_true
      dsimp at h
      if h_i : i < cur_n + count then
        have := check_huge_implies _ _ _ h_ok (i - cur_n) (by omega)
        have h_eq : cur_n + (i - cur_n) = i := by omega
        rw [h_eq] at this
        exact this
      else
        rw [h_next] at h
        apply ih (cur_n + count) h i
        · omega
        · omega
    else
      have : ok = false := by cases ok <;> tauto
      subst this
      dsimp at h
      contradiction

lemma check_list_implies (n stop : Nat) (l : List Nat) :
  check_list n stop l = true →
  ∀ i, n ≤ i → i < stop → ∃ x_rt y z w L_rt, check_one i x_rt y z w L_rt = true := by
  intro h
  exact check_list_loop_implies n stop l h

lemma valid_range (start stop : Nat) (l : List Nat) :
  check_list start stop l = true →
  ∀ n, start ≤ n → n < stop → A281977 n > 0 := by
  intro h n hn1 hn2
  have ⟨x_rt, y, z, w, L_rt, H⟩ := check_list_implies start stop l h n hn1 hn2
  exact leaf_implies_real n x_rt y z w L_rt H

set_option maxHeartbeats 0
set_option maxRecDepth 2000000
/-- We have verified the conjecture for all n = 0..10^6. -/
theorem A281977_verified_up_to_1e6 (n : ℕ) (h : n ≤ 10^6) : A281977 n > 0 := by
  have H0 := valid_range _ _ _ chunk_0_valid n
  have H1 := valid_range _ _ _ chunk_1_valid n
  have H2 := valid_range _ _ _ chunk_2_valid n
  have H3 := valid_range _ _ _ chunk_3_valid n
  have H4 := valid_range _ _ _ chunk_4_valid n
  have H5 := valid_range _ _ _ chunk_5_valid n
  have H6 := valid_range _ _ _ chunk_6_valid n
  have H7 := valid_range _ _ _ chunk_7_valid n
  have H8 := valid_range _ _ _ chunk_8_valid n
  have H9 := valid_range _ _ _ chunk_9_valid n
  have H10 := valid_range _ _ _ chunk_10_valid n
  have H11 := valid_range _ _ _ chunk_11_valid n
  have H12 := valid_range _ _ _ chunk_12_valid n
  have H13 := valid_range _ _ _ chunk_13_valid n
  have H14 := valid_range _ _ _ chunk_14_valid n
  have H15 := valid_range _ _ _ chunk_15_valid n
  have H16 := valid_range _ _ _ chunk_16_valid n
  have H17 := valid_range _ _ _ chunk_17_valid n
  have H18 := valid_range _ _ _ chunk_18_valid n
  have H19 := valid_range _ _ _ chunk_19_valid n
  have H20 := valid_range _ _ _ chunk_20_valid n
  have H21 := valid_range _ _ _ chunk_21_valid n
  have H22 := valid_range _ _ _ chunk_22_valid n
  have H23 := valid_range _ _ _ chunk_23_valid n
  have H24 := valid_range _ _ _ chunk_24_valid n
  have H25 := valid_range _ _ _ chunk_25_valid n
  have H26 := valid_range _ _ _ chunk_26_valid n
  have H27 := valid_range _ _ _ chunk_27_valid n
  have H28 := valid_range _ _ _ chunk_28_valid n
  have H29 := valid_range _ _ _ chunk_29_valid n
  have H30 := valid_range _ _ _ chunk_30_valid n
  have H31 := valid_range _ _ _ chunk_31_valid n
  have H32 := valid_range _ _ _ chunk_32_valid n
  have H33 := valid_range _ _ _ chunk_33_valid n
  have H34 := valid_range _ _ _ chunk_34_valid n
  have H35 := valid_range _ _ _ chunk_35_valid n
  have H36 := valid_range _ _ _ chunk_36_valid n
  have H37 := valid_range _ _ _ chunk_37_valid n
  have H38 := valid_range _ _ _ chunk_38_valid n
  have H39 := valid_range _ _ _ chunk_39_valid n
  have H40 := valid_range _ _ _ chunk_40_valid n
  have H41 := valid_range _ _ _ chunk_41_valid n
  have H42 := valid_range _ _ _ chunk_42_valid n
  have H43 := valid_range _ _ _ chunk_43_valid n
  have H44 := valid_range _ _ _ chunk_44_valid n
  have H45 := valid_range _ _ _ chunk_45_valid n
  have H46 := valid_range _ _ _ chunk_46_valid n
  have H47 := valid_range _ _ _ chunk_47_valid n
  have H48 := valid_range _ _ _ chunk_48_valid n
  have H49 := valid_range _ _ _ chunk_49_valid n
  have H50 := valid_range _ _ _ chunk_50_valid n
  have H51 := valid_range _ _ _ chunk_51_valid n
  have H52 := valid_range _ _ _ chunk_52_valid n
  have H53 := valid_range _ _ _ chunk_53_valid n
  have H54 := valid_range _ _ _ chunk_54_valid n
  have H55 := valid_range _ _ _ chunk_55_valid n
  have H56 := valid_range _ _ _ chunk_56_valid n
  have H57 := valid_range _ _ _ chunk_57_valid n
  have H58 := valid_range _ _ _ chunk_58_valid n
  have H59 := valid_range _ _ _ chunk_59_valid n
  have H60 := valid_range _ _ _ chunk_60_valid n
  have H61 := valid_range _ _ _ chunk_61_valid n
  have H62 := valid_range _ _ _ chunk_62_valid n
  have H63 := valid_range _ _ _ chunk_63_valid n
  have H64 := valid_range _ _ _ chunk_64_valid n
  have H65 := valid_range _ _ _ chunk_65_valid n
  have H66 := valid_range _ _ _ chunk_66_valid n
  have H67 := valid_range _ _ _ chunk_67_valid n
  have H68 := valid_range _ _ _ chunk_68_valid n
  have H69 := valid_range _ _ _ chunk_69_valid n
  have H70 := valid_range _ _ _ chunk_70_valid n
  have H71 := valid_range _ _ _ chunk_71_valid n
  have H72 := valid_range _ _ _ chunk_72_valid n
  have H73 := valid_range _ _ _ chunk_73_valid n
  have H74 := valid_range _ _ _ chunk_74_valid n
  have H75 := valid_range _ _ _ chunk_75_valid n
  have H76 := valid_range _ _ _ chunk_76_valid n
  have H77 := valid_range _ _ _ chunk_77_valid n
  have H78 := valid_range _ _ _ chunk_78_valid n
  have H79 := valid_range _ _ _ chunk_79_valid n
  have H80 := valid_range _ _ _ chunk_80_valid n
  have H81 := valid_range _ _ _ chunk_81_valid n
  have H82 := valid_range _ _ _ chunk_82_valid n
  have H83 := valid_range _ _ _ chunk_83_valid n
  have H84 := valid_range _ _ _ chunk_84_valid n
  have H85 := valid_range _ _ _ chunk_85_valid n
  have H86 := valid_range _ _ _ chunk_86_valid n
  have H87 := valid_range _ _ _ chunk_87_valid n
  have H88 := valid_range _ _ _ chunk_88_valid n
  have H89 := valid_range _ _ _ chunk_89_valid n
  have H90 := valid_range _ _ _ chunk_90_valid n
  have H91 := valid_range _ _ _ chunk_91_valid n
  have H92 := valid_range _ _ _ chunk_92_valid n
  have H93 := valid_range _ _ _ chunk_93_valid n
  have H94 := valid_range _ _ _ chunk_94_valid n
  have H95 := valid_range _ _ _ chunk_95_valid n
  have H96 := valid_range _ _ _ chunk_96_valid n
  have H97 := valid_range _ _ _ chunk_97_valid n
  have H98 := valid_range _ _ _ chunk_98_valid n
  have H99 := valid_range _ _ _ chunk_99_valid n
  if h0 : n < 10000 then exact H0 (by omega) (by omega)
  else
  if h1 : n < 20000 then exact H1 (by omega) (by omega)
  else
  if h2 : n < 30000 then exact H2 (by omega) (by omega)
  else
  if h3 : n < 40000 then exact H3 (by omega) (by omega)
  else
  if h4 : n < 50000 then exact H4 (by omega) (by omega)
  else
  if h5 : n < 60000 then exact H5 (by omega) (by omega)
  else
  if h6 : n < 70000 then exact H6 (by omega) (by omega)
  else
  if h7 : n < 80000 then exact H7 (by omega) (by omega)
  else
  if h8 : n < 90000 then exact H8 (by omega) (by omega)
  else
  if h9 : n < 100000 then exact H9 (by omega) (by omega)
  else
  if h10 : n < 110000 then exact H10 (by omega) (by omega)
  else
  if h11 : n < 120000 then exact H11 (by omega) (by omega)
  else
  if h12 : n < 130000 then exact H12 (by omega) (by omega)
  else
  if h13 : n < 140000 then exact H13 (by omega) (by omega)
  else
  if h14 : n < 150000 then exact H14 (by omega) (by omega)
  else
  if h15 : n < 160000 then exact H15 (by omega) (by omega)
  else
  if h16 : n < 170000 then exact H16 (by omega) (by omega)
  else
  if h17 : n < 180000 then exact H17 (by omega) (by omega)
  else
  if h18 : n < 190000 then exact H18 (by omega) (by omega)
  else
  if h19 : n < 200000 then exact H19 (by omega) (by omega)
  else
  if h20 : n < 210000 then exact H20 (by omega) (by omega)
  else
  if h21 : n < 220000 then exact H21 (by omega) (by omega)
  else
  if h22 : n < 230000 then exact H22 (by omega) (by omega)
  else
  if h23 : n < 240000 then exact H23 (by omega) (by omega)
  else
  if h24 : n < 250000 then exact H24 (by omega) (by omega)
  else
  if h25 : n < 260000 then exact H25 (by omega) (by omega)
  else
  if h26 : n < 270000 then exact H26 (by omega) (by omega)
  else
  if h27 : n < 280000 then exact H27 (by omega) (by omega)
  else
  if h28 : n < 290000 then exact H28 (by omega) (by omega)
  else
  if h29 : n < 300000 then exact H29 (by omega) (by omega)
  else
  if h30 : n < 310000 then exact H30 (by omega) (by omega)
  else
  if h31 : n < 320000 then exact H31 (by omega) (by omega)
  else
  if h32 : n < 330000 then exact H32 (by omega) (by omega)
  else
  if h33 : n < 340000 then exact H33 (by omega) (by omega)
  else
  if h34 : n < 350000 then exact H34 (by omega) (by omega)
  else
  if h35 : n < 360000 then exact H35 (by omega) (by omega)
  else
  if h36 : n < 370000 then exact H36 (by omega) (by omega)
  else
  if h37 : n < 380000 then exact H37 (by omega) (by omega)
  else
  if h38 : n < 390000 then exact H38 (by omega) (by omega)
  else
  if h39 : n < 400000 then exact H39 (by omega) (by omega)
  else
  if h40 : n < 410000 then exact H40 (by omega) (by omega)
  else
  if h41 : n < 420000 then exact H41 (by omega) (by omega)
  else
  if h42 : n < 430000 then exact H42 (by omega) (by omega)
  else
  if h43 : n < 440000 then exact H43 (by omega) (by omega)
  else
  if h44 : n < 450000 then exact H44 (by omega) (by omega)
  else
  if h45 : n < 460000 then exact H45 (by omega) (by omega)
  else
  if h46 : n < 470000 then exact H46 (by omega) (by omega)
  else
  if h47 : n < 480000 then exact H47 (by omega) (by omega)
  else
  if h48 : n < 490000 then exact H48 (by omega) (by omega)
  else
  if h49 : n < 500000 then exact H49 (by omega) (by omega)
  else
  if h50 : n < 510000 then exact H50 (by omega) (by omega)
  else
  if h51 : n < 520000 then exact H51 (by omega) (by omega)
  else
  if h52 : n < 530000 then exact H52 (by omega) (by omega)
  else
  if h53 : n < 540000 then exact H53 (by omega) (by omega)
  else
  if h54 : n < 550000 then exact H54 (by omega) (by omega)
  else
  if h55 : n < 560000 then exact H55 (by omega) (by omega)
  else
  if h56 : n < 570000 then exact H56 (by omega) (by omega)
  else
  if h57 : n < 580000 then exact H57 (by omega) (by omega)
  else
  if h58 : n < 590000 then exact H58 (by omega) (by omega)
  else
  if h59 : n < 600000 then exact H59 (by omega) (by omega)
  else
  if h60 : n < 610000 then exact H60 (by omega) (by omega)
  else
  if h61 : n < 620000 then exact H61 (by omega) (by omega)
  else
  if h62 : n < 630000 then exact H62 (by omega) (by omega)
  else
  if h63 : n < 640000 then exact H63 (by omega) (by omega)
  else
  if h64 : n < 650000 then exact H64 (by omega) (by omega)
  else
  if h65 : n < 660000 then exact H65 (by omega) (by omega)
  else
  if h66 : n < 670000 then exact H66 (by omega) (by omega)
  else
  if h67 : n < 680000 then exact H67 (by omega) (by omega)
  else
  if h68 : n < 690000 then exact H68 (by omega) (by omega)
  else
  if h69 : n < 700000 then exact H69 (by omega) (by omega)
  else
  if h70 : n < 710000 then exact H70 (by omega) (by omega)
  else
  if h71 : n < 720000 then exact H71 (by omega) (by omega)
  else
  if h72 : n < 730000 then exact H72 (by omega) (by omega)
  else
  if h73 : n < 740000 then exact H73 (by omega) (by omega)
  else
  if h74 : n < 750000 then exact H74 (by omega) (by omega)
  else
  if h75 : n < 760000 then exact H75 (by omega) (by omega)
  else
  if h76 : n < 770000 then exact H76 (by omega) (by omega)
  else
  if h77 : n < 780000 then exact H77 (by omega) (by omega)
  else
  if h78 : n < 790000 then exact H78 (by omega) (by omega)
  else
  if h79 : n < 800000 then exact H79 (by omega) (by omega)
  else
  if h80 : n < 810000 then exact H80 (by omega) (by omega)
  else
  if h81 : n < 820000 then exact H81 (by omega) (by omega)
  else
  if h82 : n < 830000 then exact H82 (by omega) (by omega)
  else
  if h83 : n < 840000 then exact H83 (by omega) (by omega)
  else
  if h84 : n < 850000 then exact H84 (by omega) (by omega)
  else
  if h85 : n < 860000 then exact H85 (by omega) (by omega)
  else
  if h86 : n < 870000 then exact H86 (by omega) (by omega)
  else
  if h87 : n < 880000 then exact H87 (by omega) (by omega)
  else
  if h88 : n < 890000 then exact H88 (by omega) (by omega)
  else
  if h89 : n < 900000 then exact H89 (by omega) (by omega)
  else
  if h90 : n < 910000 then exact H90 (by omega) (by omega)
  else
  if h91 : n < 920000 then exact H91 (by omega) (by omega)
  else
  if h92 : n < 930000 then exact H92 (by omega) (by omega)
  else
  if h93 : n < 940000 then exact H93 (by omega) (by omega)
  else
  if h94 : n < 950000 then exact H94 (by omega) (by omega)
  else
  if h95 : n < 960000 then exact H95 (by omega) (by omega)
  else
  if h96 : n < 970000 then exact H96 (by omega) (by omega)
  else
  if h97 : n < 980000 then exact H97 (by omega) (by omega)
  else
  if h98 : n < 990000 then exact H98 (by omega) (by omega)
  else
  exact H99 (by omega) (by omega)

theorem A281977_verified_up_to_1e6.disproof : ¬ (type_of% @A281977_verified_up_to_1e6) := sorry
