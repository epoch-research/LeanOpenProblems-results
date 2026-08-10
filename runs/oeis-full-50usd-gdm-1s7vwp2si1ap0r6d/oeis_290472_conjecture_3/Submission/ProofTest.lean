import FormalConjectures.Util.ProofHelper

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def div2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => div2 n + 1

def div3 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | n + 3 => div3 n + 1

def div7 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | n + 7 => div7 n + 1

def fast_sqrt_aux (n : Nat) (low high : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => low
  | fuel + 1 =>
    if low >= high then low
    else
      let mid := div2 (low + high + 1)
      if mid * mid <= n then
        fast_sqrt_aux n mid high fuel
      else
        fast_sqrt_aux n low (mid - 1) fuel

def fast_sqrt (n : Nat) : Nat :=
  fast_sqrt_aux n 0 n 30

def loop_3var_opt (fuel : Nat) (N max_z : Nat) (init_z_sq7 : Nat) (x y y_sq3 z count sum : Nat) : Bool :=
  if count >= 2 then true
  else
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if y_sq3 >= N then false
      else
        if sum == N then
          let count' := count + 1
          if count' >= 2 then true
          else if z == 0 then
            let y_sq3' := y_sq3 + 6 * y + 3
            loop_3var_opt fuel N max_z init_z_sq7 1 (y + 1) y_sq3' max_z count' (1 + y_sq3' + init_z_sq7)
          else
            loop_3var_opt fuel N max_z init_z_sq7 x y y_sq3 (z - 1) count' (sum - 14 * z + 7)
        else if sum < N then
          loop_3var_opt fuel N max_z init_z_sq7 (x + 1) y y_sq3 z count (sum + 2 * x + 1)
        else
          if z == 0 then
            let y_sq3' := y_sq3 + 6 * y + 3
            loop_3var_opt fuel N max_z init_z_sq7 1 (y + 1) y_sq3' max_z count (1 + y_sq3' + init_z_sq7)
          else
            loop_3var_opt fuel N max_z init_z_sq7 x y y_sq3 (z - 1) count (sum - 14 * z + 7)

def fast_has_two_sols (n : ℕ) : Bool :=
  let N := 6 * n + 1
  let max_z := fast_sqrt (div7 N)
  let init_z_sq7 := 7 * max_z * max_z
  let fuel := N * 2
  loop_3var_opt fuel N max_z init_z_sq7 1 0 0 max_z 0 (1 + init_z_sq7)
theorem block_0 : check_range fast_has_two_sols 386 100 287 = true := by decide
theorem block_1 : check_range fast_has_two_sols 486 100 387 = true := by decide
theorem block_2 : check_range fast_has_two_sols 586 100 487 = true := by decide
theorem block_3 : check_range fast_has_two_sols 686 100 587 = true := by decide
theorem block_4 : check_range fast_has_two_sols 786 100 687 = true := by decide
theorem block_5 : check_range fast_has_two_sols 886 100 787 = true := by decide
theorem block_6 : check_range fast_has_two_sols 986 100 887 = true := by decide
theorem block_7 : check_range fast_has_two_sols 1086 100 987 = true := by decide
theorem block_8 : check_range fast_has_two_sols 1186 100 1087 = true := by decide
theorem block_9 : check_range fast_has_two_sols 1286 100 1187 = true := by decide
theorem block_10 : check_range fast_has_two_sols 1386 100 1287 = true := by decide
theorem block_11 : check_range fast_has_two_sols 1486 100 1387 = true := by decide
theorem block_12 : check_range fast_has_two_sols 1586 100 1487 = true := by decide
theorem block_13 : check_range fast_has_two_sols 1686 100 1587 = true := by decide
theorem block_14 : check_range fast_has_two_sols 1786 100 1687 = true := by decide
theorem block_15 : check_range fast_has_two_sols 1886 100 1787 = true := by decide
theorem block_16 : check_range fast_has_two_sols 1986 100 1887 = true := by decide
theorem block_17 : check_range fast_has_two_sols 2086 100 1987 = true := by decide
theorem block_18 : check_range fast_has_two_sols 2186 100 2087 = true := by decide
theorem block_19 : check_range fast_has_two_sols 2286 100 2187 = true := by decide
theorem block_20 : check_range fast_has_two_sols 2386 100 2287 = true := by decide
theorem block_21 : check_range fast_has_two_sols 2486 100 2387 = true := by decide
theorem block_22 : check_range fast_has_two_sols 2586 100 2487 = true := by decide
theorem block_23 : check_range fast_has_two_sols 2686 100 2587 = true := by decide
theorem block_24 : check_range fast_has_two_sols 2786 100 2687 = true := by decide
theorem block_25 : check_range fast_has_two_sols 2886 100 2787 = true := by decide
theorem block_26 : check_range fast_has_two_sols 2986 100 2887 = true := by decide
theorem block_27 : check_range fast_has_two_sols 3086 100 2987 = true := by decide
theorem block_28 : check_range fast_has_two_sols 3186 100 3087 = true := by decide
theorem block_29 : check_range fast_has_two_sols 3286 100 3187 = true := by decide
theorem block_30 : check_range fast_has_two_sols 3386 100 3287 = true := by decide
theorem block_31 : check_range fast_has_two_sols 3486 100 3387 = true := by decide
theorem block_32 : check_range fast_has_two_sols 3586 100 3487 = true := by decide
theorem block_33 : check_range fast_has_two_sols 3686 100 3587 = true := by decide
theorem block_34 : check_range fast_has_two_sols 3786 100 3687 = true := by decide
theorem block_35 : check_range fast_has_two_sols 3886 100 3787 = true := by decide
theorem block_36 : check_range fast_has_two_sols 3986 100 3887 = true := by decide
theorem block_37 : check_range fast_has_two_sols 4086 100 3987 = true := by decide
theorem block_38 : check_range fast_has_two_sols 4186 100 4087 = true := by decide
theorem block_39 : check_range fast_has_two_sols 4286 100 4187 = true := by decide
theorem block_40 : check_range fast_has_two_sols 4386 100 4287 = true := by decide
theorem block_41 : check_range fast_has_two_sols 4486 100 4387 = true := by decide
theorem block_42 : check_range fast_has_two_sols 4586 100 4487 = true := by decide
theorem block_43 : check_range fast_has_two_sols 4686 100 4587 = true := by decide
theorem block_44 : check_range fast_has_two_sols 4786 100 4687 = true := by decide
theorem block_45 : check_range fast_has_two_sols 4886 100 4787 = true := by decide
theorem block_46 : check_range fast_has_two_sols 4986 100 4887 = true := by decide
theorem block_47 : check_range fast_has_two_sols 5086 100 4987 = true := by decide
theorem block_48 : check_range fast_has_two_sols 5186 100 5087 = true := by decide
theorem block_49 : check_range fast_has_two_sols 5286 100 5187 = true := by decide
theorem block_50 : check_range fast_has_two_sols 5386 100 5287 = true := by decide
theorem block_51 : check_range fast_has_two_sols 5486 100 5387 = true := by decide
theorem block_52 : check_range fast_has_two_sols 5586 100 5487 = true := by decide
theorem block_53 : check_range fast_has_two_sols 5686 100 5587 = true := by decide
theorem block_54 : check_range fast_has_two_sols 5786 100 5687 = true := by decide
theorem block_55 : check_range fast_has_two_sols 5886 100 5787 = true := by decide
theorem block_56 : check_range fast_has_two_sols 5986 100 5887 = true := by decide
theorem block_57 : check_range fast_has_two_sols 6086 100 5987 = true := by decide
theorem block_58 : check_range fast_has_two_sols 6186 100 6087 = true := by decide
theorem block_59 : check_range fast_has_two_sols 6286 100 6187 = true := by decide
theorem block_60 : check_range fast_has_two_sols 6386 100 6287 = true := by decide
theorem block_61 : check_range fast_has_two_sols 6486 100 6387 = true := by decide
theorem block_62 : check_range fast_has_two_sols 6586 100 6487 = true := by decide
theorem block_63 : check_range fast_has_two_sols 6686 100 6587 = true := by decide
theorem block_64 : check_range fast_has_two_sols 6786 100 6687 = true := by decide
theorem block_65 : check_range fast_has_two_sols 6886 100 6787 = true := by decide
theorem block_66 : check_range fast_has_two_sols 6986 100 6887 = true := by decide
theorem block_67 : check_range fast_has_two_sols 7086 100 6987 = true := by decide
theorem block_68 : check_range fast_has_two_sols 7186 100 7087 = true := by decide
theorem block_69 : check_range fast_has_two_sols 7286 100 7187 = true := by decide
theorem block_70 : check_range fast_has_two_sols 7386 100 7287 = true := by decide
theorem block_71 : check_range fast_has_two_sols 7486 100 7387 = true := by decide
theorem block_72 : check_range fast_has_two_sols 7586 100 7487 = true := by decide
theorem block_73 : check_range fast_has_two_sols 7686 100 7587 = true := by decide
theorem block_74 : check_range fast_has_two_sols 7786 100 7687 = true := by decide
theorem block_75 : check_range fast_has_two_sols 7886 100 7787 = true := by decide
theorem block_76 : check_range fast_has_two_sols 7986 100 7887 = true := by decide
theorem block_77 : check_range fast_has_two_sols 8086 100 7987 = true := by decide
theorem block_78 : check_range fast_has_two_sols 8186 100 8087 = true := by decide
theorem block_79 : check_range fast_has_two_sols 8286 100 8187 = true := by decide
theorem block_80 : check_range fast_has_two_sols 8386 100 8287 = true := by decide
theorem block_81 : check_range fast_has_two_sols 8486 100 8387 = true := by decide
theorem block_82 : check_range fast_has_two_sols 8586 100 8487 = true := by decide
theorem block_83 : check_range fast_has_two_sols 8686 100 8587 = true := by decide
theorem block_84 : check_range fast_has_two_sols 8786 100 8687 = true := by decide
theorem block_85 : check_range fast_has_two_sols 8886 100 8787 = true := by decide
theorem block_86 : check_range fast_has_two_sols 8986 100 8887 = true := by decide
theorem block_87 : check_range fast_has_two_sols 9086 100 8987 = true := by decide
theorem block_88 : check_range fast_has_two_sols 9186 100 9087 = true := by decide
theorem block_89 : check_range fast_has_two_sols 9286 100 9187 = true := by decide
theorem block_90 : check_range fast_has_two_sols 9386 100 9287 = true := by decide
theorem block_91 : check_range fast_has_two_sols 9486 100 9387 = true := by decide
theorem block_92 : check_range fast_has_two_sols 9586 100 9487 = true := by decide
theorem block_93 : check_range fast_has_two_sols 9686 100 9587 = true := by decide
theorem block_94 : check_range fast_has_two_sols 9786 100 9687 = true := by decide
theorem block_95 : check_range fast_has_two_sols 9886 100 9787 = true := by decide
theorem block_96 : check_range fast_has_two_sols 9986 100 9887 = true := by decide
theorem block_97 : check_range fast_has_two_sols 10086 100 9987 = true := by decide
theorem block_98 : check_range fast_has_two_sols 10186 100 10087 = true := by decide
theorem block_99 : check_range fast_has_two_sols 10286 100 10187 = true := by decide
